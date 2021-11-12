theory BPlusTree_ImpRange
imports
  BPlusTree_Range
  BPlusTree_Iter
begin

(* Adding an actual range iterator based on the normal iterator
is trivial (just forward until we reach the first element \<ge> and stop
as soon as we have an element <)
We now try to implement a search for the first element of the range efficiently
 *)
subsection "The imperative split locale"

locale imp_split_range = abs_split_range: split_range split lrange_list
  for split::
    "('a::{heap,default,linorder,order_top} bplustree \<times> 'a) list \<Rightarrow> 'a
       \<Rightarrow> ('a bplustree \<times> 'a) list \<times> ('a bplustree \<times> 'a) list" 
    and lrange_list ::  "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) list \<Rightarrow> 'a list" +
  fixes imp_split:: "('a btnode ref option \<times> 'a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a \<Rightarrow> nat Heap"
  assumes imp_split_rule [sep_heap_rules]:"sorted_less (separators ts) \<Longrightarrow>
  length tsi = length rs \<Longrightarrow>
  tsi'' = zip (zip (map fst tsi) (zip (butlast (r#rs)) (butlast (rs@[z])))) (map snd tsi) \<Longrightarrow>
 <is_pfa c tsi (a,n) 
  * blist_assn k ts tsi'' > 
    imp_split (a,n) p 
  <\<lambda>i. 
    is_pfa c tsi (a,n)
    * blist_assn k ts tsi''
    * \<up>(split_relation ts (split ts p) i)>\<^sub>t"

locale imp_split2 = abs_split_range: split_range split lrange_list + imp_split_range split lrange_list imp_split
  for split::
    "('a bplustree \<times> 'a::{heap,default,linorder,order_top}) list \<Rightarrow> 'a
       \<Rightarrow> ('a bplustree \<times> 'a) list \<times> ('a bplustree \<times> 'a) list" 
    and lrange_list ::  "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) list \<Rightarrow> 'a list"
    and imp_split :: "('a btnode ref option \<times> 'a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a \<Rightarrow> nat Heap" +
  fixes imp_lrange_list:: "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a pfa_it Heap"
  assumes lrange_list_rule [sep_heap_rules]:"sorted_less ks \<Longrightarrow>
   <is_pfa c ks (a',n')> 
    imp_lrange_list x (a',n') 
  <pfa_is_it c ks (a',n') (lrange_list x ks)>\<^sub>t"
begin

partial_function (heap) leafs_range ::
  "'a btnode ref \<Rightarrow> 'a \<Rightarrow> 'a btnode ref option Heap"
  where
    "leafs_range p x = do {
  node \<leftarrow> !p;
  (case node of
     Btleaf xs z \<Rightarrow> do {
        return (Some p)
      }
       |
     Btnode ts t \<Rightarrow> do {
       i \<leftarrow> imp_split ts x;
       tsl \<leftarrow> pfa_length ts;
       if i < tsl then do {
         s \<leftarrow> pfa_get ts i;
         let (sub,sep) = s in
           leafs_range (the sub) x
       } else
           leafs_range t x
    }
)}"


(* HT when expressed on list of leaves 
lemma leafs_range_rule:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn_leafs k t ti r z lptrs>
leafs_range ti x
<\<lambda>p. (\<exists>\<^sub>A xs1 xs2 lptrs1 lptrs2 ps.
  inner_nodes_assn k t ti r z lptrs *
  leaf_nodes_assn k xs1 r p lptrs1 *
  list_assn leaf_node xs2 (map bplustree.vals xs2) *
  list_assn (is_pfa (2 * k)) (map bplustree.vals xs2) ps *
  leafs_assn ps lptrs2 p z *
  \<up>(concat (map bplustree.vals xs2) = abs_split_range.leafs_range t x) *
  \<up>(lptrs = lptrs1@lptrs2) *
  \<up>(leaf_nodes t = xs1@xs2)
)>\<^sub>t"
sorry
*)

(* much shorter when expressed on the nodes themselves *)
lemma leafs_range_rule:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn_leafs k t ti r z lptrs>
leafs_range ti x
<\<lambda>p. (\<exists>\<^sub>A xs1 lptrs1 lptrs2.
  inner_nodes_assn k t ti r z lptrs *
  leaf_nodes_assn k xs1 r p lptrs1 *
  leaf_nodes_assn k (abs_split_range.leafs_range t x) p z lptrs2 *
  \<up>(lptrs = lptrs1@lptrs2) *
  \<up>(leaf_nodes t = xs1@(abs_split_range.leafs_range t x))
)
>\<^sub>t"
  apply(induction t x rule: abs_split_range.leafs_range.induct)
  subgoal for ks x
    apply(subst leafs_range.simps)
    apply (sep_auto eintros del: exI)
    apply(inst_existentials "[]::'a bplustree list" "[]::'a btnode ref list" "[ti]")
    apply sep_auto+
    done
  subgoal for ts t x
    apply(subst leafs_range.simps)
    (*apply (sep_auto heap add: imp_split_rule)*)
    sorry
  done
  (* TODO *)

(*fun concat_leafs_range where
  "concat_leafs_range t x = (case leafs_range t x of (LNode ks)#list \<Rightarrow> lrange_list x ks @ (concat (map leaves list)))"
*)

definition concat_leafs_range where
"concat_leafs_range ti x = do {
  lp \<leftarrow> leafs_range ti x;
  li \<leftarrow> !(the lp);
  case li of Btleaf xs nxt \<Rightarrow> do {
    arr_it \<leftarrow> imp_lrange_list x xs;
    fla_it \<leftarrow> leaf_elements_adjust (nxt,None) arr_it;
    return fla_it
  }
}"

lemma sorted_less_leaf_nodes: "sorted_less (leaves t) \<Longrightarrow> (LNode ks) \<in> set (leaf_nodes t) \<Longrightarrow> sorted_less ks"
proof(induction t arbitrary: ks rule: leaf_nodes.induct)
  case (1 xs)
  then show ?case by simp
next
  case I: (2 ts t)
  then have "(\<exists>x \<in> set ts. LNode ks \<in> set (leaf_nodes (fst x))) \<or> LNode ks \<in> set (leaf_nodes t)"
    by simp
  then show ?case 
  proof(standard, goal_cases)
    case 1
    then show ?case
      using I
      by (metis (no_types, lifting) in_set_conv_decomp list.simps(9) map_append sorted_leaves_subtrees)
  next
    case 2
    then show ?case
      using I
      by (meson sorted_leaves_induct_last)
  qed
qed

lemmas leaf_elements_adjust_rule = leaf_elements_iter.flatten_it_adjust_rule

lemma concat_leafs_range_rule:
  assumes "k > 0" "root_order k t" "sorted_less (leaves t)"
  shows "<bplustree_assn_leafs k t ti r None lptrs>
concat_leafs_range ti x
<leaf_elements_iter k t ti r (abs_split_range.lrange t x)>\<^sub>t"
  apply(subst concat_leafs_range_def)
  apply(vcg (ss) heap: leafs_range_rule)+
  subgoal using assms by simp
  subgoal using assms by simp
  apply simp
  apply(rule norm_pre_ex_rule)+
  apply(rule hoare_triple_preI)
  apply(auto dest!: mod_starD)
proof(goal_cases)
  case (1 l xs1 lptrs1 lptrs2)
  obtain ks list where *[simp]: "abs_split_range.leafs_range t x = (LNode ks)#list \<and> (LNode ks) \<in> set (leaf_nodes t)"
    using abs_split_range.leafs_range_not_empty by blast
  then obtain r' lptrs2' where [simp]: "lptrs2 = r' # lptrs2'"
    using 1
    by (metis Suc_length_conv leaf_nodes_assn_impl_length)
  have sorted_less_ks: "sorted_less ks"
    using \<open>abs_split_range.leafs_range t x = LNode ks # list \<and> LNode ks \<in> set (leaf_nodes t)\<close> assms(3) imp_split2.sorted_less_leaf_nodes imp_split2_axioms by blast
  then obtain pref where ks_split: "ks = pref @ lrange_list x ks"
  proof (goal_cases)
    case 1
    have "suffix (lrange_list x ks) ks"
      by (metis \<open>sorted_less ks\<close> abs_split_range.lrange_list_req lrange_suffix sorted_less_lrange)
    then have "\<exists>pref. ks = pref @ lrange_list x ks"
      by (meson suffixE)
    then show ?case
      using 1
      by blast
  qed
  show ?case
  proof(cases l)
    case None
    show ?thesis
      apply(rule hoare_triple_preI)
      using None by simp
  next
  case (Some a)
    then show ?thesis
      apply simp
      apply(rule norm_pre_ex_rule)+
      apply vcg
      apply simp
      subgoal for xsi fwd
        apply(cases xsi)
        apply simp
      thm lrange_list_rule
      using sorted_less_ks apply (vcg  heap: lrange_list_rule)
      apply(subst leaf_nodes_assn_flatten)+
      apply(simp)
      apply(rule norm_pre_ex_rule)+
      subgoal for ksia ksin it ps2 ps1
      supply R = fi_rule[
            OF leaf_elements_adjust_rule,
            where F="list_assn leaf_node (leaf_nodes t) (leaf_lists t) *
                     inner_nodes_assn k t ti r None (lptrs1 @ r' # lptrs2') *
                     true"]
        thm R
        supply R' = R[of _ k "map leaves xs1" ps1 "map leaves list" ps2 "(ksia,ksin)"
                         "lptrs1@r'#lptrs2'" r "(fwd,None)" pref "lrange_list x ks" it]
      thm R'
      apply(vcg heap: R')
      apply(subst leaf_iter_assn_def)
      apply simp
      subgoal
        apply(inst_ex_assn "ps1@[(ksia,ksin)]" "lptrs1@[r']" lptrs2')
        apply sep_auto
          subgoal
            apply(rule entails_preI)
            apply(subst leafs_assn_aux_append)
            subgoal by (auto dest!: mod_starD leafs_assn_impl_length)
            subgoal
              apply simp
              apply(inst_ex_assn "Some r'")
              subgoal using 1(1) ks_split by sep_auto
              done
        done
      done
      subgoal
        apply (sep_auto eintros del: exI simp add: leaf_elements_iter_def)
        apply(inst_existentials lptrs)
        apply(subgoal_tac "leaves t = (concat (map leaves xs1) @ pref @ lrange_list x ks @ concat (map leaves list))")
        apply(subgoal_tac "abs_split_range.lrange t x = (lrange_list x ks @ concat (map leaves list))")
        subgoal using 1(1) 1(2) ks_split by sep_auto
        subgoal by (metis \<open>abs_split_range.leafs_range t x = LNode ks # list \<and> LNode ks \<in> set (leaf_nodes t)\<close> abs_split_range.split_range_axioms split_range.leafs_range_pre_lrange)
        subgoal
          using concat_leaf_nodes_leaves[symmetric, of t] 1(1) ks_split
          by auto
        done
      done
    done
  done
  qed
qed


end

end