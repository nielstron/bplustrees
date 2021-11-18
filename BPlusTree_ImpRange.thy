theory BPlusTree_ImpRange
imports
  BPlusTree_Range
  BPlusTree_Iter
  BPlusTree_ImpSplitSpec
begin

abbreviation "blist_leafs_assn k \<equiv> list_assn ((\<lambda> t (ti,r',z',lptrs). bplustree_assn_leafs k t (the ti) r' z' lptrs) \<times>\<^sub>a id_assn)"

context imp_split_tree
begin

lemma list_induct5 [consumes 4, case_names Nil Cons]:
  "length xs = length ys \<Longrightarrow> length ys = length zs \<Longrightarrow> length zs = length ws \<Longrightarrow> length ws = length vs \<Longrightarrow>
   P [] [] [] [] [] \<Longrightarrow> (\<And>x xs y ys z zs w ws v vs. length xs = length ys \<Longrightarrow>
   length ys = length zs \<Longrightarrow> length zs = length ws \<Longrightarrow> length ws = length vs \<Longrightarrow> P xs ys zs ws vs \<Longrightarrow>
   P (x#xs) (y#ys) (z#zs) (w#ws) (v#vs)) \<Longrightarrow> P xs ys zs ws vs"
proof (induct xs arbitrary: ys zs ws vs)
  case Nil then show ?case by simp
next
  case (Cons x xs ys zs ws) then show ?case by ((cases ys, simp_all), (cases zs,simp_all), (cases ws, simp_all)) (cases vs, simp_all)
qed

declare butlast.simps[simp del] last.simps[simp del]
lemma blist_assn_extract_leafs: "
length ts = length tsi \<Longrightarrow>
length tsi = length rs \<Longrightarrow>
blist_assn k ts (zip (zip (map fst tsi) (zip (butlast (r#rs)) rs)) (map snd tsi))
=
(\<exists>\<^sub>Aspl. blist_leafs_assn k ts (zip (zip (map fst tsi) (zip (butlast (r#rs)) (zip rs spl))) (map snd tsi)) * \<up>(length spl = length rs))"
proof(induction arbitrary: r rule: list_induct3)
  case Nil
  then show ?case
    apply(intro ent_iffI)
    by sep_auto+
next
  case (Cons x xs y ys z zs r)
  show ?case
    using Cons.hyps
    using Cons.hyps
  apply (sep_auto simp add: butlast_double_Cons last_double_Cons)
    supply R= Cons.IH[simplified, of z]
    thm R
    apply(subst R)
  proof(intro ent_iffI, goal_cases)
    case 1
    then show ?case
    apply(sep_auto eintros del: exI simp add: prod_assn_def bplustree_extract_leafs split!: prod.splits)
      subgoal for _ _ spl lptrs
      apply(inst_existentials "lptrs#spl")
        apply auto
        done
      done
  next
    case 2
    then show ?case
    apply(sep_auto eintros del: exI)
      subgoal for spl
      apply(cases spl)
        apply simp
        subgoal for hdspl tlspl
          apply(inst_existentials tlspl)
          apply (auto simp add: prod_assn_def bplustree_extract_leafs split!: prod.splits)
          done
        done
      done
    qed
  qed
declare butlast.simps[simp add] last.simps[simp add]

declare butlast.simps[simp del] last.simps[simp del]
lemma imp_split_leafs_rule[sep_heap_rules]: "sorted_less (separators ts) \<Longrightarrow>
  length tsi = length rs \<Longrightarrow>
  length spl = length rs + 1 \<Longrightarrow>
  tsi'' = zip (zip (map fst tsi) (zip (butlast (r#rs)) (zip (butlast (rs@[z])) (butlast spl)))) (map snd tsi) \<Longrightarrow>
 <is_pfa c tsi (a,n) 
  * blist_leafs_assn k ts tsi'' > 
    imp_split (a,n) p 
  <\<lambda>i. 
    is_pfa c tsi (a,n)
    * blist_leafs_assn k ts tsi''
    * \<up>(split_relation ts (split ts p) i)>\<^sub>t"
proof(rule hoare_triple_preI, goal_cases) 
  case 1
  have "length tsi'' = length rs"
    using 1 by auto
  then have *: "length ts = length tsi''"
    using 1 by (auto dest!: mod_starD list_assn_len)
  then have **: "length ts = length tsi"
    using 1 by (auto dest!: mod_starD list_assn_len)
  note R = imp_split_rule[of ts tsi rs "zip (zip (subtrees tsi) (zip (butlast (r # rs)) rs)) (separators tsi)" r]
  note blist_assn_extract_leafs[OF ** 1(2), of k r]
  find_theorems "<_> _ <_>" "_ \<Longrightarrow>\<^sub>A _"
  then show ?thesis
    using R 1
    apply simp
  sorry
qed

end

(* Adding an actual range iterator based on the normal iterator
is trivial (just forward until we reach the first element \<ge> and stop
as soon as we have an element <)
We now try to implement a search for the first element of the range efficiently
 *)
subsection "The imperative split locale"


locale imp_split_range = abs_split_range: split_range split lrange_list + imp_split_tree split imp_split
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

lemma leaf_nodes_assn_split2:
"length xs = length xsi \<Longrightarrow>
  leaf_nodes_assn k (xs @ ys) r z (xsi @ ysi) = (\<exists>\<^sub>Al. leaf_nodes_assn k xs r l xsi * leaf_nodes_assn k ys l z ysi)"
proof(induction arbitrary: r rule: list_induct2)
  case (Nil r)
  then show ?case
    apply(cases r; cases ys)
    apply clarsimp_all
      subgoal
        apply(rule ent_iffI)
        by (sep_auto dest!: leaf_nodes_assn_impl_length)+
      subgoal
        apply(rule ent_iffI)
        by (sep_auto dest!: leaf_nodes_assn_impl_length)+
      subgoal
        apply(rule ent_iffI)
        by (sep_auto dest!: leaf_nodes_assn_impl_length)+
    subgoal for _ t _
      apply(cases t)
      subgoal
      apply clarsimp_all
          apply(rule ent_iffI)
          by (sep_auto dest!: leaf_nodes_assn_impl_length)+
        subgoal by clarsimp
        done
    done
next
  case (Cons x xs xi xsi r)
  show ?case
    apply(cases r; cases x)
    apply clarsimp_all
        apply(rule ent_iffI)
    subgoal for _ ts
      apply(subst Cons.IH)
      apply simp
      apply(rule ent_ex_preI)+
      subgoal for tsi fwd l
        apply(inst_ex_assn l tsi fwd)
        apply sep_auto
        done
      done
    subgoal for _ ts
      apply(subst Cons.IH)
      apply(simp)
      apply(rule ent_ex_preI)+
      subgoal for l tsi fwd
        apply(inst_ex_assn tsi fwd l)
        apply sep_auto
      done
    done
  done
qed

lemma eq_preI: "(\<forall>h. h \<Turnstile> P \<longrightarrow> Q = Q') \<Longrightarrow> P * Q = P * Q'"
  apply(intro ent_iffI)
  using entails_def mod_starD apply blast+
  done

lemma simp_map_temp: "(map (leaf_nodes \<circ> fst)) = map (\<lambda>a. (leaf_nodes (fst a)))"
  by (meson comp_apply)

declare last.simps[simp del] butlast.simps[simp del]
lemma blist_leafs_assn_split:
"   length tsi' = length rrs \<Longrightarrow>
    length rrs = length ts \<Longrightarrow>
    length ts = length spl \<Longrightarrow>
    (blist_leafs_assn k ts
      (zip (zip (subtrees tsi') (zip (butlast (r # rrs)) (zip rrs spl))) (separators tsi'))
      =
     list_assn ((\<lambda>t (ti, r', x, y). inner_nodes_assn k t (the ti) r' x y) \<times>\<^sub>a id_assn) ts
      (zip (zip (subtrees tsi') (zip (butlast (r # rrs)) (zip rrs spl))) (separators tsi')) *
     leaf_nodes_assn k (concat (map (leaf_nodes \<circ> fst) ts)) r (last (r#rrs)) (concat spl)
) "
proof(induction tsi' rrs ts spl arbitrary: r rule: list_induct4)
  case Nil
  then show ?case
    by (sep_auto simp add: last.simps butlast.simps)
next
  case (Cons x xs y ys z zs w ws r)
  show ?case
    using Cons.hyps Cons.prems
    apply(clarsimp simp add: butlast_double_Cons last_double_Cons)
    apply(clarsimp simp add: prod_assn_def split!: prod.splits)
        apply(simp add: bplustree_leaf_nodes_sep)
    apply(subst Cons.IH[of y])
    subgoal for sub sep
      apply(intro ent_iffI)
      subgoal
      apply(rule entails_preI)
    apply(subst leaf_nodes_assn_split2)
        subgoal by (auto dest!: mod_starD leaf_nodes_assn_impl_length)
        apply (simp add: simp_map_temp)
        apply(inst_ex_assn y)
        apply(sep_auto)
        done
      subgoal
      apply(rule entails_preI)
        apply(cases zs)
      proof(goal_cases)
        case 1
        then show ?thesis
          by (sep_auto simp add: last.simps)
      next
        case (2 _ a list)
        then show ?thesis
          apply(cases xs, simp)
          apply(cases ys, simp)
          apply(cases ws, simp)
          subgoal for x' xs' y'' ys'' w' ws'
          apply(clarsimp simp add: butlast_double_Cons last_double_Cons)
          apply(clarsimp simp add: prod_assn_def split!: prod.splits)
            subgoal for sub' sep'
            apply(subgoal_tac "y = Some (hd w')")
            prefer 2
            subgoal by (auto dest!: mod_starD inner_nodes_assn_hd)
          apply sep_auto
    apply(subst leaf_nodes_assn_split[where yi="the y" and ysr="tl w'@concat ws'"])
        find_theorems inner_nodes_assn length
        subgoal by (auto dest!: mod_starD inner_nodes_assn_leafs_len_imp)
        apply(subgoal_tac "w' \<noteq> []")
        prefer 2
          subgoal by (auto dest!: mod_starD inner_nodes_assn_leafs_len_imp simp add: leaf_nodes_not_empty)
          subgoal by simp
        apply (simp add: simp_map_temp)
        apply(sep_auto)
        done
      done
    done
    qed
  done
  done
qed
declare last.simps[simp add] butlast.simps[simp add]



(* much shorter when expressed on the nodes themselves *)
declare last.simps[simp del] butlast.simps[simp del]
lemma leafs_range_rule:
  assumes "k > 0" "root_order k t" "Laligned t u"
  shows "<bplustree_assn_leafs k t ti r z lptrs >
leafs_range ti x
<\<lambda>p. (\<exists>\<^sub>A xs1 lptrs1 lptrs2.
  inner_nodes_assn k t ti r z lptrs *
  leaf_nodes_assn k xs1 r p lptrs1 *
  leaf_nodes_assn k (abs_split_range.leafs_range t x) p z lptrs2 *
  \<up>(lptrs = lptrs1@lptrs2) *
  \<up>(leaf_nodes t = xs1@(abs_split_range.leafs_range t x))
)
>\<^sub>t"
  using assms
proof(induction t x arbitrary: ti r z u lptrs rule: abs_split_range.leafs_range.induct)
  case (1 ks x)
  then show ?case
    apply(subst leafs_range.simps)
    apply (sep_auto eintros del: exI)
    apply(inst_existentials "[]::'a bplustree list" "[]::'a btnode ref list" "[ti]")
    apply sep_auto+
    done
next
  case (2 ts t x ti r z u lptrs)
  then have "sorted_less (separators ts)"
    by (meson Laligned_sorted_separators sorted_wrt_append)
  obtain ls rs where split_pair: "split ts x = (ls,rs)"
    by (meson surj_pair)
  show ?case
  proof(cases rs)
    case Nil
    then show ?thesis
      using split_pair
    apply(subst leafs_range.simps)
    apply simp
    apply(vcg)
    apply simp
    thm imp_split_rule
    subgoal for tsi tii tsi' rrs spl
      apply(cases tsi)
      subgoal for tsia tsin
    supply R = imp_split_leafs_rule[of ts tsi' rrs spl "(zip (zip (subtrees tsi') (zip (butlast (r # rrs)) (zip rrs (butlast spl))))
        (separators tsi'))" r z]
      thm R
    apply (vcg heap add: R)
      subgoal using \<open>sorted_less (separators ts)\<close> by linarith
      subgoal by simp
      subgoal by simp
      subgoal by (simp add: butlast.simps)
      apply(rule hoare_triple_preI)
      apply(vcg)
(* discard wrong path *)
      subgoal by (auto simp add: split_relation_alt is_pfa_def dest!:  mod_starD list_assn_len)[]
(* correct path *)
      subgoal
      supply R = "2.IH"(1)[OF split_pair[symmetric] Nil, of u]
      thm R
      apply(vcg heap add: R)
      subgoal using "2.prems" by simp
      subgoal 
      using "2.prems"(2) assms(1) order_impl_root_order root_order.simps(2) by blast
      subgoal 
      using "2.prems"(3) Lalign_Llast by blast
    apply (sep_auto eintros del: exI)
    subgoal for y xs1 lptrs1 lptrs2
      apply(inst_existentials "concat (map (leaf_nodes \<circ> fst) ts) @ xs1" "(concat (butlast spl)) @ lptrs1" lptrs2
                              tsia tsin tii tsi' "(zip (zip (subtrees tsi') (zip (butlast (r # rrs)) (zip rrs (butlast spl))))
            (separators tsi'))" rrs spl)
      subgoal
        apply(auto)
        by (metis Suc_neq_Zero append.assoc append_Nil append_butlast_last_id append_same_eq concat.simps(1) concat.simps(2) concat_append list.size(3))
      subgoal
        apply sep_auto
        apply(subst blist_leafs_assn_split)
        subgoal by simp
        subgoal sorry
        subgoal sorry
        apply(subst leaf_nodes_assn_split2)
        subgoal sorry
        apply (sep_auto eintros del: exI)
        apply(inst_existentials "(last (r # rrs))")
        apply (sep_auto)
        done
      done
    done
  done
  done
  done
  next
    case (Cons a list)
    then show ?thesis sorry
  qed
qed
declare last.simps[simp add] butlast.simps[simp add]

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

lemma concat_leafs_range_rule_help:
  assumes "k > 0" "root_order k t" "sorted_less (leaves t)" "Laligned t u"
  shows "<bplustree_assn_leafs k t ti r None lptrs>
concat_leafs_range ti x
<leaf_elements_iter k t ti r (abs_split_range.lrange t x)>\<^sub>t"
  apply(subst concat_leafs_range_def)
  apply(vcg (ss) heap: leafs_range_rule[of k t u])+
  subgoal using assms by simp
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
    using \<open>abs_split_range.leafs_range t x = LNode ks # list \<and> LNode ks \<in> set (leaf_nodes t)\<close> assms(3) sorted_less_leaf_nodes imp_split_range_axioms by blast
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
        apply(inst_existentials "lptrs1@lptrs2")
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

lemma concat_leafs_range_rule:
  assumes "k > 0" "root_order k t" "sorted_less (leaves t)" "Laligned t u"
  shows "<bplustree_assn k t ti r None>
concat_leafs_range ti x
<leaf_elements_iter k t ti r (abs_split_range.lrange t x)>\<^sub>t"
  find_theorems bplustree_assn_leafs
  apply(simp add: bplustree_extract_leafs)
  using assms apply(sep_auto heap add: concat_leafs_range_rule_help)
  done

end

end