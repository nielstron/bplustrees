theory BPlusTree_Imp
  imports
    BPlusTree
    Partially_Filled_Array
    Basic_Assn
    Inst_Ex_Assn
begin

section "Imperative B-tree Definition"

text "The heap data type definition. Anything stored on the heap always contains data,
leafs are represented as None."

(* Option as we need a default for non-initializeed entries *)
datatype 'a btnode =
  Btnode "('a btnode ref option *'a) pfarray" "'a btnode ref" |
  Btleaf "'a pfarray" "'a btnode ref option"


text \<open>Selector Functions\<close>
primrec kvs :: "'a::heap btnode \<Rightarrow> ('a btnode ref option * 'a) pfarray" where
  [sep_dflt_simps]: "kvs (Btnode ts _) = ts"

primrec last :: "'a::heap btnode \<Rightarrow> 'a btnode ref" where
  [sep_dflt_simps]: "last (Btnode _ t) = t"

primrec vals :: "'a::heap btnode \<Rightarrow> 'a pfarray" where
  [sep_dflt_simps]: "vals (Btleaf ts _) = ts"

primrec fwd :: "'a::heap btnode \<Rightarrow> 'a btnode ref option" where
  [sep_dflt_simps]: "fwd (Btleaf _ t) = t"

text \<open>Encoding to natural numbers, as required by Imperative/HOL\<close>
  (* Note: should also work using the package "Deriving" *)
fun
  btnode_encode :: "'a::heap btnode \<Rightarrow> nat"
  where
    "btnode_encode (Btnode ts t) = to_nat (Some ts, Some t, None::'a pfarray option, None::'a btnode ref option option)" |
    "btnode_encode (Btleaf ts t) = to_nat (None::('a btnode ref option * 'a) pfarray option, None::'a btnode ref option, Some ts, Some t)"

instance btnode :: (heap) heap
  apply (rule heap_class.intro)
   apply (rule countable_classI [of "btnode_encode"])
  apply(elim btnode_encode.elims)
  apply auto
  ..

text "The refinement relationship to abstract B-trees."

text "The idea is: a refines the given node of degree k where the first leaf node of the subtree
of a is r and the forward pointer in the last leaf node is z"

find_theorems list_assn
find_theorems id_assn

fun leaf_nodes where
"leaf_nodes (LNode xs) = [LNode xs]" |
"leaf_nodes (Node ts t) = concat (map leaf_nodes (subtrees ts)) @ leaf_nodes t"

locale bplustree =
  fixes A :: "'a \<Rightarrow> ('b::heap) \<Rightarrow> bool"
begin


definition "A_assn x y \<equiv> \<up>(A x y)"


fun bplustree_assn :: "nat \<Rightarrow> 'a bplustree \<Rightarrow> 'b btnode ref \<Rightarrow> 'b btnode ref option \<Rightarrow> 'b btnode ref option \<Rightarrow> assn" where
  "bplustree_assn k (LNode xs) a r z = 
 (\<exists>\<^sub>A xsi xsi' fwd.
      a \<mapsto>\<^sub>r Btleaf xsi fwd
    * is_pfa (2*k) xsi' xsi
    * list_assn A_assn xs xsi'
    * \<up>(fwd = z)
    * \<up>(the r = a)
  )" |
  "bplustree_assn k (Node ts t) a r z = 
 (\<exists>\<^sub>A tsi ti tsi' tsi'' rs.
      a \<mapsto>\<^sub>r Btnode tsi ti
    * bplustree_assn k t ti (List.last (r#rs)) (List.last (rs@[z]))
    * is_pfa (2*k) tsi' tsi
    * \<up>(length tsi' = length rs)
    * \<up>(tsi'' = zip (zip (map fst tsi') (zip (butlast (r#rs)) (butlast (rs@[z])))) (map snd tsi'))
    * list_assn ((\<lambda> t (ti,r',z'). bplustree_assn k t (the ti) r' z') \<times>\<^sub>a A_assn) ts tsi''
    )"

find_theorems "map _ (zip _ _)"
(*
rs = the list of pointers to the leaves of this subtree
TODO how to weave rs@[z] and a#rs into the list_assn most elegantly
*)

text "With the current definition of deletion, we would
also need to directly reason on nodes and not only on references
to them."

fun btnode_assn :: "nat \<Rightarrow> 'a bplustree \<Rightarrow> 'b btnode \<Rightarrow> 'b btnode ref option \<Rightarrow> 'b btnode ref option \<Rightarrow> assn" where
  "btnode_assn k (LNode xs) (Btleaf xsi zi) r z = 
 (\<exists>\<^sub>A xsi xsi' zi.
    is_pfa (2*k) xsi' xsi
    * list_assn A_assn xs xsi'
    * \<up>(zi = z)
  )" |
  "btnode_assn k (Node ts t) (Btnode tsi ti) r z = 
 (\<exists>\<^sub>A tsi' tsi'' rs.
    bplustree_assn k t ti (List.last (r#rs)) (List.last (rs@[z]))
    * is_pfa (2*k) tsi' tsi
    * \<up>(length tsi' = length rs)
    * \<up>(tsi'' = zip (zip (map fst tsi') (zip (butlast (r#rs)) (butlast (rs@[z])))) (map snd tsi'))
    * list_assn ((\<lambda> t (ti,r',z'). bplustree_assn k t (the ti) r' z') \<times>\<^sub>a A_assn) ts tsi''
    )" |
  "btnode_assn _ _ _ _ _ = false"

abbreviation "blist_assn k ts tsi'' \<equiv> list_assn ((\<lambda> t (ti,r',z'). bplustree_assn k t (the ti) r' z') \<times>\<^sub>a A_assn) ts tsi'' "

fun leaf_nodes_assn :: "nat \<Rightarrow> 'a bplustree list \<Rightarrow> 'b btnode ref option \<Rightarrow> 'b btnode ref option \<Rightarrow> assn" where
  "leaf_nodes_assn k ((LNode xs)#lns) r z = 
 (\<exists>\<^sub>A xsi xsi' fwd.
      the r \<mapsto>\<^sub>r Btleaf xsi fwd
    * is_pfa (2*k) xsi' xsi
    * list_assn A_assn xs xsi'
    * leaf_nodes_assn k lns fwd z
  )" | 
  "leaf_nodes_assn k [] r z = \<up>(z = r)" |
  "leaf_nodes_assn _ _ _ _ = false"

lemma leaf_nodes_assn_aux_append: "leaf_nodes_assn k (xs@ys) r z = (\<exists>\<^sub>Al. leaf_nodes_assn k xs r l * leaf_nodes_assn k ys l z)"
  apply(induction xs arbitrary: r)
  apply (sep_auto intro!: ent_iffI)
  subgoal for a xs r
    apply(cases a)
    apply (sep_auto intro!: ent_iffI)+
    done
  done

lemma butlast_double_Cons: "butlast (x#y#xs) = x#(butlast (y#xs))"
  by auto

lemma last_double_Cons: "List.last (x#y#xs) = (List.last (y#xs))"
  by auto

lemma entails_preI: "(\<And>h. h \<Turnstile> P \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q) \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q"
  unfolding entails_def
  by auto

lemma ent_true_drop_true: 
  "P*true\<Longrightarrow>\<^sub>AQ*true \<Longrightarrow> P*R*true\<Longrightarrow>\<^sub>AQ*true"
  using assn_aci(10) ent_true_drop(1) by presburger

declare List.last.simps[simp del] butlast.simps[simp del]
declare mult.left_assoc[simp add]

lemma "bplustree_assn k t ti r z * true \<Longrightarrow>\<^sub>A leaf_nodes_assn k (leaf_nodes t) r z * true"
proof(induction arbitrary: r rule: bplustree_assn.induct)
  case (1 k xs a r z)
  then show ?case
    by (sep_auto)
next
  case (2 k ts t a r z ra)
  show ?case
    apply(sep_auto)
  proof (goal_cases)
    case (1 a b ti tsi' rs)
(* FIX blist_assn ... \<Longrightarrow> leaf_nodes_assn *)
    have *: "
        length tsi's = length rss \<Longrightarrow>
        length rss = length tss \<Longrightarrow>
        set tsi's \<subseteq> set tsi' \<Longrightarrow>
        set rss \<subseteq> set rs \<Longrightarrow>
        set tss \<subseteq> set ts \<Longrightarrow>
       bplustree_assn k t ti (List.last (ra # rss)) z * 
       blist_assn k tss
        (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) rss)) (separators tsi's)) * true \<Longrightarrow>\<^sub>A
       leaf_nodes_assn k (concat (map (leaf_nodes \<circ> fst) tss) @ leaf_nodes t) ra z * true"
      for rss tsi's tss
    proof (induct arbitrary: ra rule: list_induct3)
      case (Nil r)
      then show ?case
        apply sep_auto
        using 2(1)[of ti r]
      apply (simp add: List.last.simps butlast.simps)
      done
    next
      case (Cons subsepi tsi's subleaf rss subsep tss r)
      show ?case
        apply (sep_auto
                simp add: butlast_double_Cons last_double_Cons)
        apply(subst prod_assn_def)
        apply(simp split!: prod.splits add: mult.left_assoc)
        apply(subst leaf_nodes_assn_aux_append)
        apply simp
        apply(inst_ex_assn subleaf)
      proof (goal_cases)
        case (1 sub sep)
        have "(sub,sep) \<in> set ts"
          using "1" Cons.prems(3) by force
        moreover have "set tsi's \<subseteq> set tsi' \<and> set rss \<subseteq> set rs \<and> set tss \<subseteq> set ts"
          by (meson Cons.prems set_subset_Cons subset_trans)
        moreover obtain temp1 temp2 where "((fst subsepi, (temp1:: 'b btnode ref option), subleaf), (temp2::'b)) \<in> set [((fst subsepi, temp1, subleaf), temp2)]"
          by auto
        ultimately  show ?case
          using
           Cons(3)[of subleaf]
           "2.IH"(2)[of "(sub,sep)"
                "((fst subsepi, (temp1, subleaf)),temp2)" "[((fst subsepi, (temp1, subleaf)),temp2)]"
                "fst subsepi" "(temp1, subleaf)" temp1 subleaf r]
          apply auto
          thm mult.commute
          thm star_aci
          apply(subst mult.commute)
          supply R=ent_star_mono_true[where
A="bplustree_assn k sub (the (fst subsepi)) r subleaf * true" and A'="leaf_nodes_assn k (leaf_nodes sub) r subleaf"
and B="bplustree_assn k t ti (List.last (subleaf # rss)) z *
    A_assn sep (snd subsepi) *
    blist_assn k tss
     (zip (zip (subtrees tsi's) (zip (butlast (subleaf # rss)) rss)) (separators tsi's)) * true"
and B'="leaf_nodes_assn k (concat (map (\<lambda>a. leaf_nodes (fst a)) tss) @ leaf_nodes t) subleaf z"
          ,simplified]
          thm R
          apply(rule R)
          subgoal
            by simp
          subgoal
            apply(subst mult.commute, simp)
            apply(rule ent_true_drop_true)
            apply(subst mult.commute, simp)
            done
      done
      qed
    qed
    show ?case
      apply(rule entails_preI[where Q="leaf_nodes_assn k (concat (map (leaf_nodes \<circ> fst) ts) @ leaf_nodes t) ra z * true"])
        using 1 apply (sep_auto dest!: mod_starD list_assn_len)
        using *[of tsi' rs ts, simplified]
        by (smt (z3) assn_aci(10) assn_times_comm ent_true_drop(1))
  qed
qed
declare List.last.simps[simp add] butlast.simps[simp add]
declare mult.left_assoc[simp del]
thm bplustree_assn.simps
end

end