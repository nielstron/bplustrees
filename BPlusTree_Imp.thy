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

primrec lst :: "'a::heap btnode \<Rightarrow> 'a btnode ref" where
  [sep_dflt_simps]: "lst (Btnode _ t) = t"

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
    * \<up>(r = Some a)
  )" |
  "bplustree_assn k (Node ts t) a r z = 
 (\<exists>\<^sub>A tsi ti tsi' rs.
      a \<mapsto>\<^sub>r Btnode tsi ti
    * bplustree_assn k t ti (last (r#rs)) (last (rs@[z]))
    * is_pfa (2*k) tsi' tsi
    * \<up>(length tsi' = length rs)
    * list_assn ((\<lambda> t (ti,r',z'). bplustree_assn k t (the ti) r' z') \<times>\<^sub>a A_assn) ts (zip (zip (map fst tsi') (zip (butlast (r#rs)) (butlast (rs@[z])))) (map snd tsi'))
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
 (\<exists>\<^sub>A tsi' rs.
    bplustree_assn k t ti (last (r#rs)) (last (rs@[z]))
    * is_pfa (2*k) tsi' tsi
    * \<up>(length tsi' = length rs)
    * list_assn ((\<lambda> t (ti,r',z'). bplustree_assn k t (the ti) r' z') \<times>\<^sub>a A_assn) ts (zip (zip (map fst tsi') (zip (butlast (r#rs)) (butlast (rs@[z])))) (map snd tsi'))
    )" |
  "btnode_assn _ _ _ _ _ = false"

abbreviation "blist_assn k ts tsi'' \<equiv> list_assn ((\<lambda> t (ti,r',z'). bplustree_assn k t (the ti) r' z') \<times>\<^sub>a A_assn) ts tsi'' "

thm bplustree_assn.simps

fun leaf_nodes_assn :: "nat \<Rightarrow> 'a bplustree list \<Rightarrow> 'b btnode ref option \<Rightarrow> 'b btnode ref option \<Rightarrow> assn" where
  "leaf_nodes_assn k ((LNode xs)#lns) (Some r) z = 
 (\<exists>\<^sub>A xsi xsi' fwd.
      r \<mapsto>\<^sub>r Btleaf xsi fwd
    * is_pfa (2*k) xsi' xsi
    * list_assn A_assn xs xsi'
    * leaf_nodes_assn k lns fwd z
  )" | 
  "leaf_nodes_assn k [] r z = \<up>(z = r)" |
  "leaf_nodes_assn _ _ _ _ = false"


fun inner_nodes_assn :: "nat \<Rightarrow> 'a bplustree \<Rightarrow> 'b btnode ref \<Rightarrow> 'b btnode ref option \<Rightarrow> 'b btnode ref option \<Rightarrow> assn" where
  "inner_nodes_assn k (LNode xs) a r z = \<up>(r = Some a)" |
  "inner_nodes_assn k (Node ts t) a r z = 
 (\<exists>\<^sub>A tsi ti tsi' rs.
      a \<mapsto>\<^sub>r Btnode tsi ti
    * bplustree_assn k t ti (last (r#rs)) (last (rs@[z]))
    * is_pfa (2*k) tsi' tsi
    * \<up>(length tsi' = length rs)
    * list_assn ((\<lambda> t (ti,r',z'). bplustree_assn k t (the ti) r' z') \<times>\<^sub>a A_assn) ts (zip (zip (map fst tsi') (zip (butlast (r#rs)) (butlast (rs@[z])))) (map snd tsi'))
    )"


lemma leaf_nodes_assn_aux_append:
   "leaf_nodes_assn k (xs@ys) r z = (\<exists>\<^sub>Al. leaf_nodes_assn k xs r l * leaf_nodes_assn k ys l z)"
  apply(induction k xs r z rule: leaf_nodes_assn.induct)
  apply (sep_auto intro!: ent_iffI)+
  done

lemma butlast_double_Cons: "butlast (x#y#xs) = x#(butlast (y#xs))"
  by auto

lemma last_double_Cons: "last (x#y#xs) = (last (y#xs))"
  by auto


declare last.simps[simp del] butlast.simps[simp del]
declare mult.left_assoc[simp add]
lemma bplustree_leaf_nodes:
  "bplustree_assn k t ti r z * true \<Longrightarrow>\<^sub>A leaf_nodes_assn k (leaf_nodes t) r z * true"
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
    have *: "
        length tsi's = length rss \<Longrightarrow>
        length rss = length tss \<Longrightarrow>
        set tsi's \<subseteq> set tsi' \<Longrightarrow>
        set rss \<subseteq> set rs \<Longrightarrow>
        set tss \<subseteq> set ts \<Longrightarrow>
       bplustree_assn k t ti (last (ra # rss)) z * 
       blist_assn k tss
        (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) rss)) (separators tsi's)) * true \<Longrightarrow>\<^sub>A
       leaf_nodes_assn k (concat (map (leaf_nodes \<circ> fst) tss) @ leaf_nodes t) ra z * true"
      for rss tsi's tss
    proof (induct arbitrary: ra rule: list_induct3)
      case (Nil r)
      then show ?case
        apply sep_auto
        using 2(1)[of ti r]
      apply (simp add: last.simps butlast.simps)
      done
    next
      case (Cons subsepi tsi's subleaf rss subsep tss r'')
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
        moreover obtain t2 where "((fst subsepi, r, subleaf),t2::'b) \<in> set
            (zip (zip [fst subsepi]
                   (zip (butlast [r, subleaf]) (butlast [subleaf, z])))
              [t2])"
          by (simp add: butlast.simps)
        ultimately  show ?case
          using
           Cons(3)[of subleaf]
           "2.IH"(2)[of "(sub,sep)" "((fst subsepi, (r, subleaf)),t2)" "[(fst subsepi, t2)]" "[subleaf]" "fst subsepi" "(r,subleaf)" r subleaf r'']
          apply auto
          thm mult.commute
          thm star_aci
          apply(subst mult.commute)
          supply R=ent_star_mono_true[where
A="bplustree_assn k sub (the (fst subsepi)) r'' subleaf * true" and A'="leaf_nodes_assn k (leaf_nodes sub) r'' subleaf"
and B="bplustree_assn k t ti (last (subleaf # rss)) z *
    A_assn sep (snd subsepi) *
    blist_assn k tss
     (zip (zip (subtrees tsi's) (zip (butlast (subleaf # rss)) rss)) (separators tsi's)) *
    true"
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
      apply(rule entails_preI)
        using 1 apply (auto dest!: mod_starD list_assn_len)
        using *[of tsi' rs ts, simplified]
        by (smt (z3) assn_aci(10) assn_times_comm ent_true_drop(1))
  qed
qed
declare last.simps[simp add] butlast.simps[simp add]
declare mult.left_assoc[simp del]

declare last.simps[simp del] butlast.simps[simp del]
declare mult.left_assoc[simp add]
lemma bplustree_leaf_nodes:
  "bplustree_assn k t ti r z \<Longrightarrow>\<^sub>A leaf_nodes_assn k (leaf_nodes t) r z * inner_nodes_assn k t ti r z"
  oops
(*
proof(induction arbitrary: r rule: bplustree_assn.induct)
  case (1 k xs a r z)
  then show ?case
    by (sep_auto)
next
  case (2 k ts t a r z ra)
  then show ?case
    apply(sep_auto)
  proof (goal_cases)
    case (1 a b ti tsi' rs)
    have *: "
        length tsi's = length rss \<Longrightarrow>
        length rss = length tss \<Longrightarrow>
        set tsi's \<subseteq> set tsi' \<Longrightarrow>
        set rss \<subseteq> set rs \<Longrightarrow>
        set tss \<subseteq> set ts \<Longrightarrow>
       bplustree_assn k t ti (last (ra # rss)) z * 
       blist_assn k tss
        (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) rss)) (separators tsi's)) * true \<Longrightarrow>\<^sub>A
       leaf_nodes_assn k (concat (map (leaf_nodes \<circ> fst) tss) @ leaf_nodes t) ra z * true"
      for rss tsi's tss
    proof (induct arbitrary: ra rule: list_induct3)
      case (Nil r)
      then show ?case
        apply sep_auto
        using 2(1)[of ti r]
      apply (simp add: last.simps butlast.simps)
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
and B="bplustree_assn k t ti (last (subleaf # rss)) z *
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
      apply(rule entails_preI)
        using 1 apply (auto dest!: mod_starD list_assn_len)
        using *[of tsi' rs ts, simplified]
        by (smt (z3) assn_aci(10) assn_times_comm ent_true_drop(1))
  qed
qed
declare last.simps[simp add] butlast.simps[simp add]
declare mult.left_assoc[simp del]
*)

subsection "Iterator"

partial_function (heap) leaf_iter_init :: "'b btnode ref \<Rightarrow> 'b btnode ref Heap"
  where
    "leaf_iter_init p = do {
  node \<leftarrow> !p;
  (case node of
    Btleaf _ _ \<Rightarrow> do { return p } |
    Btnode tsi ti \<Rightarrow> do {
        s \<leftarrow> pfa_get tsi 0;
        let (sub,sep) = s in do { 
          leaf_iter_init (the sub)
        }
  }
)}"

declare last.simps[simp del] butlast.simps[simp del]
lemma obtain_first_leaf_rule:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn k t ti r z>
  leaf_iter_init ti
  <\<lambda>u. bplustree_assn k t ti r z * \<up>(Some u = r)>\<^sub>t"
  using assms
proof(induction t arbitrary: ti z)
  case (LNode x)
  then show ?case
    apply(subst leaf_iter_init.simps)
    apply (sep_auto dest!: mod_starD)
    done
next
  case (Node ts t)
  then obtain sub sep tts where Cons: "ts = (sub,sep)#tts"
    apply(cases ts) by auto
  then show ?case 
    apply(subst leaf_iter_init.simps)
    apply(rule hoare_triple_preI)
    apply (sep_auto simp add: last.simps butlast.simps)
    subgoal for a b aa ba ti tsi' rs ab bb tiaa tsi'a rsa ac bc
    using "Node.IH"(1)[of "(sub,sep)" sub]
    apply sep_auto
    sorry
  done
qed
declare last.simps[simp add] butlast.simps[simp add]

lemma obtain_iter_rule:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn k t ti r z>
  leaf_iter_init ti
  <\<lambda>u. leaf_nodes_assn k (leaf_nodes t) (Some u) z>\<^sub>t"
  using assms
  using bplustree_leaf_nodes[of k t ti r z]
  by (sep_auto heap add: obtain_first_leaf_rule)

definition leaf_iter_next where
"leaf_iter_next r = do {
  p \<leftarrow> !(the r);
  return (fwd p)
}"

lemma leaf_iter_next_rule: "<leaf_nodes_assn k (x#xs) r z>
      leaf_iter_next r <\<lambda>n. leaf_nodes_assn k [x] r n * leaf_nodes_assn k xs n z>"
  apply(subst leaf_iter_next_def)
  apply(cases r; cases x)
  apply(sep_auto)+
  done

definition leaf_iter_assn where "leaf_iter_assn k xs r z xs2 n = 
  (\<exists>\<^sub>Axs1. \<up>(xs = xs1@xs2) * leaf_nodes_assn k xs1 r n * leaf_nodes_assn k xs2 n z)" 

lemma "<leaf_iter_assn k xs r z (x#xs2) n>
leaf_iter_next n
<\<lambda>n'. leaf_iter_assn k xs r z xs2 n'>"
  unfolding leaf_iter_assn_def
  apply(sep_auto heap add: leaf_iter_next_rule simp add: leaf_nodes_assn_aux_append)
  done





end

end