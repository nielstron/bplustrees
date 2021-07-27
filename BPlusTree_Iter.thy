theory BPlusTree_Iter
  imports
     BPlusTree_Imp
    "HOL-Real_Asymp.Inst_Existentials"
    "Separation_Logic_Imperative_HOL.Imp_List_Spec"
begin

context bplustree
begin


fun leaf_nodes_assn :: "nat \<Rightarrow> 'a bplustree list \<Rightarrow> 'b btnode ref option \<Rightarrow> 'b btnode ref option \<Rightarrow> assn" where
  "leaf_nodes_assn k ((LNode xs)#lns) (Some r) z = 
 (\<exists>\<^sub>A xsi xsi' fwd.
      r \<mapsto>\<^sub>r Btleaf xsi fwd
    * is_pfa (2*k) xsi' xsi
    * list_assn A_assn xs xsi'
    * leaf_nodes_assn k lns fwd z
  )" | 
  "leaf_nodes_assn k [] r z = \<up>(r = z)" |
  "leaf_nodes_assn _ _ _ _ = false"


fun inner_nodes_assn :: "nat \<Rightarrow> 'a bplustree \<Rightarrow> 'b btnode ref \<Rightarrow> 'b btnode ref option \<Rightarrow> 'b btnode ref option \<Rightarrow> assn" where
  "inner_nodes_assn k (LNode xs) a r z = \<up>(r = Some a)" |
  "inner_nodes_assn k (Node ts t) a r z = 
 (\<exists>\<^sub>A tsi ti tsi' tsi'' rs.
      a \<mapsto>\<^sub>r Btnode tsi ti
    * bplustree_assn k t ti (last (r#rs)) (last (rs@[z]))
    * is_pfa (2*k) tsi' tsi
    * \<up>(length tsi' = length rs)
    * \<up>(tsi'' = zip (zip (map fst tsi') (zip (butlast (r#rs)) (butlast (rs@[z])))) (map snd tsi'))
    * list_assn ((\<lambda> t (ti,r',z'). bplustree_assn k t (the ti) r' z') \<times>\<^sub>a A_assn) ts tsi''
    )"


lemma leaf_nodes_assn_aux_append:
   "leaf_nodes_assn k (xs@ys) r z = (\<exists>\<^sub>Al. leaf_nodes_assn k xs r l * leaf_nodes_assn k ys l z)"
  apply(induction k xs r z rule: leaf_nodes_assn.induct)
  apply(sep_auto intro!: ent_iffI)+
  done



declare last.simps[simp del] butlast.simps[simp del]
declare mult.left_assoc[simp add]
lemma bplustree_leaf_nodes_help:
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

lemma bplustree_leaf_nodes:
  "bplustree_assn k t ti r z \<Longrightarrow>\<^sub>A leaf_nodes_assn k (leaf_nodes t) r z * true"
  apply(rule rem_true)
  using bplustree_leaf_nodes_help by simp

fun leaf_node:: "nat \<Rightarrow> 'a bplustree \<Rightarrow> 'b pfarray \<Rightarrow> assn" where
  "leaf_node k (LNode xs) xsi = 
 (\<exists>\<^sub>A xsi'.
      is_pfa (2*k) xsi' xsi
    * list_assn A_assn xs xsi'
  )" |
  "leaf_node _ _ _ = false"

fun leafs_assn :: "'b pfarray list \<Rightarrow> 'b btnode ref option \<Rightarrow> 'b btnode ref option \<Rightarrow> assn" where
  "leafs_assn (ln#lns) (Some r) z = 
 (\<exists>\<^sub>A fwd.
      r \<mapsto>\<^sub>r Btleaf ln fwd
    * leafs_assn lns fwd z
  )" | 
  "leafs_assn [] r z = \<up>(r = z)" |
  "leafs_assn _ _ _ = false"


lemma list_assn_prod_split: "list_assn (\<lambda>x y. P x y * Q x y) as bs = list_assn P as bs * list_assn Q as bs"
proof(cases "length as = length bs")
  case True
  then show ?thesis
  proof (induction rule: list_induct2)
    case Nil
    then show ?case by sep_auto
  next
    case (Cons x xs y ys)
    show ?case
    proof (rule ent_iffI, goal_cases)
      case 1
      then show ?case
      using Cons by sep_auto
    next
      case 2
      then show ?case
      using Cons by sep_auto
    qed
  qed
next
  case False
  then show ?thesis
    by (simp add: list_assn_aux_ineq_len)
qed

lemma assn_eq_split:
  assumes "B = C"
  shows "B \<Longrightarrow>\<^sub>A C"
  and "C \<Longrightarrow>\<^sub>A B"
  by (simp_all add: assms)

lemma ent_ex_inst: "\<exists>\<^sub>Ax. P x \<Longrightarrow>\<^sub>A Q \<Longrightarrow> P y \<Longrightarrow>\<^sub>A Q"
  using ent_trans by blast

lemma "leaf_nodes_assn k xs r z = (\<exists>\<^sub>Aps. list_assn (leaf_node k) xs ps * leafs_assn ps r z)"
proof (induction xs arbitrary: r)
  case Nil
  then show ?case
  apply(intro ent_iffI)
    subgoal by sep_auto
    subgoal by sep_auto
    done
next
  case (Cons a xs)
  then show ?case
  proof(intro ent_iffI, goal_cases)
    case 1
    show ?case
      apply(cases r; cases a)
      apply simp_all
      find_theorems "\<exists>\<^sub>A_._ \<Longrightarrow>\<^sub>A_"
      apply(rule ent_ex_preI)+
      subgoal for aa x1 xsi xsi' fwd
      apply (subst "Cons.IH"[of fwd]) 
        apply simp
      apply(rule ent_ex_preI)
        subgoal for ps
          apply(inst_ex_assn "xsi#ps")
          apply simp_all
          apply(inst_ex_assn fwd xsi')
          apply (sep_auto)
          done
        done
      done
  next
    case 2
    have *: "list_assn (leaf_node k) xs ps' * leafs_assn ps' r' z
          \<Longrightarrow>\<^sub>A leaf_nodes_assn k xs r' z" 
      for ps' r'
      using assn_eq_split(1)[OF sym[OF "Cons.IH"[of r']]]
            ent_ex_inst[where y=ps' and Q="leaf_nodes_assn k xs r' z"]
      by blast
    show ?case
      apply(rule ent_ex_preI)+
      subgoal for ps
        apply(cases ps; cases r; cases a)
      apply sep_auto
      apply sep_auto
      apply sep_auto
      apply sep_auto
      apply sep_auto
      apply sep_auto
        apply simp
      apply(rule ent_ex_preI)+
        subgoal for aa list aaa x1 fwd xsi'
          apply(inst_ex_assn aa xsi' fwd)
          apply sep_auto
          using *[of list fwd]
          sorry
        apply simp
        done
      done
  qed
qed

(* TODO this cleanly separates the heap *)
lemma bplustree_leaf_nodes_sep:
  "bplustree_assn k t ti r z = leaf_nodes_assn k (leaf_nodes t) r z * inner_nodes_assn k t ti r z"
proof(induction arbitrary: r rule: bplustree_assn.induct)
  case (1 k xs a r z)
  then show ?case
    apply(intro ent_iffI)
    apply sep_auto
    apply sep_auto
    done
next
  case (2 k ts t a r z)
  show ?case
    apply(intro ent_iffI)
    apply (sep_auto eintros del: exI)
    oops

subsection "Iterator"

partial_function (heap) first_leaf :: "'b btnode ref \<Rightarrow> 'b btnode ref option Heap"
  where
    "first_leaf p = do {
  node \<leftarrow> !p;
  (case node of
    Btleaf _ _ \<Rightarrow> do { return (Some p) } |
    Btnode tsi ti \<Rightarrow> do {
        s \<leftarrow> pfa_get tsi 0;
        let (sub,sep) = s in do { 
          first_leaf (the sub)
        }
  }
)}"

partial_function (heap) last_leaf :: "'b btnode ref \<Rightarrow> 'b btnode ref option Heap"
  where
    "last_leaf p = do {
  node \<leftarrow> !p;
  (case node of
    Btleaf _ z \<Rightarrow> do { return z } |
    Btnode tsi ti \<Rightarrow> do {
        last_leaf ti
  }
)}"

declare last.simps[simp del] butlast.simps[simp del]
lemma first_leaf_rule[sep_heap_rules]:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn k t ti r z>
  first_leaf ti
  <\<lambda>u. bplustree_assn k t ti r z * \<up>(u = r)>\<^sub>t"
  using assms
proof(induction t arbitrary: ti z)
  case (LNode x)
  then show ?case
    apply(subst first_leaf.simps)
    apply (sep_auto dest!: mod_starD)
    done
next
  case (Node ts t)
  then obtain sub sep tts where Cons: "ts = (sub,sep)#tts"
    apply(cases ts) by auto
  then show ?case 
    apply(subst first_leaf.simps)
    apply (sep_auto simp add: butlast.simps)
    subgoal for tsia tsil ti tsi' rs subi sepi
    apply(cases rs; cases tsi')
    apply simp_all
      subgoal for subleaf rrs _ ttsi'
        supply R = "Node.IH"(1)[of "(sub,sep)" sub "(the subi)" subleaf]
        thm R
    using  "Node.prems"(1)
    apply (sep_auto heap add: R)
    subgoal by (metis Node.prems(2) assms(1) bplustree.inject(2) bplustree.simps(4) Cons list.set_intros(1) order_impl_root_order root_order.elims(2) some_child_sub(1))
    apply (sep_auto eintros del: exI)
    apply(inst_existentials tsia tsil ti "(subi, sepi) # ttsi'" "((subi, (r, subleaf)),sepi)#(zip (zip (subtrees ttsi') (zip (butlast (subleaf # rrs)) rrs)) (separators ttsi'))" "subleaf # rrs")
    apply (sep_auto simp add: last.simps butlast.simps)+
    done
  done
  done
qed
declare last.simps[simp add] butlast.simps[simp add]

declare last.simps[simp del] butlast.simps[simp del]
lemma last_leaf_rule[sep_heap_rules]:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn k t ti r z>
  last_leaf ti
  <\<lambda>u. bplustree_assn k t ti r z * \<up>(u = z)>\<^sub>t"
  using assms
proof(induction t arbitrary: ti r)
  case (LNode x)
  then show ?case
    apply(subst last_leaf.simps)
    apply (sep_auto dest!: mod_starD)
    done
next
  case (Node ts t)
  show ?case 
    apply(subst last_leaf.simps)
        supply R = "Node.IH"(2)
    apply (sep_auto heap add: R)
    subgoal using "Node.prems" by simp
    subgoal by (metis Node.prems(2) assms(1) bplustree.inject(2) bplustree.simps(4) Cons list.set_intros(1) order_impl_root_order root_order.elims(2) some_child_sub(1))
    apply (sep_auto eintros del: exI)
    subgoal for tsia tsil ti tsi' rs
    apply(inst_existentials tsia tsil ti "tsi'" " (zip (zip (subtrees tsi') (zip (butlast (r # rs)) rs)) (separators tsi'))" rs)
    apply (sep_auto simp add: last.simps butlast.simps)+
    done
  done
qed
declare last.simps[simp add] butlast.simps[simp add]


definition leaf_iter_init where
"leaf_iter_init p = do {
  r \<leftarrow> first_leaf (the p);
  z \<leftarrow> last_leaf (the p);
  return  (r, z)
}"

lemma leaf_iter_init_rule:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn k t ti r z>
  leaf_iter_init (Some ti)
  <\<lambda>(u,v). leaf_nodes_assn k (leaf_nodes t) u v>\<^sub>t"
  using assms
  using bplustree_leaf_nodes_help[of k t ti r z]
  unfolding leaf_iter_init_def
  by (sep_auto)

definition leaf_iter_next where
"leaf_iter_next = (\<lambda>(r,z). do {
  p \<leftarrow> !(the r);
  return (the r, (fwd p, z))
})"

lemma leaf_iter_next_rule_help:
  "<leaf_nodes_assn k (x#xs) r z>
      leaf_iter_next (r,f)
   <\<lambda>(p,(n,_)). leaf_nodes_assn k [x] r n * leaf_nodes_assn k xs n z * \<up>(r = Some p)>"
  apply(subst leaf_iter_next_def)
  apply(cases r; cases x)
  apply(sep_auto)+
  done

definition leaf_iter_assn where "leaf_iter_assn k xs r xs2 = (\<lambda>(n,z). 
  (\<exists>\<^sub>Axs1. \<up>(xs = xs1@xs2) * leaf_nodes_assn k xs1 r n * leaf_nodes_assn k xs2 n z))" 

lemma leaf_nodes_assn_imp_iter_assn: "leaf_nodes_assn k xs r z \<Longrightarrow>\<^sub>A leaf_iter_assn k xs r xs (r,z)"
  unfolding leaf_iter_assn_def
  by sep_auto

lemma leaf_iter_next_rule: "<leaf_iter_assn k xs r (x#xs2) (n,z)>
leaf_iter_next (n,z)
<\<lambda>(p, (n',_)). leaf_iter_assn k xs r xs2 (n',z) * \<up>(n = Some p)>"
  unfolding leaf_iter_assn_def
  by (sep_auto heap add: leaf_iter_next_rule_help simp add: leaf_nodes_assn_aux_append)

definition leaf_iter_has_next where
"leaf_iter_has_next  = (\<lambda>(r,z). return (r \<noteq> z))"

(* TODO this so far only works for the whole tree (z = None)
for subintervals, we would need to show that the list of pointers is indeed distinct,
hence r = z can only occur at the end *)
lemma leaf_iter_has_next_rule:
  assumes "z = None"
  shows "<leaf_iter_assn k xs r xs2 (n,z)> leaf_iter_has_next (n,z) <\<lambda>u. leaf_iter_assn k xs r xs2 (n,z) * \<up>(u \<longleftrightarrow> xs2 \<noteq> [])>"
  unfolding leaf_iter_has_next_def
  apply(sep_auto simp add: leaf_iter_assn_def split!: prod.splits dest!: mod_starD)
  apply(cases xs2; cases z)
  using assms by auto

interpretation leaf_node_it: imp_list_iterate
    "\<lambda>x y. leaf_nodes_assn k x y None"
    "leaf_iter_assn k"
    leaf_iter_init
    leaf_iter_has_next
    leaf_iter_next
  apply(unfold_locales)
  subgoal 
    by (rule flatten_prec)
  subgoal for l p
    by (rule flatten_it_init_rule[of l p])
  subgoal for  l' l p it
    by (rule flatten_it_next_rule[of l' l p it]) simp
  subgoal for l p l' it
    by (rule flatten_it_has_next_rule[of l p l' it])
  subgoal for l p l' it
    by (rule flatten_quit_iteration[of l p l' it])
  done


end


end