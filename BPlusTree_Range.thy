theory BPlusTree_Range
imports BPlusTree
    "HOL-Data_Structures.Set_Specs"
    "HOL-Library.Sublist"
    BPlusTree_SplitSpec
begin

definition Lower_bound where
  "Lower_bound y X = Min ({x \<in> X. x \<ge> y} \<union> {top})"


fun lower_bound where
"lower_bound (y::'a::{linorder, order_top}) (x#xs) = (if x \<ge> y then x else lower_bound y xs)" |
"lower_bound y [] = top"

lemma Lower_bound_empty: "Lower_bound y {} = top"
  unfolding Lower_bound_def
  by auto

lemma lower_bound_set: "sorted_less xs \<Longrightarrow>
  lower_bound y xs = Lower_bound y (set xs)"
proof(induction xs)
  case Nil
  then show ?case by (auto simp add: Lower_bound_def)
next
case (Cons x xs)
  then show ?case 
  proof(cases "x \<ge> y")
    case True
    then have "\<forall>x2 \<in> set (x#xs). y \<le> x2"
      using Cons.prems True by auto
    then have "{xa \<in> set (x # xs). y \<le> xa} = set(x#xs)"
      by auto
    then have "Lower_bound y (set (x#xs)) = Min (set (x#xs) \<union> {top})"
      unfolding Lower_bound_def
      by auto
    moreover have "x = Min (set (x#xs) \<union> {top})"
      using Cons.prems
      by (metis List.finite_set Min.union Min_insert2 Min_singleton less_imp_le list.simps(15) list.simps(3) min_def set_empty sorted_Cons_iff top_greatest)
    ultimately show ?thesis 
      using Cons.prems True
      by (auto simp add: Lower_bound_def)
  next
    case False
    then have "{xa \<in> set (x # xs). y \<le> xa} = {xa \<in> set xs. y \<le> xa}"
      by auto
    moreover have "sorted_less xs"
      using Cons.prems by auto
    ultimately show ?thesis
      using False Cons.IH
      by (simp add: Lower_bound_def)
  qed
qed

lemma lower_bound_split: "sorted_less (xs@x#ys) \<Longrightarrow>
  lower_bound y (xs@x#ys) =
  (if x < y then lower_bound y ys else lower_bound y (xs@[x]))" 
  apply (induction xs) 
  apply auto
  done

(* Since this splits into the wrong direction,
   we need to find a different value with similar properties
   compatible with the current tree structure *)

definition Lower_bound2 where
  "Lower_bound2 y X = Max ({x \<in> X. x < y} \<union> {bot})"


fun lower_bound2 where
"lower_bound2 (y::'a::{linorder, order_bot}) (x#xs) = (if (last (x#xs)) < y then (last (x#xs)) else lower_bound2 y (butlast (x#xs)))" |
"lower_bound2 y [] = bot"

declare lower_bound2.simps[simp del]

lemma lower_bound2_simps [simp]:
  "lower_bound2 y (xs@[x]) = (if x < y then x else lower_bound2 y xs)"
  "lower_bound2 y [] = bot"
proof (goal_cases)
  case 1
  obtain xs' x' where *: "xs@[x] = x'#xs'"
    by (metis Nil_is_append_conv neq_Nil_conv)
  show ?case
    apply(subst *)+
    apply(subst lower_bound2.simps)
    apply(subst *[symmetric])+
    apply auto
    done
qed (auto simp add: lower_bound2.simps)



lemma Lower_bound2_empty: "Lower_bound2 y {} = bot"
  unfolding Lower_bound2_def
  by auto


lemma lower_bound2_set: "sorted_less xs \<Longrightarrow>
  lower_bound2 y xs = Lower_bound2 y (set xs)"
proof(induction xs rule: rev_induct)
  case Nil
  then show ?case by (auto simp add: Lower_bound2_def)
next
  case (snoc x xs)
  then obtain x' xs' where *: "x'#xs' = xs@[x]"
    by (metis Nil_is_append_conv neq_Nil_conv)
  then show ?case 
  proof(cases "x < y")
    case True
    then have "\<forall>x2 \<in> set (xs@[x]). x2 < y"
      using snoc.prems True
      by (auto simp add: sorted_snoc_iff)
    then have "{xa \<in> set (xs@[x]). xa < y} = set(xs@[x])"
      by auto
    then have "Lower_bound2 y (set (xs@[x])) = Max (set (xs@[x]) \<union> {bot})"
      unfolding Lower_bound2_def
      by auto
    moreover have "x = Max (set (xs@[x]) \<union> {bot})"
      using snoc.prems
      by (auto simp add: Max_insert2 less_imp_le sorted_snoc_iff)
    ultimately show ?thesis 
      using snoc.prems True
      by (auto simp add: Lower_bound2_def sorted_snoc_iff)
  next
    case False
    then have "{xa \<in> set (xs@[x]). xa < y} = {xa \<in> set xs. xa < y}"
      by auto
    moreover have "sorted_less xs"
      using snoc.prems sorted_snoc_iff by auto
    ultimately show ?thesis
      using False snoc.IH
      by (simp add: Lower_bound2_def)
  qed
qed

lemma lower_bound2_split: "sorted_less (xs@x#ys) \<Longrightarrow>
  lower_bound2 y (xs@x#ys) =
  (if x < y then lower_bound2 y (x#ys) else lower_bound2 y xs)" 
  apply(induction ys rule: rev_induct)
  subgoal by (simp add: lower_bound2.simps(1))
  apply (auto)
  subgoal for x' xs'
    by (smt (verit, del_insts) Nil_is_append_conv butlast.simps(2) butlast_append butlast_snoc last_appendR list.distinct(1) lower_bound2.elims sorted_mid_iff sorted_mid_iff2)
  subgoal for x' xs'
    by (smt (verit, ccfv_threshold) Nil_is_append_conv butlast.simps(2) butlast_append butlast_snoc dual_order.strict_trans last.simps last_appendR last_snoc lower_bound2.elims sorted_mid_iff sorted_mid_iff2)
  done


(* these values lie directly next to each other
in the sorted list.
in other words there is no element between them.
in other words all elements are smeq or greq. *)
lemma Lower_bound_12_neighbours:
  assumes "finite X"
  shows "\<forall>x \<in> X. x \<le> Lower_bound2 y X \<or> Lower_bound y X \<le> x"
proof (standard, goal_cases)
  case (1 x)
  have "\<not>(x > Lower_bound2 y X \<and> x < Lower_bound y X)"
  proof (rule ccontr, goal_cases)
    case contr: 1
    then have "x > Lower_bound2 y X"
      by auto
    then have **: "x \<ge> y"
      unfolding Lower_bound2_def
    proof(cases "x < y")
      case True
      then have *: "x \<in> {x \<in> X. x < y}"
        by (simp add: 1)
      moreover have "finite {x \<in> X. x < y}"
        using assms by auto
      ultimately have "x \<le> Max {x \<in> X. x < y}"
        using Max.coboundedI by blast
      then have "x \<le> Lower_bound2 y X"
        unfolding Lower_bound2_def
        using "*" \<open>finite {x \<in> X. x < y}\<close> by auto
      then show ?thesis
        using \<open>Lower_bound2 y X < x\<close> by auto
    qed simp
    from contr have "x < Lower_bound y X"
      by auto
    then have "x < y"
      unfolding Lower_bound2_def
    proof(cases "x \<ge> y")
      case True
      then have *: "x \<in> {x \<in> X. x \<ge> y}"
        by (simp add: 1)
      moreover have "finite {x \<in> X. x \<ge> y}"
        using assms by auto
      ultimately have "x \<ge> Min {x \<in> X. x \<ge> y}"
        using Min.coboundedI by blast
      then have "x \<ge> Lower_bound y X"
        unfolding Lower_bound_def
        using "*" \<open>finite {x \<in> X. x \<ge> y}\<close> by auto
      then show ?thesis
        using \<open>Lower_bound y X > x\<close> by auto
    qed simp
    then show ?case
      using ** by simp
  qed 
  then show ?case
    by auto
qed

lemma Lower_bound_in_X: "finite X \<Longrightarrow> Lower_bound y X \<in> X \<union> {top}"
proof(goal_cases)
  case 1
  have "{x \<in> X. y \<le> x} \<union> {top} \<noteq> {}"
    by auto
  moreover have "finite ({x \<in> X. y \<le> x} \<union> {top})"
    using 1 by auto
  ultimately have "Lower_bound y X \<in> {x \<in> X. y \<le> x} \<union> {top}"
    unfolding Lower_bound_def
    using Min_in[of "{x \<in> X. y \<le> x} \<union> {top}"] by blast
  then show ?case
    by blast
qed

lemma Lower_bound2_in_X: "finite X \<Longrightarrow> Lower_bound2 y X \<in> X \<union> {bot}"
proof(goal_cases)
  case 1
  have "{x \<in> X. y > x} \<union> {bot} \<noteq> {}"
    by auto
  moreover have "finite ({x \<in> X. y > x} \<union> {bot})"
    using 1 by auto
  ultimately have "Lower_bound2 y X \<in> {x \<in> X. y > x} \<union> {bot}"
    unfolding Lower_bound2_def
    using Max_in[of "{x \<in> X. y > x} \<union> {bot}"] by blast
  then show ?case
    by blast
qed

lemma lb2_le: "finite X \<Longrightarrow> Lower_bound2 (y::'a::{linorder,order_bot}) X \<le> y"
proof(goal_cases)
  case 1
  have "{x \<in> X. y > x} \<union> {bot} \<noteq> {}"
    by auto
  moreover have "finite ({x \<in> X. y > x} \<union> {bot})"
    using 1 by auto
  ultimately have "Lower_bound2 y X \<in> {x \<in> X. y > x} \<union> {bot}"
    unfolding Lower_bound2_def
    using Max_in[of "{x \<in> X. y > x} \<union> {bot}"] by blast
  then show ?case
  proof(standard, goal_cases)
    case 1
    then have "Lower_bound2 y X < y"
      by blast
    then show ?case
      by simp
  next
    case 2
    then have "Lower_bound2 y X = bot"
      by simp
    then show ?case 
      by simp
  qed
qed

lemma lb_ge: "finite X \<Longrightarrow> Lower_bound (y::'a::{linorder,order_top}) X \<ge> y"
proof(goal_cases)
  case 1
  have "{x \<in> X. y \<le> x} \<union> {top} \<noteq> {}"
    by auto
  moreover have "finite ({x \<in> X. y \<le> x} \<union> {top})"
    using 1 by auto
  ultimately have "Lower_bound y X \<in> {x \<in> X. y \<le> x} \<union> {top}"
    unfolding Lower_bound_def
    using Min_in[of "{x \<in> X. y \<le> x} \<union> {top}"] by blast
  then show ?case
  proof(standard, goal_cases)
    case 1
    then have "Lower_bound y X \<ge> y"
      by blast
    then show ?case
      by simp
  next
    case 2
    then have "Lower_bound y X = top"
      by simp
    then show ?case 
      by simp
  qed
qed

lemma lb2_le_lb: "finite X \<Longrightarrow> Lower_bound2 (y::'a::{linorder, order_top,order_bot}) X \<le> Lower_bound y X"
  by (meson lb2_le lb_ge order_trans)

(* the below lemmata describe how to obtain Lower_bound
once we obtained Lower_bound2 - it can be done within constant time! *)

lemma lb2_obtain_lb: "sorted_less (xs@x#y#ys) \<Longrightarrow> x \<noteq> z \<Longrightarrow> x = lower_bound2 z (xs@x#y#ys) \<Longrightarrow> y = lower_bound z (xs@x#y#ys)"
proof(goal_cases)
  case assms: 1
  then have "x = Lower_bound2 z (set (xs@x#y#ys))"
    using lower_bound2_set by fastforce
  then have "x < z \<or> x = z"
    by (metis List.finite_set lb2_le order.not_eq_order_implies_strict)
  then show ?thesis
  proof(standard, goal_cases)
    case 1
    then have "lower_bound z (xs@x#y#ys) = lower_bound z (y#ys)"
      using assms lower_bound_split[of xs x "y#ys"]
      by simp
    moreover have "y \<ge> z"
      by (metis List.finite_set Un_insert_right \<open>x = Lower_bound2 z (set (xs @ x # y # ys))\<close> assms(1) insertCI lb_ge list.set(2) Lower_bound_12_neighbours not_le order_trans set_append sorted_Cons_iff sorted_wrt_append)
    ultimately show ?case
      by simp
  next
    case 2
    then show ?case
      using assms(2) by auto
  qed
qed

lemma lb2_obtain_lb_edge: "sorted_less (xs@x#ys) \<Longrightarrow> x = z \<Longrightarrow> x = lower_bound2 z (xs@x#ys) \<Longrightarrow> x = lower_bound z (xs@x#ys)"
proof(goal_cases)
  case assms: 1
  then have "x = Lower_bound2 z (set (xs@x#ys))"
    using lower_bound2_set by fastforce
  then have "x < z \<or> x = z"
    by (metis List.finite_set lb2_le order.not_eq_order_implies_strict)
  then show ?thesis
  proof(standard, goal_cases)
    case 1
    then show ?case
    using assms(2) by auto
  next
    case 2
    then have "xs = []"
      by (metis "2" assms(1) assms(3) last_in_set less_irrefl list.set_intros(1) lower_bound2.elims lower_bound2_split sorted_wrt_append)
    then show ?case 
      using 2
      by (auto)
  qed
qed

definition Lrange where
  "Lrange l X = {x \<in> X. x \<ge> l}"

definition "lrange_filter l = filter (\<lambda>x. x \<ge> l)"

lemma lrange_filter_iff_Lrange: "set (lrange_filter l xs) = Lrange l (set xs)" 
  by (auto simp add: lrange_filter_def Lrange_def)

fun lrange_list where
  "lrange_list l (x#xs) = (if x \<ge> l then (x#xs) else lrange_list l xs)" |
  "lrange_list l [] = []"

lemma sorted_leq_lrange: "sorted_wrt (\<le>) xs \<Longrightarrow> lrange_list (l::'a::linorder) xs = lrange_filter l xs"
  apply(induction xs)
  apply(auto simp add: lrange_filter_def)
  by (metis dual_order.trans filter_True)

lemma sorted_less_lrange: "sorted_less xs \<Longrightarrow> lrange_list (l::'a::linorder) xs = lrange_filter l xs"
  by (metis sorted_leq_lrange sorted_sorted_wrt strict_sorted_iff strict_sorted_sorted_wrt)

lemma lrange_list_sorted: "sorted_less (xs@x#ys) \<Longrightarrow>
  lrange_list l (xs@x#ys) =
  (if l < x then (lrange_list l xs)@x#ys else lrange_list l (x#ys))" 
  by (induction xs arbitrary: x) auto

lemma lrange_filter_sorted: "sorted_less (xs@x#ys) \<Longrightarrow>
  lrange_filter l (xs@x#ys) =
  (if l < x then (lrange_filter l xs)@x#ys else lrange_filter l (x#ys))" 
  by (metis lrange_list_sorted sorted_less_lrange sorted_wrt_append)


lemma lrange_suffix: "suffix (lrange_list l xs) xs" 
  apply(induction xs)
  apply (auto dest: suffix_ConsI)
  done


locale split_range = split_tree split
  for split::
    "('a bplustree \<times> 'a::{linorder,order_top}) list \<Rightarrow> 'a
       \<Rightarrow> ('a bplustree \<times> 'a) list \<times> ('a bplustree \<times> 'a) list" +
  fixes lrange_list ::  "'a \<Rightarrow> ('a::{linorder,order_top}) list \<Rightarrow> 'a list"
  assumes lrange_list_req:
    (* TODO locale that derives such a function from a split function similar to the above *)
    "sorted_less ks \<Longrightarrow> lrange_list l ks = lrange_filter l ks"
begin

fun lrange:: "'a bplustree \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "lrange (LNode ks) x = (lrange_list x ks)" |
  "lrange (Node ts t) x = (
      case split ts x of (_,(sub,sep)#rs) \<Rightarrow> (
             lrange sub x @ leaves_list rs @ leaves t
      ) 
   | (_,[]) \<Rightarrow> lrange t x
  )"

text "lrange proof"


(* lift to split *)

lemma leaves_conc: "leaves (Node (ls@rs) t) = leaves_list ls @ leaves_list rs @ leaves t"
  apply(induction ls)
  apply auto
  done

lemma leaves_split: "split ts x = (ls,rs) \<Longrightarrow> leaves (Node ts t) = leaves_list ls @ leaves_list rs @ leaves t"
  using leaves_conc split_conc by blast



lemma lrange_sorted_split:
  assumes "Laligned (Node ts t) u"
    and "sorted_less (leaves (Node ts t))"
    and "split ts x = (ls, rs)"
  shows "lrange_filter x (leaves (Node ts t)) = lrange_filter x (leaves_list rs @ leaves t)"
proof (cases ls)
  case Nil
  then have "ts = rs"
    using assms by (auto dest!: split_conc)
  then show ?thesis by simp
next
  case Cons
  then obtain ls' sub sep where ls_tail_split: "ls = ls' @ [(sub,sep)]"
    by (metis list.simps(3) rev_exhaust surj_pair)
  then have x_sm_sep: "sep < x"
    using split_req(2)[of ts x ls' sub sep rs]
    using Laligned_sorted_separators[OF assms(1)]
    using assms sorted_cons sorted_snoc 
    by blast
  moreover have leaves_split: "leaves (Node ts t) = leaves_list ls @ leaves_list rs @ leaves t"
    using assms(3) leaves_split by blast
  then show ?thesis
  proof (cases "leaves_list ls")
    case Nil
    then show ?thesis
      using leaves_split
      by (metis self_append_conv2)
  next
    case Cons
    then obtain leavesls' l' where leaves_tail_split: "leaves_list ls = leavesls' @ [l']"
      by (metis list.simps(3) rev_exhaust)
    then have "l' \<le> sep"
    proof -
      have "l' \<in> set (leaves_list ls)"
        using leaves_tail_split by force
      then have "l' \<in> set (leaves (Node ls' sub))"
        using ls_tail_split
        by auto
      moreover have "Laligned (Node ls' sub) sep" 
        using assms split_conc[OF assms(3)] Cons ls_tail_split
        using Laligned_split_left[of ls' sub sep rs t u]
        by simp
      ultimately show ?thesis
        using Laligned_leaves_inbetween[of "Node ls' sub" sep]
        by blast
    qed
    then have "l' < x"
      using le_less_trans x_sm_sep by blast
    then show ?thesis
      using assms(2) ls_tail_split leaves_tail_split leaves_split x_sm_sep
      using lrange_filter_sorted[of "leavesls'" l' "leaves_list rs @ leaves t" x]
      by (auto simp add: lrange_filter_def) 
  qed
qed


lemma lrange_sorted_split_right:
  assumes "split ts x = (ls, (sub,sep)#rs)"
    and "sorted_less (leaves (Node ts t))"
    and "Laligned (Node ts t) u"
  shows "lrange_filter x (leaves_list ((sub,sep)#rs) @ leaves t) = lrange_filter x (leaves sub)@leaves_list rs@leaves t"
proof -
  from assms have "x \<le> sep"
  proof -
    from assms have "sorted_less (separators ts)"
      by (meson Laligned_sorted_inorder sorted_cons sorted_inorder_separators sorted_snoc)
    then show ?thesis
      using split_req(3)
      using assms
      by fastforce
  qed
  moreover have leaves_split: "leaves (Node ts t) = leaves_list ls @ leaves sub @ leaves_list rs @ leaves t"
    using split_conc[OF assms(1)] by auto
  ultimately show ?thesis
  proof (cases "leaves_list rs @ leaves t")
    case Nil
    then show ?thesis 
      by (metis assms(1) leaves_split same_append_eq self_append_conv split_range.leaves_split split_range_axioms)
  next
    case (Cons r' rs')
    then have "sep < r'"
      by (metis (mono_tags, lifting) Laligned_split_right aligned_leaves_inbetween append.right_neutral append_assoc assms(1) assms(3) concat.simps(1) leaves_conc list.set_intros(1) list.simps(8) split_tree.split_conc split_tree_axioms)
    then have  "x < r'"
      using \<open>x \<le> sep\<close> by auto
    moreover have "sorted_less (leaves_list ((sub,sep)#rs) @ leaves t)"
      using assms sorted_wrt_append split_conc
      by fastforce
    ultimately show ?thesis
      using lrange_filter_sorted[of "leaves sub" "r'" "rs'" x] Cons 
      by auto
  qed
qed


theorem lrange_set: 
  assumes "sorted_less (leaves t)"
    and "aligned l t u"
  shows "lrange t x = lrange_filter x (leaves t)"
  using assms
proof(induction t x arbitrary: l u rule: lrange.induct)
  case (1 ks x)
  then show ?case
    using lrange_list_req
    by auto
next
  case (2 ts t x)
  then obtain ls rs where list_split: "split ts x = (ls, rs)"
    by (meson surj_pair)
  then have list_conc: "ts = ls @ rs" 
    using split_conc by auto
  show ?case
  proof (cases rs)
    case Nil
    then have "lrange (Node ts t) x = lrange t x"
      by (simp add: list_split)
    also have "\<dots> = lrange_filter x (leaves t)"
      by (metis "2.IH"(1) "2.prems"(1) "2.prems"(2) align_last' list_split local.Nil sorted_leaves_induct_last)
    also have "\<dots> = lrange_filter x (leaves (Node ts t))"
      by (metis (no_types, lifting) "2.prems"(1) "2.prems"(2) aligned_imp_Laligned leaves.simps(2) list_conc list_split local.Nil lrange_sorted_split same_append_eq self_append_conv split_range.leaves_split split_range_axioms)
    finally show ?thesis .
  next
    case (Cons a list)
    then obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a)
      then have "lrange (Node ts t) x = lrange sub x @ leaves_list list @ leaves t"
        using list_split Cons a_split
        by auto
      also have "\<dots> = lrange_filter x (leaves sub) @ leaves_list list @ leaves t"
        using "2.IH"(2)[of ls rs "(sub,sep)" list sub sep]
        using "2.prems" a_split list_conc list_split local.Cons sorted_leaves_induct_subtree
              align_sub
        by (metis in_set_conv_decomp)
      also have "\<dots> = lrange_filter x (leaves (Node ts t))"
        by (metis "2.prems"(1) "2.prems"(2) a_split aligned_imp_Laligned list_split local.Cons lrange_sorted_split lrange_sorted_split_right)
      finally show ?thesis  .
    qed
qed

fun leafs_range:: "'a bplustree \<Rightarrow> 'a \<Rightarrow> 'a bplustree list" where
  "leafs_range (LNode ks) x = [LNode ks]" |
  "leafs_range (Node ts t) x = (
      case split ts x of (_,(sub,sep)#rs) \<Rightarrow> (
             leafs_range sub x @ leaf_nodes_list rs @ leaf_nodes t
      ) 
   | (_,[]) \<Rightarrow> leafs_range t x
  )"

text "lrange proof"


(* lift to split *)

lemma concat_leaf_nodes_leaves_list: "(concat (map leaves (leaf_nodes_list ts))) = leaves_list ts"
  apply(induction ts)
  subgoal by auto
  subgoal using concat_leaf_nodes_leaves by auto
  done

theorem leafs_range_set: 
  assumes "sorted_less (leaves t)"
    and "aligned l t u"
  shows "suffix (lrange_filter x (leaves t)) (concat (map leaves (leafs_range t x)))"
  using assms
proof(induction t x arbitrary: l u rule: lrange.induct)
  case (1 ks x)
  then show ?case
    apply simp
    by (metis lrange_suffix sorted_less_lrange)
next
  case (2 ts t x)
  then obtain ls rs where list_split: "split ts x = (ls, rs)"
    by (meson surj_pair)
  then have list_conc: "ts = ls @ rs" 
    using split_conc by auto
  show ?case
  proof (cases rs)
    case Nil
    then have *: "leafs_range (Node ts t) x = leafs_range t x"
      by (simp add: list_split)
    moreover have "suffix (lrange_filter x (leaves t)) (concat (map leaves (leafs_range t x)))"
      by (metis "2.IH"(1) "2.prems"(1) "2.prems"(2) align_last' list_split local.Nil sorted_leaves_induct_last)
    then have "suffix (lrange_filter x (leaves (Node ts t))) (concat (map leaves (leafs_range t x)))"
      by (metis (no_types, lifting) "2.prems"(1) "2.prems"(2) aligned_imp_Laligned leaves.simps(2) list_conc list_split local.Nil lrange_sorted_split same_append_eq self_append_conv split_range.leaves_split split_range_axioms)
    ultimately show ?thesis by simp
  next
    case (Cons a list)
    then obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a)
      then have "leafs_range (Node ts t) x = leafs_range sub x @ leaf_nodes_list list @ leaf_nodes t"
        using list_split Cons a_split
        by auto
      moreover have *: "suffix (lrange_filter x (leaves sub)) (concat (map leaves (leafs_range sub x)))"
        by (metis "2.IH"(2) "2.prems"(1) "2.prems"(2) a_split align_sub in_set_conv_decomp list_conc list_split local.Cons sorted_leaves_induct_subtree)
      then have "suffix (lrange_filter x (leaves (Node ts t))) (concat (map leaves (leafs_range sub x @ leaf_nodes_list list @ leaf_nodes t)))"
      proof (goal_cases)
        case 1
        have "lrange_filter x (leaves (Node ts t)) = lrange_filter x (leaves sub @ leaves_list list @ leaves t)" 
          by (metis (no_types, lifting) "2.prems"(1) "2.prems"(2) a_split aligned_imp_Laligned append.assoc concat_map_maps fst_conv list.simps(9) list_split local.Cons lrange_sorted_split maps_simps(1))
        also have "\<dots> = lrange_filter x (leaves sub) @ leaves_list list @ leaves t"
          by (metis "2.prems"(1) "2.prems"(2) a_split aligned_imp_Laligned calculation list_split local.Cons lrange_sorted_split_right split_range.lrange_sorted_split split_range_axioms)
        moreover have "(concat (map leaves (leafs_range sub x @ leaf_nodes_list list @ leaf_nodes t))) = (concat (map leaves (leafs_range sub x)) @ leaves_list list @ leaves t)" 
          using concat_leaf_nodes_leaves_list[of list] concat_leaf_nodes_leaves[of t]
          by simp
        ultimately show ?case
          using *
          by simp
      qed
      ultimately show ?thesis by simp
    qed
qed

lemma leafs_range_not_empty: "\<exists>ks list. leafs_range t x = (LNode ks)#list \<and> (LNode ks) \<in> set (leaf_nodes t)" 
  apply(induction t x rule: leafs_range.induct)
  apply (auto split!: prod.splits list.splits)
  by (metis Cons_eq_appendI fst_conv in_set_conv_decomp split_conc)


(* Note that, conveniently, this argument is purely syntactic,
we do not need to show that this has anything to do with smeq relationships *)
lemma leafs_range_pre_lrange: "leafs_range t x = (LNode ks)#list \<Longrightarrow> lrange_list x ks @ (concat (map leaves list)) = lrange t x"
proof(induction t x arbitrary: ks list rule: leafs_range.induct)
  case (1 ks x)
  then show ?case by simp
next
  case (2 ts t x ks list)
  then show ?case
  proof(cases "split ts x")
    case split: (Pair ls rs)
    then show ?thesis
    proof (cases rs)
      case Nil
      then show ?thesis
        using "2.IH"(1) "2.prems" split by auto
    next
      case (Cons subsep rss)
      then show ?thesis
      proof(cases subsep)
        case sub_sep: (Pair sub sep)
        thm "2.IH"(2) "2.prems"
        have "\<exists>list'. leafs_range sub x = (LNode ks)#list'"
          using "2.prems" split Cons sub_sep leafs_range_not_empty[of sub x]
            apply simp
          by fastforce
        then obtain list' where *: "leafs_range sub x = (LNode ks)#list'"
          by blast
        moreover have "list = list'@concat (map (leaf_nodes \<circ> fst) rss) @ leaf_nodes t"
          using * 
          using "2.prems" split Cons sub_sep
          by simp
        ultimately show ?thesis
          using split "2.IH"(2)[OF split[symmetric] Cons sub_sep[symmetric] *,symmetric]
                Cons sub_sep concat_leaf_nodes_leaves_list[of rss] concat_leaf_nodes_leaves[of t]
          by simp
      qed
    qed
  qed
qed

(* A function that is way easier to reason about in the imperative setting *)
fun concat_leafs_range where
  "concat_leafs_range t x = (case leafs_range t x of (LNode ks)#list \<Rightarrow> lrange_list x ks @ (concat (map leaves list)))"

lemma concat_leafs_range_lrange: "concat_leafs_range t x = lrange t x"
proof -
  obtain ks list where *: "leafs_range t x = (LNode ks)#list"
    using leafs_range_not_empty by blast
  then have "concat_leafs_range t x = lrange_list x ks @ (concat (map leaves list))"
    by simp
  also have "\<dots> = lrange t x"
    using leafs_range_pre_lrange[OF *]
    by simp
  finally show ?thesis .
qed

end

context split_list
begin

definition lrange_split where
"lrange_split l xs = (case split_list xs l of (ls,rs) \<Rightarrow> rs)"

lemma lrange_filter_split: 
  assumes "sorted_less xs"
    and "split_list xs l = (ls,rs)"
  shows "lrange_list l xs = rs"
  find_theorems split_list
proof(cases rs)
  case rs_Nil: Nil
  then show ?thesis
  proof(cases ls)
    case Nil
    then show ?thesis
      using assms split_list_req(1)[of xs l ls rs] rs_Nil
      by simp
  next
    case Cons
    then obtain lss sep where snoc: "ls = lss@[sep]"
      by (metis append_butlast_last_id list.simps(3))
    then have "sep < l"
      using assms(1) assms(2) split_list_req(2) by blast
    then show ?thesis 
      using lrange_list_sorted[of lss sep rs l]
            snoc split_list_req(1)[OF assms(2)]
            assms rs_Nil
      by simp
  qed
next
  case ls_Cons: (Cons sep rss)
  then have *: "l \<le> sep"
    using assms(1) assms(2) split_list_req(3) by auto
  then show ?thesis 
  proof(cases ls)
    case Nil
    then show ?thesis
    using lrange_list_sorted[of ls sep rss l]
          split_list_req(1)[OF assms(2)] assms
          ls_Cons *
    by simp
  next
    case Cons
    then obtain lss sep2 where snoc: "ls = lss@[sep2]"
      by (metis append_butlast_last_id list.simps(3))
    then have "sep2 < l"
      using assms(1) assms(2) split_list_req(2) by blast
    moreover have "sorted_less (lss@[sep2])"
      using assms(1) assms(2) ls_Cons snoc sorted_mid_iff sorted_snoc split_list_req(1) by blast
    ultimately show ?thesis 
      using lrange_list_sorted[of ls sep rss l]
            lrange_list_sorted[of lss "sep2" "[]" l]
            split_list_req(1)[OF assms(2)] assms
            ls_Cons * snoc
      by simp
  qed
qed

lemma lrange_split_req: 
  assumes "sorted_less xs"
  shows "lrange_split l xs = lrange_filter l xs"
  unfolding lrange_split_def
  using lrange_filter_split[of xs l] assms
  using sorted_less_lrange
  by (simp split!: prod.splits)

end

context split_full
begin

sublocale split_range split lrange_split 
  using lrange_split_req
  by unfold_locales auto

end

end