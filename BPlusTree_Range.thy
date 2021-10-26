theory BPlusTree_Range
imports BPlusTree
    "HOL-Data_Structures.Set_Specs"
begin

definition lower_bound where
  "lower_bound y X = Min ({x \<in> X. x \<ge> y} \<union> {top})"


fun lower_bound_list where
"lower_bound_list (y::'a::{linorder, order_top}) (x#xs) = (if x \<ge> y then x else lower_bound_list y xs)" |
"lower_bound_list y [] = top"

lemma lower_bound_empty: "lower_bound y {} = top"
  unfolding lower_bound_def
  by auto

lemma lower_bound_list_set: "sorted_less xs \<Longrightarrow>
  lower_bound_list y xs = lower_bound y (set xs)"
proof(induction xs)
  case Nil
  then show ?case by (auto simp add: lower_bound_def)
next
case (Cons x xs)
  then show ?case 
  proof(cases "x \<ge> y")
    case True
    then have "\<forall>x2 \<in> set (x#xs). y \<le> x2"
      using Cons.prems True by auto
    then have "{xa \<in> set (x # xs). y \<le> xa} = set(x#xs)"
      by auto
    then have "lower_bound y (set (x#xs)) = Min (set (x#xs) \<union> {top})"
      unfolding lower_bound_def
      by auto
    moreover have "x = Min (set (x#xs) \<union> {top})"
      using Cons.prems
      by (metis List.finite_set Min.union Min_insert2 Min_singleton less_imp_le list.simps(15) list.simps(3) min_def set_empty sorted_Cons_iff top_greatest)
    ultimately show ?thesis 
      using Cons.prems True
      by (auto simp add: lower_bound_def)
  next
    case False
    then have "{xa \<in> set (x # xs). y \<le> xa} = {xa \<in> set xs. y \<le> xa}"
      by auto
    moreover have "sorted_less xs"
      using Cons.prems by auto
    ultimately show ?thesis
      using False Cons.IH
      by (simp add: lower_bound_def)
  qed
qed

lemma lower_bound_split: "sorted_less (xs@x#ys) \<Longrightarrow>
  lower_bound_list y (xs@x#ys) =
  (if x < y then lower_bound_list y ys else lower_bound_list y (xs@[x]))" 
  apply (induction xs) 
  apply auto
  done

(* Since this splits into the wrong direction,
   we need to find a different value with similar properties
   compatible with the current tree structure *)

definition lower_bound2 where
  "lower_bound2 y X = Max ({x \<in> X. x < y} \<union> {bot})"


fun lower_bound2_list where
"lower_bound2_list (y::'a::{linorder, order_bot}) (x#xs) = (if (last (x#xs)) < y then (last (x#xs)) else lower_bound2_list y (butlast (x#xs)))" |
"lower_bound2_list y [] = bot"

declare lower_bound2_list.simps[simp del]

lemma lower_bound2_list_simps [simp]:
  "lower_bound2_list y (xs@[x]) = (if x < y then x else lower_bound2_list y xs)"
  "lower_bound2_list y [] = bot"
proof (goal_cases)
  case 1
  obtain xs' x' where *: "xs@[x] = x'#xs'"
    by (metis Nil_is_append_conv neq_Nil_conv)
  show ?case
    apply(subst *)+
    apply(subst lower_bound2_list.simps)
    apply(subst *[symmetric])+
    apply auto
    done
qed (auto simp add: lower_bound2_list.simps)



lemma lower_bound2_empty: "lower_bound2 y {} = bot"
  unfolding lower_bound2_def
  by auto


lemma lower_bound2_list_set: "sorted_less xs \<Longrightarrow>
  lower_bound2_list y xs = lower_bound2 y (set xs)"
proof(induction xs rule: rev_induct)
  case Nil
  then show ?case by (auto simp add: lower_bound2_def)
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
    then have "lower_bound2 y (set (xs@[x])) = Max (set (xs@[x]) \<union> {bot})"
      unfolding lower_bound2_def
      by auto
    moreover have "x = Max (set (xs@[x]) \<union> {bot})"
      using snoc.prems
      by (auto simp add: Max_insert2 less_imp_le sorted_snoc_iff)
    ultimately show ?thesis 
      using snoc.prems True
      by (auto simp add: lower_bound2_def sorted_snoc_iff)
  next
    case False
    then have "{xa \<in> set (xs@[x]). xa < y} = {xa \<in> set xs. xa < y}"
      by auto
    moreover have "sorted_less xs"
      using snoc.prems sorted_snoc_iff by auto
    ultimately show ?thesis
      using False snoc.IH
      by (simp add: lower_bound2_def)
  qed
qed

lemma lower_bound2_split: "sorted_less (xs@x#ys) \<Longrightarrow>
  lower_bound2_list y (xs@x#ys) =
  (if x < y then lower_bound2_list y (x#ys) else lower_bound2_list y xs)" 
  apply(induction ys rule: rev_induct)
  subgoal by (simp add: lower_bound2_list.simps(1))
  apply (auto)
  subgoal for x' xs'
    by (smt (verit, del_insts) Nil_is_append_conv butlast.simps(2) butlast_append butlast_snoc last_appendR list.distinct(1) lower_bound2_list.elims sorted_mid_iff sorted_mid_iff2)
  subgoal for x' xs'
    by (smt (verit, ccfv_threshold) Nil_is_append_conv butlast.simps(2) butlast_append butlast_snoc dual_order.strict_trans last.simps last_appendR last_snoc lower_bound2_list.elims sorted_mid_iff sorted_mid_iff2)
  done


(* these values lie directly next to each other
in the sorted list.
in other words there is no element between them.
in other words all elements are smeq or greq. *)
lemma lower_bound_12_neighbours:
  assumes "finite X"
  shows "\<forall>x \<in> X. x \<le> lower_bound2 y X \<or> lower_bound y X \<le> x"
proof (standard, goal_cases)
  case (1 x)
  have "\<not>(x > lower_bound2 y X \<and> x < lower_bound y X)"
  proof (rule ccontr, goal_cases)
    case contr: 1
    then have "x > lower_bound2 y X"
      by auto
    then have **: "x \<ge> y"
      unfolding lower_bound2_def
    proof(cases "x < y")
      case True
      then have *: "x \<in> {x \<in> X. x < y}"
        by (simp add: 1)
      moreover have "finite {x \<in> X. x < y}"
        using assms by auto
      ultimately have "x \<le> Max {x \<in> X. x < y}"
        using Max.coboundedI by blast
      then have "x \<le> lower_bound2 y X"
        unfolding lower_bound2_def
        using "*" \<open>finite {x \<in> X. x < y}\<close> by auto
      then show ?thesis
        using \<open>lower_bound2 y X < x\<close> by auto
    qed simp
    from contr have "x < lower_bound y X"
      by auto
    then have "x < y"
      unfolding lower_bound2_def
    proof(cases "x \<ge> y")
      case True
      then have *: "x \<in> {x \<in> X. x \<ge> y}"
        by (simp add: 1)
      moreover have "finite {x \<in> X. x \<ge> y}"
        using assms by auto
      ultimately have "x \<ge> Min {x \<in> X. x \<ge> y}"
        using Min.coboundedI by blast
      then have "x \<ge> lower_bound y X"
        unfolding lower_bound_def
        using "*" \<open>finite {x \<in> X. x \<ge> y}\<close> by auto
      then show ?thesis
        using \<open>lower_bound y X > x\<close> by auto
    qed simp
    then show ?case
      using ** by simp
  qed 
  then show ?case
    by auto
qed

lemma lower_bound_in_X: "finite X \<Longrightarrow> lower_bound y X \<in> X \<union> {top}"
proof(goal_cases)
  case 1
  have "{x \<in> X. y \<le> x} \<union> {top} \<noteq> {}"
    by auto
  moreover have "finite ({x \<in> X. y \<le> x} \<union> {top})"
    using 1 by auto
  ultimately have "lower_bound y X \<in> {x \<in> X. y \<le> x} \<union> {top}"
    unfolding lower_bound_def
    using Min_in[of "{x \<in> X. y \<le> x} \<union> {top}"] by blast
  then show ?case
    by blast
qed

lemma lower_bound2_in_X: "finite X \<Longrightarrow> lower_bound2 y X \<in> X \<union> {bot}"
proof(goal_cases)
  case 1
  have "{x \<in> X. y > x} \<union> {bot} \<noteq> {}"
    by auto
  moreover have "finite ({x \<in> X. y > x} \<union> {bot})"
    using 1 by auto
  ultimately have "lower_bound2 y X \<in> {x \<in> X. y > x} \<union> {bot}"
    unfolding lower_bound2_def
    using Max_in[of "{x \<in> X. y > x} \<union> {bot}"] by blast
  then show ?case
    by blast
qed

lemma lb2_le: "finite X \<Longrightarrow> lower_bound2 (y::'a::{linorder,order_bot}) X \<le> y"
proof(goal_cases)
  case 1
  have "{x \<in> X. y > x} \<union> {bot} \<noteq> {}"
    by auto
  moreover have "finite ({x \<in> X. y > x} \<union> {bot})"
    using 1 by auto
  ultimately have "lower_bound2 y X \<in> {x \<in> X. y > x} \<union> {bot}"
    unfolding lower_bound2_def
    using Max_in[of "{x \<in> X. y > x} \<union> {bot}"] by blast
  then show ?case
  proof(standard, goal_cases)
    case 1
    then have "lower_bound2 y X < y"
      by blast
    then show ?case
      by simp
  next
    case 2
    then have "lower_bound2 y X = bot"
      by simp
    then show ?case 
      by simp
  qed
qed

lemma lb_ge: "finite X \<Longrightarrow> lower_bound (y::'a::{linorder,order_top}) X \<ge> y"
proof(goal_cases)
  case 1
  have "{x \<in> X. y \<le> x} \<union> {top} \<noteq> {}"
    by auto
  moreover have "finite ({x \<in> X. y \<le> x} \<union> {top})"
    using 1 by auto
  ultimately have "lower_bound y X \<in> {x \<in> X. y \<le> x} \<union> {top}"
    unfolding lower_bound_def
    using Min_in[of "{x \<in> X. y \<le> x} \<union> {top}"] by blast
  then show ?case
  proof(standard, goal_cases)
    case 1
    then have "lower_bound y X \<ge> y"
      by blast
    then show ?case
      by simp
  next
    case 2
    then have "lower_bound y X = top"
      by simp
    then show ?case 
      by simp
  qed
qed

lemma lb2_le_lb: "finite X \<Longrightarrow> lower_bound2 (y::'a::{linorder, order_top,order_bot}) X \<le> lower_bound y X"
  by (meson lb2_le lb_ge order_trans)

(* the below lemmata describe how to obtain lower_bound
once we obtained lower_bound2 - it can be done within constant time! *)

lemma "sorted_less (xs@x#y#ys) \<Longrightarrow> x \<noteq> z \<Longrightarrow> x = lower_bound2_list z (xs@x#y#ys) \<Longrightarrow> y = lower_bound_list z (xs@x#y#ys)"
proof(goal_cases)
  case assms: 1
  then have "x = lower_bound2 z (set (xs@x#y#ys))"
    using lower_bound2_list_set by fastforce
  then have "x < z \<or> x = z"
    by (metis List.finite_set lb2_le order.not_eq_order_implies_strict)
  then show ?thesis
  proof(standard, goal_cases)
    case 1
    then have "lower_bound_list z (xs@x#y#ys) = lower_bound_list z (y#ys)"
      using assms lower_bound_split[of xs x "y#ys"]
      by simp
    moreover have "y \<ge> z"
      by (metis List.finite_set Un_insert_right \<open>x = lower_bound2 z (set (xs @ x # y # ys))\<close> assms(1) insertCI lb_ge list.set(2) lower_bound_12_neighbours not_le order_trans set_append sorted_Cons_iff sorted_wrt_append)
    ultimately show ?case
      by simp
  next
    case 2
    then show ?case
      using assms(2) by auto
  qed
qed

lemma "sorted_less (xs@x#ys) \<Longrightarrow> x = z \<Longrightarrow> x = lower_bound2_list z (xs@x#ys) \<Longrightarrow> x = lower_bound_list z (xs@x#ys)"
proof(goal_cases)
  case assms: 1
  then have "x = lower_bound2 z (set (xs@x#ys))"
    using lower_bound2_list_set by fastforce
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
      by (metis "2" assms(1) assms(3) last_in_set less_irrefl list.set_intros(1) lower_bound2_list.elims lower_bound2_split sorted_wrt_append)
    then show ?case 
      using 2
      by (auto)
  qed
qed


end