theory BPlusTree_Range
imports BPlusTree
begin

definition lower_bound where
  "lower_bound y X = Min ({x \<in> X. x \<ge> y} \<union> {top})"


fun lower_bound_list where
"lower_bound_list (y::'a::{linorder, order_top}) (x#xs) = (if x \<ge> y then x else lower_bound_list y xs)" |
"lower_bound_list y [] = top"

lemma lower_bound_empty: "lower_bound y {} = top"
  unfolding lower_bound_def
  by auto

lemma "sorted xs \<Longrightarrow> lower_bound_list y xs = lower_bound y (set xs)"
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
      by (simp add: Min_insert2)
    ultimately show ?thesis 
      using Cons.prems True
      by (auto simp add: lower_bound_def)
  next
    case False
    then have "{xa \<in> set (x # xs). y \<le> xa} = {xa \<in> set xs. y \<le> xa}"
      by auto
    moreover have "sorted xs"
      using Cons.prems sorted.simps(2) by blast
    ultimately show ?thesis
      using False Cons.IH
      by (simp add: lower_bound_def)
  qed
qed



end