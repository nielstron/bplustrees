theory BPlusTree_Range
imports BPlusTree
    "HOL-Data_Structures.Set_Specs"
    BPlusTree_Set
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

locale split_range = split_tree split
  for split::
    "('a bplustree \<times> 'a::{linorder,order_top,order_bot}) list \<Rightarrow> 'a
       \<Rightarrow> ('a bplustree \<times> 'a) list \<times> ('a bplustree \<times> 'a) list" +
  fixes lb_list ::  "'a \<Rightarrow> ('a::{linorder,order_top,order_bot}) list \<Rightarrow> 'a"
  assumes lb2_list_req:
    (* TODO locale that derives such a function from a split function similar to the above *)
    "sorted_less ks \<Longrightarrow> lb_list x ks = lower_bound x ks"
begin

fun lb:: "'a bplustree \<Rightarrow> 'a \<Rightarrow> 'a" where
  "lb (LNode ks) x = (lb_list x ks)" |
  "lb (Node ts t) x = (
      case split ts x of (_,(sub,sep)#rs) \<Rightarrow> (
             lb sub x
      )
   | (_,[]) \<Rightarrow> lb t x
  )"

text "lower bound 2 proof"

thm lower_bound2_simps
  (* copied from comment in List_Ins_Del *)

(* lift to split *)

lemma leaves_conc: "leaves (Node (ls@rs) t) = leaves_list ls @ leaves_list rs @ leaves t"
  apply(induction ls)
  apply auto
  done

lemma leaves_split: "split ts x = (ls,rs) \<Longrightarrow> leaves (Node ts t) = leaves_list ls @ leaves_list rs @ leaves t"
  using leaves_conc split_conc by blast


(* Problem: the elements left/right of the separators
 cannot be excluded from the search for lower_bound2/lower_bound
and hence we cannot make any guarantees on the quality
of our result (just that it will be \<le> lower_bound for example)
Solution: we can guarantee that we retrieve *either* lb or lb2
*)

lemma lb_sorted_split:
  assumes "Laligned (Node ts t) u"
    and "sorted_less (leaves (Node ts t))"
    and "split ts x = (ls, rs)"
  shows "lower_bound x (leaves (Node ts t)) = lower_bound x (leaves_list rs @ leaves t)"
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
      using lower_bound_split[of "leavesls'" l' "leaves_list rs @ leaves t" x]
      by auto
  qed
qed


lemma lb2_sorted_split_right:
  assumes "split ts x = (ls, (sub,sep)#rs)"
    and "sorted_less (leaves (Node ts t))"
    and "Laligned (Node ts t) u"
  shows "lower_bound2 x (leaves_list ((sub,sep)#rs) @ leaves t) = lower_bound2 x (leaves sub)"
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
      using lower_bound2_split[of "leaves sub" "r'" "rs'" x] Cons 
      by auto
  qed
qed


theorem lb_set_inorder: 
  assumes "sorted_less (leaves t)"
    and "aligned l t u"
  shows "lb t x = lower_bound x (leaves t) \<or> lb t x = lower_bound2 x (leaves t)"
  using assms
proof(induction t x arbitrary: l u rule: lb.induct)
  case (2 ts t x)
  then obtain ls rs where list_split: "split ts x = (ls, rs)"
    by (meson surj_pair)
  then have list_conc: "ts = ls @ rs" 
    using split_conc by auto
  show ?case
  proof (cases rs)
    case Nil
    then have "lb (Node ts t) x = lb t x"
      by (simp add: list_split)
    have "lb t x = lower_bound x (leaves t) \<or> lb t x = lower_bound2 x (leaves t)"
      using "2.IH"(1)[of ls rs] list_split Nil
      using "2.prems" sorted_leaves_induct_last align_last'
      by metis
    then show ?thesis
    proof (standard, goal_cases)
      case 1
      have "lower_bound x (leaves t) = lower_bound x (leaves (Node ts t))"
        using lower_bound_split
        using "2.prems" list_split list_conc Nil
        by (metis (no_types, lifting) aligned_imp_Laligned lb_sorted_split leaves.simps(2) same_append_eq self_append_conv split_range.leaves_split split_range_axioms)
      then show ?case 
        using "1" \<open>lb (Node ts t) x = lb t x\<close> by presburger
    next
      case 2
      have "lower_bound2 x (leaves t) = lower_bound2 x (leaves (Node ts t))
            \<or> lower_bound2 x (leaves t) = lower_bound x (leaves (Node ts t))"

        using lower_bound2_split
        using "2.prems" list_split list_conc Nil
        apply auto
      then show ?case 
        using "1" \<open>lb (Node ts t) x = lb t x\<close> by presburger
    qed

    also have "\<dots> = lower_bound x (leaves (Node ts t))"
      using lower_bound2_split
      using "2.prems" list_split list_conc Nil
      sorry
    finally show ?thesis .
  next
    case (Cons a list)
    then obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a)
      then have "lb2 (Node ts t) x = lb2 sub x"
        using list_split Cons a_split
        by auto
      also have "\<dots> = lower_bound2 x (leaves sub)"
        using "2.IH"(2)[of ls rs "(sub,sep)" list sub sep]
        using "2.prems" a_split list_conc list_split local.Cons sorted_leaves_induct_subtree
              align_sub
        by (metis in_set_conv_decomp)
      also have "\<dots> = lower_bound2 x (leaves (Node ts t))"
        using lower_bound2_split
        using lb2_sorted_split_right "2.prems" list_split Cons a_split
        using aligned_imp_Laligned sorry
      finally show ?thesis  .
    qed
qed (auto simp add: lb2_list_req)


theorem lb2_set_Linorder: 
  assumes "sorted_less (leaves t)"
    and "Laligned t u"
  shows "lb2 t x = lower_bound2 x (leaves t)"
  using assms
proof(induction t x arbitrary: u rule: lb2.induct)
  case (2 ts t x)
  then obtain ls rs where list_split: "split ts x = (ls, rs)"
    by (meson surj_pair)
  then have list_conc: "ts = ls @ rs" 
    using split_conc by auto
  show ?case
  proof (cases rs)
    case Nil
    then have "lb2 (Node ts t) x = lb2 t x"
      by (simp add: list_split)
    also have "\<dots> = lower_bound2 x (leaves t)"
      using "2.IH"(1)[of ls rs] list_split Nil
      using "2.prems" sorted_leaves_induct_last
      by (metis Lalign_Llast)
    also have "\<dots> = lower_bound2 x (leaves (Node ts t))"
      using lower_bound2_split
      using "2.prems" list_split list_conc Nil
      sorry
    finally show ?thesis .
  next
    case (Cons a list)
    then obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a)
      then have "lb2 (Node ts t) x = lb2 sub x"
        using list_split Cons a_split
        by auto
      also have "\<dots> = lower_bound2 x (leaves sub)"
        using "2.IH"(2)[of ls rs "(sub,sep)" list sub sep]
        using "2.prems" a_split list_conc list_split local.Cons sorted_leaves_induct_subtree
        by (metis Lalign_Llast Laligned_split_left)
      also have "\<dots> = lower_bound2 x (leaves (Node ts t))"
        using lower_bound2_split
        using lb2_sorted_split_right "2.prems" list_split Cons a_split
        using aligned_imp_Laligned sorry
      finally show ?thesis  .
    qed
qed (auto simp add: lb2_list_req)

corollary isin_set_Linorder_top: 
  assumes "sorted_less (leaves t)"
    and "Laligned t top"
  shows "lb2 t x = lower_bound2 x (leaves t)"
  using assms lb2_set_Linorder
  by simp

end

end