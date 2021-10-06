theory BPlusTree_Iter
  imports
    BPlusTree_Imp
    "HOL-Real_Asymp.Inst_Existentials"
    "Separation_Logic_Imperative_HOL.Imp_List_Spec"
    Flatten_Iter
    Partially_Filled_Array_Iter
begin


(* TODO use list_zip? \<rightarrow> not well defined return type *)

fun bplustree_assn_leafs :: "nat \<Rightarrow> ('a::heap) bplustree \<Rightarrow> 'a btnode ref \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref list \<Rightarrow> assn" where
  "bplustree_assn_leafs k (LNode xs) a r z leafptrs = 
 (\<exists>\<^sub>A xsi fwd.
      a \<mapsto>\<^sub>r Btleaf xsi fwd
    * is_pfa (2*k) xs xsi
    * \<up>(fwd = z)
    * \<up>(r = Some a)
    * \<up>(leafptrs = [a])
  )" |
  "bplustree_assn_leafs k (Node ts t) a r z leafptrs = 
 (\<exists>\<^sub>A tsi ti tsi' tsi'' rs split.
      a \<mapsto>\<^sub>r Btnode tsi ti
    * bplustree_assn_leafs k t ti (last (r#rs)) (last (rs@[z])) (last split)
    * is_pfa (2*k) tsi' tsi
    * \<up>(concat split = leafptrs)
    * \<up>(length tsi' = length rs)
    * \<up>(length split = length rs + 1)
    * \<up>(tsi'' = zip (zip (map fst tsi') (zip (butlast (r#rs)) (zip (butlast (rs@[z])) (butlast split)))) (map snd tsi'))
    * list_assn ((\<lambda> t (ti,r',z',lptrs). bplustree_assn_leafs k t (the ti) r' z' lptrs) \<times>\<^sub>a id_assn) ts tsi''
    )"

fun make_list_list where "make_list_list xs = [xs]"

lemma make_list_list_concat: "concat (make_list_list ys) = ys"
  by auto

lemma ex_concat: "\<exists>xs. concat xs = ys"
  using make_list_list_concat by blast

lemma simp_ex_assn: "(\<And>x. f x = g x) \<Longrightarrow> ex_assn f = ex_assn g"
  by meson

lemma reorder_ex: 
  "(\<exists>\<^sub>Aa b c d e f g. z a b c d e f g) = (\<exists>\<^sub>Ab c d e f a g. z a b c d e f g)"
  "(\<exists>\<^sub>Aa b c. x a b c) = (\<exists>\<^sub>Ab c a. x a b c)"
  "(\<exists>\<^sub>Aa b c d. y a b c d) = (\<exists>\<^sub>Ab c a d. y a b c d)"
  apply(intro ent_iffI; sep_auto)+
  done

lemma inst_same: "(\<And>x. P x = Q x) \<Longrightarrow> (\<exists>\<^sub>A x. P x) = (\<exists>\<^sub>A x. Q x)"
  by simp

lemma inst_same2: "(\<And>x. P = Q x) \<Longrightarrow> P = (\<exists>\<^sub>A x. Q x)"
  by simp

lemma pure_eq_pre:
 "(P \<Longrightarrow> Q = R) \<Longrightarrow> (Q * \<up>P = R * \<up>P)"
  by fastforce


declare last.simps[simp del] butlast.simps[simp del]
lemma bplustree_extract_leafs:
 "bplustree_assn k t ti r z = (\<exists>\<^sub>Aleafptrs. bplustree_assn_leafs k t ti r z leafptrs)"
  apply(induction arbitrary: r rule: bplustree_assn.induct )
  (*apply auto*)
  subgoal for k xs a r z ra
    apply (rule ent_iffI)
    subgoal
      apply(inst_ex_assn "[a]")
      apply sep_auto
      done
    subgoal
      apply(rule ent_ex_preI)
      apply clarsimp
      apply(rule ent_ex_preI)+
      subgoal for x xsi fwd
      apply(inst_ex_assn xsi fwd)
        apply simp
        done
      done
    done
  subgoal for k ts t a r z ra
    apply(simp (no_asm))
(* TODO improve s.t. we get both directions for free *)
    (*apply(clarsimp)
    thm bplustree_assn_leafs.simps(2)
    apply(simp add: simp_ex_assn[OF bplustree_assn_leafs.simps(2)])
    apply(subst reorder_ex(1))
    apply(rule inst_same)+
    apply(subst reorder_ex(2))
    apply(subst reorder_ex(3))
    apply(rule inst_same)+*)
(* pre-massage term for an explicit treatment. ignore inductive assumptions in simp s.t.
bplustree of the last tree does not get simplified away immediately *)
  proof((rule ent_iffI; (rule ent_ex_preI)+),  goal_cases)
    case Istep: (1 tsi ti tsi' tsi'' rs)
    have *: "
        length tsi's = length rss \<Longrightarrow>
        length rss = length tss \<Longrightarrow>
        set tsi's \<subseteq> set tsi' \<Longrightarrow>
        set rss \<subseteq> set rs \<Longrightarrow>
        set tss \<subseteq> set ts \<Longrightarrow>
       blist_assn k tss
        (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) rss)) (separators tsi's)) =
       (\<exists>\<^sub>Asplit. list_assn ((\<lambda> t (ti,r',z',lptrs). bplustree_assn_leafs k t (the ti) r' z' lptrs) \<times>\<^sub>a id_assn) tss 
        (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) (zip rss split))) (separators tsi's)) *
        \<up>(length split = length rss))"
      for rss tsi's tss
    proof (induct arbitrary: ra rule: list_induct3)
      case Nil
      then show ?case
        apply sep_auto
        apply(subst ex_one_point_gen[where v="[]"])
        apply simp_all
        done
    next
    case (Cons subsepi tsi's subleaf rss subsep tss r)
      then show ?case 
        apply (auto simp add: butlast_double_Cons last_double_Cons)
        apply(auto simp add: prod_assn_def split: prod.splits)
      proof(goal_cases)
        case (1 sub sep)
        then have *: "bplustree_assn k sub (the (fst subsepi)) r subleaf = (\<exists>\<^sub>As. bplustree_assn_leafs k sub (the (fst subsepi)) r subleaf s)"
        proof -
          have "subsep \<in> set ts"
            by (simp add: "1"(10) "1"(8))
          moreover obtain temp1 temp2 where "((fst subsepi, (temp1:: 'a btnode ref option), subleaf), (temp2::'a)) \<in> set [((fst subsepi, temp1, subleaf), temp2)]"
            by auto
          ultimately  show ?thesis
            using Istep(2)[of subsep "((fst subsepi, (temp1:: 'a btnode ref option), subleaf), (temp2::'a))" "[((fst subsepi, temp1, subleaf), temp2)]"
                            "fst subsepi" "(temp1, subleaf)" temp1 subleaf r]
            using 1
            by simp
        qed
        show ?case
          apply (simp add: * 1(3)[of subleaf])
          apply(intro ent_iffI)
          subgoal
            apply(intro ent_ex_preI)
            subgoal for split x
            apply(inst_ex_assn "x#split")
              apply simp
              done
            done
          subgoal
            apply(intro ent_ex_preI)
            subgoal for split
              apply(cases split)
              apply simp
            subgoal for hdsplit tlsplit
            apply(inst_ex_assn "tlsplit" "hdsplit")
              apply (auto)
            done
          done
        done
      done
     qed
  qed
  show ?case
    apply(rule entails_preI)
        apply (auto dest!: mod_starD list_assn_len)
    apply(subst *[of tsi' rs ts])
    apply simp_all
    apply(subgoal_tac "bplustree_assn k t ti (last (ra # rs)) z = ex_assn (bplustree_assn_leafs k t ti (last (ra # rs)) z)")
    prefer 2
    subgoal
      using Istep(1)[of ti "last (ra#rs)" "[]", simplified]
      by (simp add: last.simps)
    apply simp
    apply(rule ent_ex_preI)+
    subgoal for _ _ _ _ _ _ split x
      apply(inst_ex_assn "concat (split@[x])")
      apply clarsimp
      apply(inst_ex_assn tsi ti tsi' "zip (zip (subtrees tsi') (zip (butlast (ra # rs)) (zip rs split))) (separators tsi')" rs "split@[x]")
      apply simp
      done
    done
next
  case Istep: (2 x)
  show ?case
    apply (clarsimp)
    apply(intro ent_ex_preI)
    subgoal for tsi ti tsi' split tsi'' rs
(* TODO but should be similar/easier than first proof *)
      sorry
    done
qed
  done
declare last.simps[simp add] butlast.simps[simp add]

fun leaf_nodes_assn :: "nat \<Rightarrow> ('a::heap) bplustree list \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref list \<Rightarrow> assn" where
  "leaf_nodes_assn k ((LNode xs)#lns) (Some r) z (r'#lptrs) = 
 (\<exists>\<^sub>A xsi fwd.
      r \<mapsto>\<^sub>r Btleaf xsi fwd
    * is_pfa (2*k) xs xsi
    * leaf_nodes_assn k lns fwd z lptrs
    * \<up>(r = r')
  )" | 
  "leaf_nodes_assn k [] r z [] = \<up>(r = z)" |
  "leaf_nodes_assn _ _ _ _ _ = false"


fun inner_nodes_assn :: "nat \<Rightarrow> ('a::heap) bplustree \<Rightarrow> 'a btnode ref \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref list \<Rightarrow> assn" where
  "inner_nodes_assn k (LNode xs) a r z lptrs = \<up>(r = Some a \<and> lptrs = [a])" |
  "inner_nodes_assn k (Node ts t) a r z lptrs = 
 (\<exists>\<^sub>A tsi ti tsi' tsi'' rs split.
      a \<mapsto>\<^sub>r Btnode tsi ti
    * inner_nodes_assn k t ti (last (r#rs)) (last (rs@[z])) (last split)
    * is_pfa (2*k) tsi' tsi
    * \<up>(concat split = lptrs)
    * \<up>(length tsi' = length rs)
    * \<up>(length split = length rs + 1)
    * \<up>(tsi'' = zip (zip (map fst tsi') (zip (butlast (r#rs)) (zip (butlast (rs@[z])) (butlast split)))) (map snd tsi'))
    * list_assn ((\<lambda> t (ti,r',z',lptrs). inner_nodes_assn k t (the ti) r' z' lptrs) \<times>\<^sub>a id_assn) ts tsi''
    )"

lemma leaf_nodes_assn_split:
"length xs = length xsi \<Longrightarrow> ysi = (yi#ysr) \<Longrightarrow>
  leaf_nodes_assn k (xs @ ys) r z (xsi @ ysi) = leaf_nodes_assn k xs r (Some yi) xsi * leaf_nodes_assn k ys (Some yi) z ysi"
proof(induction arbitrary: r rule: list_induct2)
  case (Nil r)
  then show ?case
    apply(cases r; cases ys)
    apply clarsimp_all
    subgoal for _ t _
    apply(cases t)
    apply clarsimp
      apply(intro inst_same)
      apply(rule pure_eq_pre)
      apply clarsimp_all
      done
    done
next
  case (Cons x xs xi xsi r)
  show ?case
    apply(cases r; cases x)
    apply clarsimp_all
      apply(intro inst_same)
      apply(rule pure_eq_pre)
      subgoal for a x1 xsi' fwd
      using Cons.IH[of fwd, OF Cons.prems]
      apply (clarsimp simp add: mult.assoc)
      done
    done
qed

lemma "length xs \<noteq> length xsi \<Longrightarrow> leaf_nodes_assn k xs r z xsi = false"
  by (induction rule: leaf_nodes_assn.induct) auto


lemma bplustree_assn_leafs_len_aux: "bplustree_assn_leafs k t a r z leafptrs = bplustree_assn_leafs k t a r z leafptrs * \<up>(length leafptrs = length (leaf_nodes t))"  
  apply(induction k t a r z leafptrs rule: bplustree_assn_leafs.induct)
  subgoal 
    apply(clarsimp)
    apply(intro ent_iffI)
    apply sep_auto+
    done
  sorry

lemma inner_nodes_assn_len_aux: "inner_nodes_assn k t a r z leafptrs = inner_nodes_assn k t a r z leafptrs * \<up>(length leafptrs = length (leaf_nodes t))"  
  apply(induction k t a r z leafptrs rule: inner_nodes_assn.induct)
  subgoal
    apply(clarsimp)
    apply sep_auto
    done
  sorry

lemma leaf_nodes_not_empty: "leaf_nodes t \<noteq> []"
  by (induction t) auto

declare last.simps[simp del] butlast.simps[simp del]
lemma bplustree_assn_leafs_not_empty_aux: "bplustree_assn_leafs k t a r z leafptrs = bplustree_assn_leafs k t a r z leafptrs * \<up>(leafptrs \<noteq> [])"
  apply(intro ent_iffI)
  subgoal 
    apply(subst bplustree_assn_leafs_len_aux)
    using leaf_nodes_not_empty
    apply sep_auto
  done
  subgoal by sep_auto
  done

lemma inner_nodes_assn_not_empty_aux: "inner_nodes_assn k t a r z leafptrs = inner_nodes_assn k t a r z leafptrs * \<up>(leafptrs \<noteq> [])"
  apply(intro ent_iffI)
  subgoal 
    apply(subst inner_nodes_assn_len_aux)
    using leaf_nodes_not_empty
    apply sep_auto
  done
  subgoal by sep_auto
  done
declare last.simps[simp add] butlast.simps[simp add]
(*proof(induction k t a r z leafptrs rule: bplustree_assn_leafs.induct)
  case (1 k xs a r z leafptrs)
  then show ?case
    apply(clarsimp)
    apply(intro ent_iffI)
    apply sep_auto+
    done
next
  case (2 k ts t a r z leafptrs)
  show ?case
    apply clarsimp
    apply(intro inst_same)
    subgoal for tsi ti tsi' tsi'' rs split
      thm "2.IH"(1)[of ti rs split, simplified]
    apply(subst (1 2) "2.IH"(1)[of ti rs split, simplified])
      apply (intro ent_iffI)
      subgoal
        apply sep_auto
        apply (metis List.last_in_set length_0_conv length_Cons list.distinct(1))
        done
      subgoal by sep_auto
      done
    done
qed*)
lemma bplustree_assn_leafs_hd:
  "bplustree_assn_leafs k t a r z leafptrs = bplustree_assn_leafs k t a r z leafptrs * \<up>(r = Some (hd leafptrs))"  
  apply(induction k t a r z leafptrs rule: bplustree_assn_leafs.induct)
  subgoal 
    apply(clarsimp)
    apply(intro ent_iffI)
    apply sep_auto+
    done
  sorry

lemma inner_nodes_assn_hd:
  "inner_nodes_assn k t a r z leafptrs = inner_nodes_assn k t a r z leafptrs * \<up>(r = Some (hd leafptrs))"  
  apply(induction k t a r z leafptrs rule: bplustree_assn_leafs.induct)
  subgoal 
    apply(clarsimp)
    apply auto
    done
  sorry

declare last.simps[simp del] butlast.simps[simp del]
lemma subleaf_at_head_of_concat_inner: "length tsi's = length rss \<Longrightarrow>
        length rss = length tss \<Longrightarrow>
        length tss = length splits \<Longrightarrow>
list_assn ((\<lambda>t (ti, x, xa, y). inner_nodes_assn k t (the ti) x xa y) \<times>\<^sub>a R) tss
     (zip (zip (subtrees tsi's) (zip (butlast (subleaf # rss)) (zip rss splits)))
       (separators tsi's)) *
    inner_nodes_assn k t ti (last (subleaf # rss)) z ss
= 
list_assn ((\<lambda>t (ti, x, xa, y). inner_nodes_assn k t (the ti) x xa y) \<times>\<^sub>a R) tss
     (zip (zip (subtrees tsi's) (zip (butlast (subleaf # rss)) (zip rss splits)))
       (separators tsi's)) *
    inner_nodes_assn k t ti (last (subleaf # rss)) z ss * \<up>(Some (hd (concat splits@ss)) = subleaf)"
  apply(cases splits)
  subgoal
    apply (sep_auto simp add: last.simps)
    apply (metis (mono_tags, hide_lams) inner_nodes_assn_hd pure_assn_eq_conv)
    done
  subgoal
  apply(cases tss; cases rss; cases tsi's)
  apply simp_all
        apply (sep_auto
                simp add: butlast_double_Cons last_double_Cons)
  apply(intro ent_iffI)
    subgoal
      apply(subst inner_nodes_assn_hd)
      apply(subst inner_nodes_assn_not_empty_aux)
      apply sep_auto
      done
    subgoal by sep_auto
    done
  done

lemma subleaf_at_head_of_concat_bplustree: "length tsi's = length rss \<Longrightarrow>
        length rss = length tss \<Longrightarrow>
        length tss = length splits \<Longrightarrow>
list_assn ((\<lambda>t (ti, x, xa, y). bplustree_assn_leafs k t (the ti) x xa y) \<times>\<^sub>a R) tss
     (zip (zip (subtrees tsi's) (zip (butlast (subleaf # rss)) (zip rss splits)))
       (separators tsi's)) *
    bplustree_assn_leafs k t ti (last (subleaf # rss)) z ss
= 
list_assn ((\<lambda>t (ti, x, xa, y). bplustree_assn_leafs k t (the ti) x xa y) \<times>\<^sub>a R) tss
     (zip (zip (subtrees tsi's) (zip (butlast (subleaf # rss)) (zip rss splits)))
       (separators tsi's)) *
    bplustree_assn_leafs k t ti (last (subleaf # rss)) z ss * \<up>(Some (hd (concat splits@ss)) = subleaf)"
  apply(cases splits)
  subgoal
    apply (sep_auto simp add: last.simps)
    apply (metis (mono_tags, hide_lams) bplustree_assn_leafs_hd pure_assn_eq_conv)
    done
  subgoal
  apply(cases tss; cases rss; cases tsi's)
  apply simp_all
        apply (sep_auto
                simp add: butlast_double_Cons last_double_Cons)
  apply(intro ent_iffI)
    subgoal
      apply(subst bplustree_assn_leafs_hd)
      apply(subst bplustree_assn_leafs_not_empty_aux)
      apply sep_auto
      done
    subgoal by sep_auto
    done
  done
declare last.simps[simp add] butlast.simps[simp add]

declare last.simps[simp add] butlast.simps[simp add]
lemma otf_mult_comm_lem:
"(a::'a::{comm_monoid_mult}) * b * c * d  * e * f = a * b * c * d * (e * f)"
"a * b * c * d = b * c * (d * a)"
"a * b * c * d = a * c * (b * d)"
"a * b * c * d * e = (a * e * c) * b * d"
  by (clarsimp_all simp add: algebra_simps)

lemma concat_butlast_last_id: "xs \<noteq> [] \<Longrightarrow> concat (butlast xs) @ (last xs) = concat xs"
  by (metis append_butlast_last_id append_self_conv concat.simps(1) concat.simps(2) concat_append)

declare last.simps[simp del] butlast.simps[simp del]
lemma bplustree_leaf_nodes_sep:
  "bplustree_assn_leafs k t ti r z lptrs = leaf_nodes_assn k (leaf_nodes t) r z lptrs * inner_nodes_assn k t ti r z lptrs"
proof(induction arbitrary: r rule: bplustree_assn_leafs.induct)
  case (1 k xs a r z)
  then show ?case
    apply(intro ent_iffI)
    apply sep_auto+
    done
next
  case (2 k ts t a r z lptrs ra)
  show ?case
      apply simp
    apply(intro inst_same)
    apply (clarsimp simp add: mult.left_assoc)
    apply(intro pure_eq_pre)
    apply(clarsimp)
    proof(goal_cases)
      case (1 tsia tsin ti tsi' rs split)
      have *: "
          length tsi's = length rss \<Longrightarrow>
          length rss = length tss \<Longrightarrow>
          length tss = length splits \<Longrightarrow>
          set tsi's \<subseteq> set tsi' \<Longrightarrow>
          set rss \<subseteq> set rs \<Longrightarrow>
          set tss \<subseteq> set ts \<Longrightarrow>
          set splits \<subseteq> set split \<Longrightarrow>
         bplustree_assn_leafs k t ti (last (ra # rss)) z (last split)* 
         list_assn ((\<lambda>t (ti, x, y, s). bplustree_assn_leafs k t (the ti) x y s) \<times>\<^sub>a id_assn) tss
         (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) (zip rss splits))) (separators tsi's)) =
         leaf_nodes_assn k (concat (map (leaf_nodes \<circ> fst) tss) @ leaf_nodes t) ra z (concat splits @ last split) *
         list_assn ((\<lambda>t (ti, x, y, s). inner_nodes_assn k t (the ti) x y s) \<times>\<^sub>a id_assn) tss
         (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) (zip rss splits))) (separators tsi's)) *
        inner_nodes_assn k t ti (last (ra#rss)) z (last split)"
        for rss tsi's tss splits
      proof (induct arbitrary: ra rule: list_induct4)
        case (Nil r)
        then show ?case
          apply(clarsimp)
          using 2(1)[of ti r "[]" "split"]
          apply (simp add: last.simps)
          done
      next
        case (Cons subsepi tsi's subleaf rss subsep tss fsplit splits r)
        show ?case 
        apply (sep_auto
                simp add: butlast_double_Cons last_double_Cons)
          apply(subst prod_assn_def)+
        apply(simp split!: prod.splits add: mult.left_assoc)
          subgoal for sub sep
(* extract fact that length of leaf nodes of subleaf matches leaf_nodes_assn_split req *)
          apply(subst bplustree_assn_leafs_len_aux[of k sub])
          apply(subst inner_nodes_assn_len_aux[of k sub])
            apply sep_auto
            apply(intro pure_eq_pre)
(* extract fact that the remaining list is not empty *)
          apply(subst bplustree_assn_leafs_not_empty_aux[of k t])
          apply(subst inner_nodes_assn_not_empty_aux[of k t])
            apply sep_auto
            apply(intro pure_eq_pre)
          supply R = leaf_nodes_assn_split[of "leaf_nodes sub" fsplit
                                        "concat splits @ last split" "hd (concat splits @ last split)" "tl (concat splits @ last split)"]
          thm R
        apply(subst R)
          subgoal by simp
          subgoal by simp
          (* show that r = hd fsplit *)
          apply(subst bplustree_assn_leafs_hd[of k sub])
          apply(subst inner_nodes_assn_hd[of k sub])
            apply sep_auto
            apply(intro pure_eq_pre)
(* refactor multiplication s.t. we can apply the lemma about two mult. factors with an OTF lemma *)
          apply(subst otf_mult_comm_lem(1))
          apply(subst subleaf_at_head_of_concat_inner)
          subgoal using Cons by simp
          subgoal using Cons by simp
          subgoal using Cons by simp
          apply(simp add: mult.left_assoc)
(* refactor multiplication s.t. we can apply the lemma about two mult. factors with an OTF lemma *)
          apply(subst otf_mult_comm_lem(2))
          apply(subst subleaf_at_head_of_concat_bplustree)
          subgoal using Cons by simp
          subgoal using Cons by simp
          subgoal using Cons by simp
          apply(simp add: mult.left_assoc)
            apply(intro pure_eq_pre)
        proof(goal_cases)
          case 1
          moreover have p: "set tsi's \<subseteq> set tsi'"
               "set rss \<subseteq> set rs"
               "set tss \<subseteq> set ts"
               "set splits \<subseteq> set split"
            using Cons.prems by auto
          moreover have "(sub,sep) \<in> set ts"
            using "1" Cons.prems(3) by force
          moreover obtain temp1 temp2 where "((fst subsepi, (temp1:: 'a btnode ref option), subleaf, fsplit), (temp2::'a)) \<in> set [((fst subsepi, temp1, subleaf, fsplit), temp2)]"
            by auto
          ultimately show ?case
            apply(inst_ex_assn subleaf)
            using "Cons.hyps"(4)[of subleaf, OF p, simplified]
            apply (auto simp add: algebra_simps)
            using "2.IH"(2)[of subsep "((fst subsepi, temp1, subleaf, fsplit),temp2)" "[((fst subsepi, temp1, subleaf, fsplit),temp2)]"
                "fst subsepi" "(temp1, subleaf, fsplit)" temp1 "(subleaf, fsplit)" subleaf fsplit r, simplified]
            apply auto
            using assn_times_assoc ent_refl by presburger
        qed
        done
    qed
      show ?case
        apply(intro ent_iffI)
        subgoal
         apply(rule entails_preI)
          using 1
        apply(auto dest!: mod_starD list_assn_len)
        apply(subst otf_mult_comm_lem(3))
          apply (subst *[of tsi' rs ts "butlast split", simplified])
          subgoal by auto
          subgoal by auto
          subgoal by auto
          subgoal by (meson in_set_butlastD subset_code(1))
          subgoal
          apply(subgoal_tac "concat (butlast split) @ (last split) = concat split") 
            prefer 2
              subgoal
                apply(subst concat_butlast_last_id)
                apply auto
                done
              subgoal by sep_auto
              done
            done
      subgoal
         apply(rule entails_preI)
        using 1
        apply(auto dest!: mod_starD list_assn_len)
          apply(subgoal_tac "concat split = concat (butlast split) @ (last split)") 
            prefer 2
              subgoal
                apply(subst concat_butlast_last_id)
                apply auto
                done
        apply(subst otf_mult_comm_lem(4))
              apply simp
              apply(subst *[of tsi' rs ts "butlast split", simplified, symmetric])
          subgoal by auto
          subgoal by auto
          subgoal by auto
          subgoal by (meson in_set_butlastD subset_code(1))
          subgoal by sep_auto
        done
      done
    qed
  qed
declare last.simps[simp add] butlast.simps[simp add]

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
        moreover obtain temp1 temp2 where "((fst subsepi, (temp1:: 'a btnode ref option), subleaf), (temp2::'a)) \<in> set [((fst subsepi, temp1, subleaf), temp2)]"
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
    id_assn sep (snd subsepi) *
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
  using bplustree_leaf_nodes_help[of k t ti r z] by simp

fun leaf_node:: "('a::heap) bplustree \<Rightarrow> 'a list \<Rightarrow> assn" where
  "leaf_node (LNode xs) xsi = \<up>(xs = xsi)" |
  "leaf_node _ _ = false"

fun leafs_assn :: "('a::heap) pfarray list \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref option \<Rightarrow> assn" where
  "leafs_assn (ln#lns) (Some r) z = 
 (\<exists>\<^sub>A fwd.
      r \<mapsto>\<^sub>r Btleaf ln fwd
    * leafs_assn lns fwd z
  )" | 
  "leafs_assn [] r z = \<up>(r = z)" |
  "leafs_assn _ _ _ = false"

lemma leafs_assn_aux_append:
   "leafs_assn (xs@ys) r z = (\<exists>\<^sub>Al. leafs_assn xs r l * leafs_assn ys l z)"
  apply(induction xs r z rule: leafs_assn.induct)
  apply(sep_auto intro!: ent_iffI)+
  done

lemma leaf_nodes_assn_split:
  "leaf_nodes_assn k ts r z = (\<exists>\<^sub>Aps. list_assn leaf_node ts (map bplustree.vals ts) * list_assn (is_pfa (2*k)) (map bplustree.vals ts) ps * leafs_assn ps r z)"
proof (induction ts arbitrary: r)
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
      subgoal for aa x1 xsi fwd
      apply (subst "Cons.IH"[of fwd]) 
        apply simp
      apply(rule ent_ex_preI)+
        subgoal for ps
          apply(inst_ex_assn "xsi#ps")
          apply simp_all
          apply(inst_ex_assn fwd)
          apply (sep_auto)
          done
        done
      done
  next
    case 2
    have *: "list_assn leaf_node xs (map bplustree.vals xs) * list_assn (is_pfa (2 * k)) (map bplustree.vals xs) ps' * leafs_assn ps' r' z
          \<Longrightarrow>\<^sub>A leaf_nodes_assn k xs r' z" 
      for ps' r'
      using assn_eq_split(1)[OF sym[OF "Cons.IH"[of r']]]
             ent_ex_inst[where Q="leaf_nodes_assn k xs r' z" and y=ps']
      by blast
    show ?case
      apply(rule ent_ex_preI)+
      subgoal for ps
        apply(cases ps; cases r; cases a)
      apply simp_all
      apply(rule ent_ex_preI)+
        subgoal for aa list aaa x1 fwd
          apply(inst_ex_assn aa fwd)
          apply sep_auto
          using *[of list fwd]
          by (smt (z3) assn_aci(9) assn_times_comm fr_refl)
        done
      done
  qed
qed

lemma inst_same: "(\<And>x. P x = Q x) \<Longrightarrow> (\<exists>\<^sub>A x. P x) = (\<exists>\<^sub>A x. Q x)"
  by simp

lemma inst_same2: "(\<And>x. P = Q x) \<Longrightarrow> P = (\<exists>\<^sub>A x. Q x)"
  by simp

lemma pure_eq_pre: "(P \<Longrightarrow> Q = R) \<Longrightarrow> (Q * \<up>P = R * \<up>P)"
  by fastforce

lemma bplustree_leaf_nodes_sep:
  "leaf_nodes_assn k (leaf_nodes t) r z * (leaf_nodes_assn k (leaf_nodes t) r z -* bplustree_assn k t ti r z) \<Longrightarrow>\<^sub>A bplustree_assn k t ti r z"
  by (simp add: ent_mp)

declare last.simps[simp del] butlast.simps[simp del]
lemma bplustree_leaf_nodes_sep:
  "bplustree_assn k t ti r z = leaf_nodes_assn k (leaf_nodes t) r z * (leaf_nodes_assn k (leaf_nodes t) r z -* bplustree_assn k t ti r z)"
proof(induction arbitrary: r rule: bplustree_assn.induct)
  case (1 k xs a r z)
  then show ?case
    apply(intro ent_iffI)
    prefer 2
    using bplustree_leaf_nodes_sep apply blast
    apply auto
    apply (cases r)
    apply (sep_auto eintros del: exI)+
    by (smt (verit, del_insts) ent_star_mono ent_wandI2 mult.right_neutral wand_ent_self)
next
  case (2 k ts t a r z ra)
  show ?case
      apply simp
    apply(rule inst_same)+
    apply(rule pure_eq_pre)
    proof(goal_cases)
      case (1 tsi ti tsi' tsi'' rs)
      have *: "
          length tsi's = length rss \<Longrightarrow>
          length rss = length tss \<Longrightarrow>
          set tsi's \<subseteq> set tsi' \<Longrightarrow>
          set rss \<subseteq> set rs \<Longrightarrow>
          set tss \<subseteq> set ts \<Longrightarrow>
         bplustree_assn k t ti (last (ra # rss)) z * 
         blist_assn k tss
          (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) rss)) (separators tsi's)) =
         leaf_nodes_assn k (concat (map (leaf_nodes \<circ> fst) tss) @ leaf_nodes t) ra z *
         list_assn ((\<lambda>t (ti, x, y). inner_nodes_assn k t (the ti) x y) \<times>\<^sub>a id_assn) tss
         (zip (zip (subtrees tsi's) (zip (butlast (ra # rss)) rss)) (separators tsi's)) *
        inner_nodes_assn k t ti (last (ra#rss)) z"
        for rss tsi's tss
      proof (induct arbitrary: ra rule: list_induct3)
        case (Nil r)
        then show ?case
          apply sep_auto
          using 2(1)[of ti r]
          apply (simp add: last.simps)
          done
      next
        case (Cons subsepi tsi's subleaf rss subsep tss r)
        show ?case 
        apply (sep_auto
                simp add: butlast_double_Cons last_double_Cons)
          apply(subst prod_assn_def)
        apply(simp split!: prod.splits add: mult.left_assoc)
        (*apply(subst leaf_nodes_assn_split_spec)*)
        proof(goal_cases)
          case (1 sub sep)
          moreover have p: "set tsi's \<subseteq> set tsi'"
               "set rss \<subseteq> set rs"
               "set tss \<subseteq> set ts"
            using Cons.prems by auto
          moreover have "(sub,sep) \<in> set ts"
            using "1" Cons.prems(3) by force
          moreover obtain temp1 temp2 where "((fst subsepi, (temp1:: 'a btnode ref option), subleaf), (temp2::'a)) \<in> set [((fst subsepi, temp1, subleaf), temp2)]"
            by auto
          ultimately show ?case
            apply(inst_ex_assn subleaf)
            using "Cons.hyps"(3)[of subleaf, OF p]
            apply (auto simp add: algebra_simps)
            using "2.IH"(2)[of subsep "((fst subsepi, (temp1, subleaf)),temp2)" "[((fst subsepi, (temp1, subleaf)),temp2)]"
                "fst subsepi" "(temp1, subleaf)" temp1 subleaf r]
            apply auto
            using assn_times_assoc ent_refl by presburger
        qed
      qed
      show ?case
        apply(intro ent_iffI)
        subgoal
         apply(rule entails_preI)
          using 1
        apply(auto dest!: mod_starD list_assn_len)
        using *[of tsi' rs ts, simplified]
        apply (smt (z3) assn_aci(10) assn_times_comm entails_def)
        done
      subgoal
         apply(rule entails_preI)
        using 1
        apply(auto dest!: mod_starD list_assn_len)
        using *[of tsi' rs ts, simplified]
        apply (smt (z3) assn_aci(10) assn_times_comm entails_def)
        done
      done
    qed
  qed
declare last.simps[simp add] butlast.simps[simp add]

(* this doesn't hold, we need to know more about the remaining list,
specifically because inner_nodes_assn doesn't say anything about next pointers *)
lemma leaf_nodes_assn_split_spec: "leaf_nodes_assn k
        (leaf_nodes x @ ys) r z *
       inner_nodes_assn k x a r m =
      leaf_nodes_assn k (leaf_nodes x) r m * leaf_nodes_assn k ys m z *
       inner_nodes_assn k x a r m"
proof(induction x)
  case (LNode x)
  then show ?case 
    apply auto
    oops



(* TODO find a statement that cleanly separates the heap *)

subsection "Iterator"

partial_function (heap) first_leaf :: "('a::heap) btnode ref \<Rightarrow> 'a btnode ref option Heap"
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

partial_function (heap) last_leaf :: "('a::heap) btnode ref \<Rightarrow> 'a btnode ref option Heap"
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


definition tree_leaf_iter_init where
"tree_leaf_iter_init p = do {
  r \<leftarrow> first_leaf (the p);
  z \<leftarrow> last_leaf (the p);
  return  (r, z)
}"

lemma tree_leaf_iter_init_rule:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn k t ti r z>
  tree_leaf_iter_init (Some ti)
  <\<lambda>(u,v). leaf_nodes_assn k (leaf_nodes t) u v * \<up>(u = r \<and> v = z)>\<^sub>t"
  using assms
  using bplustree_leaf_nodes_help[of k t ti r z]
  unfolding tree_leaf_iter_init_def
  by (sep_auto)


definition leaf_iter_next where
"leaf_iter_next = (\<lambda>(r,z). do {
  p \<leftarrow> !(the r);
  return (vals p, (fwd p, z))
})"

lemma leaf_iter_next_rule_help:
  "<leafs_assn (x#xs) r z>
      leaf_iter_next (r,z)
   <\<lambda>(p,(n,z')). leafs_assn [x] r n * leafs_assn xs n z' * \<up>(p = x) * \<up>(z=z')>"
  apply(subst leaf_iter_next_def)
  apply(cases r; cases x)
  apply(sep_auto)+
  done

definition leaf_iter_assn where "leaf_iter_assn xs r xs2 = (\<lambda>(n,z). 
  (\<exists>\<^sub>Axs1. \<up>(xs = xs1@xs2) * leafs_assn xs1 r n * leafs_assn xs2 n z * \<up>(z=None)))" 

lemma leaf_nodes_assn_imp_iter_assn: "leafs_assn xs r None \<Longrightarrow>\<^sub>A leaf_iter_assn xs r xs (r,None)"
  unfolding leaf_iter_assn_def
  by sep_auto

definition leaf_iter_init where
"leaf_iter_init p = do {
  return  (p, None)
}"

lemma leaf_iter_init_rule:
  shows "<leafs_assn xs r None>
  leaf_iter_init r
  <\<lambda>u. leaf_iter_assn xs r xs u>"
  unfolding leaf_iter_init_def
  using leaf_nodes_assn_imp_iter_assn
  by (sep_auto)

lemma leaf_iter_next_rule: "<leaf_iter_assn xs r (x#xs2) it>
leaf_iter_next it
<\<lambda>(p, it'). leaf_iter_assn xs r xs2 it' * \<up>(p = x)>"
  unfolding leaf_iter_assn_def
  apply(cases it)
  by (sep_auto heap add: leaf_iter_next_rule_help simp add: leafs_assn_aux_append)

definition leaf_iter_has_next where
"leaf_iter_has_next  = (\<lambda>(r,z). return (r \<noteq> z))"

(* TODO this so far only works for the whole tree (z = None)
for subintervals, we would need to show that the list of pointers is indeed distinct,
hence r = z can only occur at the end *)
lemma leaf_iter_has_next_rule:
  "<leaf_iter_assn xs r xs2 it> leaf_iter_has_next it <\<lambda>u. leaf_iter_assn xs r xs2 it * \<up>(u \<longleftrightarrow> xs2 \<noteq> [])>"
  unfolding leaf_iter_has_next_def
  apply(cases it)
  apply(sep_auto simp add: leaf_iter_assn_def split!: prod.splits dest!: mod_starD)
  subgoal for a
  apply(cases xs2; cases a)
    by auto
  done

(* copied from peter lammichs lseg_prec2 *)
declare mult.left_commute[simp add]
lemma leafs_assn_prec2: 
  "\<forall>l l'. (h\<Turnstile>
      (leafs_assn l p None * F1) \<and>\<^sub>A (leafs_assn l' p None * F2)) 
    \<longrightarrow> l=l'"
  apply (intro allI)
  subgoal for l l'
  proof (induct l arbitrary: p l' F1 F2)
    case Nil thus ?case
      apply simp_all
      apply (cases l')
      apply simp
      apply (cases p)
      apply auto
      done
  next
    case (Cons y l)
    from Cons.prems show ?case
      apply (cases p)
      apply simp
      apply (cases l')
      apply (auto) []
      apply (clarsimp)
      apply (rule)
      apply (drule_tac p=a in prec_frame[OF sngr_prec])
      apply frame_inference
      apply frame_inference
      apply simp
      subgoal for a aa b list fwd fwda
        apply(subgoal_tac "fwd=fwda")
      using Cons.hyps[of fwd "a \<mapsto>\<^sub>r Btleaf y fwda * F1" list "a \<mapsto>\<^sub>r Btleaf (aa, b) fwd * F2", simplified]
       apply (simp add: mult.left_assoc mod_and_dist)
      apply (simp add: ab_semigroup_mult_class.mult.commute)
      apply (drule_tac p=a in prec_frame[OF sngr_prec])
      apply frame_inference
      apply frame_inference
      apply simp
      done
    done
  qed
  done
declare mult.left_commute[simp del]

interpretation leaf_node_it: imp_list_iterate
    "\<lambda>x y. leafs_assn x y None"
    leaf_iter_assn
    leaf_iter_init
    leaf_iter_has_next
    leaf_iter_next
  apply(unfold_locales)
  subgoal 
    by (simp add: leafs_assn_prec2 precise_def)
  subgoal for l p 
    by (sep_auto heap add: leaf_iter_init_rule)
  subgoal for l' l p it
    thm leaf_iter_next_rule
    apply(cases l'; cases it)
    by (sep_auto heap add: leaf_iter_next_rule)+
  subgoal for l p l' it'
    thm leaf_iter_has_next_rule
    apply(cases it')
    apply(rule hoare_triple_preI)
    apply(sep_auto heap add: leaf_iter_has_next_rule)
    done
  subgoal for l p l' it
  unfolding leaf_iter_assn_def
  apply(cases it)
    apply simp_all
  apply(rule ent_ex_preI)
  by (sep_auto simp add: leafs_assn_aux_append)
  done

interpretation leaf_elements_iter: flatten_iter
  "\<lambda>x y. leafs_assn x y None" leaf_iter_assn leaf_iter_init leaf_iter_has_next leaf_iter_next
  "is_pfa (2*k)" "pfa_is_it (2*k)" pfa_it_init pfa_it_has_next pfa_it_next
  by (unfold_locales)

thm leaf_elements_iter.is_flatten_list.simps
thm leaf_elements_iter.is_flatten_it.simps
thm tree_leaf_iter_init_def
thm leaf_elements_iter.flatten_it_init_def
print_theorems

fun leaf_elements_iter_init :: "('a::heap) btnode ref \<Rightarrow> _" where
  "leaf_elements_iter_init ti = do {
        rz \<leftarrow> tree_leaf_iter_init (Some ti);
        it \<leftarrow> leaf_elements_iter.flatten_it_init (fst rz);
        return it
}"


(* NOTE: the other direction does not work, we are loosing information here
  workaround: introduce specialized is_flatten_list assumption, show that all operations
  preserve its correctness
*)
lemma leaf_nodes_imp_flatten_list:
  "leaf_nodes_assn k ts r None \<Longrightarrow>\<^sub>A
   list_assn leaf_node ts (map bplustree.vals ts) *
   leaf_elements_iter.is_flatten_list k (concat (map bplustree.vals ts)) r"
  apply(simp add: leaf_nodes_assn_split)
  apply(rule ent_ex_preI)+
  subgoal for ps
    apply(inst_ex_assn ps "map bplustree.vals ts")
    apply sep_auto
    done
  done

lemma concat_leaf_nodes_leaves: "(concat (map bplustree.vals (leaf_nodes t))) = leaves t"
  apply(induction t rule: leaf_nodes.induct)
  subgoal by auto
  subgoal for ts t
    apply(induction ts)
    apply simp
    apply auto
    done
  done

lemma leaf_elements_iter_init_rule:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn k t ti r None>
leaf_elements_iter_init ti
<leaf_elements_iter.is_flatten_it k (leaves t) r (leaves t)>\<^sub>t"
  unfolding leaf_elements_iter_init.simps
  using assms 
  apply (sep_auto heap add:
      tree_leaf_iter_init_rule
  )
    find_theorems "<_>_<_>" "_\<Longrightarrow>\<^sub>A_"
    supply R = Hoare_Triple.cons_pre_rule[OF leaf_nodes_imp_flatten_list[of k "leaf_nodes t" r],
        where Q="\<lambda>it. leaf_elements_iter.is_flatten_it k (leaves t) r (leaves t) it * true"
        and c="leaf_elements_iter.flatten_it_init r"]
    thm R
    apply(sep_auto heap add: R)
    apply(simp add: concat_leaf_nodes_leaves)
    apply sep_auto
    apply sep_auto
    done

end