theory Basic_Assn
  imports
    "Refine_Imperative_HOL.Sepref_HOL_Bindings"
    "Refine_Imperative_HOL.Sepref_Basic"
begin

section "Auxilary imperative assumptions"

text "The following auxiliary assertion types and lemmas were provided by Peter Lammich"

subsection \<open>List-Assn\<close>



lemma list_assn_cong[fundef_cong]:
  "\<lbrakk> xs=xs'; ys=ys'; \<And>x y. \<lbrakk> x\<in>set xs; y\<in>set ys \<rbrakk> \<Longrightarrow> A x y = A' x y \<rbrakk> \<Longrightarrow> list_assn A xs ys = list_assn A' xs' ys'"
  by (induction xs ys arbitrary: xs' ys' rule: list_assn.induct) auto


lemma list_assn_app_one: "list_assn P (l1@[x]) (l1'@[y]) = list_assn P l1 l1' * P x y"
  by simp

(* ------------------ ADDED by NM in course of btree_imp -------- *)


lemma list_assn_len: "h \<Turnstile> list_assn A xs ys \<Longrightarrow> length xs = length ys"
  using list_assn_aux_ineq_len by fastforce


lemma list_assn_append_Cons_left: "list_assn A (xs@x#ys) zs = (\<exists>\<^sub>A zs1 z zs2. list_assn A xs zs1 * A x z * list_assn A ys zs2 * \<up>(zs1@z#zs2 = zs))"
  by (sep_auto simp add: list_assn_aux_cons_conv list_assn_aux_append_conv1 intro!: ent_iffI)


lemma list_assn_aux_append_Cons: 
  shows "length xs = length zsl \<Longrightarrow> list_assn A (xs@x#ys) (zsl@z#zsr) = (list_assn A xs zsl * A x z * list_assn A ys zsr) "
  by (sep_auto simp add: mult.assoc)


(* -------------------------------------------- *)

subsection \<open>Prod-Assn\<close>


lemma prod_assn_cong[fundef_cong]:
  "\<lbrakk> p=p'; pi=pi'; A (fst p) (fst pi) = A' (fst p) (fst pi); B (snd p) (snd pi) = B' (snd p) (snd pi) \<rbrakk> 
    \<Longrightarrow> (A\<times>\<^sub>aB) p pi = (A'\<times>\<^sub>aB') p' pi'" 
  apply (cases p; cases pi)
  by auto

(*
subsection \<open>Four-List-Assn\<close>


fun four_list_assn :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'd list \<Rightarrow> assn" where
  "four_list_assn P [] [] [] [] = emp"
| "four_list_assn P (a#as) (b#bs) (c#cs) (d#ds) = P a b c d * four_list_assn P as bs cs ds"
| "four_list_assn _ _ _ _ _ = false"

lemma four_list_assn_aux_simps[simp]:
  "four_list_assn P [] l' l'' l''' = (\<up>(l'=[] \<and> l''=[] \<and> l'''=[]))"
  "four_list_assn P l [] l'' l''' = (\<up>(l=[] \<and> l''=[] \<and> l'''=[]))"
  "four_list_assn P l l' [] l''' = (\<up>(l=[] \<and> l'=[] \<and> l'''=[]))"
  "four_list_assn P l l' l'' [] = (\<up>(l=[] \<and> l'=[] \<and> l''=[]))"
  subgoal by (cases l; cases l'; cases l''; cases l''') auto
  subgoal by (cases l; cases l'; cases l''; cases l''') auto
  subgoal by (cases l; cases l'; cases l''; cases l''') auto
  subgoal by (cases l; cases l'; cases l''; cases l''') auto
  done

lemma four_list_assn_aux_append[simp]:
  "length l1=length l1' \<Longrightarrow> 
  length l1'=length l1'' \<Longrightarrow> 
  length l1''=length l1''' \<Longrightarrow> 
    four_list_assn P (l1@l2) (l1'@l2') (l1''@l2'') (l1'''@l2''')
    = four_list_assn P l1 l1' l1'' l1''' * four_list_assn P l2 l2' l2'' l2'''"
  apply (induct rule: list_induct4)
  apply simp
  apply (auto simp add: star_assoc)
  done

lemma four_list_assn_aux_ineq_len: "length l \<noteq> length l' \<or> length l' \<noteq> length l'' \<or> length l'' \<noteq> length l''' \<Longrightarrow> four_list_assn A l l' l'' l''' = false"
proof (induction l arbitrary: l' l'' l''')
  case (Cons x l l' l'' l''') thus ?case by (cases l'; cases l''; cases l'''; auto)
qed auto

lemma four_list_assn_aux_append2[simp]:
  assumes "length l2=length l2'" "length l2'=length l2''" "length l2''=length l2'''" 
    shows "four_list_assn P (l1@l2) (l1'@l2') (l1''@l2'') (l1'''@l2''')
    = four_list_assn P l1 l1' l1'' l1''' * four_list_assn P l2 l2' l2'' l2'''"
  apply (cases "length l1 = length l1' \<and> length l1' = length l1'' \<and> length l1'' = length l1'''")
  subgoal by (simp; erule four_list_assn_aux_append)
  subgoal by (simp add: four_list_assn_aux_ineq_len assms)
  done

lemma list_assn_pure_conv[constraint_simps]: "list_assn (pure R) = pure (\<langle>R\<rangle>list_rel)"
proof (intro ext)
  fix l li
  show "list_assn (pure R) l li = pure (\<langle>R\<rangle>list_rel) l li"
    apply (induction "pure R" l li rule: list_assn.induct)
    by (auto simp: pure_def)
qed

lemmas [sepref_import_rewrite, sepref_frame_normrel_eqs, fcomp_norm_unfold] = list_assn_pure_conv[symmetric]


lemma list_assn_simps[simp]:
  "hn_ctxt (list_assn P) [] l' = (\<up>(l'=[]))"
  "hn_ctxt (list_assn P) l [] = (\<up>(l=[]))"
  "hn_ctxt (list_assn P) [] [] = emp"
  "hn_ctxt (list_assn P) (a#as) (c#cs) = hn_ctxt P a c * hn_ctxt (list_assn P) as cs"
  "hn_ctxt (list_assn P) (a#as) [] = false"
  "hn_ctxt (list_assn P) [] (c#cs) = false"
  unfolding hn_ctxt_def
  apply (cases l')
  apply simp
  apply simp
  apply (cases l)
  apply simp
  apply simp
  apply simp_all
  done

lemma list_assn_precise[constraint_rules]: "precise P \<Longrightarrow> precise (list_assn P)"
proof
  fix l1 l2 l h F1 F2
  assume P: "precise P"
  assume "h\<Turnstile>list_assn P l1 l * F1 \<and>\<^sub>A list_assn P l2 l * F2"
  thus "l1=l2"
  proof (induct l arbitrary: l1 l2 F1 F2)
    case Nil thus ?case by simp
  next
    case (Cons a ls)
    from Cons obtain a1 ls1 where [simp]: "l1=a1#ls1"
      by (cases l1, simp)
    from Cons obtain a2 ls2 where [simp]: "l2=a2#ls2"
      by (cases l2, simp)
    
    from Cons.prems have M:
      "h \<Turnstile> P a1 a * list_assn P ls1 ls * F1 
        \<and>\<^sub>A P a2 a * list_assn P ls2 ls * F2" by simp
    have "a1=a2"
      apply (rule preciseD[OF P, where a=a1 and a'=a2 and p=a
        and F= "list_assn P ls1 ls * F1" 
        and F'="list_assn P ls2 ls * F2"
        ])
      using M
      by (simp add: star_assoc)
    
    moreover have "ls1=ls2"
      apply (rule Cons.hyps[where ?F1.0="P a1 a * F1" and ?F2.0="P a2 a * F2"])
      using M
      by (simp only: star_aci)
    ultimately show ?case by simp
  qed
qed
lemma list_assn_pure[constraint_rules]: 
  assumes P: "is_pure P" 
  shows "is_pure (list_assn P)"
proof -
  from P obtain P' where P_eq: "\<And>x x'. P x x' = \<up>(P' x x')" 
    by (rule is_pureE) blast

  {
    fix l l'
    have "list_assn P l l' = \<up>(list_all2 P' l l')"
      by (induct P\<equiv>P l l' rule: list_assn.induct)
         (simp_all add: P_eq)
  } thus ?thesis by rule
qed

lemma four_list_assn_mono: 
  "\<lbrakk>\<And>x x' x'' x'''. P x x' x'' x'''\<Longrightarrow>\<^sub>AP' x x' x'' x'''\<rbrakk> \<Longrightarrow> four_list_assn P l l' l'' l''' \<Longrightarrow>\<^sub>A four_list_assn P' l l' l'' l'''"
  unfolding hn_ctxt_def
  apply (induct P l l' l'' l''' rule: four_list_assn.induct)
  by (auto intro: ent_star_mono)

lemma four_list_assn_monot: 
  "\<lbrakk>\<And>x x' x'' x'''. P x x' x'' x'''\<Longrightarrow>\<^sub>tP' x x' x'' x'''\<rbrakk> \<Longrightarrow> four_list_assn P l l' l'' l''' \<Longrightarrow>\<^sub>t four_list_assn P' l l' l'' l'''"
  unfolding hn_ctxt_def
  apply (induct P l l' l'' l''' rule: four_list_assn.induct)
  by (auto intro: entt_star_mono)

lemma list_match_cong[sepref_frame_match_rules]: 
  "\<lbrakk>\<And>x x'. \<lbrakk>x\<in>set l; x'\<in>set l'\<rbrakk> \<Longrightarrow> hn_ctxt A x x' \<Longrightarrow>\<^sub>t hn_ctxt A' x x' \<rbrakk> \<Longrightarrow> hn_ctxt (list_assn A) l l' \<Longrightarrow>\<^sub>t hn_ctxt (list_assn A') l l'"
  unfolding hn_ctxt_def
  by (induct A l l' rule: list_assn.induct) (simp_all add: entt_star_mono)

lemma list_merge_cong[sepref_frame_merge_rules]:
  assumes "\<And>x x'. \<lbrakk>x\<in>set l; x'\<in>set l'\<rbrakk> \<Longrightarrow> hn_ctxt A x x' \<or>\<^sub>A hn_ctxt A' x x' \<Longrightarrow>\<^sub>t hn_ctxt Am x x'"
  shows "hn_ctxt (list_assn A) l l' \<or>\<^sub>A hn_ctxt (list_assn A') l l' \<Longrightarrow>\<^sub>t hn_ctxt (list_assn Am) l l'"
  apply (blast intro: entt_disjE list_match_cong entt_disjD1[OF assms] entt_disjD2[OF assms])
  done
  
lemma invalid_list_split: 
  "invalid_assn (list_assn A) (x#xs) (y#ys) \<Longrightarrow>\<^sub>t invalid_assn A x y * invalid_assn (list_assn A) xs ys"
  by (fastforce simp: invalid_assn_def intro!: enttI simp: mod_star_conv)

lemma entt_invalid_list: "hn_invalid (list_assn A) l l' \<Longrightarrow>\<^sub>t hn_ctxt (list_assn (invalid_assn A)) l l'"
  apply (induct A l l' rule: list_assn.induct)
  applyS simp

  subgoal
    apply1 (simp add: hn_ctxt_def cong del: invalid_assn_cong)
    apply1 (rule entt_trans[OF invalid_list_split])
    apply (rule entt_star_mono)
      applyS simp

      apply (rule entt_trans)
        applyS assumption
        applyS simp
    done
    
  applyS (simp add: hn_ctxt_def invalid_assn_def) 
  applyS (simp add: hn_ctxt_def invalid_assn_def) 
  done

lemmas invalid_list_merge[sepref_frame_merge_rules] = gen_merge_cons[OF entt_invalid_list]


lemma list_assn_comp[fcomp_norm_unfold]: "hr_comp (list_assn A) (\<langle>B\<rangle>list_rel) = list_assn (hr_comp A B)"
proof (intro ext)  
  { fix x l y m
    have "hr_comp (list_assn A) (\<langle>B\<rangle>list_rel) (x # l) (y # m) = 
      hr_comp A B x y * hr_comp (list_assn A) (\<langle>B\<rangle>list_rel) l m"
      by (sep_auto 
        simp: hr_comp_def list_rel_split_left_iff
        intro!: ent_ex_preI ent_iffI) (* TODO: ent_ex_preI should be applied by default, before ent_ex_postI!*)
  } note aux = this

  fix l li
  show "hr_comp (list_assn A) (\<langle>B\<rangle>list_rel) l li = list_assn (hr_comp A B) l li"
    apply (induction l arbitrary: li; case_tac li; intro ent_iffI)
    apply (sep_auto simp: hr_comp_def; fail)+
    by (simp_all add: aux)
qed  

lemma hn_ctxt_eq: "A x y = z \<Longrightarrow> hn_ctxt A x y = z" by (simp add: hn_ctxt_def)

lemmas hn_ctxt_list = hn_ctxt_eq[of "list_assn A" for A]

lemma hn_case_list[sepref_prep_comb_rule, sepref_comb_rules]:
  fixes p p' P
  defines [simp]: "INVE \<equiv> hn_invalid (list_assn P) p p'"
  assumes FR: "\<Gamma> \<Longrightarrow>\<^sub>t hn_ctxt (list_assn P) p p' * F"
  assumes Rn: "p=[] \<Longrightarrow> hn_refine (hn_ctxt (list_assn P) p p' * F) f1' (hn_ctxt XX1 p p' * \<Gamma>1') R f1"
  assumes Rs: "\<And>x l x' l'. \<lbrakk> p=x#l; p'=x'#l' \<rbrakk> \<Longrightarrow> 
    hn_refine (hn_ctxt P x x' * hn_ctxt (list_assn P) l l' * INVE * F) (f2' x' l') (hn_ctxt P1' x x' * hn_ctxt (list_assn P2') l l' * hn_ctxt XX2 p p' * \<Gamma>2') R (f2 x l)"
  assumes MERGE1[unfolded hn_ctxt_def]: "\<And>x x'. hn_ctxt P1' x x' \<or>\<^sub>A hn_ctxt P2' x x' \<Longrightarrow>\<^sub>t hn_ctxt P' x x'"  
  assumes MERGE2: "\<Gamma>1' \<or>\<^sub>A \<Gamma>2' \<Longrightarrow>\<^sub>t \<Gamma>'"  
  shows "hn_refine \<Gamma> (case_list f1' f2' p') (hn_ctxt (list_assn P') p p' * \<Gamma>') R (case_list$f1$(\<lambda>\<^sub>2x l. f2 x l)$p)"
    apply (rule hn_refine_cons_pre[OF FR])
    apply1 extract_hnr_invalids
    apply (cases p; cases p'; simp add: list_assn.simps[THEN hn_ctxt_list])
    subgoal 
      apply (rule hn_refine_cons[OF _ Rn _ entt_refl]; assumption?)
      applyS (simp add: hn_ctxt_def)

      apply (subst mult.commute, rule entt_fr_drop)
      apply (rule entt_trans[OF _ MERGE2])
      apply (simp add: ent_disjI1' ent_disjI2')
    done  

    subgoal
      apply (rule hn_refine_cons[OF _ Rs _ entt_refl]; assumption?)
      applyS (simp add: hn_ctxt_def)
      apply (rule entt_star_mono)
      apply1 (rule entt_fr_drop)
      apply (rule entt_star_mono)

      apply1 (simp add: hn_ctxt_def)
      apply1 (rule entt_trans[OF _ MERGE1])
      applyS (simp)

      apply1 (simp add: hn_ctxt_def)
      apply (rule list_assn_monot)
      apply1 (rule entt_trans[OF _ MERGE1])
      applyS (simp)

      apply1 (rule entt_trans[OF _ MERGE2])
      applyS (simp)
    done
    done

lemma hn_Nil[sepref_fr_rules]: 
  "hn_refine emp (return []) emp (list_assn P) (RETURN$[])"
  unfolding hn_refine_def
  by sep_auto

lemma hn_Cons[sepref_fr_rules]: "hn_refine (hn_ctxt P x x' * hn_ctxt (list_assn P) xs xs') 
  (return (x'#xs')) (hn_invalid P x x' * hn_invalid (list_assn P) xs xs') (list_assn P)
  (RETURN$((#) $x$xs))"
  unfolding hn_refine_def
  apply (sep_auto simp: hn_ctxt_def)
  apply (rule ent_frame_fwd[OF invalidate_clone'[of P]], frame_inference)
  apply (rule ent_frame_fwd[OF invalidate_clone'[of "list_assn P"]], frame_inference)
  apply solve_entails
  done

lemma list_assn_aux_len: 
  "list_assn P l l' = list_assn P l l' * \<up>(length l = length l')"
  apply (induct P\<equiv>P l l' rule: list_assn.induct)
  apply simp_all
  subgoal for a as c cs
    by (erule_tac t="list_assn P as cs" in subst[OF sym]) simp
  done

lemma list_assn_aux_eqlen_simp: 
  "vassn_tag (list_assn P l l') \<Longrightarrow> length l' = length l"
  "h \<Turnstile> (list_assn P l l') \<Longrightarrow> length l' = length l"
  apply (subst (asm) list_assn_aux_len; auto simp: vassn_tag_def)+
  done

lemma hn_append[sepref_fr_rules]: "hn_refine (hn_ctxt (list_assn P) l1 l1' * hn_ctxt (list_assn P) l2 l2')
  (return (l1'@l2')) (hn_invalid (list_assn P) l1 l1' * hn_invalid (list_assn P) l2 l2') (list_assn P)
  (RETURN$((@) $l1$l2))"
  apply rule
  apply (sep_auto simp: hn_ctxt_def)
  apply (subst list_assn_aux_len)
  apply (sep_auto)
  apply (rule ent_frame_fwd[OF invalidate_clone'[of "list_assn P"]], frame_inference)
  apply (rule ent_frame_fwd[OF invalidate_clone'[of "list_assn P"]], frame_inference)
  apply solve_entails
  done

lemma list_assn_aux_cons_conv1:
  "list_assn R (a#l) m = (\<exists>\<^sub>Ab m'. R a b * list_assn R l m' * \<up>(m=b#m'))"
  apply (cases m)
  apply sep_auto
  apply (sep_auto intro!: ent_iffI)
  done
lemma list_assn_aux_cons_conv2:
  "list_assn R l (b#m) = (\<exists>\<^sub>Aa l'. R a b * list_assn R l' m * \<up>(l=a#l'))"
  apply (cases l)
  apply sep_auto
  apply (sep_auto intro!: ent_iffI)
  done
lemmas list_assn_aux_cons_conv = list_assn_aux_cons_conv1 list_assn_aux_cons_conv2

lemma list_assn_aux_append_conv1:
  "list_assn R (l1@l2) m = (\<exists>\<^sub>Am1 m2. list_assn R l1 m1 * list_assn R l2 m2 * \<up>(m=m1@m2))"
  apply (induction l1 arbitrary: m)
  apply (sep_auto intro!: ent_iffI)
  apply (sep_auto intro!: ent_iffI simp: list_assn_aux_cons_conv)
  done
lemma list_assn_aux_append_conv2:
  "list_assn R l (m1@m2) = (\<exists>\<^sub>Al1 l2. list_assn R l1 m1 * list_assn R l2 m2 * \<up>(l=l1@l2))"
  apply (induction m1 arbitrary: l)
  apply (sep_auto intro!: ent_iffI)
  apply (sep_auto intro!: ent_iffI simp: list_assn_aux_cons_conv)
  done
lemmas list_assn_aux_append_conv = list_assn_aux_append_conv1 list_assn_aux_append_conv2  

declare param_upt[sepref_import_param]
*)

end