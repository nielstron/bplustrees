theory While_Iter
  imports
  Basic_Assn
  "Separation_Logic_Imperative_HOL.Imp_List_Spec"
  "HOL-Real_Asymp.Inst_Existentials"
begin


text "This locale takes an iterator over elements and a predicate and returns
elements of the iterator until the predicate returns false."
find_theorems takeWhile

locale while_iter =
  list: imp_list_iterate is_list is_it it_init it_has_next it_next 
  for is_list :: "'a list \<Rightarrow> 'l \<Rightarrow> assn"
  and is_it :: "'a list \<Rightarrow> 'l \<Rightarrow> 'a list \<Rightarrow> 'iit \<Rightarrow> assn"
  and it_init :: "'l \<Rightarrow> ('iit) Heap"
  and it_has_next :: "'iit \<Rightarrow> bool Heap"
  and it_next :: "'iit \<Rightarrow> ('a\<times>'iit) Heap" +
  fixes P :: "'a \<Rightarrow> bool"
begin

fun is_while_list :: "'a list \<Rightarrow> 'l \<Rightarrow> assn" where
  "is_while_list ls lsi = (\<exists>\<^sub>Als'. is_list ls' lsi * \<up>(ls = takeWhile P ls'))"

lemma while_prec:
  "precise is_while_list"
  unfolding precise_def is_while_list.simps 
  using list.precise mod_and_dist preciseD' by fastforce

(*type_synonym while_it = "'a \<times> 'iit"*)
fun is_while_it :: "'a list \<Rightarrow> 'l \<Rightarrow> 'a list \<Rightarrow> ('a option \<times> 'iit) \<Rightarrow> assn"
  where 
"is_while_it ls lsi [] (None, iit) = 
        (\<exists>\<^sub>A ls'.
          is_it ls lsi ls' iit *
          \<up>([] = takeWhile P ls')
)" |
"is_while_it ls lsi (x#xs) (Some xi, iit) = 
        (\<exists>\<^sub>A ls'.
          is_it ls lsi ls' iit *
          \<up>(xs = takeWhile P ls') *
          \<up>(P x) *
          \<up>(x = xi)
)" |
"is_while_it _ _ _ _ = false"

definition while_it_init :: "'l \<Rightarrow> _ Heap" 
  where "while_it_init l = do {
    iit \<leftarrow> it_init l;
    ihasnext \<leftarrow> it_has_next iit;
    if ihasnext then do {
      inextp \<leftarrow> it_next iit;
      let (inext, iiit) = inextp in
      if P inext then
        return (Some inext, iiit)
      else
        return (None, iiit)
    }
    else return (None, iit)
}"

lemma flatten_it_init_rule[sep_heap_rules]: 
    "<is_while_list l p> while_it_init p <is_while_it l p l>\<^sub>t"
  unfolding while_it_init_def
  apply sep_auto
  apply simp
  apply(rule norm_pre_ex_rule)+
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  subgoal for lsi' ls' x xa
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply(case_tac lsi'; case_tac ls')
  apply simp+
  apply(rule impI)
  thm list.it_init_rule
  apply (vcg heap add: list.it_init_rule)
  subgoal for _ nxt oit a list aa lista xaa
  supply R = flatten_it_adjust_rule[of "[]" "[]" lista list a p oit "[]" aa xaa, simplified]
  thm R
  apply (sep_auto heap add: R)
  done
  done
  apply (sep_auto eintros del: exI)
  apply(inst_existentials "[]::'l list" "[]::'a list list" "[]::'a list list" "[]::'l list" "[]::'l list")
  apply simp_all
  done

definition flatten_it_next where 
  "flatten_it_next \<equiv> \<lambda>(oit,iit). do {
    (x, iit) \<leftarrow> it_next (the iit);
    (oit, iit) \<leftarrow> flatten_it_adjust oit iit;
    return (x, (oit,iit))
  }"

lemma flatten_it_next_rule:
    " l' \<noteq> [] \<Longrightarrow>
    <is_flatten_it l p l' it> 
      flatten_it_next it 
    <\<lambda>(a,it'). is_flatten_it l p (tl l') it' * \<up>(a=hd l')>\<^sub>t"
  apply(subst flatten_it_next_def)
  thm list.it_next_rule
  apply (vcg (ss))
  apply (vcg (ss))
  apply(case_tac iit; case_tac l')
  apply simp_all
  apply(rule norm_pre_ex_rule)+
  subgoal for oit iit a aa list lsi' ls2' ls1' lsi1 lsi2 lsim ls2m lsm ls1m
    apply(vcg (ss))
    apply(vcg (ss))
    apply(vcg (ss))
    apply(vcg (ss))
    apply(vcg (ss))
    apply(vcg (ss))
    apply(vcg (ss))
    apply(vcg (ss))
    apply(vcg (ss))
    apply(case_tac ls2m)
    apply simp_all
    subgoal for _ _ iita lista
  supply R = flatten_it_adjust_rule[of ls1' lsi1 ls2' lsi2 lsim p oit "ls1m@[aa]" "lista" iita, simplified]
  thm R
  apply (sep_auto heap add: R)
  done
  done
  done

definition flatten_it_has_next where
  "flatten_it_has_next \<equiv> \<lambda>(oit, iit). do {
    return (iit \<noteq> None)
}"

lemma flatten_it_has_next_rule[sep_heap_rules]: 
    "<is_flatten_it l p l' it> 
       flatten_it_has_next it 
     <\<lambda>r. is_flatten_it l p l' it * \<up>(r\<longleftrightarrow>l'\<noteq>[])>\<^sub>t"
  apply(subst flatten_it_has_next_def)
  apply(sep_auto)
  apply(case_tac iit, case_tac l')
  apply simp_all
  apply sep_auto
  done

declare mult.left_assoc[simp add]
lemma flatten_quit_iteration:
    "is_flatten_it l p l' it \<Longrightarrow>\<^sub>A is_flatten_list l p * true"
  apply(cases it)
  subgoal for oit iit
    apply(cases iit; cases l') 
  proof (goal_cases)
    case 1
    then show ?case
      apply (sep_auto eintros del: exI)
      subgoal for lsi' lsi''
        apply(inst_existentials lsi' lsi'')
        subgoal by auto
        subgoal by (metis (no_types, lifting) assn_aci(10) assn_times_comm fr_refl outer_list.quit_iteration)
        done
      done
  next
    case (2 lsim ll')
    then show ?case
      by (sep_auto eintros del: exI)
  next
    case (3 iit)
    then show ?case
      by (sep_auto eintros del: exI)
  next
  case (4 iit lsim ll')
    then show ?case
      apply (sep_auto eintros del: exI)
      subgoal for lsi' ls2' ls1' lsi1 lsi2 lsima ls2m lsm ls1m
        apply(inst_existentials "(lsi1 @ lsima # lsi2)" "ls1'@(ls1m@ls2m)#ls2'")
        subgoal by auto
            subgoal
              apply(rule impI; rule entails_preI)
              apply (auto dest!: mod_starD list_assn_len)
              apply(simp add:
                  mult.commute[where ?b="outer_is_it (lsi1 @ lsima # lsi2) p lsi2 oit"]
                  mult.commute[where ?b="is_outer_list (lsi1 @ lsima # lsi2) p"]
                  mult.left_assoc)
              apply(rule rem_true)
              supply R = ent_star_mono_true[of
                  "outer_is_it (lsi1 @ lsima # lsi2) p lsi2 oit"
                  "is_outer_list (lsi1 @ lsima # lsi2) p"
                  "list_assn is_list ls1' lsi1 *
                         list_assn is_list ls2' lsi2 *
                         is_it (ls1m @ ls2m) lsima ls2m iit"
                  " list_assn is_list ls1' lsi1 *
                         is_list (ls1m @ ls2m) lsima *
                         list_assn is_list ls2' lsi2"
              ,simplified]
              thm R
              apply(rule R)
              subgoal by (rule outer_list.quit_iteration)
              apply(simp add:
                  mult.commute[where ?b="is_it (ls1m @ ls2m) lsima ls2m iit"]
                  mult.commute[where ?b="is_list (ls1m @ ls2m) lsima"]
                  mult.left_assoc)
              apply(rule rem_true)
              supply R = ent_star_mono_true[of
                  "is_it (ls1m @ ls2m) lsima ls2m iit"
                  "is_list (ls1m @ ls2m) lsima"
                  "list_assn is_list ls1' lsi1 *
                         list_assn is_list ls2' lsi2"
                  " list_assn is_list ls1' lsi1 *
                         list_assn is_list ls2' lsi2"
              ,simplified]
              thm R
              apply(rule R)
              subgoal by (rule list.quit_iteration)
              subgoal by sep_auto
              done
            done
          done
      qed
  done
declare mult.left_assoc[simp del]

interpretation flatten_it: imp_list_iterate is_flatten_list is_flatten_it flatten_it_init flatten_it_has_next flatten_it_next
  apply(unfold_locales)
  subgoal 
    by (rule flatten_prec)
  subgoal for l p
    by (rule flatten_it_init_rule[of l p])
  subgoal for  l' l p it
    thm flatten_it_next_rule
    by (rule flatten_it_next_rule[of l' l p it])
  subgoal for l p l' it
    by (rule flatten_it_has_next_rule[of l p l' it])
  subgoal for l p l' it
    by (rule flatten_quit_iteration[of l p l' it])
  done
end

end