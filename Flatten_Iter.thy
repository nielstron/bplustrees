theory Flatten_Iter
  imports
  Basic_Assn
  "Separation_Logic_Imperative_HOL.Imp_List_Spec"
  "HOL-Real_Asymp.Inst_Existentials"
begin

text "This locale takes an iterator that refines a list of elements that themselves
can be iterated and defines an iterator over the flattened list of lower level elements"

locale flatten_iter =
  inner_list: imp_list_iterate is_inner_list inner_is_it inner_it_init inner_it_has_next inner_it_next + 
  outer_list: imp_list_iterate is_outer_list outer_is_it outer_it_init outer_it_has_next outer_it_next 
  for is_outer_list :: "'l list \<Rightarrow> 'm \<Rightarrow> assn"
  and outer_is_it :: "'l list \<Rightarrow> 'm \<Rightarrow> 'l list \<Rightarrow> 'oit \<Rightarrow> assn"
  and outer_it_init :: "'m \<Rightarrow> ('oit) Heap"
  and outer_it_has_next :: "'oit \<Rightarrow> bool Heap"
  and outer_it_next :: "'oit \<Rightarrow> ('l\<times>'oit) Heap"
  and is_inner_list :: "'a list \<Rightarrow> 'l \<Rightarrow> assn"
  and inner_is_it :: "'a list \<Rightarrow> 'l \<Rightarrow> 'a list \<Rightarrow> 'iit \<Rightarrow> assn"
  and inner_it_init :: "'l \<Rightarrow> ('iit) Heap"
  and inner_it_has_next :: "'iit \<Rightarrow> bool Heap"
  and inner_it_next :: "'iit \<Rightarrow> ('a\<times>'iit) Heap"
begin

fun is_flatten_list :: "'a list \<Rightarrow> 'm \<Rightarrow> assn" where
  "is_flatten_list ls lsi = (\<exists>\<^sub>A lsi' ls'.
    is_outer_list lsi' lsi * list_assn is_inner_list ls' lsi' * \<up>(ls = concat ls')
)"

(*type_synonym flatten_it = "'iit \<times> 'oit"*)
fun is_flatten_it :: "'a list \<Rightarrow> 'm \<Rightarrow> 'a list \<Rightarrow> ('oit \<times> 'iit option) \<Rightarrow> assn"
  where 
"is_flatten_it ls lsi ls2 (oit, None) = 
        (\<exists>\<^sub>A lsi' ls2' ls1' lsi1 lsi2.
          list_assn is_inner_list ls1' lsi1 *
          list_assn is_inner_list ls2' lsi2 *
           \<up>(ls2 = concat ls2' \<and> ls = (concat (ls1'@ls2'))) *
          outer_is_it lsi' lsi lsi2 oit *
          \<up>(lsi'=lsi1@lsi2)
)" |
"is_flatten_it ls lsi ls2 (oit, Some iit) = 
        (\<exists>\<^sub>A lsi' ls2' ls1' lsi1 lsi2 lsim ls2m lsm ls1m.
          list_assn is_inner_list ls1' lsi1 *
          list_assn is_inner_list ls2' lsi2 *
           \<up>(ls2m \<noteq> [] \<and> ls2 = ls2m@(concat ls2') \<and> ls = (concat (ls1'@lsm#ls2'))) *
          outer_is_it lsi' lsi lsi2 oit *
          \<up>(lsm = ls1m@ls2m \<and> lsi'=(lsi1@lsim#lsi2)) *
          inner_is_it lsm lsim ls2m iit
)
"

partial_function (heap) flatten_it_adjust:: "'oit \<Rightarrow> 'iit \<Rightarrow> ('oit \<times> 'iit option) Heap" where
"flatten_it_adjust oit iit = do {
      ihasnext \<leftarrow> inner_it_has_next iit;
      if ihasnext then
        return (oit, Some iit)
      else do {
        ohasnext \<leftarrow> outer_it_has_next oit;
        if \<not>ohasnext then
          return (oit, None)
        else do {
          (next, oit) \<leftarrow> outer_it_next oit;
          nextit \<leftarrow> inner_it_init next;
          flatten_it_adjust oit nextit
        }
      }
  }
"

lemma flatten_it_adjust_rule: 
  "lsm = lsm1@lsm2 \<Longrightarrow> 
<list_assn is_inner_list ls1' ls1 * list_assn is_inner_list ls2' ls2 * outer_is_it (ls1@lsim#ls2) lsi ls2 oit * inner_is_it lsm lsim lsm2 iit>
  flatten_it_adjust oit iit
  <is_flatten_it (concat (ls1'@lsm#ls2')) lsi (concat (lsm2#ls2'))>\<^sub>t"
  apply(subst flatten_it_adjust.simps)
  apply (sep_auto eintros del: exI heap add: inner_list.it_has_next_rule)
  apply(inst_existentials "(ls1 @ lsim # ls2)" ls2' ls1' ls1 ls2 lsim lsm2 lsm)
  subgoal by auto
  subgoal by (sep_auto)
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
  apply (sep_auto eintros del: exI)
  apply(inst_existentials "(ls1 @ [lsim])" "[lsm]" ls1' ls1 "[lsim]")
  apply auto
  apply(case_tac ls2; case_tac ls2')
  apply (simp add: mult.left_assoc)+
  apply (sep_auto eintros del: exI heap add: inner_list.it_init_rule)

definition flatten_it_init :: "'m \<Rightarrow> _ Heap" 
  where "flatten_it_init l = do {
    oit \<leftarrow> outer_it_init l;
    ohasnext \<leftarrow> outer_it_has_next oit;
    if ohasnext then do {
       (next, oit) \<leftarrow> outer_it_next oit;
       nextit \<leftarrow> inner_it_init next;
       flatten_it_adjust oit nextit
    } else return (oit, None)
}"

lemma flatten_it_init_rule[sep_heap_rules]: 
    "<is_flatten_list l p> flatten_it_init p <is_flatten_it l p l>\<^sub>t"
  unfolding flatten_it_init_def
  apply simp
  find_theorems "<\<exists>\<^sub>A_._>_<_>"
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
  thm inner_list.it_init_rule
  apply (vcg heap add: inner_list.it_init_rule)

definition flatten_it_next where 
  "flatten_it_next \<equiv> \<lambda>(oit,iit). do {
    (x, iit) \<leftarrow> inner_it_next iit;
    (oit, iit) \<leftarrow> flatten_it_adjust oit iit;
    return (x, (oit,iit))
  }"

definition flatten_it_has_next where
  "flatten_it_has_next \<equiv> \<lambda>(oit, iit). do {
    return (iit \<noteq> None)
}"


end