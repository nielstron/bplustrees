theory Flatten_Iter
imports Basic_Assn
begin

locale imp_list_iterate = 
  constrains is_list :: "'a list \<Rightarrow> 'l \<Rightarrow> assn"
  fixes is_it :: "'a list \<Rightarrow> 'l \<Rightarrow> 'a list \<Rightarrow> 'it \<Rightarrow> assn"
  fixes it_init :: "'l \<Rightarrow> ('it) Heap"
  fixes it_has_next :: "'it \<Rightarrow> bool Heap"
  fixes it_next :: "'it \<Rightarrow> ('a\<times>'it) Heap"
  assumes it_init_rule[sep_heap_rules]: 
    "<is_list l p> it_init p <is_it l p l>\<^sub>t"
  assumes it_next_rule[sep_heap_rules]: "l'\<noteq>[] \<Longrightarrow> 
    <is_it l p l' it> 
      it_next it 
    <\<lambda>(a,it'). is_it l p (tl l') it' * \<up>(a=hd l')>"
  assumes it_has_next_rule[sep_heap_rules]: 
    "<is_it l p l' it> 
       it_has_next it 
     <\<lambda>r. is_it l p l' it * \<up>(r\<longleftrightarrow>l'\<noteq>[])>"
  assumes quit_iteration:
    "is_it l p l' it \<Longrightarrow>\<^sub>A is_list l p * true"

end