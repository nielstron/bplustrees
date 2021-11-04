theory BPlusTree_ImpRange
imports
  BPlusTree_Range
  BPlusTree_Iter
begin

(* Adding an actual range iterator based on the normal iterator
is trivial (just forward until we reach the first element \<ge> and stop
as soon as we have an element <)
We now try to implement a search for the first element of the range efficiently
 *)
subsection "The imperative split locale"

locale imp_split_range = abs_split_range: split_range split lrange_list
  for split::
    "('a::{heap,default,linorder,order_top} bplustree \<times> 'a) list \<Rightarrow> 'a
       \<Rightarrow> ('a bplustree \<times> 'a) list \<times> ('a bplustree \<times> 'a) list" 
    and lrange_list ::  "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) list \<Rightarrow> 'a list" +
  fixes imp_split:: "('a btnode ref option \<times> 'a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a \<Rightarrow> nat Heap"
  assumes imp_split_rule [sep_heap_rules]:"sorted_less (separators ts) \<Longrightarrow>
  length tsi = length rs \<Longrightarrow>
  tsi'' = zip (zip (map fst tsi) (zip (butlast (r#rs)) (butlast (rs@[z])))) (map snd tsi) \<Longrightarrow>
 <is_pfa c tsi (a,n) 
  * blist_assn k ts tsi'' > 
    imp_split (a,n) p 
  <\<lambda>i. 
    is_pfa c tsi (a,n)
    * blist_assn k ts tsi''
    * \<up>(split_relation ts (split ts p) i)>\<^sub>t"

locale imp_split2 = abs_split_range: split_range split lrange_list + imp_split_range split lrange_list imp_split
  for split::
    "('a bplustree \<times> 'a::{heap,default,linorder,order_top}) list \<Rightarrow> 'a
       \<Rightarrow> ('a bplustree \<times> 'a) list \<times> ('a bplustree \<times> 'a) list" 
    and lrange_list ::  "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) list \<Rightarrow> 'a list"
    and imp_split :: "('a btnode ref option \<times> 'a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a \<Rightarrow> nat Heap" +
  fixes imp_lrange_list:: "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a pfa_it Heap"
  assumes lrange_list_rule [sep_heap_rules]:"sorted_less ks \<Longrightarrow>
   <is_pfa c ks (a',n')> 
    imp_lrange_list x (a',n') 
  <pfa_is_it c ks (a',n') (lrange_list x ks)>\<^sub>t"
begin

partial_function (heap) lrange_iter_init ::
  "'a btnode ref \<Rightarrow> 'a \<Rightarrow> (('a btnode ref option \<times> 'a btnode ref option) \<times> 'a pfa_it option) Heap"
  where
    "lrange_iter_init p x = do {
  node \<leftarrow> !p;
  (case node of
     Btleaf xs _ \<Rightarrow> do {
        local_iter \<leftarrow> imp_lrange_list x xs;
        return (((Some p,None),Some local_iter))
      }
       |
     Btnode ts t \<Rightarrow> do {
       i \<leftarrow> imp_split ts x;
       tsl \<leftarrow> pfa_length ts;
       if i < tsl then do {
         s \<leftarrow> pfa_get ts i;
         let (sub,sep) = s in
           lrange_iter_init (the sub) x
       } else
           lrange_iter_init t x
    }
)}"

(*TODO prove correct *)
(* might need a modularization, where a z is inserted somewhere *)
lemma lrange_iter_init_rule:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn k t ti r None>
lrange_iter_init ti x
<\<lambda>it. leaf_elements_iter k t ti r (abs_split_range.lrange t x) it>\<^sub>t"
  sorry

end

end