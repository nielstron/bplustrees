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
  "'a btnode ref \<Rightarrow> 'a \<Rightarrow> 'a btnode ref option Heap"
  where
    "lrange_iter_init p x = do {
  node \<leftarrow> !p;
  (case node of
     Btleaf xs z \<Rightarrow> do {
        return (Some p)
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
find_theorems leafs_assn
lemma lrange_iter_init_rule:
  assumes "k > 0" "root_order k t"
  shows "<bplustree_assn_leafs k t ti r z lptrs>
lrange_iter_init ti x
<\<lambda>p. (\<exists>\<^sub>A xs1 xs2 lptrs1 lptrs2 ps.
  inner_nodes_assn k t ti r z lptrs *
  leaf_nodes_assn k xs1 r p lptrs1 *
  list_assn leaf_node xs2 (map bplustree.vals xs2) *
  list_assn (is_pfa (2 * k)) (map bplustree.vals xs2) ps *
  leafs_assn ps lptrs2 p z *
  \<up>(concat (map bplustree.vals xs2) = abs_split_range.leafs_range t x) *
  \<up>(lptrs = lptrs1@lptrs2) *
  \<up>(leaf_nodes t = xs1@xs2)
)>\<^sub>t"
  find_theorems leaf_nodes_assn
(* this does not hold but maybe we can create something like
inner_nodes_assn * leafs_assn first_half * leafs_assn second_half * 
the second half concats to leafs_range

  (*leaf_nodes_assn k xs2 p z lptrs2 **)



leafs_assn xs * hd xs = ys * (take i ys)@(tl xs) = lrange t x
which will eventually translate to the leaf elements iter
but can be extended at the last position
*)
  sorry

end

end