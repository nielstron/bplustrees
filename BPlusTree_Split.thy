theory BPlusTree_Split
  imports BPlusTree_Set
begin

section "Abstract split functions"

subsection "Linear split"

text "Finally we show that the split axioms are feasible by providing an example split function"

text "Linear split is similar to well known functions, therefore a quick proof can be done."

fun linear_split where "linear_split xs x = (takeWhile (\<lambda>(_,s). s<x) xs, dropWhile (\<lambda>(_,s). s<x) xs)"
fun linear_split_list where "linear_split_list xs x = (takeWhile (\<lambda>s. s<x) xs, dropWhile (\<lambda>s. s<x) xs)"

global_interpretation bplustree_linear_search: split_full linear_split linear_split_list
  (* the below definitions are required to be set here for evaluating example code... *)
  defines bplustree_ls_isin = bplustree_linear_search.isin 
    and bplustree_ls_ins = bplustree_linear_search.ins
    and bplustree_ls_insert = bplustree_linear_search.insert
    and bplustree_ls_del = bplustree_linear_search.del
    and bplustree_ls_delete = bplustree_linear_search.delete
  apply unfold_locales
  unfolding linear_split.simps
    apply (auto split: list.splits)
  subgoal
    by (metis (no_types, lifting) case_prodD in_set_conv_decomp takeWhile_eq_all_conv takeWhile_idem)
  subgoal
    by (metis case_prod_conv hd_dropWhile le_less_linear list.sel(1) list.simps(3))
  subgoal
    by (metis Nil_is_append_conv last_in_set last_snoc list.simps(3) set_takeWhileD)
  subgoal
    by (metis hd_dropWhile le_less_linear list.sel(1) list.simps(3))
  done


text "Some examples follow to show that the implementation works
      and the above lemmas make sense. The examples are visualized in the thesis."



abbreviation "bplustree\<^sub>i \<equiv> bplustree_ls_insert"
abbreviation "bplustree\<^sub>d \<equiv> bplustree_ls_delete"

typedef uint32 = "{n::nat. n \<le> 100}" 
  by auto

setup_lifting type_definition_uint32

instantiation uint32 :: linorder
begin

lift_definition less_eq_uint32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> bool"
  is "(less_eq::nat \<Rightarrow> nat \<Rightarrow> bool)" .

lift_definition less_uint32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> bool"
  is "(less::nat \<Rightarrow> nat \<Rightarrow> bool)" .

instance
  by standard (transfer; auto)+
end

instantiation uint32 :: order_top
begin

lift_definition top_uint32 :: uint32 is "100::nat"
  by simp


instance 
  by standard (transfer; simp)
end


instantiation uint32 :: numeral
begin

lift_definition one_uint32 :: uint32 is "1::nat"
  by auto

lift_definition plus_uint32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32"
  is "\<lambda>a b. min (a + b) (100)"
  by simp

instance by standard (transfer; auto)
end


(* the below will take ages to evaluate

lemma [code]: "(2^32::nat) = 4294967296" 
  by simp

value "2^32::nat"
*)

value "let k=2::nat; x::uint32 bplustree = (Node [(Node [(LNode [1,2], 2),(LNode [3,4], 4),(LNode [5,6,7], 8)] (LNode [9,10]), 10)] (Node [(LNode [11,12,13,14], 14), (LNode [15,17], 20)] (LNode [21,22,23]))) in
      root_order k x"
value "let k=2::nat; x::uint32 bplustree = (Node [(Node [(LNode [1,2], 2),(LNode [3,4], 4),(LNode [5,6,7], 8)] (LNode [9,10]), 10)] (Node [(LNode [11,12,13,14], 14), (LNode [15,17], 20)] (LNode [21,22,23]))) in
      bal x"
value "let k=2::nat; x::uint32 bplustree = (Node [(Node [(LNode [1,2], 2),(LNode [3,4], 4),(LNode [5,6,7], 8)] (LNode [9,10]), 10)] (Node [(LNode [11,12,13,14], 14), (LNode [15,17], 20)] (LNode [50,55,56]))) in
      sorted_less (inorder x)"
value "let k=2::nat; x::uint32 bplustree = (Node [(Node [(LNode [1,2], 2),(LNode [3,4], 4),(LNode [5,6,7], 8)] (LNode [9,10]), 10)] (Node [(LNode [11,12,13,14], 14), (LNode [15,17], 20)] (LNode [50,55,56]))) in
      x"
value "let k=2::nat; x::uint32 bplustree = (Node [(Node [(LNode [1,2], 2),(LNode [3,4], 4),(LNode [5,6,7], 8)] (LNode [9,10]), 10)] (Node [(LNode [11,12,13,14], 14), (LNode [15,17], 20)] (LNode [50,55,56]))) in
      bplustree\<^sub>i k 9 x"
value "let k=2::nat; x::uint32 bplustree = (Node [(Node [(Leaf, 3),(Leaf, 5),(Leaf, 6)] Leaf, 10)] (Node [(Leaf, 14), (Leaf, 20)] Leaf)) in
      bplustree\<^sub>i k 1 (bplustree\<^sub>i k 9 x)"
value "let k=2::nat; x::uint32 bplustree = (Node [(Node [(Leaf, 3),(Leaf, 5),(Leaf, 6)] Leaf, 10)] (Node [(Leaf, 14), (Leaf, 20)] Leaf)) in
      bplustree\<^sub>d k 10 (bplustree\<^sub>i k 1 (bplustree\<^sub>i k 9 x))"
value "let k=2::nat; x::uint32 bplustree = (Node [(Node [(Leaf, 3),(Leaf, 5),(Leaf, 6)] Leaf, 10)] (Node [(Leaf, 14), (Leaf, 20)] Leaf)) in
      bplustree\<^sub>d k 3 (bplustree\<^sub>d k 10 (bplustree\<^sub>i k 1 (bplustree\<^sub>i k 9 x)))"


end
