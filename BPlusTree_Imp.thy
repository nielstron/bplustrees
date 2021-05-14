theory BPlusTree_Imp
  imports
    BPlusTree
    Partially_Filled_Array
    Basic_Assn
begin

section "Imperative B-tree Definition"

text "The heap data type definition. Anything stored on the heap always contains data,
leafs are represented as None."

datatype 'a btnode =
  Btnode "('a btnode ref*'a) pfarray" "'a btnode ref" |
  Btleaf "'a pfarray" 

text \<open>Selector Functions\<close>
primrec kvs :: "'a::heap btnode \<Rightarrow> ('a btnode ref*'a) pfarray" where
  [sep_dflt_simps]: "kvs (Btnode ts _) = ts"

primrec last :: "'a::heap btnode \<Rightarrow> 'a btnode ref" where
  [sep_dflt_simps]: "last (Btnode _ t) = t"

primrec vals :: "'a::heap btnode \<Rightarrow> 'a pfarray" where
  [sep_dflt_simps]: "vals (Btleaf ts) = ts"

term arrays_update

text \<open>Encoding to natural numbers, as required by Imperative/HOL\<close>
  (* Note: should also work using the package "Deriving" *)
fun
  btnode_encode :: "'a::heap btnode \<Rightarrow> nat"
  where
    "btnode_encode (Btnode ts t) = to_nat (Some ts, Some t, None::('a) pfarray option)" |
    "btnode_encode (Btleaf ts) = to_nat (None::('a btnode ref*'a) pfarray option, None::'a btnode ref option, Some ts)"

instance btnode :: (heap) heap
  apply (rule heap_class.intro)
   apply (rule countable_classI [of "btnode_encode"])
  apply(elim btnode_encode.elims)
  apply auto
  ..

text "The refinement relationship to abstract B-trees."


fun btnode_assn :: "nat \<Rightarrow> 'a::heap bplustree \<Rightarrow> 'a btnode \<Rightarrow> assn" where
  "btnode_assn k (LNode xs) (Btleaf xsi) = 
 (\<exists>\<^sub>A xsi'.
      is_pfa (2*k) xsi' xsi
    * list_assn (id_assn) xs xsi'
  )" |
  "btnode_assn k (Node ts t) (Btnode tsi ti) = 
 (\<exists>\<^sub>A tsi'.
      bplustree_assn k t ti
    * is_pfa (2*k) tsi' tsi
    * list_assn ((bplustree_assn k) \<times>\<^sub>a id_assn) ts tsi'
    )" |
  "btnode_assn _ _ _ = false"

abbreviation "blist_assn k \<equiv> list_assn ((bplustree_assn k) \<times>\<^sub>a id_assn)"

end