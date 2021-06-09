theory BPlusTree_Imp
  imports
    BPlusTree
    Partially_Filled_Array
    Basic_Assn
begin

section "Imperative B-tree Definition"

text "The heap data type definition. Anything stored on the heap always contains data,
leafs are represented as None."

(* Option as we need a default for non-initializeed entries *)
datatype 'a btnode =
  Btnode "('a btnode ref option *'a) pfarray" "'a btnode ref" |
  Btleaf "'a pfarray" "'a btnode ref option" (* the last pointer is a pointer to the next leaf *)


text \<open>Selector Functions\<close>
primrec kvs :: "'a::heap btnode \<Rightarrow> ('a btnode ref option * 'a) pfarray" where
  [sep_dflt_simps]: "kvs (Btnode ts _) = ts"

primrec last :: "'a::heap btnode \<Rightarrow> 'a btnode ref" where
  [sep_dflt_simps]: "last (Btnode _ t) = t"

primrec vals :: "'a::heap btnode \<Rightarrow> 'a pfarray" where
  [sep_dflt_simps]: "vals (Btleaf ts _) = ts"

primrec nxt :: "'a::heap btnode \<Rightarrow> 'a btnode ref option" where
  [sep_dflt_simps]: "nxt (Btleaf _ t) = t"

text \<open>Encoding to natural numbers, as required by Imperative/HOL\<close>
  (* Note: should also work using the package "Deriving" *)
fun
  btnode_encode :: "'a::heap btnode \<Rightarrow> nat"
  where
    "btnode_encode (Btnode ts t) = to_nat (Some ts, Some t, None::'a pfarray option, None::'a btnode ref option option)" |
    "btnode_encode (Btleaf ts t) = to_nat (None::('a btnode ref option * 'a) pfarray option, None::'a btnode ref option, Some ts, Some t)"

instance btnode :: (heap) heap
  apply (rule heap_class.intro)
   apply (rule countable_classI [of "btnode_encode"])
  apply(elim btnode_encode.elims)
  apply auto
  ..

text "The refinement relationship to abstract B-trees."
find_theorems fold foldr

fun fold_assn :: "('a \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'c list \<Rightarrow> 'd \<Rightarrow> assn" where
  "fold_assn P P' [] [] _ = emp"
| "fold_assn P P' (a#as) (c#cs) d = (P' a c d) * (fold_assn P P' as cs (P a c))"
| "fold_assn _ _ _ _ _ = false"

text "Naive approach"

fun bplustree_assn :: "nat \<Rightarrow> 'a::heap bplustree \<Rightarrow> 'a btnode ref \<Rightarrow> 'a bplustree option option \<Rightarrow> assn" where
  "bplustree_assn k (LNode xs) a t = 
 (\<exists>\<^sub>A xsi xsi' ti.
      a \<mapsto>\<^sub>r Btleaf xsi ti
    * is_pfa (2*k) xsi' xsi
    * list_assn (id_assn) xs xsi'
    * (case t of Some t \<Rightarrow> (case t of Some t \<Rightarrow> bplustree_assn k t (the ti) None | None \<Rightarrow> \<up>(ti = None)) | None \<Rightarrow> emp)
  )" |
  "bplustree_assn k (Node ts t) a tn = 
 (\<exists>\<^sub>A tsi ti tsi'.
      a \<mapsto>\<^sub>r Btnode tsi ti
    * is_pfa (2*k) tsi' tsi
    * fold_assn (\<lambda> (sub,_) _ . first_leaf sub) (\<lambda>(sub,sep) (subi,sepi) prevsub. bplustree_assn k sub (the subi) (Some (Some prevsub)) * (id_assn sep sepi)) (rev ts) (rev tsi') (first_leaf t)
    * bplustree_assn k t ti tn
    )"

text "Assuming we can generate a pointer from an abstract object"

fun first_leaf where
"first_leaf (LNode xs) = (LNode xs)" |
"first_leaf (Node ts t) = (case ts of ((sub,sep)#tts) \<Rightarrow> first_leaf sub | [] \<Rightarrow> t)"


fun bplustree_assn :: "nat \<Rightarrow> 'a::heap bplustree \<Rightarrow> 'a btnode ref \<Rightarrow> 'a bplustree option option \<Rightarrow> assn" where
  "bplustree_assn k (LNode xs) a t = 
 (\<exists>\<^sub>A xsi xsi' ti.
      a \<mapsto>\<^sub>r Btleaf xsi ti
    * is_pfa (2*k) xsi' xsi
    * list_assn (id_assn) xs xsi'
    * (case t of Some t \<Rightarrow> (case t of Some t \<Rightarrow> \<up>(ptrOf t = (the ti)) | None \<Rightarrow> \<up>(ti = None)) | None \<Rightarrow> emp)
  )" |
  "bplustree_assn k (Node ts t) a tn = 
 (\<exists>\<^sub>A tsi ti tsi'.
      a \<mapsto>\<^sub>r Btnode tsi ti
    * is_pfa (2*k) tsi' tsi
    * fold_assn (\<lambda> (sub,_) _ . first_leaf sub) (\<lambda>(sub,sep) (subi,sepi) prevsub. bplustree_assn k sub (the subi) (Some (Some prevsub)) * (id_assn sep sepi)) (rev ts) (rev tsi') (first_leaf t)
    * bplustree_assn k t ti tn
    )"

text "Assuming we may obtain the first leaf of a tree on the heap"

fun first_leafi where
"first_leafi a = (
  if (\<forall>h. h \<Turnstile> (\<exists>\<^sub>A xsi ti. a \<mapsto>\<^sub>r Btleaf xsi ti)) then
    a
  else \<dots>?
  )"


fun bplustree_assn :: "nat \<Rightarrow> 'a::heap bplustree \<Rightarrow> 'a btnode ref \<Rightarrow> 'a btnode ref option option \<Rightarrow> assn" where
  "bplustree_assn k (LNode xs) a nxti = 
 (\<exists>\<^sub>A xsi xsi' ti.
      a \<mapsto>\<^sub>r Btleaf xsi ti
    * is_pfa (2*k) xsi' xsi
    * list_assn (id_assn) xs xsi'
    * (case nxti of Some nxti \<Rightarrow> \<up>(ti = nxti) | None \<Rightarrow> emp)
  )" |
  "bplustree_assn k (Node ts t) a tn = 
 (\<exists>\<^sub>A tsi ti tsi'.
      a \<mapsto>\<^sub>r Btnode tsi ti
    * is_pfa (2*k) tsi' tsi
    * fold_assn (\<lambda> _ (subi,_) . first_leafi (the subi)) (\<lambda>(sub,sep) (subi,sepi) prevsub. bplustree_assn k sub (the subi) (Some (Some prevsub)) * (id_assn sep sepi)) (rev ts) (rev tsi') (first_leafi ti)
    * bplustree_assn k t ti tn
    )"

end