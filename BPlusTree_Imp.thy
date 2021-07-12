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
  Btleaf "'a pfarray" "'a btnode ref option"


text \<open>Selector Functions\<close>
primrec kvs :: "'a::heap btnode \<Rightarrow> ('a btnode ref option * 'a) pfarray" where
  [sep_dflt_simps]: "kvs (Btnode ts _) = ts"

primrec last :: "'a::heap btnode \<Rightarrow> 'a btnode ref" where
  [sep_dflt_simps]: "last (Btnode _ t) = t"

primrec vals :: "'a::heap btnode \<Rightarrow> 'a pfarray" where
  [sep_dflt_simps]: "vals (Btleaf ts _) = ts"

primrec fwd :: "'a::heap btnode \<Rightarrow> 'a btnode ref option" where
  [sep_dflt_simps]: "fwd (Btleaf _ t) = t"

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

text "The idea is: a refines the given node of degree k where the first leaf node of the subtree
of a is r and the forward pointer in the last leaf node is z"

find_theorems list_assn
find_theorems id_assn

fun leaf_nodes where
"leaf_nodes (LNode xs) = [LNode xs]" |
"leaf_nodes (Node ts t) = concat (map leaf_nodes (subtrees ts)) @ leaf_nodes t"

locale bplustree =
  fixes A :: "'a \<Rightarrow> ('b::heap) \<Rightarrow> bool"
begin


definition "A_assn x y \<equiv> \<up>(A x y)"


fun bplustree_assn :: "nat \<Rightarrow> 'a bplustree \<Rightarrow> 'b btnode ref \<Rightarrow> 'b btnode ref option \<Rightarrow> 'b btnode ref option \<Rightarrow> assn" where
  "bplustree_assn k (LNode xs) a r z = 
 (\<exists>\<^sub>A xsi xsi' fwd.
      a \<mapsto>\<^sub>r Btleaf xsi fwd
    * is_pfa (2*k) xsi' xsi
    * list_assn A_assn xs xsi'
    * \<up>(fwd = z)
    * \<up>(the r = a)
  )" |
  "bplustree_assn k (Node ts t) a r z = 
 (\<exists>\<^sub>A tsi ti tsi' tsi'' rs.
      a \<mapsto>\<^sub>r Btnode tsi ti
    * bplustree_assn k t ti (List.last (r#rs)) (List.last (rs@[z]))
    * is_pfa (2*k) tsi' tsi
    * \<up>(length tsi' = length rs)
    * \<up>(tsi'' = zip (zip (map fst tsi') (zip (butlast (r#rs)) (butlast (rs@[z])))) (map snd tsi'))
    * list_assn ((\<lambda> t (ti,r',z'). bplustree_assn k t (the ti) r' z') \<times>\<^sub>a A_assn) ts tsi''
    )"

find_theorems "map _ (zip _ _)"
(*
rs = the list of pointers to the leaves of this subtree
TODO how to weave rs@[z] and a#rs into the list_assn most elegantly
*)

text "With the current definition of deletion, we would
also need to directly reason on nodes and not only on references
to them."

fun btnode_assn :: "nat \<Rightarrow> 'a bplustree \<Rightarrow> 'b btnode \<Rightarrow> 'b btnode ref option \<Rightarrow> 'b btnode ref option \<Rightarrow> assn" where
  "btnode_assn k (LNode xs) (Btleaf xsi zi) r z = 
 (\<exists>\<^sub>A xsi xsi' zi.
    is_pfa (2*k) xsi' xsi
    * list_assn A_assn xs xsi'
    * \<up>(zi = z)
  )" |
  "btnode_assn k (Node ts t) (Btnode tsi ti) r z = 
 (\<exists>\<^sub>A tsi' tsi'' rs.
    bplustree_assn k t ti (List.last (r#rs)) (List.last (rs@[z]))
    * is_pfa (2*k) tsi' tsi
    * \<up>(length tsi' = length rs)
    * \<up>(tsi'' = zip (zip (map fst tsi') (zip (butlast (r#rs)) (butlast (rs@[z])))) (map snd tsi'))
    * list_assn ((\<lambda> t (ti,r',z'). bplustree_assn k t (the ti) r' z') \<times>\<^sub>a A_assn) ts tsi''
    )" |
  "btnode_assn _ _ _ _ _ = false"

abbreviation "blist_assn k ts tsi'' \<equiv> list_assn ((\<lambda> t (ti,r',z'). bplustree_assn k t (the ti) r' z') \<times>\<^sub>a A_assn) ts tsi'' "

fun leaf_nodes_assn :: "nat \<Rightarrow> 'a bplustree list \<Rightarrow> 'b btnode ref option \<Rightarrow> 'b btnode ref option \<Rightarrow> assn" where
  "leaf_nodes_assn k ((LNode xs)#lns) r z = 
 (\<exists>\<^sub>A xsi xsi' fwd.
      the r \<mapsto>\<^sub>r Btleaf xsi fwd
    * is_pfa (2*k) xsi' xsi
    * list_assn A_assn xs xsi'
    * leaf_nodes_assn k lns fwd z
  )" | 
  "leaf_nodes_assn k [] r z = \<up>(z = r)" |
  "leaf_nodes_assn _ _ _ _ = false"


find_theorems "_ \<Longrightarrow>\<^sub>t _"
(* FIX blist_assn ... \<Longrightarrow> leaf_nodes_assn *)
lemma "bplustree_assn k t ti r z \<Longrightarrow>\<^sub>A leaf_nodes_assn k (leaf_nodes t) r z * true"
proof(induction rule: bplustree_assn.induct)
  case (1 k xs a r z)
  then show ?case
    by (sep_auto)
next
  case (2 k ts t a r z)
  show ?case
    apply(sep_auto simp del: List.last.simps butlast.simps)
  proof (goal_cases)
    case (1 a b ti tsi' rs)
    then show ?case
    proof (induct arbitrary: a b rule: list_induct2)
      case Nil
      then show ?case
        apply sep_auto
      apply(rule ent_true_drop(1))
      apply(rule fr_rot)
      apply(rule ent_true_drop(1))
        using 2(1)[of ti "[]"]
      apply simp
      done
    next
      case (Cons x xs y ys)
      then show ?case
      apply (sep_auto simp del: List.last.simps butlast.simps)
        apply (simp del: List.last.simps butlast.simps)
    qed
  qed
     apply (sep_auto)
  proof (goal_cases)
    case (1 a b ti)
    then show ?case
      using 2(1)[of ti "[]"]
      apply sep_auto
      apply(rule ent_true_drop(1))
      apply(rule fr_rot)
      apply(rule ent_true_drop(1))
      apply simp
      done
  next
    case (2 tsi ti tsi' rs)
    then show ?case sorry
  qed
qed
thm bplustree_assn.simps
end

end