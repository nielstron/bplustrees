theory BPlusTree                 
  imports Main "HOL-Data_Structures.Sorted_Less" "HOL-Data_Structures.Cmp" "HOL-Library.Multiset"
begin

(* some setup to cover up the redefinition of sorted in Sorted_Less
   but keep the lemmas *)
hide_const (open) Sorted_Less.sorted
abbreviation "sorted_less \<equiv> Sorted_Less.sorted"

section "Definition of the B-Plus-Tree"

subsection "Datatype definition"

text "B-Plus-Trees are basically B-Trees, that don't have empty Leafs but Leafs that contain
the relevant data. "


datatype 'a bplustree = LNode "'a list" | Node "('a bplustree * 'a) list" "'a bplustree"

type_synonym 'a bplustree_list =  "('a bplustree * 'a) list"
type_synonym 'a bplustree_pair =  "('a bplustree * 'a)"

abbreviation subtrees where "subtrees xs \<equiv> (map fst xs)"
abbreviation separators where "separators xs \<equiv> (map snd xs)"

subsection "Inorder and Set"

text "The set of B-Plus-tree needs to be manually defined, regarding only the leaves.
This overrides the default instantiation."

fun set_nodes :: "'a bplustree \<Rightarrow> 'a set" where
  "set_nodes (LNode ks) = {}" |
  "set_nodes (Node ts t) = \<Union>(set (map set_nodes (subtrees ts))) \<union> (set (separators ts)) \<union> set_nodes t"

fun set_leaves :: "'a bplustree \<Rightarrow> 'a set" where
  "set_leaves (LNode ks) = set ks" |
  "set_leaves (Node ts t) = \<Union>(set (map set_leaves (subtrees ts))) \<union> set_leaves t"

text "The inorder is a view of only internal seperators"

fun inorder :: "'a bplustree \<Rightarrow> 'a list" where
  "inorder (LNode ks) = []" |
  "inorder (Node ts t) = concat (map (\<lambda> (sub, sep). inorder sub @ [sep]) ts) @ inorder t"

abbreviation "inorder_list ts \<equiv> concat (map (\<lambda> (sub, sep). inorder sub @ [sep]) ts)"

text "The leaves view considers only its leafs."

fun leaves :: "'a bplustree \<Rightarrow> 'a list" where
  "leaves (LNode ks) = ks" |
  "leaves (Node ts t) = concat (map leaves (subtrees ts)) @ leaves t"

abbreviation "leaves_list ts \<equiv> concat (map leaves (subtrees ts))"

(* this abbreviation makes handling the list much nicer *)
thm leaves.simps
thm inorder.simps

value "leaves (Node [(LNode [], (0::nat)), (Node [(LNode [], 1), (LNode [], 10)] (LNode []), 12), ((LNode []), 30), ((LNode []), 100)] (LNode []))"

subsection "Height and Balancedness"

class height =
  fixes height :: "'a \<Rightarrow> nat"

instantiation bplustree :: (type) height
begin

fun height_bplustree :: "'a bplustree \<Rightarrow> nat" where
  "height (LNode ks) = 0" |
  "height (Node ts t) = Suc (Max (height ` (set (subtrees ts@[t]))))"

instance ..

end

text "Balancedness is defined is close accordance to the definition by Ernst"

fun bal:: "'a bplustree \<Rightarrow> bool" where
  "bal (LNode ks) = True" |
  "bal (Node ts t) = (
    (\<forall>sub \<in> set (subtrees ts). height sub = height t) \<and>
    (\<forall>sub \<in> set (subtrees ts). bal sub) \<and> bal t
  )"


value "height (Node [(LNode [], (0::nat)), (Node [(LNode [], 1), (LNode [], 10)] (LNode []), 12), ((LNode []), 30), ((LNode []), 100)] (LNode []))"
value "bal (Node [(LNode [], (0::nat)), (Node [(LNode [], 1), (LNode [], 10)] (LNode []), 12), ((LNode []), 30), ((LNode []), 100)] (LNode []))"


subsection "Order"

text "The order of a B-tree is defined just as in the original paper by Bayer."

(* alt1: following knuths definition to allow for any
   natural number as order and resolve ambiguity *)
(* alt2: use range [k,2*k] allowing for valid bplustrees
   from k=1 onwards NOTE this is what I ended up implementing *)

fun order:: "nat \<Rightarrow> 'a bplustree \<Rightarrow> bool" where
  "order k (LNode ks) = ((length ks \<ge> k)  \<and> (length ks \<le> 2*k))" |
  "order k (Node ts t) = (
  (length ts \<ge> k)  \<and>
  (length ts \<le> 2*k) \<and>
  (\<forall>sub \<in> set (subtrees ts). order k sub) \<and> order k t
)"

text \<open>The special condition for the root is called \textit{root\_order}\<close>

(* the invariant for the root of the bplustree *)
fun root_order:: "nat \<Rightarrow> 'a bplustree \<Rightarrow> bool" where
  "root_order k (LNode ks) = (length ks \<le> 2*k)" |
  "root_order k (Node ts t) = (
  (length ts > 0) \<and>
  (length ts \<le> 2*k) \<and>
  (\<forall>s \<in> set (subtrees ts). order k s) \<and> order k t
)"


subsection "Auxiliary Lemmas"

(* auxiliary lemmas when handling sets *)
lemma separators_split:
  "set (separators (l@(a,b)#r)) = set (separators l) \<union> set (separators r) \<union> {b}"
  by simp

lemma subtrees_split:
  "set (subtrees (l@(a,b)#r)) = set (subtrees l) \<union> set (subtrees r) \<union> {a}"
  by simp

(* height and set lemmas *)


lemma finite_set_ins_swap:
  assumes "finite A"
  shows "max a (Max (Set.insert b A)) = max b (Max (Set.insert a A))"
  using Max_insert assms max.commute max.left_commute by fastforce

lemma finite_set_in_idem:
  assumes "finite A"
  shows "max a (Max (Set.insert a A)) = Max (Set.insert a A)"
  using Max_insert assms max.commute max.left_commute by fastforce

lemma height_Leaf: "height t = 0 \<longleftrightarrow> (\<exists>ks. t = (LNode ks))"
  by (induction t) (auto)

lemma height_bplustree_order:
  "height (Node (ls@[a]) t) = height (Node (a#ls) t)"
  by simp

lemma height_bplustree_sub: 
  "height (Node ((sub,x)#ls) t) = max (height (Node ls t)) (Suc (height sub))"
  by simp

lemma height_bplustree_last: 
  "height (Node ((sub,x)#ts) t) = max (height (Node ts sub)) (Suc (height t))"
  by (induction ts) auto


lemma set_leaves_leaves: "set (leaves t) = set_leaves t"
  apply(induction t)
   apply(auto)
  done

lemma set_nodes_nodes: "set (inorder t) = set_nodes t"
  apply(induction t)
   apply(auto simp add: rev_image_eqI)
  done


lemma child_subset_leaves: "p \<in> set t \<Longrightarrow> set_leaves (fst p) \<subseteq> set_leaves (Node t n)"
  apply(induction p arbitrary: t n)
  apply(auto)
  done

lemma child_subset: "p \<in> set t \<Longrightarrow> set_nodes (fst p) \<subseteq> set_nodes (Node t n)"
  apply(induction p arbitrary: t n)
  apply(auto)
  done

lemma some_child_sub: 
  assumes "(sub,sep) \<in> set t"
  shows "sub \<in> set (subtrees t)"
    and "sep \<in> set (separators t)"
  using assms by force+ 

(* balancedness lemmas *)


lemma bal_all_subtrees_equal: "bal (Node ts t) \<Longrightarrow> (\<forall>s1 \<in> set (subtrees ts). \<forall>s2 \<in> set (subtrees ts). height s1 = height s2)"
  by (metis BPlusTree.bal.simps(2))


lemma fold_max_set: "\<forall>x \<in> set t. x = f \<Longrightarrow> fold max t f = f"
  apply(induction t)
   apply(auto simp add: max_def_raw)
  done

lemma height_bal_tree: "bal (Node ts t) \<Longrightarrow> height (Node ts t) = Suc (height t)"
  by (induction ts) auto



lemma bal_split_last: 
  assumes "bal (Node (ls@(sub,sep)#rs) t)"
  shows "bal (Node (ls@rs) t)"
    and "height (Node (ls@(sub,sep)#rs) t) = height (Node (ls@rs) t)"
  using assms by auto


lemma bal_split_right: 
  assumes "bal (Node (ls@rs) t)"
  shows "bal (Node rs t)"
    and "height (Node rs t) = height (Node (ls@rs) t)"
  using assms by (auto simp add: image_constant_conv)

lemma bal_split_left:
  assumes "bal (Node (ls@(a,b)#rs) t)"
  shows "bal (Node ls a)"
    and "height (Node ls a) = height (Node (ls@(a,b)#rs) t)"
  using assms by (auto simp add: image_constant_conv)


lemma bal_substitute: "\<lbrakk>bal (Node (ls@(a,b)#rs) t); height t = height c; bal c\<rbrakk> \<Longrightarrow> bal (Node (ls@(c,b)#rs) t)"
  unfolding bal.simps
  by auto

lemma bal_substitute_subplustree: "\<lbrakk>bal (Node (ls@(a,b)#rs) t); height a = height c; bal c\<rbrakk> \<Longrightarrow> bal (Node (ls@(c,b)#rs) t)"
  using bal_substitute
  by auto

lemma bal_substitute_separator: "bal (Node (ls@(a,b)#rs) t) \<Longrightarrow> bal (Node (ls@(a,c)#rs) t)"
  unfolding bal.simps
  by auto

(* order lemmas *)

lemma order_impl_root_order: "\<lbrakk>k > 0; order k t\<rbrakk> \<Longrightarrow> root_order k t"
  apply(cases t)
   apply(auto)
  done


(* sorted leaves implies that some sublists are sorted. This can be followed directly *)

lemma sorted_inorder_list_separators: "sorted_less (inorder_list ts) \<Longrightarrow> sorted_less (separators ts)"
  apply(induction ts)
   apply (auto simp add: sorted_lems)
  done

corollary sorted_inorder_separators: "sorted_less (inorder (Node ts t)) \<Longrightarrow> sorted_less (separators ts)"
  using sorted_inorder_list_separators sorted_wrt_append
  by auto


lemma sorted_inorder_list_subtrees:
  "sorted_less (inorder_list ts) \<Longrightarrow> \<forall> sub \<in> set (subtrees ts). sorted_less (inorder sub)"
  apply(induction ts)
   apply (auto simp add: sorted_lems)+
  done

corollary sorted_inorder_subtrees: "sorted_less (inorder (Node ts t)) \<Longrightarrow> \<forall> sub \<in> set (subtrees ts). sorted_less (inorder sub)"
  using sorted_inorder_list_subtrees sorted_wrt_append by auto

lemma sorted_inorder_list_induct_subplustree:
  "sorted_less (inorder_list (ls@(sub,sep)#rs)) \<Longrightarrow> sorted_less (inorder sub)"
  by (simp add: sorted_wrt_append)

corollary sorted_inorder_induct_subplustree:
  "sorted_less (inorder (Node (ls@(sub,sep)#rs) t)) \<Longrightarrow> sorted_less (inorder sub)"
  by (simp add: sorted_wrt_append)

lemma sorted_inorder_induct_last: "sorted_less (inorder (Node ts t)) \<Longrightarrow> sorted_less (inorder t)"
  by (simp add: sorted_wrt_append)

text "Additional lemmas on the sortedness of the whole tree, which is
correct alignment of navigation structure and leave data"

fun inbetween where
"inbetween f l Nil t u = f l t u" |
"inbetween f l ((sub,sep)#xs) t u = (f l sub sep \<and> inbetween f sep xs t u)"

thm fold_cong

lemma cong_inbetween[fundef_cong]: "
\<lbrakk>a = b; xs = ys; \<And>l' u' sub sep. (sub,sep) \<in> set ys \<Longrightarrow> f l' sub u' = g l' sub u'; \<And>l' u'. f l' a u' = g l' b u'\<rbrakk>
  \<Longrightarrow> inbetween f l xs a u = inbetween g l ys b u"
  apply(induction ys arbitrary: l a b u xs)
  apply auto
  apply fastforce+
  done

fun aligned where 
"aligned l (LNode ks) u = (\<forall>x \<in> set ks. l < x \<and> x \<le> u)" |
"aligned l (Node ts t) u = (inbetween aligned l ts t u)"

definition aligned_tree where "aligned_tree t = aligned bot t top"

thm aligned.simps

lemma "aligned l t u \<Longrightarrow> \<forall>x \<in> set (leaves t). l < x \<and> x \<le> u"
oops

lemma "aligned l (Node (ls@(sub', subl)#(sub,subsep)#rs) t) u \<Longrightarrow> aligned subl subsub subsep \<Longrightarrow>
aligned l (Node (ls@(sub',subl)#(subsub,subsep)#rs) t) u" 
  apply (induction ls arbitrary: l)
  apply auto
  done

end