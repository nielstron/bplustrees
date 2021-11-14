theory BPlusTree_ImpSplitSpec
imports BPlusTree_Imp BPlusTree_SplitSpec
begin

definition "split_relation xs \<equiv>
   \<lambda>(as,bs) i. i \<le> length xs \<and> as = take i xs \<and> bs = drop i xs"

lemma split_relation_alt: 
  "split_relation as (ls,rs) i = (as = ls@rs \<and> i = length ls)"
  by (auto simp add: split_relation_def)


lemma split_relation_length: "split_relation xs (ls,rs) (length xs) = (ls = xs \<and> rs = [])"
  by (simp add: split_relation_def)

(* auxiliary lemmas on assns *)
(* simp? not sure if it always makes things more easy *)
lemma list_assn_prod_map: "list_assn (A \<times>\<^sub>a B) xs ys = list_assn B (map snd xs) (map snd ys) * list_assn A (map fst xs) (map fst ys)"
  apply(induct "(A \<times>\<^sub>a B)" xs ys rule: list_assn.induct)
     apply(auto simp add: ab_semigroup_mult_class.mult.left_commute ent_star_mono star_aci(2) star_assoc)
  done

(* concrete *)
lemma id_assn_list: "h \<Turnstile> list_assn id_assn (xs::'a list) ys \<Longrightarrow> xs = ys"
  apply(induction "id_assn::('a \<Rightarrow> 'a \<Rightarrow> assn)" xs ys rule: list_assn.induct)
     apply(auto simp add: less_Suc_eq_0_disj pure_def)
  done

lemma id_assn_list_alt: "list_assn id_assn (xs::'a list) ys = \<up>(xs = ys)"
  apply(induction "id_assn::('a \<Rightarrow> 'a \<Rightarrow> assn)" xs ys rule: list_assn.induct)
     apply(auto simp add: less_Suc_eq_0_disj pure_def)
  done


lemma snd_map_help:
  "x \<le> length tsi \<Longrightarrow>
       (\<forall>j<x. snd (tsi ! j) = ((map snd tsi)!j))"
  "x < length tsi \<Longrightarrow> snd (tsi!x) = ((map snd tsi)!x)"
  by auto


lemma split_ismeq: "((a::nat) \<le> b \<and> X) = ((a < b \<and> X) \<or> (a = b \<and> X))"
  by auto

lemma split_relation_map: "split_relation as (ls,rs) i \<Longrightarrow> split_relation (map f as) (map f ls, map f rs) i"
  apply(induction as arbitrary: ls rs i)
   apply(auto simp add: split_relation_def take_map drop_Cons')
  apply(metis list.simps(9) take_map)
  done

lemma split_relation_access: "\<lbrakk>split_relation as (ls,rs) i; rs = r#rrs\<rbrakk> \<Longrightarrow> as!i = r"
  by (simp add: split_relation_alt)



lemma index_to_elem_all: "(\<forall>j<length xs. P (xs!j)) = (\<forall>x \<in> set xs. P x)"
  by (simp add: all_set_conv_nth)

lemma index_to_elem: "n < length xs \<Longrightarrow> (\<forall>j<n. P (xs!j)) = (\<forall>x \<in> set (take n xs). P x)"
  by (simp add: all_set_conv_nth)
    (* ----------------- *)

definition split_half :: "'a::heap pfarray \<Rightarrow> nat Heap"
  where
    "split_half a \<equiv> do {
  l \<leftarrow> pfa_length a;
  return ((l + 1) div 2)
}"

lemma split_half_rule[sep_heap_rules]: "<
    is_pfa c tsi a>
    split_half a
  <\<lambda>i. 
      is_pfa c tsi a
    * \<up>(i = (length tsi + 1) div 2 \<and>  split_relation tsi (BPlusTree_SplitSpec.split_half tsi) i)>"
  unfolding split_half_def split_relation_def
  apply(rule hoare_triple_preI)
  apply(sep_auto dest!: list_assn_len mod_starD)
  done


subsection "The imperative split locale"

locale imp_split_tree = abs_split_tree: BPlusTree_SplitSpec.split_tree split
  for split::
    "('a::{heap,default,linorder,order_top} bplustree \<times> 'a) list \<Rightarrow> 'a
       \<Rightarrow> ('a bplustree \<times> 'a) list \<times> ('a bplustree \<times> 'a) list" +
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



end