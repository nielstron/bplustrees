theory BPlusTree_ImpSplitCE
  imports
    BPlusTree_ImpRange
    BPlusTree_ImpSet
    BPlusTree_SplitCE
begin


subsection "Obtaining executable code"

text "In order to obtain fully defined functions,
we need to plug our split function implementations
into the locales we introduced previously."

text "Obtaining actual code turns out to be slightly more difficult
  due to the use of locales. However, we successfully obtain
the B-tree insertion and membership query with binary search splitting."



global_interpretation bplustree_imp_binary_split_list: imp_split_list_smeq bin'_split
  defines bplustree_isin_list = bplustree_imp_binary_split_list.imp_isin_list
    and bplustree_ins_list = bplustree_imp_binary_split_list.imp_ins_list
    and bplustree_del_list = bplustree_imp_binary_split_list.imp_del_list
    and bplustree_lrange_list = bplustree_imp_binary_split_list.imp_lrange_list
  apply unfold_locales
  apply(sep_auto heap: bin'_split_rule)
  done

print_theorems

global_interpretation bplustree_imp_binary_split: 
  imp_split_full_smeq bin_split bin'_split 
  defines bplustree_isin = bplustree_imp_binary_split.isin
    and bplustree_ins = bplustree_imp_binary_split.ins
    and bplustree_insert = bplustree_imp_binary_split.insert
    (*and bplustree_del = bplustree_imp_binary_split.del
    and bplustree_delete = bplustree_imp_binary_split.delete*)
    and bplustree_empty = bplustree_imp_binary_split.empty
    and bplustree_leafs_range = bplustree_imp_binary_split.leafs_range
    and bplustree_lrange = bplustree_imp_binary_split.concat_leafs_range
  apply unfold_locales
  apply(sep_auto heap: bin_split_rule)
  done

lemma [code]:
"bplustree_isin p x =
!p \<bind>
(\<lambda>node.
    case node of
    Btnode ts t \<Rightarrow>
      bin_split ts x \<bind>
      (\<lambda>i. pfa_length ts \<bind>
            (\<lambda>tsl. if i < tsl
                    then pfa_get ts i \<bind>
                         (\<lambda>s. let (sub, sep) = s in bplustree_isin (the sub) x)
                    else bplustree_isin t x))
    | Btleaf xs xa \<Rightarrow> bplustree_isin_list x xs)"
  unfolding bplustree_isin_list_def
  by (simp add: bplustree_imp_binary_split.isin.simps)
lemma [code]:
"bplustree_ins k x p =
!p \<bind>
(\<lambda>node.
    case node of
    Btnode tsi ti \<Rightarrow>
      bin_split tsi x \<bind>
      (\<lambda>i. pfa_length tsi \<bind>
            (\<lambda>tsl. if i < tsl
                    then pfa_get tsi i \<bind>
                         (\<lambda>s. let (sub, sep) = s
                               in bplustree_ins k x (the sub) \<bind>
                                  (\<lambda>r. case r of
                                        bplustree_imp_binary_split.T\<^sub>i lp \<Rightarrow>
                                          pfa_set tsi i (Some lp, sep) \<bind>
                                          (\<lambda>_. return (bplustree_imp_binary_split.T\<^sub>i p))
                                        | bplustree_imp_binary_split.Up\<^sub>i lp x' rp \<Rightarrow>
                                            pfa_set tsi i (Some rp, sep) \<bind>
                                            (\<lambda>_.
  pfa_insert_grow tsi i (Some lp, x') \<bind>
  (\<lambda>tsi'. p := Btnode tsi' ti \<bind> (\<lambda>_. bplustree_imp_binary_split.node\<^sub>i k p)))))
                    else bplustree_ins k x ti \<bind>
                         (\<lambda>r. case r of
                               bplustree_imp_binary_split.T\<^sub>i lp \<Rightarrow>
                                 p := Btnode tsi lp \<bind>
                                 (\<lambda>_. return (bplustree_imp_binary_split.T\<^sub>i p))
                               | bplustree_imp_binary_split.Up\<^sub>i lp x' rp \<Rightarrow>
                                   pfa_append_grow' tsi (Some lp, x') \<bind>
                                   (\<lambda>tsi'.
                                       p := Btnode tsi' rp \<bind>
                                       (\<lambda>_. bplustree_imp_binary_split.node\<^sub>i k p)))))
    | Btleaf ksi nxt \<Rightarrow>
         bplustree_ins_list x ksi \<bind>
        (\<lambda>ksi'. p := Btleaf ksi' nxt \<bind> (\<lambda>_. bplustree_imp_binary_split.Lnode\<^sub>i k p)))"
  unfolding bplustree_ins_list_def
  by (simp add: bplustree_imp_binary_split.ins.simps)

declare bplustree_imp_binary_split.leafs_range.simps[code]
lemma [code]:
"bplustree_lrange ti x =
    bplustree_leafs_range ti x \<bind>
    (\<lambda>lp. !the lp \<bind>
           (\<lambda>li. case li of
                  Btleaf xs nxt \<Rightarrow>
                    bplustree_lrange_list x xs \<bind>
                    (\<lambda>arr_it. leaf_elements_adjust (nxt, None) arr_it \<bind> return)))"
  unfolding bplustree_lrange_list_def
  by (simp add: bplustree_imp_binary_split.concat_leafs_range_def)

export_code bplustree_empty bplustree_isin bplustree_insert bplustree_lrange leaf_elements_iter_init leaf_elements_next leaf_elements_has_next checking OCaml SML Scala
export_code bplustree_empty bplustree_isin bplustree_insert bplustree_lrange leaf_elements_iter_init leaf_elements_next leaf_elements_has_next in OCaml module_name BPlusTree
export_code bplustree_empty bplustree_isin bplustree_insert bplustree_lrange leaf_elements_iter_init leaf_elements_next leaf_elements_has_next in SML module_name BPlusTree
export_code bplustree_empty bplustree_isin bplustree_insert bplustree_lrange leaf_elements_iter_init leaf_elements_next leaf_elements_has_next in Scala module_name BPlusTree



end