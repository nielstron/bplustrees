theory BPlusTree_ImpSplitCE
  imports
    BPlusTree_ImpRange
    BPlusTree_ImpSet
begin


subsection "Obtaining executable code"

text "In order to obtain fully defined functions,
we need to plug our split function implementations
into the locales we introduced previously."

global_interpretation bplustree_imp_binary_split_list_lrange: imp_split_list_smeq bin'_split
  defines bplustree_lrange_list = bplustree_imp_binary_split_list_lrange.imp_lrange_list
  apply unfold_locales
  by(sep_auto heap add: bin'_split_rule)


global_interpretation bplustree_imp_binary_split_range: 
  imp_split_range linear_split bplustree_linear_search_list.lrange_split bin_split bplustree_lrange_list
  apply unfold_locales
  subgoal by (simp add: bplustree_linear_search_list.lrange_split_req)
  subgoal 
    apply(simp add: bplustree_lrange_list_def)
    apply(vcg heap: bplustree_imp_binary_split_list.imp_lrange_list_rule)
  done

find_theorems bplustree_lrange
find_theorems bplustree_lrange_list
find_theorems imp_split_range.concat_leafs_range
find_theorems bplustree_leafs_range

export_code bplustree_leafs_range bplustree_lrange checking OCaml SML Scala
export_code bplustree_lrange in OCaml module_name BPlusTree
export_code bplustree_lrange in SML module_name BPlusTree
export_code bplustree_lrange in Scala module_name BPlusTree

global_interpretation bplustree_imp_binary_split_list: imp_split_list_smeq bin'_split
  defines bplustree_isin_list = bplustree_imp_binary_split_list.imp_isin_list
    and bplustree_ins_list = bplustree_imp_binary_split_list.imp_ins_list
    and bplustree_del_list = bplustree_imp_binary_split_list.imp_del_list
  apply unfold_locales
  apply(sep_auto heap: bin'_split_rule)
  done

print_theorems



global_interpretation bplustree_imp_binary_split_set: 
  imp_split_set bplustree_ls_isin_list bplustree_ls_insert_list bplustree_ls_delete_list
  linear_split bin_split bplustree_isin_list bplustree_ins_list bplustree_del_list
  defines bplustree_isin = bplustree_imp_binary_split_set.isin
    and bplustree_ins = bplustree_imp_binary_split_set.ins
    and bplustree_insert = bplustree_imp_binary_split_set.insert
    (*and bplustree_del = bplustree_imp_binary_split.del
    and bplustree_delete = bplustree_imp_binary_split.delete*)
    and bplustree_empty = bplustree_imp_binary_split_set.empty
  apply unfold_locales
  subgoal
    apply(vcg heap: bplustree_imp_binary_split_list.imp_isin_list_rule)
    apply (simp add: bplustree_ls_isin_list_def)
    done
  subgoal
    apply(vcg heap: bplustree_imp_binary_split_list.imp_ins_list_rule)
    apply (simp add: bplustree_ls_insert_list_def)
    done
  subgoal
    apply(vcg heap: bplustree_imp_binary_split_list.imp_del_list_rule)
    apply (simp add: bplustree_ls_delete_list_def)
    done
  done

declare bplustree_imp_binary_split_set.ins.simps[code]
declare bplustree_imp_binary_split_set.isin.simps[code]

export_code bplustree_empty bplustree_isin bplustree_insert checking OCaml SML Scala
export_code bplustree_empty bplustree_isin bplustree_insert in OCaml module_name BPlusTree
export_code bplustree_empty bplustree_isin bplustree_insert in SML module_name BPlusTree
export_code bplustree_empty bplustree_isin bplustree_insert in Scala module_name BPlusTree



interpretation bplustree_imp_linear_split_tree: imp_split_tree_smeq lin_split
  apply unfold_locales
  apply(sep_auto heap: lin_split_rule)
  done


text "Obtaining actual code turns out to be slightly more difficult
  due to the use of locales. However, we successfully obtain
the B-tree insertion and membership query with binary search splitting."

(* interpretation bplustree_imp_binary_split_list: imp_split_list_smeq bin'_split
  apply unfold_locales
  apply(sep_auto heap: bin'_split_rule)
  done
*)

interpretation bplustree_imp_bin_split_tree: imp_split_tree_smeq bin_split
  apply unfold_locales
  apply(sep_auto heap: bin_split_rule)
  done


end