theory BPlusTree_SplitSpec
imports BPlusTree
begin

subsection "Auxiliary functions"

(* a version of split half that assures the left side to be non-empty *)
fun split_half:: "_ list \<Rightarrow> _ list \<times> _ list" where
  "split_half xs = (take ((length xs + 1) div 2) xs, drop ((length xs + 1) div 2) xs)"

lemma split_half_conc: "split_half xs = (ls, rs) = (xs = ls@rs \<and> length ls = (length xs + 1) div 2)"
  by force

lemma drop_not_empty: "xs \<noteq> [] \<Longrightarrow> drop (length xs div 2) xs \<noteq> []"
  apply(induction xs)
   apply(auto split!: list.splits)
  done

lemma take_not_empty: "xs \<noteq> [] \<Longrightarrow> take ((length xs + 1) div 2) xs \<noteq> []"
  apply(induction xs)
   apply(auto split!: list.splits)
  done

lemma split_half_not_empty: "length xs \<ge> 1 \<Longrightarrow> \<exists>ls a rs. split_half xs = (ls@[a],rs)"
  using take_not_empty
  by (metis (no_types, hide_lams) Ex_list_of_length One_nat_def le_trans length_Cons list.size(4) nat_1_add_1 not_one_le_zero rev_exhaust split_half.simps take0 take_all_iff)

subsection "The split function locale"

text "Here, we abstract away the inner workings of the split function
      for B-tree operations."

locale split_tree =
  fixes split ::  "('a bplustree\<times>'a::{linorder,order_top}) list \<Rightarrow> 'a \<Rightarrow> (('a bplustree\<times>'a) list \<times> ('a bplustree\<times>'a) list)"
  assumes split_req:
    "\<lbrakk>split xs p = (ls,rs)\<rbrakk> \<Longrightarrow> xs = ls @ rs"
    "\<lbrakk>split xs p = (ls@[(sub,sep)],rs); sorted_less (separators xs)\<rbrakk> \<Longrightarrow> sep < p"
    "\<lbrakk>split xs p = (ls,(sub,sep)#rs); sorted_less (separators xs)\<rbrakk> \<Longrightarrow> p \<le> sep"
begin
  lemmas split_conc = split_req(1)
  lemmas split_sorted = split_req(2,3)
  
  
  lemma [termination_simp]:"(ls, (sub, sep) # rs) = split ts y \<Longrightarrow>
        size sub < Suc (size_list (\<lambda>x. Suc (size (fst x))) ts  + size l)"
    using split_conc[of ts y ls "(sub,sep)#rs"] by auto
end

end