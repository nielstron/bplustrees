theory BPlusTree_ImpSet
  imports
    BPlusTree_Imp
    BPlusTree_Set
    BPlusTree_Iter
    "HOL-Real_Asymp.Inst_Existentials"
begin

section "Imperative Set operations"

subsection "Auxiliary operations"

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
    * \<up>(i = (length tsi + 1) div 2 \<and>  split_relation tsi (BPlusTree_Set.split_half tsi) i)>"
  unfolding split_half_def split_relation_def
  apply(rule hoare_triple_preI)
  apply(sep_auto dest!: list_assn_len mod_starD)
  done


subsection "The imperative split locale"

locale imp_split_tree = abs_split_tree: BPlusTree_Set.split_tree split
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

text "This locale extends the abstract split locale,
assuming that we are provided with an imperative program
that refines the abstract split function."


(* TODO separate into split_tree and split + split_list  *)
locale imp_split = abs_split: BPlusTree_Set.split split + imp_split_tree split imp_split
  for split::
    "('a bplustree \<times> 'a::{heap,default,linorder,order_top}) list \<Rightarrow> 'a
       \<Rightarrow> ('a bplustree \<times> 'a) list \<times> ('a bplustree \<times> 'a) list" 
  and imp_split :: "('a btnode ref option \<times> 'a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a \<Rightarrow> nat Heap" +
  fixes imp_isin_list:: "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> bool Heap"
    and imp_ins_list:: "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a pfarray Heap"
    and imp_del_list:: "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a pfarray Heap"
  assumes isin_list_rule [sep_heap_rules]:"sorted_less ks \<Longrightarrow>
   <is_pfa c ks (a',n')> 
    imp_isin_list x (a',n') 
  <\<lambda>b. 
    is_pfa c ks (a',n')
    * \<up>(isin_list x ks = b)>\<^sub>t"
  and ins_list_rule [sep_heap_rules]:"sorted_less ks' \<Longrightarrow>
   <is_pfa c ks' (a',n')>
    imp_ins_list x (a',n') 
  <\<lambda>(a'',n'').  is_pfa (max c (length (insert_list x ks'))) (insert_list x ks') (a'',n'') >\<^sub>t"
  and del_list_rule [sep_heap_rules]:"sorted_less ks'' \<Longrightarrow>
   <is_pfa c ks'' (a',n')> 
    imp_del_list x (a',n') 
  <\<lambda>(a'',n''). is_pfa c (delete_list x ks'') (a'',n'') >\<^sub>t"
begin

subsection "Initialization"

definition empty ::"nat \<Rightarrow> 'a btnode ref Heap"
  where "empty k = do {
  empty_list \<leftarrow> pfa_empty (2*k);
  empty_leaf \<leftarrow> ref (Btleaf empty_list None);
  return empty_leaf
}"

lemma empty_rule:
  shows "<emp>
  empty k
  <\<lambda>r. bplustree_assn k (abs_split.empty_bplustree) r (Some r) None>"
  apply(subst empty_def)
  apply(sep_auto simp add: abs_split.empty_bplustree_def)
  done

subsection "Membership"

(* TODO introduce imperative equivalents to searching/inserting/deleting in a list *)
partial_function (heap) isin :: "'a btnode ref \<Rightarrow> 'a \<Rightarrow>  bool Heap"
  where
    "isin p x = do {
  node \<leftarrow> !p;
  (case node of
     Btleaf xs _ \<Rightarrow> imp_isin_list x xs |
     Btnode ts t \<Rightarrow> do {
       i \<leftarrow> imp_split ts x;
       tsl \<leftarrow> pfa_length ts;
       if i < tsl then do {
         s \<leftarrow> pfa_get ts i;
         let (sub,sep) = s in
           isin (the sub) x
       } else
           isin t x
    }
)}"

lemma nth_zip_zip:
  assumes "length ys = length xs"
    and "length zs = length xs"
    and "zs1 @ ((suba', x), sepa') # zs2 =
    zip (zip ys xs) zs"
  shows "suba' = ys ! length zs1 \<and>
         sepa' = zs ! length zs1 \<and>
         x = xs ! length zs1"
proof -
  obtain suba'' x' sepa'' where "zip (zip ys xs) zs ! length zs1 = ((suba'', x'), sepa'')"
    by (metis surj_pair)
  moreover have "((suba'', x'), sepa'')  = ((suba', x), sepa')"
    by (metis calculation assms(3) nth_append_length)
  moreover have "length zs1 < length xs"
  proof - 
    have "length (zip (zip ys xs) zs) = length xs"
      by (simp add: assms(1,2))
    then have "length zs1 + 1 + length zs2 = length xs"
      by (metis assms(1,3) group_cancel.add1 length_Cons length_append plus_1_eq_Suc)
    then show ?thesis
    by (simp add: assms(1))
  qed
  ultimately show ?thesis
    using assms(1,2) by auto
qed


lemma  "k > 0 \<Longrightarrow> root_order k t \<Longrightarrow> sorted_less (inorder t) \<Longrightarrow> sorted_less (leaves t) \<Longrightarrow>
   <bplustree_assn k t ti r z>
     isin ti x
   <\<lambda>y. bplustree_assn k t ti r z * \<up>(abs_split.isin t x = y)>\<^sub>t"
proof(induction t x arbitrary: ti r z rule: abs_split.isin.induct)
  case (1 x r z)
  then show ?case
    apply(subst isin.simps)
    apply sep_auto
    done
next
  case (2 ts t x ti r z)
   obtain ls rs where list_split[simp]: "split ts x = (ls,rs)"
     by (cases "split ts x")
  moreover have ts_non_empty: "length ts > 0"
    using "2.prems"(2) root_order.simps(2) by blast
  moreover have "sorted_less (separators ts)"
    using "2.prems"(3) sorted_inorder_separators by blast
  ultimately show ?case
  proof (cases rs)
    (* NOTE: induction condition trivial here *)
    case [simp]: Nil
    show ?thesis
      apply(subst isin.simps)
      using ts_non_empty  apply(sep_auto)
      subgoal  using \<open>sorted_less (separators ts)\<close> by blast
      apply simp
      apply sep_auto
        apply(rule hoare_triple_preI)
      apply (sep_auto)
      subgoal for a b ti tsi' rs x sub sep
        apply(auto simp add: split_relation_alt is_pfa_def dest!:  mod_starD list_assn_len)[]
        done
      thm "2.IH"(1)[of ls "[]"]
      using 2(3) apply(sep_auto heap: "2.IH"(1)[of ls "[]"] simp add: sorted_wrt_append)
      subgoal
        using "2.prems"(2) order_impl_root_order
        by (auto simp add: split_relation_alt is_pfa_def dest!:  mod_starD list_assn_len)[]
      subgoal 
        using "2.prems"(3) sorted_inorder_induct_last
        by (auto simp add: split_relation_alt is_pfa_def dest!:  mod_starD list_assn_len)[]
      subgoal using "2"(6) sorted_leaves_induct_last
        by (auto simp add: split_relation_alt is_pfa_def dest!:  mod_starD list_assn_len)[]
      using 2(3) apply(sep_auto heap: "2.IH"(1)[of ls "[]"] simp add: sorted_wrt_append)
      done
  next
    case [simp]: (Cons h rrs)
    obtain sub sep where h_split[simp]: "h = (sub,sep)"
      by (cases h)
      then show ?thesis
        apply(simp split: list.splits prod.splits)
        apply(subst isin.simps)
        using "2.prems" sorted_inorder_separators 
        apply(sep_auto)
          (* simplify towards induction step *)
         apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!: mod_starD list_assn_len)[]
(* NOTE show that z = (suba, sepa)  -- adjusted since we now contain also current pointers and forward pointers *)
         apply(rule norm_pre_ex_rule)+
         apply(rule hoare_triple_preI)
        subgoal for tsi n ti tsi' pointers suba sepa zs1 z zs2
          apply(cases z)
          subgoal for subacomb sepa'
            apply(cases subacomb)
            subgoal for suba' subp subfwd
          apply(subgoal_tac "z = ((suba, subp, subfwd), sepa)", simp)
          thm "2.IH"(2)[of ls rs h rrs sub sep "(the suba')" subp subfwd]
          using 2(3,4,5,6) apply(sep_auto
              heap:"2.IH"(2)[of ls rs h rrs sub sep "the suba'" subp subfwd]
              simp add: sorted_wrt_append)
          using list_split Cons h_split apply simp_all
          subgoal 
            by (meson "2.prems"(1) order_impl_root_order)
          subgoal
            apply(rule impI)
            apply(inst_ex_assn "(tsi,n)" "ti" "tsi'" "(zs1 @ ((suba', subp, subfwd), sepa') # zs2)" "pointers" "zs1" "z" "zs2")
              (* proof that previous assumptions hold later *)
             apply sep_auto
            done
          subgoal
            (* prove subgoal_tac assumption *)
            using nth_zip_zip[of "subtrees tsi'" "zip (r # butlast pointers) pointers" "separators tsi'" zs1 suba' "(subp, subfwd)" sepa' zs2]
             apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!: mod_starD list_assn_len)[]
          done
        done
      done
    done
      (* eliminate last vacuous case *)
  apply(rule hoare_triple_preI)
  apply(auto simp add: split_relation_def dest!: mod_starD list_assn_len)[]
  done
  qed
qed

subsection "Insertion"


datatype 'c btupi = 
  T\<^sub>i "'c btnode ref" |
  Up\<^sub>i "'c btnode ref" "'c" "'c btnode ref"

fun btupi_assn where
  "btupi_assn k (abs_split.T\<^sub>i l) (T\<^sub>i li) r z =
   bplustree_assn k l li r z" |
(*TODO ai is not necessary not in the heap area of li *)
  "btupi_assn k (abs_split.Up\<^sub>i l a r) (Up\<^sub>i li ai ri) r' z' =
   (\<exists>\<^sub>A newr. bplustree_assn k l li r' newr * bplustree_assn k r ri newr z' * id_assn a ai)" |
  "btupi_assn _ _ _ _ _ = false"


(* TODO take in a pointer ot a btnode instead, only create one new node *)
definition node\<^sub>i :: "nat \<Rightarrow> 'a btnode ref \<Rightarrow> 'a btupi Heap" where
  "node\<^sub>i k p \<equiv> do {
    pt \<leftarrow> !p;
    let a = kvs pt; ti = lst pt in do {
    n \<leftarrow> pfa_length a;
    if n \<le> 2*k then do {
      a' \<leftarrow> pfa_shrink_cap (2*k) a;
      p := Btnode a' ti;
      return (T\<^sub>i p)
    }
    else do {
      b \<leftarrow> (pfa_empty (2*k) :: ('a btnode ref option \<times> 'a) pfarray Heap);
      i \<leftarrow> split_half a;
      m \<leftarrow> pfa_get a (i-1);
      b' \<leftarrow> pfa_drop a i b;
      a' \<leftarrow> pfa_shrink (i-1) a;
      a'' \<leftarrow> pfa_shrink_cap (2*k) a';
      let (sub,sep) = m in do {
        p := Btnode a'' (the sub);
        r \<leftarrow> ref (Btnode b' ti);
        return (Up\<^sub>i p sep r)
      }
    }
  }
}"

definition Lnode\<^sub>i :: "nat \<Rightarrow> 'a btnode ref  \<Rightarrow> 'a btupi Heap" where
  "Lnode\<^sub>i k p \<equiv> do {
    pt \<leftarrow> !p;
    let a = vals pt; nxt = fwd pt in do {
    n \<leftarrow> pfa_length a;
    if n \<le> 2*k then do {
      a' \<leftarrow> pfa_shrink_cap (2*k) a;
      p := Btleaf a' nxt;
      return (T\<^sub>i p)
    }
    else do {
      b \<leftarrow> (pfa_empty (2*k) :: 'a pfarray Heap);
      i \<leftarrow> split_half a;
      m \<leftarrow> pfa_get a (i-1);
      b' \<leftarrow> pfa_drop a i b;
      a' \<leftarrow> pfa_shrink i a;
      a'' \<leftarrow> pfa_shrink_cap (2*k) a';
      r \<leftarrow> ref (Btleaf b' nxt);
      p := Btleaf a'' (Some r);
      return (Up\<^sub>i p m r)
    }
  }
}"

(* TODO Lnode\<^sub>i allocates a new node when invoked, do not invoke if array didn't grow *)
partial_function (heap) ins :: "nat \<Rightarrow> 'a \<Rightarrow> 'a btnode ref \<Rightarrow> 'a btupi Heap"
  where
    "ins k x p = do {
  node \<leftarrow> !p;
  (case node of
    Btleaf ksi nxt \<Rightarrow> do {
      ksi' \<leftarrow> imp_ins_list x ksi; 
      p := Btleaf ksi' nxt;
      Lnode\<^sub>i k p
    } |
    Btnode tsi ti \<Rightarrow> do {
      i \<leftarrow> imp_split tsi x;
      tsl \<leftarrow> pfa_length tsi;
      if i < tsl then do {
        s \<leftarrow> pfa_get tsi i;
        let (sub,sep) = s in do {
          r \<leftarrow> ins k x (the sub);
          case r of (T\<^sub>i lp) \<Rightarrow> do {
            pfa_set tsi i (Some lp,sep);
            return (T\<^sub>i p)
          } |
          (Up\<^sub>i lp x' rp) \<Rightarrow> do {
            pfa_set tsi i (Some rp,sep);
            tsi' \<leftarrow> pfa_insert_grow tsi i (Some lp,x');
            p := Btnode tsi' ti;
            node\<^sub>i k p
          }
        }
      }
      else do {
        r \<leftarrow> ins k x ti;
        case r of (T\<^sub>i lp) \<Rightarrow> do {
            p := (Btnode tsi lp);
            return (T\<^sub>i p)
        } | (Up\<^sub>i lp x' rp) \<Rightarrow> do { 
            tsi' \<leftarrow> pfa_append_grow' tsi (Some lp,x');
            p := Btnode tsi' rp;
            node\<^sub>i k p
        }
      }
  }
)}"


(*fun tree\<^sub>i::"'a up\<^sub>i \<Rightarrow> 'a bplustree" where
  "tree\<^sub>i (T\<^sub>i sub) = sub" |
  "tree\<^sub>i (Up\<^sub>i l a r) = (Node [(l,a)] r)" 

fun insert::"nat \<Rightarrow> 'a \<Rightarrow> 'a bplustree \<Rightarrow> 'a bplustree" where
  "insert k x t = tree\<^sub>i (ins k x t)"
*)

definition insert :: "nat \<Rightarrow> 'a \<Rightarrow> 'a btnode ref \<Rightarrow> 'a btnode ref Heap" where
  "insert \<equiv> \<lambda>k x ti. do {
  ti' \<leftarrow> ins k x ti;
  case ti' of
     T\<^sub>i sub \<Rightarrow> return sub |
     Up\<^sub>i l a r \<Rightarrow> do {
        kvs \<leftarrow> pfa_init (2*k) (Some l,a) 1;
        t' \<leftarrow> ref (Btnode kvs r);
        return t'
      }
}"


lemma take_butlast_prepend: "take n (butlast (r # pointers)) =
       butlast (r # take n pointers)"
  apply(cases pointers)
  subgoal by auto[]
  by (smt (verit, del_insts) One_nat_def Suc_to_right length_Cons length_butlast length_take min_eq_arg(2) nat_le_linear take_Suc_Cons take_butlast_conv take_take)

lemma take_butlast_append: "take n (butlast (xs @ x # ys)) =
       take n (xs @ (butlast (x#ys)))"
  by (auto simp add: butlast_append)

lemma map_eq_nth_eq_diff:
  assumes A: "map f l = map g l'"
  and B: "i < length l"
  shows "f (l!i) = g (l'!i)"
proof -
  from A have "length l = length l'"
    by (metis length_map)
  thus ?thesis using A B
    apply (induct l l' arbitrary: i rule: list_induct2)
      apply (simp)
    subgoal for x xs y ys i
      apply(cases i)
      apply(simp add: nth_def)
      apply simp
      done
    done
qed

lemma "BPlusTree_Set.split_half ts = (ls,rs) \<Longrightarrow> length ls = Suc (length ts) div 2"
  by (metis Suc_eq_plus1 split_half_conc)


declare abs_split.node\<^sub>i.simps [simp add]
declare last.simps[simp del] butlast.simps[simp del]
lemma node\<^sub>i_rule: assumes c_cap: "2*k \<le> c" "c \<le> 4*k+1"
    and "length tsi' = length pointers"
    and "tsi'' = zip (zip (map fst tsi') (zip (butlast (r#pointers)) (butlast (pointers@[z])))) (map snd tsi')"
  shows "<p \<mapsto>\<^sub>r Btnode (a,n) ti * is_pfa c tsi' (a,n) * blist_assn k ts tsi'' * bplustree_assn k t ti (last (r#pointers)) z>
  node\<^sub>i k p
  <\<lambda>u. btupi_assn k (abs_split.node\<^sub>i k ts t) u r z>\<^sub>t"
proof (cases "length ts \<le> 2*k")
  case [simp]: True
  then show ?thesis
    apply(subst node\<^sub>i_def)
    apply(rule hoare_triple_preI)
    apply(sep_auto)
    subgoal by (sep_auto simp add: is_pfa_def)[]
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    subgoal using assms(3,4) by (sep_auto)
    subgoal 
      apply(subgoal_tac "length ts = length tsi'")
    subgoal using True by (sep_auto)
    subgoal using True assms by (sep_auto dest!: mod_starD list_assn_len)
    done
  done
next
  case [simp]: False
  then obtain ls sub sep rs where      
    split_half_eq: "BPlusTree_Set.split_half ts = (ls@[(sub,sep)],rs)"
    using abs_split.node\<^sub>i_cases by blast
  then show ?thesis
    apply(subst node\<^sub>i_def)
    apply(rule hoare_triple_preI)
    apply sep_auto
    subgoal by (sep_auto simp add:  split_relation_alt split_relation_length is_pfa_def dest!: mod_starD list_assn_len)
    subgoal using assms by (sep_auto dest!: mod_starD list_assn_len)
    subgoal
      apply(subgoal_tac "length ts = length tsi'")
      subgoal using False by (sep_auto dest!: mod_starD list_assn_len)
      subgoal using assms(3,4) by (sep_auto dest!: mod_starD list_assn_len)
      done
    apply sep_auto
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    using c_cap apply sep_auto
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    using c_cap apply simp
    apply(rule hoare_triple_preI)
    apply(vcg)
    apply(simp add: split_relation_alt)
    apply(rule impI)+
    subgoal for  _ _ rsia subi' sepi' rsin lsi _
      supply R = append_take_drop_id[of "(length ls)" ts,symmetric]
      thm R
      apply(subst R)
      supply R = Cons_nth_drop_Suc[of "length ls" ts, symmetric]
      thm R
      apply(subst R)
      subgoal
          using assms(3,4) apply(auto dest!: mod_starD  list_assn_len     
          simp add: list_assn_prod_map id_assn_list_alt)
          apply (metis One_nat_def Suc_eq_plus1 length_Cons length_append length_take list.size(3) min_less_self_conv(2) not_less_eq trans_less_add1)
          done
     supply R=list_assn_append_Cons_left[where xs="take (length ls) ts" and ys="drop (Suc (length ls)) ts" and x="ts ! (length ls)"]
      thm R
      apply(subst R)
      apply(auto)[]
      apply(rule ent_ex_preI)+
      apply(subst ent_pure_pre_iff; rule impI)
      apply (simp add: prod_assn_def split!: prod.splits)
      subgoal for tsi''l subi'' subir subinext sepi'' tsi''r sub' sep'
        (* instantiate right hand side *)
(* newr is the first leaf of the tree directly behind sub
  and (r#pointers) is the list of all first leafs of the tree in this node
   \<rightarrow> the pointer at position of sub in pointers
      or the pointer at position of sub+1 in (r#pointers)
*)
      (* Suc (length tsi') div 2 - Suc 0) = length ls *)
        apply(inst_ex_assn "subinext" "(rsia,rsin)" ti
        "drop (length ls+1) tsi'"
        "drop (length ls+1) tsi''"
        "drop (length ls+1) pointers"
        lsi
        "the subi'"
        "take (length ls) tsi'"
        "take (length ls) tsi''"
        "take (length ls) pointers"
      )
      apply (sep_auto)
      subgoal using assms(3) by linarith
      subgoal 
        using assms(3,4) by (auto dest!: mod_starD 
          simp add: take_map[symmetric] take_zip[symmetric] take_butlast_prepend[symmetric]
      )
         subgoal using assms(3,4) by (auto dest!: mod_starD      
          simp add: list_assn_prod_map id_assn_list_alt)
         subgoal 
           apply(subgoal_tac "length ls < length pointers")
           apply(subgoal_tac "subinext = pointers ! (length ls)")
           subgoal
        using assms(3,4) apply (auto 
          simp add: drop_map[symmetric] drop_zip[symmetric] drop_butlast[symmetric] Cons_nth_drop_Suc
      )[]
           supply R = drop_Suc_Cons[where n="length ls" and xs="butlast pointers" and x=r, symmetric]
           thm R
           apply(simp only: R drop_zip[symmetric])
           apply (simp add: last.simps butlast.simps)
           done
        subgoal apply(auto dest!: mod_starD list_assn_len)     
        proof (goal_cases)
        case 1
        have "length ls < length tsi''"
          using assms(3,4) "1"(11) by auto
        moreover have "subinext = snd (snd (fst (tsi'' ! length ls)))"
          using 1 calculation by force
        ultimately have "subinext = map snd (map snd (map fst tsi'')) ! length ls"
          by auto
        then show ?case
          using assms(3,4) by auto
      qed
          subgoal apply(auto dest!: mod_starD  list_assn_len)     
        proof (goal_cases)
          case 1 
          then have "length ls  < length ts"
            by (simp)
          moreover have "length ts = length tsi''"
            by (simp add: 1)
          moreover have "\<dots> = length pointers"
            using assms(3,4) by auto
          ultimately show ?case by simp
        qed
      done
    apply(rule entails_preI)
      (* introduce some simplifying equalities *)
        apply(subgoal_tac "Suc (length tsi') div 2 = length ls + 1")
     prefer 2 subgoal 
        apply(auto dest!: mod_starD  list_assn_len)     
        proof (goal_cases)
          case 1
          have "length tsi' = length tsi''"
            using assms(3,4) by auto
          also have "\<dots> = length ts"
            by (simp add: 1)
          finally show ?case 
            by (metis 1 div2_Suc_Suc length_append_singleton length_take)
        qed
    apply(subgoal_tac "length ts = length tsi''")
        prefer 2 subgoal using assms(3,4) by (auto dest!: mod_starD  list_assn_len)     
    apply(subgoal_tac "(sub', sep') = (sub, sep)")
        prefer 2 subgoal
        by (metis One_nat_def Suc_eq_plus1 Suc_length_conv abs_split.length_take_left length_0_conv length_append less_add_Suc1 nat_arith.suc1 nth_append_length nth_take)
      apply(subgoal_tac "length ls = length tsi''l")
        prefer 2 subgoal by (auto dest!: mod_starD list_assn_len)
    apply(subgoal_tac "(subi'', sepi'') = (subi', sepi')")
      prefer 2 subgoal
        using assms(3,4) apply (auto dest!: mod_starD list_assn_len)
      proof (goal_cases)
        case 1
        then have "tsi'' ! length tsi''l =  ((subi'', subir, subinext), sepi'')"
          by auto
        moreover have "length tsi''l < length tsi''"
          by (simp add: 1)
        moreover have "length tsi''l < length tsi'"
          using "1" assms(3) by linarith
        ultimately have
            "fst (fst (tsi'' ! length tsi''l)) = fst (tsi' ! length tsi''l)"
            "snd (tsi'' ! length tsi''l) = snd (tsi' ! length tsi''l)"
          using assms(4) by auto
        then show ?case
          by (simp add: "1"(4) \<open>tsi'' ! length tsi''l = ((subi'', subir, subinext), sepi'')\<close>)
        case 2
        then show ?case
          by (metis \<open>snd (tsi'' ! length tsi''l) = snd (tsi' ! length tsi''l)\<close> \<open>tsi'' ! length tsi''l = ((subi'', subir, subinext), sepi'')\<close> snd_conv)
      qed
    apply(subgoal_tac "(last (r # take (length ls) pointers)) = subir")
      prefer 2 subgoal
        using assms(3) apply (auto dest!: mod_starD list_assn_len)
      proof (goal_cases)
        case 1
        have "length tsi''l < length tsi''"
          by (simp add: 1)
        then have "fst (snd (fst (tsi'' ! length tsi''l))) = subir"
          using 1 assms(4) by auto
        moreover have "map fst (map snd (map fst tsi'')) = butlast (r#pointers)"
          using assms(3,4) by auto
        moreover have "(last (r#take (length ls) pointers)) = butlast (r#pointers) ! (length tsi''l)"
          by (smt (z3) "1"(10) "1"(11) One_nat_def Suc_eq_plus1 Suc_to_right abs_split.length_take_left append_butlast_last_id div_le_dividend le_add2 length_butlast length_ge_1_conv length_take lessI list.size(4) min_eq_arg(2) nth_append_length nth_take nz_le_conv_less take_Suc_Cons take_butlast_conv)
        ultimately show ?case
          using 1 apply auto
          by (metis (no_types, hide_lams) "1"(11) length_map map_map nth_append_length)
      qed
    apply(subgoal_tac "(last (subinext # drop (Suc (length tsi''l)) pointers)) = last (r#pointers)")
       prefer 2 subgoal
        using assms(3) apply (auto dest!: mod_starD list_assn_len)
      proof (goal_cases)
        case 1
        have "length tsi''l < length tsi''"
          using 1 by auto
        moreover have "subinext = snd (snd (fst (tsi'' ! length tsi''l)))"
          using "1" calculation by force
        ultimately have "subinext = map snd (map snd (map fst tsi'')) ! length tsi''l"
          by auto
        then have "subinext = pointers ! length tsi''l" 
          using assms(3,4) by auto
        then have "(subinext # drop (Suc (length tsi''l)) pointers) = drop (length tsi''l) pointers"
          by (metis 1 Cons_nth_drop_Suc Suc_eq_plus1 Suc_to_right abs_split.length_take_left div_le_dividend le_add1 less_Suc_eq nz_le_conv_less take_all_iff zero_less_Suc)
        moreover have "last (drop (length tsi''l) pointers) = last pointers"
          using \<open>length tsi''l < length tsi''\<close>  1 by force
        ultimately show ?case
          by (auto simp add: last.simps butlast.simps)
      qed
    apply(subgoal_tac "take (length tsi''l) ts = ls")
      prefer 2 subgoal
        by (metis append.assoc append_eq_conv_conj append_take_drop_id)
    apply(subgoal_tac "drop (Suc (length tsi''l)) ts = rs")
      prefer 2 subgoal by (metis One_nat_def Suc_eq_plus1 Suc_length_conv append_eq_conv_conj append_take_drop_id length_0_conv length_append)
    subgoal by (sep_auto)
    done
  done
  done
qed
declare last.simps[simp add] butlast.simps[simp add]
declare abs_split.node\<^sub>i.simps [simp del]

declare abs_split.Lnode\<^sub>i.simps [simp add]
lemma Lnode\<^sub>i_rule:
  assumes "k > 0 " "r = Some a" "2*k \<le> c" "c \<le> 4*k"
  shows "<a \<mapsto>\<^sub>r (Btleaf xsi z) * is_pfa c xs xsi>
  Lnode\<^sub>i k a
  <\<lambda>a. btupi_assn k (abs_split.Lnode\<^sub>i k xs) a r z>\<^sub>t"
proof (cases "length xs \<le> 2*k")
  case [simp]: True
  then show ?thesis
    apply(subst Lnode\<^sub>i_def)
      apply(rule hoare_triple_preI; simp)
    using assms apply(sep_auto eintros del: exI heap add: pfa_shrink_cap_rule)
    subgoal for _ _ aaa ba
      apply(inst_existentials aaa ba z)
      apply simp_all
      done
    subgoal
      apply(rule hoare_triple_preI)
      using True apply (auto dest!: mod_starD list_assn_len)+
      done
    done
next
  case [simp]: False
  then obtain ls sep rs where
    split_half_eq: "BPlusTree_Set.split_half xs = (ls@[sep],rs)"
    using abs_split.Lnode\<^sub>i_cases by blast
  then show ?thesis
    apply(subst Lnode\<^sub>i_def)
    apply auto
    using assms apply (vcg heap add: pfa_shrink_cap_rule; simp)
      apply(rule hoare_triple_preI)
      apply (sep_auto heap add: pfa_drop_rule simp add: split_relation_alt
              dest!: mod_starD list_assn_len)

    subgoal by (sep_auto simp add: is_pfa_def split!: prod.splits)
    subgoal by (sep_auto simp add: is_pfa_def split!: prod.splits)
    apply(sep_auto)
    subgoal by (sep_auto simp add: is_pfa_def split!: prod.splits)
    subgoal by (sep_auto simp add: is_pfa_def split!: prod.splits)
    apply(sep_auto eintros del: exI)
    subgoal for  _ _ _ _ rsa rn lsa ln newr
        (* instantiate right hand side *)
      apply(inst_existentials "Some newr"
             rsa rn  z
             lsa ln "Some newr"
            )
        (* introduce equality between equality of split tsi/ts and original lists *)
      apply(simp_all add: pure_def)
      apply(sep_auto dest!: mod_starD)
      apply(subgoal_tac "Suc (length xs) div 2 = Suc (length ls)")
      apply(subgoal_tac "xs = take (Suc (length ls)) xs @  drop (Suc (length ls)) xs")
      subgoal 
        by (metis nth_append_length)
      subgoal by auto
      subgoal by auto
      subgoal by sep_auto
      done
    done
qed
declare abs_split.Lnode\<^sub>i.simps [simp del]

lemma Lnode\<^sub>i_rule_tree:
  assumes "k > 0"
  shows "<bplustree_assn k (LNode xs) a r z>
  Lnode\<^sub>i k a
  <\<lambda>a. btupi_assn k (abs_split.Lnode\<^sub>i k xs) a r z>\<^sub>t"
proof -
  note Lnode\<^sub>i_rule
  then show ?thesis
    using assms by (sep_auto)
qed

lemma node\<^sub>i_no_split: "length ts \<le> 2*k \<Longrightarrow> abs_split.node\<^sub>i k ts t = abs_split.T\<^sub>i (Node ts t)"
  by (simp add: abs_split.node\<^sub>i.simps)

lemma Lnode\<^sub>i_no_split: "length ts \<le> 2*k \<Longrightarrow> abs_split.Lnode\<^sub>i k ts = abs_split.T\<^sub>i (LNode ts)"
  by (simp add: abs_split.Lnode\<^sub>i.simps)

lemma id_assn_emp[simp]: "id_assn a a = emp"
  by (simp add: pure_def)

lemma butlast2[simp]: "butlast (ts@[a,b]) = ts@[a]"
  by (induction ts) auto

lemma butlast3[simp]: "butlast (ts@[a,b,c]) = ts@[a,b]"
  by (induction ts) auto

lemma zip_append_last: "length as = length bs \<Longrightarrow> zip (as@[a]) (bs@[b]) = zip as bs @ [(a,b)]"
  by simp

lemma pointers_append: "zip (z#as) (as@[a]) = zip (butlast (z#as)) as @ [(last (z#as),a)]"
  by (metis (no_types, hide_lams) Suc_eq_plus1 append_butlast_last_id butlast_snoc length_Cons length_append_singleton length_butlast list.distinct(1) zip_append_last)

lemma node\<^sub>i_rule_app: assumes c_cap: "2*k \<le> c" "c \<le> 4*k+1"
    and "length tsi' = length pointers"
    and "tsi'' = zip (zip (map fst tsi') (zip (butlast (r'#pointers)) pointers)) (map snd tsi')"
  shows "
<  p \<mapsto>\<^sub>r Btnode (tsia,tsin) ri *
   is_pfa c (tsi' @ [(Some li, a)]) (tsia, tsin) *
   blist_assn k ts tsi'' *
   bplustree_assn k l li (last (r'#pointers)) lz *
   bplustree_assn k r ri lz rz> node\<^sub>i k p
 <\<lambda>u. btupi_assn k (abs_split.node\<^sub>i k (ts @ [(l, a)]) r) u r' rz>\<^sub>t"
proof -
(*[of k c "(tsi' @ [(Some li, b)])" _ _ "(ls @ [(l, a)])" r ri]*)
  note node\<^sub>i_rule[of k c "tsi'@[(Some li, a)]" "pointers@[lz]" "tsi''@[((Some li, last(r'#pointers), lz),a)]" r' rz p tsia tsin ri "ts@[(l,a)]" r, OF assms(1,2)]
  then show ?thesis
    using assms
    apply (auto simp add:
         list_assn_app_one pointers_append
         mult.left_assoc
    )
    done
qed

lemma norm_pre_ex_drule: "<\<exists>\<^sub>Ax. P x> c <Q> \<Longrightarrow> (\<And>x. <P x> c <Q>)"
proof (goal_cases)
  case 1
  then show ?case
    using Hoare_Triple.cons_pre_rule by blast
qed

(* setting up the simplifier for tsi'' in the other direction *)
lemma node\<^sub>i_rule_diff_simp: assumes c_cap: "2*k \<le> c" "c \<le> 4*k+1"
    and "length tsi' = length pointers"
    and "zip (zip (map fst tsi') (zip (butlast (r#pointers)) (butlast (pointers@[z])))) (map snd tsi') = tsi''"
  shows "<p \<mapsto>\<^sub>r Btnode (a,n) ti * is_pfa c tsi' (a,n) * blist_assn k ts tsi'' * bplustree_assn k t ti (last (r#pointers)) z>
  node\<^sub>i k p
  <\<lambda>u. btupi_assn k (abs_split.node\<^sub>i k ts t) u r z>\<^sub>t"
  using node\<^sub>i_rule assms by (auto simp del: butlast.simps last.simps)

lemma list_assn_aux_append_Cons2: 
  shows "length xs = length zsl \<Longrightarrow> list_assn R (xs@x#y#ys) (zsl@z1#z2#zsr) = (list_assn R xs zsl * R x z1 * R y z2 * list_assn R ys zsr)"
  by (sep_auto simp add: mult.assoc)

lemma pointer_zip_access: "length tsi' = length pointers \<Longrightarrow> i < length tsi' \<Longrightarrow>
  zip (zip (map fst tsi') (zip (butlast (r'#pointers)) (butlast (pointers@[z])))) (map snd tsi') ! i
= ((fst (tsi' ! i), (r'#pointers) ! i, pointers ! i), snd (tsi' ! i))"
  apply(auto)
  by (metis append_butlast_last_id butlast.simps(2) len_greater_imp_nonempty length_Cons length_append_singleton nth_butlast)

lemma pointer_zip'_access: "length tsi' = length pointers \<Longrightarrow> i < length tsi' \<Longrightarrow>
  zip (zip (map fst tsi') (zip (butlast (r'#pointers)) (butlast (pointers@[z])))) (map snd tsi') ! i
= ((fst (tsi' ! i), (r'#pointers) ! i, pointers ! i), snd (tsi' ! i))"
  apply(auto)
  by (metis One_nat_def nth_take take_Cons' take_butlast_conv)

lemma access_len_last: "(x#xs@ys) ! (length xs) = last (x#xs)"
  by (induction xs) auto


lemma node\<^sub>i_rule_ins2: assumes c_cap: "2*k \<le> c" "c \<le> 4*k+1"
    and "pointers = lpointers@lz#rz#rpointers"
    and "length tsi'' = length pointers"
    and "length lpointers = length lsi'"
    and "length rpointers = length rsi'"
    and "length lsi'' = length ls"
    and "length lsi' = length ls"
    and "tsi'' = zip (zip (map fst tsi') (zip (butlast (r'#pointers)) (butlast (pointers@[z])))) (map snd tsi')"
    and "tsi' = (lsi' @ (Some li, a) # (Some ri,a') # rsi')" 
    and "lsi'' = take (length lsi') tsi''"
    and "rsi'' = drop (Suc (Suc (length lsi'))) tsi''"
    and "r'' = last (r'#lpointers)"
    and "z'' = last (r'#pointers)"
    and "length tsi' = length pointers"
  shows "
<  p \<mapsto>\<^sub>r Btnode (tsia,tsin) ti *
   is_pfa c (lsi' @ (Some li, a) # (Some ri,a') # rsi') (tsia, tsin) *
   blist_assn k ls lsi'' *
   bplustree_assn k l li r'' lz*
   bplustree_assn k r ri lz rz*
   blist_assn k rs rsi'' *
   bplustree_assn k t ti z'' z> node\<^sub>i k p 
<\<lambda>u. btupi_assn k (abs_split.node\<^sub>i k (ls @ (l, a) # (r,a') # rs) t) u r' z>\<^sub>t"
proof -
  have "
     tsi'' =
     lsi'' @ ((Some li, r'', lz), a) # ((Some ri, lz, rz), a') # rsi''"
  proof (goal_cases)
    case 1
    have "tsi'' = take (length lsi') tsi'' @ drop (length lsi') tsi''"
      by auto
    also have "\<dots> = take (length lsi') tsi'' @ tsi''!(length lsi') # drop (Suc (length lsi')) tsi''"
      by (simp add: Cons_nth_drop_Suc assms(3) assms(4) assms(5))
    also have "\<dots> = take (length lsi') tsi'' @ tsi''!(length lsi') # tsi''!(Suc (length lsi')) #drop (Suc (Suc (length lsi'))) tsi''"
      by (metis (no_types, lifting) Cons_nth_drop_Suc One_nat_def Suc_eq_plus1 Suc_le_eq assms(3) assms(4) assms(5) diff_add_inverse2 diff_is_0_eq length_append list.size(4) nat.simps(3) nat_add_left_cancel_le not_less_eq_eq)
    also have "\<dots> = lsi'' @ tsi''!(length lsi') # tsi''!(Suc (length lsi')) # rsi''"
      using assms(11) assms(12) by force
    also have "\<dots> = lsi'' @ ((Some li, r'', lz), a) # ((Some ri, lz, rz), a') # rsi''"
    proof (auto, goal_cases)
      case 1
      have "pointers ! length lsi' = lz"
        by (metis assms(3) assms(5) list.sel(3) nth_append_length)
      moreover have "(r'#pointers) ! length lsi' = r''"
        using assms access_len_last[of r' lpointers]
        by (auto simp del: last.simps butlast.simps)
      moreover have " tsi'!(length lsi') = (Some li,a)"
        using assms(10) by auto
      moreover have "length lsi' < length tsi'"
        using \<open>take (length lsi') tsi'' @ tsi'' ! length lsi' # drop (Suc (length lsi')) tsi'' = take (length lsi') tsi'' @ tsi'' ! length lsi' # tsi'' ! Suc (length lsi') # drop (Suc (Suc (length lsi'))) tsi''\<close> assms(15) assms(4) same_append_eq by fastforce
      ultimately show ?case 
        using pointer_zip'_access[of tsi' "pointers" "length lsi'" r'] assms(15) assms(9)
        by (auto simp del: last.simps butlast.simps)
    next
      case 2
      have "pointers ! (Suc (length lsi')) = rz"
        by (metis Suc_eq_plus1 append_Nil assms(3) assms(5) list.sel(3) nth_Cons_Suc nth_append_length nth_append_length_plus)
      moreover have "(r'#pointers) ! (Suc (length lsi')) = lz"
        using assms(3,4,5,6,7,8) apply auto
        by (metis nth_append_length)
      moreover have " tsi'!(Suc (length lsi')) = (Some ri,a')"
        using assms(10)
        by (metis (no_types, lifting) Cons_nth_drop_Suc Suc_le_eq append_eq_conv_conj assms(15) assms(4) drop_all drop_eq_ConsD list.inject list.simps(3) not_less_eq_eq)
      moreover have "Suc (length lsi') < length tsi'"
        by (simp add: assms(10))
      ultimately show ?case 
        using pointer_zip'_access[of tsi' pointers "Suc (length lsi')"] assms(15) assms(9)
        by (auto simp del: last.simps butlast.simps)
    qed
    finally show ?thesis .
  qed
  moreover note node\<^sub>i_rule_diff_simp[of k c 
    "(lsi' @ (Some li, a) # (Some ri,a') # rsi')" 
    "lpointers@lz#rz#rpointers" r' z
    "lsi''@((Some li, r'', lz), a)#((Some ri, lz, rz), a')#rsi''"
    p tsia tsin ti "ls@(l,a)#(r,a')#rs" t
]
  ultimately show ?thesis
    using assms(1,2,3,4,5,6,7,8,9,10,13,14)
    apply (auto simp add: mult.left_assoc list_assn_aux_append_Cons2 prod_assn_def
simp del: last.simps)
    done
qed

lemma upd_drop_prepend: "i < length xs \<Longrightarrow> drop i (list_update xs i a) = a#(drop (Suc i) xs)" 
  by (simp add: upd_conv_take_nth_drop)

lemma zip_update: "(zip xs ys)!i = (a,b) \<Longrightarrow> list_update (zip xs ys) i (c,b) = zip (list_update xs i c) ys"
  by (metis fst_conv list_update_beyond list_update_id not_le_imp_less nth_zip snd_conv update_zip)

lemma append_Cons_last: "last (xs@x#ys) = last (x#ys)"
  by (induction xs) auto
                                                                                            
declare last.simps[simp del] butlast.simps[simp del]
lemma ins_rule:
  "k > 0 \<Longrightarrow>
  sorted_less (inorder t) \<Longrightarrow>
  sorted_less (leaves t) \<Longrightarrow>
  root_order k t \<Longrightarrow>
  <bplustree_assn k t ti r z>
  ins k x ti
  <\<lambda>a. btupi_assn k (abs_split.ins k x t) a r z>\<^sub>t"
proof (induction k x t arbitrary: ti r z rule: abs_split.ins.induct)
  case (1 k x xs ti r z)
  then show ?case
    apply(subst ins.simps)
    apply (sep_auto heap: Lnode\<^sub>i_rule)
    done
next
  case (2 k x ts t ti r' z)
  obtain ls rrs where list_split: "split ts x = (ls,rrs)"
    by (cases "split ts x")
  have [simp]: "sorted_less (separators ts)"
    using "2.prems" sorted_inorder_separators by simp
  have [simp]: "sorted_less (inorder t)"
    using "2.prems" sorted_inorder_induct_last by simp
  show ?case
  proof (cases rrs)
    case Nil
    then have split_rel_i: "split_relation ts (ls,[]) i \<Longrightarrow> i = length ts" for i
      by (simp add: split_relation_alt)
    show ?thesis
    proof (cases "abs_split.ins k x t")
      case (T\<^sub>i a)
      then show ?thesis
        apply(subst ins.simps)
        using Nil 
        apply(simp)
        apply vcg
        apply(simp)
        apply vcg
        thm imp_split_rule
        apply sep_auto
          apply(rule hoare_triple_preI)
        using Nil split_rel_i list_split
        apply (sep_auto dest!: split_rel_i mod_starD)
        subgoal
          using Nil list_split
          by (simp add: list_assn_aux_ineq_len split_relation_alt)
        subgoal
          using Nil list_split
          by (simp add: list_assn_aux_ineq_len split_relation_alt)
        subgoal for tsil tsin tti tsi'
          thm "2.IH"(1)[of ls rrs tti]
          using "2.prems" sorted_leaves_induct_last
          using  Nil list_split T\<^sub>i abs_split.split_conc[OF list_split] order_impl_root_order 
          apply(sep_auto split!: list.splits simp add: split_relation_alt
              heap add: "2.IH"(1)[of ls rrs tti])
          subgoal for ai
            apply(cases ai)
            subgoal by sep_auto
            subgoal by sep_auto
            done
          done
        done
    next
      case (Up\<^sub>i l a r)
      then show ?thesis
        apply(subst ins.simps)
        using Nil 
        apply(simp)
        apply vcg
        apply simp
        apply vcg
        apply sep_auto
          apply(rule hoare_triple_preI)
        using Nil list_split
        apply (sep_auto dest!: split_rel_i mod_starD)
        subgoal
          using Nil list_split
          by (simp add: list_assn_aux_ineq_len split_relation_alt)                 
        subgoal
          using Nil list_split 
          by (simp add: list_assn_aux_ineq_len split_relation_alt)
        subgoal for tsia tsin tti tsi' pointers _ _ _ _ _ _ _ _ _ _  i 
          thm "2.IH"(1)[of ls rrs tti "last (r'#pointers)" z]
          using "2.prems" sorted_leaves_induct_last
          using  Nil list_split Up\<^sub>i abs_split.split_conc[OF list_split] order_impl_root_order
          apply(sep_auto split!: list.splits 
              simp add: split_relation_alt
              heap add: "2.IH"(1)[of ls rrs tti])
          subgoal for ai
            apply(cases ai)
            subgoal by sep_auto
            apply(rule hoare_triple_preI)
            thm node\<^sub>i_rule_app
            apply(sep_auto heap add: node\<^sub>i_rule_app)
            apply(sep_auto simp add: pure_def)
            done
          done
        done
    qed
  next
    case (Cons a rs)
    obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a)
    then have [simp]: "sorted_less (inorder sub)"
      by (metis "2"(4) abs_split.split_set(1) list_split local.Cons some_child_sub(1) sorted_inorder_subtrees)
    from Cons have split_rel_i: "ts = ls@a#rs \<and> i = length ls \<Longrightarrow> i < length ts" for i
      by (simp add: split_relation_alt)
    then show ?thesis
      proof (cases "abs_split.ins k x sub")
        case (T\<^sub>i a')
        then show ?thesis
          apply(auto simp add: Cons list_split a_split)
          apply(subst ins.simps)
          apply vcg
           apply auto
          apply vcg
          subgoal by sep_auto
          apply simp
          (*this solves a subgoal*) apply simp
            (* at this point, we want to introduce the split, and after that tease the
  hoare triple assumptions out of the bracket, s.t. we don't split twice *)
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          using list_split Cons abs_split.split_conc[of ts x ls rrs] 
          apply (simp add: list_assn_append_Cons_left)
          apply(rule norm_pre_ex_rule)+
          apply(rule hoare_triple_preI)
          apply(simp add: split_relation_alt prod_assn_def split!: prod.splits)
              (* actual induction branch *)
          subgoal for tsia tsin tti tsi' pointers suba' sepa' lsi' suba subleaf subnext sepa rsi' _ _ sub' sep'
            apply(subgoal_tac "length ls = length lsi'")
          apply(subgoal_tac "(suba', sepa') = (suba, sepa)") 
          apply(subgoal_tac "(sub', sep') = (sub, sep)") 
          thm "2.IH"(2)[of ls rs a rrs sub sep "the suba" subleaf subnext]
             apply (sep_auto heap add: "2.IH"(2))
          subgoal using "2.prems" by metis
            subgoal using "2.prems" sorted_leaves_induct_subtree \<open>sorted_less (inorder sub)\<close>
              by (auto split!: btupi.splits) 
            subgoal 
              using "2.prems"(3) sorted_leaves_induct_subtree by blast
            subgoal using "2.prems"(1,4) order_impl_root_order[of k sub] by auto
            subgoal for up
              apply(cases up)
              subgoal for ai
               apply (sep_auto eintros del: exI)
                apply(inst_existentials tsia tsin tti "tsi'[length ls := (Some ai, sepa)]" "lsi'@((Some ai, subleaf, subnext),sepa)#rsi'" pointers)
                  apply (sep_auto simp add: prod_assn_def split!: prod.splits)
                  subgoal  (* necessary goal due to the difference between implementation and abstract code *)
                  proof (goal_cases)
                    case 1
                    then have *: "((suba, subleaf, subnext), sepa) = (zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi'))!(length lsi')"
                      by (metis nth_append_length)
                    have **:"(zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi'))!(length lsi') = (((subtrees tsi')!(length lsi'), (butlast (r'#pointers))!(length lsi'), pointers!(length lsi')), (separators tsi')!(length lsi'))" 
                      using 1 by simp
                    have "lsi' @ ((Some ai, subleaf, subnext), sepa) # rsi' =
                          list_update (lsi' @ ((suba, subleaf, subnext), sepa) # rsi') (length lsi') ((Some ai, subleaf, subnext), sepa)"
                      by simp
                    also have "\<dots> = list_update (zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi')) (length lsi') ((Some ai, subleaf,subnext), sepa)" 
                      using 1 by simp
                    also have "\<dots> = zip (list_update (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (length lsi') (Some ai, subleaf, subnext)) (separators tsi')"
                      by (meson zip_update sym[OF *])
                    finally show ?case
                      using ** *
                      by (simp add: update_zip map_update)
                  qed
                  subgoal by sep_auto
                  done
              subgoal
                apply(rule hoare_triple_preI)
                using T\<^sub>i
                subgoal by (auto dest!: mod_starD)
                done
              done
            subgoal
              using a_split by fastforce
            subgoal
                  proof (goal_cases)
                    case 1
                    then have *: "((suba, subleaf, subnext), sepa) = (zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi'))!(length lsi')"
                      by (metis nth_append_length)
                    have **:"(zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi'))!(length lsi') = (((subtrees tsi')!(length lsi'), (butlast (r'#pointers))!(length lsi'), pointers!(length lsi')), (separators tsi')!(length lsi'))" 
                      using 1 by simp
                    then show ?case
                      using ** * 1
                      by simp
                  qed
                  subgoal by (auto dest!: mod_starD list_assn_len)
                  done
                subgoal
                  apply(rule hoare_triple_preI)
                    using Cons split_relation_alt[of ts ls "a#rs"] list_split
                    by (auto dest!: list_assn_len mod_starD)
                  done
      next
        case (Up\<^sub>i l w r)
        then show ?thesis
          apply(auto simp add: Cons list_split a_split)
          apply(subst ins.simps)
          apply vcg
           apply auto
          apply vcg
          subgoal by sep_auto
          apply simp
          (*this solves a subgoal*) apply simp
            (* at this point, we want to introduce the split, and after that tease the
  hoare triple assumptions out of the bracket, s.t. we don't split twice *)
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          apply (vcg (ss))
          using list_split Cons abs_split.split_conc[of ts x ls rrs] 
          apply (simp add: list_assn_append_Cons_left)
          apply(rule norm_pre_ex_rule)+
          apply(rule hoare_triple_preI)
          apply(simp add: split_relation_alt prod_assn_def split!: prod.splits)
              (* actual induction branch *)
          subgoal for tsia tsin tti tsi' pointers suba' sepa' lsi' suba subleaf subnext sepa rsi' _ _ sub' sep'
          apply(subgoal_tac "length ls = length lsi'") 
          apply(subgoal_tac "(suba', sepa') = (suba, sepa)") 
          apply(subgoal_tac "(sub', sep') = (sub, sep)") 
          thm "2.IH"(2)[of ls rs a rrs sub sep "the suba" subleaf subnext]
             apply (sep_auto heap add: "2.IH"(2))
          subgoal using "2.prems" by metis
            subgoal using "2.prems" sorted_leaves_induct_subtree \<open>sorted_less (inorder sub)\<close>
              by (auto split!: btupi.splits) 
            subgoal 
              using "2.prems"(3) sorted_leaves_induct_subtree by blast
            subgoal using "2.prems"(1,4) order_impl_root_order[of k sub] by auto
            subgoal for up
              apply(cases up)
            subgoal by simp
            subgoal for li ai ri (* split case *)
              apply (sep_auto dest!: mod_starD list_assn_len heap: pfa_insert_grow_rule)
              subgoal by (sep_auto simp add: is_pfa_def)
              subgoal for aa ba ac bc ae be ak bk al bl newr x xaa
                apply(simp split!: prod.splits)
              subgoal for tsia'
                supply R= node\<^sub>i_rule_ins2[where k=k and c="max (2*k) (Suc tsin)" and
                      lsi'="take (length lsi') tsi'" and li=li and ri=ri
                      and rsi'="drop (Suc (length lsi')) tsi'"
                      and lpointers="take (length lsi') pointers"
                      and rpointers="drop (Suc (length lsi')) pointers"
                      and pointers="take (length lsi') pointers @ newr # subnext # drop (Suc (length lsi')) pointers"
                      and z''="last (r'#pointers)"
                      and tsi'="take (length lsi') tsi' @ (Some li, ai) # (Some ri, sepa) # drop (Suc (length lsi')) tsi'"
                      and r'="r'" and z="z"
and tsi''="zip (zip (subtrees
           (take (length lsi') tsi' @
            (Some li, ai) # (Some ri, sepa) # drop (Suc (length lsi')) tsi'))
      (zip (butlast
             (r' #
              take (length lsi') pointers @ newr # subnext # drop (Suc (length lsi')) pointers))
        (butlast
          ((take (length lsi') pointers @ newr # subnext # drop (Suc (length lsi')) pointers) @
           [z]))))
 (separators
   (take (length lsi') tsi' @
    (Some li, ai) # (Some ri, sepa) # drop (Suc (length lsi')) tsi'))"
                    ]
                thm R
              apply (sep_auto simp add: upd_drop_prepend eintros del: exI heap: R split!: prod.splits)
                subgoal
                proof (goal_cases)
                  case 1
                  from sym[OF 1(8)] have "lsi' = take (length lsi') (zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi'))"
                    by auto
                  then show ?case using 1
                    by (auto simp add: take_zip take_map take_butlast_prepend take_butlast_append)
                qed
                subgoal 
                proof (goal_cases)
                  case 1
                  let ?tsi''="zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi')"
                  from sym[OF 1(8)] have "rsi' = drop (Suc (length lsi')) ?tsi''"
                    by auto
                  moreover have "pointers ! length lsi' = subnext" 
                  proof -
                    let ?i = "length lsi'"
                    have "?tsi'' ! ?i = ((fst (tsi'!?i), (r' # pointers) ! ?i, pointers ! ?i), snd (tsi' ! ?i))"
                      using pointer_zip_access 1 by fastforce
                    moreover have "?tsi'' ! ?i = ((suba, subleaf, subnext), sepa)"
                      by (metis "1"(19) "1"(8) nth_append_length)
                    ultimately show ?thesis by simp
                  qed
                  ultimately show ?case using 1
                    by (auto simp add: drop_zip drop_map drop_butlast Cons_nth_drop_Suc)
                qed
              subgoal 
                proof (goal_cases)
                  case 1
                  let ?tsi''="zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi')"
                  let ?i = "length lsi'"
                  show ?thesis
                  proof -
                    let ?i = "length lsi'"
                    have "?tsi'' ! ?i = ((fst (tsi'!?i), (r' # pointers) ! ?i, pointers ! ?i), snd (tsi' ! ?i))"
                      using pointer_zip_access 1 by fastforce
                    moreover have "?tsi'' ! ?i = ((suba, subleaf, subnext), sepa)"
                      by (metis "1"(19) "1"(8) nth_append_length)
                    ultimately have "(r'#pointers) ! ?i = subleaf"
                      by simp
                    then show ?thesis
                      using sym[OF append_take_drop_id, of pointers "length lsi'"]
                      using access_len_last[of r' "take (length lsi') pointers" "drop (length lsi') pointers"]
                      using 1
                      by simp
                  qed
                qed
                subgoal
                proof (goal_cases)
                  case 1
                  let ?tsi''="zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi')"
                  let ?i = "length lsi'"
                  have "pointers ! ?i = subnext" 
                  proof -
                    have "?tsi'' ! ?i = ((fst (tsi'!?i), (r' # pointers) ! ?i, pointers ! ?i), snd (tsi' ! ?i))"
                      using pointer_zip_access 1 by fastforce
                    moreover have "?tsi'' ! ?i = ((suba, subleaf, subnext), sepa)"
                      by (metis "1"(19) "1"(8) nth_append_length)
                    ultimately show ?thesis by simp
                  qed
                  moreover have "drop (length lsi') pointers \<noteq> []"
                    using "1"(3) by auto
                  moreover have "pointers \<noteq> []"
                    using "1"(3) by auto
                  ultimately show ?case
                    apply(auto simp add: Cons_nth_drop_Suc  last.simps)
                    apply(auto simp add: last_conv_nth)
                    by (metis Suc_to_right le_SucE)
                qed
              subgoal by auto
              subgoal by (sep_auto simp add: pure_def)
              done
            done
          done
        done
            subgoal
              using a_split by fastforce
            subgoal
                  proof (goal_cases)
                    case 1
                    then have *: "((suba, subleaf, subnext), sepa) = (zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi'))!(length lsi')"
                      by (metis nth_append_length)
                    have **:"(zip (zip (subtrees tsi') (zip (butlast (r' # pointers)) pointers)) (separators tsi'))!(length lsi') = (((subtrees tsi')!(length lsi'), (butlast (r'#pointers))!(length lsi'), pointers!(length lsi')), (separators tsi')!(length lsi'))" 
                      using 1 by simp
                    then show ?case
                      using ** * 1
                      by simp
                  qed
                  subgoal by (auto dest!: mod_starD list_assn_len)
                  done
                subgoal
                  apply(rule hoare_triple_preI)
                    using Cons split_relation_alt[of ts ls "a#rs"] list_split
                    by (auto dest!: list_assn_len mod_starD)
                  done
      qed
    qed
  qed
declare last.simps[simp add] butlast.simps[simp add]

text "The imperative insert refines the abstract insert."

lemma insert_rule:
  assumes "k > 0" "sorted_less (inorder t)" "sorted_less (leaves t)" "root_order k t"
  shows "<bplustree_assn k t ti r z>
  insert k x ti
  <\<lambda>u. bplustree_assn k (abs_split.insert k x t) u r z>\<^sub>t"
proof(cases "abs_split.ins k x t")
  case (T\<^sub>i x1)
  then show ?thesis
  unfolding insert_def
   using assms
    by (sep_auto split!: btupi.splits heap: ins_rule)
next
  case (Up\<^sub>i x21 x22 x23)
  then show ?thesis
  unfolding insert_def
  using assms
  apply (sep_auto eintros del: exI split!: btupi.splits heap: ins_rule)
  subgoal for x21a x22a x23a newr a b xa
  apply(inst_existentials a b x23a "[(Some x21a, x22a)]" "[((Some x21a, r, newr),x22a)]" "[newr]")
    apply (auto simp add: prod_assn_def)
    apply (sep_auto)
    done
  done
qed

text "The \"pure\" resulting rule follows automatically."
lemma insert_rule':
  shows "<bplustree_assn (Suc k) t ti r z * \<up>(abs_split.invar_leaves (Suc k) t \<and> sorted_less (leaves t))>
  insert (Suc k) x ti
  <\<lambda>ri.\<exists>\<^sub>Au. bplustree_assn (Suc k) u ri r z * \<up>(abs_split.invar_leaves (Suc k) u \<and> sorted_less (leaves u) \<and> leaves u = (ins_list x (leaves t)))>\<^sub>t"
  using Laligned_sorted_inorder[of t top] sorted_wrt_append
  using abs_split.insert_bal[of t] abs_split.insert_order[of "Suc k" t]
  using abs_split.insert_Linorder_top[of "Suc k" t]
  by (sep_auto heap: insert_rule simp add: sorted_ins_list)


subsection "Deletion"

text "The below definitions work for non-linked-leaf B-Plus-Trees
but not yet for linked-leaf trees"


(* rebalance middle tree gets a list of trees, an index pointing to
the position of sub/sep and a last tree *)
(*
definition rebalance_middle_tree:: "nat \<Rightarrow> (('a::{default,heap,linorder,order_top}) btnode ref option \<times> 'a) pfarray \<Rightarrow> nat \<Rightarrow> 'a btnode ref \<Rightarrow> 'a btnode Heap"
  where
    "rebalance_middle_tree \<equiv> \<lambda> k tsi i p_ti. ( do {
  ti \<leftarrow> !p_ti;
  case ti of
  Btleaf txsi \<Rightarrow> do {
      (r_sub,sep) \<leftarrow> pfa_get tsi i;
      subi \<leftarrow> !(the r_sub);
      l_sub \<leftarrow> pfa_length (vals subi);
      l_txs \<leftarrow> pfa_length (txsi);
      if l_sub \<ge> k \<and> l_txs \<ge> k then do {
        return (Btnode tsi p_ti)
      } else do {
        l_tsi \<leftarrow> pfa_length tsi;
        if i+1 = l_tsi then do {
          mts' \<leftarrow> pfa_extend_grow (vals subi) (txsi);
          res_node\<^sub>i \<leftarrow> Lnode\<^sub>i k mts';
          case res_node\<^sub>i of
            T\<^sub>i u \<Rightarrow> do {
              tsi' \<leftarrow> pfa_shrink i tsi;
              return (Btnode tsi' u)
            } |
            Up\<^sub>i l a r \<Rightarrow> do {
              tsi' \<leftarrow> pfa_set tsi i (Some l,a);
              return (Btnode tsi' r)
            }
        } else do {
          (r_rsub,rsep) \<leftarrow> pfa_get tsi (i+1);
          rsub \<leftarrow> !(the r_rsub);
          mts' \<leftarrow> pfa_extend_grow (vals subi) (vals rsub);
          res_node\<^sub>i \<leftarrow> Lnode\<^sub>i k mts';
          case res_node\<^sub>i of
           T\<^sub>i u \<Rightarrow> do {
            tsi' \<leftarrow> pfa_set tsi i (Some u,rsep);
            tsi'' \<leftarrow> pfa_delete tsi' (i+1);
            return (Btnode tsi'' p_ti)
          } |
           Up\<^sub>i l a r \<Rightarrow> do {
            tsi' \<leftarrow> pfa_set tsi i (Some l,a);
            tsi'' \<leftarrow> pfa_set tsi' (i+1) (Some r,rsep);
            return (Btnode tsi'' p_ti)
          }
        }
  }} |
  Btnode ttsi tti \<Rightarrow> do {
      (r_sub,sep) \<leftarrow> pfa_get tsi i;
      subi \<leftarrow> !(the r_sub);
      l_sub \<leftarrow> pfa_length (kvs subi);
      l_tts \<leftarrow> pfa_length (ttsi);
      if l_sub \<ge> k \<and> l_tts \<ge> k then do {
        return (Btnode tsi p_ti)
      } else do {
        l_tsi \<leftarrow> pfa_length tsi;
        if i+1 = l_tsi then do {
          mts' \<leftarrow> pfa_append_extend_grow (kvs subi) (Some (lst subi),sep) (ttsi);
          res_node\<^sub>i \<leftarrow> node\<^sub>i k mts' (lst ti);
          case res_node\<^sub>i of
            T\<^sub>i u \<Rightarrow> do {
              tsi' \<leftarrow> pfa_shrink i tsi;
              return (Btnode tsi' u)
            } |
            Up\<^sub>i l a r \<Rightarrow> do {
              tsi' \<leftarrow> pfa_set tsi i (Some l,a);
              return (Btnode tsi' r)
            }
        } else do {
          (r_rsub,rsep) \<leftarrow> pfa_get tsi (i+1);
          rsub \<leftarrow> !(the r_rsub);
          mts' \<leftarrow> pfa_append_extend_grow (kvs subi) (Some (lst subi),sep) (kvs rsub);
          res_node\<^sub>i \<leftarrow> node\<^sub>i k mts' (lst rsub);
          case res_node\<^sub>i of
           T\<^sub>i u \<Rightarrow> do {
            tsi' \<leftarrow> pfa_set tsi i (Some u,rsep);
            tsi'' \<leftarrow> pfa_delete tsi' (i+1);
            return (Btnode tsi'' p_ti)
          } |
           Up\<^sub>i l a r \<Rightarrow> do {
            tsi' \<leftarrow> pfa_set tsi i (Some l,a);
            tsi'' \<leftarrow> pfa_set tsi' (i+1) (Some r,rsep);
            return (Btnode tsi'' p_ti)
          }
        }
  }
}}
)
"


definition rebalance_last_tree:: "nat \<Rightarrow> (('a::{default,heap,linorder,order_top}) btnode ref option \<times> 'a) pfarray \<Rightarrow> 'a btnode ref \<Rightarrow> 'a btnode Heap"
  where
    "rebalance_last_tree \<equiv> \<lambda>k tsi ti. do {
   l_tsi \<leftarrow> pfa_length tsi;
   rebalance_middle_tree k tsi (l_tsi-1) ti
}"


subsection "Refinement of the abstract B-tree operations"


lemma P_imp_Q_implies_P: "P \<Longrightarrow> (Q \<longrightarrow> P)"
  by simp

lemma node\<^sub>i_rule_ins: "\<lbrakk>2*k \<le> c; c \<le> 4*k+1; length ls = length lsi\<rbrakk> \<Longrightarrow>
 <is_pfa c (lsi @ (Some li, a) # rsi) (aa, al) *
   blist_assn k ls lsi *
   bplustree_assn k l li *
   blist_assn k rs rsi *
   bplustree_assn k t ti>
     node\<^sub>i k (aa, al) ti
 <btupi_assn k (abs_split.node\<^sub>i k (ls @ (l, a) # rs) t)>\<^sub>t"
proof -
  assume [simp]: "2*k \<le> c" "c \<le> 4*k+1" "length ls = length lsi"
  moreover note node\<^sub>i_rule[of k c "(lsi @ (Some li, a) # rsi)" aa al "(ls @ (l, a) # rs)" t ti]
  ultimately show ?thesis
    by (simp add: mult.left_assoc list_assn_aux_append_Cons)
qed

lemma Lnode\<^sub>i_rule_extend: "\<lbrakk>2*k \<le> c; c \<le> 4*k; length ls = length lsi\<rbrakk> \<Longrightarrow>
 <is_pfa c (lsi @ rsi) (aa, al) *
   list_assn id_assn ls lsi *
   list_assn id_assn rs rsi >
     Lnode\<^sub>i k (aa, al)
 <btupi_assn k (abs_split.Lnode\<^sub>i k (ls @ rs))>\<^sub>t"
proof -
  assume [simp]: "2*k \<le> c" "c \<le> 4*k" "length ls = length lsi"
  moreover note Lnode\<^sub>i_rule[of k c "(lsi @ rsi)" aa al "(ls @ rs)"]
  ultimately show ?thesis
    by (simp add: mult.left_assoc list_assn_aux_append_Cons)
qed


lemma btupi_assn_T: "h \<Turnstile> btupi_assn k (abs_split.node\<^sub>i k ts t) (T\<^sub>i x) \<Longrightarrow> abs_split.node\<^sub>i k ts t = abs_split.T\<^sub>i (Node ts t)"
  apply(auto simp add: abs_split.node\<^sub>i.simps dest!: mod_starD split!: list.splits prod.splits)
  done

lemma btupi_assn_Up: "h \<Turnstile> btupi_assn k (abs_split.node\<^sub>i k ts t) (Up\<^sub>i l a r) \<Longrightarrow>
  abs_split.node\<^sub>i k ts t = (
    case BPlusTree_Set.split_half ts of (ls,rs) \<Rightarrow> (
      case last ls of (sub,sep) \<Rightarrow>
        abs_split.Up\<^sub>i (Node (butlast ls) sub) sep (Node rs t)
  )
)"
  apply(auto simp add: abs_split.node\<^sub>i.simps split!: list.splits prod.splits)
  done

lemma Lbtupi_assn_T: "h \<Turnstile> btupi_assn k (abs_split.Lnode\<^sub>i k ts) (T\<^sub>i x) \<Longrightarrow> abs_split.Lnode\<^sub>i k ts = abs_split.T\<^sub>i (LNode ts)"
  apply(cases "length ts \<le> 2*k")
  apply(auto simp add: abs_split.Lnode\<^sub>i.simps split!: list.splits prod.splits)
  done

lemma Lbtupi_assn_Up: "h \<Turnstile> btupi_assn k (abs_split.Lnode\<^sub>i k ts) (Up\<^sub>i l a r) \<Longrightarrow>
  abs_split.Lnode\<^sub>i k ts = (
    case BPlusTree_Set.split_half ts of (ls,rs) \<Rightarrow> (
      case last ls of sep \<Rightarrow>
        abs_split.Up\<^sub>i (LNode ls) sep (LNode rs)
  )
)"
  apply(auto simp add: abs_split.Lnode\<^sub>i.simps split!: list.splits prod.splits)
  done

lemma second_last_access:"(xs@a#b#ys) ! Suc(length xs) = b"
  by (simp add: nth_via_drop)

lemma second_last_update:"(xs@a#b#ys)[Suc(length xs) := c] = (xs@a#c#ys)"
  by (metis append.assoc append_Cons empty_append_eq_id length_append_singleton list_update_length)

lemma clean_heap:"\<lbrakk>(a, b) \<Turnstile> P \<Longrightarrow> Q; (a, b) \<Turnstile> P\<rbrakk> \<Longrightarrow> Q"
  by auto

lemma rebalance_middle_tree_rule:
  assumes "height t = height sub"
    and "case rs of (rsub,rsep) # list \<Rightarrow> height rsub = height t | [] \<Rightarrow> True"
    and "i = length ls"
  shows "<is_pfa (2*k) tsi (a,n) * blist_assn k (ls@(sub,sep)#rs) tsi * bplustree_assn k t ti>
  rebalance_middle_tree k (a,n) i ti
  <\<lambda>r. btnode_assn k (abs_split.rebalance_middle_tree k ls sub sep rs t) r >\<^sub>t"
apply(simp add: list_assn_append_Cons_left prod_assn_def)
  apply(rule norm_pre_ex_rule)+
proof(goal_cases)
  case (1 lsi z rsi)
  then show ?case 
  proof(cases z)
    case z_split[simp]: (Pair subi sepi)
    then show ?thesis 
proof(cases sub)
  case sub_leaf[simp]: (LNode mxs)
  then obtain txs where t_leaf[simp]: "t = LNode txs" using assms
    by (cases t) auto
  show ?thesis 
  proof(cases "length mxs \<ge> k \<and> length txs \<ge> k")
    case True
    then show ?thesis
      apply(subst rebalance_middle_tree_def)
      apply(rule hoare_triple_preI)
      apply(sep_auto)
      subgoal using assms by (auto  dest!: mod_starD list_assn_len)
      subgoal for _ _ _ _ _ _ _ _ _ _ _ _ _ _ x
      using assms apply(sep_auto  split!: prod.splits)
        apply(subgoal_tac "x = (subi, sepi)")
      using assms apply(sep_auto  split!: prod.splits)
      subgoal using assms by (auto simp del: height_bplustree.simps dest!: mod_starD list_assn_len)[]
    subgoal for subi' sepi' x
      apply(auto dest!: mod_starD list_assn_len)[]
        apply(vcg)
       apply(auto split!: prod.splits)[]
      subgoal
        apply (rule ent_ex_postI[where x="lsi@(subi', sepi)#rsi"])
        apply (sep_auto)
        done
      subgoal
        apply(rule hoare_triple_preI)
        using True apply(auto dest!: mod_starD list_assn_len)
        done
      done
    done
  done
  next
    case False
    then show ?thesis  
    proof(cases rs)
      case Nil
      then show ?thesis
      apply(subst rebalance_middle_tree_def)
      apply(rule hoare_triple_preI)
      apply(sep_auto)
       subgoal using assms by (auto dest!: mod_starD dest!: list_assn_len)[]
      subgoal for _ _ _ _ _ _ _ _ _ _ _ _ _ _  x
      using assms apply(sep_auto  split!: prod.splits)
        apply(subgoal_tac "x = (subi, sepi)")
      using assms apply(sep_auto  split!: prod.splits)
      subgoal using assms by (auto simp del: height_bplustree.simps dest!: mod_starD list_assn_len)[]
      apply(auto dest!: mod_starD list_assn_len simp: prod_assn_def)[]
      apply(vcg)
       apply(auto)[]
     using False apply(auto dest!: mod_starD list_assn_len)
     done
      apply(sep_auto)
      subgoal using assms by (auto dest!: mod_starD list_assn_len)[]
      subgoal using assms by (auto dest!: mod_starD list_assn_len)[]
      subgoal for _ _ _ _ _ _ _ _ _ _ _ _ _ _ x
        apply(sep_auto dest!: mod_starD)
        apply(subgoal_tac "x = (subi, sepi)")
     prefer 2
        subgoal by (metis assms(3) list_assn_len nth_append_length)
        using assms apply(sep_auto  split!: prod.splits)
        subgoal for _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r_sub r_sep
          apply(subgoal_tac "r_sub = subi \<and> r_sep = sepi")
          using assms apply(sep_auto  split!: prod.splits)
          apply (metis assms(3) list_assn_len nth_append_length prod.inject)
          done
        apply simp
        apply sep_auto
     subgoal
  (* still the "IF" branch *)
  (* solves impossible case*)
       apply(rule entailsI)
       using False apply (sep_auto del: impCE dest!: list_assn_len mod_starD)[]
      (*TODO subst by nice solution *)
       done
     subgoal
  (* still the "IF" branch *)
  (* solves impossible case*)
       apply (rule entailsI)
       using False apply (sep_auto del: impCE dest!: list_assn_len mod_starD)[]
       done
     apply simp
     apply(rule hoare_triple_preI)
(* for each possible combination of \<le> and \<not>\<le>, a subgoal is created *)
     apply(sep_auto heap add: Lnode\<^sub>i_rule_extend dest!: mod_starD)
     subgoal by (auto simp add: is_pfa_def)
     subgoal by (auto simp add: is_pfa_def)
    subgoal by (auto simp add: is_pfa_def)
    subgoal by (auto simp add: is_pfa_def)
    subgoal by (auto simp add: is_pfa_def dest!: list_assn_len)
     subgoal
       apply(rule hoare_triple_preI)
     apply(sep_auto del: impCE split!: btupi.splits)
       subgoal 
         apply(auto del: impCE dest!: Lbtupi_assn_T mod_starD)
         apply(rule ent_ex_postI[where x="lsi"])
         apply sep_auto
         done
       subgoal for _ _ li ai ri
       apply (sep_auto del: impCE)
       apply(auto del: impCE dest!: Lbtupi_assn_Up mod_starD split!: list.splits)
         apply(rule ent_ex_postI[where x="lsi @ [(Some li, ai)]"])
         apply sep_auto
         done
       done
     apply (sep_auto del: impCE)
     subgoal using assms by (auto simp add: is_pfa_def dest!: list_assn_len mod_starD)[]
     apply (sep_auto del: impCE)
     subgoal using assms by (auto dest!: list_assn_len mod_starD)[]
     subgoal using assms by (auto dest!: list_assn_len mod_starD)[]
     done
   done
next
  case (Cons rss rrs)
  then obtain rrsub rrsep where rss_split[simp]: "rss = (rrsub, rrsep)"
    by (cases rss)
  moreover obtain rrxs where rrsub_node[simp]: "rrsub = LNode rrxs" 
    using assms Cons rss_split t_leaf by (cases rrsub) auto 
  from Cons show ?thesis
      apply(subst rebalance_middle_tree_def)
      apply(rule hoare_triple_preI)
      apply(sep_auto)
       subgoal using assms by (auto  dest!: mod_starD list_assn_len)
      subgoal for _ _ _ _ _ _ _ _ _ _ _ _ _ _  x
      using assms apply(sep_auto  split!: prod.splits)
        apply(subgoal_tac "x = (subi, sepi)")
      using assms apply (sep_auto  split!: prod.splits)
      subgoal using assms by (auto simp del: height_bplustree.simps dest!: mod_starD list_assn_len)[]
      apply(auto dest!: mod_starD list_assn_len simp: prod_assn_def)[]
      apply(vcg)
      using False apply(auto dest!: mod_starD list_assn_len)
     done
      apply(sep_auto)
       subgoal using assms by (auto dest!: mod_starD list_assn_len)[]
       subgoal using assms by (auto dest!: mod_starD list_assn_len)[]

      subgoal for _ _ txsia txsin txsi subxsia subxsin subxsi txsia' txsin' txsi' subxsia' subxsin' subxsi' x
   apply(sep_auto dest!: mod_starD)
        apply(subgoal_tac "x = (subi, sepi)")
     prefer 2
        subgoal by (metis assms(3) list_assn_len nth_append_length)
        apply simp
        apply vcg
        subgoal for _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r_sub r_sep
          apply(subgoal_tac "r_sub = subi \<and> r_sep = sepi")
          using assms apply(sep_auto  split!: prod.splits)
          apply (metis assms(3) list_assn_len nth_append_length prod.inject)
          done
      apply(sep_auto  split!: prod.splits)
(* TODO show more nicely that the node to the right is not a leaf *)
          subgoal
            apply(rule entailsI)
            using assms apply (auto simp del: height_bplustree.simps dest!: mod_starD list_assn_len)[]
            done
          subgoal 
            apply(rule entailsI)
            using assms apply (auto simp del: height_bplustree.simps dest!: mod_starD list_assn_len)[]
            done
      apply(vcg)
      subgoal using assms by (auto simp del: height_bplustree.simps dest!: mod_starD list_assn_len)[]
      subgoal using assms by (auto simp del: height_bplustree.simps dest!: mod_starD list_assn_len)[]
      apply vcg
      subgoal using assms by (auto simp del: height_bplustree.simps dest!: mod_starD list_assn_len)[]
      subgoal for _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ _ _  rsubi rsepi _ _ _ rx
        apply(subgoal_tac "rsepi = sep")
        prefer 2
        subgoal
          using assms by (auto simp del: height_bplustree.simps dest!: mod_starD list_assn_len)[]
        supply R = list_assn_append_Cons_left[where xs="[]" and x=rss and ys=rrs and zs=rsi]
        using R
       apply(auto del: impCE simp add: R)[]
          apply(simp add: prod_assn_def)
        apply(rule norm_pre_ex_rule)+
        subgoal for rrsubi rrsepi rrsi rrtsia rrtsin rrxsi  _ z _ 
          apply(rule hoare_triple_preI)
        apply(subgoal_tac "rx = z")
          prefer 2
          apply (sep_auto simp add: assms(3) list_assn_len second_last_access)
          apply(thin_tac "_\<Turnstile>_")+
          apply(auto del: impCE simp add: prod_assn_def)[]
          apply(vcg (ss))
          apply(vcg (ss))
          apply(vcg (ss))
          apply(vcg (ss))
          apply(vcg (ss))
          subgoal for rrxsia rrxsi _
            apply(cases "rrxsia")
            apply simp
            apply (sep_auto del: impCE)
             supply R = Lnode\<^sub>i_rule_extend[where
                 k=k and
                 c="(max (2 * k) (subxsin' + _))" 
                  and lsi=subxsi'
                  and rsi=rrxsi
                  and al="(subxsin' + _)"
              ]
       thm R
          apply(rule hoare_triple_preI)
     apply(sep_auto del: impCE heap add: R)
       subgoal by (auto del: impCE simp add: is_pfa_def dest!: list_assn_len mod_starD)
       subgoal by (auto del: impCE simp add: is_pfa_def dest!: list_assn_len mod_starD)
          apply(rule hoare_triple_preI)
     apply(sep_auto del: impCE split!: btupi.splits)
         subgoal using assms by (auto del: impCE simp add: is_pfa_def dest!: list_assn_len mod_starD)
         subgoal for _ _ _ _ a
      apply(rule hoare_triple_preI)
         apply(sep_auto del: impCE dest!: Lbtupi_assn_T mod_starD)
         subgoal using assms apply (auto del: impCE simp add: is_pfa_def dest!: list_assn_len mod_starD)
           by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 Suc_lessI Suc_n_not_le_n add_Suc_right le_add1 length_append length_take less_add_Suc1 list.size(4) min_eq_arg(2) nat.inject)
         subgoal
       apply(auto del: impCE)[]
         apply(vcg)
         apply(auto del: impCE split!: prod.splits)
         apply(rule ent_ex_postI[where x="((take (Suc i) lsi @ take (Suc i - length lsi) ((rsubi, sep) # (rrsubi, rrsep) # rrsi))
         [i := (Some a, rrsep)] @
         drop (Suc (Suc i)) lsi @
         drop (Suc (Suc i) - length lsi) ((rsubi, sep) # (rrsubi, rrsep) # rrsi))"])
           apply(rule ent_ex_postI[where x="(txsia', txsin')"])
           apply(rule ent_ex_postI[where x="txsi'"])
         using assms apply (sep_auto del: impCE dest!: list_assn_len mod_starD)
         done
       done
     subgoal for _ _ _ _ l a r 
      apply(rule hoare_triple_preI)
       apply(auto del: impCE dest!: mod_starD)[]
         apply(sep_auto del: impCE)
         subgoal using assms by (auto dest!: list_assn_len)
         apply(sep_auto del: impCE)
         subgoal using assms by (auto dest!: list_assn_len)
         apply(vcg)
         apply (auto del: impCE dest!: Lbtupi_assn_Up split!: prod.splits)
         apply(rule ent_ex_postI[where x="(lsi @ (Some l, a) # (Some r, rrsep) # rrsi)"])
        apply(rule ent_ex_postI[where x="(txsia', txsin')"])
        apply(rule ent_ex_postI[where x="txsi'"])
         using assms apply (sep_auto del: impCE simp add: second_last_update list_assn_aux_append_Cons dest!: list_assn_len mod_starD )
         done
       done
     done
   done
  done
  done
qed
qed
next
  case sub_node[simp]: (Node mts mt)
  then obtain tts tt where t_node[simp]: "t = Node tts tt" using assms
    by (cases t) auto
  then show ?thesis 
  proof(cases "length mts \<ge> k \<and> length tts \<ge> k")
    case True
    then show ?thesis
      apply(subst rebalance_middle_tree_def)
      apply(rule hoare_triple_preI)
      apply(sep_auto dest!: mod_starD)
      subgoal using assms by (auto  dest!: list_assn_len)
      subgoal for _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          tsia tsin  tti ttsi _ _ _ _ x
      using assms apply(sep_auto  split!: prod.splits)
        apply(subgoal_tac "x = (subi, sepi)")
      using assms apply(sep_auto  split!: prod.splits)
      subgoal using assms by (auto simp del: height_bplustree.simps dest!: mod_starD list_assn_len)[]
    subgoal for subi' sepi' x
      apply(auto dest!: mod_starD list_assn_len)[]
        apply(vcg)
       apply(auto split!: prod.splits)[]
      subgoal
        apply (rule ent_ex_postI[where x="lsi@(subi', sepi)#rsi"])
        apply (rule ent_ex_postI[where x="(tsia, tsin)"])
        apply (rule ent_ex_postI[where x="tti"])
        apply (rule ent_ex_postI[where x=ttsi])
        apply (sep_auto)
        done
      subgoal
        apply(rule hoare_triple_preI)
        using True apply(auto dest!: mod_starD list_assn_len)
        done
      done
    done
  done
  next
    case False
    then show ?thesis  
    proof(cases rs)
      case Nil
      then show ?thesis
      apply(subst rebalance_middle_tree_def)
      apply(rule hoare_triple_preI)
      apply(sep_auto dest!: mod_starD)
       subgoal using assms by (auto  dest!: list_assn_len)[]
      subgoal for _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ _ _
          tsia tsin  tti ttsi _ _ _ _ x
      using assms apply(sep_auto  split!: prod.splits)
        apply(subgoal_tac "x = (subi, sepi)")
      using assms apply(sep_auto  split!: prod.splits)
      subgoal using assms by (auto simp del: height_bplustree.simps dest!: mod_starD list_assn_len)[]
      apply(auto dest!: mod_starD list_assn_len simp: prod_assn_def)[]
      apply(vcg)
       apply(auto)[]
     using False apply(auto dest!: mod_starD list_assn_len)
     done
      apply(sep_auto dest!: mod_starD)
      subgoal using assms by (auto dest!: list_assn_len)[]
      subgoal using assms by (auto dest!: list_assn_len)[]
      subgoal for _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ _ _
          tsia tsin  tti ttsi _ _ _ _ x
        apply(sep_auto)
        apply(subgoal_tac "x = (subi, sepi)")
     prefer 2
        subgoal by (metis assms(3) list_assn_len nth_append_length)
        using assms apply(sep_auto  split!: prod.splits)
        subgoal for r_sub r_sep
          apply(subgoal_tac "r_sub = subi \<and> r_sep = sepi")
          using assms apply(sep_auto  split!: prod.splits)
          apply (metis assms(3) list_assn_len nth_append_length prod.inject)
          done
        apply simp
        apply sep_auto
     subgoal
  (* still the "IF" branch *)
  (* solves impossible case*)
       apply(rule entailsI)
       using False apply (sep_auto del: impCE dest!: list_assn_len mod_starD)[]
      (*TODO subst by nice solution *)
       done
     subgoal
  (* still the "IF" branch *)
  (* solves impossible case*)
       apply (rule entailsI)
       using False apply (sep_auto del: impCE dest!: list_assn_len mod_starD)[]
       done
     apply simp
     apply(rule hoare_triple_preI)
(* for each possible combination of \<le> and \<not>\<le>, a subgoal is created *)
     apply(sep_auto heap add: node\<^sub>i_rule_ins dest!: mod_starD)
     subgoal by (auto simp add: is_pfa_def)
     subgoal by (auto simp add: is_pfa_def)
    subgoal by (auto simp add: is_pfa_def)
    subgoal by (auto simp add: is_pfa_def)
    subgoal by (auto simp add: is_pfa_def dest!: list_assn_len)
     subgoal
       apply(rule hoare_triple_preI)
     apply(sep_auto del: impCE split!: btupi.splits)
       subgoal 
         apply(auto del: impCE dest!: btupi_assn_T mod_starD)
         apply(rule ent_ex_postI[where x="lsi"])
         apply sep_auto
         done
       apply (sep_auto del: impCE)
       apply(auto del: impCE dest!: btupi_assn_Up mod_starD split!: list.splits prod.splits)[]
       subgoal for li ai ri
        apply(rule ent_ex_postI[where x="lsi @ [(Some li, ai)]"])
         apply sep_auto
         done
       done
     apply (sep_auto del: impCE)
     subgoal using assms by (auto simp add: is_pfa_def dest!: list_assn_len mod_starD)[]
     apply (sep_auto del: impCE)
     subgoal using assms by (auto dest!: list_assn_len mod_starD)[]
     subgoal using assms by (auto dest!: list_assn_len mod_starD)[]
     done
   done
next
  case (Cons rss rrs)
  then obtain rrsub rrsep where rss_split[simp]: "rss = (rrsub, rrsep)"
    by (cases rss)
  moreover obtain rrts rrt where rrsub_node[simp]: "rrsub = Node rrts rrt" 
    using assms Cons rss_split t_node by (cases rrsub) auto 
  from Cons show ?thesis
      apply(subst rebalance_middle_tree_def)
      apply(rule hoare_triple_preI)
      apply(sep_auto dest!: mod_starD)
       subgoal using assms by (auto  dest!: list_assn_len)
      subgoal for _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ _ _
          tsia tsin  tti ttsi _ _ _ _ x
      using assms apply(sep_auto  split!: prod.splits)
        apply(subgoal_tac "x = (subi, sepi)")
      using assms apply (sep_auto  split!: prod.splits)
      subgoal using assms by (auto simp del: height_bplustree.simps dest!: mod_starD list_assn_len)[]
      apply(auto dest!: mod_starD list_assn_len simp: prod_assn_def)[]
      apply(vcg)
      using False apply(auto dest!: mod_starD list_assn_len)
     done
      apply(sep_auto dest!: mod_starD)
       subgoal using assms by (auto dest!: list_assn_len)[]
       subgoal using assms by (auto dest!: list_assn_len)[]

      subgoal for _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ _ _
          tsia tsin ttsia ttsin tti ttsi rtsia rtsin mti rtsi x
   apply(sep_auto)
        apply(subgoal_tac "x = (subi, sepi)")
     prefer 2
        subgoal by (metis assms(3) list_assn_len nth_append_length)
        apply simp
        apply vcg
        subgoal for r_sub r_sep
          apply(subgoal_tac "r_sub = subi \<and> r_sep = sepi")
          using assms apply(sep_auto  split!: prod.splits)
          apply (metis assms(3) list_assn_len nth_append_length prod.inject)
          done
      apply(sep_auto  split!: prod.splits)
(* TODO show more nicely that the node to the right is not a leaf *)
          subgoal
            apply(rule entailsI)
            using assms apply (auto simp del: height_bplustree.simps dest!: mod_starD list_assn_len)[]
            done
          subgoal 
            apply(rule entailsI)
            using assms apply (auto simp del: height_bplustree.simps dest!: mod_starD list_assn_len)[]
            done
      apply(vcg)
      subgoal using assms by (auto simp del: height_bplustree.simps dest!: mod_starD list_assn_len)[]
      subgoal using assms by (auto simp del: height_bplustree.simps dest!: mod_starD list_assn_len)[]
      apply vcg
      subgoal using assms by (auto simp del: height_bplustree.simps dest!: mod_starD list_assn_len)[]
      subgoal for rsubi rsepi _ _ _ rx
        apply(subgoal_tac "rsepi = sep")
        prefer 2
        subgoal
          using assms by (auto simp del: height_bplustree.simps dest!: mod_starD list_assn_len)[]
        supply R = list_assn_append_Cons_left[where xs="[]" and x=rss and ys=rrs and zs=rsi]
        using R
       apply(auto del: impCE simp add: R)[]
          apply(simp add: prod_assn_def)
        apply(rule norm_pre_ex_rule)+
        subgoal for rrsubi rrsepi rrsi rrtsia rrtsin rrti rrtsi _ z _
          apply(rule hoare_triple_preI)
        apply(subgoal_tac "rx = z")
          prefer 2
          apply (sep_auto simp add: assms(3) list_assn_len second_last_access)
          apply(thin_tac "_\<Turnstile>_")+
          apply(auto del: impCE simp add: prod_assn_def)[]
          apply(vcg (ss))
          apply(vcg (ss))
          apply(vcg (ss))
          apply(vcg (ss))
          apply(vcg (ss))
          subgoal for rrtsia rrtti rrtsi _
            apply(cases "rrtsia")
            apply simp
            apply (sep_auto del: impCE)
             supply R = node\<^sub>i_rule_ins[where
                 k=k and
                 c="(max (2 * k) (Suc (rtsin + _)))" and
                 lsi=rtsi and li=mti and a=rsepi and rsi=rrtsi
                  and al="Suc (rtsin + _)" and ti=rrtti
              ]
       thm R
          apply(rule hoare_triple_preI)
     apply(sep_auto del: impCE heap add: R)
       subgoal by (auto del: impCE simp add: is_pfa_def dest!: list_assn_len mod_starD)
       subgoal by (auto del: impCE simp add: is_pfa_def dest!: list_assn_len mod_starD)
          apply(rule hoare_triple_preI)
     apply(sep_auto del: impCE split!: btupi.splits)
         subgoal using assms by (auto del: impCE simp add: is_pfa_def dest!: list_assn_len mod_starD)
         subgoal for _ _ _ _ a
      apply(rule hoare_triple_preI)
         apply(sep_auto del: impCE dest!: btupi_assn_T mod_starD)
         subgoal using assms apply (auto del: impCE simp add: is_pfa_def dest!: list_assn_len mod_starD)
           by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 Suc_lessI Suc_n_not_le_n add_Suc_right le_add1 length_append length_take less_add_Suc1 list.size(4) min_eq_arg(2) nat.inject)
       apply(auto del: impCE)[]
         apply(vcg)
         apply(auto del: impCE)
         apply(rule ent_ex_postI[where x="(take (Suc i) lsi @ take (Suc i - length lsi) ((rsubi, sep) # (rrsubi, rrsep) # rrsi))
         [i := (Some a, rrsep)] @
         drop (Suc (Suc i)) lsi @
         drop (Suc (Suc i) - length lsi) ((rsubi, sep) # (rrsubi, rrsep) # rrsi)"])
        apply(rule ent_ex_postI[where x="(ttsia, ttsin)"])
        apply(rule ent_ex_postI[where x="tti"])
        apply(rule ent_ex_postI[where x="ttsi"])
         using assms apply (sep_auto del: impCE dest!: list_assn_len mod_starD)
         done
     subgoal for _ _ _ _ l a r 
      apply(rule hoare_triple_preI)
       apply(auto del: impCE dest!: mod_starD)[]
         apply(sep_auto del: impCE)
         subgoal using assms by (auto dest!: list_assn_len)
         apply(sep_auto del: impCE)
         subgoal using assms by (auto dest!: list_assn_len)
         apply(vcg)
         apply (auto del: impCE dest!: btupi_assn_Up split!: prod.splits)
         apply(rule ent_ex_postI[where x="(lsi @ (Some l, a) # (Some r, rrsep) # rrsi)"])
        apply(rule ent_ex_postI[where x="(ttsia, ttsin)"])
        apply(rule ent_ex_postI[where x="tti"])
        apply(rule ent_ex_postI[where x="ttsi"])
         using assms apply (sep_auto del: impCE simp add: second_last_update list_assn_aux_append_Cons dest!: list_assn_len mod_starD )
         done
       done
     done
   done
  done
  done
qed
qed
qed
qed
qed

lemma rebalance_last_tree_rule:
  assumes "height t = height sub"
    and "ts = list@[(sub,sep)]"
  shows "<is_pfa (2*k) tsi tsia * blist_assn k ts tsi * bplustree_assn k t ti>
  rebalance_last_tree k tsia ti
  <\<lambda>r. btnode_assn k (abs_split.rebalance_last_tree k ts  t) r >\<^sub>t"
  apply(subst rebalance_last_tree_def)
  apply(rule hoare_triple_preI)
  apply(subgoal_tac "length tsi - Suc 0 = length list")
  prefer 2
  subgoal using assms by (auto dest!: mod_starD list_assn_len)[]
  apply(cases tsia)
  supply R = rebalance_middle_tree_rule[where 
    ls="list" and 
    rs="[]" and
    i="length tsi - 1", simplified]
  using assms apply(sep_auto heap add: R)
  done


partial_function (heap) del ::"nat \<Rightarrow> 'a \<Rightarrow> ('a::{default,heap,linorder,order_top}) btnode ref \<Rightarrow> 'a btnode ref Heap"
  where
    "del k x tp = do {
  ti \<leftarrow> !tp;
  (case ti of Btleaf xs \<Rightarrow> do { 
      xs' \<leftarrow> imp_del_list x xs;
      tp := (Btleaf xs');
      return tp
} |
   Btnode tsi tti \<Rightarrow> do {
   i \<leftarrow> imp_split tsi x;
   tsl \<leftarrow> pfa_length tsi;
   if i < tsl then do {
       (sub,sep) \<leftarrow> pfa_get tsi i;
       sub' \<leftarrow> del k x (the sub);
       kvs' \<leftarrow> pfa_set tsi i (Some sub',sep);
       node' \<leftarrow> rebalance_middle_tree k kvs' i tti;
       tp := node';
       return tp
   } else do {
       t' \<leftarrow> del k x tti;
       node' \<leftarrow> rebalance_last_tree k tsi t';
       tp := node';
       return tp
    }
  })
}"

lemma rebalance_middle_tree_update_rule:
  assumes "height tt = height sub"
    and "case rs of (rsub,rsep) # list \<Rightarrow> height rsub = height tt | [] \<Rightarrow> True"
    and "i = length ls"
  shows "<is_pfa (2 * k) (zs1 @ (Some x', sep) # zs2) a * bplustree_assn k sub x' *
     blist_assn k ls zs1 *
     blist_assn k rs zs2 *
     bplustree_assn k tt ti>
  rebalance_middle_tree k a i ti
   <btnode_assn k (abs_split.rebalance_middle_tree k ls sub sep rs tt)>\<^sub>t"
proof (cases a)
  case [simp]: (Pair a n)
  note R=rebalance_middle_tree_rule[of tt sub rs i ls k "zs1@(Some x', sep)#zs2" a n sep ti]
  show ?thesis
    apply(rule hoare_triple_preI)
    using R assms apply (sep_auto dest!: mod_starD list_assn_len simp add: prod_assn_def)
    using assn_times_assoc star_aci(3) by auto
qed

lemma del_rule:
  assumes "bal t" and "sorted_less (leaves t)" and "root_order k t" and "k > 0" and "Laligned t u"
  shows "<bplustree_assn k t ti>
  del k x ti
  <bplustree_assn k (abs_split.del k x t)>\<^sub>t"
  using assms
proof (induction k x t arbitrary: ti u rule: abs_split.del.induct)
case (1 k x xs ti u)
  then show ?case
    apply(subst del.simps)
    apply sep_auto
    done
next
  case (2 k x ts tt ti u)
  obtain ls rs where split_ts[simp]: "split ts x = (ls, rs)"
    by (cases "split ts x")
  obtain tss lastts_sub lastts_sep where last_ts: "ts = tss@[(lastts_sub, lastts_sep)]"
    using "2.prems"  apply auto 
    by (metis abs_split.isin.cases neq_Nil_rev_conv)
  show ?case
  proof(cases "rs")
    case Nil
    then show ?thesis
    apply(subst del.simps)
    apply sep_auto 
      subgoal  using "2.prems"(5) Laligned_sorted_separators sorted_wrt_append by blast
      apply(rule hoare_triple_preI)
      apply (sep_auto)
      subgoal using Nil by (auto simp add: split_relation_alt dest!: mod_starD list_assn_len)[]
      subgoal using Nil by  (auto simp add: split_relation_alt dest!: mod_starD list_assn_len)[]
      apply (sep_auto heap add: "2.IH"(1)[where u=u])
      subgoal using "2.prems" by (auto dest!: mod_starD)
      subgoal using "2.prems" by (auto dest!: mod_starD simp add: sorted_wrt_append)
      subgoal using "2.prems" order_impl_root_order by (auto dest!: mod_starD)
      subgoal using "2.prems" by (auto)
      subgoal using "2.prems" Lalign_Llast by auto
      subgoal for tsia tsin tti tsi i _ _ tti'
      apply(rule hoare_triple_preI)
        supply R = rebalance_last_tree_rule[where t="(abs_split.del k x tt)" and ti=tti' and ts=ts and sub=lastts_sub
and list=tss and sep=lastts_sep]
      thm R
      using last_ts apply(sep_auto heap add: R)
      subgoal using "2.prems" abs_split.del_height[of k tt x] order_impl_root_order[of k tt] by (auto dest!: mod_starD)
      subgoal by simp
      apply(rule hoare_triple_preI)
       apply (sep_auto)
      apply(cases "abs_split.rebalance_last_tree k ts (abs_split.del k x tt)")
      apply(auto simp add: split_relation_alt dest!: mod_starD list_assn_len)
      subgoal for tnode 
        apply (cases tnode; sep_auto)
        done
      subgoal for tnode 
        apply (cases tnode; sep_auto)
        done
      done
    done
  next
    case [simp]: (Cons rrs rss)
    then obtain sub sep where [simp]: "rrs = (sub, sep)"
      by (cases rrs)
    then show ?thesis
    apply(subst del.simps)
    apply sep_auto 
      subgoal using "2.prems"(5) Laligned_sorted_separators sorted_wrt_append by blast
      apply(vcg (ss))
      apply(vcg (ss))
      apply(vcg (ss))
      apply(vcg (ss))
      apply(vcg (ss))
      apply(vcg (ss))
      apply(vcg (ss))
      apply(vcg (ss))
      apply(vcg (ss))
      apply(vcg (ss))
      apply(vcg (ss))
      apply(vcg (ss))
      apply (simp split!: prod.splits)
      apply(vcg (ss))
(* i < length ls *)
      subgoal for tsia tsin tti tsi i subi sepi
      (* TODO this causes 4 subgoals *)
        apply(auto simp add: split_relation_alt list_assn_append_Cons_left;
         rule norm_pre_ex_rule; rule norm_pre_ex_rule; rule norm_pre_ex_rule;
         rule hoare_triple_preI;
          auto dest!: mod_starD)[]
      apply (auto simp add: split_relation_alt dest!: list_assn_len)[]
      subgoal for lsi rsi
        supply R = "2.IH"(2)[of ls rs rrs rss sub sep sep]
        thm R
        using split_ts apply(sep_auto heap add: R)
        subgoal using "2.prems" by auto[]
        subgoal using "2.prems"(2) sorted_leaves_induct_subtree by blast
          subgoal
            apply(subgoal_tac "order k sub") 
            subgoal using "2.prems"(4) order_impl_root_order by blast
            subgoal using "2.prems" by auto
          done
        subgoal using "2.prems"(4) by fastforce
        subgoal 
          using "2.prems" Lalign_Llast Laligned_split_left by blast
        apply(vcg (ss))
        apply(vcg (ss))
        apply(vcg (ss))
        subgoal by (auto simp add: split_relation_alt dest!: list_assn_len)
        apply(vcg (ss))
        apply(vcg (ss); simp)
          apply(cases tsi; simp)
        subgoal for subi' _ tti'
        supply R = rebalance_middle_tree_update_rule 
        thm R
(* TODO create a new heap rule, in the node_i style *)
        apply(rule hoare_triple_preI)
        apply (sep_auto heap add: R dest!: mod_starD)
        using "2.prems" abs_split.del_height[of k sub x] order_impl_root_order[of k sub] apply (auto)[]
        using "2.prems" apply (auto split!: list.splits)[]
        apply auto[]
        apply sep_auto
        subgoal for _ _ _ _ _ _ _ _ _ _ _ _ _ _ tnode''
          apply (cases "(abs_split.rebalance_middle_tree k ls (abs_split.del k x sub) sepi rss tt)"; cases tnode'')
          subgoal by sep_auto
          subgoal by sep_auto
          subgoal by sep_auto
          subgoal by sep_auto
          done
        done
      done
    done
      (* ~ i < length ls *)
      apply(rule hoare_triple_preI)
      using Cons  apply (auto simp add: split_relation_alt dest!: mod_starD list_assn_len)[]
      done
  qed
qed

definition reduce_root ::"('a::{default,heap,linorder,order_top}) btnode ref \<Rightarrow> 'a btnode ref Heap"
  where
    "reduce_root tp = do {
  ti \<leftarrow> !tp; 
  (case ti of
  Btleaf xs \<Rightarrow> return tp |
  Btnode ts t \<Rightarrow> do {
    tsl \<leftarrow> pfa_length ts;
    case tsl of 0 \<Rightarrow> return t |
    _ \<Rightarrow> return tp
})
}"

lemma reduce_root_rule:
"<bplustree_assn k t ti> reduce_root ti <bplustree_assn k (abs_split.reduce_root t)>\<^sub>t"
  apply(subst reduce_root_def)
  apply(cases t; cases ti)
  apply (sep_auto split!: nat.splits list.splits)+
  done

definition delete ::"nat \<Rightarrow> 'a \<Rightarrow> ('a::{default,heap,linorder,order_top}) btnode ref \<Rightarrow> 'a btnode ref Heap"
  where
    "delete k x ti = do {
    ti' \<leftarrow> del k x ti;
    reduce_root ti'
  }"

lemma delete_rule:
  assumes "bal t" and "root_order k t" and "k > 0" and "sorted (leaves t)" and "Laligned t u"
  shows "<bplustree_assn k t ti> delete k x ti <bplustree_assn k (abs_split.delete k x t)>\<^sub>t"
  apply(subst delete_def)
  using assms apply (sep_auto heap add: del_rule reduce_root_rule)
  done
*)

end

locale imp_split_list = abs_split_list: BPlusTree_Set.split_list split_list
  for split_list::
    "('a::{heap,default,linorder,order_top}) list \<Rightarrow> 'a
       \<Rightarrow> 'a list \<times> 'a list" +
  fixes imp_split_list:: "('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a \<Rightarrow> nat Heap"
  assumes imp_split_list_rule [sep_heap_rules]: "sorted_less xs \<Longrightarrow>
   <is_pfa c xs (a,n)> 
    imp_split_list (a,n) p 
  <\<lambda>i. 
    is_pfa c xs (a,n)
    * \<up>(split_relation xs (split_list xs p) i)>\<^sub>t"
begin

definition imp_isin_list:: "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> bool Heap"
  where "imp_isin_list x ks = do {
    i \<leftarrow> imp_split_list ks x;
    xsl \<leftarrow> pfa_length ks;
    if i \<ge> xsl then return False
    else do {
      sep \<leftarrow> pfa_get ks i;
      return (sep = x)
  }
}"

lemma imp_isin_list_rule [sep_heap_rules]:
  assumes "sorted_less ks"
  shows
   "<is_pfa c ks (a',n')> 
    imp_isin_list x (a',n') 
  <\<lambda>b. 
    is_pfa c ks (a',n')
    * \<up>(b = abs_split_list.isin_list x ks)>\<^sub>t"
proof -
  obtain ls rs where list_split: "split_list ks x = (ls, rs)"
    by (cases "split_list ks x")
  then show ?thesis
  proof (cases rs)
    case Nil
    then show ?thesis
      apply(subst imp_isin_list_def)
      using assms list_split apply(sep_auto simp add: split_relation_alt dest!: mod_starD list_assn_len)
      done
  next
  case (Cons a rrs)
  then show ?thesis
      apply(subst imp_isin_list_def)
      using list_split apply simp
      using assms list_split  apply(sep_auto simp add: split_relation_alt list_assn_append_Cons_left dest!: mod_starD list_assn_len)
      done
  qed
qed

definition imp_ins_list:: "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a pfarray Heap"
  where "imp_ins_list x ks = do {
    i \<leftarrow> imp_split_list ks x;
    xsl \<leftarrow> pfa_length ks;
    if i \<ge> xsl then
      pfa_append_grow ks x
    else do {
      sep \<leftarrow> pfa_get ks i;
      if sep = x then
        return ks
      else
        pfa_insert_grow ks i x 
  }
}"

lemma imp_ins_list_rule [sep_heap_rules]:
  assumes "sorted_less ks"
  shows
   "<is_pfa c ks (a',n')> 
    imp_ins_list x (a',n') 
  <\<lambda>(a'',n''). is_pfa (max c (length (abs_split_list.insert_list x ks))) (abs_split_list.insert_list x ks) (a'',n'')
    >\<^sub>t"
proof -
  obtain ls rs where list_split: "split_list ks x = (ls, rs)"
    by (cases "split_list ks x")
  then show ?thesis
  proof (cases rs)
    case Nil
    then show ?thesis
      apply(subst imp_ins_list_def)
      apply vcg
      subgoal using assms by auto
      apply(rule hoare_triple_preI)
      apply vcg
      using list_split apply (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
    subgoal
      apply(simp add: is_pfa_def)
        apply(rule ent_ex_preI)
      subgoal for l
        apply(rule ent_ex_postI[where x="l"])
      using assms list_split apply(sep_auto simp add: split_relation_alt pure_def dest!: mod_starD list_assn_len)
      done
    done
    subgoal
      apply(simp add: is_pfa_def)
        apply(rule ent_ex_preI)
      subgoal for l
        apply(rule ent_ex_postI[where x="l"])
      using assms list_split apply(sep_auto simp add: split_relation_alt pure_def dest!: mod_starD list_assn_len)
      done
    done
  done
  next
  case (Cons a rrs)
  then show ?thesis
  proof (cases "a = x")
    case True
    then show ?thesis
      apply(subst imp_ins_list_def)
      apply vcg
      subgoal using assms by auto
      apply(rule hoare_triple_preI)
      apply vcg
      subgoal using list_split Cons by (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      apply vcg
      subgoal using list_split Cons by (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      apply vcg
      prefer 2
      subgoal by (metis (no_types, lifting) id_assn_list list_split local.Cons mod_starD split_relation_access)
      using list_split Cons apply (auto simp add: split_relation_alt list_assn_append_Cons_left split!: prod.splits list.splits dest!: mod_starD list_assn_len)
        apply(subgoal_tac "max c (Suc (length ls + length rrs)) = c")
      subgoal using assms list_split by (sep_auto simp add: split_relation_alt  dest!: mod_starD id_assn_list)
          subgoal
            apply(auto simp add: is_pfa_def)
            by (metis add_Suc_right length_Cons length_append length_take max.absorb1 min_eq_arg(2))
      done
  next
    case False
    then show ?thesis
      apply(subst imp_ins_list_def)
      apply vcg
      subgoal using assms by auto
      apply(rule hoare_triple_preI)
      apply vcg
      subgoal using list_split Cons by (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      apply vcg
      subgoal using list_split Cons by (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      apply vcg
      subgoal by (metis (no_types, lifting) id_assn_list list_split local.Cons mod_starD split_relation_access)
      apply vcg
      subgoal by (auto simp add: is_pfa_def)
      using list_split Cons apply (auto simp add: split_relation_alt list_assn_append_Cons_left split!: prod.splits list.splits dest!: mod_starD list_assn_len)
    subgoal for _ _ _ _
        apply(subgoal_tac "(Suc (Suc (length ls + length rrs))) = Suc n'")
        subgoal
      using assms list_split Cons by (sep_auto simp add: split_relation_alt dest!: mod_starD id_assn_list)
      subgoal
        apply(auto simp add: is_pfa_def)
        by (metis add_Suc_right length_Cons length_append length_take min_eq_arg(2))
      done
    done
qed
qed
qed

definition imp_del_list:: "'a \<Rightarrow> ('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a pfarray Heap"
  where "imp_del_list x ks = do {
    i \<leftarrow> imp_split_list ks x;
    xsl \<leftarrow> pfa_length ks;
    if i \<ge> xsl then
      return ks
    else do {
      sep \<leftarrow> pfa_get ks i;
      if sep = x then
        pfa_delete ks i
      else
        return ks
  }
}"

lemma imp_del_list_rule [sep_heap_rules]:
  assumes "sorted_less ks"
  shows "<is_pfa c ks (a',n')> 
    imp_del_list x (a',n') 
  <\<lambda>(a'',n''). is_pfa c (abs_split_list.delete_list x ks) (a'',n'')>\<^sub>t"
proof -
  obtain ls rs where list_split: "split_list ks x = (ls, rs)"
    by (cases "split_list ks x")
  then show ?thesis
  proof (cases rs)
    case Nil
    then show ?thesis
      apply(subst imp_del_list_def)
      apply vcg
      subgoal using assms by auto
      apply(rule hoare_triple_preI)
      apply vcg
      using list_split apply (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      done
  next
  case (Cons a rrs)
  then show ?thesis
  proof (cases "a = x")
    case True
    then show ?thesis
      apply(subst imp_del_list_def)
      apply vcg
      subgoal using assms by auto
      apply(rule hoare_triple_preI)
      apply vcg
      subgoal using list_split Cons by (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      apply vcg
      subgoal using list_split Cons by (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      apply vcg
      subgoal using list_split Cons apply (auto simp add: split_relation_alt is_pfa_def split!: prod.splits list.splits dest!: mod_starD list_assn_len)
        by (metis add_Suc_right length_Cons length_append length_take less_add_Suc1 min_eq_arg(2))
      prefer 2
      subgoal by (smt (z3) assn_aci(10) ent_pure_pre_iff id_assn_list_alt list_split local.Cons return_cons_rule split_relation_access)
      using list_split Cons apply (auto simp add: split_relation_alt list_assn_append_Cons_left split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      done
  next
    case False
    then show ?thesis
      apply(subst imp_del_list_def)
      apply vcg
      subgoal using assms by auto
      apply(rule hoare_triple_preI)
      apply vcg
      subgoal using list_split Cons by (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      apply vcg
      subgoal using list_split Cons by (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      apply vcg
      subgoal using list_split Cons by (auto simp add: split_relation_alt is_pfa_def split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      subgoal by (smt (z3) ent_pure_pre_iff fr_refl id_assn_list_alt list_split local.Cons split_relation_access)
      apply vcg
      using list_split Cons apply (auto simp add: split_relation_alt split!: prod.splits list.splits dest!: mod_starD list_assn_len)
    done
    qed
  qed
qed

end

locale imp_split_full = imp_split_tree: imp_split_tree split + imp_split_list: imp_split_list split_list
    for split::
      "('a bplustree \<times> 'a::{linorder,heap,default,order_top}) list \<Rightarrow> 'a
         \<Rightarrow> ('a bplustree \<times> 'a) list \<times> ('a bplustree \<times> 'a) list"
    and split_list::
      "'a::{default,linorder,order_top,heap} list \<Rightarrow> 'a
         \<Rightarrow> 'a list \<times> 'a list"
begin

sublocale imp_split imp_split_list.abs_split_list.isin_list imp_split_list.abs_split_list.insert_list 
  imp_split_list.abs_split_list.delete_list split imp_split imp_split_list.imp_isin_list imp_split_list.imp_ins_list imp_split_list.imp_del_list
  using imp_split_list.abs_split_list.isin_list_set imp_split_list.abs_split_list.insert_list_set imp_split_list.abs_split_list.delete_list_set
  apply unfold_locales 
  apply sep_auto +
  done

end

end

