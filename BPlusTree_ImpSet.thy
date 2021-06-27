theory BPlusTree_ImpSet
  imports
    BPlusTree_Imp
    BPlusTree_Set
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

locale imp_split_tree = bplustree A + abs_split_tree: BPlusTree_Set.split_tree split
  for A :: "'a::{linorder,order_top} \<Rightarrow> ('b::{heap,default,linorder,order_top}) \<Rightarrow> assn"
  and split::
    "('a bplustree \<times> 'a) list \<Rightarrow> 'a
       \<Rightarrow> ('a bplustree \<times> 'a) list \<times> ('a bplustree \<times> 'a) list" +
  fixes imp_split:: "('b btnode ref option \<times> 'b::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'b \<Rightarrow> nat Heap"
  assumes imp_split_rule [sep_heap_rules]:"sorted_less (separators ts) \<Longrightarrow>
  tsi'' = zip (zip (map fst tsi') (zip (butlast (r#rs)) (butlast (rs@[z])))) (map snd tsi') \<Longrightarrow>
 <is_pfa c tsi (a,n) 
  * blist_assn k ts tsi''
  * A p pi> 
    imp_split (a,n) pi 
  <\<lambda>i. 
    is_pfa c tsi (a,n)
    * blist_assn k ts tsi''
    * A p pi
    * \<up>(split_relation ts (split ts p) i)>\<^sub>t"

text "This locale extends the abstract split locale,
assuming that we are provided with an imperative program
that refines the abstract split function."


(* TODO separate into split_tree and split + split_list  *)
locale imp_split = abs_split: BPlusTree_Set.split split + imp_split_tree A split imp_split
  for split::
    "('a bplustree \<times> 'a::{heap,default,linorder,order_top}) list \<Rightarrow> 'a
       \<Rightarrow> ('a bplustree \<times> 'a) list \<times> ('a bplustree \<times> 'a) list" 
  and imp_split :: "('b btnode ref option \<times> 'b::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'b \<Rightarrow> nat Heap"
  and A :: "'a \<Rightarrow> 'b \<Rightarrow> assn" +
  fixes imp_isin_list:: "'b \<Rightarrow> ('b::{heap,default,linorder,order_top}) pfarray \<Rightarrow> bool Heap"
    and imp_ins_list:: "'b \<Rightarrow> ('b::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'b pfarray Heap"
    and imp_del_list:: "'b \<Rightarrow> ('b::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'b pfarray Heap"
  assumes isin_list_rule [sep_heap_rules]:"sorted_less ks \<Longrightarrow>
   <is_pfa c ksi (a',n') * list_assn A ks ksi * A x xi> 
    imp_isin_list xi (a',n') 
  <\<lambda>b. 
    is_pfa c ksi (a',n') * list_assn A ks ksi
    * A x xi
    * \<up>(isin_list x ks = b)>\<^sub>t"
  and ins_list_rule [sep_heap_rules]:"sorted_less ks \<Longrightarrow>
   <is_pfa c ksi (a',n') * list_assn A ks ksi * A x xi> 
    imp_ins_list xi (a',n') 
  <\<lambda>(a'',n''). 
    \<exists>\<^sub>Aksi''. is_pfa (max c (length (insert_list x ks))) ksi'' (a'',n'') * list_assn A (insert_list x ks) ksi''
    >\<^sub>t"
  and del_list_rule [sep_heap_rules]:"sorted_less ks \<Longrightarrow>
   <is_pfa c ksi (a',n') * list_assn A ks ksi * A x xi> 
    imp_del_list xi (a',n') 
  <\<lambda>(a'',n''). 
    \<exists>\<^sub>Aksi''. is_pfa c ksi'' (a'',n'') * list_assn A (delete_list x ks) ksi'' * A x xi
    >\<^sub>t"
begin

subsection "Membership"

(* TODO introduce imperative equivalents to searching/inserting/deleting in a list *)
partial_function (heap) isin :: "'b btnode ref \<Rightarrow> 'b \<Rightarrow>  bool Heap"
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

(* TODO use, maybe with a list instead? *)
method instantiate_assn for y = 
  ((rule impI)?, rule ent_ex_postI[where x=y])

lemma  "k > 0 \<Longrightarrow> root_order k t \<Longrightarrow> sorted_less (inorder t) \<Longrightarrow> sorted_less (leaves t) \<Longrightarrow>
   <bplustree_assn k t ti r z * A x xi>
     isin ti xi
   <\<lambda>y. bplustree_assn k t ti r z * A x xi * \<up>(abs_split.isin t x = y)>\<^sub>t"
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
              (* proof that previous assumptions hold later *)
             apply(rule ent_ex_postI[where x="(tsi,n)"])
             apply(rule ent_ex_postI[where x="ti"])
             apply(rule ent_ex_postI[where x="tsi'"])
             apply(rule ent_ex_postI[where x="(zs1 @ ((suba', subp, subfwd), sepa') # zs2)"])
             apply(rule ent_ex_postI[where x="pointers"])
             apply(rule ent_ex_postI[where x="zs1"])
             apply(rule ent_ex_postI[where x="z"])
             apply(rule ent_ex_postI[where x="zs2"])
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
   (\<exists>\<^sub>A newr. bplustree_assn k l li r' newr * A a ai * bplustree_assn k r ri newr z')" |
  "btupi_assn _ _ _ _ _ = false"



definition node\<^sub>i :: "nat \<Rightarrow> ('b btnode ref option \<times> 'b) pfarray \<Rightarrow> 'b btnode ref \<Rightarrow> 'b btupi Heap" where
  "node\<^sub>i k a ti \<equiv> do {
    n \<leftarrow> pfa_length a;
    if n \<le> 2*k then do {
      a' \<leftarrow> pfa_shrink_cap (2*k) a;
      l \<leftarrow> ref (Btnode a' ti);
      return (T\<^sub>i l)
    }
    else do {
      b \<leftarrow> (pfa_empty (2*k) :: ('b btnode ref option \<times> 'b) pfarray Heap);
      i \<leftarrow> split_half a;
      m \<leftarrow> pfa_get a (i-1);
      b' \<leftarrow> pfa_drop a i b;
      a' \<leftarrow> pfa_shrink (i-1) a;
      a'' \<leftarrow> pfa_shrink_cap (2*k) a';
      let (sub,sep) = m in do {
        l \<leftarrow> ref (Btnode a'' (the sub));
        r \<leftarrow> ref (Btnode b' ti);
        return (Up\<^sub>i l sep r)
      }
    }
}"

definition Lnode\<^sub>i :: "nat \<Rightarrow> 'b pfarray  \<Rightarrow> 'b btnode ref option \<Rightarrow> 'b btupi Heap" where
  "Lnode\<^sub>i k a nxt \<equiv> do {
    n \<leftarrow> pfa_length a;
    if n \<le> 2*k then do {
      a' \<leftarrow> pfa_shrink_cap (2*k) a;
      l \<leftarrow> ref (Btleaf a' nxt);
      return (T\<^sub>i l)
    }
    else do {
      b \<leftarrow> (pfa_empty (2*k) :: 'b pfarray Heap);
      i \<leftarrow> split_half a;
      m \<leftarrow> pfa_get a (i-1);
      b' \<leftarrow> pfa_drop a i b;
      a' \<leftarrow> pfa_shrink i a;
      a'' \<leftarrow> pfa_shrink_cap (2*k) a';
      r \<leftarrow> ref (Btleaf b' nxt);
      l \<leftarrow> ref (Btleaf a'' (Some r));
      return (Up\<^sub>i l m r)
    }
}"

(* TODO Lnode\<^sub>i allocates a new node when invoked, do not invoke if array didn't grow *)
partial_function (heap) ins :: "nat \<Rightarrow> 'b \<Rightarrow> 'b btnode ref \<Rightarrow> 'b btupi Heap"
  where
    "ins k x p = do {
  node \<leftarrow> !p;
  (case node of
  Btleaf ksi nxt \<Rightarrow> do {
    ksi' \<leftarrow> imp_ins_list x ksi; 
    Lnode\<^sub>i k ksi' nxt
  } |
  Btnode tsi ti \<Rightarrow> do {
    i \<leftarrow> imp_split tsi x;
    tsl \<leftarrow> pfa_length tsi;
    if i < tsl then do {
      s \<leftarrow> pfa_get tsi i;
      let (sub,sep) = s in
      do {
        r \<leftarrow> ins k x (the sub);
        case r of 
          (T\<^sub>i lp) \<Rightarrow> do {
            pfa_set tsi i (Some lp,sep);
            return (T\<^sub>i p)
          } |
          (Up\<^sub>i lp x' rp) \<Rightarrow> do {
            pfa_set tsi i (Some rp,sep);
            if tsl < 2*k then do {
                tsi' \<leftarrow> pfa_insert tsi i (Some lp,x');
                p := (Btnode tsi' ti);
                return (T\<^sub>i p)
            } else do {
              tsi' \<leftarrow> pfa_insert_grow tsi i (Some lp,x');
              node\<^sub>i k tsi' ti
            }
          }
        }
      }
    else do {
      r \<leftarrow> ins k x ti;
      case r of 
        (T\<^sub>i lp) \<Rightarrow> do {
          p := (Btnode tsi lp);
          return (T\<^sub>i p)
        } |
        (Up\<^sub>i lp x' rp) \<Rightarrow> 
          if tsl < 2*k then do {
            tsi' \<leftarrow> pfa_append tsi (Some lp,x');
            p := (Btnode tsi' rp);
            return (T\<^sub>i p)
          } else do {
            tsi' \<leftarrow> pfa_append_grow' tsi (Some lp,x');
            node\<^sub>i k tsi' rp
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

definition insert :: "nat \<Rightarrow> 'b \<Rightarrow> 'b btnode ref \<Rightarrow> 'b btnode ref Heap" where
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

value "butlast (take 1 [1,2::nat])"
value "take 1 (butlast [1,2::nat])"

lemma take_butlast_prepend: "take n (butlast (r # pointers)) =
       butlast (r # take n pointers)"
  apply(cases pointers)
  apply auto[]
  by (smt (verit, del_insts) One_nat_def Suc_to_right length_Cons length_butlast length_take min_eq_arg(2) nat_le_linear take_Suc_Cons take_butlast_conv take_take)


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

lemma entails_preI: "(\<And>h. h \<Turnstile> P \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q) \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q"
  unfolding entails_def
  by auto


declare abs_split.node\<^sub>i.simps [simp add]
lemma node\<^sub>i_rule: assumes c_cap: "2*k \<le> c" "c \<le> 4*k+1"
    and "length tsi' = length pointers"
    and "tsi'' = zip (zip (map fst tsi') (zip (butlast (r#pointers)) (butlast (pointers@[z])))) (map snd tsi')"
  shows "<is_pfa c tsi' (a,n) * blist_assn k ts tsi'' * bplustree_assn k t ti (List.last (r#pointers)) z>
  node\<^sub>i k (a,n) ti
  <\<lambda>u. btupi_assn k (abs_split.node\<^sub>i k ts t) u r z>\<^sub>t"
proof (cases "length ts \<le> 2*k")
  case [simp]: True
  then show ?thesis
    apply(subst node\<^sub>i_def)
    apply(rule hoare_triple_preI)
    apply(sep_auto simp del: List.last.simps)
    subgoal by (sep_auto simp add: is_pfa_def)[]
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    subgoal using assms(3,4) by sep_auto
    subgoal 
      apply(subgoal_tac "length ts = length tsi'")
    subgoal using True by (sep_auto simp del: List.last.simps)
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
    apply(sep_auto simp del: List.last.simps)
    subgoal by (sep_auto simp add:  split_relation_alt split_relation_length is_pfa_def dest!: mod_starD list_assn_len)
    subgoal using assms by (sep_auto dest!: mod_starD list_assn_len)
    subgoal
      apply(subgoal_tac "length ts = length tsi'")
      subgoal using False by (sep_auto dest!: mod_starD list_assn_len)
      subgoal using assms(3,4) by (sep_auto dest!: mod_starD list_assn_len)
      done
    apply(sep_auto simp del: List.last.simps)[]
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    using c_cap apply(sep_auto simp del: List.last.simps)[]
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    using c_cap apply(simp del: List.last.simps)
    apply(rule hoare_triple_preI)
    apply(vcg)
    apply(simp add: split_relation_alt del: List.last.simps butlast.simps)
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
          simp add: list_assn_prod_map id_assn_list_alt
          simp del: List.last.simps butlast.simps)[]
          apply (metis One_nat_def Suc_eq_plus1 length_Cons length_append length_take list.size(3) min_less_self_conv(2) not_less_eq trans_less_add1)
          done
     supply R=list_assn_append_Cons_left[where xs="take (length ls) ts" and ys="drop (Suc (length ls)) ts" and x="ts ! (length ls)"]
      thm R
      apply(subst R)
      apply (auto
          simp del: List.last.simps butlast.simps)[]
      apply(rule ent_ex_preI)+
      apply(subst ent_pure_pre_iff; rule impI)
      apply (simp add: prod_assn_def split!: prod.splits del: List.last.simps butlast.simps)
      subgoal for tsi''l subi'' subir subinext sepi'' tsi''r sub' sep'
        (* instantiate right hand side *)
(* newr is the first leaf of the tree directly behind sub
  and (r#pointers) is the list of all first leafs of the tree in this node
   \<rightarrow> the pointer at position of sub in pointers
      or the pointer at position of sub+1 in (r#pointers)
*)
      (* Suc (length tsi') div 2 - Suc 0) = length ls *)
      apply(rule ent_ex_postI[where x="subinext"])
      apply(rule ent_ex_postI[where x="(rsia,rsin)"])
      apply(rule ent_ex_postI[where x="ti"])
      apply(rule ent_ex_postI[where x="drop (length ls+1) tsi'"])
      apply(rule ent_ex_postI[where x="drop (length ls+1) tsi''"])
      apply(rule ent_ex_postI[where x="drop (length ls+1) pointers"])
      apply(rule ent_ex_postI[where x="lsi"])
      apply(rule ent_ex_postI[where x="the subi'"])
      apply(rule ent_ex_postI[where x="take (length ls) tsi'"])
      apply(rule ent_ex_postI[where x="take (length ls) tsi''"])
      apply(rule ent_ex_postI[where x="take (length ls) pointers"])
      apply (sep_auto simp del: List.last.simps butlast.simps)
      subgoal using assms(3) by linarith
      subgoal 
        using assms(3,4) by (auto dest!: mod_starD 
          simp add: take_map[symmetric] take_zip[symmetric] take_butlast_prepend[symmetric]
          simp del: List.last.simps butlast.simps
      )
         subgoal using assms(3,4) by (auto dest!: mod_starD      
          simp add: list_assn_prod_map id_assn_list_alt
          simp del: List.last.simps butlast.simps)
         subgoal 
           apply(subgoal_tac "length ls < length pointers")
           apply(subgoal_tac "subinext = pointers ! (length ls)")
           subgoal
        using assms(3,4) apply (auto 
          simp add: drop_map[symmetric] drop_zip[symmetric] drop_butlast[symmetric] Cons_nth_drop_Suc
          simp del: List.last.simps butlast.simps
      )[]
           supply R = drop_Suc_Cons[where n="length ls" and xs="butlast pointers" and x=r, symmetric]
           thm R
           apply(simp only: R drop_zip[symmetric])
           apply simp
           done
        subgoal apply(auto dest!: mod_starD  list_assn_len     
          simp del: List.last.simps butlast.simps)[]
        proof (goal_cases)
        case 1
        have "length ls < length tsi''"
          using assms(3,4) "1"(11) by auto
        moreover have "subinext = snd (snd (fst (tsi'' ! length ls)))"
          using "1"(24) "1"(9) calculation by force
        ultimately have "subinext = map snd (map snd (map fst tsi'')) ! length ls"
          by auto
        then show ?case
          using assms(3,4) by auto
      qed
          subgoal apply(auto dest!: mod_starD  list_assn_len     
          simp del: List.last.simps butlast.simps)[]
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
        apply(auto dest!: mod_starD  list_assn_len     
        simp del: List.last.simps butlast.simps)[]
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
        prefer 2 subgoal using assms(3,4) by (auto dest!: mod_starD  list_assn_len     
        simp del: List.last.simps butlast.simps)[]
    apply(subgoal_tac "(sub', sep') = (sub, sep)")
        prefer 2 subgoal
        by (metis One_nat_def Suc_eq_plus1 Suc_length_conv abs_split.length_take_left length_0_conv length_append less_add_Suc1 nat_arith.suc1 nth_append_length nth_take)
      apply(subgoal_tac "length ls = length tsi''l")
        prefer 2 subgoal by (auto dest!: mod_starD list_assn_len
          simp del: List.last.simps butlast.simps)
    apply(subgoal_tac "(subi'', sepi'') = (subi', sepi')")
      prefer 2 subgoal
        using assms(3,4) apply (auto dest!: mod_starD list_assn_len
          simp del: List.last.simps butlast.simps)
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
    apply(subgoal_tac "(List.last (r # take (length ls) pointers)) = subir")
      prefer 2 subgoal
        using assms(3) apply (auto dest!: mod_starD list_assn_len
          simp del: List.last.simps butlast.simps)
      proof (goal_cases)
        case 1
        have "length tsi''l < length tsi''"
          by (simp add: 1)
        then have "fst (snd (fst (tsi'' ! length tsi''l))) = subir"
          using 1 assms(4) by auto
        moreover have "map fst (map snd (map fst tsi'')) = butlast (r#pointers)"
          using assms(3,4) by auto
        moreover have "(List.last (r#take (length ls) pointers)) = butlast (r#pointers) ! (length tsi''l)"
          by (smt (z3) "1"(10) "1"(11) One_nat_def Suc_eq_plus1 Suc_to_right abs_split.length_take_left append_butlast_last_id div_le_dividend le_add2 length_butlast length_ge_1_conv length_take lessI list.size(4) min_eq_arg(2) nth_append_length nth_take nz_le_conv_less take_Suc_Cons take_butlast_conv)
        ultimately show ?case
          using 1 apply auto
          by (metis (no_types, hide_lams) "1"(11) length_map map_map nth_append_length)
      qed
    apply(subgoal_tac "(List.last (subinext # drop (Suc (length tsi''l)) pointers)) = List.last (r#pointers)")
       prefer 2 subgoal
        using assms(3) apply (auto dest!: mod_starD list_assn_len
          simp del: List.last.simps butlast.simps)
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
        moreover have "List.last (drop (length tsi''l) pointers) = List.last pointers"
          using \<open>length tsi''l < length tsi''\<close>  1 by force
        ultimately show ?case
          by auto
      qed
    apply(subgoal_tac "take (length tsi''l) ts = ls")
      prefer 2 subgoal
        by (metis append.assoc append_eq_conv_conj append_take_drop_id)
    apply(subgoal_tac "drop (Suc (length tsi''l)) ts = rs")
      prefer 2 subgoal by (metis One_nat_def Suc_eq_plus1 Suc_length_conv append_eq_conv_conj append_take_drop_id length_0_conv length_append)
    subgoal by (sep_auto
          simp del: List.last.simps butlast.simps)
    done
  done
  done
qed
declare abs_split.node\<^sub>i.simps [simp del]

declare abs_split.Lnode\<^sub>i.simps [simp add]
lemma Lnode\<^sub>i_rule: assumes c_cap: "2*k \<le> c" "c \<le> 4*k"
  shows "<is_pfa c tsi (a,n) * list_assn id_assn ts tsi>
  Lnode\<^sub>i k (a,n)
  <\<lambda>r. btupi_assn k (abs_split.Lnode\<^sub>i k ts) r >\<^sub>t"
proof (cases "length ts \<le> 2*k")
  case [simp]: True
  then show ?thesis
    apply(subst Lnode\<^sub>i_def)
    apply(rule hoare_triple_preI)
    apply(sep_auto dest!: mod_starD list_assn_len)
    subgoal by (sep_auto simp add: is_pfa_def)[]
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
     subgoal by (sep_auto  dest!: mod_starD list_assn_len)[]
    subgoal using True by (sep_auto dest!: mod_starD list_assn_len)
    done
next
  case [simp]: False
  then obtain ls sep rs where
    split_half_eq: "BPlusTree_Set.split_half ts = (ls@[sep],rs)"
    using abs_split.Lnode\<^sub>i_cases by blast
  then show ?thesis
    apply(subst Lnode\<^sub>i_def)
    apply(rule hoare_triple_preI)
    apply(sep_auto dest!: mod_starD list_assn_len)
    subgoal by (sep_auto simp add:  split_relation_alt split_relation_length is_pfa_def dest!: mod_starD list_assn_len)

    subgoal using False by (sep_auto simp add: split_relation_alt )
    subgoal using False by (sep_auto simp add: is_pfa_def)[]
    apply(sep_auto)[]
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    using c_cap apply(sep_auto)[]
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    subgoal using c_cap by (sep_auto simp add: is_pfa_def)[]
    using c_cap apply(simp)
    apply(vcg)
    apply(simp add: split_relation_alt)
    apply(rule impI)
    subgoal for  _ _ rsa rn lsi al ar a
        (* instantiate right hand side *)
      apply(rule ent_ex_postI[where x="(rsa,rn)"])
      apply(rule ent_ex_postI[where x="(drop (Suc (length ls)) tsi)"])
      apply(rule ent_ex_postI[where x="lsi"])
      apply(rule ent_ex_postI[where x="take (Suc (length ls)) tsi"])
        (* introduce equality between equality of split tsi/ts and original lists *)
      apply (sep_auto dest!: mod_starD)
      subgoal by (metis (no_types, lifting) id_assn_list nth_append_length)
      apply(subgoal_tac "take (length ls) ts = ls")
      prefer 2
      subgoal by (metis append_eq_conv_conj)
      apply(subgoal_tac "tsi =
            take (Suc (length ls)) tsi @  drop (Suc (length ls)) tsi")
       apply(rule back_subst[where a="list_assn id_assn ts (take (Suc (length ls)) tsi @ (drop (Suc (length ls)) tsi))" and b="list_assn id_assn ts tsi"])
        apply(rule back_subst[where a="list_assn id_assn (take (Suc (length ls)) ts @ rs)" and b="list_assn id_assn ts"])
         apply(subst list_assn_aux_append)
      subgoal by auto
      subgoal by sep_auto 
      subgoal by sep_auto
      subgoal by sep_auto
      subgoal by sep_auto
      done
    done
qed
declare abs_split.Lnode\<^sub>i.simps [simp del]

lemma node\<^sub>i_no_split: "length ts \<le> 2*k \<Longrightarrow> abs_split.node\<^sub>i k ts t = abs_split.T\<^sub>i (Node ts t)"
  by (simp add: abs_split.node\<^sub>i.simps)

lemma Lnode\<^sub>i_no_split: "length ts \<le> 2*k \<Longrightarrow> abs_split.Lnode\<^sub>i k ts = abs_split.T\<^sub>i (LNode ts)"
  by (simp add: abs_split.Lnode\<^sub>i.simps)

lemma id_assn_emp[simp]: "id_assn a a = emp"
  by (simp add: pure_def)

lemma node\<^sub>i_rule_app: "\<lbrakk>2*k \<le> c; c \<le> 4*k+1\<rbrakk> \<Longrightarrow>
<is_pfa c (tsi' @ [(Some li, a)]) (aa, al) *
   blist_assn k ls tsi' *
   bplustree_assn k l li *
   bplustree_assn k r ri> node\<^sub>i k (aa, al) ri
 <btupi_assn k (abs_split.node\<^sub>i k (ls @ [(l, a)]) r)>\<^sub>t"
proof -
  note node\<^sub>i_rule[of k c "(tsi' @ [(Some li, a)])" aa al "(ls @ [(l, a)])" r ri]
  moreover assume "2*k \<le> c" "c \<le> 4*k+1"
  ultimately show ?thesis
    by (simp add: mult.left_assoc)
qed

lemma node\<^sub>i_rule_ins2: "\<lbrakk>2*k \<le> c; c \<le> 4*k+1; length ls = length lsi\<rbrakk> \<Longrightarrow>
 <is_pfa c (lsi @ (Some li, a) # (Some ri,a') # rsi) (aa, al) *
   blist_assn k ls lsi *
   bplustree_assn k l li *
   bplustree_assn k r ri *
   blist_assn k rs rsi *
   bplustree_assn k t ti> node\<^sub>i k (aa, al)
          ti <btupi_assn k (abs_split.node\<^sub>i k (ls @ (l, a) # (r,a') # rs) t)>\<^sub>t"
proof -
  assume [simp]: "2*k \<le> c" "c \<le> 4*k+1" "length ls = length lsi"
  moreover note node\<^sub>i_rule[of k c "(lsi @ (Some li, a) # (Some ri,a') # rsi)" aa al "(ls @ (l, a) # (r,a') # rs)" t ti]
  ultimately show ?thesis
    by (simp add: mult.left_assoc list_assn_aux_append_Cons)
qed


lemma ins_rule:
  "k > 0 \<Longrightarrow>
  sorted_less (inorder t) \<Longrightarrow>
  sorted_less (leaves t) \<Longrightarrow>
  root_order k t \<Longrightarrow>
  <bplustree_assn k t ti>
  ins k x ti
  <\<lambda>r. btupi_assn k (abs_split.ins k x t) r>\<^sub>t"
proof (induction k x t arbitrary: ti rule: abs_split.ins.induct)
  case (1 k x)
  then show ?case
    apply(subst ins.simps)
    apply (sep_auto simp add: pure_app_eq heap: Lnode\<^sub>i_rule)
    done
next
  case (2 k x ts t)
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
        apply simp
        apply vcg
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
        using Nil split_rel_i list_split
        apply (sep_auto dest!: split_rel_i mod_starD)
        subgoal for tsil tsin tti
          using Nil list_split
          by (simp add: list_assn_aux_ineq_len split_relation_alt)                 
        subgoal for tsil tsin tti tsi' i tsin' _ sub sep
          using Nil list_split 
          by (simp add: list_assn_aux_ineq_len split_relation_alt)
        subgoal for tsil tsin tti tsi' i tsin'
          thm "2.IH"(1)[of ls rrs tti]
          using "2.prems" sorted_leaves_induct_last
          using  Nil list_split Up\<^sub>i abs_split.split_conc[OF list_split] order_impl_root_order
          apply(sep_auto split!: list.splits 
              simp add: split_relation_alt
              heap add: "2.IH"(1)[of ls rrs tti])
          subgoal for ai
            apply(cases ai)
            subgoal by sep_auto
            apply(rule hoare_triple_preI)
            apply(sep_auto)
            subgoal by (auto dest!: mod_starD simp add: is_pfa_def)[]
             apply (sep_auto)
            subgoal for li ri (* no split case *)
              apply(subgoal_tac "length (ls @ [(l,a)]) \<le> 2*k")
               apply(simp add: node\<^sub>i_no_split)
               apply(rule ent_ex_postI[where x="(tsil,Suc tsin)"])
               apply(rule ent_ex_postI[where x="ri"])
               apply(rule ent_ex_postI[where x="tsi' @ [(Some li, a)]"])
              subgoal by (sep_auto)
              subgoal by (sep_auto dest!: mod_starD list_assn_len simp add: is_pfa_def)
              done
                (* split case*)
            subgoal by (sep_auto heap add: node\<^sub>i_rule_app)
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
    then show ?thesis
      proof (cases "abs_split.ins k x sub")
        case (T\<^sub>i a')
        then show ?thesis
          apply(auto simp add: Cons list_split a_split)
          apply(subst ins.simps)
          apply vcg
           apply auto
            (* at this point, we want to introduce the split, and after that tease the
  hoare triple assumptions out of the bracket, s.t. we don't split twice *)
          apply vcg
          subgoal by sep_auto
          using list_split Cons
          apply (simp add: split_relation_alt list_assn_append_Cons_left)
          apply (rule impI)
          apply(rule norm_pre_ex_rule)+
          apply(rule hoare_triple_preI)
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
          apply (simp add: prod_assn_def split!: prod.splits)
              (* actual induction branch *)
          subgoal for tsil tsin ti zs1 subi sepi zs2 _ _ suba sepa
            apply (cases a, simp)
            apply(subgoal_tac "subi = suba", simp)
          thm "2.IH"(2)[of ls rs a rrs sub sep]
            using list_split a_split T\<^sub>i 
             apply (vcg heap: "2.IH"(2))
            using "2.prems" sorted_leaves_induct_subtree \<open>sorted_less (inorder sub)\<close>
                apply(auto split!: btupi.splits) 
            subgoal using "2.prems"(1) order_impl_root_order by blast
              (* careful progression for manual value insertion *)
             apply vcg
            subgoal by simp
             apply vcg
             apply simp
            subgoal for a'i q r
              apply (rule impI)
              apply (simp add: list_assn_append_Cons_left)
              apply (rule ent_ex_postI[where x="(tsil,tsin)"])
              apply (rule ent_ex_postI[where x="ti"])
              apply (rule ent_ex_postI[where x="(zs1 @ (Some a'i, sepi) # zs2)"])
              apply (rule ent_ex_postI[where x="zs1"])
              apply (rule ent_ex_postI[where x="(Some a'i,sepi)"])
              apply (rule ent_ex_postI[where x="zs2"])
              apply sep_auto
               apply (simp add: pure_app_eq)
              apply (sep_auto dest!:  mod_starD list_assn_len)[]
              done
            subgoal by (auto dest!: mod_starD list_assn_len)
            done
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ 
            by (auto dest!:  mod_starD list_assn_len)[]
          done
      next
        case (Up\<^sub>i l w r)
        then show ?thesis
          apply (auto simp add: Cons list_split a_split)
          apply (subst ins.simps)
          apply vcg
           apply auto
            (* at this point, we want to introduce the split, and after that tease the
  hoare triple assumptions out of the bracket, s.t. we don't split twice *)
          apply vcg
          subgoal by sep_auto
          using list_split Cons
          apply (simp add: split_relation_alt list_assn_append_Cons_left)
          apply (rule impI)
          apply (rule norm_pre_ex_rule)+
          apply (rule hoare_triple_preI)
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
          apply (simp add: prod_assn_def split!: prod.splits)
              (* actual induction branch *)
          subgoal for tsil tsin ti zs1 subi sepi zs2 _ _ suba sepa
            apply(subgoal_tac "subi = suba", simp)
            thm 2(2)[of ls rrs a rs sub sep]
            using list_split a_split Cons Up\<^sub>i
             apply (sep_auto heap: 2(2))
            using "2.prems" sorted_leaves_induct_subtree \<open>sorted_less (inorder sub)\<close>
                apply(auto split!: btupi.splits) 
            using "2.prems"(1) order_impl_root_order apply blast
              (* careful progression for manual value insertion *)
              apply vcg
               apply simp
            subgoal for li ri u (* no split case *)
              apply (cases u,simp)
              apply (sep_auto dest!: mod_starD list_assn_len heap: pfa_insert_grow_rule)
              subgoal
                apply (simp add: is_pfa_def)
                apply (metis le_less_linear length_append length_take less_not_refl min.absorb2 trans_less_add1)
                done
              subgoal
               apply (simp add: is_pfa_def)
               apply (metis add_Suc_right length_Cons length_append length_take min.absorb2)
                done
              apply(sep_auto split: prod.splits  dest!: mod_starD list_assn_len)[]
                (* no split case *)
              apply(subgoal_tac "length (ls @ [(l,w)]) \<le> 2*k")
              subgoal 
                 apply(simp add: node\<^sub>i_no_split)
                 apply(rule ent_ex_postI[where x="(tsil,Suc tsin)"])
                 apply(rule ent_ex_postI[where x="ti"])
                 apply(rule ent_ex_postI[where x="(zs1 @ (Some li, w) # (Some ri, sep) # zs2)"])
                 apply(sep_auto dest!: mod_starD list_assn_len)
                done
              subgoal by (sep_auto dest!: mod_starD list_assn_len simp add: is_pfa_def)
              done
             apply vcg
            subgoal by simp
            subgoal for x21 x23 u (* split case *)
              apply (cases u,simp)
              thm pfa_insert_grow_rule[where ?l="((zs1 @ (suba, sepi) # zs2)[length ls := (Some x23, sepa)])"]
              apply (sep_auto dest!: mod_starD list_assn_len heap: pfa_insert_grow_rule)
              subgoal
               apply (simp add: is_pfa_def)
               apply (metis le_less_linear length_append length_take less_not_refl min.absorb2 trans_less_add1)
                done
              apply(auto split: prod.splits  dest!: mod_starD list_assn_len)[]

              apply (vcg heap: node\<^sub>i_rule_ins2)
              subgoal by simp
              subgoal by simp
              subgoal by simp
              subgoal by sep_auto
              done
            subgoal by (auto dest!:  mod_starD list_assn_len)
            done
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ 
            by (auto dest!:  mod_starD list_assn_len)
          done
      qed
    qed
  qed

text "The imperative insert refines the abstract insert."

lemma insert_rule:
  assumes "k > 0" "sorted_less (inorder t)" "sorted_less (leaves t)" "root_order k t"
  shows "<bplustree_assn k t ti>
  insert k x ti
  <\<lambda>r. bplustree_assn k (abs_split.insert k x t) r>\<^sub>t"
  unfolding insert_def
  apply(cases "abs_split.ins k x t")
  subgoal  using assms
    by (sep_auto split!: btupi.splits heap: ins_rule)
  using assms
  apply(vcg heap: ins_rule)
  apply(simp split!: btupi.splits)
   apply auto[]
  apply vcg
  subgoal by auto
  apply vcg
  subgoal for l r li a ri tsi
    apply(rule ent_ex_postI[where x="tsi"])
    apply(rule ent_ex_postI[where x="ri"])
    apply(rule ent_ex_postI[where x="[(Some li, a)]"])
    apply sep_auto
    done
  done

text "The \"pure\" resulting rule follows automatically."
lemma insert_rule':
  shows "<bplustree_assn (Suc k) t ti * \<up>(abs_split.invar_leaves (Suc k) t \<and> sorted_less (leaves t))>
  insert (Suc k) x ti
  <\<lambda>ri.\<exists>\<^sub>Ar. bplustree_assn (Suc k) r ri * \<up>(abs_split.invar_leaves (Suc k) r \<and> sorted_less (leaves r) \<and> leaves r = (ins_list x (leaves t)))>\<^sub>t"
  using Laligned_sorted_inorder[of t top] sorted_wrt_append
  using abs_split.insert_bal[of t] abs_split.insert_order[of "Suc k" t]
  using abs_split.insert_Linorder_top[of "Suc k" t]
  by (sep_auto heap: insert_rule simp add: sorted_ins_list)

subsection "Deletion"


(* rebalance middle tree gets a list of trees, an index pointing to
the position of sub/sep and a last tree *)
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
          mts' \<leftarrow> pfa_append_extend_grow (kvs subi) (Some (last subi),sep) (ttsi);
          res_node\<^sub>i \<leftarrow> node\<^sub>i k mts' (last ti);
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
          mts' \<leftarrow> pfa_append_extend_grow (kvs subi) (Some (last subi),sep) (kvs rsub);
          res_node\<^sub>i \<leftarrow> node\<^sub>i k mts' (last rsub);
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

definition empty ::"nat \<Rightarrow> ('a::{default,heap,linorder,order_top}) btnode ref Heap"
  where "empty k = do {
  empty_list \<leftarrow> pfa_empty (2*k);
  empty_leaf \<leftarrow> ref (Btleaf empty_list);
  return empty_leaf
}"


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
      case List.last ls of (sub,sep) \<Rightarrow>
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
      case List.last ls of sep \<Rightarrow>
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

lemma empty_rule:
  shows "<emp>
  empty k
  <\<lambda>r. bplustree_assn k (abs_split.empty_bplustree) r>"
  apply(subst empty_def)
  apply(sep_auto simp add: abs_split.empty_bplustree_def)
  done

end

locale imp_split_list = abs_split_list: BPlusTree_Set.split_list split_list
  for split_list::
    "('a::{heap,default,linorder,order_top}) list \<Rightarrow> 'a
       \<Rightarrow> 'a list \<times> 'a list" +
  fixes imp_split_list:: "('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a \<Rightarrow> nat Heap"
  assumes imp_split_list_rule [sep_heap_rules]: "sorted_less xs \<Longrightarrow>
   <is_pfa c xsi (a,n)
  * list_assn (id_assn) xs xsi> 
    imp_split_list (a,n) p 
  <\<lambda>i. 
    is_pfa c xsi (a,n)
    * list_assn (id_assn) xs xsi
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
   "<is_pfa c ksi (a',n') * list_assn (id_assn) ks ksi> 
    imp_isin_list x (a',n') 
  <\<lambda>b. 
    is_pfa c ksi (a',n') * list_assn (id_assn) ks ksi
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
   "<is_pfa c ksi (a',n') * list_assn (id_assn) ks ksi> 
    imp_ins_list x (a',n') 
  <\<lambda>(a'',n''). 
    \<exists>\<^sub>Aksi''. is_pfa (max c (length (abs_split_list.insert_list x ks))) ksi'' (a'',n'')
           * list_assn (id_assn) (abs_split_list.insert_list x ks) ksi''
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
        apply(rule ent_ex_postI[where x="ksi@[x]"])
      apply(simp add: is_pfa_def)
        apply(rule ent_ex_preI)
      subgoal for l
        apply(rule ent_ex_postI[where x="l"])
      using assms list_split apply(sep_auto simp add: split_relation_alt pure_def dest!: mod_starD list_assn_len)
      done
    done
    subgoal
        apply(rule ent_ex_postI[where x="ksi@[x]"])
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
    subgoal for _ _ lsi rsi
        apply(rule ent_ex_postI[where x="lsi@a#rsi"])
        apply(rule ent_ex_preI)+
      subgoal for lsi' ai' rsi'
        apply(rule ent_ex_postI[where x="lsi'"])
        apply(rule ent_ex_postI[where x="ai'"])
        apply(rule ent_ex_postI[where x="rsi'"])
        apply(subgoal_tac "max c (Suc (length lsi + length rsi)) = c")
      subgoal using assms list_split by (sep_auto simp add: split_relation_alt  dest!: mod_starD id_assn_list)
          subgoal
            apply(auto simp add: is_pfa_def)
            by (metis add_Suc_right length_Cons length_append length_take max.absorb1 min_eq_arg(2))
      done
    done
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
    subgoal for lsi rsi
        apply(rule ent_ex_postI[where x="lsi@x#a#rsi"])
        apply(rule ent_ex_preI)+
      subgoal for lsi' ai rsi'
        apply(rule ent_ex_postI[where x="lsi'"])
        apply(rule ent_ex_postI[where x="x"])
        apply(rule ent_ex_postI[where x="ai#rsi'"])
        apply(subgoal_tac "(Suc (Suc (length lsi + length rsi))) = Suc n'")
        subgoal
      using assms list_split Cons apply(sep_auto simp add: split_relation_alt dest!: mod_starD id_assn_list)
      apply(sep_auto simp add: pure_def)
      done
      subgoal
        apply(auto simp add: is_pfa_def)
        by (metis add_Suc_right length_Cons length_append length_take min_eq_arg(2))
      done
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
  shows "<is_pfa c ksi (a',n') * list_assn (id_assn) ks ksi> 
    imp_del_list x (a',n') 
  <\<lambda>(a'',n''). 
    \<exists>\<^sub>Aksi''. is_pfa c ksi'' (a'',n'') * list_assn (id_assn) (abs_split_list.delete_list x ks) ksi''
    >\<^sub>t"
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
      subgoal using list_split Cons by (auto simp add: split_relation_alt is_pfa_def split!: prod.splits list.splits dest!: mod_starD list_assn_len)
      prefer 2
      subgoal by (smt (z3) assn_aci(10) ent_pure_pre_iff id_assn_list_alt list_split local.Cons return_cons_rule split_relation_access)
      using list_split Cons apply (auto simp add: split_relation_alt list_assn_append_Cons_left split!: prod.splits list.splits dest!: mod_starD list_assn_len)
    subgoal for lsi rsi
        apply(rule ent_ex_postI[where x="lsi@rsi"])
      subgoal using assms list_split apply (sep_auto simp add: split_relation_alt id_assn_list_alt  dest!: mod_starD)
      done
    done
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
      apply vcg
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

