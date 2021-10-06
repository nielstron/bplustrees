theory Ramify
  imports
    Basic_Assn
    "HOL-Real_Asymp.Inst_Existentials"
begin

(* Introducing overlapping conjunction *)

fun overlap_assn_raw :: "assn_raw \<Rightarrow> assn_raw \<Rightarrow> assn_raw" where
  "overlap_assn_raw P Q (h,as) 
  = (\<exists>as1 as2 as3. as=as1\<union>as2\<union>as3 \<and> as1 \<inter> as2 = {} \<and> as2 \<inter> as3 = {} \<and> as1 \<inter> as3 = {}
      \<and> P (h,as1\<union>as3) \<and> Q (h,as2\<union>as3))"

lemma overlap_assn_proper[intro!,simp]: 
  "proper P \<Longrightarrow> proper Q \<Longrightarrow> proper (overlap_assn_raw P Q)"
  apply (rule properI)
  subgoal
    apply (auto dest: properD1) []
    apply (meson in_range_dist_union properD1)+
    done
  subgoal
    apply clarsimp
    by (metis proper_def relH_dist_union relH_in_rangeI(2))
  done

definition overlap_assn (infixl "\<uplus>" 70) where "P \<uplus> Q \<equiv> 
  Abs_assn (overlap_assn_raw (Rep_assn P) (Rep_assn Q))" 

lemma mod_overlap_conv: "h\<Turnstile>A \<uplus> B 
  \<longleftrightarrow> (\<exists>hr as1 as2 as3. h=(hr,as1\<union>as2\<union>as3) \<and> as1 \<inter> as2 = {} \<and> as2 \<inter> as3 = {} \<and> as1 \<inter> as3 = {} \<and> (hr,as1\<union>as3)\<Turnstile>A \<and> (hr,as2\<union>as3)\<Turnstile>B)"
  unfolding overlap_assn_def
  apply (cases h)
  by (auto simp: Abs_assn_inverse)

lemma overlap_emp[simp]: "P \<uplus> emp = P"
  apply(intro ent_iffI)
  subgoal by (clarsimp simp add: entails_def mod_overlap_conv mod_emp)
  subgoal by (clarsimp simp add: entails_def mod_overlap_conv mod_emp)
  done

lemma and_ent_overlap: "P \<and>\<^sub>A Q \<Longrightarrow>\<^sub>A P \<uplus> Q"
  apply (clarsimp simp add: entails_def mod_overlap_conv mod_and_dist)
  subgoal for a b
    apply(inst_existentials "{}:: nat set" "{}::nat set" b)
    apply simp_all
    done
  done

lemma star_ent_overlap: "P * Q \<Longrightarrow>\<^sub>A P \<uplus> Q"
  apply (clarsimp simp add: entails_def mod_overlap_conv mod_star_conv)
  subgoal for a b1 b2
    apply(inst_existentials b1 b2 "{}::nat set")
    apply simp_all
    done
  done

lemma overlap_discard: "P \<uplus> Q \<Longrightarrow>\<^sub>A P * true"
  apply (clarsimp simp add: entails_def mod_overlap_conv mod_star_conv)
  subgoal for a b1 b2 b3
    apply(inst_existentials "b1\<union>b3" b2)
    subgoal by blast
    subgoal by blast
    subgoal by simp
    subgoal by (meson in_range_dist_union models_in_range)
    done
  done

lemma overlap_comm: "P \<uplus> Q = Q \<uplus> P"
  apply(rule ent_iffI; clarsimp simp add: entails_def mod_overlap_conv mod_star_conv)
  subgoal for a b1 b2 b3
    apply(inst_existentials b2 b1 b3)
    apply blast+
    done
  subgoal for a b1 b2 b3
    apply(inst_existentials b2 b1 b3)
    apply blast+
    done
  done

lemma cross_split: "\<lbrakk>a \<union> b = z; c \<union> d = z; a \<inter> b = {}; c \<inter> d = {}\<rbrakk> \<Longrightarrow> (\<exists>ac ad bc bd.
ac \<union> ad = a \<and> bc \<union> bd = b \<and> ac \<union> bc = c \<and> ad \<union> bd = d \<and>
ac \<inter> ad = {} \<and> bc \<inter> bd = {} \<and> ac \<inter> bc = {} \<and> ad \<inter> bd = {} \<and>
ac \<inter> bd = {} \<and> ad \<inter> bc = {})"
proof(goal_cases)
  case 1
  then show ?case 
    apply(inst_existentials "a-d" "a-c" "b-d" "b-c")
    apply blast+
    done
qed

lemma overlap_assoc: "R \<uplus> (P \<uplus> Q) = (R \<uplus> P) \<uplus> Q"
  apply(rule ent_iffI; clarsimp simp add: entails_def mod_overlap_conv)
proof(goal_cases)
  case (1 h r pq' rpq p q pq)
  then show ?case
    sledgehammer
  then have "(p \<union> pq) \<inter> q = {}"
    by auto
  then obtain ac ad bc bd where *: "ac \<union> ad = pq' \<and>
     bc \<union> bd = rpq \<and>
     ac \<union> bc = pq \<and>
     ad \<union> bd = (p \<union> q) \<and>
     ac \<inter> ad = {} \<and> bc \<inter> bd = {} \<and>
     ac \<inter> bc = {} \<and> ad \<inter> bd = {} \<and> 
     ac \<inter> bd = {} \<and> ad \<inter> bc = {}"
    using cross_split[of pq' rpq _ "pq" "p \<union> q"] 1 
    by (smt (verit, best) Int_Un_distrib Un_commute inf_commute)
  then obtain ac' ad' bc' bd' where **: "ac' \<union> ad' = ad \<and>
     bc' \<union> bd' = bd \<and>
     ac' \<union> bc' = p \<and>
     ad' \<union> bd' = q \<and>
     ac' \<inter> ad' = {} \<and> bc' \<inter> bd' = {} \<and>
     ac' \<inter> bc' = {} \<and> ad' \<inter> bd' = {} \<and> 
     ac' \<inter> bd' = {} \<and> ad' \<inter> bc' = {}"
    using cross_split[of ad bd _ p q] 1 
    by (smt (verit, best) Int_Un_distrib Un_commute inf_commute)
  show ?case 
    using 1 * **
    apply(inst_existentials "r \<union> p" q pq)
    apply auto
    apply(inst_existentials "r \<union> bd'" "p \<union> ac" "bc \<union> bc'")
    oops


lemma "P \<uplus> Q = (\<exists>\<^sub>AR. (R -* P) * (R -* Q) * R)"
  apply(rule ent_iffI)
    subgoal
      apply (clarsimp simp add: entails_def mod_overlap_conv mod_star_conv)
proof (goal_cases)
  case (1 a as1 as2 as3)
  obtain R where "(a, as3) \<Turnstile> R"
    by (meson "1"(5) in_range_dist_union mod_true models_in_range)
  then show ?case
    using 1
    apply(inst_existentials R "as1 \<union> as2" as3)
    subgoal by blast
    subgoal by blast
    subgoal
    apply(inst_existentials as1 as2)
    subgoal by blast
    subgoal by blast
    apply(intro wand_assnI)
    subgoal by (meson in_range_dist_union models_in_range)
    subgoal for h as' sledgehammer
qed
  subgoal sorry
  done

end 