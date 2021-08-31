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

end 