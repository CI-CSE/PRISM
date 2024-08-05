theory Inverse
  imports "../T_01_Core"
begin
section \<open>Inverse top\<close>

theorem inverse_state [simp]: "S (f\<^sup>-\<^sup>1) = S (f)"
  by (auto simp: inverse_def restr_post_def Range_p_def restrict_r_def S_def Field_def)

theorem inverse_pre [simp]: "Pre (f\<^sup>-\<^sup>1) = Range_p (f)"
  by (auto simp: inverse_def)

theorem inverse_post_1 [simp]: "post (f\<^sup>-\<^sup>1) \<subseteq> (post f)\<inverse>"
  by (auto simp: inverse_def restr_post_def restrict_r_def)

theorem inverse_post_2 [simp]: "post (f\<^sup>-\<^sup>1) = (restr_post f)\<inverse>"
  by (auto simp: inverse_def restr_post_def restrict_r_def)

theorem inverse_feasible: "is_feasible p \<Longrightarrow> is_feasible (p\<^sup>-\<^sup>1)"
  by (auto simp: is_feasible_def inverse_def Range_p_def restr_post_def)

theorem inverse_of_inverse_is_self: "is_feasible p \<Longrightarrow> p\<^sup>-\<^sup>1\<^sup>-\<^sup>1 \<equiv>\<^sub>p p"
  apply (auto simp: inverse_def converse_def Range_p_def restr_post_def equiv_def restrict_r_def is_feasible_def Range_iff subset_iff Domain_iff)
  apply blast
  by blast

lemma pre_of_inverse: "is_deterministic (p\<^sup>-\<^sup>1) \<Longrightarrow> Pre p = Pre (p ; (p\<^sup>-\<^sup>1))"
  oops

lemma pre_is_unchanged: "is_feasible p \<Longrightarrow> Pre (p ; (p\<^sup>-\<^sup>1)) = Pre p"
  apply (auto simp: is_feasible_def S_def Field_def composition_def inverse_def Range_p_def restrict_r_def corestrict_r_def Domain_iff Range_iff)
  by blast

lemma post_is_identity: "is_deterministic (p\<^sup>-\<^sup>1) \<Longrightarrow> (x,y)\<in> restr_post (p ; (p\<^sup>-\<^sup>1)) \<Longrightarrow> x = y"
  by (auto simp: is_deterministic_def inverse_def is_function_def restr_post_def composition_def restrict_r_def converse_def)

lemma post_is_identity_2: "is_deterministic (p\<^sup>-\<^sup>1) \<Longrightarrow> (x,y)\<in> restr_post (p ;\<^sub>p (p\<^sup>-\<^sup>1)) \<Longrightarrow> x = y"
  by (auto simp: is_deterministic_def inverse_def is_function_def restr_post_def unsafe_composition_def restrict_r_def converse_def)

lemma post_of_inverse: "is_feasible p \<Longrightarrow> is_deterministic (p\<^sup>-\<^sup>1) \<Longrightarrow> restr_post (Skip (Pre p)) = restr_post (p ; (p\<^sup>-\<^sup>1))"
proof -
  assume a0: "is_feasible p"
  assume a2: "is_deterministic (p\<^sup>-\<^sup>1)"
  show ?thesis
  proof (cases "\<exists>e. e \<in> Pre p")
    case False
    assume a3: "\<nexists>e. e \<in> Pre p"
    from a3 have l2: "\<nexists>r. r \<in> restr_post (Skip (Pre p))"
      by (auto simp: Skip_def restr_post_def restrict_r_def) 
    from a3 have l3: "\<nexists>r. r \<in> restr_post (p ; (p\<^sup>-\<^sup>1))"
      by (auto simp: restr_post_def restrict_r_def composition_def)
    from a3 have l4: "restr_post (Skip (Pre p)) = {}"
      using l2 by fastforce
    from a3 have l5: "restr_post (p ; (p\<^sup>-\<^sup>1)) = {}"
      using l3 by fastforce
    from l4 l5 show ?thesis
      by simp
  next
    case True
    assume a3: "\<exists>e. e \<in> Pre p"
    from a0 a3 have l1: "\<forall>x. x \<in> Pre p \<longrightarrow> (\<exists>y. (x,y) \<in> restr_post p)"
      by (auto simp: is_feasible_def restr_post_def restrict_r_def)
    from a0 a3 l1 have l2: "\<forall>x. x \<in> Pre p \<longrightarrow> (\<exists>y. (x,y) \<in> restr_post p \<and> y \<in> Pre (p\<^sup>-\<^sup>1))"
      by (metis Range.intros Range_p_def inverse_pre restr_post_def)
    from a0 a3 l1 l2 have l3: "\<forall>x. x \<in> Pre p \<longrightarrow> (\<exists>y. (x,y) \<in> restr_post p \<and> y \<in> Pre (p\<^sup>-\<^sup>1) \<and> (\<exists>z. (y,z) \<in> restr_post (p\<^sup>-\<^sup>1)))"
      by (metis Domain_iff a0 implementation_1 in_mono inverse_feasible is_feasible_def restr_post_def)
    have l5: "\<forall>x. x \<in> Pre p \<longrightarrow> (x,x) \<in> restr_post (Skip (Pre p))"
      by (auto simp: Skip_def restr_post_def restrict_r_def)
    have l6: "\<forall>x. x \<in> Pre p \<longrightarrow> (x,x) \<in> restr_post (p ; (p\<^sup>-\<^sup>1))"
      by (metis a2 char_rel_composition char_rel_def l3 post_is_identity relcomp.relcompI restr_post_def)
    have l7: "\<forall>r. r \<in> restr_post (Skip (Pre p)) \<longrightarrow> (fst r \<in> Pre p \<and> snd r \<in> Pre p \<and> fst r = snd r)"
      by (auto simp: Skip_def restr_post_def restrict_r_def)
    have l8: "\<forall>r. r \<in> restr_post (p ; (p\<^sup>-\<^sup>1)) \<longrightarrow> (fst r \<in> Pre p \<and> snd r \<in> Pre p \<and> fst r = snd r)"
      using a0 a2 by (auto simp: restr_post_def inverse_def composition_def corestrict_r_def restrict_r_def Range_p_def is_feasible_def is_deterministic_def is_function_def converse_def)
    from l5 l6 l7 l8 show ?thesis
      by (metis (no_types, lifting) Collect_cong Collect_mem_eq prod.collapse)
  qed
qed

theorem inverse_reverses_composition_1: "is_feasible p \<Longrightarrow> is_deterministic (p\<^sup>-\<^sup>1) \<Longrightarrow> Skip (Pre p) \<equiv>\<^sub>p (p ; (p\<^sup>-\<^sup>1))"
  apply (auto simp: equiv_def)
  apply (auto simp: is_feasible_def is_deterministic_def restr_post_def is_function_def converse_def restrict_r_def inverse_def Range_p_def Skip_def composition_def corestrict_r_def Domain_iff Range_iff subset_iff) [2]
  apply blast
  apply (simp add: post_of_inverse)
  by (simp add: post_of_inverse)

theorem inverse_reverses_composition_2: "Skip (S p) \<subseteq>\<^sub>p (p ; (p\<^sup>-\<^sup>1))"
  apply (auto simp: refines_def)
  apply (auto simp: extends_def Skip_def composition_def inverse_def restrict_r_def restr_post_def Range_p_def S_def Field_def) [1]
  apply (auto simp: weakens_def Skip_def composition_def S_def) [1]
  by (auto simp: strengthens_def Skip_def composition_def inverse_def restrict_r_def restr_post_def corestrict_r_def) [1]

theorem equivalence_is_maintained_by_inverse: "f \<equiv>\<^sub>p p \<Longrightarrow> f\<^sup>-\<^sup>1 \<equiv>\<^sub>p p\<^sup>-\<^sup>1" \<comment> \<open>NEW\<close>
  by (auto simp: equiv_def restr_post_def inverse_def Range_p_def)

theorem equality_is_maintained_by_inverse: "f \<triangleq> p \<Longrightarrow> f\<^sup>-\<^sup>1 \<triangleq> p\<^sup>-\<^sup>1" \<comment> \<open>NEW\<close>
  by (auto simp: equal_def restr_post_def inverse_def Range_p_def)

theorem refinement_safety_inverse: "S f = S g \<Longrightarrow> all_feasible [f, g] \<Longrightarrow> f \<subseteq>\<^sub>p g \<Longrightarrow> (g\<^sup>-\<^sup>1) \<subseteq>\<^sub>p (f\<^sup>-\<^sup>1)"
  oops \<comment> \<open>post `strengthening` is the problem\<close>

theorem inverse_makes_feasible: "is_feasible (p\<^sup>-\<^sup>1)"
  by (auto simp: inverse_def is_feasible_def Range_p_def restr_post_def)

end