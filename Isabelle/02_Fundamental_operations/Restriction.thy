theory Restriction
  imports "../T_01_Core"
begin
section \<open>Restriction for top\<close>

theorem restriction_state [simp]: "S (f \<sslash>\<^sub>p C) = S f"
  by (auto simp: restrict_p_def S_def restrict_r_def Field_def)

theorem restriction_pre [simp]: "Pre (f \<sslash>\<^sub>p C) \<subseteq> Pre f"
  by (auto simp: restrict_p_def)

theorem restriction_post [simp]: "post (f \<sslash>\<^sub>p C) \<subseteq> post f"
  by (auto simp: restrict_p_def S_def restrict_r_def)
lemma restrict_prop_1: "Pre (p \<sslash>\<^sub>p D) \<subseteq> D"
  by (auto simp: restrict_p_def)

lemma restrict_prop_2: "Pre (p \<sslash>\<^sub>p D) \<subseteq> Pre p"
  by (auto simp: restrict_p_def)

theorem restrict_prop: "Pre (p \<sslash>\<^sub>p D) \<subseteq> Pre p \<inter> D"
  by (auto simp: restrict_p_def)

theorem restrict_idem: "(p \<sslash>\<^sub>p C) \<sslash>\<^sub>p C = p \<sslash>\<^sub>p C" \<comment> \<open>/Restrict_idem/\<close>
  by (auto simp: restrict_p_def S_def restrict_r_def Field_def)

lemma restrict_inter: "(p\<sslash>\<^sub>pC\<^sub>1)\<sslash>\<^sub>pC\<^sub>2 = p\<sslash>\<^sub>p(C\<^sub>1 \<inter> C\<^sub>2)" \<comment> \<open>/Restrict_inter/\<close>
  by (auto simp: equal_def S_def Field_def restrict_p_def restrict_r_def)

theorem restrict_commute [simp]: "(p\<sslash>\<^sub>pC\<^sub>1)\<sslash>\<^sub>pC\<^sub>2 = (p\<sslash>\<^sub>pC\<^sub>2)\<sslash>\<^sub>pC\<^sub>1" \<comment> \<open>/Restrict_commute/\<close>
  by (simp add: inf_commute restrict_inter)

theorem restriction_equiv: "f\<^sub>1 \<equiv>\<^sub>p p\<^sub>1 \<Longrightarrow> (f\<^sub>1 \<sslash>\<^sub>p C) \<equiv>\<^sub>p p\<^sub>1 \<sslash>\<^sub>p C" \<comment> \<open>Restriction_equiv\<close>
  by (auto simp: equiv_def restr_post_def restrict_r_def restrict_p_def)

theorem equality_is_maintained_by_restriction: "f\<^sub>1 \<triangleq> p\<^sub>1 \<Longrightarrow> (f\<^sub>1 \<sslash>\<^sub>p C) \<triangleq> p\<^sub>1 \<sslash>\<^sub>p C" \<comment> \<open>NEW\<close>
  by (auto simp: equal_def restr_post_def restrict_p_def)

theorem restrict_feasible: "is_feasible p \<Longrightarrow> is_feasible (p \<sslash>\<^sub>p C)" \<comment> \<open>/Restrict_feasible/\<close>
  by (auto simp: is_feasible_def restrict_p_def restrict_r_def Domain_def)

theorem restrict_might_make_feasible: "C \<subseteq> Domain (post p) \<Longrightarrow> is_feasible (p \<sslash>\<^sub>p C)"
  apply (auto simp: is_feasible_def restrict_p_def restrict_r_def Domain_iff) by auto

theorem restrict_refine_1: "strengthens p  (p \<sslash>\<^sub>p C)"
  by (auto simp: strengthens_def restrict_p_def restrict_r_def)

theorem restrict_refine_2: "strengthens (p \<sslash>\<^sub>p C) p" 
  by (auto simp: strengthens_def restrict_p_def restrict_r_def)

theorem restrict_refine_3: "strengthens p  q \<Longrightarrow> strengthens (p \<sslash>\<^sub>p C) (q \<sslash>\<^sub>p C)"
  by (auto simp: strengthens_def restrict_p_def restrict_r_def)


theorem restrict_refine_4: "weakens p  (p \<sslash>\<^sub>p C)"
  by (auto simp: weakens_def restrict_p_def restrict_r_def)

theorem restrict_refine_5: "weakens p  q \<Longrightarrow> weakens (p \<sslash>\<^sub>p C) (q \<sslash>\<^sub>p C)"
  by (auto simp: weakens_def restrict_p_def restrict_r_def)

theorem restrict_refine: "p \<subseteq>\<^sub>p p \<sslash>\<^sub>p C" \<comment> \<open>/Restrict_refine/\<close>
  by (auto simp: refines_def extends_def weakens_def strengthens_def restrict_p_def restrict_r_def S_def Field_def)

theorem restrict_refineorder1: "D \<subseteq> C \<Longrightarrow> p \<sslash>\<^sub>p C \<subseteq>\<^sub>p p \<sslash>\<^sub>p D" \<comment> \<open>/Restrict_refineorder1/\<close>
  by (auto simp: refines_def extends_def weakens_def strengthens_def restrict_p_def restrict_r_def S_def Field_def)

theorem restriction_refsafety: "q \<subseteq>\<^sub>p p \<Longrightarrow> q \<sslash>\<^sub>p C \<subseteq>\<^sub>p p \<sslash>\<^sub>p C" \<comment> \<open>/Restriction_refsafety/\<close>
  by (auto simp: refines_def extends_def weakens_def strengthens_def restrict_p_def restrict_r_def S_def Field_def)

theorem restriction_subsafety: "q \<preceq>\<^sub>p p \<Longrightarrow> q \<sslash>\<^sub>p C \<preceq>\<^sub>p p \<sslash>\<^sub>p C" \<comment> \<open>/Restriction_subsafety/\<close>
  by (simp add: extends_def restrict_refine_3 restrict_refine_5 subprogram_def)

theorem restriction_refsafety2: "q \<subseteq>\<^sub>p p \<Longrightarrow> D \<subseteq> C \<Longrightarrow> q \<sslash>\<^sub>p C \<subseteq>\<^sub>p p \<sslash>\<^sub>p D" \<comment> \<open>//\<close>
  by (meson restrict_refineorder1 restriction_refsafety refines_is_preorder)

theorem implements_safety_restriction: "implements a b \<Longrightarrow> implements (a \<sslash>\<^sub>p C) (b \<sslash>\<^sub>p C)"
  by (simp add: implements_def restriction_refsafety restrict_feasible)

theorem restrict_subprogorder1: "D \<subseteq> C \<Longrightarrow> p \<sslash>\<^sub>p D \<preceq>\<^sub>p p \<sslash>\<^sub>p C" \<comment> \<open>Restrict_subprogorder1\<close>
  by (metis extends_def inf.absorb_iff2 order_refl restrict_inter restrict_refine_2 restrict_refine_4 restriction_state subprogram_def)

theorem restrict_subprog: "p \<sslash>\<^sub>p C \<preceq>\<^sub>p p" \<comment> \<open>Restrict_subprog\<close>
  by (auto simp: restrict_p_def subprogram_def extends_def weakens_def S_def strengthens_def restrict_r_def Field_def)


end