theory Restriction
  imports "../T_01_Core"
begin
section \<open>Restriction for top\<close>

theorem restriction_state [simp]: "S (f \<sslash>\<^sub>p C) = S f"
  by (auto simp: restrict_p_def S_def)

theorem restriction_pre [simp]: "Pre (f \<sslash>\<^sub>p C) \<subseteq> Pre f"
  by (auto simp: restrict_p_def)

theorem restriction_post [simp]: "post (f \<sslash>\<^sub>p C) \<subseteq> post f"
  by (auto simp: restrict_p_def S_def)
lemma restrict_prop_1: "Pre (p \<sslash>\<^sub>p D) \<subseteq> D"
  by (auto simp: restrict_p_def)

lemma restrict_prop_2: "Pre (p \<sslash>\<^sub>p D) \<subseteq> Pre p"
  by (auto simp: restrict_p_def)

theorem restrict_prop: "Pre (p \<sslash>\<^sub>p D) \<subseteq> Pre p \<inter> D"
  by (auto simp: restrict_p_def)

theorem restrict_idem: "(p \<sslash>\<^sub>p C) \<sslash>\<^sub>p C = p \<sslash>\<^sub>p C" \<comment> \<open>NEW\<close>
  by (auto simp: restrict_p_def S_def)

lemma restrict_inter: "(p\<sslash>\<^sub>pC\<^sub>1)\<sslash>\<^sub>pC\<^sub>2 = p\<sslash>\<^sub>p(C\<^sub>1 \<inter> C\<^sub>2)" \<comment> \<open>/Restrict_inter/\<close>
  by (auto simp: equal_def S_def Field_def restrict_p_def restrict_r_def)

theorem restrict_commute [simp]: "(p\<sslash>\<^sub>pC\<^sub>1)\<sslash>\<^sub>pC\<^sub>2 = (p\<sslash>\<^sub>pC\<^sub>2)\<sslash>\<^sub>pC\<^sub>1" \<comment> \<open>/Restrict_commute/\<close>
  by (simp add: inf_commute restrict_inter)

theorem equivalence_is_maintained_by_restriction: "f\<^sub>1 \<equiv>\<^sub>p p\<^sub>1 \<Longrightarrow> (f\<^sub>1 \<sslash>\<^sub>p C) \<equiv>\<^sub>p p\<^sub>1 \<sslash>\<^sub>p C" \<comment> \<open>NEW\<close>
  by (auto simp: equiv_def restr_post_def restrict_r_def restrict_p_def)

theorem equality_is_maintained_by_restriction: "f\<^sub>1 \<triangleq> p\<^sub>1 \<Longrightarrow> (f\<^sub>1 \<sslash>\<^sub>p C) \<triangleq> p\<^sub>1 \<sslash>\<^sub>p C" \<comment> \<open>NEW\<close>
  by (auto simp: equal_def restr_post_def restrict_p_def)

theorem restrict_feasible: "is_feasible p \<Longrightarrow> is_feasible (p \<sslash>\<^sub>p C)" \<comment> \<open>/Restrict_feasible/\<close>
  by (auto simp: is_feasible_def restrict_p_def restrict_r_def Domain_def)

theorem restrict_might_make_feasible: "C \<subseteq> Domain (post p) \<Longrightarrow> is_feasible (p \<sslash>\<^sub>p C)"
  by (auto simp: is_feasible_def restrict_p_def)

theorem restrict_refine: "p \<subseteq>\<^sub>p p \<sslash>\<^sub>p C" \<comment> \<open>/Restrict_refine/\<close>
  by (auto simp: refines_def extends_def weakens_def strengthens_def restrict_p_def restrict_r_def S_def Field_def)

theorem order_reversal: "D \<subseteq> C \<Longrightarrow> p \<sslash>\<^sub>p C \<subseteq>\<^sub>p p \<sslash>\<^sub>p D" \<comment> \<open>/Order_reverse/\<close>
  by (auto simp: refines_def extends_def weakens_def strengthens_def restrict_p_def restrict_r_def S_def Field_def)

theorem refinement_safety_restriction: "q \<subseteq>\<^sub>p p \<Longrightarrow> q \<sslash>\<^sub>p C \<subseteq>\<^sub>p p \<sslash>\<^sub>p C" \<comment> \<open>/Order_reverse/\<close>
  by (auto simp: refines_def extends_def weakens_def strengthens_def restrict_p_def restrict_r_def S_def Field_def)

theorem refinement_safety_restriction2: "q \<subseteq>\<^sub>p p \<Longrightarrow> D \<subseteq> C \<Longrightarrow> q \<sslash>\<^sub>p C \<subseteq>\<^sub>p p \<sslash>\<^sub>p D" \<comment> \<open>/Order_reverse/\<close>
  by (meson order_reversal refinement_safety_restriction refines_is_preorder)
end