theory Corestriction
  imports "../T_01_Core"
begin
section \<open>Corestriction for top\<close>

theorem corestriction_state [simp]: "S (f \<setminus>\<^sub>p C) = S f"
  by (auto simp: corestrict_p_def S_def corestrict_r_def Field_def)

theorem corestrict_idem: "(p \<setminus>\<^sub>p C) \<setminus>\<^sub>p C = p \<setminus>\<^sub>p C" \<comment> \<open>NEW\<close>
  by (auto simp: corestrict_p_def S_def Field_def corestrict_r_def)

theorem corestriction_pre [simp]: "Pre (f \<setminus>\<^sub>p C) \<subseteq> Pre f"
  by (auto simp: corestrict_p_def)

theorem corestriction_post [simp]: "post (f \<setminus>\<^sub>p C) \<subseteq> post f"
  by (auto simp: corestrict_p_def S_def corestrict_r_def Field_def)

lemma corestrict_prop_1: "Range_p (p \<setminus>\<^sub>p D) \<subseteq> D"
  by (auto simp: Range_p_def corestrict_p_def corestrict_r_def restrict_r_def)

lemma corestrict_prop_2: "Range_p (p \<setminus>\<^sub>p D) \<subseteq> Range_p p"
  by (auto simp: Range_p_def corestrict_p_def corestrict_r_def restrict_r_def)

theorem corestrict_prop_: "Range_p (p \<setminus>\<^sub>p D) \<subseteq> Range_p p \<inter> D"
  by (auto simp: Range_p_def corestrict_p_def corestrict_r_def restrict_r_def)

theorem NOT_corestricted_p_refines_p: "p \<setminus>\<^sub>p C \<subseteq>\<^sub>p p"
  oops \<comment> \<open>Not true as corestriction might remove a post relation completely\<close>

theorem NOT_p_refines_corestricted_p: "p \<subseteq>\<^sub>p p \<setminus>\<^sub>p C"
  oops \<comment> \<open>Not true as corestriction might remove a post ambiguity\<close>

theorem corestricted_refines_unrestricted_1: "p \<setminus>\<^sub>p C \<subseteq>\<^sub>p p" \<comment> \<open>T31\<close>
  oops
theorem unrestricted_refines_corestricted_1: "p \<subseteq>\<^sub>p p \<setminus>\<^sub>p C"
  oops
theorem corestricted_refines_unrestricted_2: "is_feasible p \<Longrightarrow> p \<setminus>\<^sub>p C \<subseteq>\<^sub>p p"
  oops
theorem unrestricted_refines_corestricted_2: "is_feasible p \<Longrightarrow> p \<subseteq>\<^sub>p p \<setminus>\<^sub>p C"
  oops

theorem corestricted_subprogram_unrestricted: "p \<setminus>\<^sub>p C \<preceq>\<^sub>p p" \<comment> \<open>NEW\<close>
  by (auto simp: subprogram_def extends_def weakens_def restr_post_def corestrict_p_def corestrict_r_def restrict_r_def S_def Field_def strengthens_def)

theorem unrestricted_weakens_corestricted: "weakens p (p \<setminus>\<^sub>p C)"
  by (auto simp: weakens_def corestrict_p_def)

theorem corestricted_strengthens_unrestricted: "strengthens (p \<setminus>\<^sub>p C) p"
  by (auto simp: strengthens_def corestrict_p_def restrict_r_def corestrict_r_def)

theorem corestriction_prop: "D \<subseteq> C \<Longrightarrow> p \<setminus>\<^sub>p D \<subseteq>\<^sub>p p \<setminus>\<^sub>p C" \<comment> \<open>T32\<close>
  oops

theorem corestriction_weakens_prop: "D \<subseteq> C \<Longrightarrow> weakens (p \<setminus>\<^sub>p C) (p \<setminus>\<^sub>p D)"
  by (auto simp: weakens_def corestrict_p_def corestrict_r_def)

theorem corestriction_strengthens_prop: "D \<subseteq> C \<Longrightarrow> strengthens (p \<setminus>\<^sub>p D) (p \<setminus>\<^sub>p C)"
  by (auto simp: strengthens_def corestrict_p_def corestrict_r_def restrict_r_def)

theorem corestrict_subprogram: "D \<subseteq> C \<Longrightarrow> (p \<setminus>\<^sub>p D) \<preceq>\<^sub>p (p \<setminus>\<^sub>p C)" \<comment> \<open>NEW\<close>
  by (auto simp: corestrict_p_def subprogram_def extends_def corestrict_r_def S_def Field_def weakens_def restr_post_def restrict_r_def strengthens_def)

theorem equivalence_is_maintained_by_corestriction: "f\<^sub>1 \<equiv>\<^sub>p p\<^sub>1 \<Longrightarrow> (f\<^sub>1 \<setminus>\<^sub>p C) \<equiv>\<^sub>p p\<^sub>1 \<setminus>\<^sub>p C" \<comment> \<open>NEW\<close>
  by (auto simp: equiv_def restr_post_def restrict_r_def corestrict_p_def corestrict_r_def)

theorem equality_is_maintained_by_corestriction: "f\<^sub>1 \<triangleq> p\<^sub>1 \<Longrightarrow> (f\<^sub>1 \<setminus>\<^sub>p C) \<triangleq> p\<^sub>1 \<setminus>\<^sub>p C" \<comment> \<open>NEW\<close>
  by (auto simp: equal_def corestrict_p_def)

theorem corestrict_feasible: "is_feasible p \<Longrightarrow> is_feasible (p \<setminus>\<^sub>p C)"
  by (auto simp: is_feasible_def corestrict_p_def)
theorem refinement_safety_corestriction: "q \<subseteq>\<^sub>p p \<Longrightarrow> q \<setminus>\<^sub>p C \<subseteq>\<^sub>p p \<setminus>\<^sub>p C" \<comment> \<open>T22\<close>
  oops
theorem weakens_corestriction_1: "all_feasible [p, q] \<Longrightarrow> q \<subseteq>\<^sub>p p \<Longrightarrow> weakens (q \<setminus>\<^sub>p C) (p \<setminus>\<^sub>p C)" \<comment> \<open>T22\<close>
  oops
theorem weakens_corestriction_2: "q \<subseteq>\<^sub>p p \<Longrightarrow> weakens (p \<setminus>\<^sub>p C) (q \<setminus>\<^sub>p C)" \<comment> \<open>T22\<close>
  oops
theorem strengthens_corestriction_1: "q \<subseteq>\<^sub>p p \<Longrightarrow> strengthens (p \<setminus>\<^sub>p C) (q \<setminus>\<^sub>p C)" \<comment> \<open>T22\<close>
  oops
theorem strengthens_corestriction_2: "q \<subseteq>\<^sub>p p \<Longrightarrow> strengthens (q \<setminus>\<^sub>p C) (p \<setminus>\<^sub>p C)" \<comment> \<open>T22\<close>
  by (auto simp: strengthens_def refines_def corestrict_p_def restrict_r_def corestrict_r_def)

theorem corestrict_is_subprogram: "p\<setminus>\<^sub>p C \<preceq>\<^sub>p p"
  by (auto simp: subprogram_def extends_def weakens_def strengthens_def corestrict_p_def corestrict_r_def restrict_r_def S_def Field_def)

theorem corestrict_range_prop: "x \<in> C \<Longrightarrow> x \<notin> Range_p (p \<setminus>\<^sub>p C) \<Longrightarrow> x \<notin> Range_p (p)"
  by (auto simp: Range_p_def corestrict_p_def corestrict_r_def restrict_r_def Range_iff Domain_iff)

theorem corestrict_range_prop_2: "is_feasible a \<Longrightarrow> Range_p a \<subseteq> C \<Longrightarrow> a \<setminus>\<^sub>p C \<equiv>\<^sub>p a"
  apply (auto simp: is_feasible_def Range_p_def corestrict_p_def equiv_def corestrict_r_def restrict_r_def Domain_iff Range_iff subset_iff restr_post_def)
  apply fastforce
  by fastforce

end