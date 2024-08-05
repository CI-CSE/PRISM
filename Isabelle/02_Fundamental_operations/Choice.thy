theory Choice
  imports "../T_01_Core"
begin
section \<open>Choice for top\<close>

theorem choice_state [simp]: "S (f \<union>\<^sub>p g) = S f \<union> S g"
  by (auto simp: choice_def S_def restr_post_def restrict_r_def Field_def)

theorem choice_pre [simp]: "Pre (f \<union>\<^sub>p g) = Pre f \<union> Pre g"
  by (simp add: choice_def)

theorem choice_post_1 [simp]: "post (f \<union>\<^sub>p g) \<subseteq> post f \<union> post g"
  by (auto simp: choice_def restr_post_def restrict_r_def)

theorem choice_post_2 [simp]: "post (f \<union>\<^sub>p g) = restr_post f \<union> restr_post g"
  by (auto simp: choice_def)

theorem choice_idem_2 [simp]: "p \<union>\<^sub>p p \<triangleq> p" \<comment> \<open>/Choice_idem/\<close>
  oops

theorem choice_idem_3 [simp]: "p \<union>\<^sub>p p \<equiv>\<^sub>p p"
  by (auto simp: choice_def equiv_def restr_post_def restrict_r_def)


theorem choice_commute [simp]: "p\<^sub>1 \<union>\<^sub>p p\<^sub>2 = p\<^sub>2 \<union>\<^sub>p p\<^sub>1" \<comment> \<open>/Choice_commute/\<close>
  by (auto simp: choice_def)

theorem choice_commute_2 [simp]: "p\<^sub>1 \<union>\<^sub>p p\<^sub>2 \<triangleq> p\<^sub>2 \<union>\<^sub>p p\<^sub>1" \<comment> \<open>/Choice_commute/\<close>
  by (simp add: equal_is_reflexive)

theorem choice_commute_3 [simp]: "p\<^sub>1 \<union>\<^sub>p p\<^sub>2 \<equiv>\<^sub>p p\<^sub>2 \<union>\<^sub>p p\<^sub>1" \<comment> \<open>/Choice_commute/\<close>
  by (auto simp: equiv_is_reflexive)

theorem choice_assoc_1 [simp]: "(p\<^sub>1 \<union>\<^sub>p p\<^sub>2) \<union>\<^sub>p p\<^sub>3 = p\<^sub>1 \<union>\<^sub>p (p\<^sub>2 \<union>\<^sub>p p\<^sub>3)" \<comment> \<open>Choice_assoc\<close>
  by (auto simp: equal_def S_def choice_def restr_post_def restrict_r_def Field_def)

theorem choice_assoc_2 [simp]: "(p\<^sub>1 \<union>\<^sub>p p\<^sub>2) \<union>\<^sub>p p\<^sub>3 \<triangleq> p\<^sub>1 \<union>\<^sub>p (p\<^sub>2 \<union>\<^sub>p p\<^sub>3)" \<comment> \<open>Choice_assoc\<close>
  by (metis choice_assoc_1 equal_is_reflexive)

theorem choice_assoc_3 [simp]: "(p\<^sub>1 \<union>\<^sub>p p\<^sub>2) \<union>\<^sub>p p\<^sub>3 \<equiv>\<^sub>p p\<^sub>1 \<union>\<^sub>p (p\<^sub>2 \<union>\<^sub>p p\<^sub>3)"
  using choice_assoc_2 equals_equiv_relation_2 by blast

theorem equivalence_is_maintained_by_choice: "f\<^sub>1 \<equiv>\<^sub>p p\<^sub>1 \<Longrightarrow> f\<^sub>2 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> f\<^sub>1 \<union>\<^sub>p f\<^sub>2 \<equiv>\<^sub>p p\<^sub>1 \<union>\<^sub>p p\<^sub>2" \<comment> \<open>NEW\<close>
  by (auto simp: equiv_def restr_post_def choice_def)

theorem equality_is_maintained_by_choice: "f\<^sub>1 \<triangleq> p\<^sub>1 \<Longrightarrow> f\<^sub>2 \<triangleq> p\<^sub>2 \<Longrightarrow> f\<^sub>1 \<union>\<^sub>p f\<^sub>2 \<triangleq> p\<^sub>1 \<union>\<^sub>p p\<^sub>2" \<comment> \<open>NEW\<close>
  by (auto simp: equal_def restr_post_def choice_def)

theorem union_feasible: "all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> is_feasible (p\<^sub>1 \<union>\<^sub>p p\<^sub>2)" \<comment> \<open>/Union_feasible/\<close>
  by (auto simp: is_feasible_def choice_def restr_post_def restrict_r_def Domain_def)

lemma condition_for_choice_simplification: "Range_p a \<inter> Pre y = {} \<Longrightarrow> Range_p x \<inter> Pre b = {} \<Longrightarrow> a;b \<union>\<^sub>p x;y \<equiv>\<^sub>p (a \<union>\<^sub>p x) ; (b \<union>\<^sub>p y)"
  apply (auto simp: equiv_def)
  apply (auto simp: Range_p_def restrict_r_def choice_def restr_post_def composition_def corestrict_r_def) [3]
  apply (simp add: composition_def choice_def restr_post_def restrict_r_def Range_p_def corestrict_r_def relcomp_unfold Range_iff Int_def Domain_iff)
  apply blast
  apply (simp add: composition_def choice_def restr_post_def restrict_r_def Range_p_def corestrict_r_def relcomp_unfold Range_iff Int_def Domain_iff)
  by blast

lemma range_p_prop_1: "Range_p (p\<^sub>1 \<union>\<^sub>p p\<^sub>2) = Range_p p\<^sub>1 \<union> Range_p p\<^sub>2"
  by (auto simp: Range_p_def restr_post_def restrict_r_def)

lemma refinement_safety_choice_e: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> extends (q\<^sub>1 \<union>\<^sub>p q\<^sub>2) (p\<^sub>1 \<union>\<^sub>p p\<^sub>2)"
  by (metis choice_state extends_def refines_def sup_mono)

lemma refinement_safety_choice_w: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> weakens (q\<^sub>1 \<union>\<^sub>p q\<^sub>2) (p\<^sub>1 \<union>\<^sub>p p\<^sub>2)"
  by (auto simp: refines_def weakens_def choice_def restr_post_def restrict_r_def)

lemma refinement_safety_choice_s_1: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> strengthens (q\<^sub>1 \<union>\<^sub>p q\<^sub>2) (p\<^sub>1 \<union>\<^sub>p p\<^sub>2)"
  oops

lemma refinement_safety_choice_s_2: "strengthens q\<^sub>1 p\<^sub>2 \<Longrightarrow> strengthens q\<^sub>2 p\<^sub>1 \<Longrightarrow> q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> strengthens (q\<^sub>1 \<union>\<^sub>p q\<^sub>2) (p\<^sub>1 \<union>\<^sub>p p\<^sub>2)"
  by (auto simp: refines_def strengthens_def choice_def restr_post_def restrict_r_def)

theorem refinement_safety_choice: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> (q\<^sub>1 \<union>\<^sub>p q\<^sub>2) \<subseteq>\<^sub>p (p\<^sub>1 \<union>\<^sub>p p\<^sub>2)" \<comment> \<open>NEW T23 weak\<close>
  oops

theorem refinement_safety_choice_1: "strengthens q\<^sub>1 p\<^sub>2 \<Longrightarrow> strengthens q\<^sub>2 p\<^sub>1 \<Longrightarrow> q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> (q\<^sub>1 \<union>\<^sub>p q\<^sub>2) \<subseteq>\<^sub>p (p\<^sub>1 \<union>\<^sub>p p\<^sub>2)" \<comment> \<open>NEW T23 weak\<close>
  by (simp add: refinement_safety_choice_e refinement_safety_choice_s_2 refinement_safety_choice_w refines_def)

theorem refinement_safety_choice_2: "independent q\<^sub>1 p\<^sub>2 \<Longrightarrow> independent q\<^sub>2 p\<^sub>1 \<Longrightarrow> q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> (q\<^sub>1 \<union>\<^sub>p q\<^sub>2) \<subseteq>\<^sub>p (p\<^sub>1 \<union>\<^sub>p p\<^sub>2)" \<comment> \<open>NEW T23 weaker\<close>
  by (simp add: independent_def independent_strengthens refinement_safety_choice_1)

theorem program_is_subprogram_of_choice: "p\<^sub>1 \<preceq>\<^sub>p (p\<^sub>1 \<union>\<^sub>p p\<^sub>2)"
  by (auto simp: subprogram_def choice_def extends_def S_def weakens_def strengthens_def restr_post_def restrict_r_def)

theorem choice_range_p_prop_1: "Range_p p \<subseteq> Range_p (p \<union>\<^sub>p q)"
  by (auto simp: Range_p_def choice_def restrict_r_def restr_post_def)

theorem choice_range_p_prop_2: "x \<in> Range_p (p \<union>\<^sub>p q) \<Longrightarrow> x \<notin> Range_p p \<Longrightarrow> x \<in> Range_p q"
  by (auto simp: Range_p_def choice_def restrict_r_def restr_post_def)

theorem choice_range_p_prop_3: "x \<notin> Range_p (p \<union>\<^sub>p q) \<Longrightarrow> x \<notin> Range_p p"
  by (auto simp: Range_p_def choice_def restrict_r_def restr_post_def)
end