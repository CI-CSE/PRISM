theory Guarded_conditional
  imports "../T_03_Basic_programs"
begin
section \<open>Guarded conditional top\<close>

theorem gc_S [simp]: "S (GC C p D q) = S p \<union> S q"
  by (auto simp: guarded_conditional_def)
theorem gc_commutative_1: "(GC C\<^sub>1 p\<^sub>1 C\<^sub>2 p\<^sub>2) = (GC C\<^sub>2 p\<^sub>2 C\<^sub>1 p\<^sub>1)" \<comment> \<open>T46\<close>
  by (simp add: guarded_conditional_def)

theorem gc_commutative_2: "(GC C\<^sub>1 p\<^sub>1 C\<^sub>2 p\<^sub>2) \<triangleq> (GC C\<^sub>2 p\<^sub>2 C\<^sub>1 p\<^sub>1)" \<comment> \<open>T46\<close>
  by (simp add: equal_is_reflexive gc_commutative_1)

theorem gc_commutative_3: "(GC C\<^sub>1 p\<^sub>1 C\<^sub>2 p\<^sub>2) \<equiv>\<^sub>p (GC C\<^sub>2 p\<^sub>2 C\<^sub>1 p\<^sub>1)" \<comment> \<open>T46\<close>
  by (simp add: equiv_is_reflexive gc_commutative_1)



theorem subprogram_gc: "D\<^sub>1 \<subseteq> C\<^sub>1 \<Longrightarrow> D\<^sub>2 \<subseteq> C\<^sub>2 \<Longrightarrow> (GC D\<^sub>1 p D\<^sub>2 q) \<preceq>\<^sub>p (GC C\<^sub>1 p C\<^sub>2 q)"
  apply (auto simp: subprogram_def extends_def weakens_def strengthens_def guarded_conditional_def restr_post_def restrict_p_def restrict_r_def choice_def)
  apply (simp add: S_def Field_def Range_iff Domain_iff)
  by force

theorem property_on_gc_3: "all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> GC C\<^sub>1 p\<^sub>1 C\<^sub>2 p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>1 \<sslash>\<^sub>p C\<^sub>1" \<comment> \<open>T54\<close>
  oops

theorem property_on_gc_3_1: "weakens (GC C\<^sub>1 p\<^sub>1 C\<^sub>2 p\<^sub>2) (p\<^sub>1 \<sslash>\<^sub>p C\<^sub>1)"
  by (auto simp: weakens_def restrict_p_def guarded_conditional_def choice_def)

theorem property_on_gc_3_2: "strengthens (p\<^sub>1 \<sslash>\<^sub>p C\<^sub>1) (GC C\<^sub>1 p\<^sub>1 C\<^sub>2 p\<^sub>2)"
  by (auto simp: strengthens_def restr_post_def restrict_r_def restrict_p_def guarded_conditional_def choice_def)

theorem property_on_gc_3_3: "(p\<^sub>1 \<sslash>\<^sub>p C\<^sub>1) \<preceq>\<^sub>p (GC C\<^sub>1 p\<^sub>1 C\<^sub>2 p\<^sub>2)"
  by (auto simp: restrict_p_def subprogram_def guarded_conditional_def extends_def weakens_def restr_post_def restrict_r_def strengthens_def)

theorem refinement_safety_gc_1: "all_feasible [p, q] \<Longrightarrow> D\<^sub>1 \<subseteq> C\<^sub>1 \<Longrightarrow> D\<^sub>2 \<subseteq> C\<^sub>2 \<Longrightarrow> GC D\<^sub>1 p D\<^sub>2 q \<subseteq>\<^sub>p GC C\<^sub>1 p C\<^sub>2 q" \<comment> \<open>T49\<close>
  oops

theorem refinement_safety_gc_2: "all_feasible [p, q] \<Longrightarrow> D\<^sub>1 \<subseteq> C\<^sub>1 \<Longrightarrow> D\<^sub>2 \<subseteq> C\<^sub>2 \<Longrightarrow> GC C\<^sub>1 p C\<^sub>2 q \<subseteq>\<^sub>p GC D\<^sub>1 p D\<^sub>2 q" \<comment> \<open>T49\<close>
  oops

theorem refinement_safety_gc_weakens: "D\<^sub>1 \<subseteq> C\<^sub>1 \<Longrightarrow> D\<^sub>2 \<subseteq> C\<^sub>2 \<Longrightarrow> weakens (GC C\<^sub>1 p C\<^sub>2 q) (GC D\<^sub>1 p D\<^sub>2 q)" \<comment> \<open>T49\<close>
  by (auto simp: weakens_def guarded_conditional_def restrict_p_def restrict_r_def choice_def)

theorem refinement_safety_gc_strengthens: "D\<^sub>1 \<subseteq> C\<^sub>1 \<Longrightarrow> D\<^sub>2 \<subseteq> C\<^sub>2 \<Longrightarrow> strengthens (GC D\<^sub>1 p D\<^sub>2 q) (GC C\<^sub>1 p C\<^sub>2 q)" \<comment> \<open>T49\<close>
  by (auto simp: strengthens_def restr_post_def guarded_conditional_def restrict_p_def restrict_r_def choice_def)

theorem refinement_safety_gc_3: "all_feasible [p\<^sub>1, p\<^sub>2, q\<^sub>1, q\<^sub>2] \<Longrightarrow> strengthens q\<^sub>1 p\<^sub>2 \<Longrightarrow> strengthens q\<^sub>2 p\<^sub>1 \<Longrightarrow> q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> GC C q\<^sub>1 C q\<^sub>2 \<subseteq>\<^sub>p GC C p\<^sub>1 C p\<^sub>2" \<comment> \<open>T50 NEW Same problem as with refinement safety of choice\<close>
  apply (auto simp: refines_def)
  apply (auto simp: is_feasible_def extends_def) [1]
  apply (auto simp: weakens_def is_feasible_def guarded_conditional_def restrict_p_def restrict_r_def choice_def)  [1]
  by (auto simp: strengthens_def restr_post_def guarded_conditional_def restrict_p_def restrict_r_def choice_def)

theorem refinement_safety_gc_4: "all_feasible [p\<^sub>1, p\<^sub>2, q\<^sub>1, q\<^sub>2] \<Longrightarrow> independent q\<^sub>1 p\<^sub>2 \<Longrightarrow> independent q\<^sub>2 p\<^sub>1 \<Longrightarrow> q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> GC C q\<^sub>1 C q\<^sub>2 \<subseteq>\<^sub>p GC C p\<^sub>1 C p\<^sub>2" \<comment> \<open>T50 NEW Same problem as with refinement safety of choice\<close>
  by (simp add: independent_strengthens refinement_safety_gc_3)


theorem "GC C\<^sub>1 p\<^sub>1 C\<^sub>2 p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>1 \<sslash>\<^sub>p C\<^sub>1"
  oops \<comment> \<open>C1 and C2 might have an overlap\<close>


end