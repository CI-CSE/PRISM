theory Boolean
  imports "../T_02_Fundamental_operations"
begin
section \<open>Boolean for top\<close>
theorem restrict_true: "p \<sslash>\<^sub>p (TRUE (S p)) \<triangleq> p" \<comment> \<open>/Restrict_true/\<close>
  by (auto simp: equal_def TRUE_def restrict_p_def restrict_r_def S_def Field_def)

theorem restrict_false: "p \<sslash>\<^sub>p (FALSE) \<equiv>\<^sub>p Fail (S p)" \<comment> \<open>/Restrict_false/\<close>
  by (auto simp: FALSE_def equiv_def Fail_def S_def restr_post_def restrict_r_def restrict_p_def)

theorem cond_false_1: "p \<sslash>\<^sub>p FALSE \<equiv>\<^sub>p Fail (S p)" \<comment> \<open>/Cond_false/\<close>
  by (auto simp: equal_def restr_post_def FALSE_def restrict_p_def restrict_r_def S_def Field_def Fail_def equiv_def)

theorem corestrict_true: "is_feasible p \<Longrightarrow> p \<setminus>\<^sub>p (TRUE (S p)) \<equiv>\<^sub>p p" \<comment> \<open>/Corestrict_true/\<close>
  by (auto simp: equiv_def is_feasible_def TRUE_def corestrict_p_def corestrict_r_def S_def Field_def restr_post_def restrict_r_def subset_iff Domain_iff Range_iff) 

theorem corestrict_false: "p \<setminus>\<^sub>p FALSE = Fail (S p)" \<comment> \<open>/Corestrict_false/\<close>
  oops

theorem corestrict_false: "p \<setminus>\<^sub>p FALSE \<equiv>\<^sub>p Infeas (Pre p)" \<comment> \<open>/Corestrict_false NEW/\<close>
  by (auto simp: equiv_def Infeas_def corestrict_p_def FALSE_def restr_post_def restrict_r_def corestrict_r_def)


theorem if_true: "ITE (TRUE (S p\<^sub>1 \<union> S p\<^sub>2)) p\<^sub>1 p\<^sub>2 \<equiv>\<^sub>p p\<^sub>1" \<comment> \<open>/If_true/\<close>
  by (auto simp: if_then_else_def TRUE_def restrict_p_def S_def restrict_r_def choice_def restr_post_def equiv_def)

theorem if_false1: "ITE (FALSE) p\<^sub>1 p\<^sub>2 \<equiv>\<^sub>p p\<^sub>2" \<comment> \<open>/If_false1/\<close>
  by (auto simp: if_then_else_def FALSE_def restrict_p_def restrict_r_def choice_def restr_post_def equiv_def)

theorem true_selects_first_program_2: "GC [(TRUE (S p\<^sub>1 \<union> S p\<^sub>2), p\<^sub>1), (FALSE, p\<^sub>2)] \<equiv>\<^sub>p p\<^sub>1" \<comment> \<open>NEW\<close>
  by (auto simp: guarded_conditional_def FALSE_def TRUE_def restrict_p_def S_def restrict_r_def choice_def restr_post_def equiv_def Fail_def)

theorem false_selects_second_program_2: "GC [(FALSE, p\<^sub>1), ((TRUE (S p\<^sub>1 \<union> S p\<^sub>2)), p\<^sub>2)] \<equiv>\<^sub>p p\<^sub>2" \<comment> \<open>NEW\<close>
  by (auto simp: guarded_conditional_def TRUE_def S_def FALSE_def restrict_p_def restrict_r_def choice_def restr_post_def equiv_def Fail_def)

theorem restrict_false2: "S p \<subseteq> S q \<Longrightarrow> p \<sslash>\<^sub>p FALSE \<union>\<^sub>p q = Fail {} \<union>\<^sub>p q"
  by (auto simp: FALSE_def Fail_def choice_def S_def restrict_p_def restr_post_def restrict_r_def)

theorem implies_prop: "(C \<rightarrow>\<^sub>s D) = UNIV \<equiv> (C \<subseteq> D)"
  apply (auto simp: IMPLIES\<^sub>s_def TRUE_def NOT\<^sub>s_def OR\<^sub>s_def)
  by (simp add: sup_shunt)

theorem and_prop: "A \<subseteq> X \<Longrightarrow> B \<subseteq> X \<Longrightarrow> A \<and>\<^sub>s B = TRUE X \<equiv> A = X \<and> B = X"
  apply (auto simp: TRUE_def AND\<^sub>s_def subset_iff Int_def)
  by (smt (verit) Collect_cong Collect_mem_eq mem_Collect_eq)

theorem or_prop: "TRUE X \<subseteq> (A \<or>\<^sub>s B) \<equiv> \<forall>x\<in>X. x \<in> A \<or> x \<in> B"
  apply (auto simp: TRUE_def OR\<^sub>s_def subset_iff Int_def)
  by (smt (verit, ccfv_SIG))

end