theory Fail
  imports "../T_02_Fundamental_operations"
begin
section \<open>Fail for top\<close>


theorem fail_is_valid: "is_valid (Fail s)"
  by (auto simp: is_valid_def Fail_def S_def)

theorem fail_is_feasible: "is_feasible (Fail s)"
  by (auto simp: is_feasible_def Fail_def)

theorem fail_is_total: "is_total (Fail s)"
  oops

theorem fail_is_idempondent_composition: "Fail C ; Fail C = Fail C" \<comment> \<open>NEW\<close>
  by (auto simp: composition_def Fail_def S_def)

theorem fail_is_idempondent_unsafe_composition: "Fail C ;\<^sub>p Fail C = Fail C" \<comment> \<open>NEW\<close>
  by (auto simp: unsafe_composition_def Fail_def S_def)

theorem fail_equiv: "Fail C \<equiv>\<^sub>p Fail D" \<comment> \<open>Fail_equiv\<close>
  by (auto simp: Fail_def equiv_def restr_post_def)

theorem no_pre_is_fail: "Pre p = {} \<Longrightarrow> Fail s \<equiv>\<^sub>p p" \<comment> \<open>NEW\<close>
  by (auto simp: Fail_def equiv_def restr_post_def restrict_r_def)

theorem NOT_fail_choice_r: "p \<union>\<^sub>p Fail (S p) \<triangleq> p"
  oops

theorem fail_choice_r: "p \<union>\<^sub>p Fail C \<equiv>\<^sub>p p" \<comment> \<open>/Fail_choice/\<close>
  by (auto simp: equiv_def choice_def Fail_def restr_post_def restrict_r_def) 

theorem NOT_fail_choice_l: "Fail (S p) \<union>\<^sub>p p \<triangleq> p"
  oops

theorem fail_choice_l: "Fail C \<union>\<^sub>p p \<equiv>\<^sub>p p" \<comment> \<open>/Fail_choice/\<close>
  by (auto simp: equiv_def choice_def Fail_def restr_post_def restrict_r_def)

theorem fail_compose_l_2: "Fail (S p) ; p \<triangleq> Fail (S p)" \<comment> \<open>/Fail_comp/\<close>
  by (auto simp: Fail_def composition_def S_def corestrict_r_def equal_def restr_post_def)

theorem fail_compose_l: "Fail C ; p \<triangleq> Fail (C \<union> S p)" \<comment> \<open>/Fail_comp/\<close>
  by (auto simp: Fail_def composition_def S_def corestrict_r_def equal_def restr_post_def)

theorem fail_compose_r_2: "p ; Fail C \<triangleq> Fail (C \<union> S p)" \<comment> \<open>/Fail_comp/\<close>
  by (auto simp: Fail_def composition_def S_def corestrict_r_def equal_def restr_post_def restrict_r_def)

theorem fail_compose_r: "p ; Fail C \<equiv>\<^sub>p Fail C" \<comment> \<open>/Fail_compo/\<close>
  by (auto simp: Fail_def composition_def S_def corestrict_r_def  restr_post_def restrict_r_def equiv_def)

theorem only_fail_refines_fail: "(p \<sqsubseteq>\<^sub>p Fail (S p)) = (p \<equiv>\<^sub>p Fail (S p))" \<comment> \<open>T26\<close>
  oops

theorem refine_fail: "p \<sqsubseteq>\<^sub>p Fail (S p)" \<comment> \<open>Refine_fail\<close>
  by (auto simp: refines_def Fail_def S_def Field_def extends_def weakens_def strengthens_def restrict_r_def)

theorem fail_refine_self: "(Fail (S p) \<sqsubseteq>\<^sub>p p) = (p \<equiv>\<^sub>p Fail (S p))" \<comment> \<open>/Fail_refine_self/\<close>
  by (auto simp: Fail_def S_def Field_def equiv_def restr_post_def restrict_r_def refines_def extends_def weakens_def strengthens_def)

theorem fail_specialize_self: "(p \<subseteq>\<^sub>p Fail (S p)) = (p \<equiv>\<^sub>p Fail (S p))" \<comment> \<open>/Fail_refine_self/\<close>
  by (metis Fail_def Program.select_convs(2) equiv_is_symetric fail_refine_self no_pre_is_fail refine_fail refines_def specialize_def subset_antisym weakens_def)

theorem range_of_fail: "Range_p (Fail C) = {}"
  by (auto simp: Fail_def Range_p_def restrict_r_def)

theorem choice_fail_implication: "(a \<union>\<^sub>p b \<equiv>\<^sub>p Fail {}) = (a \<equiv>\<^sub>p Fail {} \<and> b \<equiv>\<^sub>p Fail {})"
  by (auto simp: Fail_def choice_def equiv_def restr_post_def restrict_r_def)

theorem fail_refine: "C \<subseteq> S p \<Longrightarrow> p \<sqsubseteq>\<^sub>p Fail C" \<comment> \<open>Fail_refine\<close>
  by (auto simp: Fail_def refines_def extends_def weakens_def S_def strengthens_def restrict_r_def)
theorem "C \<subseteq> S p \<Longrightarrow> Fail C \<subseteq>\<^sub>p p"
  by (auto simp: Fail_def specialize_def extends_def weakens_def S_def strengthens_def restrict_r_def)

theorem fail_specialize2: "p \<subseteq>\<^sub>p Fail (S p) \<equiv> p \<equiv>\<^sub>p Fail {}" \<comment> \<open>Fail_specialize2\<close>
  apply (auto simp: specialize_def Fail_def extends_def weakens_def S_def strengthens_def restrict_r_def equiv_def restr_post_def)
  by (smt (verit, del_insts) empty_iff)

theorem fail_refine2: "Fail (S p) \<sqsubseteq>\<^sub>p p \<equiv> p \<equiv>\<^sub>p Fail {}" \<comment> \<open>Fail_refine2\<close>
  apply (auto simp: refines_def Fail_def extends_def weakens_def S_def strengthens_def restrict_r_def equiv_def restr_post_def)
  by (smt (verit, ccfv_SIG) empty_iff)

theorem compose_empty_1: "S a = {} \<Longrightarrow> b ; a = Fail (S b)"
  by (auto simp: Fail_def composition_def S_def corestrict_r_def restr_post_def restrict_r_def)

theorem compose_empty_2: "S a = {} \<Longrightarrow> a; b = Fail (S b)"
  by (auto simp: Fail_def composition_def S_def corestrict_r_def restr_post_def restrict_r_def Field_def)

theorem fail_union_1: "C \<subseteq> S p \<Longrightarrow> Fail C \<union>\<^sub>p (p \<union>\<^sub>p q) = (p \<union>\<^sub>p q)"
  by (auto simp: Fail_def choice_def S_def restr_post_def restrict_r_def Field_def)


theorem fail_compose: "Fail (S p);p = Fail (S p)"
  by (auto simp: Fail_def composition_def S_def)

lemma fail_union_2: "C \<subseteq> S a \<Longrightarrow> a \<union>\<^sub>p Fail C = a \<union>\<^sub>p Fail {}"
  by (auto simp: Fail_def choice_def S_def restr_post_def)

theorem fail_choice_decomp: "p \<union>\<^sub>p q \<equiv>\<^sub>p Fail {} \<equiv> p \<equiv>\<^sub>p Fail {} \<and> q \<equiv>\<^sub>p Fail {}" \<comment> \<open>Fail_choice_decomp\<close>
  apply (auto simp: equiv_def choice_def Fail_def S_def restr_post_def restrict_r_def)
  by (smt (verit, ccfv_SIG))

theorem fail_specialize: "C \<subseteq> S p \<Longrightarrow> Fail C \<subseteq>\<^sub>p p" \<comment> \<open>/Fail_specialize/\<close>
  by (auto simp: Fail_def specialize_def weakens_def extends_def strengthens_def restrict_r_def S_def)

theorem fail_specialize3: "Fail {} \<subseteq>\<^sub>p p"
  by (auto simp: Fail_def specialize_def extends_def weakens_def strengthens_def S_def restrict_r_def)

end