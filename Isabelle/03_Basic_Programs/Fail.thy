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

theorem fail_is_equivalent_independant_of_arg: "Fail C \<equiv>\<^sub>p Fail D"
  by (auto simp: Fail_def equiv_def restr_post_def)

theorem no_pre_is_fail: "Pre p = {} \<Longrightarrow> Fail s \<equiv>\<^sub>p p" \<comment> \<open>NEW\<close>
  by (auto simp: Fail_def equiv_def restr_post_def restrict_r_def)

theorem NOT_fail_union_r: "p \<union>\<^sub>p Fail (S p) \<triangleq> p"
  oops

theorem fail_union_r: "p \<union>\<^sub>p Fail C \<equiv>\<^sub>p p" \<comment> \<open>/Fail_union/\<close>
  by (auto simp: equiv_def choice_def Fail_def restr_post_def restrict_r_def) 

theorem NOT_fail_union_l: "Fail (S p) \<union>\<^sub>p p \<triangleq> p"
  oops

theorem fail_union_l: "Fail C \<union>\<^sub>p p \<equiv>\<^sub>p p" \<comment> \<open>/Fail_union/\<close>
  by (auto simp: equiv_def choice_def Fail_def restr_post_def restrict_r_def)

theorem fail_compose_l: "Fail C ; p \<equiv>\<^sub>p Fail C" \<comment> \<open>/Fail_compose/\<close>
  by (auto simp: Fail_def composition_def S_def corestrict_r_def equiv_def restr_post_def)

theorem fail_compose_r: "p ; Fail C \<equiv>\<^sub>p Fail C" \<comment> \<open>/Fail_compose/\<close>
  by (auto simp: Fail_def composition_def S_def corestrict_r_def  restr_post_def restrict_r_def equiv_def)

theorem only_fail_refines_fail: "(p \<subseteq>\<^sub>p Fail (S p)) = (p \<equiv>\<^sub>p Fail (S p))" \<comment> \<open>T26\<close>
  oops

theorem refine_fail: "p \<subseteq>\<^sub>p Fail (S p)" \<comment> \<open>Refine_fail\<close>
  by (auto simp: refines_def Fail_def S_def Field_def extends_def weakens_def strengthens_def restrict_r_def)

theorem fail_refine_self: "(Fail (S p) \<subseteq>\<^sub>p p) = (p \<equiv>\<^sub>p Fail (S p))" \<comment> \<open>/Fail_refine_self/\<close>
  by (auto simp: Fail_def S_def Field_def equiv_def restr_post_def restrict_r_def refines_def extends_def weakens_def strengthens_def)

theorem range_of_fail: "Range_p (Fail C) = {}"
  by (auto simp: Fail_def Range_p_def restrict_r_def)

end