theory Infeas
  imports "../T_02_Fundamental_operations"
begin
section \<open>Infeas for top\<close>

theorem infeas_is_valid: "is_valid (Infeas s)"
  by (auto simp: is_valid_def Infeas_def S_def)

theorem infeas_is_feasible: "is_feasible (Infeas s)"
  oops

theorem infeas_is_total: "is_total (Infeas s)"
  by (simp add: Infeas_def is_total_def S_def)

theorem infeas_is_idempondent_composition: "Infeas C ; Infeas C = Infeas C"
  oops

theorem infeas_is_idempondent_unsafe_composition: "Infeas C ;\<^sub>p Infeas C = Infeas C"
  by (simp add: unsafe_composition_def Infeas_def S_def)


theorem fail_is_equivalent_independant_of_arg: "Infeas C \<equiv>\<^sub>p Infeas D"
  oops

theorem not_total_infeas_makes_infeasible: "\<not>is_total p \<Longrightarrow> \<not>is_feasible (p \<union>\<^sub>p Infeas (S p))"
  apply (cases "\<not>is_feasible p")
   apply (auto simp: is_feasible_def Infeas_def S_def restr_post_def restrict_r_def Field_def subset_iff Domain_iff Range_iff) [1]
proof -
  assume a1: "\<not>\<not>is_feasible p"
  assume a2: "\<not>is_total p"
  from a1 have l1: "is_feasible p" by simp
  from a2 have l2: "\<exists>x \<in> S p. x \<notin> Pre p"
    by (auto simp: is_total_def S_def)
  from a1 a2 l1 l2 show "\<not> is_feasible (p \<union>\<^sub>p Infeas (S p))"
    apply (simp add: Infeas_def choice_def is_feasible_def restr_post_def restrict_r_def S_def Field_def subset_iff Domain_iff Range_iff is_total_def Un_def)
    by (auto)
qed

theorem infeas_makes_total: "is_total (p \<union>\<^sub>p Infeas (S p))"
  by (auto simp: Infeas_def is_total_def S_def choice_def restr_post_def restrict_r_def Field_def)

theorem infeas_to_smaller_self: "p ; Infeas (S p) \<equiv>\<^sub>p Infeas (Pre p \<inter> Domain (post p))"
  by (auto simp: Infeas_def Fail_def S_def composition_def restr_post_def restrict_r_def corestrict_r_def Field_def Domain_iff equiv_def Range_iff)

theorem infeas_composition: "Infeas (S p) ; p = Fail (S p)"
  by (auto simp: Infeas_def Fail_def composition_def S_def corestrict_r_def)

theorem infeas_unsafe_composition_1: "Infeas (S p) ;\<^sub>p p = Infeas (S p)"
  by (auto simp: Infeas_def unsafe_composition_def S_def)

theorem infeas_unsafe_composition_2: "p ;\<^sub>p Infeas (S p) \<equiv>\<^sub>p Infeas (Pre p)"
  by (auto simp: Infeas_def equiv_def unsafe_composition_def restr_post_def restrict_r_def)

theorem infeas_restriction: "Infeas (C) \<sslash>\<^sub>p D \<equiv>\<^sub>p Infeas (C \<inter> D)"
  by (auto simp: Infeas_def restrict_p_def S_def equiv_def restr_post_def)

theorem infeas_corestriction: "Infeas (C) \<setminus>\<^sub>p D = Fail (C)"
  by (auto simp: Infeas_def corestrict_p_def corestrict_r_def S_def Fail_def)

end