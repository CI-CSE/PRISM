theory T_03_Basic_programs
  imports 
"T_02_Fundamental_operations"
"03_Basic_Programs/Boolean"
"03_Basic_Programs/Fail"
"03_Basic_Programs/Havoc"
"03_Basic_Programs/Infeas"
"03_Basic_Programs/Skip"
begin
section \<open>Basic programs of top\<close>

theorem special_empty1: "Skip {} = Fail {}" \<comment> \<open>Special_empty\<close>
  by (auto simp: Skip_def Fail_def)
theorem special_empty2: "Havoc {} = Fail {}" \<comment> \<open>Special_empty\<close>
  by (auto simp: Havoc_def Fail_def)
theorem special_empty3: "Havoc {} = Infeas {}" \<comment> \<open>Special_empty\<close>
  by (auto simp: Havoc_def Infeas_def)

theorem "Havoc C = \<lparr>State=C, Pre=TRUE C, post=TRUE\<^sub>r C \<rparr>" \<comment> \<open>Special_def\<close>
  by (auto simp: Havoc_def TRUE_def TRUE\<^sub>r_def)
theorem "Skip C = \<lparr>State=C, Pre=TRUE C, post=ID C\<rparr>"
  by (auto simp: Skip_def TRUE_def ID_def)
theorem "Fail C = \<lparr>State=C, Pre=FALSE, post=FALSE\<rparr>"
  by (auto simp: Fail_def FALSE_def ID_def)
theorem "Infeas C = \<lparr>State=C, Pre=TRUE C, post=FALSE\<rparr>"
  by (auto simp: Infeas_def TRUE_def FALSE_def ID_def)


theorem special_refine1: "Infeas C \<subseteq>\<^sub>p Skip C" \<comment> \<open>Special_refine\<close>
  by (auto simp: Havoc_def Skip_def Field_def Infeas_def refines_def extends_def weakens_def strengthens_def S_def restrict_r_def)

theorem special_refine2: "Skip C \<subseteq>\<^sub>p Havoc C" \<comment> \<open>Special_refine\<close>
  by (auto simp: Havoc_def Skip_def Infeas_def refines_def extends_def weakens_def strengthens_def S_def restrict_r_def)

theorem special_refine3: "Havoc C \<subseteq>\<^sub>p Fail C" \<comment> \<open>Special_refine\<close>
  by (auto simp: Havoc_def Fail_def refines_def extends_def weakens_def strengthens_def S_def restrict_r_def)

theorem special_refine4: "Infeas C \<subseteq>\<^sub>p Fail C" \<comment> \<open>Special_refine\<close>
  by (auto simp: Infeas_def Fail_def refines_def extends_def weakens_def strengthens_def S_def restrict_r_def)

theorem special_subprogram1: "Fail C \<preceq>\<^sub>p Infeas C" \<comment> \<open>Special_subprogram\<close>
  by (auto simp: Infeas_def Fail_def subprogram_def extends_def weakens_def strengthens_def S_def restrict_r_def)

theorem special_subprogram2: "Infeas C \<preceq>\<^sub>p Skip C" \<comment> \<open>Special_subprogram\<close>
by (auto simp: Infeas_def Skip_def Field_def Havoc_def subprogram_def extends_def weakens_def strengthens_def S_def restrict_r_def)

theorem special_subprogram3: "Skip C \<preceq>\<^sub>p Havoc C" \<comment> \<open>Special_subprogram\<close>
  by (auto simp: Infeas_def Skip_def Field_def Havoc_def subprogram_def extends_def weakens_def strengthens_def S_def restrict_r_def)

theorem "C \<subseteq> D \<Longrightarrow> Fail D \<subseteq>\<^sub>p Fail C" \<comment> \<open>Special_nonempty\<close>
  by (auto simp: refines_def extends_def weakens_def strengthens_def Fail_def restrict_r_def S_def)
theorem "C \<subseteq> D \<Longrightarrow> Fail C \<preceq>\<^sub>p Fail D"
  by (auto simp: refines_def subprogram_def extends_def weakens_def strengthens_def Fail_def restrict_r_def S_def)
theorem "C \<subseteq> D \<Longrightarrow> Infeas D \<subseteq>\<^sub>p Infeas C"
  by (auto simp: refines_def extends_def weakens_def strengthens_def Fail_def restrict_r_def S_def Infeas_def)
theorem "C \<subseteq> D \<Longrightarrow> Infeas C \<preceq>\<^sub>p Infeas D"
  by (auto simp: refines_def subprogram_def extends_def weakens_def strengthens_def Fail_def restrict_r_def S_def Infeas_def)
theorem "C \<subseteq> D \<Longrightarrow> Skip D \<subseteq>\<^sub>p Skip C"
  by (auto simp: refines_def extends_def weakens_def strengthens_def Fail_def restrict_r_def S_def Infeas_def Skip_def Field_def)
theorem "C \<subseteq> D \<Longrightarrow> Skip C \<preceq>\<^sub>p Skip D"
  by (auto simp: refines_def subprogram_def extends_def weakens_def strengthens_def Fail_def restrict_r_def S_def Infeas_def Skip_def Field_def)
theorem "C \<subseteq> D \<Longrightarrow> Havoc C \<subseteq>\<^sub>p Havoc D"
  oops
theorem "C \<subseteq> D \<Longrightarrow> Havoc D \<subseteq>\<^sub>p Havoc C"
  oops
theorem "C \<subseteq> D \<Longrightarrow> Havoc C \<preceq>\<^sub>p Havoc D"
  by (auto simp: refines_def subprogram_def extends_def weakens_def strengthens_def Fail_def restrict_r_def S_def Infeas_def Skip_def Field_def Havoc_def)


end