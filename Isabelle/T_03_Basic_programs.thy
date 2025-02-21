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


theorem special_refine1: "Infeas C \<sqsubseteq>\<^sub>p Skip C" \<comment> \<open>Special_refine\<close>
  by (auto simp: Havoc_def Skip_def Field_def Infeas_def refines_def extends_def weakens_def strengthens_def S_def restrict_r_def)

theorem special_refine2: "Skip C \<sqsubseteq>\<^sub>p Havoc C" \<comment> \<open>Special_refine\<close>
  by (auto simp: Havoc_def Skip_def Infeas_def refines_def extends_def weakens_def strengthens_def S_def restrict_r_def)

theorem special_refine3: "Havoc C \<sqsubseteq>\<^sub>p Fail C" \<comment> \<open>Special_refine\<close>
  by (auto simp: Havoc_def Fail_def refines_def extends_def weakens_def strengthens_def S_def restrict_r_def)

theorem special_refine4: "Infeas C \<sqsubseteq>\<^sub>p Fail C" \<comment> \<open>Special_refine\<close>
  by (auto simp: Infeas_def Fail_def refines_def extends_def weakens_def strengthens_def S_def restrict_r_def)

theorem special_specialize1: "Fail C \<subseteq>\<^sub>p Infeas C" \<comment> \<open>Special_specialize\<close>
  by (auto simp: Infeas_def Fail_def specialize_def extends_def weakens_def strengthens_def S_def restrict_r_def)

theorem special_specialize2: "Infeas C \<subseteq>\<^sub>p Skip C" \<comment> \<open>Special_specialize\<close>
by (auto simp: Infeas_def Skip_def Field_def Havoc_def specialize_def extends_def weakens_def strengthens_def S_def restrict_r_def)

theorem special_specialize3: "Skip C \<subseteq>\<^sub>p Havoc C" \<comment> \<open>Special_specialize\<close>
  by (auto simp: Infeas_def Skip_def Field_def Havoc_def specialize_def extends_def weakens_def strengthens_def S_def restrict_r_def)

theorem "C \<subseteq> D \<Longrightarrow> Fail D \<sqsubseteq>\<^sub>p Fail C" \<comment> \<open>Special_nonempty\<close>
  by (auto simp: refines_def extends_def weakens_def strengthens_def Fail_def restrict_r_def S_def)
theorem "C \<subseteq> D \<Longrightarrow> Fail C \<subseteq>\<^sub>p Fail D"
  by (auto simp: refines_def specialize_def extends_def weakens_def strengthens_def Fail_def restrict_r_def S_def)
theorem "C \<subseteq> D \<Longrightarrow> Infeas D \<sqsubseteq>\<^sub>p Infeas C"
  by (auto simp: refines_def extends_def weakens_def strengthens_def Fail_def restrict_r_def S_def Infeas_def)
theorem "C \<subseteq> D \<Longrightarrow> Infeas C \<subseteq>\<^sub>p Infeas D"
  by (auto simp: refines_def specialize_def extends_def weakens_def strengthens_def Fail_def restrict_r_def S_def Infeas_def)
theorem "C \<subseteq> D \<Longrightarrow> Skip D \<sqsubseteq>\<^sub>p Skip C"
  by (auto simp: refines_def extends_def weakens_def strengthens_def Fail_def restrict_r_def S_def Infeas_def Skip_def Field_def)
theorem "C \<subseteq> D \<Longrightarrow> Skip C \<subseteq>\<^sub>p Skip D"
  by (auto simp: refines_def specialize_def extends_def weakens_def strengthens_def Fail_def restrict_r_def S_def Infeas_def Skip_def Field_def)
theorem "C \<subseteq> D \<Longrightarrow> Havoc C \<sqsubseteq>\<^sub>p Havoc D"
  oops
theorem "C \<subseteq> D \<Longrightarrow> Havoc D \<sqsubseteq>\<^sub>p Havoc C"
  oops
theorem "C \<subseteq> D \<Longrightarrow> Havoc C \<subseteq>\<^sub>p Havoc D"
  by (auto simp: refines_def specialize_def extends_def weakens_def strengthens_def Fail_def restrict_r_def S_def Infeas_def Skip_def Field_def Havoc_def)


end