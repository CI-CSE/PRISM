theory Corestriction
  imports "../T_01_Core"
begin
section ‹Corestriction for top›

theorem corestriction_state [simp]: "S (f ∖⇩p C) = S f"
  by (auto simp: corestrict_p_def S_def corestrict_r_def Field_def)

theorem corestriction_pre [simp]: "Pre (f ∖⇩p C) ⊆ Pre f"
  by (auto simp: corestrict_p_def)

theorem corestriction_post [simp]: "post (f ∖⇩p C) ⊆ post f"
  by (auto simp: corestrict_p_def S_def corestrict_r_def Field_def)

lemma corestrict_prop_1: "Range_p (p ∖⇩p D) ⊆ D"
  by (auto simp: Range_p_def corestrict_p_def corestrict_r_def restrict_r_def)

lemma corestrict_prop_2: "Range_p (p ∖⇩p D) ⊆ Range_p p"
  by (auto simp: Range_p_def corestrict_p_def corestrict_r_def restrict_r_def)

theorem corestrict_prop_: "Range_p (p ∖⇩p D) ⊆ Range_p p ∩ D"
  by (auto simp: Range_p_def corestrict_p_def corestrict_r_def restrict_r_def)

theorem NOT_corestricted_p_refines_p: "p ∖⇩p C ⊆⇩p p"
  oops ― ‹Not true as corestriction might remove a post relation completely›

theorem NOT_p_refines_corestricted_p: "p ⊆⇩p p ∖⇩p C"
  oops ― ‹Not true as corestriction might remove a post ambiguity›

theorem corestricted_refines_unrestricted_1: "p ∖⇩p C ⊆⇩p p" ― ‹T31›
  oops
theorem unrestricted_refines_corestricted_1: "p ⊆⇩p p ∖⇩p C"
  oops
theorem corestricted_refines_unrestricted_2: "is_feasible p ⟹ p ∖⇩p C ⊆⇩p p"
  oops
theorem unrestricted_refines_corestricted_2: "is_feasible p ⟹ p ⊆⇩p p ∖⇩p C"
  oops

theorem corestricted_subprogram_unrestricted: "p ∖⇩p C ≼⇩p p" ― ‹NEW›
  by (auto simp: subprogram_def extends_def weakens_def restr_post_def corestrict_p_def corestrict_r_def restrict_r_def S_def Field_def strengthens_def)

theorem unrestricted_weakens_corestricted: "weakens p (p ∖⇩p C)"
  by (auto simp: weakens_def corestrict_p_def)

theorem corestricted_strengthens_unrestricted: "strengthens (p ∖⇩p C) p"
  by (auto simp: strengthens_def corestrict_p_def restrict_r_def corestrict_r_def)

theorem corestriction_prop: "D ⊆ C ⟹ p ∖⇩p D ⊆⇩p p ∖⇩p C" ― ‹T32›
  oops

theorem corestriction_weakens_prop: "D ⊆ C ⟹ weakens (p ∖⇩p C) (p ∖⇩p D)"
  by (auto simp: weakens_def corestrict_p_def corestrict_r_def)

theorem corestriction_strengthens_prop: "D ⊆ C ⟹ strengthens (p ∖⇩p D) (p ∖⇩p C)"
  by (auto simp: strengthens_def corestrict_p_def corestrict_r_def restrict_r_def)

theorem corestriction_subprogram_prop: "D ⊆ C ⟹ (p ∖⇩p D) ≼⇩p (p ∖⇩p C)" ― ‹NEW›
  by (auto simp: corestrict_p_def subprogram_def extends_def corestrict_r_def S_def Field_def weakens_def restr_post_def restrict_r_def strengthens_def)

theorem equivalence_is_maintained_by_corestriction: "f⇩1 ≡⇩p p⇩1 ⟹ (f⇩1 ∖⇩p C) ≡⇩p p⇩1 ∖⇩p C" ― ‹NEW›
  by (auto simp: equiv_def restr_post_def restrict_r_def corestrict_p_def corestrict_r_def)

theorem equality_is_maintained_by_corestriction: "f⇩1 ≜ p⇩1 ⟹ (f⇩1 ∖⇩p C) ≜ p⇩1 ∖⇩p C" ― ‹NEW›
  by (auto simp: equal_def corestrict_p_def)

theorem corestrict_feasible: "is_feasible p ⟹ is_feasible (p ∖⇩p C)"
  by (auto simp: is_feasible_def corestrict_p_def)
theorem refinement_safety_corestriction: "q ⊆⇩p p ⟹ q ∖⇩p C ⊆⇩p p ∖⇩p C" ― ‹T22›
  oops
theorem weakens_corestriction_1: "all_feasible [p, q] ⟹ q ⊆⇩p p ⟹ weakens (q ∖⇩p C) (p ∖⇩p C)" ― ‹T22›
  oops
theorem weakens_corestriction_2: "q ⊆⇩p p ⟹ weakens (p ∖⇩p C) (q ∖⇩p C)" ― ‹T22›
  oops
theorem strengthens_corestriction_1: "q ⊆⇩p p ⟹ strengthens (p ∖⇩p C) (q ∖⇩p C)" ― ‹T22›
  oops
theorem strengthens_corestriction_2: "q ⊆⇩p p ⟹ strengthens (q ∖⇩p C) (p ∖⇩p C)" ― ‹T22›
  by (auto simp: strengthens_def refines_def corestrict_p_def restrict_r_def corestrict_r_def)

theorem corestrict_is_subprogram: "p∖⇩p C ≼⇩p p"
  by (auto simp: subprogram_def extends_def weakens_def strengthens_def corestrict_p_def corestrict_r_def restrict_r_def S_def Field_def)

end