theory Implementation
  imports Definitions
begin

section "Implementation for top"


lemma implementation_1: "x ∈ X ⟹ x ∈ Domain (R) ⟹ x ∈ Domain (R ⫽⇩r X)"
  by (auto simp: restrict_r_def)

theorem implementation_theorem: "implements p⇩2 p⇩1 ⟹ is_feasible p⇩1" ― ‹Implement_theorem›
proof -
  assume a1: "implements p⇩2 p⇩1"
  have l1: "Pre p⇩1 ⊆ Domain (post p⇩2)"
    using a1 by (auto simp: implements_def is_feasible_def refines_def weakens_def)
  have l4: "∀x ∈ Pre p⇩1. x ∈ Domain (post p⇩1)"
    using a1 by (meson Domain_mono l1 implementation_1 implements_def refines_def strengthens_def subsetD weakens_def)
  have l5: "Pre p⇩1 ⊆ Domain (post p⇩1)"
    by (simp add: l4 subsetI)
  then show "is_feasible p⇩1"
    by (simp add: is_feasible_def)
qed

end