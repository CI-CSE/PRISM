theory Independence
  imports Definitions
begin
section ‹Independence for top›


subsubsection ‹Independent properties›

theorem independent_symetric: "independent p⇩1 p⇩2 = independent p⇩2 p⇩1"
  by (auto simp: independent_def)

theorem independent_weakens: "independent p⇩1 p⇩2 ⟹ Pre p⇩2 ≠ {} ⟹ ¬weakens p⇩1 p⇩2"
  by (auto simp: independent_def weakens_def)

theorem independent_strengthens: "independent p⇩1 p⇩2 ⟹ strengthens p⇩1 p⇩2"
  by (auto simp: independent_def strengthens_def restrict_r_def)

end