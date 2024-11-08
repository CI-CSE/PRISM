theory Implementation
  imports Definitions Refinement
begin

section "Implementation for top"


lemma implementation_1: "x \<in> X \<Longrightarrow> x \<in> Domain (R) \<Longrightarrow> x \<in> Domain (R \<sslash>\<^sub>r X)"
  by (auto simp: restrict_r_def)

theorem implementation_theorem: "implements p\<^sub>2 p\<^sub>1 \<Longrightarrow> is_feasible p\<^sub>1" \<comment> \<open>Implement_theorem\<close>
proof -
  assume a1: "implements p\<^sub>2 p\<^sub>1"
  have l1: "Pre p\<^sub>1 \<subseteq> Domain (post p\<^sub>2)"
    using a1 by (auto simp: implements_def is_feasible_def refines_def weakens_def)
  have l4: "\<forall>x \<in> Pre p\<^sub>1. x \<in> Domain (post p\<^sub>1)"
    using a1 by (meson Domain_mono l1 implementation_1 implements_def refines_def strengthens_def subsetD weakens_def)
  have l5: "Pre p\<^sub>1 \<subseteq> Domain (post p\<^sub>1)"
    by (simp add: l4 subsetI)
  then show "is_feasible p\<^sub>1"
    by (simp add: is_feasible_def)
qed

lemma implementation_is_reflexive: "is_feasible p\<^sub>1 \<Longrightarrow> implements p\<^sub>1 p\<^sub>1" \<comment> \<open>Implementation_reflexive\<close>
  by (simp add: implements_def refines_is_preorder)
lemma implementation_is_transitive: "implements p\<^sub>1 p\<^sub>2 \<Longrightarrow> implements p\<^sub>2 p\<^sub>3 \<Longrightarrow> implements p\<^sub>1 p\<^sub>3" \<comment> \<open>Implementation_transitive\<close>
  using implements_def refines_is_preorder by blast
lemma implementation_is_antisymetric: "implements p\<^sub>1 p\<^sub>2 \<Longrightarrow> implements p\<^sub>2 p\<^sub>1 \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2" \<comment> \<open>Implementation_antisym\<close>
  using implements_def refines_is_order by blast

end