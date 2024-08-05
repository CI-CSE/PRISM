theory Atomic_concurrency
  imports "../T_03_Basic_programs"
begin
section \<open>Atomic concurrency for top\<close>


theorem atomic_conc_S [simp]: "S (p\<^sub>1 || p\<^sub>2) = S p\<^sub>1 \<union> S p\<^sub>2"
  by (auto simp: atomic_conc_def)

theorem atomic_conc_commutative_1: "p\<^sub>1 || p\<^sub>2 = p\<^sub>2 || p\<^sub>1" \<comment> \<open>T46 1\<close>
  by (auto simp: atomic_conc_def choice_def)
theorem atomic_conc_commutative_2: "p\<^sub>1 || p\<^sub>2 \<triangleq> p\<^sub>2 || p\<^sub>1"
  by (simp add: atomic_conc_commutative_1 equal_is_reflexive)
theorem atomic_conc_commutative_3: "p\<^sub>1 || p\<^sub>2 \<equiv>\<^sub>p p\<^sub>2 || p\<^sub>1"
  by (simp add: atomic_conc_commutative_1 equiv_is_reflexive)


theorem atomic_conc_associative: "(p\<^sub>1 || p\<^sub>2) || p\<^sub>3 \<equiv>\<^sub>p p\<^sub>1 || (p\<^sub>2 || p\<^sub>3)" \<comment> \<open>p1;p3;p2 is only only on the right possible\<close>
  apply (simp add: atomic_conc_def)
  oops
theorem atomic_conc_idempotence_1 [simp]: "p || p \<triangleq> p ; p"
  oops
theorem atomic_conc_idempotence_2 [simp]: "p || p \<equiv>\<^sub>p p ; p"
  by (auto simp: atomic_conc_def equiv_def composition_def choice_def restr_post_def restrict_r_def)

theorem atomic_conc_feasible_preserving: "is_feasible p\<^sub>1 \<Longrightarrow> is_feasible p\<^sub>2 \<Longrightarrow> is_feasible (p\<^sub>1 || p\<^sub>2)"
  apply (simp add: atomic_conc_def)
  by (auto simp: union_feasible compose_feasible)

theorem atomic_conc_refinement_safe: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> (q\<^sub>1 || q\<^sub>2) \<subseteq>\<^sub>p (p\<^sub>1 || p\<^sub>2)"
  oops \<comment> \<open>Is dependent on refinement safety of composition and choice\<close>
end