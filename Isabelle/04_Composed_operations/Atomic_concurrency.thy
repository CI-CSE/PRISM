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
  oops
theorem atomic_conc_idempotence_1 [simp]: "p || p \<triangleq> p ; p"
  oops
theorem atomic_conc_idempotence_2 [simp]: "p || p \<equiv>\<^sub>p p ; p"
  by (auto simp: atomic_conc_def equiv_def composition_def choice_def restr_post_def restrict_r_def)
theorem atomic_conc_distributes_left_over_choice: "p\<^sub>1 || (p\<^sub>2 \<union>\<^sub>p p\<^sub>3) \<equiv>\<^sub>p (p\<^sub>1 || p\<^sub>2) \<union>\<^sub>p (p\<^sub>1 || p\<^sub>3)"
  apply (auto simp: atomic_conc_def)
proof -
  have l1: "p\<^sub>1 ; (p\<^sub>2 \<union>\<^sub>p p\<^sub>3) \<equiv>\<^sub>p (p\<^sub>1 ; p\<^sub>2 \<union>\<^sub>p p\<^sub>1 ; p\<^sub>3)"
    by (simp add: compose_distrib1_3)
  have l2: "(p\<^sub>2 \<union>\<^sub>p p\<^sub>3) ; p\<^sub>1 \<equiv>\<^sub>p (p\<^sub>2 ; p\<^sub>1 \<union>\<^sub>p p\<^sub>3 ; p\<^sub>1)"
    by (simp add: compose_distrib2_3)
  have l3: "(p\<^sub>1 ; p\<^sub>2 \<union>\<^sub>p p\<^sub>1 ; p\<^sub>3) \<union>\<^sub>p (p\<^sub>2 ; p\<^sub>1 \<union>\<^sub>p p\<^sub>3 ; p\<^sub>1) \<equiv>\<^sub>p (p\<^sub>1 ; p\<^sub>2 \<union>\<^sub>p p\<^sub>2 ; p\<^sub>1) \<union>\<^sub>p (p\<^sub>1 ; p\<^sub>3 \<union>\<^sub>p p\<^sub>3 ; p\<^sub>1)"
    by (metis choice_assoc_1 choice_assoc_3 choice_commute)
  from l1 l2 l3 show "p\<^sub>1 ; (p\<^sub>2 \<union>\<^sub>p p\<^sub>3) \<union>\<^sub>p (p\<^sub>2 \<union>\<^sub>p p\<^sub>3) ; p\<^sub>1 \<equiv>\<^sub>p p\<^sub>1 ; p\<^sub>2 \<union>\<^sub>p (p\<^sub>2 ; p\<^sub>1 \<union>\<^sub>p (p\<^sub>1 ; p\<^sub>3 \<union>\<^sub>p p\<^sub>3 ; p\<^sub>1))"
    by (metis choice_assoc_1 choice_commute equivalence_is_maintained_by_choice)
qed

theorem atomic_conc_distributes_right_over_choice: "(p\<^sub>2 \<union>\<^sub>p p\<^sub>3) || p\<^sub>1 \<equiv>\<^sub>p (p\<^sub>2 || p\<^sub>1) \<union>\<^sub>p (p\<^sub>3 || p\<^sub>1)"
  apply (auto simp: equiv_def atomic_conc_def)
  apply (smt (verit) equiv_def Un_iff atomic_conc_def choice_pre compose_distrib1_3 compose_distrib2_3)
  apply (smt (verit) equiv_def Un_iff atomic_conc_def choice_pre compose_distrib1_3 compose_distrib2_3)
  apply (metis equiv_def UnCI choice_pre compose_distrib1_3)
  apply (metis equiv_def UnCI choice_pre compose_distrib2_3)
  apply (metis equiv_def UnCI choice_pre compose_distrib1_3)
    apply (metis equiv_def UnCI choice_pre compose_distrib2_3)
  apply (metis Definitions.equiv_def atomic_conc_def atomic_conc_distributes_left_over_choice choice_assoc_1)
  by (metis Definitions.equiv_def atomic_conc_def atomic_conc_distributes_left_over_choice choice_assoc_1)

theorem composition_refines_atomic_conc_weakens: "weakens (p\<^sub>1||p\<^sub>2) (p\<^sub>1;p\<^sub>2)"
  by (simp add: atomic_conc_def weakens_def)

theorem composition_refines_atomic_conc_strengthens: "strengthens (p\<^sub>1;p\<^sub>2) (p\<^sub>1||p\<^sub>2)"
  by (metis Un_Int_eq(3) Un_iff atomic_conc_def char_rel_def char_rel_restriction choice_post_2 choice_pre restr_post_def restrict_p_def select_convs(2) select_convs(3) strengthens_def subsetI)

theorem composition_refines_atomic_conc: "p\<^sub>1;p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>1||p\<^sub>2"
  oops

theorem composition_is_subprogram_of_atomic_conc: "p\<^sub>1;p\<^sub>2 \<preceq>\<^sub>p p\<^sub>1||p\<^sub>2"
  by (simp add: atomic_conc_def program_is_subprogram_of_choice)

theorem atomic_commute_1: "commute p\<^sub>1 p\<^sub>2 \<Longrightarrow> p\<^sub>1 || p\<^sub>2 \<equiv>\<^sub>p p\<^sub>1 ; p\<^sub>2"
  by (auto simp: commute_def atomic_conc_def choice_def equiv_def restr_post_def composition_def restrict_r_def)

theorem atomic_conc_feasible_preserving: "is_feasible p\<^sub>1 \<Longrightarrow> is_feasible p\<^sub>2 \<Longrightarrow> is_feasible (p\<^sub>1 || p\<^sub>2)"
  apply (simp add: atomic_conc_def)
  by (auto simp: union_feasible compose_feasible)

theorem atomic_conc_refinement_safe: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> (q\<^sub>1 || q\<^sub>2) \<subseteq>\<^sub>p (p\<^sub>1 || p\<^sub>2)"
  oops \<comment> \<open>Is dependent on refinement safety of composition and choice\<close>
end