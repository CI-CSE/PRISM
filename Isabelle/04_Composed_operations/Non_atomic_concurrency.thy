theory Non_atomic_concurrency
  imports "../T_03_Basic_programs" "Atomic_concurrency"
begin
section \<open>Non-Atomic concurrency for top\<close>

theorem non_atomic_conc_S [simp]: "S ((p\<^sub>1,p\<^sub>2)\<parallel>q) = (S p\<^sub>1 \<union> S p\<^sub>2) \<union> S q"
  by (auto simp: non_atomic_conc_def atomic_conc_def)
theorem fine_grain_1: "(p\<^sub>1, p\<^sub>2) \<parallel> q = ((q;p\<^sub>1);p\<^sub>2 \<union>\<^sub>p ((p\<^sub>1;q);p\<^sub>2)) \<union>\<^sub>p ((p\<^sub>1;p\<^sub>2);q)"
proof -
  have state_lemma: "State ((p\<^sub>1, p\<^sub>2) \<parallel> q) = State (((q;p\<^sub>1);p\<^sub>2 \<union>\<^sub>p ((p\<^sub>1;q);p\<^sub>2)) \<union>\<^sub>p ((p\<^sub>1;p\<^sub>2);q))"
    apply (auto simp: non_atomic_conc_def atomic_conc_def)
    apply (smt (verit) Program.select_convs(1) atomic_conc_S atomic_conc_def choice_def compose_assoc compose_distrib2_1 composition_state)
    by (smt (verit) Program.select_convs(1) atomic_conc_S atomic_conc_def choice_def compose_assoc compose_distrib2_1 composition_state)
  have pre_lemma: "Pre ((p\<^sub>1, p\<^sub>2) \<parallel> q) = Pre (((q;p\<^sub>1);p\<^sub>2 \<union>\<^sub>p ((p\<^sub>1;q);p\<^sub>2)) \<union>\<^sub>p ((p\<^sub>1;p\<^sub>2);q))"
    apply (auto simp: non_atomic_conc_def atomic_conc_def)
    apply (smt (verit) Definitions.equiv_def Un_iff choice_pre compose_distrib1_3)
    apply (simp add: compose_distrib2_1)
    apply (metis Definitions.equiv_def UnCI choice_pre compose_distrib1_3)
    apply (simp add: compose_distrib2_1)
    by (simp add: compose_distrib2_1)
  have post_lemma: "post ((p\<^sub>1, p\<^sub>2) \<parallel> q) = post (((q;p\<^sub>1);p\<^sub>2 \<union>\<^sub>p ((p\<^sub>1;q);p\<^sub>2)) \<union>\<^sub>p ((p\<^sub>1;p\<^sub>2);q))"
    apply (auto simp: non_atomic_conc_def atomic_conc_def restr_post_def)
    apply (metis Un_iff char_rel_choice char_rel_composition char_rel_def choice_post_2 choice_pre relcomp_distrib restr_post_def)
    apply (simp add: compose_distrib2_1 restr_post_def)
    apply (metis Un_iff char_rel_choice char_rel_composition char_rel_def relcomp_distrib)
    by (simp add: compose_distrib2_1 restr_post_def)
  from state_lemma pre_lemma post_lemma show "((p\<^sub>1, p\<^sub>2) \<parallel> q) = ((q ; p\<^sub>1) ; p\<^sub>2 \<union>\<^sub>p (p\<^sub>1 ; q) ; p\<^sub>2) \<union>\<^sub>p (p\<^sub>1 ; p\<^sub>2) ; q"
    by (auto simp: non_atomic_conc_def atomic_conc_def)
qed

lemma fine_grain_2: "(p\<^sub>1, p\<^sub>2) \<parallel> q \<triangleq> ((q;p\<^sub>1);p\<^sub>2 \<union>\<^sub>p ((p\<^sub>1;q);p\<^sub>2)) \<union>\<^sub>p ((p\<^sub>1;p\<^sub>2);q)"
  by (simp add: equals_equiv_relation_1 fine_grain_1)

lemma fine_grain_3: "(p\<^sub>1, p\<^sub>2) \<parallel> q \<equiv>\<^sub>p ((q;p\<^sub>1);p\<^sub>2 \<union>\<^sub>p ((p\<^sub>1;q);p\<^sub>2)) \<union>\<^sub>p ((p\<^sub>1;p\<^sub>2);q)"
  by (simp add: equals_equiv_relation_3 fine_grain_1)

theorem non_atomic_conc_feasible_preserving: "is_feasible p\<^sub>1 \<Longrightarrow> is_feasible p\<^sub>2 \<Longrightarrow> is_feasible q \<Longrightarrow> is_feasible ((p\<^sub>1, p\<^sub>2) \<parallel> q)"
  by (simp add: non_atomic_conc_def atomic_conc_feasible_preserving union_feasible compose_feasible)

theorem atomic_conc_refinement_safe: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> q\<^sub>3 \<subseteq>\<^sub>p p\<^sub>3 \<Longrightarrow> ((q\<^sub>1, q\<^sub>2) \<parallel> q\<^sub>3) \<subseteq>\<^sub>p ((p\<^sub>1, p\<^sub>2) \<parallel> p\<^sub>3)"
  oops \<comment> \<open>Is dependent on refinement safety of composition and choice\<close>

theorem "((ys@[x])@xs) \<parallel>\<^sub>G q \<equiv>\<^sub>p (ys@([x]@xs)) \<parallel>\<^sub>G q"
  by (simp add: equiv_is_reflexive)
end