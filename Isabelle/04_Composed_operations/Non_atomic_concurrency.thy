theory Non_atomic_concurrency
  imports "../T_03_Basic_programs" "Atomic_concurrency"
begin
section \<open>Non-Atomic concurrency for top\<close>

theorem non_atomic_conc_S [simp]: "S ((p\<^sub>1,p\<^sub>2)\<parallel>q) = (S p\<^sub>1 \<union> S p\<^sub>2) \<union> S q"
  by (auto simp: non_atomic_conc_def atomic_conc_def)
theorem non_atomic_conc_definition_1: "(p\<^sub>1, p\<^sub>2) \<parallel> q = ((q;p\<^sub>1);p\<^sub>2 \<union>\<^sub>p ((p\<^sub>1;q);p\<^sub>2)) \<union>\<^sub>p ((p\<^sub>1;p\<^sub>2);q)"
  apply (auto simp: non_atomic_conc_def atomic_conc_def equal_def choice_def restr_post_def)
  apply (auto simp: S_def composition_def restr_post_def restrict_r_def corestrict_r_def Field_def) [5]
  apply (auto simp: composition_def restrict_r_def corestrict_r_def restr_post_def Domain_iff) [3]
  apply (auto simp: composition_def restrict_r_def corestrict_r_def restr_post_def Domain_iff relcomp_unfold) [2]
  apply (simp add: restrict_r_def composition_def restr_post_def corestrict_r_def relcomp_unfold Domain_iff)
  apply (smt (z3))
  apply (simp add: restrict_r_def composition_def restr_post_def corestrict_r_def relcomp_unfold Domain_iff)
  apply auto[1]
  apply (simp add: restrict_r_def composition_def restr_post_def corestrict_r_def relcomp_unfold Domain_iff)
  by blast

lemma non_atomic_conc_definition_2: "(p\<^sub>1, p\<^sub>2) \<parallel> q \<triangleq> ((q;p\<^sub>1);p\<^sub>2 \<union>\<^sub>p ((p\<^sub>1;q);p\<^sub>2)) \<union>\<^sub>p ((p\<^sub>1;p\<^sub>2);q)"
  by (simp add: equals_equiv_relation_1 non_atomic_conc_definition_1)

lemma non_atomic_conc_definition_3: "(p\<^sub>1, p\<^sub>2) \<parallel> q \<equiv>\<^sub>p ((q;p\<^sub>1);p\<^sub>2 \<union>\<^sub>p ((p\<^sub>1;q);p\<^sub>2)) \<union>\<^sub>p ((p\<^sub>1;p\<^sub>2);q)"
  by (simp add: equals_equiv_relation_3 non_atomic_conc_definition_1)

theorem non_atomic_conc_feasible_preserving: "is_feasible p\<^sub>1 \<Longrightarrow> is_feasible p\<^sub>2 \<Longrightarrow> is_feasible q \<Longrightarrow> is_feasible ((p\<^sub>1, p\<^sub>2) \<parallel> q)"
  by (simp add: non_atomic_conc_def atomic_conc_feasible_preserving union_feasible compose_feasible)

theorem atomic_conc_refinement_safe: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> q\<^sub>3 \<subseteq>\<^sub>p p\<^sub>3 \<Longrightarrow> ((q\<^sub>1, q\<^sub>2) \<parallel> q\<^sub>3) \<subseteq>\<^sub>p ((p\<^sub>1, p\<^sub>2) \<parallel> p\<^sub>3)"
  oops \<comment> \<open>Is dependent on refinement safety of composition and choice\<close>
end