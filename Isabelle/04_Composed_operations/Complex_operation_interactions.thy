theory Complex_operation_interactions
  imports 
"../T_03_Basic_programs"
"Arbitrary_repetition"
"Atomic_concurrency"
"Big_choice"
"Fixed_repetition"
"Guarded_conditional"
"If_then_else"
"Non_atomic_concurrency"
"Until_loop"
"Until_support"
begin
section \<open>Complex operation interactions for top\<close>


subsubsection \<open>Restriction atomic concurrency\<close>
theorem restriction_distrib_1: "(p\<^sub>1 || p\<^sub>2) \<sslash>\<^sub>p C = p\<^sub>1 \<sslash>\<^sub>p C || p\<^sub>2 \<sslash>\<^sub>p C"
  oops

theorem restriction_distrib_2: "(p\<^sub>1 || p\<^sub>2) \<sslash>\<^sub>p C \<equiv>\<^sub>p (p\<^sub>1 \<sslash>\<^sub>p C ; p\<^sub>2) \<union>\<^sub>p (p\<^sub>2 \<sslash>\<^sub>p C ; p\<^sub>1)" \<comment> \<open>NEW\<close>
  by (metis atomic_conc_def compose_absorb_1 restrict_distrib_3)

subsubsection \<open>Restriction non-atomic concurrency\<close>
theorem restriction_distrib_1: "((p\<^sub>1, p\<^sub>2) \<parallel> q) \<sslash>\<^sub>p C = ((q\<sslash>\<^sub>p C;p\<^sub>1);p\<^sub>2 \<union>\<^sub>p ((p\<^sub>1\<sslash>\<^sub>p C;q);p\<^sub>2)) \<union>\<^sub>p ((p\<^sub>1\<sslash>\<^sub>p C;p\<^sub>2);q)"
  oops
theorem restriction_distrib_2: "((p\<^sub>1, p\<^sub>2) \<parallel> q) \<sslash>\<^sub>p C \<triangleq> ((q\<sslash>\<^sub>p C;p\<^sub>1);p\<^sub>2 \<union>\<^sub>p ((p\<^sub>1\<sslash>\<^sub>p C;q);p\<^sub>2)) \<union>\<^sub>p ((p\<^sub>1\<sslash>\<^sub>p C;p\<^sub>2);q)"
  oops
theorem restriction_distrib_3: "((p\<^sub>1, p\<^sub>2) \<parallel> q) \<sslash>\<^sub>p C \<equiv>\<^sub>p ((q\<sslash>\<^sub>p C;p\<^sub>1);p\<^sub>2 \<union>\<^sub>p ((p\<^sub>1\<sslash>\<^sub>p C;q);p\<^sub>2)) \<union>\<^sub>p ((p\<^sub>1\<sslash>\<^sub>p C;p\<^sub>2);q)"
  apply (auto simp: non_atomic_conc_def)
proof -
  have l1: "((p\<^sub>1 || q) ; p\<^sub>2 \<union>\<^sub>p p\<^sub>1 ; (p\<^sub>2 || q)) \<sslash>\<^sub>p C \<equiv>\<^sub>p ((p\<^sub>1 || q)\<sslash>\<^sub>p C ; p\<^sub>2 \<union>\<^sub>p p\<^sub>1\<sslash>\<^sub>p C ; (p\<^sub>2 || q))"
    by (metis compose_absorb_1 restrict_distrib_3)
  have l2: "((p\<^sub>1 || q)\<sslash>\<^sub>p C ; p\<^sub>2 \<union>\<^sub>p p\<^sub>1\<sslash>\<^sub>p C ; (p\<^sub>2 || q)) \<equiv>\<^sub>p ((p\<^sub>1\<sslash>\<^sub>p C;q \<union>\<^sub>p q\<sslash>\<^sub>p C;p\<^sub>1) ; p\<^sub>2 \<union>\<^sub>p p\<^sub>1\<sslash>\<^sub>p C ; (p\<^sub>2;q \<union>\<^sub>p q;p\<^sub>2))"
    by (metis atomic_conc_def equiv_is_reflexive equivalence_is_maintained_by_choice equivalence_is_maintained_by_composition restriction_distrib_2)
  have l3: "(p\<^sub>1\<sslash>\<^sub>p C;q \<union>\<^sub>p q\<sslash>\<^sub>p C;p\<^sub>1) ; p\<^sub>2 \<union>\<^sub>p p\<^sub>1\<sslash>\<^sub>p C ; (p\<^sub>2;q \<union>\<^sub>p q;p\<^sub>2) \<equiv>\<^sub>p ((p\<^sub>1\<sslash>\<^sub>pC;q);p\<^sub>2\<union>\<^sub>p(q\<sslash>\<^sub>pC;p\<^sub>1);p\<^sub>2)\<union>\<^sub>p((p\<^sub>1\<sslash>\<^sub>pC;p\<^sub>2);q\<union>\<^sub>p(p\<^sub>1\<sslash>\<^sub>pC;q);p\<^sub>2)"
    by (metis compose_assoc compose_distrib1_3 compose_distrib2_3 equivalence_is_maintained_by_choice)
  from choice_assoc_3 have l4: "((p\<^sub>1\<sslash>\<^sub>pC;q);p\<^sub>2\<union>\<^sub>p(q\<sslash>\<^sub>pC;p\<^sub>1);p\<^sub>2)\<union>\<^sub>p((p\<^sub>1\<sslash>\<^sub>pC;p\<^sub>2);q\<union>\<^sub>p(p\<^sub>1\<sslash>\<^sub>pC;q);p\<^sub>2) \<equiv>\<^sub>p (((p\<^sub>1\<sslash>\<^sub>pC;q);p\<^sub>2\<union>\<^sub>p(q\<sslash>\<^sub>pC;p\<^sub>1);p\<^sub>2)\<union>\<^sub>p(p\<^sub>1\<sslash>\<^sub>pC;p\<^sub>2);q)\<union>\<^sub>p(p\<^sub>1\<sslash>\<^sub>pC;q);p\<^sub>2"
    by (metis choice_assoc_1)
  from compose_assoc_3 have l5: "((p\<^sub>1\<sslash>\<^sub>pC;q);p\<^sub>2\<union>\<^sub>p(q\<sslash>\<^sub>pC;p\<^sub>1);p\<^sub>2)\<union>\<^sub>p((p\<^sub>1\<sslash>\<^sub>pC;p\<^sub>2);q\<union>\<^sub>p(p\<^sub>1\<sslash>\<^sub>pC;q);p\<^sub>2) \<equiv>\<^sub>p (((p\<^sub>1\<sslash>\<^sub>pC;(q;p\<^sub>2))\<union>\<^sub>p(q\<sslash>\<^sub>pC;(p\<^sub>1;p\<^sub>2)))\<union>\<^sub>p(p\<^sub>1\<sslash>\<^sub>pC;(p\<^sub>2;q)))\<union>\<^sub>p(p\<^sub>1\<sslash>\<^sub>pC;(q;p\<^sub>2))"
    using l4 by auto
  from l5 have l6: "(((p\<^sub>1\<sslash>\<^sub>pC;(q;p\<^sub>2))\<union>\<^sub>p(q\<sslash>\<^sub>pC;(p\<^sub>1;p\<^sub>2)))\<union>\<^sub>p(p\<^sub>1\<sslash>\<^sub>pC;(p\<^sub>2;q)))\<union>\<^sub>p(p\<^sub>1\<sslash>\<^sub>pC;(q;p\<^sub>2)) \<equiv>\<^sub>p (((p\<^sub>1\<sslash>\<^sub>pC;(q;p\<^sub>2))\<union>\<^sub>p(q\<sslash>\<^sub>pC;(p\<^sub>1;p\<^sub>2)))\<union>\<^sub>p(p\<^sub>1\<sslash>\<^sub>pC;(p\<^sub>2;q)))"
    by (smt (z3) choice_assoc_1 choice_commute choice_idem_3 equals_equiv_relation_3 equivalence_is_maintained_by_choice)
  from l1 l2 l3 l4 l5 l6 show "(p\<^sub>1 ; (p\<^sub>2 || q) \<union>\<^sub>p (p\<^sub>1 || q) ; p\<^sub>2) \<sslash>\<^sub>p C \<equiv>\<^sub>p p\<^sub>1 \<sslash>\<^sub>p C ; (p\<^sub>2 ; q) \<union>\<^sub>p (p\<^sub>1 \<sslash>\<^sub>p C ; (q ; p\<^sub>2) \<union>\<^sub>p q \<sslash>\<^sub>p C ; (p\<^sub>1 ; p\<^sub>2))"
    by (simp add: equiv_def)
qed


subsubsection \<open>Restriction guarded conditional\<close>
theorem cond_distrib2_1: "(GC C\<^sub>1 p C\<^sub>2 q) \<sslash>\<^sub>p D \<triangleq> GC (D \<inter> C\<^sub>1) p (D \<inter> C\<^sub>2) q"
  oops

theorem Cond_distrib2_2: "(GC C\<^sub>1 p C\<^sub>2 q) \<sslash>\<^sub>p D \<equiv>\<^sub>p GC (D \<inter> C\<^sub>1) p (D \<inter> C\<^sub>2) q"
  by (auto simp: equiv_def guarded_conditional_def restrict_p_def restrict_r_def choice_def restr_post_def S_def Field_def)

subsubsection \<open>Restriction If-then-else\<close>
theorem restriction_ite: "(ITE C a b) \<sslash>\<^sub>p D = (ITE C (a\<sslash>\<^sub>pD) (b\<sslash>\<^sub>pD))"
  oops
theorem restriction_ite: "(ITE C a b) \<sslash>\<^sub>p D \<triangleq> (ITE C (a\<sslash>\<^sub>pD) (b\<sslash>\<^sub>pD))"
  oops
theorem restriction_ite: "(ITE C a b) \<sslash>\<^sub>p D \<equiv>\<^sub>p (ITE C (a\<sslash>\<^sub>pD) (b\<sslash>\<^sub>pD))"
  apply (auto simp: if_then_else_def)
  by (metis restrict_distrib_3 restrict_commute)

subsubsection \<open>Restriction fixed repetition\<close>
theorem restriction_fixed_repetition_1: "0<n \<Longrightarrow> (p\<^bold>^Suc n) \<sslash>\<^sub>p C \<equiv>\<^sub>p (p \<sslash>\<^sub>p C);(p\<^bold>^n)"
proof -
  assume a1: "0<n"
  from a1 fixed_rep_decomp_front have l0: "(p \<^bold>^ Suc n) \<equiv>\<^sub>p p;p \<^bold>^ n" by auto
  from a1 have l1: "(p \<^bold>^ Suc n) \<sslash>\<^sub>p C \<equiv>\<^sub>p (p;p \<^bold>^ n) \<sslash>\<^sub>p C"
    using equivalence_is_maintained_by_restriction l0 by auto
  have "(p;p \<^bold>^ n) \<sslash>\<^sub>p C \<equiv>\<^sub>p ((p\<sslash>\<^sub>p C);p \<^bold>^ n)"
    using compose_absorb_3 by auto
  then show ?thesis
    using equiv_is_transitive l1 by auto
qed


theorem restriction_fixed_repetition_2: "is_feasible p \<Longrightarrow> (p\<^bold>^n) \<sslash>\<^sub>p C \<equiv>\<^sub>p (Skip (S p) \<sslash>\<^sub>p C);(p\<^bold>^n)"
  by (metis compose_absorb_1 equivalence_is_maintained_by_restriction skip_compose_l_of_fixed_rep_1)

theorem restriction_fixed_repetition_3:  "(p\<^bold>^n) \<sslash>\<^sub>p C \<equiv>\<^sub>p (Skip C);(p\<^bold>^n)"
  by (simp add: equiv_is_symetric skip_prop_3)

subsubsection \<open>Restriction arbitrary repetition\<close>
theorem "loop p s f \<sslash>\<^sub>p C \<equiv>\<^sub>p Skip C ; loop p s f"
  by (simp add: equiv_is_symetric skip_prop_3)

subsubsection \<open>Restriction until_support\<close>
subsubsection \<open>Restriction until\<close>



subsubsection \<open>Composition atomic concurrency\<close>
theorem composition_refines_atomic_conc_weakens: "weakens (p\<^sub>1||p\<^sub>2) (p\<^sub>1;p\<^sub>2)"
  by (simp add: atomic_conc_def weakens_def)

theorem composition_refines_atomic_conc_strengthens: "strengthens (p\<^sub>1;p\<^sub>2) (p\<^sub>1||p\<^sub>2)"
  by (metis atomic_conc_def program_is_subprogram_of_choice subprogram_def)

theorem composition_refines_atomic_conc: "p\<^sub>1;p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>1||p\<^sub>2"
  oops

theorem composition_is_subprogram_of_atomic_conc: "p\<^sub>1;p\<^sub>2 \<preceq>\<^sub>p p\<^sub>1||p\<^sub>2"
  by (simp add: atomic_conc_def program_is_subprogram_of_choice)

theorem commute_compose: "commute_programs p\<^sub>1 p\<^sub>2 \<Longrightarrow> p\<^sub>1 || p\<^sub>2 \<equiv>\<^sub>p p\<^sub>1 ; p\<^sub>2"
  by (auto simp: commute_programs_def atomic_conc_def choice_def equiv_def restr_post_def composition_def restrict_r_def)

subsubsection \<open>Composition non-atomic concurrency\<close>
subsubsection \<open>Composition If-then-else\<close>
subsubsection \<open>Composition fixed repetition\<close>
subsubsection \<open>Composition arbitrary repetition\<close>
subsubsection \<open>Composition until_support\<close>
subsubsection \<open>Composition until\<close>


subsubsection \<open>Choice atomic concurrency\<close>
theorem concur_distrib1: "p\<^sub>1 || (p\<^sub>2 \<union>\<^sub>p p\<^sub>3) \<equiv>\<^sub>p (p\<^sub>1 || p\<^sub>2) \<union>\<^sub>p (p\<^sub>1 || p\<^sub>3)"
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

theorem concur_distrib2: "(p\<^sub>2 \<union>\<^sub>p p\<^sub>3) || p\<^sub>1 \<equiv>\<^sub>p (p\<^sub>2 || p\<^sub>1) \<union>\<^sub>p (p\<^sub>3 || p\<^sub>1)"
  apply (auto simp: equiv_def atomic_conc_def)
  apply (smt (verit) equiv_def Un_iff atomic_conc_def choice_pre compose_distrib1_3 compose_distrib2_3)
  apply (smt (verit) equiv_def Un_iff atomic_conc_def choice_pre compose_distrib1_3 compose_distrib2_3)
  apply (metis equiv_def UnCI choice_pre compose_distrib1_3)
  apply (metis equiv_def UnCI choice_pre compose_distrib2_3)
  apply (metis equiv_def UnCI choice_pre compose_distrib1_3)
    apply (metis equiv_def UnCI choice_pre compose_distrib2_3)
  apply (metis Definitions.equiv_def atomic_conc_def concur_distrib1 choice_assoc_1)
  by (metis Definitions.equiv_def atomic_conc_def concur_distrib1 choice_assoc_1)
subsubsection \<open>Choice non-atomic concurrency\<close>

subsubsection \<open>Choice guarded conditional\<close>
theorem cond_distrib1_gc_1: "(GC C\<^sub>1 p\<^sub>1 C\<^sub>2 (p\<^sub>2 \<union>\<^sub>p p\<^sub>3)) \<triangleq> (GC C\<^sub>1 p\<^sub>1 C\<^sub>2 p\<^sub>2) \<union>\<^sub>p (GC C\<^sub>1 p\<^sub>1 C\<^sub>2 p\<^sub>3)" \<comment> \<open>T48\<close>
  apply (auto simp: equal_def guarded_conditional_def restrict_p_def restrict_r_def choice_def restr_post_def)
  apply (simp add: S_def Field_def Domain_iff Range_iff)
  apply force
  apply (simp add: S_def Field_def Domain_iff Range_iff)
  by force

theorem cond_distrib1_gc_2: "(GC C\<^sub>1 p\<^sub>1 C\<^sub>2 (p\<^sub>2 \<union>\<^sub>p p\<^sub>3)) \<equiv>\<^sub>p (GC C\<^sub>1 p\<^sub>1 C\<^sub>2 p\<^sub>2) \<union>\<^sub>p (GC C\<^sub>1 p\<^sub>1 C\<^sub>2 p\<^sub>3)" \<comment> \<open>T48\<close>
  by (simp add: equals_equiv_relation_2 cond_distrib1_gc_1)

theorem cond_distrib1_gc_3: "(GC C\<^sub>1 (p\<^sub>1 \<union>\<^sub>p p\<^sub>3) C\<^sub>2 p\<^sub>2) \<triangleq> (GC C\<^sub>1 p\<^sub>1 C\<^sub>2 p\<^sub>2) \<union>\<^sub>p (GC C\<^sub>1 p\<^sub>3 C\<^sub>2 p\<^sub>2)" \<comment> \<open>T48\<close>
  by (metis cond_commute_1 cond_distrib1_gc_1)

theorem cond_distrib1_gc_4: "(GC C\<^sub>1 (p\<^sub>1 \<union>\<^sub>p p\<^sub>3) C\<^sub>2 p\<^sub>2) \<equiv>\<^sub>p (GC C\<^sub>1 p\<^sub>1 C\<^sub>2 p\<^sub>2) \<union>\<^sub>p (GC C\<^sub>1 p\<^sub>3 C\<^sub>2 p\<^sub>2)" \<comment> \<open>T48\<close>
  using cond_distrib1_gc_3 inverse_equality_1 by blast

subsubsection \<open>Choice If-then-else\<close>
theorem cond_distrib1_ite_1: "(ITE C p\<^sub>1 (p\<^sub>2 \<union>\<^sub>p p\<^sub>3)) \<triangleq> (ITE C p\<^sub>1 p\<^sub>2) \<union>\<^sub>p (ITE C p\<^sub>1 p\<^sub>3)" \<comment> \<open>T48\<close>
  apply (auto simp: equal_def if_then_else_def restrict_p_def restrict_r_def choice_def restr_post_def)
  apply (simp add: S_def Field_def Domain_iff Range_iff)
  apply force
  apply (simp add: S_def Field_def Domain_iff Range_iff)
  by force

theorem cond_distrib1_ite_2: "(ITE C p\<^sub>1 (p\<^sub>2 \<union>\<^sub>p p\<^sub>3)) \<equiv>\<^sub>p (ITE C p\<^sub>1 p\<^sub>2) \<union>\<^sub>p (ITE C p\<^sub>1 p\<^sub>3)" \<comment> \<open>T48\<close>
  using inverse_equality_1 cond_distrib1_ite_1 by blast

theorem cond_distrib1_ite_3: "(ITE C (p\<^sub>1 \<union>\<^sub>p p\<^sub>2) p\<^sub>3) \<triangleq> (ITE C p\<^sub>1 p\<^sub>3) \<union>\<^sub>p (ITE C p\<^sub>2 p\<^sub>3)" \<comment> \<open>T48\<close>
  by (metis cond_distrib1_ite_1 cond_swap)

theorem cond_distrib1_ite_4: "(ITE C (p\<^sub>1 \<union>\<^sub>p p\<^sub>2) p\<^sub>3) \<equiv>\<^sub>p (ITE C p\<^sub>1 p\<^sub>3) \<union>\<^sub>p (ITE C p\<^sub>2 p\<^sub>3)" \<comment> \<open>T48\<close>
  using inverse_equality_1 cond_distrib1_ite_3 by blast

subsubsection \<open>Choice fixed repetition\<close>   
subsubsection \<open>Choice arbitrary repetition\<close> 
subsubsection \<open>Choice until_support\<close>
subsubsection \<open>Choice until\<close>

subsubsection \<open>Corestriction atomic concurrency\<close>
theorem corestriction_distrib: "(p\<^sub>1 || p\<^sub>2) \<setminus>\<^sub>p C = p\<^sub>1 \<setminus>\<^sub>p C || p\<^sub>2 \<setminus>\<^sub>p C"
  oops

theorem corestriction_distributes_not_over_atomic_conc: "(p\<^sub>1 || p\<^sub>2) \<setminus>\<^sub>p C \<equiv>\<^sub>p p\<^sub>1 ; p\<^sub>2\<setminus>\<^sub>p C  \<union>\<^sub>p p\<^sub>2 ; p\<^sub>1 \<setminus>\<^sub>p C" \<comment> \<open>NEW\<close>
  by (metis equiv_def atomic_conc_def choice_def composition_state corestrict_union corestrict_compose corestriction_state)


subsubsection \<open>Corestriction non-atomic concurrency\<close>

subsubsection \<open>Corestriction guarded conditional\<close>

subsubsection \<open>Corestriction If-then-else\<close>
subsubsection \<open>Corestriction fixed repetition\<close>
subsubsection \<open>Corestriction arbitrary repetition\<close> 
subsubsection \<open>Corestriction until_support\<close>
subsubsection \<open>Corestriction until\<close>

subsubsection \<open>Unsafe composition atomic concurrency\<close>

subsubsection \<open>Unsafe composition non-atomic concurrency\<close>

subsubsection \<open>Unsafe composition guarded conditional\<close>

subsubsection \<open>Unsafe composition If-then-else\<close>
subsubsection \<open>Unsafe composition fixed repetition\<close>
subsubsection \<open>Unsafe composition arbitrary repetition\<close> 
subsubsection \<open>Unsafe composition until_support\<close>
subsubsection \<open>Unsafe composition until\<close>

subsubsection \<open>Atomic concurrency non-atomic concurreny\<close>

lemma atomic_refines_non_atomic_1: "((p\<^sub>1; p\<^sub>2) || q) = (p\<^sub>1 ; p\<^sub>2) ; q \<union>\<^sub>p q ; (p\<^sub>1 ; p\<^sub>2)"
  by (simp add: atomic_conc_def)

lemma atomic_refines_non_atomic_2: "((p\<^sub>1, p\<^sub>2) \<parallel> q) = ((p\<^sub>1 ; q) ; p\<^sub>2 \<union>\<^sub>p (q ; p\<^sub>1) ; p\<^sub>2)  \<union>\<^sub>p ((p\<^sub>1 ; p\<^sub>2) ; q \<union>\<^sub>p (p\<^sub>1 ; q) ; p\<^sub>2)"
  apply (simp add: atomic_conc_def non_atomic_conc_def)
  by (smt (verit) Definitions.equiv_def choice_assoc_1 choice_def choice_state compose_assoc compose_distrib1_3 compose_distrib2_1 composition_state inf_sup_aci(5) inf_sup_aci(7) sup.left_idem)

lemma atomic_refines_non_atomic_weakens: "weakens ((p\<^sub>1, p\<^sub>2) \<parallel> q) ((p\<^sub>1; p\<^sub>2) || q)"
  apply (auto simp: non_atomic_conc_def atomic_conc_def equal_def weakens_def)
  apply (metis Definitions.equiv_def UnCI choice_pre compose_distrib1_3)
  by (simp add: compose_distrib2_1)

lemma atomic_refines_non_atomic_strengthens: "strengthens ((p\<^sub>1; p\<^sub>2) || q) ((p\<^sub>1, p\<^sub>2) \<parallel> q)"
  apply (auto simp: non_atomic_conc_def atomic_conc_def strengthens_def restr_post_def restrict_r_def)
  apply (auto simp: choice_def composition_def corestrict_r_def S_def restr_post_def restrict_r_def) [8]
  apply (auto simp: composition_def restrict_r_def restr_post_def corestrict_r_def relcomp_unfold) [1]
  by (auto simp: choice_def composition_def corestrict_r_def S_def restr_post_def restrict_r_def relcomp_unfold Domain_iff) [7]

theorem coarse_fine: "((p\<^sub>1; p\<^sub>2) || q) \<subseteq>\<^sub>p ((p\<^sub>1, p\<^sub>2) \<parallel> q)" \<comment> \<open>Coarse_fine\<close>
  oops \<comment> \<open>This does not hold. When the previous lemmas hold\<close>

theorem atomic_subprogram_non_atomic: "((p\<^sub>1; p\<^sub>2) || q) \<preceq>\<^sub>p ((p\<^sub>1, p\<^sub>2) \<parallel> q)" \<comment> \<open>T56\<close>
  apply (auto simp: subprogram_def extends_def)
  apply (simp add: atomic_refines_non_atomic_weakens)
  by (simp add: atomic_refines_non_atomic_strengthens)

lemma atomic_refines_non_atomic_weakens_2: "weakens ((p\<^sub>1, p\<^sub>2) \<parallel> q) (q || (p\<^sub>1; p\<^sub>2))"
  by (metis atomic_conc_commutative_1 atomic_refines_non_atomic_weakens)

lemma atomic_refines_non_atomic_strengthens_2: "strengthens (q || (p\<^sub>1; p\<^sub>2)) ((p\<^sub>1, p\<^sub>2) \<parallel> q)"
  by (metis atomic_conc_commutative_1 atomic_refines_non_atomic_strengthens)

theorem atomic_subprogram_non_atomic_2: "(q || (p\<^sub>1; p\<^sub>2)) \<preceq>\<^sub>p ((p\<^sub>1, p\<^sub>2) \<parallel> q)" \<comment> \<open>T56\<close>
  apply (auto simp: subprogram_def extends_def)
  apply (simp add: atomic_refines_non_atomic_weakens_2)
  by (simp add: atomic_refines_non_atomic_strengthens_2)

theorem exchange_law1: "p\<^sub>1 ; (p\<^sub>2 || q) \<preceq>\<^sub>p ((p\<^sub>1, p\<^sub>2) \<parallel> q)" \<comment> \<open>Exchange_law1\<close>
  apply (auto simp: non_atomic_conc_def)
  by (simp add: program_is_subprogram_of_choice)

theorem exchange_law2: "p\<^sub>1 ; (p\<^sub>2 || q) \<preceq>\<^sub>p ((p\<^sub>1, p\<^sub>2) \<parallel> q)" \<comment> \<open>Exchange_law2\<close>
  apply (auto simp: non_atomic_conc_def)
  by (simp add: program_is_subprogram_of_choice)

subsubsection \<open>Atomic concurrency inverse\<close>

subsubsection \<open>Atomic concurrency guarded conditional\<close>
theorem cond_distrib1_conc_gc: "(GC C\<^sub>1 p\<^sub>1 C\<^sub>2 (p\<^sub>2 || p\<^sub>3)) \<equiv>\<^sub>p (GC C\<^sub>1 p\<^sub>1 C\<^sub>2 p\<^sub>2) || (GC C\<^sub>1 p\<^sub>1 C\<^sub>2 p\<^sub>3)" \<comment> \<open>Cond_distrib1\<close>
  oops \<comment> \<open>p1;p1 can only happen right\<close>

subsubsection \<open>Atomic concurrency If-then-else\<close>
subsubsection \<open>Atomic concurrency fixed repetition\<close>
subsubsection \<open>Atomic concurrency arbitrary repetition\<close> 
subsubsection \<open>Atomic concurrency until_support\<close>
subsubsection \<open>Atomic concurrency until\<close>

subsubsection \<open>Non-atomic concurrency inverse\<close>

subsubsection \<open>Non-atomic concurrency guarded conditional\<close>
theorem cond_distrib1_conc_ite: "(ITE C p\<^sub>1 (p\<^sub>2 || p\<^sub>3)) \<equiv>\<^sub>p (ITE C p\<^sub>1 p\<^sub>2) || (ITE C p\<^sub>1 p\<^sub>3)" \<comment> \<open>Cond_distrib1\<close>
  oops \<comment> \<open>p1;p1 can only happen right\<close>


subsubsection \<open>Non-atomic concurrency If-then-else\<close>
subsubsection \<open>Non-atomic concurrency fixed repetition\<close>
subsubsection \<open>Non-atomic concurrency arbitrary repetition\<close> 
subsubsection \<open>Non-atomic concurrency composition until_support\<close>
subsubsection \<open>Non-atomic concurrency composition until\<close>

subsubsection \<open>Inverse guarded conditional\<close>

subsubsection \<open>Inverse If-then-else\<close>
subsubsection \<open>Inverse fixed repetition\<close>
subsubsection \<open>Inverse arbitrary repetition\<close> 
subsubsection \<open>Inverse until_support\<close>
subsubsection \<open>Inverse until\<close>

subsubsection \<open>Guarded conditional If-then-else\<close>
theorem guard_ifthenelse: "ITE C p\<^sub>1 p\<^sub>2 = GC C p\<^sub>1 (-C) p\<^sub>2" \<comment> \<open>Guard_ifthenelse\<close>
  by (auto simp: guarded_conditional_def if_then_else_def)
subsubsection \<open>Guarded conditional fixed repetition\<close>
subsubsection \<open>Guarded conditional arbitrary repetition\<close> 
subsubsection \<open>Guarded conditional until_support\<close>
subsubsection \<open>Guarded conditional until\<close>
subsubsection \<open>If-then-else fixed repetition\<close>
subsubsection \<open>If-then-else arbitrary repetition\<close> 
subsubsection \<open>If-then-else until_support\<close>
subsubsection \<open>If-then-else until\<close>
subsubsection \<open>Fixed repetition arbitrary repetition\<close> 
subsubsection \<open>Fixed repetition until_support\<close>

subsubsection \<open>Fixed repetition until\<close>
subsubsection \<open>Arbitrary repetition until_support\<close>
subsubsection \<open>Arbitrary repetition until\<close>
lemma until_def_lemma: "until_loop a C b n \<equiv>\<^sub>p a;(loop (b\<sslash>\<^sub>p(-C)) 0 n)\<setminus>\<^sub>pC"
  by (simp add: equals_equiv_relation_3 until_loop_def)
subsubsection \<open>until_support until\<close> 



end