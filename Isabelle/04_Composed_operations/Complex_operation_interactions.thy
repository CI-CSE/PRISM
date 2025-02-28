theory Complex_operation_interactions
  imports 
"../T_03_Basic_programs"
"Arbitrary_repetition"
"Atomic_concurrency"
"Big_choice"
"Fixed_repetition"
"Guarded_conditional"
"If_then_else"
"Until_loop"
"Until_support"
begin
section \<open>Complex operation interactions for top\<close>



subsubsection \<open>Restriction guarded conditional\<close>
theorem cond_distrib2_1: "GC [(C\<^sub>1, p), (C\<^sub>2, q)] \<sslash>\<^sub>p D \<triangleq> GC [((D \<inter> C\<^sub>1), p), ((D \<inter> C\<^sub>2), q)]"
  oops

theorem Cond_distrib2_2: "GC [(C\<^sub>1, p), (C\<^sub>2, q)] \<sslash>\<^sub>p D \<equiv>\<^sub>p GC [((D \<inter> C\<^sub>1), p), ((D \<inter> C\<^sub>2), q)]"
  by (auto simp: equiv_def guarded_conditional_def restrict_p_def restrict_r_def choice_def restr_post_def S_def Field_def Fail_def)

subsubsection \<open>Restriction If-then-else\<close>
theorem restriction_ite: "(ITE C a b) \<sslash>\<^sub>p D = (ITE C (a\<sslash>\<^sub>pD) (b\<sslash>\<^sub>pD))"
  oops
theorem restriction_ite: "(ITE C a b) \<sslash>\<^sub>p D \<triangleq> (ITE C (a\<sslash>\<^sub>pD) (b\<sslash>\<^sub>pD))"
  oops
theorem restriction_ite: "(ITE C a b) \<sslash>\<^sub>p D \<equiv>\<^sub>p (ITE C (a\<sslash>\<^sub>pD) (b\<sslash>\<^sub>pD))"
  apply (auto simp: if_then_else_def)
  by (metis restrict_distrib_3 restrict_commute)

subsubsection \<open>Restriction fixed repetition\<close>
theorem restriction_fixed_repetition_1: "0<n \<Longrightarrow> (p\<^bold>^(Suc n)) \<sslash>\<^sub>p C \<equiv>\<^sub>p (p \<sslash>\<^sub>p C);(p\<^bold>^n)"
proof -
  assume a1: "0<n"
  from a1 fixed_rep_decomp_front have l0: "(p \<^bold>^ (Suc n)) \<equiv>\<^sub>p p;p \<^bold>^ n" by auto
  from a1 have l1: "(p \<^bold>^ (Suc n)) \<sslash>\<^sub>p C \<equiv>\<^sub>p (p;p \<^bold>^ n) \<sslash>\<^sub>p C"
    using restriction_equiv l0 by auto
  have "(p;p \<^bold>^ n) \<sslash>\<^sub>p C \<equiv>\<^sub>p ((p\<sslash>\<^sub>p C);p \<^bold>^ n)"
    using compose_absorb_3 by auto
  then show ?thesis
    using equiv_is_transitive l1 by auto
qed


theorem restriction_fixed_repetition_2: "is_feasible p \<Longrightarrow> (p\<^bold>^n) \<sslash>\<^sub>p C \<equiv>\<^sub>p (Skip (S p) \<sslash>\<^sub>p C);(p\<^bold>^n)"
  by (metis compose_absorb_1 restriction_equiv skip_compose_l_of_fixed_rep_1)

theorem restriction_fixed_repetition_3:  "(p\<^bold>^n) \<sslash>\<^sub>p C \<equiv>\<^sub>p (Skip C);(p\<^bold>^n)"
  by (simp add: Skip_comprestrict equiv_is_symetric)

subsubsection \<open>Restriction arbitrary repetition\<close>
theorem "loop p s f \<sslash>\<^sub>p C \<equiv>\<^sub>p Skip C ; loop p s f"
  by (simp add: Skip_comprestrict equiv_is_symetric)

subsubsection \<open>Restriction until_support\<close>
subsubsection \<open>Restriction until\<close>


subsubsection \<open>Composition non-atomic concurrency\<close>
subsubsection \<open>Composition If-then-else\<close>
subsubsection \<open>Composition fixed repetition\<close>
subsubsection \<open>Composition arbitrary repetition\<close>
subsubsection \<open>Composition until_support\<close>
subsubsection \<open>Composition until\<close>


subsubsection \<open>Choice guarded conditional\<close>
theorem cond_distrib1_gc_1: "GC [(C\<^sub>1, p\<^sub>1), (C\<^sub>2, (p\<^sub>2 \<union>\<^sub>p p\<^sub>3))] \<triangleq> (GC [(C\<^sub>1, p\<^sub>1), (C\<^sub>2, p\<^sub>2)]) \<union>\<^sub>p (GC [(C\<^sub>1, p\<^sub>1), (C\<^sub>2, p\<^sub>3)])" \<comment> \<open>T48\<close>
  apply (auto simp: equal_def guarded_conditional_def restrict_p_def restrict_r_def choice_def restr_post_def)
  apply (simp add: S_def Field_def Domain_iff Range_iff)
  apply force
  apply (simp add: S_def Field_def Domain_iff Range_iff)
  by force

theorem cond_distrib1_gc_2: "GC [(C\<^sub>1, p\<^sub>1), (C\<^sub>2, (p\<^sub>2 \<union>\<^sub>p p\<^sub>3))] \<equiv>\<^sub>p (GC [(C\<^sub>1, p\<^sub>1), (C\<^sub>2, p\<^sub>2)]) \<union>\<^sub>p (GC [(C\<^sub>1, p\<^sub>1), (C\<^sub>2, p\<^sub>3)])" \<comment> \<open>T48\<close>
  using cond_distrib1_gc_1 inverse_equality_1 by blast

theorem cond_distrib1_gc_3: "GC [(C\<^sub>1, (p\<^sub>1 \<union>\<^sub>p p\<^sub>3)), (C\<^sub>2, p\<^sub>2)] \<triangleq> GC [(C\<^sub>1, p\<^sub>1), ( C\<^sub>2, p\<^sub>2)] \<union>\<^sub>p GC [(C\<^sub>1, p\<^sub>3), ( C\<^sub>2, p\<^sub>2)]" \<comment> \<open>T48\<close>
  by (metis Cons_eq_appendI append_Nil cond_distrib1_gc_1 cond_helper_1)

theorem cond_distrib1_gc_4: "GC [(C\<^sub>1, (p\<^sub>1 \<union>\<^sub>p p\<^sub>3)), ( C\<^sub>2, p\<^sub>2)] \<equiv>\<^sub>p GC [(C\<^sub>1, p\<^sub>1), ( C\<^sub>2, p\<^sub>2)] \<union>\<^sub>p GC [(C\<^sub>1, p\<^sub>3), ( C\<^sub>2, p\<^sub>2)]" \<comment> \<open>T48\<close>
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
subsubsection \<open>Atomic concurrency inverse\<close>

subsubsection \<open>Atomic concurrency guarded conditional\<close>
subsubsection \<open>Atomic concurrency If-then-else\<close>
subsubsection \<open>Atomic concurrency fixed repetition\<close>
subsubsection \<open>Atomic concurrency arbitrary repetition\<close> 
subsubsection \<open>Atomic concurrency until_support\<close>
subsubsection \<open>Atomic concurrency until\<close>

subsubsection \<open>Non-atomic concurrency inverse\<close>

subsubsection \<open>Non-atomic concurrency guarded conditional\<close>


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
theorem guard_ifthenelse: "ITE C p\<^sub>1 p\<^sub>2 = GC [(C, p\<^sub>1), ((-C), p\<^sub>2)]" \<comment> \<open>Guard_ifthenelse\<close>
  by (auto simp: guarded_conditional_def if_then_else_def Fail_def choice_def restr_post_def S_def restrict_r_def restrict_p_def Field_def)

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