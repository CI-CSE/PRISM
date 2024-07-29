
theory Invariant
  imports "../T_04_Composed_operations"
begin
section \<open>Invariant for top\<close>

theorem false_is_invariant: "is_invariant FALSE p"
  oops
  (* by (simp add: FALSE_def invariant_disjoint_from_pre) *)

theorem invariant_implication [simp]: "Pre p \<subseteq> I \<Longrightarrow> Range_p p \<subseteq> I \<Longrightarrow> is_invariant I p"
  by (simp add: is_invariant_def)

theorem invariant_under_equiv: "p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> is_invariant I p\<^sub>1 = is_invariant I p\<^sub>2"
  apply (auto simp: is_invariant_def equiv_def restr_post_def restrict_r_def Range_p_def subset_iff Range_iff)
  apply fastforce
  by fastforce

theorem invariant_disjoint_from_pre: "I \<inter> (Pre p) = {} \<Longrightarrow> is_invariant I p" \<comment> \<open>T78\<close>
  oops
  (* by (auto simp: is_invariant_def Range_p_def restrict_p_def restrict_r_def) *)

theorem invariant_relation_1: "is_invariant I p \<Longrightarrow> is_invariant J p \<Longrightarrow> is_invariant (I \<union> J) p" \<comment> \<open>T79\<close>
  by (auto simp: is_invariant_def Range_p_def restrict_p_def restrict_r_def)

theorem invariant_relation_2: "is_invariant I p \<Longrightarrow> is_invariant J p \<Longrightarrow> is_invariant (I \<inter> J) p" \<comment> \<open>T79\<close>
  by (auto simp: is_invariant_def Range_p_def restrict_p_def restrict_r_def)

value "\<lparr>State={1::nat, 2}, Pre={1}, post={(1,1)}\<rparr>"
value "\<lparr>State={1::nat, 2}, Pre={1}, post={(1,1), (1,2)}\<rparr>"
value "{1::nat}"
value "is_invariant {1::nat} \<lparr>State={1::nat, 2}, Pre={1}, post={(1,1)}\<rparr>"
value "\<lparr>State={1::nat, 2}, Pre={1}, post={(1,1)}\<rparr> \<subseteq>\<^sub>p \<lparr>State={1::nat, 2}, Pre={1}, post={(1,1), (1,2)}\<rparr>"
value "is_invariant {1::nat} (\<lparr>State={1::nat, 2}, Pre={1}, post={(1,1),(1,2)}\<rparr> \<sslash>\<^sub>p (Pre \<lparr>State={1::nat, 2}, Pre={1}, post={(1,1)}\<rparr>))"


theorem invariant_prop_refinement: "is_invariant I p\<^sub>1 \<Longrightarrow> p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> is_invariant I (p\<^sub>2 \<sslash>\<^sub>p (Pre p\<^sub>1))" \<comment> \<open>T80\<close>
  proof -
  assume a1: "is_invariant I p\<^sub>1"
  assume a2: "p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>1"
  from a1 a2 have l1: "Pre (p\<^sub>2 \<sslash>\<^sub>p (Pre p\<^sub>1)) \<subseteq> I"
    by (auto simp: is_invariant_def Range_p_def restrict_p_def)
  from a2 have l2: "Range_p (p\<^sub>2 \<sslash>\<^sub>p (Pre p\<^sub>1)) \<subseteq> Range_p p\<^sub>1"
    by (auto simp: is_invariant_def Range_p_def restrict_p_def restrict_r_def refines_def strengthens_def subset_iff Range_iff)
  from a1 a2 l2 have l3: "Range_p (p\<^sub>2 \<sslash>\<^sub>p (Pre p\<^sub>1)) \<subseteq> I"
    by (auto simp: is_invariant_def)
  show ?thesis
    by (simp add: l3 is_invariant_def l1)
qed
  (* by (auto simp: is_invariant_def Range_p_def restrict_p_def restrict_r_def refines_def weakens_def strengthens_def) *)
  

theorem invariant_prop_refinement_new: "is_invariant I p\<^sub>1 \<Longrightarrow> p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> is_invariant I (p\<^sub>2 \<sslash>\<^sub>p (Pre p\<^sub>1))" \<comment> \<open>T80\<close>
  by (simp add: invariant_prop_refinement)
  (* by (auto simp: is_invariant_def Range_p_def restrict_p_def restrict_r_def refines_def weakens_def strengthens_def) *)

theorem invariant_prop_subprogram: "is_invariant I p\<^sub>1 \<Longrightarrow> p\<^sub>2 \<preceq>\<^sub>p p\<^sub>1 \<Longrightarrow> is_invariant I (p\<^sub>2)" \<comment> \<open>T80\<close>
  apply (auto simp: is_invariant_def)
  apply (auto simp: is_invariant_def subprogram_def weakens_def) [1]
  apply (auto simp: is_invariant_def subprogram_def strengthens_def Range_p_def restrict_r_def subset_iff Range_iff weakens_def) [1]
  by blast
  (* by (auto simp: is_invariant_def Range_p_def subprogram_def restrict_r_def weakens_def strengthens_def restrict_p_def subset_iff Range_iff) *)

theorem invariant_prop_2: "is_invariant I (Fail C)"
  by (auto simp: Fail_def is_invariant_def Range_p_def restrict_r_def)
  (* by (simp add: Fail_def invariant_disjoint_from_pre) *)

theorem invariant_prop_3: "C \<subseteq> I \<Longrightarrow> is_invariant I (Havoc C)"
  by (auto simp: Havoc_def is_invariant_def Range_p_def restrict_p_def restrict_r_def)

theorem invariant_prop_4: "C \<subseteq> I \<Longrightarrow> is_invariant I (Skip C)"
  by (auto simp: is_invariant_def Skip_def Range_p_def restrict_r_def)

(* theorem invariant_prop_4: "is_invariant I (Skip C)" *)
  (* by (auto simp: Skip_def is_invariant_def Range_p_def restrict_p_def restrict_r_def) *)

theorem composition_invariant_preserving: "is_invariant I p\<^sub>1 \<Longrightarrow> is_invariant I p\<^sub>2 \<Longrightarrow> is_invariant I (p\<^sub>1 ; p\<^sub>2)" \<comment> \<open>T81\<close>
  by (auto simp: is_invariant_def composition_def Range_p_def restrict_p_def restrict_r_def restr_post_def )
  
  (* apply (auto simp: is_invariant_def composition_def Range_p_def restrict_p_def restrict_r_def restr_post_def corestrict_r_def) *)
  (* by (smt (verit, ccfv_threshold) Range.intros fst_conv mem_Collect_eq subsetD) *)

theorem choice_invariant_preserving: "is_invariant I p\<^sub>1 \<Longrightarrow> is_invariant I p\<^sub>2 \<Longrightarrow> is_invariant I (p\<^sub>1 \<union>\<^sub>p p\<^sub>2)" \<comment> \<open>T81\<close>
  by (auto simp: is_invariant_def choice_def Range_p_def restrict_p_def restrict_r_def restr_post_def)

theorem choice_invariant_preserving_2: "is_invariant I (p\<^sub>1 \<union>\<^sub>p p\<^sub>2) \<Longrightarrow> is_invariant I p\<^sub>1" \<comment> \<open>NEW\<close>
  using invariant_prop_subprogram program_is_subprogram_of_choice by blast

theorem choice_invariant_preserving_3: "is_invariant I (p\<^sub>1 \<union>\<^sub>p p\<^sub>2) \<Longrightarrow> is_invariant I p\<^sub>2" \<comment> \<open>NEW\<close>
  by (metis choice_commute choice_invariant_preserving_2)

theorem choice_invariant_preserving_4: "is_invariant I (p\<^sub>1 \<union>\<^sub>p p\<^sub>2) = (is_invariant I p\<^sub>1 \<and> is_invariant I p\<^sub>2)" \<comment> \<open>NEW\<close>
  by (meson choice_invariant_preserving choice_invariant_preserving_2 choice_invariant_preserving_3)

theorem restriction_invariant_preserving: "is_invariant I p \<Longrightarrow> is_invariant I (p \<sslash>\<^sub>p C)" \<comment> \<open>T81\<close>
  by (auto simp: is_invariant_def Range_p_def restrict_p_def restrict_r_def)

theorem restriction_invariant_preserving_2: "I \<subseteq> C \<Longrightarrow> is_invariant I (p \<sslash>\<^sub>p C) \<Longrightarrow> is_invariant I p"
  oops
  (* by (auto simp: is_invariant_def restrict_p_def Range_p_def restrict_r_def)  *)

theorem corestriction_invariant_preserving: "is_invariant I p \<Longrightarrow> is_invariant I (p \<setminus>\<^sub>p C)" \<comment> \<open>T81\<close>
  by (auto simp: is_invariant_def Range_p_def corestrict_p_def corestrict_r_def restrict_p_def restrict_r_def)

theorem c_is_invariant: "is_invariant C (p \<setminus>\<^sub>p C)"
  oops
  (* by (auto simp: is_invariant_def Range_p_def corestrict_p_def corestrict_r_def restrict_p_def restrict_r_def) *)

theorem guarded_conditional_invariant_preserving: "is_invariant I p \<Longrightarrow> is_invariant I q \<Longrightarrow> is_invariant I (GC C p D q)"
  by (simp add: guarded_conditional_def choice_invariant_preserving restriction_invariant_preserving)

theorem if_then_else_invariant_preserving: "is_invariant I p \<Longrightarrow> is_invariant I q \<Longrightarrow> is_invariant I (ITE C p q)"
  by (simp add: if_then_else_def choice_invariant_preserving restriction_invariant_preserving)

theorem atomic_conc_invariant_preserving: "is_invariant I p\<^sub>1 \<Longrightarrow> is_invariant I p\<^sub>2 \<Longrightarrow> is_invariant I (p\<^sub>1 || p\<^sub>2)" \<comment> \<open>T81\<close>
  apply (simp add: atomic_conc_def)
  by (meson choice_invariant_preserving composition_invariant_preserving)

theorem non_atomic_conc_invariant_preserving: "is_invariant I p\<^sub>1 \<Longrightarrow> is_invariant I p\<^sub>2 \<Longrightarrow> is_invariant I q \<Longrightarrow> is_invariant I ((p\<^sub>1, p\<^sub>2) \<parallel> q)" \<comment> \<open>T81\<close>
  by (simp add: non_atomic_conc_def atomic_conc_invariant_preserving choice_invariant_preserving composition_invariant_preserving)

theorem fixed_repetition_invariant_preserving: "0<n \<Longrightarrow> is_invariant I p \<Longrightarrow> is_invariant I (p\<^bold>^n)" \<comment> \<open>T81\<close>
  apply (induction n)
   apply (simp)
proof -
  fix n assume a1: "0 < Suc n"
  assume a2: "is_invariant I p"
  assume IH: "0 < n \<Longrightarrow> is_invariant I p \<Longrightarrow> is_invariant I (p \<^bold>^ n)"
  show "is_invariant I (p \<^bold>^ Suc n)"
    apply (cases "n=0")
    using a2 apply (auto simp: is_invariant_def Skip_def composition_def corestrict_r_def Range_p_def restr_post_def restrict_r_def) [1]
  proof -
    assume a3: "n \<noteq> 0"
    from a2 a3 IH have l1: "is_invariant I (p \<^bold>^ n)" by simp
    from a2 l1 composition_invariant_preserving show "is_invariant I (p \<^bold>^ Suc n)" by auto
  qed
qed

(* theorem fixed_repetition_invariant_preserving: " is_invariant I p \<Longrightarrow> is_invariant I (p\<^bold>^n)" \<comment> \<open>T81\<close> *)
  (* apply (induction n) *)
   (* apply (auto simp: fixed_repetition_def is_invariant_def Range_p_def restrict_p_def restrict_r_def S_def Skip_def) [1] *)
  (* by (simp add: composition_invariant_preserving) *)

theorem arbitrary_repetition_invariant_preserving: "0<s \<Longrightarrow> is_invariant I p \<Longrightarrow> is_invariant I (loop p s f)" \<comment> \<open>T81\<close>
  apply (cases "f<s")
proof -
  assume a1: "0 < s"
  assume a2: "is_invariant I p"
  fix f assume a3: "f < s" 
  from a3 have l1: "loop p s f \<equiv>\<^sub>p Fail (S p)"
    by (metis arbitrary_repetition.elims fail_is_equivalent_independant_of_arg)
  from l1 show "is_invariant I (loop p s f)"
    by (simp add: invariant_prop_2 invariant_under_equiv)
next
  assume a1: "0 < s"
  assume a2: "is_invariant I p"
  assume a3: "\<not>f < s"
  from a3 have l1: "s\<le>f" by simp
  show "is_invariant I (loop p s f)"
    apply (induction f)
    using a1 l1 apply (auto simp: is_invariant_def Fail_def Range_p_def restrict_r_def ) [1]
  proof -
    fix f assume IH: "is_invariant I (loop p s f)"
    show "is_invariant I (loop p s (Suc f))"
      apply (cases "\<not>s\<le>f")
      using IH apply (auto simp:) [1]
      apply (simp add: invariant_prop_2)
       apply (metis a1 a2 choice_invariant_preserving fixed_repetition.simps(2) fixed_repetition_invariant_preserving less_Suc_eq_le linorder_neqE_nat)
    proof -
      assume a4: "\<not>\<not> s \<le> f"
      from a4 have l2: "s\<le>f" by simp
      from l1 l2 loop_l3 have l3: "loop p s (Suc f) \<equiv>\<^sub>p p\<^bold>^(Suc f) \<union>\<^sub>p loop p s f " by auto
      from l3 IH show "is_invariant I (loop p s (Suc f))"
        by (metis a2 choice_invariant_preserving_4 fixed_repetition_invariant_preserving invariant_under_equiv less_Suc_eq_0_disj)
    qed
  qed
qed

(* theorem arbitrary_repetition_invariant_preserving: "is_invariant I p \<Longrightarrow> is_invariant I (loop p s f)" \<comment> \<open>T81\<close> *)
  (* apply (induction f) *)
  (* apply (auto simp: arbitrary_repetition.cases) *)
  (* apply (simp add: invariant_prop_2) *)
  (* apply (simp add: invariant_prop_4) *)
  (* apply (simp add: invariant_prop_2) *)
  (* by (simp add: choice_invariant_preserving composition_invariant_preserving fixed_repetition_invariant_preserving) *)

theorem while_support_invariant_preserving: "0<s \<Longrightarrow> is_invariant I a \<Longrightarrow> is_invariant I b \<Longrightarrow> is_invariant I (while_support a C b s f)"
    apply (auto simp: while_support_def)
    apply (cases "s\<le>f")
    apply (simp add: arbitrary_repetition_invariant_preserving composition_invariant_preserving corestriction_invariant_preserving restriction_invariant_preserving)
    by (simp add: arbitrary_repetition_invariant_preserving composition_invariant_preserving corestriction_invariant_preserving restriction_invariant_preserving)
    (* apply (auto simp: while_support_def) *)
    (* apply (cases "s\<le>f") *)
    (* apply (simp add: arbitrary_repetition_invariant_preserving composition_invariant_preserving corestriction_invariant_preserving restriction_invariant_preserving) *)
    (* by (simp add: arbitrary_repetition_invariant_preserving composition_invariant_preserving corestriction_invariant_preserving restriction_invariant_preserving) *)

theorem while_loop_invariant_preserving: "is_invariant I a \<Longrightarrow> is_invariant I b \<Longrightarrow> is_invariant I (while_loop a C b n)" \<comment> \<open>T81\<close>
  oops
  (* by (simp add: arbitrary_repetition_invariant_preserving composition_invariant_preserving corestriction_invariant_preserving restriction_invariant_preserving while_loop_def) *)

theorem inverse_is_not_invariant_preseving: "is_invariant I p \<Longrightarrow> is_invariant I (p\<^sup>-\<^sup>1)"
  by (auto simp: is_invariant_def inverse_def restr_post_def Range_p_def restrict_r_def)
  (* oops *)

theorem true_is_invariant: "S p \<subseteq> C \<Longrightarrow> is_invariant (TRUE C) p"
  by (auto simp: TRUE_def is_invariant_def Range_p_def restrict_p_def restrict_r_def S_def Field_def)

end