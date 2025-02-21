
theory Invariant
  imports "../T_04_Composed_operations"
begin
section \<open>Invariant for top\<close>

theorem invariant_disjoint_from_pre: "I \<inter> (Pre p) = {} \<Longrightarrow> is_invariant I p" \<comment> \<open>Inv_prop1\<close>
  by (auto simp: is_invariant_def Range_p_def restrict_p_def restrict_r_def)

theorem false_is_invariant: "is_invariant FALSE p"
  by (simp add: FALSE_def invariant_disjoint_from_pre)

theorem equiv_inv: "p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> is_invariant I p\<^sub>1 = is_invariant I p\<^sub>2" \<comment> \<open>Equiv_inv\<close>
  apply (auto simp: is_invariant_def equiv_def restr_post_def restrict_r_def)
   apply (auto simp add: restrict_p_def restrict_r_def)
  by (auto simp: Range_p_def restrict_r_def)

theorem invariant_relation_1: "is_invariant I p \<Longrightarrow> is_invariant J p \<Longrightarrow> is_invariant (I \<union> J) p" \<comment> \<open>Inv_prop1\<close>
  by (auto simp: is_invariant_def Range_p_def restrict_p_def restrict_r_def)

theorem invariant_relation_2: "is_invariant I p \<Longrightarrow> is_invariant J p \<Longrightarrow> is_invariant (I \<inter> J) p" \<comment> \<open>Inv_prop1\<close>
  by (auto simp: is_invariant_def Range_p_def restrict_p_def restrict_r_def)

value "\<lparr>State={1::nat, 2}, Pre={1}, post={(1,1)}\<rparr>"
value "\<lparr>State={1::nat, 2}, Pre={1}, post={(1,1), (1,2)}\<rparr>"
value "{1::nat}"
value "is_invariant {1::nat} \<lparr>State={1::nat, 2}, Pre={1}, post={(1,1)}\<rparr>"
value "\<lparr>State={1::nat, 2}, Pre={1}, post={(1,1)}\<rparr> \<sqsubseteq>\<^sub>p \<lparr>State={1::nat, 2}, Pre={1}, post={(1,1), (1,2)}\<rparr>"
value "is_invariant {1::nat} (\<lparr>State={1::nat, 2}, Pre={1}, post={(1,1),(1,2)}\<rparr> \<sslash>\<^sub>p (Pre \<lparr>State={1::nat, 2}, Pre={1}, post={(1,1)}\<rparr>))"


theorem invariant_refinement: "is_invariant I p\<^sub>1 \<Longrightarrow> p\<^sub>2 \<sqsubseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> is_invariant I (p\<^sub>2 \<sslash>\<^sub>p (Pre p\<^sub>1))" \<comment> \<open>Inv_prop2\<close>
  (* proof - *)
  (* assume a1: "is_invariant I p\<^sub>1" *)
  (* assume a2: "p\<^sub>2 \<sqsubseteq>\<^sub>p p\<^sub>1" *)
  (* from a1 a2 have l1: "Pre (p\<^sub>2 \<sslash>\<^sub>p (Pre p\<^sub>1)) \<subseteq> I" *)
    (* by (auto simp: is_invariant_def Range_p_def restrict_p_def) *)
  (* from a2 have l2: "Range_p (p\<^sub>2 \<sslash>\<^sub>p (Pre p\<^sub>1)) \<subseteq> Range_p p\<^sub>1" *)
    (* by (auto simp: is_invariant_def Range_p_def restrict_p_def restrict_r_def refines_def strengthens_def subset_iff Range_iff) *)
  (* from a1 a2 l2 have l3: "Range_p (p\<^sub>2 \<sslash>\<^sub>p (Pre p\<^sub>1)) \<subseteq> I" *)
    (* by (auto simp: is_invariant_def) *)
  (* show ?thesis *)
    (* by (simp add: l3 is_invariant_def l1) *)
(* qed *)
  by (auto simp: is_invariant_def Range_p_def restrict_p_def restrict_r_def refines_def weakens_def strengthens_def)

theorem invariant_prop_specialize: "is_invariant I p\<^sub>1 \<Longrightarrow> p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> is_invariant I (p\<^sub>2)" \<comment> \<open>Inv_prop3\<close>
  (* apply (auto simp: is_invariant_def) *)
  (* apply (auto simp: is_invariant_def specialize_def weakens_def) [1] *)
  (* apply (auto simp: is_invariant_def specialize_def strengthens_def Range_p_def restrict_r_def subset_iff Range_iff weakens_def) [1] *)
  (* by blast *)
  apply (simp add: is_invariant_def Range_p_def specialize_def restrict_r_def weakens_def strengthens_def restrict_p_def extends_def)
  apply (auto simp: S_def Range_iff Field_def Domain_iff Un_def)
  by fastforce

theorem invariant_prop_2: "is_invariant I (Fail C)"
  (* by (auto simp: Fail_def is_invariant_def Range_p_def restrict_r_def) *)
  by (simp add: Fail_def invariant_disjoint_from_pre)

theorem invariant_prop_3: "C \<subseteq> I \<Longrightarrow> is_invariant I (Havoc C)"
  by (auto simp: Havoc_def is_invariant_def Range_p_def restrict_p_def restrict_r_def)

(* theorem invariant_prop_4: "C \<subseteq> I \<Longrightarrow> is_invariant I (Skip C)" *)
  (* by (auto simp: is_invariant_def Skip_def Range_p_def restrict_r_def) *)

theorem invariant_prop_4: "is_invariant I (Skip C)"
  by (auto simp: Skip_def is_invariant_def Range_p_def restrict_p_def restrict_r_def)

theorem composition_invariant_preserve: "is_invariant I p\<^sub>1 \<Longrightarrow> is_invariant I p\<^sub>2 \<Longrightarrow> is_invariant I (p\<^sub>1 ; p\<^sub>2)" \<comment> \<open>Inv_preserving\<close>
  (* by (auto simp: is_invariant_def composition_def Range_p_def restrict_p_def restrict_r_def restr_post_def ) *)
  apply (auto simp: is_invariant_def composition_def Range_p_def restrict_p_def restrict_r_def restr_post_def corestrict_r_def)
  by (smt (verit, ccfv_threshold) Range.intros fst_conv mem_Collect_eq subsetD)

theorem choice_invariant_preserve: "is_invariant I p\<^sub>1 \<Longrightarrow> is_invariant I p\<^sub>2 \<Longrightarrow> is_invariant I (p\<^sub>1 \<union>\<^sub>p p\<^sub>2)" \<comment> \<open>Inv_preserving\<close>
  by (auto simp: is_invariant_def choice_def Range_p_def restrict_p_def restrict_r_def restr_post_def)

theorem choice_invariant_preserve_2: "is_invariant I (p\<^sub>1 \<union>\<^sub>p p\<^sub>2) \<Longrightarrow> is_invariant I p\<^sub>1" \<comment> \<open>NEW\<close>
  using invariant_prop_specialize program_is_specialize_of_choice by blast

theorem choice_invariant_preserve_3: "is_invariant I (p\<^sub>1 \<union>\<^sub>p p\<^sub>2) \<Longrightarrow> is_invariant I p\<^sub>2" \<comment> \<open>NEW\<close>
  by (metis choice_commute choice_invariant_preserve_2)

theorem choice_invariant_preserve_4: "is_invariant I (p\<^sub>1 \<union>\<^sub>p p\<^sub>2) = (is_invariant I p\<^sub>1 \<and> is_invariant I p\<^sub>2)" \<comment> \<open>NEW\<close>
  by (meson choice_invariant_preserve choice_invariant_preserve_2 choice_invariant_preserve_3)

theorem restriction_invariant_preserve: "is_invariant I p \<Longrightarrow> is_invariant I (p \<sslash>\<^sub>p C)" \<comment> \<open>Inv_preserving\<close>
  by (auto simp: is_invariant_def Range_p_def restrict_p_def restrict_r_def)

theorem restriction_invariant_preserve_2: "I \<subseteq> C \<Longrightarrow> is_invariant I (p \<sslash>\<^sub>p C) \<Longrightarrow> is_invariant I p"
  (* oops *)
  by (auto simp: is_invariant_def restrict_p_def Range_p_def restrict_r_def)

theorem corestriction_invariant_preserve: "is_invariant I p \<Longrightarrow> is_invariant I (p \<setminus>\<^sub>p C)" \<comment> \<open>Inv_preserving\<close>
  by (auto simp: is_invariant_def Range_p_def corestrict_p_def corestrict_r_def restrict_p_def restrict_r_def)

theorem c_is_invariant: "is_invariant C (p \<setminus>\<^sub>p C)"
  (* oops *)
  by (auto simp: is_invariant_def Range_p_def corestrict_p_def corestrict_r_def restrict_p_def restrict_r_def)

theorem guarded_conditional_invariant_preserve: "is_invariant I p \<Longrightarrow> is_invariant I q \<Longrightarrow> is_invariant I (GC [(C, p), (D, q)])" \<comment> \<open>Gen_inv\<close>
  by (simp add: guarded_conditional_def choice_invariant_preserve restriction_invariant_preserve invariant_prop_2)

theorem if_then_else_invariant_preserve: "is_invariant I p \<Longrightarrow> is_invariant I q \<Longrightarrow> is_invariant I (ITE C p q)" \<comment> \<open>Inv_preserving\<close>
  by (simp add: if_then_else_def choice_invariant_preserve restriction_invariant_preserve)

(*
theorem atomic_conc_invariant_preserve: "is_invariant I p\<^sub>1 \<Longrightarrow> is_invariant I p\<^sub>2 \<Longrightarrow> is_invariant I ([p\<^sub>1] \<parallel> p\<^sub>2)" \<comment> \<open>Gen_inv\<close>
  apply (simp add: non_atomic_conc_def)
  by (meson choice_invariant_preserve composition_invariant_preserve)
*)

(*
theorem non_atomic_conc_invariant_preserve: "is_invariant I p\<^sub>1 \<Longrightarrow> is_invariant I p\<^sub>2 \<Longrightarrow> is_invariant I q \<Longrightarrow> is_invariant I ([p\<^sub>1, p\<^sub>2] \<parallel> q)" \<comment> \<open>Gen_inv\<close>
  by (simp add: non_atomic_conc_def atomic_conc_invariant_preserve choice_invariant_preserve composition_invariant_preserve)
*)
(* theorem fixed_repetition_invariant_preserve: "0<n \<Longrightarrow> is_invariant I p \<Longrightarrow> is_invariant I (p\<^bold>^n)" \<comment> \<open>Gen_inv\<close> *)
  (* apply (induction n) *)
   (* apply (simp) *)
(* proof - *)
  (* fix n assume a1: "0 < Suc n" *)
  (* assume a2: "is_invariant I p" *)
  (* assume IH: "0 < n \<Longrightarrow> is_invariant I p \<Longrightarrow> is_invariant I (p \<^bold>^ n)" *)
  (* show "is_invariant I (p \<^bold>^ Suc n)" *)
    (* apply (cases "n=0") *)
    (* using a2 apply (auto simp: is_invariant_def Skip_def composition_def corestrict_r_def Range_p_def restr_post_def restrict_r_def) [1] *)
  (* proof - *)
    (* assume a3: "n \<noteq> 0" *)
    (* from a2 a3 IH have l1: "is_invariant I (p \<^bold>^ n)" by simp *)
    (* from a2 l1 composition_invariant_preserve show "is_invariant I (p \<^bold>^ Suc n)" by auto *)
  (* qed *)
(* qed *)

theorem fixed_repetition_invariant_preserve: " is_invariant I p \<Longrightarrow> is_invariant I (p\<^bold>^n)" \<comment> \<open>Gen_inv\<close>
  apply (induction n)
  apply (auto simp: fixed_repetition_def is_invariant_def Range_p_def restrict_p_def restrict_r_def S_def Skip_def) [1]
  by (simp add: composition_invariant_preserve)

(* theorem arbitrary_repetition_invariant_preserve: "0<s \<Longrightarrow> is_invariant I p \<Longrightarrow> is_invariant I (loop p s f)" \<comment> \<open>General_invariant\<close> *)
  (* apply (cases "f<s") *)
(* proof - *)
  (* assume a1: "0 < s" *)
  (* assume a2: "is_invariant I p" *)
  (* fix f assume a3: "f < s"  *)
  (* from a3 have l1: "loop p s f \<equiv>\<^sub>p Fail (S p)" *)
    (* by (metis arbitrary_repetition.elims fail_equiv) *)
  (* from l1 show "is_invariant I (loop p s f)" *)
    (* by (simp add: invariant_prop_2 equiv_inv) *)
(* next *)
  (* assume a1: "0 < s" *)
  (* assume a2: "is_invariant I p" *)
  (* assume a3: "\<not>f < s" *)
  (* from a3 have l1: "s\<le>f" by simp *)
  (* show "is_invariant I (loop p s f)" *)
    (* apply (induction f) *)
    (* using a1 l1 apply (auto simp: is_invariant_def Fail_def Range_p_def restrict_r_def ) [1] *)
  (* proof - *)
    (* fix f assume IH: "is_invariant I (loop p s f)" *)
    (* show "is_invariant I (loop p s (Suc f))" *)
      (* apply (cases "\<not>s\<le>f") *)
      (* using IH apply (auto simp:) [1] *)
      (* apply (simp add: invariant_prop_2) *)
       (* apply (metis a1 a2 choice_invariant_preserve fixed_repetition.simps(2) fixed_repetition_invariant_preserve less_Suc_eq_le linorder_neqE_nat) *)
    (* proof - *)
      (* assume a4: "\<not>\<not> s \<le> f" *)
      (* from a4 have l2: "s\<le>f" by simp *)
      (* from l1 l2 loop_l3 have l3: "loop p s (Suc f) \<equiv>\<^sub>p p\<^bold>^(Suc f) \<union>\<^sub>p loop p s f " by auto *)
      (* from l3 IH show "is_invariant I (loop p s (Suc f))" *)
        (* by (metis a2 choice_invariant_preserve_4 fixed_repetition_invariant_preserve equiv_inv less_Suc_eq_0_disj) *)
    (* qed *)
  (* qed *)
(* qed *)

theorem arbitrary_repetition_invariant_preserve: "is_invariant I p \<Longrightarrow> is_invariant I (loop p s f)" \<comment> \<open>Gen_inv\<close>
  apply (induction f)
  apply (auto simp: arbitrary_repetition.cases)
  apply (simp add: invariant_prop_2)
  apply (simp add: invariant_prop_4 restriction_invariant_preserve)
  apply (simp add: invariant_prop_2)
  by (simp add: choice_invariant_preserve composition_invariant_preserve fixed_repetition_invariant_preserve)

theorem until_support_invariant_preserve: "0<s \<Longrightarrow> is_invariant I a \<Longrightarrow> is_invariant I b \<Longrightarrow> is_invariant I (until_support a C b s f)" \<comment> \<open>Gen_inv\<close>
    apply (auto simp: until_support_def)
    apply (cases "s\<le>f")
    apply (simp add: arbitrary_repetition_invariant_preserve composition_invariant_preserve corestriction_invariant_preserve restriction_invariant_preserve)
    by (simp add: arbitrary_repetition_invariant_preserve composition_invariant_preserve corestriction_invariant_preserve restriction_invariant_preserve)

theorem until_loop_invariant_preserve: "is_invariant I a \<Longrightarrow> is_invariant I b \<Longrightarrow> is_invariant I (until_loop a C b n)" \<comment> \<open>Gen_inv\<close>
  (* oops *)
  by (simp add: arbitrary_repetition_invariant_preserve composition_invariant_preserve corestriction_invariant_preserve restriction_invariant_preserve until_loop_def)

(* theorem inverse_is_not_invariant_preseving: "is_invariant I p \<Longrightarrow> is_invariant I (p\<^sup>-\<^sup>1)" \<comment> \<open>General_invariant\<close> *)
  (* by (auto simp: is_invariant_def inverse_def restr_post_def Range_p_def restrict_r_def) *)

theorem inverse_is_not_invariant_preseving: "Pre p \<subseteq> I \<Longrightarrow> is_invariant I p \<Longrightarrow> is_invariant I (p\<^sup>-\<^sup>1)" \<comment> \<open>Gen_inv\<close>
  by (auto simp: is_invariant_def inverse_def restr_post_def Range_p_def restrict_r_def restrict_p_def)

theorem true_is_invariant: "S p \<subseteq> C \<Longrightarrow> is_invariant (TRUE C) p"
  by (auto simp: TRUE_def is_invariant_def Range_p_def restrict_p_def restrict_r_def S_def Field_def)

theorem invariant_exp: "is_invariant I b \<Longrightarrow> x \<in> Pre b \<Longrightarrow> (x,y) \<in> post b  \<Longrightarrow> x \<in> I \<Longrightarrow> y \<in> I"
  apply (auto simp: is_invariant_def restrict_p_def Range_p_def restrict_r_def)
  by fastforce

theorem invariant_preserve: "is_invariant I b \<Longrightarrow> Range_p a \<subseteq> I \<Longrightarrow> x \<in> Pre a \<Longrightarrow> (x,y) \<in> post (a;b) \<Longrightarrow> y \<in> I"
  apply (auto simp: is_invariant_def Range_p_def composition_def restr_post_def restrict_p_def restrict_r_def)
  by fastforce


end