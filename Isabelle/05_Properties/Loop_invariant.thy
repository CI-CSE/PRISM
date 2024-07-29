
theory Loop_invariant
  imports "../T_04_Composed_operations" Invariant
begin
section \<open>Loop invariant for top\<close>


theorem false_is_loop_invariant: "is_loop_invariant FALSE a C b"
  oops
  (* by (simp add: FALSE_def invariant_disjoint_from_pre is_loop_invariant_def) *)

theorem true_is_loop_invariant: "S a \<union> S b \<union> C \<subseteq> D \<Longrightarrow> is_loop_invariant (TRUE D) a C b"
  by (auto simp: is_loop_invariant_def is_invariant_def Range_p_def restrict_r_def TRUE_def S_def Field_def restrict_p_def)
  (* oops *)

theorem loop_invariant_is_invariant_of_loop: "0<s \<Longrightarrow> is_loop_invariant I a C b \<Longrightarrow> is_invariant I (loop (b\<sslash>\<^sub>p(-C)) s n)"
  by (simp add: arbitrary_repetition_invariant_preserving is_loop_invariant_def)

theorem loop_correctness: "0 < n \<Longrightarrow> is_loop_invariant I a C b \<Longrightarrow> Range_p (while_loop a C b n) \<subseteq> C \<inter> I"
  apply (auto)
proof -
  assume a1: "is_loop_invariant I a C b"
  fix x assume a2: "x \<in> Range_p (while_loop a C b n)"
  from a1 a2 show "x \<in> C"
    apply (auto simp: while_loop_def)
    by (meson Corestriction.corestrict_prop_1 in_mono range_decreases_composition)
next
  assume a0: "0 < n"
  assume a1: "is_loop_invariant I a C b"
  fix x assume a2: "x \<in> Range_p (while_loop a C b n)"
  from a0 a1 a2 show "x \<in> I"
    apply (induction n)
    apply simp
     (* apply (simp add: while_loop_def) \<comment> \<open>Maybe a lemma\<close> *)
    apply (simp add: is_loop_invariant_def) [1]
    sorry
  (* proof - *)
    (* fix n assume IH: "0 < n \<Longrightarrow> x \<in> Range_p (while_loop a C b n) \<Longrightarrow> x \<in> I" *)
    (* assume a2: "I \<subseteq> Range_p a \<and> is_invariant I (b \<sslash>\<^sub>p (- C))" *)
    (* assume a3: "x \<in> Range_p (while_loop a C b (Suc n))" *)
    (* show " x \<in> I" *)
    (* proof (cases "0 < n") *)
      (* case True *)
      (* assume a4: "0 < n" *)
      (* then show ?thesis sorry *)
    (* next *)
      (* case False *)
      (* assume a4: "\<not> 0 < n" *)
      (* then have l1: "n=0" by simp *)
      (* from l1 a3 have l2: "x \<in> Range_p (while_loop a C b 1)" by simp *)
      (* have l3: "while_loop a C b 1 = a ; (loop (b\<sslash>\<^sub>p(-C)) 0 1)\<setminus>\<^sub>p C" by (simp add: while_loop_def) *)
      (* have l4: "loop (b\<sslash>\<^sub>p(-C)) 0 1 \<equiv>\<^sub>p loop (b\<sslash>\<^sub>p(-C)) 0 0 \<union>\<^sub>p loop (b\<sslash>\<^sub>p(-C)) 1 1" *)
        (* by (metis One_nat_def le_numeral_extra(3) loop_l5 zero_less_one_class.zero_le_one) *)
      (* have l5: "loop (b\<sslash>\<^sub>p(-C)) 0 0 \<equiv>\<^sub>p Skip (S b)" *)
        (* using loop_l1 by auto *)
      (* have l6: "loop (b\<sslash>\<^sub>p(-C)) 1 1 \<equiv>\<^sub>p (b\<sslash>\<^sub>p(-C))\<^bold>^1" *)
        (* using loop_l2_1 by blast *)
      (* have l7: "(b\<sslash>\<^sub>p(-C))\<^bold>^1 \<equiv>\<^sub>p Skip (S b);(b\<sslash>\<^sub>p(-C))" *)
        (* by (simp add: equiv_is_reflexive) *)
      (* have l8: "a ; (loop (b\<sslash>\<^sub>p(-C)) 0 1)\<setminus>\<^sub>p C \<equiv>\<^sub>p a ; ((Skip (S b)) \<union>\<^sub>p (b\<sslash>\<^sub>p(-C)))\<setminus>\<^sub>p C" *)
        (* by (simp add: equals_equiv_relation_3 equivalence_is_maintained_by_choice equivalence_is_maintained_by_composition equivalence_is_maintained_by_corestriction skip_prop_5) *)
      (* from l1 l2 l3 l4 l5 l6 l7 l8 show ?thesis sorry *)
    (* qed *)
  (* qed *)
  (* have l1: "\<forall> i. is_invariant I ((b\<sslash>\<^sub>p(-C))\<^bold>^i)" *)
    (* using a1 fixed_repetition_invariant_preserving is_loop_invariant_def by blast *)
  (* have l2: "I \<subseteq> Range_p a" *)
    (* by (meson a1 is_loop_invariant_def) *)
  (* have l3: "x \<in> Range_p (a ; (loop (b\<sslash>\<^sub>p(-C)) 0 n)\<setminus>\<^sub>p C)" *)
    (* by (metis a2 while_loop_def) *)
  (* have l4: "x \<in> C" *)
    (* by (meson Corestriction.corestrict_prop_1 l3 range_decreases_composition subsetD) *)
  (* from a1 a2 l1 l2 l3 l4 show "x \<in> I" *)
    (* apply (simp add: is_loop_invariant_def while_loop_def is_invariant_def Range_p_def restrict_p_def restrict_r_def corestrict_p_def corestrict_r_def fixed_repetition_def S_def Field_def arbitrary_repetition.elims) *)
    (* sorry *)
qed

end