
theory Loop_invariant
  imports "../T_04_Composed_operations" Invariant
begin
section \<open>Loop invariant for top\<close>


theorem false_is_loop_invariant: "is_loop_invariant FALSE a C b"
  oops

theorem true_is_loop_invariant: "S a \<union> S b \<union> C \<subseteq> D \<Longrightarrow> is_loop_invariant (TRUE D) a C b"
  by (auto simp: is_loop_invariant_def is_invariant_def Range_p_def restrict_r_def TRUE_def S_def Field_def restrict_p_def)

theorem loop_invariant_is_invariant_of_loop: "0<s \<Longrightarrow> is_loop_invariant I a C b \<Longrightarrow> is_invariant I (loop (b\<sslash>\<^sub>p(-C)) s n)"
  by (simp add: arbitrary_repetition_invariant_preserve is_loop_invariant_def)

lemma loop_correct_1: "is_loop_invariant I a C b \<Longrightarrow> Range_p (a ; loop (b \<sslash>\<^sub>p (- C)) n n) \<subseteq> I"
  proof (induction n)
    case 0
    then show ?case by (auto simp: is_loop_invariant_def is_invariant_def composition_def Skip_def restrict_p_def restrict_r_def corestrict_p_def corestrict_r_def Range_p_def restr_post_def)
  next
    case (Suc n)
    assume IH: "is_loop_invariant I a C b \<Longrightarrow> Range_p (a ; loop (b \<sslash>\<^sub>p (- C)) n n) \<subseteq> I"
    assume a2: "is_loop_invariant I a C b"
    from IH a2 have IH2: "Range_p (a ; loop (b \<sslash>\<^sub>p (- C)) n n) \<subseteq> I" by simp
    have l1: "a ; loop (b \<sslash>\<^sub>p (- C)) (Suc n) (Suc n) \<equiv>\<^sub>p (a ; (b \<sslash>\<^sub>p (- C))\<^bold>^n) ; (b \<sslash>\<^sub>p (- C))"
      by (metis compose_assoc equiv_is_reflexive equivalence_is_maintained_by_composition fixed_repetition.simps(2) loop_l2_1)
    then have "\<forall> y \<in> Range_p (a ; (b \<sslash>\<^sub>p (- C))\<^bold>^(Suc n)). y \<in> I"
      by (meson a2 composition_pre fixed_repetition_invariant_preserve in_mono invariant_preserve is_loop_invariant_def range_p_explicit_1)
    then show "Range_p (a ; loop (b \<sslash>\<^sub>p (- C)) (Suc n) (Suc n)) \<subseteq> I"
      using l1 same_range_p_3 by auto
  qed

lemma loop_correct_2: "is_loop_invariant I a C b \<Longrightarrow> Range_p (until_support a C b n n) \<subseteq> I"
  proof (induction n)
    case 0
    then show ?case by (auto simp: until_support_def composition_def Skip_def restrict_p_def restrict_r_def corestrict_p_def corestrict_r_def Range_p_def)
  next
    case (Suc n)
    assume IH: "is_loop_invariant I a C b \<Longrightarrow> Range_p (until_support a C b n n) \<subseteq> I"
    assume a2: "is_loop_invariant I a C b"
    from IH a2 have IH2: "Range_p (until_support a C b n n) \<subseteq> I" by simp
    then have IH_exp: "\<forall>x y. x \<in> Pre a \<and> (x, y) \<in> post (a; ((b\<sslash>\<^sub>p(-C))\<^bold>^n)) \<longrightarrow> y \<in> I"
      by (meson a2 corestriction_invariant_preserve fixed_repetition_invariant_preserve invariant_preserve is_loop_invariant_def)
    then have IH_exp_2: "\<forall>x y. x \<in> Pre a \<and> (x, y) \<in> post (a; ((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc n))) \<longrightarrow> y \<in> I"
      by (meson a2 fixed_repetition_invariant_preserve invariant_preserve is_loop_invariant_def)
    then have IH_exp_3: "\<forall>x y. x \<in> Pre a \<and> (x, y) \<in> post (a; ((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc n)) \<setminus>\<^sub>p C) \<longrightarrow> y \<in> I"
      by (meson a2 corestriction_invariant_preserve fixed_repetition_invariant_preserve invariant_preserve is_loop_invariant_def)
    have l1: "until_support a C b (Suc n) (Suc n) \<equiv>\<^sub>p a; ((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc n)) \<setminus>\<^sub>p C"
      using until_decomp_7 by blast
    then have "\<forall>x y. x \<in> Pre a \<and> (x, y) \<in> post (until_support a C b (Suc n) (Suc n)) \<longrightarrow> y \<in> I"
      by (metis (full_types) IH_exp_3 composition_pre knowing_pre_composition range_p_explicit_1 range_p_explicit_2 same_range_p_3 subsetD until_support_def)
    then show "Range_p (until_support a C b (Suc n) (Suc n)) \<subseteq> I"
      by (metis composition_pre in_mono range_p_explicit_1 subsetI until_support_def)
  qed

lemma loop_correct_3: "s\<le>f \<Longrightarrow> is_loop_invariant I a C b \<Longrightarrow> Range_p (until_support a C b s f) \<subseteq> I"
  apply (induction f)
   apply (smt (verit) in_mono le_numeral_extra(3) loop_correct_2 range_until_loop_2 subsetI until_conncetion)
proof -
  fix f assume IH: "s \<le> f \<Longrightarrow> is_loop_invariant I a C b \<Longrightarrow> Range_p (until_support a C b s f) \<subseteq> I"
  assume a1: "is_loop_invariant I a C b"
  assume a2: " s \<le> Suc f"
  show "Range_p (until_support a C b s (Suc f)) \<subseteq> I"
  proof (cases "s\<le>f")
    case True
    from IH a1 True have l1: "Range_p (until_support a C b s f) \<subseteq> I" by simp
    from True have l2: "until_support a C b s (Suc f) \<equiv>\<^sub>p until_support a C b s f \<union>\<^sub>p until_support a C b (Suc f) (Suc f)"
      by (metis choice_commute until_decomp_4)
    then show ?thesis
      by (smt (verit) l1 a1 choice_range_p_prop_2 loop_correct_2 same_range_p_3 subsetD subsetI)
  next
    case False
    then show ?thesis
      by (metis a1 a2 le_Suc_eq loop_correct_2)
  qed
qed


theorem loop_correct: "is_loop_invariant I a C b \<Longrightarrow> Range_p (until_loop a C b n) \<subseteq> C \<inter> I" \<comment> \<open>Loop_correct\<close>
  apply (auto)
proof -
  assume a1: "is_loop_invariant I a C b"
  fix n x assume a2: "x \<in> Range_p (until_loop a C b n)"
  from a1 a2 show "x \<in> C"
    apply (auto simp: until_loop_def)
    by (meson Corestriction.corestrict_prop_1 in_mono range_decreases_composition)
next
  fix x assume a2: "x \<in> Range_p (until_loop a C b n)"
  assume a1: "is_loop_invariant I a C b"
  
  from a1 a2 have "x \<in> C"
    apply (auto simp: until_loop_def)
    by (meson Corestriction.corestrict_prop_1 in_mono range_decreases_composition)
  from a1 a2 show "x \<in> I"
    by (metis bot_nat_0.extremum in_mono loop_correct_3 until_conncetion)
qed

end