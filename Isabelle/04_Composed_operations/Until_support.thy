theory Until_support
  imports 
"../T_03_Basic_programs"
"Arbitrary_repetition"
begin
section \<open>Until support for top\<close>

subsection \<open>Step cases\<close>
lemma until_decomp_1: "until_support a C b 0 n \<equiv>\<^sub>p until_support a C b 0 0 \<union>\<^sub>p until_support a C b (Suc 0) n"
  apply (simp add: until_support_def)
proof (induction n)
  case 0
  have right_1: "loop (b \<sslash>\<^sub>p (- C)) (Suc 0) 0 \<setminus>\<^sub>p C \<equiv>\<^sub>p Fail (S b)"
    by (metis Fail.fail_compose corestrict_compose corestriction_state fail_equiv loop_l2_01)
  from right_1 have right_2: "a; loop (b \<sslash>\<^sub>p (- C)) (Suc 0) 0 \<setminus>\<^sub>p C \<equiv>\<^sub>p Fail (S b)"
    by (metis equiv_def composition_def corestriction_state fail_compose_r loop_l2_01 restriction_state)
  from right_2 have right_3: "a ; Skip (S b) \<setminus>\<^sub>p C \<union>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) (Suc 0) 0 \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; Skip (S b) \<setminus>\<^sub>p C \<union>\<^sub>p Fail (S b)"
    by (simp add: equiv_is_reflexive choice_equiv)
  from right_3 have right_4: "a ; Skip (S b) \<setminus>\<^sub>p C \<union>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) (Suc 0) 0 \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; Skip (S b) \<setminus>\<^sub>p C"
    by (meson equiv_is_transitive fail_choice_r)
  have l1: "a ; Fail (S b) \<setminus>\<^sub>p C \<equiv>\<^sub>p Fail (S b)"
    using right_2 by auto
  from right_3 show ?case
    by (auto simp: equiv_def Skip_def Fail_def composition_def corestrict_p_def corestrict_r_def choice_def restr_post_def restrict_r_def)
next
  case (Suc n)
  have l2: "a ; loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n) \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; ((Skip (S (b \<sslash>\<^sub>p (- C)))) \<sslash>\<^sub>p (Pre (b \<sslash>\<^sub>p (- C))) \<union>\<^sub>p loop (b \<sslash>\<^sub>p (- C)) (Suc 0) (Suc n)) \<setminus>\<^sub>p C"
    by (metis One_nat_def equals_equiv_relation_3 composition_equiv equivalence_is_maintained_by_corestriction loop_l6 zero_less_Suc)
  have l3: "a ; (Skip (Pre (b \<sslash>\<^sub>p (- C))) \<union>\<^sub>p loop (b \<sslash>\<^sub>p (- C)) (Suc 0) (Suc n)) \<setminus>\<^sub>p C \<equiv>\<^sub>p ((a ; Skip (Pre (b \<sslash>\<^sub>p (- C)))) \<union>\<^sub>p (a ; loop (b \<sslash>\<^sub>p (- C)) (Suc 0) (Suc n))) \<setminus>\<^sub>p C"
    using corestrict_compose equiv_is_symetric equivalence_is_maintained_by_corestriction equiv_is_transitive compose_distrib1_3
    by (smt (verit, del_insts))
  then have l4: "((a ; Skip (Pre (b \<sslash>\<^sub>p (- C)))) \<union>\<^sub>p (a ; loop (b \<sslash>\<^sub>p (- C)) (Suc 0) (Suc n))) \<setminus>\<^sub>p C \<equiv>\<^sub>p ((a ; Skip (Pre (b \<sslash>\<^sub>p (- C))) \<setminus>\<^sub>p C) \<union>\<^sub>p (a ; loop (b \<sslash>\<^sub>p (- C)) (Suc 0) (Suc n) \<setminus>\<^sub>p C))"
    by (metis corestrict_choice_3 corestrict_compose)
  from compose_distrib1_3 l2 show ?case
    using equiv_is_transitive l3 l4
    by (smt (verit) choice_commute equiv_is_symetric restriction_state until_simplification_1) 
qed

lemma until_decomp_2: "until_support a C b 0 (Suc n) \<equiv>\<^sub>p until_support a C b 0 n \<union>\<^sub>p until_support a C b (Suc n) (Suc n)"
proof (induction n)
  case 0
  then show ?case
    using until_decomp_1 by auto
next
  case (Suc n)
  assume IH: "until_support a C b 0 (Suc n) \<equiv>\<^sub>p until_support a C b 0 n \<union>\<^sub>p until_support a C b (Suc n) (Suc n)"
  have t2: "until_support a C b 0 (Suc (Suc n)) \<equiv>\<^sub>p (a ; (loop (b\<sslash>\<^sub>p(-C)) 0 (Suc n))\<setminus>\<^sub>p C) \<union>\<^sub>p (a ; (loop (b\<sslash>\<^sub>p(-C)) (Suc (Suc n)) (Suc (Suc n)))\<setminus>\<^sub>p C)"
    apply (auto simp: until_support_def)
  proof -
    have l1: "a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ n ; (b \<sslash>\<^sub>p (- C) ; b \<sslash>\<^sub>p (- C))) \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; (Fail (S b) \<union>\<^sub>p (b \<sslash>\<^sub>p (- C)) \<^bold>^ n ; (b \<sslash>\<^sub>p (- C) ; b \<sslash>\<^sub>p (- C))) \<setminus>\<^sub>p C"
      by (simp add: equiv_is_reflexive equiv_is_symetric composition_equiv equivalence_is_maintained_by_corestriction fail_choice_l)
    have l2: "a ; (loop (b \<sslash>\<^sub>p (- C)) 0 n \<union>\<^sub>p b \<sslash>\<^sub>p (- C) ; (b \<sslash>\<^sub>p (- C)) \<^bold>^ n) \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; (loop (b \<sslash>\<^sub>p (- C)) 0 n \<union>\<^sub>p b \<sslash>\<^sub>p (- C) ; (b \<sslash>\<^sub>p (- C)) \<^bold>^ n) \<setminus>\<^sub>p C"
      by (simp add: equiv_is_reflexive)
    from l1 l2 until_simplification_1 show "a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ n ; (b \<sslash>\<^sub>p (- C) ; b \<sslash>\<^sub>p (- C)) \<union>\<^sub>p (loop (b \<sslash>\<^sub>p (- C)) 0 n \<union>\<^sub>p (b \<sslash>\<^sub>p (- C)) \<^bold>^ n ; b \<sslash>\<^sub>p (- C))) \<setminus>\<^sub>p C \<equiv>\<^sub>p
    a ; (loop (b \<sslash>\<^sub>p (- C)) 0 n \<union>\<^sub>p (b \<sslash>\<^sub>p (- C)) \<^bold>^ n ; b \<sslash>\<^sub>p (- C)) \<setminus>\<^sub>p C \<union>\<^sub>p a ; (Fail (S b) \<union>\<^sub>p (b \<sslash>\<^sub>p (- C)) \<^bold>^ n ; (b \<sslash>\<^sub>p (- C) ; b \<sslash>\<^sub>p (- C))) \<setminus>\<^sub>p C"
      by (smt (verit, ccfv_threshold) choice_commute equiv_is_symetric equiv_is_transitive choice_equiv)
  qed
  then show "until_support a C b 0 (Suc (Suc n)) \<equiv>\<^sub>p until_support a C b 0 (Suc n) \<union>\<^sub>p until_support a C b (Suc (Suc n)) (Suc (Suc n))"
    by (simp add: until_support_def)
qed

lemma until_decomp_3: "s \<le> f \<Longrightarrow> until_support a C b s f \<equiv>\<^sub>p until_support a C b s s \<union>\<^sub>p until_support a C b (Suc s) f"
  apply (simp add: until_support_def)
proof (induction s)
  case 0
  from until_decomp_1 show ?case
    by (metis until_support_def)
next
  case (Suc s)
  assume IH: "s \<le> f \<Longrightarrow>  a ; loop (b \<sslash>\<^sub>p (- C)) s f \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) s s \<setminus>\<^sub>p C \<union>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) (Suc s) f \<setminus>\<^sub>p C"
  assume a1: "Suc s \<le> f"
  have IH2: "a ; loop (b \<sslash>\<^sub>p (- C)) s f \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) s s \<setminus>\<^sub>p C \<union>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) (Suc s) f \<setminus>\<^sub>p C"
    by (simp add: IH Suc_leD a1)
  from IH2 have l1: "a ; loop (b \<sslash>\<^sub>p (- C)) (Suc s) f \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; (loop (b \<sslash>\<^sub>p (- C)) (Suc s) (Suc s) \<union>\<^sub>p loop (b \<sslash>\<^sub>p (- C)) (Suc (Suc s)) f) \<setminus>\<^sub>p C"
    by (metis a1 equiv_is_reflexive composition_equiv equivalence_is_maintained_by_corestriction le_refl loop_l5)
  then have l2: "a ; (loop (b \<sslash>\<^sub>p (- C)) (Suc s) (Suc s) \<union>\<^sub>p loop (b \<sslash>\<^sub>p (- C)) (Suc (Suc s)) f) \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) (Suc s) (Suc s) \<setminus>\<^sub>p C \<union>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) (Suc (Suc s)) f \<setminus>\<^sub>p C"
    by (simp add: compose_distrib1_3 corestrict_choice_1)
  then show ?case
    using equiv_is_transitive l1 by blast
qed

lemma until_decomp_4: "s \<le> f \<Longrightarrow> until_support a C b s (Suc f) \<equiv>\<^sub>p until_support a C b (Suc f) (Suc f) \<union>\<^sub>p until_support a C b s f"
proof (induction f)
  case 0
  assume a1: "s \<le> 0"
  have l1: "s = 0"
    using a1 by auto
  from loop_l5 l1 show ?case
    by (simp add: until_decomp_2)
next
  case (Suc f)
  assume IH: "s \<le> f \<Longrightarrow> until_support a C b s (Suc f) \<equiv>\<^sub>p until_support a C b (Suc f) (Suc f) \<union>\<^sub>p until_support a C b s f"
  assume a1: "s \<le> Suc f"
  from loop_l3 have l1: "(a ; (loop (b\<sslash>\<^sub>p(-C)) s (Suc (Suc f)))\<setminus>\<^sub>p C) \<equiv>\<^sub>p a ; (((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc (Suc f))) \<union>\<^sub>p (loop (b\<sslash>\<^sub>p(-C)) s (Suc f)))\<setminus>\<^sub>p C"
    using a1 equiv_is_reflexive by auto
  have l2: "until_support a C b s (Suc (Suc f)) \<equiv>\<^sub>p a ; (((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc (Suc f))) \<union>\<^sub>p (loop (b\<sslash>\<^sub>p(-C)) s (Suc f)))\<setminus>\<^sub>p C"
    by (metis l1 until_support_def)
  have l3: "until_support a C b (Suc (Suc f)) (Suc (Suc f)) \<union>\<^sub>p until_support a C b s (Suc f) \<equiv>\<^sub>p a ; ((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc (Suc f)) \<union>\<^sub>p loop (b\<sslash>\<^sub>p(-C)) s (Suc f))\<setminus>\<^sub>p C"
  proof -
    have l3_1: "until_support a C b (Suc (Suc f)) (Suc (Suc f)) \<equiv>\<^sub>p a ; ((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc (Suc f))) \<setminus>\<^sub>p C"
      by (metis equiv_is_reflexive composition_equiv equivalence_is_maintained_by_corestriction loop_l2_1 until_support_def)
    have l3_2: "until_support a C b s (Suc f) \<equiv>\<^sub>p a ; (loop (b\<sslash>\<^sub>p(-C)) s (Suc f))\<setminus>\<^sub>p C"
      by (simp add: equiv_is_reflexive until_support_def)
    from l3_1 l3_2 have l3_3: "until_support a C b (Suc (Suc f)) (Suc (Suc f)) \<union>\<^sub>p until_support a C b s (Suc f) \<equiv>\<^sub>p a ; ((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc (Suc f))) \<setminus>\<^sub>p C \<union>\<^sub>p a ; (loop (b\<sslash>\<^sub>p(-C)) s (Suc f))\<setminus>\<^sub>p C"
      using choice_equiv by blast
    then show ?thesis
      by (meson equiv_is_transitive until_simplification_1)
  qed
  then show "until_support a C b s (Suc (Suc f)) \<equiv>\<^sub>p until_support a C b (Suc (Suc f)) (Suc (Suc f)) \<union>\<^sub>p until_support a C b s (Suc f)"
    using equiv_is_symetric equiv_is_transitive l2 by blast
qed

subsection \<open>Decomposition\<close>

lemma until_decomp_5: "0 \<le> k \<Longrightarrow> k \<le> n \<Longrightarrow> until_support a C b 0 n \<equiv>\<^sub>p until_support a C b 0 k \<union>\<^sub>p until_support a C b (Suc k) n"
proof (induction k)
  case 0
  then show ?case
    by (simp add: until_decomp_1)
next
  case (Suc k)
  assume IH: "0 \<le> k \<Longrightarrow> k \<le> n \<Longrightarrow> until_support a C b 0 n \<equiv>\<^sub>p until_support a C b 0 k \<union>\<^sub>p until_support a C b (Suc k) n"
  assume a1: "0 \<le> Suc k"
  assume a2: "Suc k \<le> n"
  have l1: "until_support a C b 0 (Suc k) \<equiv>\<^sub>p until_support a C b 0 k \<union>\<^sub>p until_support a C b (Suc k) (Suc k)"
    by (simp add: until_decomp_2)
  have l2: "until_support a C b 0 n \<equiv>\<^sub>p until_support a C b 0 k \<union>\<^sub>p until_support a C b (Suc k) n"
    using IH a2 by auto
  have l3: "until_support a C b (Suc k) n \<equiv>\<^sub>p until_support a C b (Suc k) (Suc k) \<union>\<^sub>p until_support a C b (Suc (Suc k)) n"
    by (simp add: a2 until_decomp_3)
  then have l4: "until_support a C b 0 n \<equiv>\<^sub>p until_support a C b 0 k \<union>\<^sub>p (until_support a C b (Suc k) (Suc k) \<union>\<^sub>p until_support a C b (Suc (Suc k)) n)"
    by (meson equiv_is_symetric equiv_is_transitive choice_equiv l2 until_decomp_1)
  from IH a1 a2 show "until_support a C b 0 n \<equiv>\<^sub>p until_support a C b 0 (Suc k) \<union>\<^sub>p until_support a C b (Suc (Suc k)) n"
    by (smt (verit, ccfv_SIG) choice_assoc_1 equiv_is_reflexive equiv_is_symetric equiv_is_transitive choice_equiv l1 l4)
qed

lemma until_decomp_6: "s \<le> k \<Longrightarrow> k \<le> f \<Longrightarrow> until_support a C b s f \<equiv>\<^sub>p until_support a C b s k \<union>\<^sub>p until_support a C b (Suc k) f"
proof (induction k)
  case 0
  then show ?case
    by (simp add: until_decomp_1)
next
  case (Suc k)
  assume IH: "s \<le> k \<Longrightarrow> k \<le> f \<Longrightarrow> until_support a C b s f \<equiv>\<^sub>p until_support a C b s k \<union>\<^sub>p until_support a C b (Suc k) f"
  assume a1: "s \<le> Suc k"
  assume a2: "Suc k \<le> f"
  from a2 have l1: "k \<le> f" by auto
  then show "until_support a C b s f \<equiv>\<^sub>p until_support a C b s (Suc k) \<union>\<^sub>p until_support a C b (Suc (Suc k)) f"
  proof (cases "s \<le> k")
    case True
    have l2: "until_support a C b s f \<equiv>\<^sub>p until_support a C b s k \<union>\<^sub>p until_support a C b (Suc k) f"
      by (simp add: IH True l1)
    have l3: "until_support a C b (Suc k) f \<equiv>\<^sub>p until_support a C b (Suc k) (Suc k) \<union>\<^sub>p until_support a C b (Suc (Suc k)) f"
      by (simp add: a2 until_decomp_3)
    have l4: "until_support a C b s (Suc k) \<equiv>\<^sub>p until_support a C b s k \<union>\<^sub>p until_support a C b (Suc k) (Suc k)"
      using True until_decomp_4 by fastforce
    have l5: "until_support a C b s f \<equiv>\<^sub>p until_support a C b s k \<union>\<^sub>p (until_support a C b (Suc k) (Suc k) \<union>\<^sub>p until_support a C b (Suc (Suc k)) f)"
      using equiv_is_reflexive equiv_is_transitive choice_equiv l2 l3 by blast
    have l6: "until_support a C b s f \<equiv>\<^sub>p (until_support a C b s k \<union>\<^sub>p until_support a C b (Suc k) (Suc k)) \<union>\<^sub>p until_support a C b (Suc (Suc k)) f"
      by (metis choice_assoc_1 l5)
    from l2 l3 l4 l5 l6 show "until_support a C b s f \<equiv>\<^sub>p until_support a C b s (Suc k) \<union>\<^sub>p until_support a C b (Suc (Suc k)) f"
      by (meson equiv_is_reflexive equiv_is_symetric equiv_is_transitive choice_equiv)
  next
    case False
    then show ?thesis
      by (metis a1 a2 le_SucE until_decomp_3)
  qed
qed

lemma until_decomp_7: "s = f \<Longrightarrow> until_support a C b s f \<equiv>\<^sub>p a ; ((b \<sslash>\<^sub>p (- C))\<^bold>^f) \<setminus>\<^sub>p C"
  by (simp add: equiv_is_reflexive composition_equiv equivalence_is_maintained_by_corestriction loop_l2_1 until_support_def)

lemma until_support_feasible: "all_feasible [a, b] \<Longrightarrow> is_feasible (until_support a C b s f)"
  oops

theorem equiv_is_maintained_by_until_support_1: "a\<^sub>1 \<equiv>\<^sub>p a\<^sub>2 \<Longrightarrow> b\<^sub>1 \<equiv>\<^sub>p b\<^sub>2 \<Longrightarrow> S b\<^sub>1 = S b\<^sub>2 \<Longrightarrow> all_feasible [b\<^sub>1, b\<^sub>2] \<Longrightarrow> until_support a\<^sub>1 C b\<^sub>1 s f \<equiv>\<^sub>p until_support a\<^sub>2 C b\<^sub>2 s f"
  apply (auto simp: until_support_def)
  apply (induction f)
  apply (auto) [1]
  apply (auto simp add: equals_equiv_relation_3 composition_equiv)
  apply (smt (verit, ccfv_SIG) Definitions.equiv_def equiv_is_symetric composition_equiv equivalence_is_maintained_by_corestriction restriction_equiv)
proof -
  fix f assume IH: "a\<^sub>1 ; loop (b\<^sub>1 \<sslash>\<^sub>p (- C)) s f \<setminus>\<^sub>p C \<equiv>\<^sub>p a\<^sub>2 ; loop (b\<^sub>2 \<sslash>\<^sub>p (- C)) s f \<setminus>\<^sub>p C"
  assume assms1: "a\<^sub>1 \<equiv>\<^sub>p a\<^sub>2" and
         assms2: "b\<^sub>1 \<equiv>\<^sub>p b\<^sub>2" and
         assms3: "S b\<^sub>1 = S b\<^sub>2" and
         assms4: "is_feasible b\<^sub>2" and
         assms5: "is_feasible b\<^sub>1" and
         assms6: "\<not> Suc f < s"
  have l1: "b\<^sub>1 \<sslash>\<^sub>p (- C) \<equiv>\<^sub>p b\<^sub>2 \<sslash>\<^sub>p (- C)"
    by (simp add: assms2 restriction_equiv)                                    
  have l2: "S (b\<^sub>1 \<sslash>\<^sub>p (- C)) = S (b\<^sub>2 \<sslash>\<^sub>p (- C))"
    by (simp add: assms3)
  from l1 l2 assms2 assms3 assms4 assms5  have l3: "loop (b\<^sub>1 \<sslash>\<^sub>p (- C)) s (Suc f) \<equiv>\<^sub>p loop (b\<^sub>2 \<sslash>\<^sub>p (- C)) s (Suc f)"
    using all_feasible.simps(2) equiv_is_maintained_by_arbitrary_repetition_1 restrict_feasible
    by (metis all_feasible.simps(1) assms5)
  show "\<not> Suc f < s \<Longrightarrow> a\<^sub>1 ; (loop (b\<^sub>1 \<sslash>\<^sub>p (- C)) s f \<union>\<^sub>p (b\<^sub>1 \<sslash>\<^sub>p (- C)) \<^bold>^ f ; b\<^sub>1 \<sslash>\<^sub>p (- C)) \<setminus>\<^sub>p C \<equiv>\<^sub>p a\<^sub>2 ; (loop (b\<^sub>2 \<sslash>\<^sub>p (- C)) s f \<union>\<^sub>p (b\<^sub>2 \<sslash>\<^sub>p (- C)) \<^bold>^ f ; b\<^sub>2 \<sslash>\<^sub>p (- C)) \<setminus>\<^sub>p C"
    using assms1 composition_equiv equivalence_is_maintained_by_corestriction l3
    by fastforce
qed

theorem equiv_is_maintained_by_until_support_2: "a\<^sub>1 \<equiv>\<^sub>p a\<^sub>2 \<Longrightarrow> b\<^sub>1 \<equiv>\<^sub>p b\<^sub>2 \<Longrightarrow> 0<s \<Longrightarrow> all_feasible [b\<^sub>1, b\<^sub>2] \<Longrightarrow> until_support a\<^sub>1 C b\<^sub>1 s f \<equiv>\<^sub>p until_support a\<^sub>2 C b\<^sub>2 s f"
  apply (auto simp: until_support_def)
  apply (induction f)
  apply (auto) [1]
  apply (simp add: composition_equiv equivalence_is_maintained_by_corestriction fail_equiv)
  apply (simp add: equals_equiv_relation_3 composition_equiv)
  apply (simp add: composition_equiv equivalence_is_maintained_by_corestriction fail_equiv)
  apply auto
proof -
  fix f assume IH: "a\<^sub>1 ; loop (b\<^sub>1 \<sslash>\<^sub>p (- C)) s f \<setminus>\<^sub>p C \<equiv>\<^sub>p a\<^sub>2 ; loop (b\<^sub>2 \<sslash>\<^sub>p (- C)) s f \<setminus>\<^sub>p C"
  assume assms1: "a\<^sub>1 \<equiv>\<^sub>p a\<^sub>2" and
         assms2: "b\<^sub>1 \<equiv>\<^sub>p b\<^sub>2" and
         assms3: "0 < s" and
         assms4: "is_feasible b\<^sub>2" and
         assms5: "is_feasible b\<^sub>1" and
         assms6: "\<not> Suc f < s"
  have l1: "b\<^sub>1 \<sslash>\<^sub>p (- C) \<equiv>\<^sub>p b\<^sub>2 \<sslash>\<^sub>p (- C)"
    by (simp add: assms2 restriction_equiv)
  from l1 assms2 assms3 assms4 assms5 have l3: "loop (b\<^sub>1 \<sslash>\<^sub>p (- C)) s (Suc f) \<equiv>\<^sub>p loop (b\<^sub>2 \<sslash>\<^sub>p (- C)) s (Suc f)"
    using all_feasible.simps(2) assms3 assms4 assms5 equiv_is_maintained_by_arbitrary_repetition_2 l1 restrict_feasible
    by (metis all_feasible.simps(1))
  show "a\<^sub>1 ; (loop (b\<^sub>1 \<sslash>\<^sub>p (- C)) s f \<union>\<^sub>p (b\<^sub>1 \<sslash>\<^sub>p (- C)) \<^bold>^ f ; b\<^sub>1 \<sslash>\<^sub>p (- C)) \<setminus>\<^sub>p C \<equiv>\<^sub>p a\<^sub>2 ; (loop (b\<^sub>2 \<sslash>\<^sub>p (- C)) s f \<union>\<^sub>p (b\<^sub>2 \<sslash>\<^sub>p (- C)) \<^bold>^ f ; b\<^sub>2 \<sslash>\<^sub>p (- C)) \<setminus>\<^sub>p C"
    using assms1 composition_equiv equivalence_is_maintained_by_corestriction l3
    using assms6 by fastforce
qed

theorem bad_index_is_fail_support: "f < s \<Longrightarrow> until_support a C b s f \<equiv>\<^sub>p Fail {}"
proof -
  assume a1: "f < s"
  then have "loop (b\<sslash>\<^sub>p(-C)) s f \<equiv>\<^sub>p Fail {}"
    by (simp add: bad_index_is_fail_arbitrary)
  then have l1: "until_support a C b s f \<equiv>\<^sub>p a ; (Fail {})\<setminus>\<^sub>p C"
    by (simp add: equiv_is_reflexive composition_equiv equivalence_is_maintained_by_corestriction until_support_def)
  have l2: "a ; (Fail {})\<setminus>\<^sub>p C \<equiv>\<^sub>p Fail {}"
    by (metis fail_compose_r infeas_corestriction2 special_empty2 special_empty3)
  then show "until_support a C b s f \<equiv>\<^sub>p Fail {}"
    using equiv_is_transitive l1 by blast
qed

theorem bad_index_range_support: "f < s \<Longrightarrow> Range_p (until_support a C b s f) = {}"
proof -
  assume a1: "f < s"
  then have "until_support a C b s f \<equiv>\<^sub>p Fail {}"
    by (simp add: bad_index_is_fail_support)
  then show "Range_p (until_support a C b s f) = {}"
    by (metis range_of_fail same_range_p_3)
qed

theorem until_support_decomp: "s\<le>s' \<Longrightarrow> f'\<le>f \<Longrightarrow> until_support a C b s f \<equiv>\<^sub>p until_support a C b s f \<union>\<^sub>p until_support a C b s' f'"
proof (cases "s'\<le>f'")
  case True
  assume "s\<le>s'" and "f'\<le>f"
  then show ?thesis using True
  proof (induction f)
    case 0
    then show ?case by (auto simp: until_support_def composition_def equiv_def restr_post_def Fail_def restrict_r_def corestrict_p_def restrict_p_def corestrict_r_def)
  next
    case (Suc f)
    assume IH: "s \<le> s' \<Longrightarrow> f' \<le> f \<Longrightarrow> s' \<le> f' \<Longrightarrow> until_support a C b s f \<equiv>\<^sub>p until_support a C b s f \<union>\<^sub>p until_support a C b s' f'"
    assume a1: "s \<le> s'"
    assume a2: "f' \<le> Suc f"
    assume a4: "s' \<le> f'"
    have a3: "s \<le> Suc f"
      using a1 a2 a4 by auto
    obtain suc where o1: "suc = until_support a C b s (Suc f)" by simp
    obtain here where o2: "here = until_support a C b s f" by simp
    obtain head where o3: "head = until_support a C b s (s'-1)" by simp
    obtain prime where o4: "prime = until_support a C b s' f'" by simp
    obtain tail where o5: "tail = until_support a C b (Suc f') (Suc f)" by simp
    obtain ptail where o6: "ptail = until_support a C b s' (Suc f)" by simp
    show "until_support a C b s (Suc f) \<equiv>\<^sub>p until_support a C b s (Suc f) \<union>\<^sub>p until_support a C b s' f'"
    proof (cases "s=0")
      case True
      assume "s=0"
      have l2: "suc \<equiv>\<^sub>p head \<union>\<^sub>p ptail"
      proof (cases "s'=s")
        case True
        then have "s'-1 = 0"
          by (simp add: \<open>s = 0\<close>)
        then have "head \<equiv>\<^sub>p until_support a C b 0 0"
          by (simp add: \<open>s = 0\<close> equals_equiv_relation_3 o3)
        have "ptail = until_support a C b 0 (Suc f)"
          by (simp add: True \<open>s = 0\<close> o6)
        obtain butfst where o8: "butfst = until_support a C b (Suc 0) (Suc f)" by simp
        have "suc \<equiv>\<^sub>p head \<union>\<^sub>p butfst" using \<open>s = 0\<close> until_decomp_3
          by (metis \<open>s' - 1 = 0\<close> a3 o1 o3 o8)
        then have "suc \<equiv>\<^sub>p (head \<union>\<^sub>p head) \<union>\<^sub>p butfst" using choice_idem_3
          by (smt (verit, del_insts) Definitions.equiv_def choice_equiv)
        then have "suc \<equiv>\<^sub>p head \<union>\<^sub>p (head \<union>\<^sub>p butfst)"
          by (metis choice_assoc_1)
        then show ?thesis
          by (metis True \<open>head \<equiv>\<^sub>p until_support a C b 0 0\<close> \<open>suc \<equiv>\<^sub>p head \<union>\<^sub>p butfst\<close> equiv_is_symetric equiv_is_transitive choice_equiv o1 o6)
      next
        case False
        obtain temp where o7: "temp = (s'-1)" by simp
        have "s'>0"
          using False a1 by auto
        have l1: "head = until_support a C b s temp"
          by (simp add: o3 o7)
        have l2: "ptail = until_support a C b (Suc temp) (Suc f)"
          by (simp add: \<open>0 < s'\<close> o6 o7)
        then show ?thesis
          by (metis (full_types) False Suc_diff_1 \<open>0 < s'\<close> a1 a2 a4 diff_le_self l1 le_SucE le_trans o1 o7 until_decomp_6)
      qed
      have l3: "ptail \<equiv>\<^sub>p prime \<union>\<^sub>p tail"
        by (simp add: a2 a4 o4 o5 o6 until_decomp_6) 
      have l4: "suc \<equiv>\<^sub>p (head \<union>\<^sub>p prime) \<union>\<^sub>p tail"
        by (metis choice_assoc_1 equiv_is_reflexive equiv_is_transitive choice_equiv l2 l3)
      have l5: "suc \<equiv>\<^sub>p ((head \<union>\<^sub>p (prime \<union>\<^sub>p prime)) \<union>\<^sub>p tail)"
        by (meson choice_idem_3 equiv_is_symetric equiv_is_transitive choice_equiv l4)
      have l6: "suc \<equiv>\<^sub>p ((head \<union>\<^sub>p prime) \<union>\<^sub>p tail) \<union>\<^sub>p prime"
        by (metis choice_assoc_1 choice_commute l5)
      have l7: "suc \<equiv>\<^sub>p suc \<union>\<^sub>p prime"
        by (smt (verit) choice_assoc_1 choice_commute choice_idem_3 equiv_is_symetric equiv_is_transitive choice_equiv l4 l5)
      then show ?thesis
        by (simp add: o1 o4)
    next
      case False
      have l2: "suc \<equiv>\<^sub>p head \<union>\<^sub>p ptail"
      proof (cases "s'=s")
        case True
        then have "head \<equiv>\<^sub>p Fail{}" using o3 False
          by (simp add: bad_index_is_fail_support)
        then show ?thesis using True o6 o1
          by (meson equiv_is_symetric equiv_is_transitive choice_equiv fail_choice_l)
      next
        case False
        obtain temp where o7: "temp = (s'-1)" by simp
        have "s'>0"
          using False a1 by auto
        have l1: "head = until_support a C b s temp"
          by (simp add: o3 o7)
        have l2: "ptail = until_support a C b (Suc temp) (Suc f)"
          by (simp add: \<open>0 < s'\<close> o6 o7)
        then show ?thesis
          by (metis (full_types) False Suc_diff_1 \<open>0 < s'\<close> a1 a2 a4 diff_le_self l1 le_SucE le_trans o1 o7 until_decomp_6)
      qed
      have l3: "ptail \<equiv>\<^sub>p prime \<union>\<^sub>p tail"
        by (simp add: a2 a4 o4 o5 o6 until_decomp_6) 
      have l4: "suc \<equiv>\<^sub>p (head \<union>\<^sub>p prime) \<union>\<^sub>p tail"
        by (metis choice_assoc_1 equiv_is_reflexive equiv_is_transitive choice_equiv l2 l3)
      have l5: "suc \<equiv>\<^sub>p ((head \<union>\<^sub>p (prime \<union>\<^sub>p prime)) \<union>\<^sub>p tail)"
        by (meson choice_idem_3 equiv_is_symetric equiv_is_transitive choice_equiv l4)
      have l6: "suc \<equiv>\<^sub>p ((head \<union>\<^sub>p prime) \<union>\<^sub>p tail) \<union>\<^sub>p prime"
        by (metis choice_assoc_1 choice_commute l5)
      have l7: "suc \<equiv>\<^sub>p suc \<union>\<^sub>p prime"
        by (smt (verit) choice_assoc_1 choice_commute choice_idem_3 equiv_is_symetric equiv_is_transitive choice_equiv l4 l5)
      then show ?thesis
        by (simp add: o1 o4)
    qed
  qed
next
  case False
  have "f' < s'"
    using False by auto
  moreover have "until_support a C b s' f' \<equiv>\<^sub>p Fail {}"
    by (simp add: bad_index_is_fail_support calculation)
  then show ?thesis
    by (meson equiv_is_symetric equiv_is_transitive choice_equiv fail_choice_r)
qed


end