theory While_support
  imports 
"../T_03_Basic_programs"
"Arbitrary_repetition"
begin
section \<open>While support for top\<close>


subsection \<open>Step cases\<close>
lemma while_decomp_1: "while_support a C b 0 n \<equiv>\<^sub>p while_support a C b 0 0 \<union>\<^sub>p while_support a C b (Suc 0) n"
  apply (simp add: while_support_def)
proof (induction n)
  case 0
  have right_1: "loop (b \<sslash>\<^sub>p (- C)) (Suc 0) 0 \<setminus>\<^sub>p C \<equiv>\<^sub>p Fail (S b)"
    by (metis corestriction_prop equiv_is_transitive fail_compose_l loop_l2_01 restriction_state)
  from right_1 have right_2: "a; loop (b \<sslash>\<^sub>p (- C)) (Suc 0) 0 \<setminus>\<^sub>p C \<equiv>\<^sub>p Fail (S b)"
    by (metis equiv_def composition_def corestriction_state fail_compose_r loop_l2_01 restriction_state)
  from right_2 have right_3: "a ; Skip (S b) \<setminus>\<^sub>p C \<union>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) (Suc 0) 0 \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; Skip (S b) \<setminus>\<^sub>p C \<union>\<^sub>p Fail (S b)"
    by (simp add: equiv_is_reflexive equivalence_is_maintained_by_choice)
  from right_3 have right_4: "a ; Skip (S b) \<setminus>\<^sub>p C \<union>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) (Suc 0) 0 \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; Skip (S b) \<setminus>\<^sub>p C"
    by (meson equiv_is_transitive fail_union_r)
  from right_2 have left_1: "a ; loop (b \<sslash>\<^sub>p (- C)) 0 0 \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; Skip (Pre (b \<sslash>\<^sub>p (- C))) \<setminus>\<^sub>p C"
    by (simp add: equals_equiv_relation_3 restrict_p_def)
  have l1: "a ; Fail (S b) \<setminus>\<^sub>p C \<equiv>\<^sub>p Fail (S b)"
    using right_2 by auto
  from right_3 show ?case
    by (auto simp: equiv_def Skip_def Fail_def composition_def corestrict_p_def corestrict_r_def choice_def restr_post_def restrict_r_def)
next
  case (Suc n)
  assume IH: "a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; Skip (Pre (b \<sslash>\<^sub>p (- C))) \<setminus>\<^sub>p C \<union>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) (Suc 0) n \<setminus>\<^sub>p C"
  have l2: "a ; loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n) \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; (Skip (Pre (b \<sslash>\<^sub>p (- C))) \<union>\<^sub>p loop (b \<sslash>\<^sub>p (- C)) (Suc 0) (Suc n)) \<setminus>\<^sub>p C"
    by (metis One_nat_def equals_equiv_relation_3 equivalence_is_maintained_by_composition equivalence_is_maintained_by_corestriction loop_l6 zero_less_Suc)
  have l3: "a ; (Skip (Pre (b \<sslash>\<^sub>p (- C))) \<union>\<^sub>p loop (b \<sslash>\<^sub>p (- C)) (Suc 0) (Suc n)) \<setminus>\<^sub>p C \<equiv>\<^sub>p ((a ; Skip (Pre (b \<sslash>\<^sub>p (- C)))) \<union>\<^sub>p (a ; loop (b \<sslash>\<^sub>p (- C)) (Suc 0) (Suc n))) \<setminus>\<^sub>p C"
    using corestrict_compose equiv_is_symetric equivalence_is_maintained_by_corestriction equiv_is_transitive compose_distrib1_3 by blast
  then have l4: "((a ; Skip (Pre (b \<sslash>\<^sub>p (- C)))) \<union>\<^sub>p (a ; loop (b \<sslash>\<^sub>p (- C)) (Suc 0) (Suc n))) \<setminus>\<^sub>p C \<equiv>\<^sub>p ((a ; Skip (Pre (b \<sslash>\<^sub>p (- C))) \<setminus>\<^sub>p C) \<union>\<^sub>p (a ; loop (b \<sslash>\<^sub>p (- C)) (Suc 0) (Suc n) \<setminus>\<^sub>p C))"
    by (meson corestrict_union corestrict_compose equiv_is_transitive equivalence_is_maintained_by_choice)
  from compose_distrib1_3 corestrict_union l2 show ?case
    using equiv_is_transitive l3 l4 by blast
qed

lemma while_decomp_2: "while_support a C b 0 (Suc n) \<equiv>\<^sub>p while_support a C b 0 n \<union>\<^sub>p while_support a C b (Suc n) (Suc n)"
proof (induction n)
  case 0
  then show ?case
    using while_decomp_1 by auto
next
  case (Suc n)
  assume IH: "while_support a C b 0 (Suc n) \<equiv>\<^sub>p while_support a C b 0 n \<union>\<^sub>p while_support a C b (Suc n) (Suc n)"
  have t2: "while_support a C b 0 (Suc (Suc n)) \<equiv>\<^sub>p (a ; (loop (b\<sslash>\<^sub>p(-C)) 0 (Suc n))\<setminus>\<^sub>p C) \<union>\<^sub>p (a ; (loop (b\<sslash>\<^sub>p(-C)) (Suc (Suc n)) (Suc (Suc n)))\<setminus>\<^sub>p C)"
    apply (auto simp: while_support_def)
  proof -
    have l1: "a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ n ; (b \<sslash>\<^sub>p (- C) ; b \<sslash>\<^sub>p (- C))) \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; (Fail (S b) \<union>\<^sub>p (b \<sslash>\<^sub>p (- C)) \<^bold>^ n ; (b \<sslash>\<^sub>p (- C) ; b \<sslash>\<^sub>p (- C))) \<setminus>\<^sub>p C"
      by (simp add: equiv_is_reflexive equiv_is_symetric equivalence_is_maintained_by_composition equivalence_is_maintained_by_corestriction fail_union_l)
    have l2: "a ; (loop (b \<sslash>\<^sub>p (- C)) 0 n \<union>\<^sub>p b \<sslash>\<^sub>p (- C) ; (b \<sslash>\<^sub>p (- C)) \<^bold>^ n) \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; (loop (b \<sslash>\<^sub>p (- C)) 0 n \<union>\<^sub>p b \<sslash>\<^sub>p (- C) ; (b \<sslash>\<^sub>p (- C)) \<^bold>^ n) \<setminus>\<^sub>p C"
      by (simp add: equiv_is_reflexive)
    from l1 l2 while_simplification_1 show "a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ n ; (b \<sslash>\<^sub>p (- C) ; b \<sslash>\<^sub>p (- C)) \<union>\<^sub>p (loop (b \<sslash>\<^sub>p (- C)) 0 n \<union>\<^sub>p (b \<sslash>\<^sub>p (- C)) \<^bold>^ n ; b \<sslash>\<^sub>p (- C))) \<setminus>\<^sub>p C \<equiv>\<^sub>p
    a ; (loop (b \<sslash>\<^sub>p (- C)) 0 n \<union>\<^sub>p (b \<sslash>\<^sub>p (- C)) \<^bold>^ n ; b \<sslash>\<^sub>p (- C)) \<setminus>\<^sub>p C \<union>\<^sub>p a ; (Fail (S b) \<union>\<^sub>p (b \<sslash>\<^sub>p (- C)) \<^bold>^ n ; (b \<sslash>\<^sub>p (- C) ; b \<sslash>\<^sub>p (- C))) \<setminus>\<^sub>p C"
      by (smt (verit, ccfv_threshold) choice_commute equiv_is_symetric equiv_is_transitive equivalence_is_maintained_by_choice)
  qed
  then show "while_support a C b 0 (Suc (Suc n)) \<equiv>\<^sub>p while_support a C b 0 (Suc n) \<union>\<^sub>p while_support a C b (Suc (Suc n)) (Suc (Suc n))"
    by (simp add: while_support_def)
qed

lemma while_decomp_3: "s \<le> f \<Longrightarrow> while_support a C b s f \<equiv>\<^sub>p while_support a C b s s \<union>\<^sub>p while_support a C b (Suc s) f"
  apply (simp add: while_support_def)
proof (induction s)
  case 0
  from while_decomp_1 show ?case
    by (metis while_support_def)
next
  case (Suc s)
  assume IH: "s \<le> f \<Longrightarrow>  a ; loop (b \<sslash>\<^sub>p (- C)) s f \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) s s \<setminus>\<^sub>p C \<union>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) (Suc s) f \<setminus>\<^sub>p C"
  assume a1: "Suc s \<le> f"
  have IH2: "a ; loop (b \<sslash>\<^sub>p (- C)) s f \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) s s \<setminus>\<^sub>p C \<union>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) (Suc s) f \<setminus>\<^sub>p C"
    by (simp add: IH Suc_leD a1)
  from IH2 have l1: "a ; loop (b \<sslash>\<^sub>p (- C)) (Suc s) f \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; (loop (b \<sslash>\<^sub>p (- C)) (Suc s) (Suc s) \<union>\<^sub>p loop (b \<sslash>\<^sub>p (- C)) (Suc (Suc s)) f) \<setminus>\<^sub>p C"
    by (metis a1 equiv_is_reflexive equivalence_is_maintained_by_composition equivalence_is_maintained_by_corestriction le_refl loop_l5)
  then have l2: "a ; (loop (b \<sslash>\<^sub>p (- C)) (Suc s) (Suc s) \<union>\<^sub>p loop (b \<sslash>\<^sub>p (- C)) (Suc (Suc s)) f) \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) (Suc s) (Suc s) \<setminus>\<^sub>p C \<union>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) (Suc (Suc s)) f \<setminus>\<^sub>p C"
    using compose_distrib1_3 corestrict_union equiv_is_reflexive equiv_is_transitive equivalence_is_maintained_by_composition by blast
  then show ?case
    using equiv_is_transitive l1 by blast
qed

lemma while_decomp_4: "s \<le> f \<Longrightarrow> while_support a C b s (Suc f) \<equiv>\<^sub>p while_support a C b (Suc f) (Suc f) \<union>\<^sub>p while_support a C b s f"
proof (induction f)
  case 0
  assume a1: "s \<le> 0"
  have l1: "s = 0"
    using a1 by auto
  from loop_l5 l1 show ?case
    by (simp add: while_decomp_2)
next
  case (Suc f)
  assume IH: "s \<le> f \<Longrightarrow> while_support a C b s (Suc f) \<equiv>\<^sub>p while_support a C b (Suc f) (Suc f) \<union>\<^sub>p while_support a C b s f"
  assume a1: "s \<le> Suc f"
  from loop_l3 have l1: "(a ; (loop (b\<sslash>\<^sub>p(-C)) s (Suc (Suc f)))\<setminus>\<^sub>p C) \<equiv>\<^sub>p a ; (((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc (Suc f))) \<union>\<^sub>p (loop (b\<sslash>\<^sub>p(-C)) s (Suc f)))\<setminus>\<^sub>p C"
    using a1 equiv_is_reflexive by auto
  have l2: "while_support a C b s (Suc (Suc f)) \<equiv>\<^sub>p a ; (((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc (Suc f))) \<union>\<^sub>p (loop (b\<sslash>\<^sub>p(-C)) s (Suc f)))\<setminus>\<^sub>p C"
    by (metis l1 while_support_def)
  have l3: "while_support a C b (Suc (Suc f)) (Suc (Suc f)) \<union>\<^sub>p while_support a C b s (Suc f) \<equiv>\<^sub>p a ; ((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc (Suc f)) \<union>\<^sub>p loop (b\<sslash>\<^sub>p(-C)) s (Suc f))\<setminus>\<^sub>p C"
  proof -
    have l3_1: "while_support a C b (Suc (Suc f)) (Suc (Suc f)) \<equiv>\<^sub>p a ; ((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc (Suc f))) \<setminus>\<^sub>p C"
      by (metis equiv_is_reflexive equivalence_is_maintained_by_composition equivalence_is_maintained_by_corestriction loop_l2_1 while_support_def)
    have l3_2: "while_support a C b s (Suc f) \<equiv>\<^sub>p a ; (loop (b\<sslash>\<^sub>p(-C)) s (Suc f))\<setminus>\<^sub>p C"
      by (simp add: equiv_is_reflexive while_support_def)
    from l3_1 l3_2 have l3_3: "while_support a C b (Suc (Suc f)) (Suc (Suc f)) \<union>\<^sub>p while_support a C b s (Suc f) \<equiv>\<^sub>p a ; ((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc (Suc f))) \<setminus>\<^sub>p C \<union>\<^sub>p a ; (loop (b\<sslash>\<^sub>p(-C)) s (Suc f))\<setminus>\<^sub>p C"
      using equivalence_is_maintained_by_choice by blast
    then show ?thesis
      by (meson compose_distrib1_3 corestrict_union equiv_is_reflexive equiv_is_symetric equiv_is_transitive equivalence_is_maintained_by_composition)
  qed
  then show "while_support a C b s (Suc (Suc f)) \<equiv>\<^sub>p while_support a C b (Suc (Suc f)) (Suc (Suc f)) \<union>\<^sub>p while_support a C b s (Suc f)"
    using equiv_is_symetric equiv_is_transitive l2 by blast
qed

subsection \<open>Decomposition\<close>

lemma while_decomp_5: "0 \<le> k \<Longrightarrow> k \<le> n \<Longrightarrow> while_support a C b 0 n \<equiv>\<^sub>p while_support a C b 0 k \<union>\<^sub>p while_support a C b (Suc k) n"
proof (induction k)
  case 0
  then show ?case
    by (simp add: while_decomp_1)
next
  case (Suc k)
  assume IH: "0 \<le> k \<Longrightarrow> k \<le> n \<Longrightarrow> while_support a C b 0 n \<equiv>\<^sub>p while_support a C b 0 k \<union>\<^sub>p while_support a C b (Suc k) n"
  assume a1: "0 \<le> Suc k"
  assume a2: "Suc k \<le> n"
  have l1: "while_support a C b 0 (Suc k) \<equiv>\<^sub>p while_support a C b 0 k \<union>\<^sub>p while_support a C b (Suc k) (Suc k)"
    by (simp add: while_decomp_2)
  have l2: "while_support a C b 0 n \<equiv>\<^sub>p while_support a C b 0 k \<union>\<^sub>p while_support a C b (Suc k) n"
    using IH a2 by auto
  have l3: "while_support a C b (Suc k) n \<equiv>\<^sub>p while_support a C b (Suc k) (Suc k) \<union>\<^sub>p while_support a C b (Suc (Suc k)) n"
    by (simp add: a2 while_decomp_3)
  then have l4: "while_support a C b 0 n \<equiv>\<^sub>p while_support a C b 0 k \<union>\<^sub>p (while_support a C b (Suc k) (Suc k) \<union>\<^sub>p while_support a C b (Suc (Suc k)) n)"
    by (meson equiv_is_symetric equiv_is_transitive equivalence_is_maintained_by_choice l2 while_decomp_1)
  from IH a1 a2 show "while_support a C b 0 n \<equiv>\<^sub>p while_support a C b 0 (Suc k) \<union>\<^sub>p while_support a C b (Suc (Suc k)) n"
    by (smt (verit, ccfv_SIG) choice_assoc_1 equiv_is_reflexive equiv_is_symetric equiv_is_transitive equivalence_is_maintained_by_choice l1 l4)
qed

lemma while_decomp_6: "s \<le> k \<Longrightarrow> k \<le> f \<Longrightarrow> while_support a C b s f \<equiv>\<^sub>p while_support a C b s k \<union>\<^sub>p while_support a C b (Suc k) f"
proof (induction k)
  case 0
  then show ?case
    by (simp add: while_decomp_1)
next
  case (Suc k)
  assume IH: "s \<le> k \<Longrightarrow> k \<le> f \<Longrightarrow> while_support a C b s f \<equiv>\<^sub>p while_support a C b s k \<union>\<^sub>p while_support a C b (Suc k) f"
  assume a1: "s \<le> Suc k"
  assume a2: "Suc k \<le> f"
  from a2 have l1: "k \<le> f" by auto
  then show "while_support a C b s f \<equiv>\<^sub>p while_support a C b s (Suc k) \<union>\<^sub>p while_support a C b (Suc (Suc k)) f"
  proof (cases "s \<le> k")
    case True
    have l2: "while_support a C b s f \<equiv>\<^sub>p while_support a C b s k \<union>\<^sub>p while_support a C b (Suc k) f"
      by (simp add: IH True l1)
    have l3: "while_support a C b (Suc k) f \<equiv>\<^sub>p while_support a C b (Suc k) (Suc k) \<union>\<^sub>p while_support a C b (Suc (Suc k)) f"
      by (simp add: a2 while_decomp_3)
    have l4: "while_support a C b s (Suc k) \<equiv>\<^sub>p while_support a C b s k \<union>\<^sub>p while_support a C b (Suc k) (Suc k)"
      using True while_decomp_4 by fastforce
    have l5: "while_support a C b s f \<equiv>\<^sub>p while_support a C b s k \<union>\<^sub>p (while_support a C b (Suc k) (Suc k) \<union>\<^sub>p while_support a C b (Suc (Suc k)) f)"
      using equiv_is_reflexive equiv_is_transitive equivalence_is_maintained_by_choice l2 l3 by blast
    have l6: "while_support a C b s f \<equiv>\<^sub>p (while_support a C b s k \<union>\<^sub>p while_support a C b (Suc k) (Suc k)) \<union>\<^sub>p while_support a C b (Suc (Suc k)) f"
      by (metis choice_assoc_1 l5)
    from l2 l3 l4 l5 l6 show "while_support a C b s f \<equiv>\<^sub>p while_support a C b s (Suc k) \<union>\<^sub>p while_support a C b (Suc (Suc k)) f"
      by (meson equiv_is_reflexive equiv_is_symetric equiv_is_transitive equivalence_is_maintained_by_choice)
  next
    case False
    then show ?thesis
      by (metis a1 a2 le_SucE while_decomp_3)
  qed
qed

lemma while_decomp_7: "s = f \<Longrightarrow> while_support a C b s f \<equiv>\<^sub>p a ; ((b \<sslash>\<^sub>p (- C))\<^bold>^f) \<setminus>\<^sub>p C"
  by (simp add: equiv_is_reflexive equivalence_is_maintained_by_composition equivalence_is_maintained_by_corestriction loop_l2_1 while_support_def)

lemma while_support_feasible: "all_feasible [a, b] \<Longrightarrow> is_feasible (while_support a C b s f)"
proof (induction f)
  case 0
  then show ?case
    by (simp add: while_support_def compose_feasible corestrict_feasible fail_is_feasible skip_is_feasible)
next
  case (Suc f)
  assume IH: "all_feasible [a, b] \<Longrightarrow> is_feasible (while_support a C b s f)"
  assume a1: "all_feasible [a, b]"
  from a1 IH have l1: "is_feasible (while_support a C b s f)" by simp
  then show ?case
  proof (cases "s \<le> f")
    case True
    assume a2: "s \<le> f"
    from a2 while_decomp_4 while_decomp_7 have l2: "while_support a C b s (Suc f) \<equiv>\<^sub>p while_support a C b s f \<union>\<^sub>p while_support a C b (Suc f) (Suc f)"
      using choice_commute by fastforce
    from l2 while_decomp_7 have l3: "while_support a C b s (Suc f) \<equiv>\<^sub>p while_support a C b s f \<union>\<^sub>p (a ; ((b \<sslash>\<^sub>p (- C))\<^bold>^(Suc f)) \<setminus>\<^sub>p C)"
      by (smt (verit, ccfv_SIG) equals_equiv_relation_3 equiv_is_transitive equivalence_is_maintained_by_choice)
    have l4: "is_feasible (a ; ((b \<sslash>\<^sub>p (- C))\<^bold>^(Suc f)) \<setminus>\<^sub>p C)"
      by (meson a1 all_feasible.simps(2) compose_feasible corestrict_feasible fixed_rep_feasibility restrict_feasible)
    then show ?thesis
      by (meson all_feasible.simps(1) all_feasible.simps(2) union_feasible equiv_is_symetric equiv_maintains_feasiblity l1 l3)
  next
    case False
    assume a2: "\<not> s \<le> f"
    from a2 have l1: "s>f" by simp
    then show ?thesis
    proof (cases "s = Suc f")
      case True
      assume a3: "s = Suc f"
      from a3 have l2: "while_support a C b s (Suc f) \<equiv>\<^sub>p while_support a C b s s"
        by (simp add: equiv_is_reflexive)
      have l3: "is_feasible (while_support a C b s s)"
        apply (simp add: while_support_def)
        by (meson a1 all_feasible.simps(2) arbitrary_rep_feasibility compose_feasible corestrict_feasible restrict_feasible verit_comp_simplify1(2))
      from a3 l2 l3 show ?thesis by simp
    next
      case False
      assume a3: "f < s"
      assume a4: " s \<noteq> Suc f"
      from a3 a4 have "s > Suc f" by simp
      then show ?thesis
        apply (simp add: while_support_def)
        by (meson a1 all_feasible.simps(2) compose_feasible corestrict_feasible fail_is_feasible)
    qed
  qed
qed

theorem equiv_is_maintained_by_while_support_1: 
  assumes "a\<^sub>1 \<equiv>\<^sub>p a\<^sub>2"
      and "b\<^sub>1 \<equiv>\<^sub>p b\<^sub>2"
      and "S b\<^sub>1 = S b\<^sub>2"
      and "all_feasible [b\<^sub>1, b\<^sub>2]"
    shows "while_support a\<^sub>1 C b\<^sub>1 s f \<equiv>\<^sub>p while_support a\<^sub>2 C b\<^sub>2 s f"
  apply (auto simp: while_support_def)
  apply (induction f)
  apply (auto) [1]
  apply (simp add: assms(1) assms(3) equals_equiv_relation_3 equivalence_is_maintained_by_composition)
  apply (metis (no_types, opaque_lifting) Definitions.equiv_def assms(1) assms(2) equivalence_is_maintained_by_composition equivalence_is_maintained_by_restriction)
proof -
  fix f assume IH: "a\<^sub>1 ; loop (b\<^sub>1 \<sslash>\<^sub>p (- C)) s f \<setminus>\<^sub>p C \<equiv>\<^sub>p a\<^sub>2 ; loop (b\<^sub>2 \<sslash>\<^sub>p (- C)) s f \<setminus>\<^sub>p C"
  have l1: "b\<^sub>1 \<sslash>\<^sub>p (- C) \<equiv>\<^sub>p b\<^sub>2 \<sslash>\<^sub>p (- C)"
    by (simp add: assms(2) equivalence_is_maintained_by_restriction)
  have l2: "S (b\<^sub>1 \<sslash>\<^sub>p (- C)) = S (b\<^sub>2 \<sslash>\<^sub>p (- C))"
    by (simp add: assms(3))
  from l1 l2 assms (2) assms (3) assms (4)  have l3: "loop (b\<^sub>1 \<sslash>\<^sub>p (- C)) s (Suc f) \<equiv>\<^sub>p loop (b\<^sub>2 \<sslash>\<^sub>p (- C)) s (Suc f)"
    by (meson all_feasible.simps(2) equiv_is_maintained_by_arbitrary_repetition_1 restrict_feasible)
  show "a\<^sub>1 ; loop (b\<^sub>1 \<sslash>\<^sub>p (- C)) s (Suc f) \<setminus>\<^sub>p C \<equiv>\<^sub>p a\<^sub>2 ; loop (b\<^sub>2 \<sslash>\<^sub>p (- C)) s (Suc f) \<setminus>\<^sub>p C"
    using assms(1) equivalence_is_maintained_by_composition equivalence_is_maintained_by_corestriction l3 by blast
qed

theorem equiv_is_maintained_by_while_support_2: 
  assumes "a\<^sub>1 \<equiv>\<^sub>p a\<^sub>2"
      and "b\<^sub>1 \<equiv>\<^sub>p b\<^sub>2"
      and "0<s"
      and "all_feasible [b\<^sub>1, b\<^sub>2]"
    shows "while_support a\<^sub>1 C b\<^sub>1 s f \<equiv>\<^sub>p while_support a\<^sub>2 C b\<^sub>2 s f"
  apply (auto simp: while_support_def)
  apply (induction f)
  apply (auto) [1]
  apply (simp add: assms(1) assms(3) equals_equiv_relation_3 equivalence_is_maintained_by_composition)
  apply (simp add: assms(1) equivalence_is_maintained_by_composition equivalence_is_maintained_by_corestriction fail_is_equivalent_independant_of_arg)
  using assms(3) apply auto[1]
proof -
  fix f assume IH: "a\<^sub>1 ; loop (b\<^sub>1 \<sslash>\<^sub>p (- C)) s f \<setminus>\<^sub>p C \<equiv>\<^sub>p a\<^sub>2 ; loop (b\<^sub>2 \<sslash>\<^sub>p (- C)) s f \<setminus>\<^sub>p C"
  have l1: "b\<^sub>1 \<sslash>\<^sub>p (- C) \<equiv>\<^sub>p b\<^sub>2 \<sslash>\<^sub>p (- C)"
    by (simp add: assms(2) equivalence_is_maintained_by_restriction)
  from l1 assms (2) assms (3) assms (4)  have l3: "loop (b\<^sub>1 \<sslash>\<^sub>p (- C)) s (Suc f) \<equiv>\<^sub>p loop (b\<^sub>2 \<sslash>\<^sub>p (- C)) s (Suc f)"
    by (metis all_feasible.simps(2) assms(3) assms(4) equiv_is_maintained_by_arbitrary_repetition_2 l1 restrict_feasible)
  show "a\<^sub>1 ; loop (b\<^sub>1 \<sslash>\<^sub>p (- C)) s (Suc f) \<setminus>\<^sub>p C \<equiv>\<^sub>p a\<^sub>2 ; loop (b\<^sub>2 \<sslash>\<^sub>p (- C)) s (Suc f) \<setminus>\<^sub>p C"
    using assms(1) equivalence_is_maintained_by_composition equivalence_is_maintained_by_corestriction l3 by blast
qed


end