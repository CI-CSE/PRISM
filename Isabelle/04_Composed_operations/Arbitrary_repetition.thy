theory Arbitrary_repetition
  imports 
"../T_03_Basic_programs"
"Fixed_repetition"
begin
section \<open>Arbitrary repetition for top\<close>


subsection \<open>Base cases\<close>
theorem loop_l1: "s=0 \<Longrightarrow> f=0 \<Longrightarrow> loop p s f = Skip (Pre p) "
  by (auto simp: arbitrary_repetition.cases choice_def Fail_def restr_post_def equiv_def restrict_r_def)

theorem loop_l2: "s=0 \<Longrightarrow> f=1 \<Longrightarrow> loop p s f = Skip (Pre p) \<union>\<^sub>p (Skip (Pre p);p) "
  by (auto simp: Skip_def equiv_def)

lemma loop_l2_01: "loop p (Suc f) f = Fail (S p)"
  by (metis arbitrary_repetition.elims lessI)

lemma loop_l2_1: "s=f \<Longrightarrow> loop p s f \<equiv>\<^sub>p p\<^bold>^s"
  apply (induction f)
   apply (simp add: equals_equiv_relation_3)
  by (metis arbitrary_repetition.simps(2) fail_union_r less_irrefl_nat loop_l2_01)

lemma loop_l2_2: "Suc s=f \<Longrightarrow> loop p s f \<equiv>\<^sub>p p\<^bold>^s \<union>\<^sub>p p\<^bold>^f"
  apply (induction f)
   apply (simp add: equals_equiv_relation_3)
  by (simp add: equals_equiv_relation_3 equivalence_is_maintained_by_choice loop_l2_1)

subsection \<open>Step cases\<close>

theorem loop_l3: "s\<le>f \<Longrightarrow> loop p s (Suc f) \<equiv>\<^sub>p (p\<^bold>^(Suc f)) \<union>\<^sub>p (loop p s f)"
  using equals_equiv_relation_3 less_iff_Suc_add by fastforce 

theorem loop_l4: "s\<le>f \<Longrightarrow> loop p s f \<equiv>\<^sub>p (p\<^bold>^s) \<union>\<^sub>p (loop p (Suc s) f)"
proof -
  let ?x = "f-s"
  assume a2: "s\<le>f"
  from a2 show ?thesis
  apply (induction ?x arbitrary: s f)
  proof -
    case 0
    assume a2: "s\<le>f"
    assume a_zero: "0=f-s"
    from a_zero a2 have l0: "s=f" by simp
    from a_zero have l1: "loop p (Suc s) f = Fail (S p)"
      by (simp add: l0 loop_l2_01)
    from a_zero have l2: "loop p s f \<equiv>\<^sub>p p \<^bold>^ s \<union>\<^sub>p Fail (S p)"
      by (metis equiv_def l0 fail_union_r loop_l2_1)
    from l0 l1 l2 have t0: "loop p s f \<equiv>\<^sub>p p \<^bold>^ s \<union>\<^sub>p loop p (Suc s) f"
      by simp
    from a2 a_zero show ?case
      using t0 by auto
  next
    case (Suc x)
    assume IH: "\<And>s f. x = f - s \<Longrightarrow> s \<le> f \<Longrightarrow> loop p s f \<equiv>\<^sub>p p \<^bold>^ s \<union>\<^sub>p loop p (Suc s) f"
    assume a2: "s \<le> f"
    assume a_suc: "Suc x = f - s"
    from a_suc have l0: "x = (f - 1) - s" by simp
    from a_suc a2 have l1: "s < f" by simp
    from l1 have "0<f" by simp
    from l1 have l2: "s \<le> f - 1" by simp
    have IH2: "loop p s (f - 1) \<equiv>\<^sub>p p \<^bold>^ s \<union>\<^sub>p loop p (Suc s) (f - 1)"
      using Suc.hyps(1) l0 l2 by blast
    from l1 loop_l3 have IH3: "loop p s f \<equiv>\<^sub>p p \<^bold>^ f \<union>\<^sub>p loop p s (f - 1)"
      by (metis Suc_diff_1 \<open>0 < f\<close> l2)
    then have IH4: "loop p s f \<equiv>\<^sub>p p \<^bold>^ f \<union>\<^sub>p (p \<^bold>^ s \<union>\<^sub>p loop p (Suc s) (f - 1))"
      by (meson IH2 IH3 equiv_is_symetric equiv_is_transitive equivalence_is_maintained_by_choice loop_l2_1)
    then have IH5: "loop p s f \<equiv>\<^sub>p p \<^bold>^ s \<union>\<^sub>p (p \<^bold>^ f \<union>\<^sub>p loop p (Suc s) (f - 1))"
      by (metis choice_assoc_1 choice_commute)
    from IH5 arbitrary_repetition.elims(1) IH2 l1
    show ?case
      by (smt (verit) One_nat_def diff_Suc_1' diff_is_0_eq' le_less_Suc_eq nat_less_le zero_less_one_class.zero_le_one)
  qed
qed

theorem loop_l6: "s=0 \<Longrightarrow> s<f \<Longrightarrow> loop p s f \<equiv>\<^sub>p (Skip (Pre p)) \<union>\<^sub>p (loop p 1 f)"
  using loop_l4 by fastforce

theorem "0<s \<Longrightarrow> s<f \<Longrightarrow> loop p s f \<equiv>\<^sub>p p\<^bold>^s \<union>\<^sub>p loop p (Suc s) f"
  by (simp add: loop_l4)

subsection \<open>Decomposition\<close>
theorem loop_l5: "s\<le>f \<Longrightarrow> s \<le> k \<Longrightarrow> k \<le> f \<Longrightarrow> loop p s f \<equiv>\<^sub>p (loop p s k) \<union>\<^sub>p (loop p (Suc k) f)"
proof (induction k arbitrary: s f)
  case 0
  assume a2: "s\<le>f"
  assume a3: "s\<le>0"
  assume a4: "0\<le>f"
  from a2 a3 a4 loop_l4 show ?case
    using equiv_is_reflexive equiv_is_transitive le_zero_eq by fastforce
next
  case (Suc k)
  assume IH: "(\<And>s f. s \<le> f \<Longrightarrow> s \<le> k \<Longrightarrow> k \<le> f \<Longrightarrow> loop p s f \<equiv>\<^sub>p loop p s k \<union>\<^sub>p loop p (Suc k) f)"
  assume a2: "s \<le> f"
  assume a3: "s \<le> Suc k"
  assume a4: "Suc k \<le> f"
  from IH a2 a3 a4 have l1: "loop p s f \<equiv>\<^sub>p loop p s k \<union>\<^sub>p loop p (Suc k) f"
    by (metis Suc.IH Suc_leD equiv_is_symetric fail_union_l le_Suc_eq loop_l2_01)
  then have l2: "loop p s f \<equiv>\<^sub>p loop p s  k \<union>\<^sub>p (p\<^bold>^(Suc k) \<union>\<^sub>p loop p (Suc (Suc k)) f)"
    by (meson a4 equiv_is_reflexive equiv_is_transitive equivalence_is_maintained_by_choice l1 loop_l4)
  then have l3: "loop p s f \<equiv>\<^sub>p (loop p s k \<union>\<^sub>p p\<^bold>^(Suc k)) \<union>\<^sub>p loop p (Suc (Suc k)) f"
    by (metis choice_assoc_1)
  then have l4: "loop p s f \<equiv>\<^sub>p loop p s (Suc k) \<union>\<^sub>p (loop p (Suc (Suc k)) f)"
    by (smt (verit) equiv_def a3 arbitrary_repetition.simps(2) choice_assoc_2 choice_commute l2 leD)
  from IH a2 a3 a4 l4 show ?case by auto
qed

lemma loop_simplification: "all_feasible [x,y] \<Longrightarrow> Range_p x \<inter> Pre y = {} \<Longrightarrow> Range_p y \<inter> Pre x = {} \<Longrightarrow> (loop x s f) \<union>\<^sub>p (loop y s f) \<equiv>\<^sub>p loop (x \<union>\<^sub>p y) s f"
proof (induction f)
  case 0
  then show ?case
  proof (cases "s=0")
    case True
    assume a0: "s=0"
    then show ?thesis apply (auto)
      by (simp add: skip_prop)
  next
    case False
    then show ?thesis apply (auto)
      using equiv_is_symetric equiv_is_transitive fail_union_l fail_union_r by blast
  qed
next
  case (Suc f)
  assume a1: "Range_p x \<inter> Pre y = {}"
  assume a2: "Range_p y \<inter> Pre x = {}"
  assume a3: "all_feasible [x,y]"
  assume IH: "all_feasible [x,y] \<Longrightarrow> Range_p x \<inter> Pre y = {} \<Longrightarrow> Range_p y \<inter> Pre x = {} \<Longrightarrow> loop x s f \<union>\<^sub>p loop y s f \<equiv>\<^sub>p loop (x \<union>\<^sub>p y) s f"
  from a1 a2 a3 IH have IH2: "loop x s f \<union>\<^sub>p loop y s f \<equiv>\<^sub>p loop (x \<union>\<^sub>p y) s f" by simp
  then show "loop x s (Suc f) \<union>\<^sub>p loop y s (Suc f) \<equiv>\<^sub>p loop (x \<union>\<^sub>p y) s (Suc f)"
  proof (cases "s\<le>f")
    case True
    assume a1: "s\<le>f"
    have l1: "loop x s (Suc f) \<equiv>\<^sub>p loop x s f \<union>\<^sub>p x\<^bold>^(Suc f)"
      using a1 equiv_is_reflexive by auto
    have l2: "loop y s (Suc f) \<equiv>\<^sub>p loop y s f \<union>\<^sub>p y\<^bold>^(Suc f)"
      using a1 equiv_is_reflexive by auto
    have l3: "loop x s (Suc f) \<union>\<^sub>p loop y s (Suc f) \<equiv>\<^sub>p (loop x s f \<union>\<^sub>p x\<^bold>^(Suc f)) \<union>\<^sub>p (loop y s f \<union>\<^sub>p y\<^bold>^(Suc f))"
      using equivalence_is_maintained_by_choice l1 l2 by blast
    then have l4: "(loop x s f \<union>\<^sub>p x\<^bold>^(Suc f)) \<union>\<^sub>p (loop y s f \<union>\<^sub>p y\<^bold>^(Suc f)) \<equiv>\<^sub>p (loop x s f \<union>\<^sub>p x\<^bold>^(Suc f)) \<union>\<^sub>p (loop y s f \<union>\<^sub>p y\<^bold>^(Suc f))"
      using equals_equiv_relation_3 by blast
    then have l5: "loop x s (Suc f) \<union>\<^sub>p loop y s (Suc f) \<equiv>\<^sub>p (loop x s f \<union>\<^sub>p loop y s f) \<union>\<^sub>p (x\<^bold>^(Suc f) \<union>\<^sub>p y\<^bold>^(Suc f))"
      by (metis (no_types, lifting) choice_assoc_1 choice_commute l3)
    have l6: "x\<^bold>^(Suc f) \<union>\<^sub>p y\<^bold>^(Suc f) \<equiv>\<^sub>p (x \<union>\<^sub>p y)\<^bold>^(Suc f)"
      using Suc.prems(2) a2 a3 arbitrary_repetition_simplification by blast
    from l5 l6 show ?thesis apply (auto)
      using a1 apply auto[1]
      by (smt (verit, ccfv_SIG) IH2 choice_assoc_1 equiv_is_transitive equivalence_is_maintained_by_choice)
  next
    case False
    assume a4: "\<not> s \<le> f"
    from a4 have l2: "f < s" by simp
    then show ?thesis
      apply (auto)
       apply (metis IH2 arbitrary_repetition.elims choice_state l2)
    proof -
      assume a5: "\<not> Suc f < s"
      from a5 have l3: "s \<le> Suc f" by simp
      from l3 l2 have l4: "s=Suc f" by simp
      have l11: "Fail (S x) \<union>\<^sub>p x \<^bold>^ (Suc f) \<equiv>\<^sub>p x \<^bold>^ (Suc f)"
        by (simp add: fail_union_l l4 loop_l2_01)
      have l12: "Fail (S y) \<union>\<^sub>p y \<^bold>^ (Suc f) \<equiv>\<^sub>p y \<^bold>^ (Suc f)"
        by (simp add: fail_union_l l4 loop_l2_01)
      have l17: "Fail (S y \<union> S x) \<union>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ (Suc f) \<equiv>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ (Suc f)"
        by (simp add: fail_union_l l4 loop_l2_01)
      from a3 a1 a2 arbitrary_repetition_simplification have l18: " x \<^bold>^ (Suc f) \<union>\<^sub>p  y \<^bold>^ (Suc f) \<equiv>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ (Suc f)"
        by blast
      from l4 l11 l12 l17 show "loop x s f \<union>\<^sub>p (x \<^bold>^ f ; x \<union>\<^sub>p (loop y s f \<union>\<^sub>p y \<^bold>^ f ; y)) \<equiv>\<^sub>p loop (x \<union>\<^sub>p y) s f \<union>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ f ; (x \<union>\<^sub>p y)"
      proof -
        have f1: "x \<^bold>^ s \<union>\<^sub>p y \<^bold>^ s \<equiv>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ s"
          by (smt (z3) l18 l4)
        have "Fail (S x) \<union>\<^sub>p Fail (S y) \<equiv>\<^sub>p Fail (S (x \<union>\<^sub>p y))"
          using equiv_is_transitive fail_is_equivalent_independant_of_arg fail_union_r by blast
        then have "Fail (S x) \<union>\<^sub>p (Fail (S y) \<union>\<^sub>p (x \<^bold>^ s \<union>\<^sub>p y \<^bold>^ s)) \<equiv>\<^sub>p Fail (S (x \<union>\<^sub>p y)) \<union>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ s"
          using f1 by (metis choice_assoc_1 equivalence_is_maintained_by_choice)
        then have "loop x s f \<union>\<^sub>p (x \<^bold>^ s \<union>\<^sub>p (y \<^bold>^ s \<union>\<^sub>p loop y s f)) \<equiv>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ s \<union>\<^sub>p loop (x \<union>\<^sub>p y) s f"
          by (smt (z3) choice_assoc_1 choice_commute l4 loop_l2_01)
        then show ?thesis
          by (simp add: l4)
      qed
    qed
  qed
qed

theorem equiv_is_maintained_by_arbitrary_repetition_1: "all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> S p\<^sub>1 = S p\<^sub>2 \<Longrightarrow> loop p\<^sub>1 s f \<equiv>\<^sub>p loop p\<^sub>2 s f"
proof (induction f)
  case 0
  then show ?case
    apply (cases "s=0")
    apply (auto)
    apply (simp add: Definitions.equiv_def)
    using fail_is_equivalent_independant_of_arg by auto
next
  case (Suc f)
  assume a1: "all_feasible [p\<^sub>1, p\<^sub>2]"
  assume a2: "p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2"
  assume a3: "S p\<^sub>1 = S p\<^sub>2"
  assume IH: "all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> S p\<^sub>1 = S p\<^sub>2 \<Longrightarrow> loop p\<^sub>1 s f \<equiv>\<^sub>p loop p\<^sub>2 s f"
  from a1 a2 a3 IH have IH2: "loop p\<^sub>1 s f \<equiv>\<^sub>p loop p\<^sub>2 s f" by simp
  then show "loop p\<^sub>1 s (Suc f) \<equiv>\<^sub>p loop p\<^sub>2 s (Suc f)"
    apply (cases "Suc f < s")
     apply (simp add: a3 equals_equiv_relation_3)
  proof -
    assume a4: "\<not> Suc f < s"
    from a4 have l1: "s \<le> Suc f" by simp
    have l2: "loop p\<^sub>1 s (Suc f) \<equiv>\<^sub>p loop p\<^sub>1 s f \<union>\<^sub>p (p\<^sub>1\<^bold>^(Suc f))"
      using a4 choice_commute_3 by auto
    have l3: "loop p\<^sub>2 s (Suc f) \<equiv>\<^sub>p loop p\<^sub>2 s f \<union>\<^sub>p (p\<^sub>2\<^bold>^(Suc f))"
      using a4 choice_commute_3 by auto
    from a1 a2 have l4: "p\<^sub>1\<^bold>^(Suc f) \<equiv>\<^sub>p p\<^sub>2\<^bold>^(Suc f)"
      using equiv_is_maintained_by_fixed_repetition by blast
    from IH2 a4 l2 l3 l4 show ?thesis
      by (simp add: equivalence_is_maintained_by_choice)
  qed
qed

theorem equiv_is_maintained_by_arbitrary_repetition_2: "all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> 0<s \<Longrightarrow> loop p\<^sub>1 s f \<equiv>\<^sub>p loop p\<^sub>2 s f"
proof (induction f)
  case 0
  then show ?case
    apply auto
    by (simp add: fail_is_equivalent_independant_of_arg)
next
  case (Suc f)
  assume a1: "all_feasible [p\<^sub>1, p\<^sub>2]"
  assume a2: "p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2"
  assume a3: "0<s"
  assume IH: "all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> 0<s \<Longrightarrow> loop p\<^sub>1 s f \<equiv>\<^sub>p loop p\<^sub>2 s f"
  from a1 a2 a3 IH have IH2: "loop p\<^sub>1 s f \<equiv>\<^sub>p loop p\<^sub>2 s f" by simp
  then show "loop p\<^sub>1 s (Suc f) \<equiv>\<^sub>p loop p\<^sub>2 s (Suc f)"
    apply (cases "Suc f < s")
     apply (simp add: a3 equals_equiv_relation_3)
  proof -
    assume a4: "\<not> Suc f < s"
    from a4 have l1: "s \<le> Suc f" by simp
    have l2: "loop p\<^sub>1 s (Suc f) \<equiv>\<^sub>p loop p\<^sub>1 s f \<union>\<^sub>p (p\<^sub>1\<^bold>^(Suc f))"
      using a4 choice_commute_3 by auto
    have l3: "loop p\<^sub>2 s (Suc f) \<equiv>\<^sub>p loop p\<^sub>2 s f \<union>\<^sub>p (p\<^sub>2\<^bold>^(Suc f))"
      using a4 choice_commute_3 by auto
    from a1 a2 have l4: "p\<^sub>1\<^bold>^(Suc f) \<equiv>\<^sub>p p\<^sub>2\<^bold>^(Suc f)"
      using equiv_is_maintained_by_fixed_repetition by blast
    from IH2 a4 l2 l3 l4 show ?thesis
      by (simp add: equivalence_is_maintained_by_choice)
  next
    show "Fail (S p\<^sub>1) \<equiv>\<^sub>p Fail (S p\<^sub>2)"
      by (simp add: fail_is_equivalent_independant_of_arg)
  qed
qed


lemma arbitrary_rep_feasibility_l1: "s > f \<Longrightarrow> is_feasible p \<Longrightarrow> is_feasible (loop p s f)"
proof -
  assume a0: "s>f"
  assume a1: "is_feasible p"
  have l1: "loop p s f = Fail (S p)"
    by (metis a0 arbitrary_repetition.elims)
  then show "is_feasible (loop p s f)"
    by (simp add: fail_is_feasible)
qed

lemma arbitrary_rep_feasibility_l2: "s \<le> f \<Longrightarrow> is_feasible p \<Longrightarrow> is_feasible (loop p s f)"
proof (induction f)
  case 0
  then show ?case
    by (metis arbitrary_repetition.simps(1) fail_is_feasible fixed_rep_feasibility)
next
  case (Suc f)
  assume IH: "s \<le> f \<Longrightarrow> is_feasible p \<Longrightarrow> is_feasible (loop p s f)"
  assume a1: "is_feasible p"
  assume a2: "s \<le> (Suc f)"
  from a1 fixed_rep_feasibility have l1: "is_feasible (p\<^bold>^(Suc f))"
    by blast
  then show "is_feasible (loop p s (Suc f))"
  proof (cases "s \<le> f")
    case True
    assume a3: "s \<le> f"
    from IH a1 a3 have l2: "is_feasible (loop p s f)" by simp
    from a3 loop_l3 have l3: "loop p s (Suc f) \<equiv>\<^sub>p loop p s f \<union>\<^sub>p p\<^bold>^(Suc f)"
      by (metis choice_commute)

    from l1 l2 union_feasible have "is_feasible (loop p s f \<union>\<^sub>p p\<^bold>^(Suc f))"
      by auto
    then show ?thesis
      using fail_is_feasible by auto
  next
    case False
    assume a3: "\<not> s \<le> f"
    from a3 have l2: "s>f" by simp
    from a2 l2 have l3: "s = Suc f" by auto
    from l3 have l4: "loop p s (Suc f) \<equiv>\<^sub>p loop p (Suc f) (Suc f)"
      by (simp add: equiv_is_reflexive)
    from l3 have l5: "loop p s (Suc f) \<equiv>\<^sub>p p \<^bold>^ (Suc f)"
      using loop_l2_1 by blast
    from l5 l1 equiv_maintains_feasiblity show ?thesis
      using equiv_is_symetric by blast
  qed
qed

theorem arbitrary_rep_feasibility: "is_feasible p \<Longrightarrow> is_feasible (loop p s f)"
  by (meson arbitrary_rep_feasibility_l1 arbitrary_rep_feasibility_l2 linorder_le_less_linear)

theorem skip_compose_l_of_loop_1: "s \<le> f \<Longrightarrow> s=0 \<Longrightarrow> loop p s f \<equiv>\<^sub>p Skip (Pre p) \<union>\<^sub>p loop p s f"
  apply (cases "s=f")
  apply (auto) [1]
   apply (simp add: equiv_is_symetric)
proof -
  assume a1: " s \<le> f"
  assume a2: "s = 0"
  assume a3: "s \<noteq> f"
  from a1 a2 a3 have l1: "0<f" by simp
  have l4: "loop p 0 f \<equiv>\<^sub>p Skip (Pre p) \<union>\<^sub>p loop p 1 f"
    using l1 loop_l6 by auto
  have l5: "Skip (Pre p) \<union>\<^sub>p loop p 1 f \<equiv>\<^sub>p Skip (Pre p) \<union>\<^sub>p (Skip (Pre p) \<union>\<^sub>p loop p 1 f)"
    by (metis choice_assoc_1 choice_idem_3 equals_equiv_relation_3 equiv_is_symetric equivalence_is_maintained_by_choice)
  have l6: "Skip (Pre p) \<union>\<^sub>p (Skip (Pre p) \<union>\<^sub>p loop p 1 f) \<equiv>\<^sub>p Skip (Pre p) \<union>\<^sub>p loop p s f"
    by (metis a2 equals_equiv_relation_3 equiv_is_symetric equivalence_is_maintained_by_choice l4)
  show "loop p s f \<equiv>\<^sub>p Skip (Pre p) \<union>\<^sub>p loop p s f"
    using a2 equiv_is_transitive l4 l5 l6 by blast
qed

theorem skip_compose_r_of_loop_2: "is_feasible p \<Longrightarrow> loop p s f \<equiv>\<^sub>p loop p s f ; Skip (S p)"
  apply (induction f)
   apply (metis arbitrary_repetition.simps(1) equiv_is_symetric fail_compose_l skip_compose_r_of_fixed_rep_1)
  apply (cases "f>s")
  apply (auto)
  apply (auto simp: Fail_def equiv_def restr_post_def is_feasible_def Skip_def restrict_r_def composition_def) [1]
  apply (metis compose_distrib2_1 composition_makes_feasible equiv_is_symetric equivalence_is_maintained_by_choice fixed_repetition.simps(2) skip_compose_r_2 state_space_is_same zero_less_Suc)
  apply (auto simp: Fail_def equiv_def restr_post_def is_feasible_def Skip_def restrict_r_def composition_def) [1]
  by (metis compose_distrib2_1 composition_makes_feasible equiv_is_symetric equivalence_is_maintained_by_choice fixed_repetition.simps(2) skip_compose_r_2 state_space_is_same zero_less_Suc)

theorem skip_compose_l_of_loop_3: "is_feasible p \<Longrightarrow> loop p s f \<equiv>\<^sub>p Skip (S p) ; loop p s f"
  apply (induction f)
   apply (auto simp: Fail_def S_def equiv_def Skip_def composition_def corestrict_r_def Field_def restr_post_def restrict_r_def Domain_iff) [1]
proof -
  fix f assume IH: "is_feasible p \<Longrightarrow> loop p s f \<equiv>\<^sub>p Skip (S p) ; loop p s f"
  assume feas: "is_feasible p"
  from feas IH have IH2: "loop p s f \<equiv>\<^sub>p Skip (S p) ; loop p s f" by simp
  from IH2 show "loop p s (Suc f) \<equiv>\<^sub>p Skip (S p) ; loop p s (Suc f)"
    apply (cases "f=0")
    apply (auto)
    apply (auto simp: Fail_def equiv_def Skip_def composition_def corestrict_r_def restr_post_def restrict_r_def S_def Domain_iff) [1]
    apply (auto simp: Fail_def equiv_def Skip_def composition_def corestrict_r_def restr_post_def restrict_r_def Domain_iff S_def) [1]
    apply (auto simp: Fail_def equiv_def Skip_def composition_def corestrict_r_def restr_post_def restrict_r_def Domain_iff S_def) [1]
  proof -
    have l1: "p \<^bold>^ f ; p \<equiv>\<^sub>p Skip (S p) ; (p \<^bold>^ f ; p)"
      by (metis fixed_repetition.simps(2) skip_compose_l_of_fixed_rep_1)
    have l2 :"Skip (S p) ; loop p s f  \<union>\<^sub>p Skip (S p) ; (p \<^bold>^ f ; p) \<equiv>\<^sub>p Skip (S p) ; (loop p s f \<union>\<^sub>p p \<^bold>^ f ; p)"
      by (simp add: compose_distrib1_3 equiv_is_symetric)
    have l3: "loop p s f \<union>\<^sub>p p \<^bold>^ f ; p \<equiv>\<^sub>p Skip (S p) ; loop p s f \<union>\<^sub>p Skip (S p) ; (p \<^bold>^ f ; p)"
      by (simp add: IH2 equivalence_is_maintained_by_choice l1)
    from IH2 feas l1 l2 l3 show "loop p s f \<union>\<^sub>p p \<^bold>^ f ; p \<equiv>\<^sub>p Skip (S p) ; (loop p s f \<union>\<^sub>p p \<^bold>^ f ; p)"
      using equiv_is_transitive by blast
  qed
qed

theorem range_fixed_rep: "s\<le>m \<Longrightarrow> m\<le>f \<Longrightarrow> x \<notin> Range_p (loop p s f) \<Longrightarrow> x \<notin> Range_p (p\<^bold>^m)"
proof (induction f)
  case 0
  then show ?case by auto
next
  case (Suc f)
  assume IH: "s \<le> m \<Longrightarrow> m \<le> f \<Longrightarrow> x \<notin> Range_p (loop p s f) \<Longrightarrow> x \<notin> Range_p (p \<^bold>^ m)"
  assume a1: "s \<le> m"
  assume a2: "m \<le> Suc f"
  assume a3: "x \<notin> Range_p (loop p s (Suc f))"
  then show ?case
  proof (cases "m\<le>f")
    case True
    then have IH2: "x \<notin> Range_p (loop p s f) \<Longrightarrow> x \<notin> Range_p (p \<^bold>^ m)"
      by (simp add: IH a1)
    have l2: "loop p s (Suc f) \<equiv>\<^sub>p loop p s f \<union>\<^sub>p p\<^bold>^(Suc f)"
      by (metis True a1 choice_commute le_trans loop_l3)
    then show ?thesis
    proof (cases "x \<notin> Range_p (loop p s f)")
      case True
      then show ?thesis
        by (simp add: IH2)
    next
      case False
      then have l1: "x \<in> Range_p (loop p s f)" by simp
      from l1 l2 have l3: "x \<in> Range_p (loop p s (Suc f))"
        by (metis choice_range_p_prop_3 same_range_p_3)
      from l3 a3 show ?thesis
        by simp
    qed
  next
    case False
    then have "m = Suc f" using a2 by simp
    then show ?thesis
    proof (cases "s\<le>f")
      case True
      from loop_l3 have l2: "loop p s (Suc f) \<equiv>\<^sub>p loop p s f \<union>\<^sub>p p\<^bold>^(Suc f)"
        by (metis True choice_commute)
      then show ?thesis
      proof (cases "x \<notin> Range_p (loop p s f)")
        case True
        then show ?thesis
          by (metis \<open>m = Suc f\<close> a3 choice_commute choice_range_p_prop_3 l2 same_range_p_3)
      next
        case False
        then show ?thesis
          by (metis a3 choice_range_p_prop_3 l2 same_range_p_3)
      qed
    next
      case False
      then have "Suc f = s"
        using \<open>m = Suc f\<close> a1 by auto
      then have l1: "loop p s (Suc f) \<equiv>\<^sub>p p\<^bold>^(Suc f)"
        by (simp add: loop_l2_1)
      from a3 show ?thesis
        using \<open>m = Suc f\<close> l1 same_range_p_3 by auto
    qed
  qed
qed

lemma pre_is_known_arbitrary_rep_1: "\<forall>x y. x \<in> Pre a \<and> (x, y) \<in> post (a ; (b \<sslash>\<^sub>p (- C))\<^bold>^n) \<longrightarrow> x \<in> Pre (a ; (b \<sslash>\<^sub>p (- C))\<^bold>^n)"
  apply (induction n)
   apply (auto simp: Skip_def composition_def restr_post_def restrict_p_def restrict_r_def corestrict_r_def) [1]
  by (metis knowing_pre_composition)

lemma pre_is_known_arbitrary_rep_2: "x \<in> Pre a \<Longrightarrow> (x, y) \<in> post (a ; (b \<sslash>\<^sub>p (- C))\<^bold>^n) \<Longrightarrow> x \<in> Pre (a ; (b \<sslash>\<^sub>p (- C))\<^bold>^n)"
  apply (induction n)
   apply (auto simp: Skip_def composition_def restr_post_def restrict_p_def restrict_r_def corestrict_r_def) [1]
  apply (auto)
  by (simp add: knowing_pre_composition)

theorem bad_index_is_fail_arbitrary: "f<s \<Longrightarrow> loop a s f \<equiv>\<^sub>p Fail {}"
  by (metis arbitrary_repetition.elims fail_is_equivalent_independant_of_arg)

end