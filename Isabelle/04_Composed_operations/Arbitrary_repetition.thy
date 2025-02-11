theory Arbitrary_repetition
  imports 
"../T_03_Basic_programs"
"Fixed_repetition"
begin
section \<open>Arbitrary repetition for top\<close>


subsection \<open>Base cases\<close>
theorem loop_l1: "s=0 \<Longrightarrow> f=0 \<Longrightarrow> loop p s f = Skip (S p) \<sslash>\<^sub>p (Pre p) "
  by (auto simp: arbitrary_repetition.cases choice_def Fail_def restr_post_def equiv_def restrict_r_def)

theorem loop_l2: "s=0 \<Longrightarrow> f=1 \<Longrightarrow> loop p s f = Skip (S p) \<sslash>\<^sub>p (Pre p) \<union>\<^sub>p  (Skip (S p) \<sslash>\<^sub>p (Pre p);p)"
  by (auto simp: Skip_def equiv_def)

lemma loop_l2_01: "loop p (Suc f) f = Fail (S p)"
  by (metis arbitrary_repetition.elims lessI)

lemma loop_l2_02: "loop p 0 f ; p = loop p (Suc 0) (Suc f)"
proof (induction f)
  case 0
  then show ?case by (auto simp: composition_def Skip_def restr_post_def restrict_r_def choice_def restrict_p_def corestrict_r_def Fail_def relcomp_unfold S_def Field_def)
next
  case (Suc f)
  have "loop p 0 (Suc f) = p\<^bold>^(Suc f) \<union>\<^sub>p loop p 0 f" by auto
  have "loop p 0 (Suc f) ; p = p\<^bold>^(Suc f) ; p \<union>\<^sub>p loop p 0 f ; p"
    by (simp add: compose_distrib2_1)
  moreover have "... = p\<^bold>^(Suc f) ; p \<union>\<^sub>p loop p (Suc 0) (Suc f)"
    by (simp add: Suc)
  moreover have "... = p\<^bold>^(Suc (Suc f)) \<union>\<^sub>p loop p (Suc 0) (Suc f)"
    by simp
  moreover have "... = loop p (Suc 0) (Suc (Suc f))"
    by simp
  ultimately show "loop p 0 (Suc f) ; p = loop p (Suc 0) (Suc (Suc f))" by argo
qed

lemma loop_l2_03: "loop p s s ; p = loop p (Suc s) (Suc s)"
proof (cases "s=0")
  case True
  then show ?thesis by (auto simp:restrict_p_def Skip_def S_def choice_def Fail_def restr_post_def restrict_r_def composition_def Field_def corestrict_r_def)
next
  case False
  have "loop p s s = p\<^bold>^s \<union>\<^sub>p Fail (S p)"
    by (metis (no_types, lifting) False arbitrary_repetition.elims loop_l2_01 nat_less_le)
  have "(p\<^bold>^s \<union>\<^sub>p Fail (S p));p = p\<^bold>^s;p \<union>\<^sub>p Fail (S p);p"
    by (simp add: compose_distrib2_1)
  moreover have "... = p\<^bold>^(Suc s) \<union>\<^sub>p Fail (S p);p"
    by simp
  moreover have "... = p\<^bold>^(Suc s) \<union>\<^sub>p Fail (S p)" using fail_compose
    by (simp add: Fail.fail_compose)
  moreover have "... = loop p (Suc s) (Suc s)"
    by (simp add: loop_l2_01)
  ultimately show ?thesis
    by (simp add: \<open>loop p s s = p \<^bold>^ s \<union>\<^sub>p Fail (S p)\<close>)
qed

lemma loop_l2_04: "s\<le>f \<Longrightarrow> loop p s f ; p = loop p (Suc s) (Suc f)"
proof (induction f arbitrary: s)
  case 0
  then show ?case
    using loop_l2_02 by blast
next
  case (Suc f)
  show ?case
  proof (cases "s=Suc f")
    case True
    have "loop p s s ; p = loop p (Suc s) (Suc s)" using loop_l2_02
      by (simp add: loop_l2_03)
    then show "loop p s (Suc f) ; p = loop p (Suc s) (Suc (Suc f))"
      by (simp add: True)
  next
    case False
    have "s \<le> Suc f" using False
      using Suc.prems by auto
    have "Suc s \<le> Suc (Suc f)"
      by (simp add: Suc.prems)
    then have "loop p s (Suc f) = p\<^bold>^(Suc f) \<union>\<^sub>p loop p s f" by auto
    have "loop p s (Suc f) ; p = p\<^bold>^(Suc f) ; p \<union>\<^sub>p loop p s f ; p"
      by (metis \<open>loop p s (Suc f) = p \<^bold>^ Suc f \<union>\<^sub>p loop p s f\<close> compose_distrib2_1)
    moreover have "... = p\<^bold>^(Suc f) ; p \<union>\<^sub>p loop p (Suc s) (Suc f)"
      by (metis False Suc.IH Suc.prems le_SucE)
    moreover have "... = p\<^bold>^(Suc (Suc f)) \<union>\<^sub>p loop p (Suc s) (Suc f)"
      by simp
    moreover have "... = loop p (Suc s) (Suc (Suc f))" 
      using \<open>Suc s \<le> Suc (Suc f)\<close> by auto
    ultimately show "loop p s (Suc f) ; p = loop p (Suc s) (Suc (Suc f))" by argo
  qed
qed

lemma loop_l2_05: "0<s \<Longrightarrow> loop p s s = p\<^bold>^s \<union>\<^sub>p Fail {}"
proof -
  assume "0<s"
  have "loop p s s = (if s>s then Fail (S p) else p\<^bold>^s \<union>\<^sub>p arbitrary_repetition p s (s-1))"
    by (metis (no_types, lifting) One_nat_def \<open>0 < s\<close> arbitrary_repetition.elims diff_Suc_1')
  moreover have "... = p\<^bold>^s \<union>\<^sub>p arbitrary_repetition p s (s-1)"
    by simp
  moreover have "... = p\<^bold>^s \<union>\<^sub>p Fail (S p)"
    by (metis Suc_diff_1 \<open>0 < s\<close> loop_l2_01)
  moreover have "... = p\<^bold>^s \<union>\<^sub>p Fail {}"
    by (metis dual_order.refl fail_union_2 state_space_is_same)
  ultimately show ?thesis by argo
qed

lemma loop_l2_1: "s=f \<Longrightarrow> loop p s f \<equiv>\<^sub>p p\<^bold>^s"
  apply (induction f)
   apply (simp add: equals_equiv_relation_3)
  by (metis arbitrary_repetition.simps(2) fail_choice_r less_irrefl_nat loop_l2_01)

lemma loop_l2_2: "loop p s (Suc s) = p\<^bold>^s \<union>\<^sub>p p\<^bold>^(Suc s)" \<comment> \<open>UNUSED\<close>
proof (cases "s=0")
  case True
  then show ?thesis by auto
next
  case False
  have "loop p s (Suc s) = p\<^bold>^(Suc s) \<union>\<^sub>p loop p s s" by auto
  have "loop p s s = p\<^bold>^s \<union>\<^sub>p Fail {}"
    using False loop_l2_05 by auto
  have "p\<^bold>^(Suc s) \<union>\<^sub>p loop p s s = p\<^bold>^(Suc s) \<union>\<^sub>p (p\<^bold>^s \<union>\<^sub>p Fail {})"
    by (simp add: \<open>loop p s s = p \<^bold>^ s \<union>\<^sub>p Fail {}\<close>)
  have "... = p\<^bold>^(Suc s) \<union>\<^sub>p p\<^bold>^s"
    by (metis choice_assoc_1 choice_commute special_empty1 skip_prop_12)
  then show ?thesis
    by (simp add: \<open>loop p s s = p \<^bold>^ s \<union>\<^sub>p Fail {}\<close>)
qed


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
    from a_zero have l1: "loop p (Suc s) f = Fail (S p)"
      by (metis a2 diff_is_0_eq le_antisym loop_l2_01)
    from a2 a_zero show ?case
      by (metis choice_commute diff_is_0_eq equiv_is_symetric equiv_is_transitive fail_choice_l l1 le_antisym loop_l2_1)
  next
    case (Suc x)
    assume IH: "\<And>s f. x = f - s \<Longrightarrow> s \<le> f \<Longrightarrow> loop p s f \<equiv>\<^sub>p p \<^bold>^ s \<union>\<^sub>p loop p (Suc s) f"
    assume a2: "s \<le> f"
    assume a_suc: "Suc x = f - s"
    have IH2: "loop p s (f - 1) \<equiv>\<^sub>p p \<^bold>^ s \<union>\<^sub>p loop p (Suc s) (f - 1)"
      by (metis IH a2 a_suc diff_Suc_1 diff_Suc_eq_diff_pred diff_diff_cancel diff_le_self diff_right_commute)
    from loop_l3 have IH3: "loop p s f \<equiv>\<^sub>p p \<^bold>^ f \<union>\<^sub>p loop p s (f - 1)"
      by (metis Suc_le_D a2 a_suc diff_Suc_1 diff_Suc_eq_diff_pred diff_diff_cancel diff_le_self loop_l3)
    then have IH4: "loop p s f \<equiv>\<^sub>p p \<^bold>^ f \<union>\<^sub>p (p \<^bold>^ s \<union>\<^sub>p loop p (Suc s) (f - 1))"
      by (meson IH2 IH3 equiv_is_symetric equiv_is_transitive choice_equiv loop_l2_1)
    then have IH5: "loop p s f \<equiv>\<^sub>p p \<^bold>^ s \<union>\<^sub>p (p \<^bold>^ f \<union>\<^sub>p loop p (Suc s) (f - 1))"
      by (metis choice_assoc_1 choice_commute)
    from IH5 arbitrary_repetition.elims(1) IH2
    show ?case
      by (smt (verit) Suc_pred' a_suc le_less_Suc_eq nat_less_le old.nat.inject zero_less_Suc zero_less_diff)
  qed
qed

theorem loop_l6: "s=0 \<Longrightarrow> s<f \<Longrightarrow> loop p s f \<equiv>\<^sub>p (Skip (S p) \<sslash>\<^sub>p (Pre p)) \<union>\<^sub>p (loop p 1 f)"
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
    by (metis Suc.IH Suc_leD equiv_is_symetric fail_choice_l le_Suc_eq loop_l2_01)
  then have l2: "loop p s f \<equiv>\<^sub>p loop p s  k \<union>\<^sub>p (p\<^bold>^(Suc k) \<union>\<^sub>p loop p (Suc (Suc k)) f)"
    by (meson a4 equiv_is_reflexive equiv_is_transitive choice_equiv l1 loop_l4)
  then have l3: "loop p s f \<equiv>\<^sub>p (loop p s k \<union>\<^sub>p p\<^bold>^(Suc k)) \<union>\<^sub>p loop p (Suc (Suc k)) f"
    by (metis choice_assoc_1)
  then have l4: "loop p s f \<equiv>\<^sub>p loop p s (Suc k) \<union>\<^sub>p (loop p (Suc (Suc k)) f)"
    by (smt (verit) equiv_def a3 arbitrary_repetition.simps(2) choice_assoc_2 choice_commute l2 leD)
  from IH a2 a3 a4 l4 show ?case by auto
qed

lemma loop_simplification: "all_feasible [x,y] \<Longrightarrow> Range_p x \<inter> Pre y = {} \<Longrightarrow> Range_p y \<inter> Pre x = {} \<Longrightarrow> (loop x s f) \<union>\<^sub>p (loop y s f) \<equiv>\<^sub>p loop (x \<union>\<^sub>p y) s f" \<comment> \<open>Loop_choice3\<close>
proof (induction f)
  case 0
  then show ?case
  proof (cases "s=0")
    case True
    assume a0: "s=0"
    then show ?thesis using arbitrary_repetition_simplification 0 by (auto simp: equiv_def restr_post_def Skip_def restrict_p_def S_def restrict_r_def)
  next
    case False
    then show ?thesis apply (auto)
      using equiv_is_symetric equiv_is_transitive fail_choice_l fail_choice_r by blast
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
      using choice_equiv l1 l2 by blast
    then have l4: "(loop x s f \<union>\<^sub>p x\<^bold>^(Suc f)) \<union>\<^sub>p (loop y s f \<union>\<^sub>p y\<^bold>^(Suc f)) \<equiv>\<^sub>p (loop x s f \<union>\<^sub>p x\<^bold>^(Suc f)) \<union>\<^sub>p (loop y s f \<union>\<^sub>p y\<^bold>^(Suc f))"
      using equals_equiv_relation_3 by blast
    then have l5: "loop x s (Suc f) \<union>\<^sub>p loop y s (Suc f) \<equiv>\<^sub>p (loop x s f \<union>\<^sub>p loop y s f) \<union>\<^sub>p (x\<^bold>^(Suc f) \<union>\<^sub>p y\<^bold>^(Suc f))"
      by (metis (no_types, lifting) choice_assoc_1 choice_commute l3)
    have l6: "x\<^bold>^(Suc f) \<union>\<^sub>p y\<^bold>^(Suc f) \<equiv>\<^sub>p (x \<union>\<^sub>p y)\<^bold>^(Suc f)"
      using Suc.prems(2) a2 a3 arbitrary_repetition_simplification2 by blast
    from l5 l6 show ?thesis apply (auto)
      using a1 apply auto[1]
      by (smt (verit, ccfv_SIG) IH2 choice_assoc_1 equiv_is_transitive choice_equiv)
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
        by (simp add: fail_choice_l l4 loop_l2_01)
      have l12: "Fail (S y) \<union>\<^sub>p y \<^bold>^ (Suc f) \<equiv>\<^sub>p y \<^bold>^ (Suc f)"
        by (simp add: fail_choice_l l4 loop_l2_01)
      have l17: "Fail (S y \<union> S x) \<union>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ (Suc f) \<equiv>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ (Suc f)"
        by (simp add: fail_choice_l l4 loop_l2_01)
      from a3 a1 a2 arbitrary_repetition_simplification2 have l18: " x \<^bold>^ (Suc f) \<union>\<^sub>p  y \<^bold>^ (Suc f) \<equiv>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ (Suc f)"
        by blast
      from l4 l11 l12 l17 show "loop x s f \<union>\<^sub>p (x \<^bold>^ f ; x \<union>\<^sub>p (loop y s f \<union>\<^sub>p y \<^bold>^ f ; y)) \<equiv>\<^sub>p loop (x \<union>\<^sub>p y) s f \<union>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ f ; (x \<union>\<^sub>p y)"
      proof -
        have f1: "x \<^bold>^ s \<union>\<^sub>p y \<^bold>^ s \<equiv>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ s"
          by (smt (z3) l18 l4)
        have "Fail (S x) \<union>\<^sub>p Fail (S y) \<equiv>\<^sub>p Fail (S (x \<union>\<^sub>p y))"
          using equiv_is_transitive fail_equiv fail_choice_r by blast
        then have "Fail (S x) \<union>\<^sub>p (Fail (S y) \<union>\<^sub>p (x \<^bold>^ s \<union>\<^sub>p y \<^bold>^ s)) \<equiv>\<^sub>p Fail (S (x \<union>\<^sub>p y)) \<union>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ s"
          using f1 by (metis choice_assoc_1 choice_equiv)
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
    using fail_equiv by auto
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
      by (simp add: choice_equiv)
  qed
qed

theorem equiv_is_maintained_by_arbitrary_repetition_2: "all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> 0<s \<Longrightarrow> loop p\<^sub>1 s f \<equiv>\<^sub>p loop p\<^sub>2 s f"
proof (induction f)
  case 0
  then show ?case
    apply auto
    by (simp add: fail_equiv)
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
      by (simp add: choice_equiv)
  next
    show "Fail (S p\<^sub>1) \<equiv>\<^sub>p Fail (S p\<^sub>2)"
      by (simp add: fail_equiv)
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

    from l1 l2 choice_feasible have "is_feasible (loop p s f \<union>\<^sub>p p\<^bold>^(Suc f))"
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

theorem skip_compose_l_of_loop_1: "s \<le> f \<Longrightarrow> s=0 \<Longrightarrow> loop p s f \<equiv>\<^sub>p Skip (S p) \<sslash>\<^sub>p (Pre p) \<union>\<^sub>p loop p s f"
  apply (cases "s=f")
  apply (auto simp: restrict_p_def equiv_def Skip_def S_def restr_post_def restrict_r_def) [1]
   apply (simp add: equiv_is_symetric)
proof -
  assume a1: " 0 < f"
  assume a2: "s = 0"
  have l4: "loop p 0 f \<equiv>\<^sub>p Skip (S p) \<sslash>\<^sub>p (Pre p) \<union>\<^sub>p loop p 1 f"
    using a1 loop_l6 by auto
  have l5: "Skip (Pre p) \<union>\<^sub>p loop p 1 f \<equiv>\<^sub>p Skip (Pre p) \<union>\<^sub>p (Skip (Pre p) \<union>\<^sub>p loop p 1 f)"
    by (metis choice_assoc_1 choice_idem_3 equals_equiv_relation_3 equiv_is_symetric choice_equiv)
  have l6: "Skip (S p) \<sslash>\<^sub>p (Pre p) \<union>\<^sub>p (Skip (S p) \<sslash>\<^sub>p (Pre p) \<union>\<^sub>p loop p 1 f) \<equiv>\<^sub>p Skip (S p) \<sslash>\<^sub>p (Pre p) \<union>\<^sub>p loop p s f"
    by (metis a2 equals_equiv_relation_3 equiv_is_symetric choice_equiv l4)
  show "loop p 0 f \<equiv>\<^sub>p loop p 0 f \<union>\<^sub>p Skip (S p) \<sslash>\<^sub>p Pre p"
    using a2 equiv_is_transitive l4 l5 l6
    by (metis (no_types, lifting) choice_commute choice_idem_2) 
qed

theorem skip_compose_r_of_loop_2: "is_feasible p \<Longrightarrow> loop p s f \<equiv>\<^sub>p loop p s f ; Skip (S p)"
  apply (induction f)
  apply (metis arbitrary_repetition.simps(1) equal_is_symetric fail_compose_l_2 inverse_equality_1 skip_compose_r_of_fixed_rep_1 skip_prop_9)
  apply (cases "f>s")
  apply (auto)
  apply (auto simp: Fail_def equiv_def restr_post_def is_feasible_def Skip_def restrict_r_def composition_def) [1]
  apply (metis compose_distrib2_1 compose_feasible equiv_is_symetric choice_equiv fixed_repetition.simps(2) skip_compose2 state_space_is_same)
  apply (auto simp: Fail_def equiv_def restr_post_def is_feasible_def Skip_def restrict_r_def composition_def) [1]
  by (metis compose_distrib2_1 compose_feasible equiv_is_symetric choice_equiv fixed_repetition.simps(2) skip_compose2 state_space_is_same)

theorem skip_compose_l_of_loop_3: "is_feasible p \<Longrightarrow> loop p s f \<equiv>\<^sub>p Skip (S p) ; loop p s f"
  apply (induction f)
   apply (auto simp: Fail_def S_def equiv_def Skip_def composition_def corestrict_r_def Field_def restr_post_def restrict_r_def Domain_iff restrict_p_def) [1]
proof -
  fix f assume IH: "is_feasible p \<Longrightarrow> loop p s f \<equiv>\<^sub>p Skip (S p) ; loop p s f"
  assume feas: "is_feasible p"
  from feas IH have IH2: "loop p s f \<equiv>\<^sub>p Skip (S p) ; loop p s f" by simp
  from IH2 show "loop p s (Suc f) \<equiv>\<^sub>p Skip (S p) ; loop p s (Suc f)"
    apply (cases "f=0")
    apply (auto)
    apply (auto simp: Fail_def equiv_def Skip_def composition_def corestrict_r_def restr_post_def restrict_r_def S_def Domain_iff restrict_p_def) [1]
    apply (auto simp: Fail_def equiv_def Skip_def composition_def corestrict_r_def restr_post_def restrict_r_def Domain_iff S_def restrict_p_def) [1]
    apply (auto simp: Fail_def equiv_def Skip_def composition_def corestrict_r_def restr_post_def restrict_r_def Domain_iff S_def restrict_p_def) [1]
  proof -
    have l1: "p \<^bold>^ f ; p \<equiv>\<^sub>p Skip (S p) ; (p \<^bold>^ f ; p)"
      by (metis fixed_repetition.simps(2) skip_compose_l_of_fixed_rep_1)
    have l2 :"Skip (S p) ; loop p s f  \<union>\<^sub>p Skip (S p) ; (p \<^bold>^ f ; p) \<equiv>\<^sub>p Skip (S p) ; (loop p s f \<union>\<^sub>p p \<^bold>^ f ; p)"
      by (simp add: compose_distrib1_3 equiv_is_symetric)
    have l3: "loop p s f \<union>\<^sub>p p \<^bold>^ f ; p \<equiv>\<^sub>p Skip (S p) ; loop p s f \<union>\<^sub>p Skip (S p) ; (p \<^bold>^ f ; p)"
      by (simp add: IH2 choice_equiv l1)
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
  by (metis arbitrary_repetition.elims fail_equiv)

theorem fail_stays_fail_arbitrary: "s\<le>f \<Longrightarrow> loop p s f \<equiv>\<^sub>p Fail {} \<Longrightarrow> loop p s (Suc f) \<equiv>\<^sub>p Fail {}"
  apply (induction f)
   apply (auto simp: Skip_def equiv_def Fail_def composition_def restr_post_def restrict_r_def) [1]
proof -
  fix f assume IH: "s \<le> f \<Longrightarrow> loop p s f \<equiv>\<^sub>p Fail {} \<Longrightarrow> loop p s (Suc f) \<equiv>\<^sub>p Fail {}"
  assume a1: "s \<le> Suc f"
  assume a2: "loop p s (Suc f) \<equiv>\<^sub>p Fail {}"
  show "loop p s (Suc (Suc f)) \<equiv>\<^sub>p Fail {}"
  proof (cases "s\<le>f")
    case True
    have l1: "loop p s (Suc (Suc f)) \<equiv>\<^sub>p loop p s (Suc f) \<union>\<^sub>p loop p (Suc (Suc f)) (Suc (Suc f))"
      by (meson a1 le_SucI loop_l5 not_less_eq_eq)
    from a2 have l2: "loop p s (Suc f) \<union>\<^sub>p loop p (Suc (Suc f)) (Suc (Suc f)) \<equiv>\<^sub>p loop p (Suc (Suc f)) (Suc (Suc f))"
      by (meson equiv_is_symetric equiv_is_transitive choice_equiv fail_choice_l)
    have l3: "loop p (Suc (Suc f)) (Suc (Suc f)) \<equiv>\<^sub>p p\<^bold>^(Suc (Suc f))"
      using loop_l2_1 by blastl
    have "p\<^bold>^(Suc (Suc f)) \<equiv>\<^sub>p p\<^bold>^(Suc f) ; p"
      by (simp add: equiv_is_reflexive)
    have "loop p s (Suc f) \<equiv>\<^sub>p p\<^bold>^(Suc f) \<union>\<^sub>p loop p s f"
      using True loop_l3 by auto
    from a2 have "p\<^bold>^(Suc f) \<equiv>\<^sub>p Fail {}"
      using a1 choice_fail_implication by auto
    then show ?thesis
      using l3 equiv_is_transitive fail_stays_fail_fixed l1 l2 by blast
  next
    case False
    then have "s=Suc f"
      using a1 by auto
    have l1: "loop p s (Suc (Suc f)) \<equiv>\<^sub>p loop p (Suc f) (Suc (Suc f))"
      by (simp add: \<open>s = Suc f\<close> equiv_is_reflexive)
    have l2: "loop p (Suc f) (Suc (Suc f)) \<equiv>\<^sub>p loop p (Suc f) (Suc f) \<union>\<^sub>p loop p (Suc (Suc f)) (Suc (Suc f))"
      by (metis False Suc_le_mono \<open>s = Suc f\<close> loop_l5 nat_le_linear)
    have l3: "loop p (Suc f) (Suc f) \<equiv>\<^sub>p Fail {}"
      using \<open>s = Suc f\<close> a2 by auto
    have l4: "loop p (Suc (Suc f)) (Suc (Suc f)) \<equiv>\<^sub>p Fail {}"
      by (metis a1 a2 arbitrary_repetition.simps(2) choice_fail_implication equiv_is_transitive fail_stays_fail_fixed leD loop_l2_1)
    have l5: "loop p (Suc f) (Suc f) \<union>\<^sub>p loop p (Suc (Suc f)) (Suc (Suc f)) \<equiv>\<^sub>p Fail {}"
      using choice_fail_implication l3 l4 by blast
    from l1 l2 l3 l4 show ?thesis
      using equiv_is_transitive l5 by blast
  qed
qed

theorem fail_stays_fail_arbitrary_2: "s\<le>f \<Longrightarrow> loop p s (Suc f) \<equiv>\<^sub>p Fail {} \<Longrightarrow> loop p s f \<equiv>\<^sub>p Fail {}"
proof -
  assume a1: "s \<le> f"
  assume a2: "loop p s (Suc f) \<equiv>\<^sub>p Fail {}"
  have l1: "loop p s (Suc f) \<equiv>\<^sub>p loop p s f \<union>\<^sub>p p\<^bold>^(Suc f)"
    using a1 loop_l3 by auto
  from a2 l1 show "loop p s f \<equiv>\<^sub>p Fail {}"
    using a1 choice_fail_implication by auto
qed

theorem fail_stays_fail_arbitrary_3: "s\<le>f \<Longrightarrow> loop p s (Suc f) \<equiv>\<^sub>p Fail {} \<equiv> loop p s f \<equiv>\<^sub>p Fail {}"
  by (smt (verit) fail_stays_fail_arbitrary fail_stays_fail_arbitrary_2)

theorem fail_stays_fail_arbitrary_4: "s\<le>f \<Longrightarrow> loop p s s \<equiv>\<^sub>p Fail {} \<equiv> loop p s f \<equiv>\<^sub>p Fail {}"
  apply (induction f)
  apply simp
  by (metis fail_stays_fail_arbitrary fail_stays_fail_arbitrary_2 le_SucE)

lemma fail_arbitrary_implies_fixed: "k \<le> n \<Longrightarrow> loop (b \<sslash>\<^sub>p (- C)) 0 n \<equiv>\<^sub>p Fail {} \<Longrightarrow> (b \<sslash>\<^sub>p (- C)) \<^bold>^ k \<equiv>\<^sub>p Fail {}"
proof (induction n)
  case 0
  then show ?case by fastforce
next
  case (Suc n)
  assume IH: "k \<le> n \<Longrightarrow> loop (b \<sslash>\<^sub>p (- C)) 0 n \<equiv>\<^sub>p Fail {} \<Longrightarrow> (b \<sslash>\<^sub>p (- C)) \<^bold>^ k \<equiv>\<^sub>p Fail {}"
  assume a1: "k \<le> Suc n"
  assume a2: "loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n) \<equiv>\<^sub>p Fail {}"
  from a2 have l1: "loop (b \<sslash>\<^sub>p (- C)) 0 n \<equiv>\<^sub>p Fail {}"
    apply (cases "loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n) \<equiv>\<^sub>p Fail {}")
    apply (simp add: fail_stays_fail_arbitrary_2)
    by simp
  then show "loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n) \<equiv>\<^sub>p Fail {} \<Longrightarrow> (b \<sslash>\<^sub>p (- C)) \<^bold>^ k \<equiv>\<^sub>p Fail {}"
    by (metis IH a1 arbitrary_repetition.simps(2) choice_fail_implication le_SucE less_nat_zero_code)
qed

lemma extract_fixed_from_arbitrary: "k\<le>n \<Longrightarrow> a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C \<union>\<^sub>p a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ k) \<setminus>\<^sub>p C"
proof (induction n)
  case 0
  then show ?case by (auto simp: equiv_def restr_post_def Skip_def composition_def restrict_p_def restrict_r_def)
next
  case (Suc n)
  assume IH: "k \<le> n \<Longrightarrow> a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C \<union>\<^sub>p a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ k) \<setminus>\<^sub>p C"
  assume a1: " k \<le> Suc n"
  then show ?case
  proof (cases "k\<le>n")
    case True
    have l1: "a ; loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n) \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; (loop (b \<sslash>\<^sub>p (- C)) 0 n \<union>\<^sub>p (b \<sslash>\<^sub>p (- C)) \<^bold>^ Suc n) \<setminus>\<^sub>p C"
      by (simp add: Definitions.equiv_def)
    have l2: "a ; loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n) \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C \<union>\<^sub>p a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ Suc n) \<setminus>\<^sub>p C"
      by (simp add: equiv_is_symetric until_simplification_1)
    from l2 IH True have l3: "a ; loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n) \<setminus>\<^sub>p C \<equiv>\<^sub>p (a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C \<union>\<^sub>p a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ k) \<setminus>\<^sub>p C) \<union>\<^sub>p a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ Suc n) \<setminus>\<^sub>p C"
      by (smt (verit) composition_removes_dead_code_2 composition_simplification_2 equiv_is_transitive choice_equiv)
    from l3 have l4: "a ; loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n) \<setminus>\<^sub>p C \<equiv>\<^sub>p (a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C \<union>\<^sub>p a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ Suc n) \<setminus>\<^sub>p C) \<union>\<^sub>p a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ k) \<setminus>\<^sub>p C"
      by (metis choice_assoc_1 choice_commute)
    show ?thesis
      by (meson equiv_is_symetric equiv_is_transitive choice_equiv inverse_equality_2 l2 l4)
  next
    case False
    have l1: "k=Suc n"
      using False a1 by fastforce
    obtain p1 where o1: "p1 = a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C" by simp
    have l2: "a ; loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n) \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C \<union>\<^sub>p p1"
      by (simp add: equiv_is_symetric until_simplification_1 o1)
    have l3: "a ; loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n) \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C \<union>\<^sub>p (p1 \<union>\<^sub>p p1)"
      by (metis Definitions.equiv_def choice_def choice_idem_3 choice_state sup_idem l2)
    have l4: "a ; loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n) \<setminus>\<^sub>p C \<equiv>\<^sub>p (a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C \<union>\<^sub>p p1) \<union>\<^sub>p p1"
      using l3 by fastforce
    have l5: "a ; loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n) \<setminus>\<^sub>p C \<equiv>\<^sub>p (a ; loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n) \<setminus>\<^sub>p C) \<union>\<^sub>p p1"
      by (smt (verit, ccfv_SIG) composition_removes_dead_code_2 composition_simplification_2 equiv_is_symetric equiv_is_transitive choice_equiv l2 l4 o1)
    then show ?thesis
      by (simp add: l1 o1)
  qed
qed

lemma fail_arbitrary_implies_fixed_2: "k \<le> n \<Longrightarrow> a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C \<equiv>\<^sub>p Fail {} \<Longrightarrow> a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ k) \<setminus>\<^sub>p C \<equiv>\<^sub>p Fail {}"
proof (cases "a \<equiv>\<^sub>p Fail {}")
  case True
  obtain pr where o1: "pr = ((b \<sslash>\<^sub>p (- C)) \<^bold>^ k) \<setminus>\<^sub>p C" by simp
  have "a ; pr \<equiv>\<^sub>p Fail {}"
    by (meson True choice_idem_3 equiv_is_symetric equiv_is_transitive composition_equiv fail_compose_l fail_equiv inverse_equality_1)
  then show ?thesis
    by (simp add: o1)
next
  case False
  assume a1: "k \<le> n"
  assume a2: "a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C \<equiv>\<^sub>p Fail {}"
  from a1 have "a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C \<union>\<^sub>p a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ k) \<setminus>\<^sub>p C" using extract_fixed_from_arbitrary
    by blast
  then show ?thesis
    by (metis (no_types, lifting) Definitions.equiv_def a2 choice_fail_implication)
qed

lemma "Fail (S x) \<union>\<^sub>p x \<^bold>^ 0 = x \<^bold>^ 0"
  oops

lemma fixed_prop: "0<f \<Longrightarrow> Fail (S x) \<union>\<^sub>p x \<^bold>^ f = x \<^bold>^ f"
proof (induction f)
  case 0
  then show ?case by simp
next
  case (Suc f)
  then show "Fail (S x) \<union>\<^sub>p x \<^bold>^ Suc f = x \<^bold>^ Suc f"
  proof (cases "f=0")
    case True
    then show ?thesis by (auto simp: composition_def Skip_def restr_post_def restrict_r_def restrict_p_def corestrict_r_def S_def choice_def Fail_def Field_def)
  next
    case False
    then show ?thesis
      by (metis Fail.fail_compose Suc.IH bot_nat_0.not_eq_extremum compose_distrib2_1 fixed_repetition.simps(2))
  qed
qed

lemma loop_choice3: "0<s \<Longrightarrow> 0<f \<Longrightarrow> all_feasible [x,y] \<Longrightarrow> Range_p x \<inter> Pre y = {} \<Longrightarrow> Range_p y \<inter> Pre x = {} \<Longrightarrow> (loop x s f) \<union>\<^sub>p (loop y s f) = loop (x \<union>\<^sub>p y) s f" \<comment> \<open>Loop_choice3\<close>
proof (induction f)
  case 0
  then show ?case by simp
next
  case (Suc f)
  assume a0: "0<s"
  assume a1: "Range_p x \<inter> Pre y = {}"
  assume a2: "Range_p y \<inter> Pre x = {}"
  assume a3: "all_feasible [x,y]"
  assume IH: "0 < s \<Longrightarrow> 0 < f \<Longrightarrow> all_feasible [x, y] \<Longrightarrow> Range_p x \<inter> Pre y = {} \<Longrightarrow> Range_p y \<inter> Pre x = {} \<Longrightarrow> loop x s f \<union>\<^sub>p loop y s f = loop (x \<union>\<^sub>p y) s f"
  then show "loop x s (Suc f) \<union>\<^sub>p loop y s (Suc f) = loop (x \<union>\<^sub>p y) s (Suc f)"
  proof (cases "f=0")
    case True
    assume "f=0"
    then show ?thesis using a0
    proof (cases "s=1")
      case True
      have "loop x s (Suc f) \<union>\<^sub>p loop y s (Suc f) = loop x 1 1 \<union>\<^sub>p loop y 1 1" by (simp add: True \<open>f = 0\<close>)
      have "... = (x\<^bold>^1 \<union>\<^sub>p Fail (S x)) \<union>\<^sub>p (y\<^bold>^1 \<union>\<^sub>p Fail (S y))" by simp
      have "... = (x\<^bold>^1 \<union>\<^sub>p y\<^bold>^1) \<union>\<^sub>p Fail {}" by (smt (verit) True a0 arbitrary_repetition.elims choice_assoc_1 choice_commute choice_idem_2 loop_l2_01 loop_l2_05 nless_le)
      have "... = (Skip (S x) \<sslash>\<^sub>p (Pre x); x \<union>\<^sub>p Skip (S y) \<sslash>\<^sub>p (Pre y); y) \<union>\<^sub>p Fail {}" by simp
      have "loop (x \<union>\<^sub>p y) s (Suc f) =  loop (x \<union>\<^sub>p y) 1 1" by (simp add: True \<open>f = 0\<close>)
      have "... = (x \<union>\<^sub>p y)\<^bold>^1 \<union>\<^sub>p Fail (S x \<union> S y)" by simp
      have "... = Skip (S x \<union> S y) \<sslash>\<^sub>p (Pre x \<union> Pre y); (x \<union>\<^sub>p y) \<union>\<^sub>p Fail {} " by (metis One_nat_def \<open>loop (x \<union>\<^sub>p y) 1 1 = (x \<union>\<^sub>p y) \<^bold>^ 1 \<union>\<^sub>p Fail (S x \<union> S y)\<close> choice_commute choice_pre choice_state special_empty1 loop_l1 loop_l2_02 skip_prop_12)
      have "(Skip (S x) \<sslash>\<^sub>p (Pre x); x \<union>\<^sub>p Skip (S y) \<sslash>\<^sub>p (Pre y); y) \<union>\<^sub>p Fail {} = Skip (S x \<union> S y) \<sslash>\<^sub>p (Pre x \<union> Pre y); (x \<union>\<^sub>p y) \<union>\<^sub>p Fail {}"
        by (metis Fixed_repetition.fixed_prop One_nat_def choice_pre choice_state fixed_repetition.simps(1) fixed_repetition.simps(2) skip_choice)
      from a1 a2 a3 have "loop x 1 1 \<union>\<^sub>p loop y 1 1 = loop (x \<union>\<^sub>p y) 1 1"
        using \<open>(Skip (S x) \<sslash>\<^sub>p Pre x ; x \<union>\<^sub>p Skip (S y) \<sslash>\<^sub>p Pre y ; y) \<union>\<^sub>p Fail {} = Skip (S x \<union> S y) \<sslash>\<^sub>p (Pre x \<union> Pre y) ; (x \<union>\<^sub>p y) \<union>\<^sub>p Fail {}\<close> \<open>(x \<^bold>^ 1 \<union>\<^sub>p Fail (S x)) \<union>\<^sub>p (y \<^bold>^ 1 \<union>\<^sub>p Fail (S y)) = (x \<^bold>^ 1 \<union>\<^sub>p y \<^bold>^ 1) \<union>\<^sub>p Fail {}\<close> \<open>(x \<^bold>^ 1 \<union>\<^sub>p y \<^bold>^ 1) \<union>\<^sub>p Fail {} = (Skip (S x) \<sslash>\<^sub>p Pre x ; x \<union>\<^sub>p Skip (S y) \<sslash>\<^sub>p Pre y ; y) \<union>\<^sub>p Fail {}\<close> \<open>(x \<union>\<^sub>p y) \<^bold>^ 1 \<union>\<^sub>p Fail (S x \<union> S y) = Skip (S x \<union> S y) \<sslash>\<^sub>p (Pre x \<union> Pre y) ; (x \<union>\<^sub>p y) \<union>\<^sub>p Fail {}\<close> \<open>loop (x \<union>\<^sub>p y) 1 1 = (x \<union>\<^sub>p y) \<^bold>^ 1 \<union>\<^sub>p Fail (S x \<union> S y)\<close> \<open>loop x 1 1 \<union>\<^sub>p loop y 1 1 = (x \<^bold>^ 1 \<union>\<^sub>p Fail (S x)) \<union>\<^sub>p (y \<^bold>^ 1 \<union>\<^sub>p Fail (S y))\<close> by presburger
      then show ?thesis
        by (simp add: True \<open>f = 0\<close>)
    next
      case False
      have "loop x s (Suc f) = Fail (S x)" using False \<open>f = 0\<close> a0 by auto
      have "loop y s (Suc f) = Fail (S y)" using False \<open>f = 0\<close> a0 by auto
      have "loop (x \<union>\<^sub>p y) s (Suc f) = Fail (S x \<union> S y)" using False \<open>f = 0\<close> a0 by auto
      have "Fail (S x) \<union>\<^sub>p Fail (S y) = Fail (S x \<union> S y)" by (auto simp: choice_def Fail_def S_def restr_post_def restrict_r_def)
      then show ?thesis
        using \<open>loop (x \<union>\<^sub>p y) s (Suc f) = Fail (S x \<union> S y)\<close> \<open>loop x s (Suc f) = Fail (S x)\<close> \<open>loop y s (Suc f) = Fail (S y)\<close> by argo
    qed
    next
      case False
      have IH2: "loop x s f \<union>\<^sub>p loop y s f = loop (x \<union>\<^sub>p y) s f"
        using False IH Suc.prems(4) a0 a2 a3 by blast
      then show ?thesis
    proof (cases "s\<le>f")
      case True
      assume a1: "s\<le>f"
      have l1: "loop x s (Suc f) = loop x s f \<union>\<^sub>p x\<^bold>^(Suc f)"
        using a1 equiv_is_reflexive by auto
      have l2: "loop y s (Suc f) = loop y s f \<union>\<^sub>p y\<^bold>^(Suc f)"
        using a1 equiv_is_reflexive by auto
      have l3: "loop x s (Suc f) \<union>\<^sub>p loop y s (Suc f) = (loop x s f \<union>\<^sub>p x\<^bold>^(Suc f)) \<union>\<^sub>p (loop y s f \<union>\<^sub>p y\<^bold>^(Suc f))"
        using choice_equiv l1 l2
        by argo
      then have l4: "(loop x s f \<union>\<^sub>p x\<^bold>^(Suc f)) \<union>\<^sub>p (loop y s f \<union>\<^sub>p y\<^bold>^(Suc f)) = (loop x s f \<union>\<^sub>p x\<^bold>^(Suc f)) \<union>\<^sub>p (loop y s f \<union>\<^sub>p y\<^bold>^(Suc f))"
        using equals_equiv_relation_3 by blast
      then have l5: "loop x s (Suc f) \<union>\<^sub>p loop y s (Suc f) = (loop x s f \<union>\<^sub>p loop y s f) \<union>\<^sub>p (x\<^bold>^(Suc f) \<union>\<^sub>p y\<^bold>^(Suc f))"
        by (metis (no_types, lifting) choice_assoc_1 choice_commute l3)
      have l6: "x\<^bold>^(Suc f) \<union>\<^sub>p y\<^bold>^(Suc f) = (x \<union>\<^sub>p y)\<^bold>^(Suc f)"
        using Suc.prems(2) a2 a3 arbitrary_repetition_simplification2
        using Suc.prems(4) arbitrary_repetition_simplification by blast
      from l5 l6 show ?thesis apply (auto)
        using a1 apply auto[1]
        by (smt (verit, ccfv_SIG) IH2 choice_assoc_1 equiv_is_transitive choice_equiv)
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
        have l11: "Fail (S x) \<union>\<^sub>p x \<^bold>^ (Suc f) = x \<^bold>^ (Suc f)"
          using Arbitrary_repetition.fixed_prop by blast
        have l12: "Fail (S y) \<union>\<^sub>p y \<^bold>^ (Suc f) = y \<^bold>^ (Suc f)"
          using Arbitrary_repetition.fixed_prop by blast
        have l17: "Fail (S y \<union> S x) \<union>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ (Suc f) = (x \<union>\<^sub>p y) \<^bold>^ (Suc f)"
          by (metis Arbitrary_repetition.fixed_prop a0 choice_commute choice_state local.l4)
        from a3 a1 a2 arbitrary_repetition_simplification2 have l18: " x \<^bold>^ (Suc f) \<union>\<^sub>p  y \<^bold>^ (Suc f) = (x \<union>\<^sub>p y) \<^bold>^ (Suc f)"
          using arbitrary_repetition_simplification by blast
        from l4 l11 l12 l17 show "loop x s f \<union>\<^sub>p (x \<^bold>^ f ; x \<union>\<^sub>p (loop y s f \<union>\<^sub>p y \<^bold>^ f ; y)) = loop (x \<union>\<^sub>p y) s f \<union>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ f ; (x \<union>\<^sub>p y)"
        proof -
          have f1: "x \<^bold>^ s \<union>\<^sub>p y \<^bold>^ s = (x \<union>\<^sub>p y) \<^bold>^ s"
            by (smt (z3) l18 l4)
          have "Fail (S x) \<union>\<^sub>p Fail (S y) = Fail (S (x \<union>\<^sub>p y))"
            by (metis IH2 local.l4 loop_l2_01)
          then have "Fail (S x) \<union>\<^sub>p (Fail (S y) \<union>\<^sub>p (x \<^bold>^ s \<union>\<^sub>p y \<^bold>^ s)) = Fail (S (x \<union>\<^sub>p y)) \<union>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ s"
            using f1 by (metis choice_assoc_1)
          then have "loop x s f \<union>\<^sub>p (x \<^bold>^ s \<union>\<^sub>p (y \<^bold>^ s \<union>\<^sub>p loop y s f)) = (x \<union>\<^sub>p y) \<^bold>^ s \<union>\<^sub>p loop (x \<union>\<^sub>p y) s f"
            by (smt (z3) choice_assoc_1 choice_commute l4 loop_l2_01)
          then show ?thesis
            by (simp add: l4)
        qed
      qed
    qed
  qed
qed

theorem Loop_fail: "loop p 0 n \<equiv>\<^sub>p Fail {} \<Longrightarrow> loop p 0 m \<equiv>\<^sub>p Fail{}" \<comment> \<open>/Loop_fail/\<close>
  apply (cases "n\<le>m")
  apply (meson bot_nat_0.extremum fail_stays_fail_arbitrary_4)
  by (meson bot_nat_0.extremum fail_stays_fail_arbitrary_4)
end