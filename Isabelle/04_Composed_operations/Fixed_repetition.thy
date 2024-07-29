theory Fixed_repetition
  imports 
"../T_03_Basic_programs" (*Fixed_repetition_support*)
begin
section \<open>Fixed repetition for top\<close>


theorem mapping_fixed_and_fixed_sup_1: "0<n \<Longrightarrow> p ^\<^sup>p n = p \<^bold>^ n"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  assume a1: "0 < Suc n"
  assume IH: "0 < n \<Longrightarrow> p ^\<^sup>p n = p \<^bold>^ n"
  then show ?case
  proof (cases "n=0")
    case True
    then show ?thesis
      by (auto simp: Skip_def composition_def S_def Field_def corestrict_r_def restr_post_def restrict_r_def)
  next
    case False
    assume a2: "n\<noteq>0"
    from a2 have l1: "0<n" by simp
    from l1 IH have IH2: "p ^\<^sup>p n = p \<^bold>^ n" by simp
    have l2: "p ^\<^sup>p Suc n \<equiv>\<^sub>p p ^\<^sup>p n ; p"
      by (simp add: equiv_is_reflexive)
    from l1 have l3: "p \<^bold>^ Suc n \<equiv>\<^sub>p p \<^bold>^ n ; p"
      using IH l2 by auto
    then show ?thesis
      by (simp add: IH2)
  qed
qed

theorem mapping_fixed_and_fixed_sup_2: "0<n \<Longrightarrow> p ^\<^sup>p n \<triangleq> p \<^bold>^ n"
  by (simp add: equals_equiv_relation_1 mapping_fixed_and_fixed_sup_1)

theorem mapping_fixed_and_fixed_sup_3: "0<n \<Longrightarrow> p ^\<^sup>p n \<equiv>\<^sub>p p \<^bold>^ n"
  by (simp add: equals_equiv_relation_3 mapping_fixed_and_fixed_sup_1)


theorem state_space_is_same: "0<n \<Longrightarrow> S p = S (p \<^bold>^ n)"
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  assume IH: "0 < n \<Longrightarrow> S p = S (p \<^bold>^ n)"
  then show ?case
  proof (cases "n=0")
    case True
    then show ?thesis
      by (auto simp: Skip_def composition_def corestrict_r_def restr_post_def restrict_r_def S_def Field_def)
  next
    case False
    then have IH2: "S p = S (p \<^bold>^ n)" using IH by simp
    have l1: "p \<^bold>^ Suc n = p \<^bold>^ n ; p" by simp
    then have l2: "S (p \<^bold>^ n ; p) = S p"
      by (simp add: IH2)
    then show ?thesis
      by simp
  qed
qed

theorem fixed_rep_one_1: "p\<^bold>^1 \<equiv>\<^sub>p p \<sslash>\<^sub>p (Pre p)"
  by (auto simp: Skip_def composition_def corestrict_r_def restr_post_def restrict_r_def equiv_def restrict_p_def)

theorem fixed_rep_one_2: "is_feasible p \<Longrightarrow> p\<^bold>^1 \<equiv>\<^sub>p p"
  by (auto simp: Skip_def composition_def corestrict_r_def restr_post_def restrict_r_def equiv_def)

theorem fixed_rep_decomp_front: "0<i \<Longrightarrow> is_feasible p \<Longrightarrow> p\<^bold>^(Suc i) \<equiv>\<^sub>p p;p\<^bold>^i"
  proof (induction i)
    case 0
    then show ?case
      by (auto)
  next
    case (Suc i)
    assume a1: "is_feasible p"
    assume a2: "0 < Suc i"
    assume IH: "0 < i \<Longrightarrow> is_feasible p \<Longrightarrow> p \<^bold>^ Suc i \<equiv>\<^sub>p p ; p \<^bold>^ i"
    then show ?case
      apply (cases "i = 0")
    proof -
      assume a3: "i = 0"
      have l3: "p ; p \<^bold>^ 1 \<equiv>\<^sub>p p \<^bold>^ 2"
        by (metis Suc_1 a1 equiv_is_symetric equivalence_is_maintained_by_composition fixed_rep_one_2 fixed_repetition.simps(2))
      show "p \<^bold>^ Suc (Suc i) \<equiv>\<^sub>p p ; p \<^bold>^ Suc i"
        by (metis One_nat_def Suc_1 a3 equiv_is_symetric l3)
    next
      assume a3: "i \<noteq> 0"
      have IH2: "p \<^bold>^ Suc i \<equiv>\<^sub>p p ; p \<^bold>^ i"
        using IH a1 a3 by auto
      have l1: "p \<^bold>^ Suc (Suc i) \<equiv>\<^sub>p p \<^bold>^ Suc i ; p"
        by (simp add: equiv_is_reflexive)
      have l2: "p \<^bold>^ Suc i ; p \<equiv>\<^sub>p (p ; p \<^bold>^ i) ; p"
        using IH2 equiv_is_reflexive equivalence_is_maintained_by_composition by blast
      show "p \<^bold>^ Suc (Suc i) \<equiv>\<^sub>p p ; p \<^bold>^ Suc i"
        using l2 by auto
      qed
    qed


theorem fixed_rep_decomp_back: "is_feasible p \<Longrightarrow> p\<^bold>^(Suc i) \<equiv>\<^sub>p p\<^bold>^i;p"
  by (simp add: equiv_is_reflexive)

theorem fixed_rep_feasibility: "is_feasible p \<Longrightarrow> is_feasible (p\<^bold>^n)"
proof (induction n)
  case 0
  then show ?case by (auto simp: is_feasible_def Skip_def)
next
  case (Suc n)
  assume IH: "is_feasible p \<Longrightarrow> is_feasible (p \<^bold>^ n)"
  assume a1: "is_feasible p"
  from IH a1 have IH2: "is_feasible (p \<^bold>^ n)" by simp
  have l1: "p \<^bold>^ Suc n \<equiv>\<^sub>p p \<^bold>^ n ; p"
    by (simp add: equiv_is_reflexive)
  then show ?case
    by (simp add: a1 composition_makes_feasible)
qed
theorem fixed_rep_prop_2: "p\<^bold>^(Suc i) \<equiv>\<^sub>p p\<^bold>^i;p"
  oops \<comment> \<open>Not true because Skip;p /= p;Skip\<close>

theorem range_decreases_fixed_repetition: "0 < n \<Longrightarrow> Range_p (x \<^bold>^ n) \<subseteq> Range_p x"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  assume a1: "0 < Suc n"
  assume IH: " 0 < n \<Longrightarrow> Range_p (x \<^bold>^ n) \<subseteq> Range_p x"
  then show "Range_p (x \<^bold>^ Suc n) \<subseteq> Range_p x"
  proof (cases "n=0")
    case True
    then show ?thesis by (auto simp: Range_p_def Skip_def composition_def restr_post_def restrict_r_def)
  next
    case False
    then show ?thesis
      by (simp add: range_decreases_composition)
  qed
qed

lemma arbitrary_repetition_simplification: "all_feasible [x,y] \<Longrightarrow> Range_p x \<inter> Pre y = {} \<Longrightarrow> Range_p y \<inter> Pre x = {} \<Longrightarrow> x\<^bold>^n \<union>\<^sub>p y\<^bold>^n \<equiv>\<^sub>p (x \<union>\<^sub>p y)\<^bold>^n" \<comment> \<open>NEW\<close>
proof (induction n)
  case 0
  then show ?case apply (auto)
    by (simp add: skip_prop)
next
  case (Suc n)
  assume a1: "all_feasible [x,y]"
  assume a2: "Range_p x \<inter> Pre y = {}"
  assume a3: "Range_p y \<inter> Pre x = {}"
  assume IH:"all_feasible [x, y] \<Longrightarrow> Range_p x \<inter> Pre y = {} \<Longrightarrow> Range_p y \<inter> Pre x = {} \<Longrightarrow> x \<^bold>^ n \<union>\<^sub>p y \<^bold>^ n \<equiv>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ n"

  from a2 have l0: "0<n \<Longrightarrow> Range_p (x \<^bold>^ n) \<inter> Pre y = {}"
    by (metis inf.orderE inf_bot_right inf_commute inf_left_commute range_decreases_fixed_repetition)
  from a1 a2 a3 IH have l0: "x \<^bold>^ n \<union>\<^sub>p y \<^bold>^ n \<equiv>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ n"
    by simp  
  have l1: "0<n \<Longrightarrow> x \<^bold>^ Suc n \<equiv>\<^sub>p x; x \<^bold>^ n"
    using a1 fixed_rep_decomp_front by auto
  have l2: "y \<^bold>^ Suc n \<equiv>\<^sub>p y \<^bold>^ n;y"
    by (simp add: equals_equiv_relation_3)
  from a1 have l3: "x \<^bold>^ Suc n \<union>\<^sub>p y \<^bold>^ Suc n \<equiv>\<^sub>p (x \<^bold>^ n;x) \<union>\<^sub>p (y \<^bold>^ n;y)"
    by (simp add: equals_equiv_relation_3)
  then show "x \<^bold>^ Suc n \<union>\<^sub>p y \<^bold>^ Suc n \<equiv>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ Suc n"
  proof (cases "n=0")
    case True
    assume a4: "n=0"
    from a4 have l4: "Suc n = 1" by simp
    then show ?thesis 
      apply (auto simp: equiv_def)
          apply (auto simp: composition_def Skip_def choice_def restr_post_def restrict_r_def corestrict_r_def S_def Domain_iff Field_def) [3]
      apply (simp add: restr_post_def composition_def Skip_def S_def Field_def restrict_r_def relcomp_unfold corestrict_r_def Domain_iff Range_iff)
      apply metis
      apply (simp add: restr_post_def composition_def Skip_def S_def Field_def restrict_r_def relcomp_unfold corestrict_r_def Domain_iff Range_iff)
      by metis
  next
    case False
    assume a4: "n\<noteq>0"
    assume a5: "x \<^bold>^ Suc n \<union>\<^sub>p y \<^bold>^ Suc n \<equiv>\<^sub>p x \<^bold>^ n ; x \<union>\<^sub>p y \<^bold>^ n ; y"
    have IH2: " x \<^bold>^ n \<union>\<^sub>p y \<^bold>^ n \<equiv>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ n"
      by (simp add: l0)
    from a4 have l4: "0<n" by simp
    from a2 l4 have l7: "Range_p (x \<^bold>^ n) \<inter> Pre y = {}"
      by (metis inf_bot_right inf_commute inf_left_commute le_iff_inf range_decreases_fixed_repetition)
    from a3 l4 have l8: "Range_p (y \<^bold>^ n) \<inter> Pre x = {}"
      by (metis inf_bot_right inf_commute inf_left_commute le_iff_inf range_decreases_fixed_repetition)
    from a1 have l9: "(x \<union>\<^sub>p y) \<^bold>^ Suc n \<equiv>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ n ; (x \<union>\<^sub>p y)"
      by (simp add: equals_equiv_relation_3)
    from l7 l8 have "x \<^bold>^ n ; x \<union>\<^sub>p y \<^bold>^ n ; y \<equiv>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ n ; (x \<union>\<^sub>p y)"
      by (meson choice_commute_3 condition_for_choice_simplification equiv_is_transitive equivalence_is_maintained_by_composition l0)
    then show "x \<^bold>^ Suc n \<union>\<^sub>p y \<^bold>^ Suc n \<equiv>\<^sub>p (x \<union>\<^sub>p y) \<^bold>^ Suc n"
      by (meson equiv_is_symetric equiv_is_transitive l3 l9)
  qed
qed

theorem equality_is_maintained_by_fixed_repetition: "p\<^sub>1 \<triangleq> p\<^sub>2 \<Longrightarrow> p\<^sub>1\<^bold>^n \<triangleq> p\<^sub>2\<^bold>^n"
  apply (induction n)
  apply (auto simp: equal_def) [1]
  by (simp add: equality_is_maintained_by_composition)

theorem equiv_is_maintained_by_fixed_repetition: "0<n \<Longrightarrow> all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>1\<^bold>^n \<equiv>\<^sub>p p\<^sub>2\<^bold>^n"
  apply (induction n)
   apply auto [1]
proof -
  fix n assume a1:"0 < Suc n"
  assume a2: "p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2"
  assume a3: "all_feasible [p\<^sub>1, p\<^sub>2]"
  assume IH: "0 < n \<Longrightarrow> all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>1 \<^bold>^ n \<equiv>\<^sub>p p\<^sub>2 \<^bold>^ n"
  show "p\<^sub>1 \<^bold>^ Suc n \<equiv>\<^sub>p p\<^sub>2 \<^bold>^ Suc n"
  proof (cases "n=0")
    case True
    assume a4: "n=0"
    then have l1: "Suc n = 1" by simp
    from l1 a2 a3 show ?thesis 
      apply (auto)
      using l1 a2 a3 apply (auto)
      by (metis equiv_is_symetric equiv_is_transitive fixed_rep_one_2 fixed_repetition.simps(1) fixed_repetition.simps(2) l1)
  next
    case False
    assume a4: "n\<noteq>0"
    then have l1: "0<n" by simp
    from l1 a3 IH have IH2: "p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>1 \<^bold>^ n \<equiv>\<^sub>p p\<^sub>2 \<^bold>^ n" by simp
    show ?thesis
      by (simp add: IH2 a2 equivalence_is_maintained_by_composition)
  qed
qed

theorem skip_compose_r_of_fixed_rep_1: "is_feasible p \<Longrightarrow> p\<^bold>^n \<equiv>\<^sub>p p\<^bold>^n ; Skip (S p)"
  apply (cases "n=0")
  apply (auto) [1]
   apply (metis (no_types, lifting) Restriction.restrict_prop_1 TRUE_def equal_def equiv_is_symetric equiv_is_transitive restrict_true skip_prop_3 skip_prop_5)
proof -
  assume a1: " n \<noteq> 0"
  assume a2: "is_feasible p"
  have l1: "p \<^bold>^ n \<equiv>\<^sub>p p \<^bold>^ (n-1) ; p"
    by (metis Suc_diff_1 a1 a2 fixed_rep_decomp_back gr_zeroI)
  have l2: "p \<equiv>\<^sub>p p ; Skip (S p)"
    by (simp add: a2 equiv_is_symetric skip_compose_r_2)
  have l3: "p \<^bold>^ (n-1) ; p \<equiv>\<^sub>p p \<^bold>^ (n-1) ; (p ; Skip (S p))"
    by (simp add: equiv_is_reflexive equivalence_is_maintained_by_composition l2)
  have l4: "p \<^bold>^ (n-1) ; (p ; Skip (S p)) \<equiv>\<^sub>p (p \<^bold>^ (n-1) ; p) ; Skip (S p)"
    using compose_assoc_3 by auto
  show "p \<^bold>^ n \<equiv>\<^sub>p p \<^bold>^ n ; Skip (S p)"
    by (metis Suc_diff_1 a1 compose_assoc fixed_repetition.simps(2) l3 not_gr_zero)
qed

theorem skip_compose_l_of_fixed_rep_1: "p\<^bold>^n \<equiv>\<^sub>p Skip (S p) ; p\<^bold>^n"
  apply (cases "n=0")
  apply (auto) [1]
   apply (metis Definitions.equiv_def Int_absorb Int_subset_iff Restriction.restrict_prop_1 equiv_is_symetric is_total_def restrict_p_def select_convs(2) skip_is_idempondent_composition skip_is_total skip_prop_3 skip_prop_6)
  using skip_compose_l apply (auto)
  by (smt (verit) equiv_is_symetric skip_compose_l state_space_is_same)


end