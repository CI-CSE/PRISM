theory Fixed_repetition_support
  imports 
"../T_03_Basic_programs"
begin
section \<open>Fixed repetition support for top\<close>

theorem fixed_rep_sup_decomp_front: "is_feasible p \<Longrightarrow> p ^\<^sup>p (Suc i) \<equiv>\<^sub>p p;p ^\<^sup>p i"
proof (induction i)
  case 0
  then show ?case
    apply (auto)
    using equiv_is_symetric equiv_is_transitive skip_compose_l skip_compose_r_2 by blast
next
  case (Suc i)
  assume a1: "is_feasible p"
  assume IH: "is_feasible p \<Longrightarrow> p ^\<^sup>p (Suc i) \<equiv>\<^sub>p p;p ^\<^sup>p i"
  have l1: "p ^\<^sup>p (Suc i) \<equiv>\<^sub>p p; p ^\<^sup>p i"
    using IH a1 by auto
  then show ?case
    using equiv_is_reflexive equivalence_is_maintained_by_composition by fastforce
qed

theorem fixed_rep_sup_decomp_back: "is_feasible p \<Longrightarrow> p ^\<^sup>p (Suc i) \<equiv>\<^sub>p p ^\<^sup>p i;p"
  by (simp add: equiv_is_reflexive)

theorem fixed_rep_sup_feasibility: "is_feasible p \<Longrightarrow> is_feasible (p^\<^sup>pn)"
proof (induction n)
  case 0
  then show ?case
    by (simp add: skip_is_feasible)
next
  case (Suc n)
  assume IH: "is_feasible p \<Longrightarrow> is_feasible (p ^\<^sup>p n)"
  assume a1: "is_feasible p"
  from IH a1 have l1: "is_feasible (p^\<^sup>pn)" by simp
  have l2: "p ^\<^sup>p Suc n = p ^\<^sup>p n;p"
    by simp
  from compose_feasible l1 a1 have l3: "is_feasible (p ^\<^sup>p n;p)"
    by auto
  then show "is_feasible (p ^\<^sup>p Suc n)"
    by simp
qed

theorem fixed_rep_sup_prop_2: "p^\<^sup>p(Suc i) \<equiv>\<^sub>p p^\<^sup>pi;p"
  oops \<comment> \<open>Not true because Skip;p /= p;Skip\<close>

theorem range_decreases_fixed_repetition_sup: "0 < n \<Longrightarrow> Range_p (x ^\<^sup>p n) \<subseteq> Range_p x"
  apply (induction n)
  apply (simp)
proof -
  fix n assume a1: "0 < Suc n"
  assume IH: "0 < n \<Longrightarrow> Range_p (x ^\<^sup>p n) \<subseteq> Range_p x"
  show "Range_p (x ^\<^sup>p Suc n) \<subseteq> Range_p x"
  proof (cases "n=0")
    case True
    assume a2: "n = 0"
    from a2 have l1: "Suc n = 1" by simp
    from a2 l1 show ?thesis by (auto simp: Skip_def composition_def Range_p_def restr_post_def restrict_r_def)
  next
    case False
    assume a2: "n \<noteq> 0"
    from a2 have l1: "0<n" by simp
    from l1 IH have IH2: "Range_p (x ^\<^sup>p n) \<subseteq> Range_p x" by simp
    from range_decreases_composition IH2 show "Range_p (x ^\<^sup>p Suc n) \<subseteq> Range_p x"
      by fastforce
  qed
qed

lemma arbitrary_repetition_sup_simplification: "all_feasible [x,y] \<Longrightarrow> Range_p x \<inter> Pre y = {} \<Longrightarrow> Range_p y \<inter> Pre x = {} \<Longrightarrow> x^\<^sup>pn \<union>\<^sub>p y^\<^sup>pn \<equiv>\<^sub>p (x \<union>\<^sub>p y)^\<^sup>pn" \<comment> \<open>NEW\<close>
proof (induction n)
  case 0
  then show ?case apply (auto)
    by (simp add: skip_prop)
next
  case (Suc n)
  assume a1: "all_feasible [x,y]"
  assume a2: "Range_p x \<inter> Pre y = {}"
  assume a3: "Range_p y \<inter> Pre x = {}"
  assume IH:"all_feasible [x, y] \<Longrightarrow> Range_p x \<inter> Pre y = {} \<Longrightarrow> Range_p y \<inter> Pre x = {} \<Longrightarrow> x ^\<^sup>p n \<union>\<^sub>p y ^\<^sup>p n \<equiv>\<^sub>p (x \<union>\<^sub>p y) ^\<^sup>p n"

  from a2 have l0: "0<n \<Longrightarrow> Range_p (x ^\<^sup>p n) \<inter> Pre y = {}"
    by (metis Int_iff disjoint_iff_not_equal inf.absorb_iff2 range_decreases_fixed_repetition_sup)
  from a1 a2 a3 IH have l0: "x ^\<^sup>p n \<union>\<^sub>p y ^\<^sup>p n \<equiv>\<^sub>p (x \<union>\<^sub>p y) ^\<^sup>p n"
    by simp  
  have l1: "x ^\<^sup>p Suc n \<equiv>\<^sub>p x; x ^\<^sup>p n"
    using a1 fixed_rep_sup_decomp_front by auto
  have l2: "y ^\<^sup>p Suc n \<equiv>\<^sub>p y ^\<^sup>p n;y"
    by (simp add: equals_equiv_relation_3)
  from a1 have l3: "x ^\<^sup>p Suc n \<union>\<^sub>p y ^\<^sup>p Suc n \<equiv>\<^sub>p (x ^\<^sup>p n;x) \<union>\<^sub>p (y ^\<^sup>p n;y)"
    by (simp add: equals_equiv_relation_3)
  then show "x ^\<^sup>p Suc n \<union>\<^sub>p y ^\<^sup>p Suc n \<equiv>\<^sub>p (x \<union>\<^sub>p y) ^\<^sup>p Suc n"
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
    assume a5: "x ^\<^sup>p Suc n \<union>\<^sub>p y ^\<^sup>p Suc n \<equiv>\<^sub>p x ^\<^sup>p n ; x \<union>\<^sub>p y ^\<^sup>p n ; y"
    have IH2: " x ^\<^sup>p n \<union>\<^sub>p y ^\<^sup>p n \<equiv>\<^sub>p (x \<union>\<^sub>p y) ^\<^sup>p n"
      by (simp add: l0)
    from a4 have l4: "0<n" by simp
    from a2 l4 have l7: "Range_p (x ^\<^sup>p n) \<inter> Pre y = {}"
      by (metis inf_bot_right inf_commute inf_left_commute le_iff_inf range_decreases_fixed_repetition_sup)
    from a3 l4 have l8: "Range_p (y ^\<^sup>p n) \<inter> Pre x = {}"
      by (metis inf_bot_right inf_commute inf_left_commute le_iff_inf range_decreases_fixed_repetition_sup)
    from a1 have l9: "(x \<union>\<^sub>p y) ^\<^sup>p Suc n \<equiv>\<^sub>p (x \<union>\<^sub>p y) ^\<^sup>p n ; (x \<union>\<^sub>p y)"
      by (simp add: equals_equiv_relation_3)
    from l7 l8 have "x ^\<^sup>p n ; x \<union>\<^sub>p y ^\<^sup>p n ; y \<equiv>\<^sub>p (x \<union>\<^sub>p y) ^\<^sup>p n ; (x \<union>\<^sub>p y)"
      by (meson choice_commute_3 condition_for_choice_simplification equiv_is_transitive equivalence_is_maintained_by_composition l0)
    then show "x ^\<^sup>p Suc n \<union>\<^sub>p y ^\<^sup>p Suc n \<equiv>\<^sub>p (x \<union>\<^sub>p y) ^\<^sup>p Suc n"
      by (meson equiv_is_symetric equiv_is_transitive l3 l9)
  qed
qed

theorem equality_is_maintained_by_fixed_repetition_sup: "p\<^sub>1 \<triangleq> p\<^sub>2 \<Longrightarrow> p\<^sub>1^\<^sup>pn \<triangleq> p\<^sub>2^\<^sup>pn"
  apply (induction n)
  apply (auto simp: equal_def) [1]
  by (simp add: equality_is_maintained_by_composition)

theorem equiv_is_maintained_by_fixed_repetition_sup: "0<n \<Longrightarrow> all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>1^\<^sup>pn \<equiv>\<^sub>p p\<^sub>2^\<^sup>pn"
  apply (induction n)
   apply auto [1]
proof -
  fix n assume a1:"0 < Suc n"
  assume a2: "p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2"
  assume a3: "all_feasible [p\<^sub>1, p\<^sub>2]"
  assume IH: "0 < n \<Longrightarrow> all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>1 ^\<^sup>p n \<equiv>\<^sub>p p\<^sub>2 ^\<^sup>p n"
  show "p\<^sub>1 ^\<^sup>p Suc n \<equiv>\<^sub>p p\<^sub>2 ^\<^sup>p Suc n"
  proof (cases "n=0")
    case True
    assume a4: "n=0"
    then have l1: "Suc n = 1" by simp
    from l1 a2 a3 show ?thesis 
      apply (auto)
      using l1 a2 a3 apply (auto)
      by (metis Definitions.equiv_def skip_compose_l)
  next
    case False
    assume a4: "n\<noteq>0"
    then have l1: "0<n" by simp
    from l1 a3 IH have IH2: "p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>1 ^\<^sup>p n \<equiv>\<^sub>p p\<^sub>2 ^\<^sup>p n" by simp
    from a3 have l2: "p\<^sub>1 ^\<^sup>p Suc n \<equiv>\<^sub>p p\<^sub>1 ^\<^sup>p n ; p\<^sub>1"
      by (simp add: equals_equiv_relation_3)
    from a3 have l3: "p\<^sub>2 ^\<^sup>p Suc n \<equiv>\<^sub>p p\<^sub>2 ^\<^sup>p n ; p\<^sub>2"
      by (simp add: equals_equiv_relation_3)
    from l2 l3 show ?thesis
      by (simp add: IH2 a2 equivalence_is_maintained_by_composition)
  qed
qed

theorem skip_compose_r_of_fixed_rep_sup_1: "is_feasible p \<Longrightarrow> p^\<^sup>pn \<equiv>\<^sub>p p^\<^sup>pn ; Skip (S p)"
  apply (cases "n=0")
  apply (metis compose_assoc_3 fixed_repetition_helper.simps(1) skip_is_idempondent_composition)
proof -
  assume a1: " n \<noteq> 0"
  assume a2: "is_feasible p"
  have l1: "p ^\<^sup>p n \<equiv>\<^sub>p p ^\<^sup>p (n-1) ; p"
    by (metis Suc_diff_1 a1 equiv_is_reflexive fixed_repetition_helper.simps(2) not_gr_zero)
  have l2: "p \<equiv>\<^sub>p p ; Skip (S p)"
    by (simp add: a2 equiv_is_symetric skip_compose_r_2)
  have l3: "p ^\<^sup>p (n-1) ; p \<equiv>\<^sub>p p ^\<^sup>p (n-1) ; (p ; Skip (S p))"
    by (simp add: equiv_is_reflexive equivalence_is_maintained_by_composition l2)
  have l4: "p ^\<^sup>p (n-1) ; (p ; Skip (S p)) \<equiv>\<^sub>p (p ^\<^sup>p (n-1) ; p) ; Skip (S p)"
    using compose_assoc_3 by auto
  show "p ^\<^sup>p n \<equiv>\<^sub>p p ^\<^sup>p n ; Skip (S p)"
    by (metis Suc_diff_1 a1 compose_assoc fixed_repetition_helper.simps(2) l3 not_gr_zero)
qed

theorem skip_compose_l_of_fixed_rep_sup_1: "is_feasible p \<Longrightarrow> p^\<^sup>pn \<equiv>\<^sub>p Skip (S p) ; p^\<^sup>pn"
  apply (induction n)
  apply (metis compose_assoc_3 fixed_repetition_helper.simps(1) skip_is_idempondent_composition)
proof -
  assume a1: "is_feasible p"
  fix n assume IH: "is_feasible p \<Longrightarrow> p ^\<^sup>p n \<equiv>\<^sub>p Skip (S p) ; p ^\<^sup>p n"
  from a1 IH have IH2: "p ^\<^sup>p n \<equiv>\<^sub>p Skip (S p) ; p ^\<^sup>p n" by simp
  have l1: "p ^\<^sup>p Suc n \<equiv>\<^sub>p p ^\<^sup>p n ; p"
    using a1 fixed_rep_sup_decomp_back by auto
  from l1 show "is_feasible p \<Longrightarrow> p ^\<^sup>p Suc n \<equiv>\<^sub>p Skip (S p) ; p ^\<^sup>p Suc n"
    by (metis IH compose_assoc equals_equiv_relation_3 equivalence_is_maintained_by_composition fixed_repetition_helper.simps(2))
qed
end