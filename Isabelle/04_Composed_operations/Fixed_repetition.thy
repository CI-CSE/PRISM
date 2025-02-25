theory Fixed_repetition
  imports 
"../T_03_Basic_programs" "Big_choice"
begin
section \<open>Fixed repetition for top\<close>


theorem state_space_is_same: "S p = S (p \<^bold>^ n)"
  apply (induction n) apply (auto simp: Skip_def S_def restrict_p_def Field_def restrict_r_def) [1]
  by simp

theorem state_space_is_same2: "State (p\<^bold>^n) = S p"
proof (induction n)
  case 0
  then show ?case by (auto simp: Skip_def restrict_p_def S_def Field_def)
next
  case (Suc n)
  have "p \<^bold>^ Suc n = p \<^bold>^ n ; p"
    by simp
  have "State (p \<^bold>^ n ; p) = S (p \<^bold>^ n) \<union> S p"
    by (simp add: composition_def)
  have "... = S p"
    using state_space_is_same by force
  then show ?case
    by (simp add: \<open>State (p \<^bold>^ n ; p) = S (p \<^bold>^ n) \<union> S p\<close>)
qed 

theorem fixed_pre_decreases: "Pre (p\<^bold>^(Suc n)) \<subseteq> Pre (p\<^bold>^n)"
  apply (induction n)
  apply (auto)
  by (metis compose_assoc composition_pre subsetD)

theorem fixed_rep_one_1: "p\<^bold>^1 \<equiv>\<^sub>p p \<sslash>\<^sub>p (Pre p)"
  by (auto simp: Skip_def composition_def corestrict_r_def restr_post_def restrict_r_def equiv_def restrict_p_def S_def)

theorem fixed_rep_one_2: "is_feasible p \<Longrightarrow> p\<^bold>^1 \<equiv>\<^sub>p p"
  by (auto simp: Skip_def composition_def corestrict_r_def restr_post_def restrict_r_def equiv_def S_def restrict_p_def)

theorem fixed_rep_one_3: "x;p\<^bold>^1 \<equiv>\<^sub>p x;p"
  by (auto simp: numeral_2_eq_2 composition_def Skip_def S_def equiv_def corestrict_r_def restr_post_def restrict_r_def relcomp_unfold Domain_iff restrict_p_def)

theorem fixed_rep_two_1: "p\<^bold>^2 \<equiv>\<^sub>p p ; p"
  by (auto simp: numeral_2_eq_2 composition_def Skip_def S_def equiv_def corestrict_r_def restr_post_def restrict_r_def relcomp_unfold restrict_p_def)

theorem fixed_rep_decomp_front: "0<i \<Longrightarrow> p\<^bold>^(Suc i) \<equiv>\<^sub>p p;p\<^bold>^i"
proof (induction i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  assume a1: "0 < Suc i"
  assume IH: "0 < i \<Longrightarrow> p \<^bold>^ Suc i \<equiv>\<^sub>p p ; p \<^bold>^ i"
  then show ?case
  proof (cases "i=0")
    case True
    assume a2: "i = 0"
    from a2 have l1: "p \<^bold>^ Suc (Suc i) = p \<^bold>^ 2" by (simp add: numeral_2_eq_2)
    have l3: "p ; p \<^bold>^ 1 \<equiv>\<^sub>p p ; p \<sslash>\<^sub>p (Pre p)"
      by (metis equals_equiv_relation_3 composition_equiv fixed_rep_one_1)
    have l6: "p \<^bold>^ 1 ; p \<equiv>\<^sub>p p \<sslash>\<^sub>p (Pre p) ; p"
      by (meson equals_equiv_relation_3 composition_equiv fixed_rep_one_1)
    have l8: "p \<sslash>\<^sub>p (Pre p) ; p \<equiv>\<^sub>p p ; p"
      by (auto simp: restrict_p_def equiv_def composition_def restr_post_def restrict_r_def corestrict_r_def)
    have l9: "p \<^bold>^ 2 \<equiv>\<^sub>p p ; p \<^bold>^ 1"
      by (metis One_nat_def a2 composition_simplification_2 equiv_is_symetric equiv_is_transitive fixed_repetition.simps(2) l1 l3 l6 l8)
    then show ?thesis
      using a2 l1 by fastforce
  next
    case False
    assume a2: "i \<noteq> 0"
    have IH2: "p \<^bold>^ Suc i \<equiv>\<^sub>p p ; p \<^bold>^ i"
      using IH a2 by auto
    have l1: "p ; p \<^bold>^ Suc i \<equiv>\<^sub>p p ; (p ; p \<^bold>^ i)"
      using IH2 equiv_is_reflexive composition_equiv by blast
    have l2: "p \<^bold>^ Suc (Suc i) \<equiv>\<^sub>p (p; p \<^bold>^ i) ;  p"
      by (metis IH2 equiv_is_reflexive composition_equiv fixed_repetition.simps(2))
    then show ?thesis
      by simp
  qed
qed

theorem fixed_rep_decomp_back: "is_feasible p \<Longrightarrow> p\<^bold>^(Suc i) \<equiv>\<^sub>p p\<^bold>^i;p"
  by (simp add: equiv_is_reflexive)

theorem fixed_rep_feasibility: "is_feasible p \<Longrightarrow> is_feasible (p\<^bold>^n)"
proof (induction n)
  case 0
  then show ?case by (auto simp: is_feasible_def Skip_def restrict_p_def restrict_r_def)
next
  case (Suc n)
  assume IH: "is_feasible p \<Longrightarrow> is_feasible (p \<^bold>^ n)"
  assume a1: "is_feasible p"
  from IH a1 have IH2: "is_feasible (p \<^bold>^ n)" by simp
  have l1: "p \<^bold>^ Suc n \<equiv>\<^sub>p p \<^bold>^ n ; p"
    by (simp add: equiv_is_reflexive)
  then show ?case
    by (simp add: a1 compose_feasible)
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

theorem range_decreases_fixed_repetition_2: "0 < n \<Longrightarrow> Range_p (x \<^bold>^ Suc n) \<subseteq> Range_p (x \<^bold>^ n)"
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  assume IH: "0 < n \<Longrightarrow> Range_p (x \<^bold>^ Suc n) \<subseteq> Range_p (x \<^bold>^ n)"
  then show ?case
  proof (cases "n=0")
    case True
    have l1: "x \<^bold>^ 2 \<equiv>\<^sub>p x;x \<^bold>^ 1"
      by (metis One_nat_def Suc.prems True fixed_rep_decomp_front numeral_2_eq_2)
    have l2: "x \<^bold>^ 1;x \<equiv>\<^sub>p x;x" by (auto simp: Skip_def composition_def equiv_def corestrict_r_def restr_post_def restrict_r_def relcomp_unfold restrict_p_def S_def)
    have "Range_p (x;x) \<subseteq> Range_p (x)"
      by (simp add: range_decreases_composition)
    then have "Range_p (x \<^bold>^ 2) \<subseteq> Range_p (x \<^bold>^ 1)"
      using l1 range_decreases_composition same_range_p_3 by fastforce
    then show ?thesis
      using One_nat_def Suc_1 True by presburger
  next
    case False
    then have IH2: "Range_p (x \<^bold>^ Suc n) \<subseteq> Range_p (x \<^bold>^ n)"
      using IH by auto
    have l1: "x \<^bold>^ Suc (Suc n) \<equiv>\<^sub>p x \<^bold>^ Suc n ; x"
      by (simp add: equals_equiv_relation_3)
    then show ?thesis
      by (metis Suc.prems fixed_rep_decomp_front range_decreases_composition same_range_p_3)
  qed
qed

theorem fixed_prop: "x\<^bold>^1 = Skip (Pre x) ; x"
  by (auto simp: is_valid_def composition_def Skip_def is_feasible_def restr_post_def restrict_p_def corestrict_r_def restrict_r_def S_def Field_def relcomp_unfold Un_def Domain_iff Range_iff subset_iff)

theorem skip_choice: "Skip (Pre x) ; x \<union>\<^sub>p Skip (Pre y) ; y = Skip (Pre x \<union> Pre y) ; (x \<union>\<^sub>p y)"
  apply (auto simp: Skip_def composition_def choice_def restr_post_def restrict_r_def corestrict_r_def)
  by (auto simp: S_def Field_def) 

(*
theorem "Range_p x \<inter> Pre y = {} \<Longrightarrow> Range_p y \<inter> Pre x = {} \<Longrightarrow> x \<^bold>^ n ; x \<union>\<^sub>p y \<^bold>^ n ; y = (x \<^bold>^ n \<union>\<^sub>p y \<^bold>^ n) ; (x \<union>\<^sub>p y)"
proof (induction n)
  case 0
  then show ?case sorry
next
  case (Suc n)
  then show ?case sorry
qed*)

theorem comp_prop: "Range_p a \<inter> Pre d = {} \<Longrightarrow> Range_p c \<inter> Pre b = {} \<Longrightarrow> a;b \<union>\<^sub>p c;d = (a \<union>\<^sub>p c);(b \<union>\<^sub>p d)"
  apply (auto simp: Range_p_def restrict_r_def choice_def composition_def S_def relcomp_unfold)
                      apply (auto simp: restr_post_def restrict_r_def Field_def corestrict_r_def)
  by (auto simp: corestrict_r_def Range_iff Int_def Domain_iff)

lemma arbitrary_repetition_simplification: "0<n \<Longrightarrow> all_feasible [x,y] \<Longrightarrow> Range_p x \<inter> Pre y = {} \<Longrightarrow> Range_p y \<inter> Pre x = {} \<Longrightarrow> x\<^bold>^n \<union>\<^sub>p y\<^bold>^n = (x \<union>\<^sub>p y)\<^bold>^n" \<comment> \<open>NEW\<close>
proof (induction n)
  case 0
  then show ?case by (auto) 
  next
  case (Suc n)
  show ?case
  proof (cases "n=0")
    case True
    have "x \<^bold>^ Suc n \<union>\<^sub>p y \<^bold>^ Suc n = Skip (Pre x) ; x \<union>\<^sub>p Skip (Pre y) ; y"
      by (metis One_nat_def True fixed_prop)
    have "(x \<union>\<^sub>p y) \<^bold>^ Suc n = Skip (Pre (x \<union>\<^sub>p y)) ; (x \<union>\<^sub>p y)"
      by (metis One_nat_def True fixed_prop)
    have "... = Skip (Pre x \<union> Pre y) ; (x \<union>\<^sub>p y)"
      by simp
    have "Skip (Pre x) ; x \<union>\<^sub>p Skip (Pre y) ; y = Skip (Pre x \<union> Pre y) ; (x \<union>\<^sub>p y)"
      by (simp add: skip_choice)
    show ?thesis
      using \<open>(x \<union>\<^sub>p y) \<^bold>^ Suc n = Skip (Pre (x \<union>\<^sub>p y)) ; (x \<union>\<^sub>p y)\<close> \<open>Skip (Pre x) ; x \<union>\<^sub>p Skip (Pre y) ; y = Skip (Pre x \<union> Pre y) ; (x \<union>\<^sub>p y)\<close> \<open>x \<^bold>^ Suc n \<union>\<^sub>p y \<^bold>^ Suc n = Skip (Pre x) ; x \<union>\<^sub>p Skip (Pre y) ; y\<close> by fastforce
  next
    case False
    have l1: "Range_p (x\<^bold>^n) \<inter> Pre y = {}"
      by (metis False Suc.prems(3) inf.orderE inf_bot_right inf_commute inf_left_commute not_gr_zero range_decreases_fixed_repetition)
    have l2: "Range_p (y\<^bold>^n) \<inter> Pre x = {}"
      by (metis (no_types, lifting) False Int_assoc Int_commute Int_empty_right Suc.prems(4) gr0I inf.absorb_iff2 range_decreases_fixed_repetition)
    have "x \<^bold>^ Suc n \<union>\<^sub>p y \<^bold>^ Suc n = x \<^bold>^ n ; x \<union>\<^sub>p y \<^bold>^ n ; y"
      by simp
    moreover have "... = (x \<^bold>^ n  \<union>\<^sub>p y \<^bold>^ n) ; (x \<union>\<^sub>p y)" using Suc comp_prop l1 l2
      by blast
    moreover have "... = (x \<union>\<^sub>p y) \<^bold>^ Suc n" using Suc comp_prop l1 l2
      using False by auto
    ultimately show ?thesis by argo
  qed
qed

lemma arbitrary_repetition_simplification2: "0<n \<Longrightarrow> all_feasible [x,y] \<Longrightarrow> Range_p x \<inter> Pre y = {} \<Longrightarrow> Range_p y \<inter> Pre x = {} \<Longrightarrow> x\<^bold>^n \<union>\<^sub>p y\<^bold>^n \<equiv>\<^sub>p (x \<union>\<^sub>p y)\<^bold>^n"
  by (metis arbitrary_repetition_simplification choice_commute choice_commute_3)
theorem equality_is_maintained_by_fixed_repetition: "p\<^sub>1 \<triangleq> p\<^sub>2 \<Longrightarrow> p\<^sub>1\<^bold>^n \<triangleq> p\<^sub>2\<^bold>^n"
  apply (induction n)
  apply (auto simp: equal_def) [1]
  apply (simp add: Definitions.equal_def)
  by (simp add: composition_def restr_post_def)

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
      by (simp add: IH2 a2 composition_equiv)
  qed
qed

theorem skip_compose_r_of_fixed_rep_1: "is_feasible p \<Longrightarrow> p\<^bold>^n \<equiv>\<^sub>p p\<^bold>^n ; Skip (S p)"
  apply (cases "n=0")
  apply (auto simp: restrict_p_def composition_def equiv_def restr_post_def restrict_r_def corestrict_r_def relcomp_unfold Skip_def) [1]
  by (metis equiv_is_symetric fixed_rep_feasibility skip_compose2 state_space_is_same)

theorem skip_compose_l_of_fixed_rep_1: "p\<^bold>^n \<equiv>\<^sub>p Skip (S p) ; p\<^bold>^n"
  apply (cases "n=0")
  apply (auto) [1]
  apply (metis composition_state equiv_is_symetric fixed_repetition.simps(1) fixed_repetition.simps(2) skip_prop_6 state_space_is_same subset_Un_eq)
  using skip_compose3 apply (auto)
  by (smt (verit) equiv_is_symetric skip_compose3 state_space_is_same)

theorem fail_stays_fail_fixed: "p\<^bold>^n \<equiv>\<^sub>p Fail {} \<Longrightarrow> p\<^bold>^Suc n \<equiv>\<^sub>p Fail {}"
  apply (induction n)
   apply (auto simp: Skip_def equiv_def Fail_def composition_def restr_post_def restrict_r_def) [1]
proof -
  fix n assume IH: "p \<^bold>^ n \<equiv>\<^sub>p Fail {} \<Longrightarrow> p \<^bold>^ Suc n \<equiv>\<^sub>p Fail {}"
  assume a1: "p \<^bold>^ Suc n \<equiv>\<^sub>p Fail {}"
  have l1: "p \<^bold>^ Suc (Suc n) \<equiv>\<^sub>p p \<^bold>^ Suc n ; p"
    by (simp add: equiv_is_reflexive)
  have l2: "p \<^bold>^ Suc n \<equiv>\<^sub>p Fail {}"
    using a1 by auto
  show "p \<^bold>^ Suc (Suc n) \<equiv>\<^sub>p Fail {}"
    by (metis Definitions.equiv_def Program.select_convs(2) bot.extremum_uniqueI fixed_pre_decreases local.l2 no_pre_is_fail)
qed

theorem repetition_fail: "i<j \<Longrightarrow> p\<^bold>^i \<equiv>\<^sub>p Fail {} \<Longrightarrow> p\<^bold>^j \<equiv>\<^sub>p Fail {}"
  apply (induction j) apply auto
  by (metis fail_stays_fail_fixed fixed_repetition.simps(2) less_antisym)

theorem fix_rep_prop1: "0<i \<Longrightarrow> p\<^bold>^i = Skip (S p) \<sslash>\<^sub>p (Pre p) ; Concat [p . t \<leftarrow> [1 .. int i]] (S p)"
proof (induction i arbitrary: p)
  case 0
  then show ?case by simp
next
  case (Suc i)
  then show "p \<^bold>^ Suc i = Skip (S p) \<sslash>\<^sub>p (Pre p) ; Concat (map (\<lambda>t. p) [1..int (Suc i)])  (S p)"
  proof (cases "i=0")
    case True
    then show ?thesis by auto
  next
    case False
    have "p \<^bold>^ Suc i = p \<^bold>^ i ; p" by simp
    have "... = (Skip (S p) \<sslash>\<^sub>p (Pre p) ; (Concat [p . t \<leftarrow> [1 .. int i]]) (S p)) ; p"
      by (metis False Suc.IH not_gr_zero)
    have "... = Skip (S p) \<sslash>\<^sub>p (Pre p) ; (Concat [p . t \<leftarrow> [1 .. int i]] (S p) ; p)"
      by simp
    have "... = Skip (S p) \<sslash>\<^sub>p (Pre p) ; Concat [p . t \<leftarrow> [1 .. int (Suc i)]] (S p)"
      by (metis Concat_prop_9 False not_gr_zero)
    then show ?thesis
      by (simp add: \<open>p \<^bold>^ i ; p = (Skip (S p) \<sslash>\<^sub>p Pre p ; Concat (map (\<lambda>t. p) [1..int i]) (S p)) ; p\<close>)
  qed
qed

theorem fix_rep_prop2: "p\<^bold>^i = Concat ((Skip (S p) \<sslash>\<^sub>p (Pre p))#[p . t \<leftarrow> [1 .. int i]]) (S p)"
  apply (cases "i=0") apply (auto simp: restrict_p_def Skip_def S_def) [1] apply auto
proof -
  assume a1: "0<i"
  have l1: "Concat (Skip (S p) \<sslash>\<^sub>p (Pre p) # map (\<lambda>t. p) [1..int i]) (S p) = Skip (S p) \<sslash>\<^sub>p (Pre p) ; Concat (map (\<lambda>t. p) [1..int i]) (S p)"
    by (smt (verit) Concat_prop_10 \<open>0 < i\<close> list.map_disc_iff of_nat_0_less_iff upto_Nil2)
  show "p \<^bold>^ i = Concat (Skip (S p) \<sslash>\<^sub>p (Pre p) # map (\<lambda>t. p) [1..int i]) (S p)" using a1 l1 fix_rep_prop1
    using map_eq_map_tailrec by auto
qed

end