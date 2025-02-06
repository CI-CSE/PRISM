theory Until_loop
  imports 
"../T_03_Basic_programs" 
"Arbitrary_repetition" 
"Atomic_concurrency"
"Big_choice"
"Until_support"
begin
section \<open>Until loop for top\<close>


lemma until_conncetion: "until_loop a C b n = until_support a C b 0 n"
  by (simp add: until_loop_def until_support_def)

lemma until_decomposition: "until_loop a C b (Suc n) \<equiv>\<^sub>p a;((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc n) \<union>\<^sub>p (loop (b\<sslash>\<^sub>p(-C)) 0 n)) \<setminus>\<^sub>p C"
proof -
  have l1: "until_loop a C b (Suc n) = until_support a C b 0 (Suc n)"
    by (simp add: until_conncetion)
  have l2: "until_support a C b 0 (Suc n) \<equiv>\<^sub>p a;((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc n) \<union>\<^sub>p (loop (b\<sslash>\<^sub>p(-C)) 0 n)) \<setminus>\<^sub>p C"
    by (simp add: equiv_is_reflexive until_support_def)
  show ?thesis
    using l1 l2 by auto
qed

lemma until_decomposition_2: "until_loop a C b (Suc n) \<equiv>\<^sub>p a;((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc n)) \<setminus>\<^sub>p C \<union>\<^sub>p until_loop a C b n"
  by (simp add: equiv_is_symetric until_loop_def until_simplification_1)

lemma until_def_lemma_3: "until_loop a C b n \<equiv>\<^sub>p a;((Skip (S (b\<sslash>\<^sub>p(-C))) \<sslash>\<^sub>p (Pre (b\<sslash>\<^sub>p(-C)))) \<union>\<^sub>p (loop (b\<sslash>\<^sub>p(-C)) 1 n)) \<setminus>\<^sub>p C"
  apply (simp add: until_loop_def)
proof -
  have l1: "loop (b \<sslash>\<^sub>p (- C)) 0 n \<equiv>\<^sub>p (Skip (S (b\<sslash>\<^sub>p(-C))) \<sslash>\<^sub>p (Pre (b\<sslash>\<^sub>p(-C))) \<union>\<^sub>p loop (b \<sslash>\<^sub>p (- C)) (Suc 0) n)"
    using le0 loop_l4
    by (metis fixed_repetition.simps(1))
  from l1 until_loop_def show "a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; (loop (b \<sslash>\<^sub>p (- C)) (Suc 0) n \<union>\<^sub>p Skip (S b) \<sslash>\<^sub>p Pre (b \<sslash>\<^sub>p (- C))) \<setminus>\<^sub>p C"
    by (simp add: equals_equiv_relation_3 composition_equiv equivalence_is_maintained_by_corestriction)
qed

theorem loop_choice1: "until_loop a C b n \<equiv>\<^sub>p \<Union>\<^sub>p [a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC. i \<leftarrow> [0..int n]]" \<comment> \<open>/Loop_choice1/\<close>
proof (induction n)
  case 0
  then show ?case
    apply (simp add: until_loop_def)
    by (simp add: equiv_is_reflexive)
next
  case (Suc n)
  assume IH: "until_loop a C b n \<equiv>\<^sub>p \<Union>\<^sub>p [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int n]]"
  have l1: "until_loop a C b (Suc n) \<equiv>\<^sub>p until_loop a C b n \<union>\<^sub>p until_support a C b (Suc n) (Suc n)"
    by (simp add: until_conncetion until_decomp_2)
  have l3: "[a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int (Suc n)]] = [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int n]] @ [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C]"
    by (metis list_comp_prop_1 nat_int)
  have l4: "\<Union>\<^sub>p [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int (Suc n)]] \<equiv>\<^sub>p \<Union>\<^sub>p [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int n]] \<union>\<^sub>p (a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C)"
    using Choice_prop_1 choice_commute l3
    by (smt (verit) choice_assoc_3 choice_idem_2 map_is_Nil_conv of_nat_less_0_iff upto_Nil)
  have l5: "until_loop a C b (Suc n) \<equiv>\<^sub>p \<Union>\<^sub>p [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int n]] \<union>\<^sub>p until_support a C b (Suc n) (Suc n)"
    using Suc equiv_is_reflexive equiv_is_transitive choice_equiv l1 by blast
  have l6: "until_support a C b (Suc n) (Suc n) \<equiv>\<^sub>p (a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C)"
    by (metis equiv_is_reflexive composition_equiv equivalence_is_maintained_by_corestriction loop_l2_1 until_support_def)
  then show "until_loop a C b (Suc n) \<equiv>\<^sub>p \<Union>\<^sub>p [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int (Suc n)]]"
    by (smt (verit, ccfv_SIG) Suc equiv_is_symetric equiv_is_transitive choice_equiv l4 l5)
qed

theorem loop_choice2: "Range_p (until_loop a C b n) = \<Union> (set [Range_p (a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC). i \<leftarrow> [0..int n]])" \<comment> \<open>/Loop_choice2/\<close>
proof (induction n)
  case 0
  then show ?case
    by (auto simp: Range_p_def until_loop_def) [1]
next
  case (Suc n)
  assume IH: "Range_p (until_loop a C b n) = \<Union> (set [Range_p (a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC). i \<leftarrow> [0..int n]])"
  have l1: "until_loop a C b (Suc n) \<equiv>\<^sub>p (until_loop a C b n) \<union>\<^sub>p (a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C)"
    apply (simp add: until_loop_def)
    by (simp add: compose_distrib1_3 corestrict_choice_1)
  from l1 have l2: "Range_p (until_loop a C b (Suc n)) = Range_p (until_loop a C b n) \<union> Range_p (a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C)"
    by (metis same_range_p_3 choice_range)
  from l1 have l3: "Range_p (until_loop a C b (Suc n)) = \<Union> (set [Range_p (a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC). i \<leftarrow> [0..int n]]) \<union> Range_p (a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C)"
    by (simp add: Suc l2)
  have l4: "\<Union> (set [Range_p (a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC). i \<leftarrow> [0..int (Suc n)]]) = \<Union> (set [Range_p (a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC). i \<leftarrow> [0..int n]]) \<union> Range_p (a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C)"
    using list_comp_prop_1 nat_int by (metis (no_types, lifting) Permutations.Union_prop_1 inf_sup_aci(5))
  from IH show "Range_p (until_loop a C b (Suc n)) = \<Union> (set [Range_p (a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC). i \<leftarrow> [0..int (Suc n)]])"
    using l3 l4 by blast
qed

theorem until_loop_feasible: "all_feasible [a, b] \<Longrightarrow> is_feasible (until_loop a C b n)" \<comment> \<open>Disproves a statement below T77\<close>
  oops

theorem equiv_is_maintained_by_until_loop_2: 
  assumes "a\<^sub>1 \<equiv>\<^sub>p a\<^sub>2"
      and "b\<^sub>1 \<equiv>\<^sub>p b\<^sub>2"
      and "S b\<^sub>1 = S b\<^sub>2"
      and "all_feasible [b\<^sub>1, b\<^sub>2]"
    shows "until_loop a\<^sub>1 C b\<^sub>1 n \<equiv>\<^sub>p until_loop a\<^sub>2 C b\<^sub>2 n"
  by (metis assms(1) assms(2) assms(3) assms(4) equiv_is_maintained_by_until_support_1 until_conncetion)

theorem until_decom: "k\<le>n \<Longrightarrow> until_loop a C b n \<equiv>\<^sub>p until_loop a C b n \<union>\<^sub>p until_loop a C b k"
proof (induction n)
  case 0
  then show ?case by (auto simp: until_loop_def Skip_def composition_def equiv_def restr_post_def restrict_p_def restrict_r_def)
next
  case (Suc n)
  assume IH: "k \<le> n \<Longrightarrow> until_loop a C b n \<equiv>\<^sub>p until_loop a C b n \<union>\<^sub>p until_loop a C b k"
  assume a1: "k \<le> Suc n"
  have l1: "until_loop a C b (Suc n) \<equiv>\<^sub>p until_loop a C b n \<union>\<^sub>p a;((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc n))\<setminus>\<^sub>pC"
    using until_decomposition_2 by auto
  then show "until_loop a C b (Suc n) \<equiv>\<^sub>p until_loop a C b (Suc n) \<union>\<^sub>p until_loop a C b k"
  proof (cases "k\<le>n")
    case True
    from IH True l1 have l2: "until_loop a C b (Suc n) \<equiv>\<^sub>p (until_loop a C b n \<union>\<^sub>p until_loop a C b k) \<union>\<^sub>p a;((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc n))\<setminus>\<^sub>pC"
      by (smt (verit, ccfv_SIG) Definitions.equiv_def choice_equiv)
    from IH True l1 have l3: "until_loop a C b (Suc n) \<equiv>\<^sub>p (until_loop a C b n \<union>\<^sub>p a;((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc n))\<setminus>\<^sub>pC) \<union>\<^sub>p until_loop a C b k"
      using l2 by auto
    then show ?thesis
      by (smt (verit, ccfv_SIG) Definitions.equiv_def choice_equiv l1)
  next
    case False
    from a1 False have "k=Suc n" by auto
    then show ?thesis
      by (simp add: equiv_is_symetric)
  qed
qed

theorem range_until_loop_1: "m\<le>n \<Longrightarrow> x \<notin> Range_p (until_loop a C b n) \<Longrightarrow> x \<notin> Range_p (until_loop a C b m)"
proof -
  assume a1: "m\<le>n"
  assume a2: "x \<notin> Range_p (until_loop a C b n)"
  obtain pr\<^sub>1 where o1: "pr\<^sub>1 = until_loop a C b n" by simp
  obtain pr\<^sub>2 where o2: "pr\<^sub>2 = until_loop a C b m" by simp
  from a1 o1 o2 have l1: "pr\<^sub>1 \<equiv>\<^sub>p pr\<^sub>1 \<union>\<^sub>p pr\<^sub>2"
    using until_decom by blast
  from a1 a2 l1 have l2: "x \<notin> Range_p pr\<^sub>2"
    using choice_range_p_prop_3 o1 same_range_p_3 by fastforce
  show "x \<notin> Range_p (until_loop a C b m)"
    using l2 o2 by auto
qed

theorem range_until_loop_2: "m\<le>n \<Longrightarrow> x \<notin> Range_p (until_loop a C b n) \<Longrightarrow> x \<notin> Range_p (until_support a C b s m)"
proof -
  assume a1: "m\<le>n"
  assume a2: "x \<notin> Range_p (until_loop a C b n)"
  obtain loop where o1: "loop = until_loop a C b n" by simp
  obtain support where o2: "support = until_support a C b s m" by simp
  obtain pref where o3: "pref = until_support a C b" by simp
  have l1: "loop = pref 0 n" using until_conncetion o1 o3 by auto
  have l2: "pref 0 n \<equiv>\<^sub>p pref 0 n \<union>\<^sub>p support" using until_support_decomp
    using a1 o2 o3 by blast
  have l3: "x \<notin> Range_p (loop)" using o1 a2 by simp
  have l4: "x \<notin> Range_p (support)" using o2
    by (metis a2 choice_commute choice_range_p_prop_3 l1 l2 o1 same_range_p_3)
  show " x \<notin> Range_p (until_support a C b s m)"
    using l4 o2 by auto
qed

theorem loop_range: "Range_p (until_loop a C b n) \<subseteq> C" \<comment> \<open>Loop_range\<close>
  by (metis Corestriction.corestrict_prop_1 corestrict_compose until_conncetion until_support_def)

theorem split_front: "until_loop (x;a) C b n \<equiv>\<^sub>p x ; until_loop a C b n"
  by (metis compose_assoc_3 until_loop_def)

theorem fail_until: "until_loop a C b (Suc n) \<equiv>\<^sub>p Fail {} \<Longrightarrow> until_loop a C b n \<equiv>\<^sub>p Fail {}"
  apply (auto simp: until_loop_def)
  by (metis (no_types, lifting) Definitions.equiv_def choice_fail_implication until_simplification_1)

theorem fail_until_2: "k\<le>n \<Longrightarrow> until_loop a C b n \<equiv>\<^sub>p Fail {} \<Longrightarrow> until_loop a C b k \<equiv>\<^sub>p Fail {}"
proof -
  assume a1: "k\<le>n"
  assume a2: "until_loop a C b n \<equiv>\<^sub>p Fail {}"
  have l1: "until_loop a C b n \<equiv>\<^sub>p until_loop a C b n \<union>\<^sub>p until_loop a C b k"
    using a1 until_decom by blast
  show "until_loop a C b k \<equiv>\<^sub>p Fail {}"
    using a2 choice_fail_implication equiv_is_symetric equiv_is_transitive l1 by blast
qed

theorem loop_prop1: "S (loop (b\<sslash>\<^sub>p(-C)) 0 n) = S b"
proof (induction n)
  case 0
  then show ?case by (auto simp: S_def restrict_p_def Skip_def Field_def restrict_r_def)
next
  case (Suc n)
  have l1: "loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n) = (if 0>(Suc n) then Fail (S b) else (b \<sslash>\<^sub>p (- C))\<^bold>^(Suc n) \<union>\<^sub>p loop ((b \<sslash>\<^sub>p (- C))) 0 n)"
    by simp
  obtain p1 where o1: "p1 = (if 0>(Suc n) then Fail (S b) else (b \<sslash>\<^sub>p (- C))\<^bold>^(Suc n))" by simp
  obtain p2 where o2: "p2 = loop ((b \<sslash>\<^sub>p (- C))) 0 n" by simp
  have "S (p1) = S b" apply (auto simp: o1)
    by (metis restriction_state state_space_is_same)
  moreover have "S (p2) = S b"
    by (simp add: Suc o2)
  ultimately have "State (p1 \<union>\<^sub>p p2) = S b"
    by (simp add: choice_def)
  then show ?case apply (simp add: o1 o2)
    by (metis Suc Un_absorb restriction_state state_space_is_same)
qed

theorem loop_prop2: "State (loop (b\<sslash>\<^sub>p(-C)) 0 n) = S b"
proof (induction n)
  case 0
  then show ?case by (auto simp: restrict_p_def S_def Field_def Skip_def restrict_r_def)
next
  case (Suc n)
  have "loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n) = (if 0>(Suc n) then Fail (S b) else (b \<sslash>\<^sub>p (- C))\<^bold>^(Suc n) \<union>\<^sub>p loop ((b \<sslash>\<^sub>p (- C))) 0 n)"
    by simp
  obtain p1 where o1: "p1 = (if 0>(Suc n) then Fail (S b) else (b \<sslash>\<^sub>p (- C))\<^bold>^(Suc n))" by simp
  obtain p2 where o2: "p2 = loop ((b \<sslash>\<^sub>p (- C))) 0 n" by simp
  have "State (p1) = S b" apply (auto simp: o1)
    apply (metis fixed_repetition.simps(2) restriction_state state_space_is_same2)
    by (metis fixed_repetition.simps(2) restriction_state state_space_is_same2)
  moreover have "State (p2) = S b"
    by (simp add: Suc o2)
  ultimately have "State (p1 \<union>\<^sub>p p2) = S b"
    by (metis Program.select_convs(1) \<open>loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n) = (if Suc n < 0 then Fail (S b) else (b \<sslash>\<^sub>p (- C)) \<^bold>^ Suc n \<union>\<^sub>p loop (b \<sslash>\<^sub>p (- C)) 0 n)\<close> choice_def choice_state le_zero_eq loop_prop1 nat_less_le o1 o2)
  then show "State (loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n)) = S b"
    by (simp add: o1 o2)
qed

theorem loop_prop3: "S (until_loop a C b n) = S a \<union> S b"
proof -
  have "until_loop a C b n = a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C" by (auto simp: until_loop_def)
  have "S (a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C) = S a \<union> S b"
    by (simp add: loop_prop1)
  show ?thesis
    using \<open>S (a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C) = S a \<union> S b\<close> \<open>until_loop a C b n = a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C\<close> by auto
qed

theorem loop_prop4: "State (until_loop a C b n) = S (until_loop a C b n)"
proof (cases "n=0")
  case True
  then show ?thesis apply (auto simp: until_loop_def)
    apply (simp add: composition_def)
    apply (simp add: composition_def)
    by (simp add: composition_def)
next
  case False
  obtain n' where "Suc n' = n"
    using False not0_implies_Suc by auto
  obtain p1 where o1: "p1 = (if 0>(Suc n') then Fail (S b) else (b \<sslash>\<^sub>p (- C))\<^bold>^(Suc n'))" by simp
  obtain p2 where o2: "p2 = loop ((b \<sslash>\<^sub>p (- C))) 0 n'" by simp
  have "until_loop a C b (Suc n') = a ; loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n') \<setminus>\<^sub>p C" by (auto simp: until_loop_def)
  have "... =  a; (if 0>(Suc n') then Fail (S b) else (b \<sslash>\<^sub>p (- C))\<^bold>^(Suc n') \<union>\<^sub>p loop ((b \<sslash>\<^sub>p (- C))) 0 n') \<setminus>\<^sub>p C"
    by simp
  have "... = a ; (p1 \<union>\<^sub>p p2) \<setminus>\<^sub>p C" by (auto simp: o1 o2)
  have "State p1 = S b" apply (auto simp: o1)
    apply (metis fixed_repetition.simps(2) restriction_state state_space_is_same2)
    by (metis fixed_repetition.simps(2) restriction_state state_space_is_same2)
  have "S p1 = S b" apply (auto simp: o1)
    by (metis restriction_state state_space_is_same)
  have "S p2 = S b" apply (auto simp: o2)
    apply (simp add: loop_prop1)
    by (simp add: loop_prop1)
  have "State p2 = S b" apply (auto simp: o2)
    apply (simp add: loop_prop2)
    by (simp add: loop_prop2)
  have "State ( a ; (p1 \<union>\<^sub>p p2) \<setminus>\<^sub>p C) = S a \<union> S b"
    by (metis Program.select_convs(1) \<open>a ; (if Suc n' < 0 then Fail (S b) else (b \<sslash>\<^sub>p (- C)) \<^bold>^ Suc n' \<union>\<^sub>p loop (b \<sslash>\<^sub>p (- C)) 0 n') \<setminus>\<^sub>p C = a ; (p1 \<union>\<^sub>p p2) \<setminus>\<^sub>p C\<close> \<open>a ; loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n') \<setminus>\<^sub>p C = a ; (if Suc n' < 0 then Fail (S b) else (b \<sslash>\<^sub>p (- C)) \<^bold>^ Suc n' \<union>\<^sub>p loop (b \<sslash>\<^sub>p (- C)) 0 n') \<setminus>\<^sub>p C\<close> composition_def corestriction_state loop_prop1)
  have "S ( a ; (p1 \<union>\<^sub>p p2) \<setminus>\<^sub>p C) = S a \<union> S b"
    using \<open>S p1 = S b\<close> \<open>S p2 = S b\<close> by force
  show "State (until_loop a C b n) = S (until_loop a C b n)"
    using \<open>S (a ; (p1 \<union>\<^sub>p p2) \<setminus>\<^sub>p C) = S a \<union> S b\<close> \<open>State (a ; (p1 \<union>\<^sub>p p2) \<setminus>\<^sub>p C) = S a \<union> S b\<close> \<open>Suc n' = n\<close> \<open>a ; (if Suc n' < 0 then Fail (S b) else (b \<sslash>\<^sub>p (- C)) \<^bold>^ Suc n' \<union>\<^sub>p loop (b \<sslash>\<^sub>p (- C)) 0 n') \<setminus>\<^sub>p C = a ; (p1 \<union>\<^sub>p p2) \<setminus>\<^sub>p C\<close> \<open>a ; loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n') \<setminus>\<^sub>p C = a ; (if Suc n' < 0 then Fail (S b) else (b \<sslash>\<^sub>p (- C)) \<^bold>^ Suc n' \<union>\<^sub>p loop (b \<sslash>\<^sub>p (- C)) 0 n') \<setminus>\<^sub>p C\<close> \<open>until_loop a C b (Suc n') = a ; loop (b \<sslash>\<^sub>p (- C)) 0 (Suc n') \<setminus>\<^sub>p C\<close> by presburger
qed

theorem loop_prop5: "State (until_loop a C b n) = S a \<union> S b"
  by (simp add: composition_def loop_prop1 until_loop_def)

theorem loop_prop6: "until_loop (Skip D) FALSE (Skip D) n = Fail D"
  oops


end