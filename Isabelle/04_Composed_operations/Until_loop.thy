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

lemma until_def_lemma_3: "until_loop a C b n \<equiv>\<^sub>p a;(Skip (Pre (b\<sslash>\<^sub>p(-C))) \<union>\<^sub>p (loop (b\<sslash>\<^sub>p(-C)) 1 n)) \<setminus>\<^sub>p C"
  apply (simp add: until_loop_def)
proof -
  from loop_l6 have l1: "loop (b \<sslash>\<^sub>p (- C)) 0 n \<equiv>\<^sub>p (Skip (Pre (b\<sslash>\<^sub>p(-C))) \<union>\<^sub>p loop (b \<sslash>\<^sub>p (- C)) (Suc 0) n)"
    using le0 loop_l4 by fastforce
  from l1 until_loop_def show "a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; (Skip (Pre (b\<sslash>\<^sub>p(-C))) \<union>\<^sub>p loop (b \<sslash>\<^sub>p (- C)) (Suc 0) n) \<setminus>\<^sub>p C"
    by (metis equiv_is_reflexive equivalence_is_maintained_by_composition equivalence_is_maintained_by_corestriction)
qed

theorem loop_union1: "until_loop a C b n \<equiv>\<^sub>p \<Union>\<^sub>p [a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC. i \<leftarrow> [0..int n]]" \<comment> \<open>T77\<close>
proof (induction n)
  case 0
  then show ?case
    apply (simp add: until_loop_def)
    by (simp add: equiv_is_symetric fail_union_l)
next
  case (Suc n)
  assume IH: "until_loop a C b n \<equiv>\<^sub>p \<Union>\<^sub>p [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int n]]"
  have l1: "until_loop a C b (Suc n) \<equiv>\<^sub>p until_loop a C b n \<union>\<^sub>p until_support a C b (Suc n) (Suc n)"
    by (simp add: until_conncetion until_decomp_2)
  have l3: "[a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int (Suc n)]] = [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int n]] @ [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C]"
    by (metis list_comp_prop_1 nat_int)
  have l4: "\<Union>\<^sub>p [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int (Suc n)]] \<equiv>\<^sub>p \<Union>\<^sub>p [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int n]] \<union>\<^sub>p (a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C)"
    using Choice_prop_1 choice_commute l3 by auto
  have l5: "until_loop a C b (Suc n) \<equiv>\<^sub>p \<Union>\<^sub>p [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int n]] \<union>\<^sub>p until_support a C b (Suc n) (Suc n)"
    using Suc equiv_is_reflexive equiv_is_transitive equivalence_is_maintained_by_choice l1 by blast
  have l6: "until_support a C b (Suc n) (Suc n) \<equiv>\<^sub>p (a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C)"
    by (metis equiv_is_reflexive equivalence_is_maintained_by_composition equivalence_is_maintained_by_corestriction loop_l2_1 until_support_def)
  then show "until_loop a C b (Suc n) \<equiv>\<^sub>p \<Union>\<^sub>p [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int (Suc n)]]"
    by (smt (verit, ccfv_SIG) Suc equiv_is_symetric equiv_is_transitive equivalence_is_maintained_by_choice l4 l5)
qed

theorem loop_union2: "Range_p (until_loop a C b n) = \<Union>\<^sub>s [Range_p (a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC). i \<leftarrow> [0..int n]]"
proof (induction n)
  case 0
  then show ?case
    by (auto simp: Range_p_def until_loop_def) [1]
next
  case (Suc n)
  assume IH: "Range_p (until_loop a C b n) = \<Union>\<^sub>s [Range_p (a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC). i \<leftarrow> [0..int n]]"
  have l1: "until_loop a C b (Suc n) \<equiv>\<^sub>p (until_loop a C b n) \<union>\<^sub>p (a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C)"
    apply (simp add: until_loop_def)
    using compose_distrib1_3 corestrict_union equiv_is_reflexive equiv_is_transitive equivalence_is_maintained_by_composition by blast
  from l1 have l2: "Range_p (until_loop a C b (Suc n)) = Range_p (until_loop a C b n) \<union> Range_p (a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C)"
    by (metis same_range_p_3 range_p_prop_1)
  from l1 have l3: "Range_p (until_loop a C b (Suc n)) = \<Union>\<^sub>s [Range_p (a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC). i \<leftarrow> [0..int n]] \<union> Range_p (a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C)"
    by (simp add: Suc l2)
  have l4: "\<Union>\<^sub>s [Range_p (a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC). i \<leftarrow> [0..int (Suc n)]] = \<Union>\<^sub>s [Range_p (a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC). i \<leftarrow> [0..int n]] \<union> Range_p (a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C)"
    by (metis (no_types, lifting) inf_sup_aci(5) list_comp_prop_1 nat_int Union_prop_1)
  from IH show "Range_p (until_loop a C b (Suc n)) = \<Union>\<^sub>s [Range_p (a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC). i \<leftarrow> [0..int (Suc n)]]"
    using l3 l4 by blast
qed

theorem until_loop_feasible: "all_feasible [a, b] \<Longrightarrow> is_feasible (until_loop a C b n)" \<comment> \<open>Disproves a statement below T77\<close>
  by (simp add: until_conncetion until_support_feasible)

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
      by (smt (verit, ccfv_SIG) Definitions.equiv_def equivalence_is_maintained_by_choice)
    from IH True l1 have l3: "until_loop a C b (Suc n) \<equiv>\<^sub>p (until_loop a C b n \<union>\<^sub>p a;((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc n))\<setminus>\<^sub>pC) \<union>\<^sub>p until_loop a C b k"
      using l2 by auto
    then show ?thesis
      by (smt (verit, ccfv_SIG) Definitions.equiv_def equivalence_is_maintained_by_choice l1)
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

theorem range_until_loop_3: "Range_p (until_loop a C b n) \<subseteq> C"
  by (metis Corestriction.corestrict_prop_1 corestrict_compose same_range_p_3 until_conncetion until_support_def)

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


end