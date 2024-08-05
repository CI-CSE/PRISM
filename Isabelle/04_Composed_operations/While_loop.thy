theory While_loop
  imports 
"../T_03_Basic_programs" 
"Arbitrary_repetition" 
"Atomic_concurrency"
"Big_choice"
"While_support"
begin
section \<open>While loop for top\<close>


lemma while_conncetion: "while_loop a C b n = while_support a C b 0 n"
  by (simp add: while_loop_def while_support_def)

lemma while_decomposition: "while_loop a C b (Suc n) \<equiv>\<^sub>p a;((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc n) \<union>\<^sub>p (loop (b\<sslash>\<^sub>p(-C)) 0 n)) \<setminus>\<^sub>p C"
proof -
  have l1: "while_loop a C b (Suc n) = while_support a C b 0 (Suc n)"
    by (simp add: while_conncetion)
  have l2: "while_support a C b 0 (Suc n) \<equiv>\<^sub>p a;((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc n) \<union>\<^sub>p (loop (b\<sslash>\<^sub>p(-C)) 0 n)) \<setminus>\<^sub>p C"
    by (simp add: equiv_is_reflexive while_support_def)
  show ?thesis
    using l1 l2 by auto
qed

lemma while_decomposition_2: "while_loop a C b (Suc n) \<equiv>\<^sub>p a;((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc n)) \<setminus>\<^sub>p C \<union>\<^sub>p while_loop a C b n"
  by (simp add: equiv_is_symetric while_loop_def while_simplification_1)

lemma while_def_lemma_3: "while_loop a C b n \<equiv>\<^sub>p a;(Skip (Pre (b\<sslash>\<^sub>p(-C))) \<union>\<^sub>p (loop (b\<sslash>\<^sub>p(-C)) 1 n)) \<setminus>\<^sub>p C"
  apply (simp add: while_loop_def)
proof -
  from loop_l6 have l1: "loop (b \<sslash>\<^sub>p (- C)) 0 n \<equiv>\<^sub>p (Skip (Pre (b\<sslash>\<^sub>p(-C))) \<union>\<^sub>p loop (b \<sslash>\<^sub>p (- C)) (Suc 0) n)"
    using le0 loop_l4 by fastforce
  from l1 while_loop_def show "a ; loop (b \<sslash>\<^sub>p (- C)) 0 n \<setminus>\<^sub>p C \<equiv>\<^sub>p a ; (Skip (Pre (b\<sslash>\<^sub>p(-C))) \<union>\<^sub>p loop (b \<sslash>\<^sub>p (- C)) (Suc 0) n) \<setminus>\<^sub>p C"
    by (metis equiv_is_reflexive equivalence_is_maintained_by_composition equivalence_is_maintained_by_corestriction)
qed

theorem loop_union1: "while_loop a C b n \<equiv>\<^sub>p \<Union>\<^sub>p [a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC. i \<leftarrow> [0..int n]]" \<comment> \<open>T77\<close>
proof (induction n)
  case 0
  then show ?case
    apply (simp add: while_loop_def)
    by (simp add: equiv_is_symetric fail_union_l)
next
  case (Suc n)
  assume IH: "while_loop a C b n \<equiv>\<^sub>p \<Union>\<^sub>p [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int n]]"
  have l1: "while_loop a C b (Suc n) \<equiv>\<^sub>p while_loop a C b n \<union>\<^sub>p while_support a C b (Suc n) (Suc n)"
    by (simp add: while_conncetion while_decomp_2)
  have l3: "[a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int (Suc n)]] = [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int n]] @ [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C]"
    by (metis list_comp_prop_1 nat_int)
  have l4: "\<Union>\<^sub>p [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int (Suc n)]] \<equiv>\<^sub>p \<Union>\<^sub>p [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int n]] \<union>\<^sub>p (a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C)"
    using Choice_prop_1 choice_commute l3 by auto
  have l5: "while_loop a C b (Suc n) \<equiv>\<^sub>p \<Union>\<^sub>p [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int n]] \<union>\<^sub>p while_support a C b (Suc n) (Suc n)"
    using Suc equiv_is_reflexive equiv_is_transitive equivalence_is_maintained_by_choice l1 by blast
  have l6: "while_support a C b (Suc n) (Suc n) \<equiv>\<^sub>p (a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C)"
    by (metis equiv_is_reflexive equivalence_is_maintained_by_composition equivalence_is_maintained_by_corestriction loop_l2_1 while_support_def)
  then show "while_loop a C b (Suc n) \<equiv>\<^sub>p \<Union>\<^sub>p [a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ nat i) \<setminus>\<^sub>p C. i \<leftarrow> [0..int (Suc n)]]"
    by (smt (verit, ccfv_SIG) Suc equiv_is_symetric equiv_is_transitive equivalence_is_maintained_by_choice l4 l5)
qed

theorem loop_union2: "Range_p (while_loop a C b n) = \<Union>\<^sub>s [Range_p (a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC). i \<leftarrow> [0..int n]]"
proof (induction n)
  case 0
  then show ?case
    by (auto simp: Range_p_def while_loop_def) [1]
next
  case (Suc n)
  assume IH: "Range_p (while_loop a C b n) = \<Union>\<^sub>s [Range_p (a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC). i \<leftarrow> [0..int n]]"
  have l1: "while_loop a C b (Suc n) \<equiv>\<^sub>p (while_loop a C b n) \<union>\<^sub>p (a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C)"
    apply (simp add: while_loop_def)
    using compose_distrib1_3 corestrict_union equiv_is_reflexive equiv_is_transitive equivalence_is_maintained_by_composition by blast
  from l1 have l2: "Range_p (while_loop a C b (Suc n)) = Range_p (while_loop a C b n) \<union> Range_p (a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C)"
    by (metis same_range_p_3 range_p_prop_1)
  from l1 have l3: "Range_p (while_loop a C b (Suc n)) = \<Union>\<^sub>s [Range_p (a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC). i \<leftarrow> [0..int n]] \<union> Range_p (a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C)"
    by (simp add: Suc l2)
  have l4: "\<Union>\<^sub>s [Range_p (a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC). i \<leftarrow> [0..int (Suc n)]] = \<Union>\<^sub>s [Range_p (a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC). i \<leftarrow> [0..int n]] \<union> Range_p (a ; ((b \<sslash>\<^sub>p (- C)) \<^bold>^ (Suc n)) \<setminus>\<^sub>p C)"
    by (metis (no_types, lifting) inf_sup_aci(5) list_comp_prop_1 nat_int Union_prop_1)
  from IH show "Range_p (while_loop a C b (Suc n)) = \<Union>\<^sub>s [Range_p (a;((b \<sslash>\<^sub>p (- C))\<^bold>^(nat i))\<setminus>\<^sub>pC). i \<leftarrow> [0..int (Suc n)]]"
    using l3 l4 by blast
qed

theorem while_loop_feasible: "all_feasible [a, b] \<Longrightarrow> is_feasible (while_loop a C b n)" \<comment> \<open>Disproves a statement below T77\<close>
  by (simp add: while_conncetion while_support_feasible)

theorem equiv_is_maintained_by_while_loop_2: 
  assumes "a\<^sub>1 \<equiv>\<^sub>p a\<^sub>2"
      and "b\<^sub>1 \<equiv>\<^sub>p b\<^sub>2"
      and "S b\<^sub>1 = S b\<^sub>2"
      and "all_feasible [b\<^sub>1, b\<^sub>2]"
    shows "while_loop a\<^sub>1 C b\<^sub>1 n \<equiv>\<^sub>p while_loop a\<^sub>2 C b\<^sub>2 n"
  by (metis assms(1) assms(2) assms(3) assms(4) equiv_is_maintained_by_while_support_1 while_conncetion)

theorem range_while_loop_1: "m\<le>n \<Longrightarrow> x \<notin> Range_p (while_loop a C b n) \<Longrightarrow> x \<notin> Range_p (while_loop a C b m)"
proof (induction n)
  case 0
  then show ?case
    by blast
next
  case (Suc n)
  assume IH: "m \<le> n \<Longrightarrow> x \<notin> Range_p (while_loop a C b n) \<Longrightarrow> x \<notin> Range_p (while_loop a C b m)"
  assume a1: "m \<le> Suc n"
  assume a2: "x \<notin> Range_p (while_loop a C b (Suc n))"
  have l1: "while_loop a C b (Suc n) \<equiv>\<^sub>p while_loop a C b n \<union>\<^sub>p a;((b\<sslash>\<^sub>p(-C))\<^bold>^(Suc n))\<setminus>\<^sub>pC"
    using while_decomposition_2 by auto
  then show "x \<notin> Range_p (while_loop a C b m)"
  proof (cases "m\<le>n")
    case True
    then show ?thesis
    proof (cases "x \<notin> Range_p (while_loop a C b n)")
      case True
      then show ?thesis
        using IH a1 a2 le_SucE by auto
    next
      case False
      then show ?thesis
        by (metis a2 choice_range_p_prop_3 l1 same_range_p_3)
    qed
  next
    case False
    then have l2: "m=Suc n"
      using a1 by auto
    then show ?thesis
      by (simp add: a2)
  qed
qed

theorem range_while_loop_2: "m\<le>n \<Longrightarrow> x \<notin> Range_p (while_loop a C b n) \<Longrightarrow> x \<notin> Range_p (while_support a C b s m)"
proof -
  fix n assume a1: "m\<le>n"
  assume a2: "x \<notin> Range_p (while_loop a C b n)"
  have l1: "x \<notin> Range_p (while_loop a C b m)"
    by (meson a1 a2 range_while_loop_1)
  show "x \<notin> Range_p (while_support a C b s m)"
  proof (induction s)
    case 0
    then show ?case
      by (metis l1 while_conncetion)
  next
    case (Suc s)
    assume a3: "x \<notin> Range_p (while_support a C b s m)"
    then show "x \<notin> Range_p (while_support a C b (Suc s) m)"
    proof (cases "s\<ge>m")
      case True
      from True have l2: "loop (b \<sslash>\<^sub>p (- C)) (Suc s) m \<equiv>\<^sub>p Fail C"
        by (metis arbitrary_repetition.elims fail_is_equivalent_independant_of_arg le_imp_less_Suc)
      have l3: "a ; Fail C \<setminus>\<^sub>p C \<equiv>\<^sub>p Fail C"
        by (metis corestrict_compose equiv_is_symetric equiv_is_transitive equivalence_is_maintained_by_corestriction fail_compose_l fail_compose_r)
      have l4: "while_support a C b (Suc s) m \<equiv>\<^sub>p Fail C"
        apply (auto simp: while_support_def)
        by (meson equiv_is_reflexive equiv_is_transitive equivalence_is_maintained_by_composition equivalence_is_maintained_by_corestriction l2 l3)
      then show ?thesis
        by (metis choice_range_p_prop_1 fail_union_l l1 same_range_p_3 subset_iff)
    next
      case False
      then have l2: "s < m" by simp
      have "while_support a C b s m \<equiv>\<^sub>p while_support a C b s s \<union>\<^sub>p while_support a C b (Suc s) m"
          by (simp add: l2 less_imp_le_nat while_decomp_3)
      (* from while_decomp_3 have l2: "while_support a C b (Suc s) m \<equiv>\<^sub>p while_support a C b s m \<union>\<^sub>p a ; loop (b \<sslash>\<^sub>p (- C)) (Suc s) m \<setminus>\<^sub>p C" *)
      then show ?thesis
        by (metis a3 choice_commute choice_range_p_prop_3 same_range_p_3)
    qed
  qed
qed

theorem range_while_loop_3: "Range_p (while_loop a C b n) \<subseteq> C"
  by (metis Corestriction.corestrict_prop_1 corestrict_compose same_range_p_3 while_conncetion while_support_def)

theorem split_front: "while_loop (x;a) C b n \<equiv>\<^sub>p x ; while_loop a C b n"
  by (metis compose_assoc_3 while_loop_def)

end