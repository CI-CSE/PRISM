theory Guarded_conditional
  imports "../T_03_Basic_programs" "Big_choice" "Permutations"
begin
section \<open>Guarded conditional top\<close>

theorem gc_S: "S (GC ((C,p)#xs)) = S p \<union> S (GC xs)"
  apply (cases "xs = []") apply (auto simp: guarded_conditional_def Fail_def S_def restrict_p_def restrict_r_def Field_def) [1]
proof -
  assume a1: "xs \<noteq> []"
  have "GC ((C,p)#xs) = p\<sslash>\<^sub>pC \<union>\<^sub>p GC (xs)"
    apply (auto simp: guarded_conditional_def)
    using Choice_prop_1_2 a1 by auto
  show ?thesis
    using \<open>GC ((C, p) # xs) = p \<sslash>\<^sub>p C \<union>\<^sub>p GC xs\<close> by auto
qed

theorem gc_S_1: "S (GC (xs)) = complete_state ([snd t. t \<leftarrow> (xs)])"
  apply (induction xs)
   apply (auto simp: complete_state_def guarded_conditional_def) [1]
  apply (metis special_empty1 equals0D skip_prop_9)
  by (metis (no_types, lifting) Choice_state_1 complete_state_prop guarded_conditional_def list.simps(9) restriction_state)


theorem cond_helper_1: "GC (x#xs) = GC (xs @ [x])"
  apply (induction xs)
  apply simp
  apply (auto simp: guarded_conditional_def)
  by (metis (no_types, lifting) Choice.simps(2) Choice_prop_1_2 Choice_prop_1_4 choice_assoc_1 foldl_Nil snoc_eq_iff_butlast)

theorem cond_helper_2: "xs\<noteq>[] \<Longrightarrow> GC (x#xs) = GC [x] \<union>\<^sub>p GC xs"
  apply (induction xs)
  apply (auto simp: guarded_conditional_def)
  using Choice_prop_1_4 by fastforce

theorem cond_helper_3: "a \<noteq>[] \<Longrightarrow> b\<noteq> [] \<Longrightarrow> GC (a@b) = GC a \<union>\<^sub>p GC b"
  apply (auto simp: guarded_conditional_def) [1]
  by (simp add: Choice_prop_7)

theorem cond_commute: "xs \<in> set (permutations ys) \<Longrightarrow> GC xs = GC ys" \<comment> \<open>Cond_commute\<close>
  apply (auto simp: guarded_conditional_def)
  by (metis (mono_tags, lifting) Choice_prop_1_1 perm_prop_2)

theorem cond_sub1: "D\<^sub>1 \<subseteq> C\<^sub>1 \<Longrightarrow> D\<^sub>2 \<subseteq> C\<^sub>2 \<Longrightarrow> (GC [(D\<^sub>1, p), (D\<^sub>2, q)]) \<preceq>\<^sub>p (GC [(C\<^sub>1, p), (C\<^sub>2, q)])" \<comment> \<open>Cond_sub1\<close>
  apply (auto simp: subprogram_def extends_def weakens_def strengthens_def guarded_conditional_def restr_post_def restrict_p_def restrict_r_def choice_def)
  apply (simp add: S_def Field_def Range_iff Domain_iff)
  by force

theorem property_on_gc_3: "all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> GC [(C\<^sub>1, p\<^sub>1), (C\<^sub>2, p\<^sub>2)] \<subseteq>\<^sub>p p\<^sub>1 \<sslash>\<^sub>p C\<^sub>1" \<comment> \<open>T54\<close>
  oops

theorem property_on_gc_3_1: "weakens (GC [(C\<^sub>1, p\<^sub>1), (C\<^sub>2, p\<^sub>2)]) (p\<^sub>1 \<sslash>\<^sub>p C\<^sub>1)"
  by (auto simp: weakens_def restrict_p_def guarded_conditional_def choice_def)

theorem property_on_gc_3_2: "strengthens (p\<^sub>1 \<sslash>\<^sub>p C\<^sub>1) (GC [(C\<^sub>1, p\<^sub>1), (C\<^sub>2, p\<^sub>2)])"
  by (auto simp: strengthens_def restr_post_def restrict_r_def restrict_p_def guarded_conditional_def choice_def)

theorem cond_sub4: "(p\<^sub>1 \<sslash>\<^sub>p C\<^sub>1) \<preceq>\<^sub>p (GC [(C\<^sub>1, p\<^sub>1), (C\<^sub>2, p\<^sub>2)])" \<comment> \<open>Cond_sub4\<close>
  by (auto simp: restrict_p_def subprogram_def guarded_conditional_def extends_def weakens_def restr_post_def restrict_r_def strengthens_def)

theorem refinement_safety_gc_1: "all_feasible [p, q] \<Longrightarrow> D\<^sub>1 \<subseteq> C\<^sub>1 \<Longrightarrow> D\<^sub>2 \<subseteq> C\<^sub>2 \<Longrightarrow> GC [(D\<^sub>1, p), (D\<^sub>2, q)] \<subseteq>\<^sub>p GC [(C\<^sub>1, p), (C\<^sub>2, q)]" \<comment> \<open>T49\<close>
  oops

theorem refinement_safety_gc_2: "all_feasible [p, q] \<Longrightarrow> D\<^sub>1 \<subseteq> C\<^sub>1 \<Longrightarrow> D\<^sub>2 \<subseteq> C\<^sub>2 \<Longrightarrow> GC [(C\<^sub>1, p), (C\<^sub>2, q)] \<subseteq>\<^sub>p GC [(D\<^sub>1, p), (D\<^sub>2, q)]" \<comment> \<open>T49\<close>
  oops

theorem refinement_safety_gc_weakens: "D\<^sub>1 \<subseteq> C\<^sub>1 \<Longrightarrow> D\<^sub>2 \<subseteq> C\<^sub>2 \<Longrightarrow> weakens (GC [(C\<^sub>1, p), (C\<^sub>2, q)]) (GC [(D\<^sub>1, p), (D\<^sub>2, q)])" \<comment> \<open>T49\<close>
  by (auto simp: weakens_def guarded_conditional_def restrict_p_def restrict_r_def choice_def)

theorem refinement_safety_gc_strengthens: "D\<^sub>1 \<subseteq> C\<^sub>1 \<Longrightarrow> D\<^sub>2 \<subseteq> C\<^sub>2 \<Longrightarrow> strengthens (GC [(D\<^sub>1, p), (D\<^sub>2, q)]) (GC [(C\<^sub>1, p), (C\<^sub>2, q)])" \<comment> \<open>T49\<close>
  by (auto simp: strengthens_def restr_post_def guarded_conditional_def restrict_p_def restrict_r_def choice_def)

theorem cond_refine1: "D\<^sub>1 \<subseteq> C\<^sub>1 \<Longrightarrow> D\<^sub>2 \<subseteq> C\<^sub>2 \<Longrightarrow> (GC [(D\<^sub>1, p), (D\<^sub>2, q)]) \<subseteq>\<^sub>p (GC [(C\<^sub>1, p), (C\<^sub>2, q)])" \<comment> \<open>Cond_refine1\<close>
  oops

theorem cond_refine2: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> GC [(C, q\<^sub>1), (C, q\<^sub>2)] \<subseteq>\<^sub>p GC [(C, p\<^sub>1), (C, p\<^sub>2)]"
  oops

theorem refinement_safety_gc_3: "all_feasible [p\<^sub>1, p\<^sub>2, q\<^sub>1, q\<^sub>2] \<Longrightarrow> strengthens q\<^sub>1 p\<^sub>2 \<Longrightarrow> strengthens q\<^sub>2 p\<^sub>1 \<Longrightarrow> q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> GC [(C, q\<^sub>1), (C, q\<^sub>2)] \<subseteq>\<^sub>p GC [(C, p\<^sub>1), (C, p\<^sub>2)]" \<comment> \<open>T50 NEW Same problem as with refinement safety of choice\<close>
  apply (auto simp: refines_def)
  apply (auto simp: is_feasible_def extends_def) [1]
  apply (metis Un_iff gc_S subsetD)
  apply (auto simp: weakens_def is_feasible_def guarded_conditional_def restrict_p_def restrict_r_def choice_def)  [1]
  apply (simp add: strengthens_def restr_post_def restrict_p_def restrict_r_def Fail_def weakens_def subset_iff guarded_conditional_def)
  by blast

theorem refinement_safety_gc_4: "all_feasible [p\<^sub>1, p\<^sub>2, q\<^sub>1, q\<^sub>2] \<Longrightarrow> independent q\<^sub>1 p\<^sub>2 \<Longrightarrow> independent q\<^sub>2 p\<^sub>1 \<Longrightarrow> q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> GC [(C, q\<^sub>1), (C, q\<^sub>2)] \<subseteq>\<^sub>p GC [(C, p\<^sub>1), (C, p\<^sub>2)]" \<comment> \<open>T50 NEW Same problem as with refinement safety of choice\<close>
  using independent_strengthens refinement_safety_gc_3 by blast


theorem cond_refine4: "GC [(C\<^sub>1, p\<^sub>1), (C\<^sub>2, p\<^sub>2)] \<subseteq>\<^sub>p p\<^sub>1 \<sslash>\<^sub>p C\<^sub>1" \<comment> \<open>Cond_refine4\<close>
  oops \<comment> \<open>C1 and C2 might have an overlap\<close>

theorem cond_sub2: "q\<^sub>1 \<preceq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<preceq>\<^sub>p p\<^sub>2 \<Longrightarrow> GC [(C, q\<^sub>1), (C, q\<^sub>2)] \<preceq>\<^sub>p GC [(C, p\<^sub>1), (C, p\<^sub>2)]" \<comment> \<open>Cond_sub2\<close>
  apply (auto simp: subprogram_def guarded_conditional_def extends_def weakens_def Fail_def)
  apply (auto simp: subprogram_def guarded_conditional_def extends_def weakens_def Fail_def restrict_p_def) [2]
  by (auto simp: subprogram_def guarded_conditional_def extends_def weakens_def Fail_def restrict_p_def strengthens_def restr_post_def restrict_r_def)

theorem cond_distrib: "GC xs \<sslash>\<^sub>p C \<equiv>\<^sub>p GC [(fst t \<inter> C, snd t) . t \<leftarrow> xs]"
proof (induction xs arbitrary: C)
  case Nil
  then show ?case by (auto simp: equiv_def guarded_conditional_def Fail_def restrict_p_def restr_post_def restrict_r_def)
next
  case (Cons x xs)
  then show "GC (x # xs) \<sslash>\<^sub>p C \<equiv>\<^sub>p GC (map (\<lambda>t. (fst t \<inter> C, snd t)) (x # xs))"
  proof (cases "xs = []")
    case True
    then show ?thesis by (auto simp: equiv_def guarded_conditional_def Fail_def restrict_p_def restr_post_def restrict_r_def)
  next
    case False
    have "GC (x # xs) \<sslash>\<^sub>p C = (snd x \<sslash>\<^sub>p fst x \<union>\<^sub>p GC xs) \<sslash>\<^sub>p C" apply (auto simp: guarded_conditional_def)
      by (simp add: Choice_prop_1_2 False)
    moreover have "... \<equiv>\<^sub>p (snd x \<sslash>\<^sub>p fst x) \<sslash>\<^sub>p C \<union>\<^sub>p GC xs \<sslash>\<^sub>p C"
      using restrict_distrib_3 by blast
    moreover have "... \<equiv>\<^sub>p snd x \<sslash>\<^sub>p (fst x \<inter> C) \<union>\<^sub>p GC (map (\<lambda>t. (fst t \<inter> C, snd t)) xs)"
      by (metis (mono_tags, lifting) choice_equiv inf_sup_ord(2) local.Cons restrict_subprogorder1 restrict_idem restrict_inter subprogram_is_antisymetric)
    moreover have "... = GC (map (\<lambda>t. (fst t \<inter> C, snd t)) (x # xs))"
      by (simp add: Choice_prop_1_2 False guarded_conditional_def)
    ultimately show "GC (x # xs) \<sslash>\<^sub>p C \<equiv>\<^sub>p GC (map (\<lambda>t. (fst t \<inter> C, snd t)) (x # xs))" using equiv_is_transitive by fastforce
  qed
qed

theorem GC_prop_22: "a \<union>\<^sub>p GC (x#xs) = a \<union>\<^sub>p (GC [x] \<union>\<^sub>p GC xs)"
  apply (auto simp: guarded_conditional_def)
  by (simp add: Choice_prop_22)


theorem gc_prop1: "S (snd x) \<subseteq> complete_state (map snd xs) \<Longrightarrow> fst x = FALSE \<Longrightarrow> 1 < length xs \<Longrightarrow> GC (x # xs) = GC xs"
apply (auto simp: guarded_conditional_def)
proof (induction "size xs" arbitrary:  xs x)
  case 0
  then show ?case by (auto)
next
  case (Suc n)
  have "\<Union>\<^sub>p (snd x \<sslash>\<^sub>p FALSE # map (\<lambda>t. snd t \<sslash>\<^sub>p fst t) xs) = (snd x \<sslash>\<^sub>p FALSE) \<union>\<^sub>p \<Union>\<^sub>p (map (\<lambda>t. snd t \<sslash>\<^sub>p fst t) xs)" using Choice_prop_1_2
    by (metis (no_types, lifting) Suc.hyps(2) Zero_not_Suc length_0_conv map_is_Nil_conv)
  moreover have "... = Fail {} \<union>\<^sub>p \<Union>\<^sub>p (map (\<lambda>t. snd t \<sslash>\<^sub>p fst t) xs)"
    by (metis Suc.prems(1) gc_S_1 guarded_conditional_def restrict_false2)
  moreover have "... = \<Union>\<^sub>p (map (\<lambda>t. snd t \<sslash>\<^sub>p fst t) xs)"
    by (smt (z3) Choice_prop_1_2 Suc.prems(2) Suc.prems(3) Suc_le_length_iff Suc_length_conv antisym_conv3 empty_def empty_subsetI fail_union_1 length_map list.size(3) map_eq_map_tailrec order.asym order_less_imp_le)
  ultimately show "\<Union>\<^sub>p (snd x \<sslash>\<^sub>p FALSE # map (\<lambda>t. snd t \<sslash>\<^sub>p fst t) xs) = \<Union>\<^sub>p (map (\<lambda>t. snd t \<sslash>\<^sub>p fst t) xs)"
    by simp
qed


theorem gc_prop2: "S (snd x) \<subseteq> complete_state (map snd (a@b)) \<Longrightarrow> fst x = FALSE \<Longrightarrow> size (a@b) > 1 \<Longrightarrow> GC (a@x#b) = GC(a@b)" \<comment> \<open>If_false2\<close>
  apply (auto simp: guarded_conditional_def)
proof (induction "size a" arbitrary: a x b)
  case 0
  then show ?case using gc_prop1 apply (auto simp: guarded_conditional_def)
    by blast
next
  case (Suc n)
  obtain a' where o1: "a' = map (\<lambda>t. snd t \<sslash>\<^sub>p fst t) a" by simp
  obtain b' where o2: "b' = map (\<lambda>t. snd t \<sslash>\<^sub>p fst t) b" by simp
  have l1: "size a' + size b' > 1" by (auto simp: o1 o2 Suc)
  have l2: "S (snd x) \<subseteq> complete_state (a' @ b')"
    by (metis (mono_tags, lifting) Choice_state_1 Suc.prems(1) gc_S_1 guarded_conditional_def map_append o1 o2)
  have "\<Union>\<^sub>p (map (\<lambda>t. snd t \<sslash>\<^sub>p fst t) a @ snd x \<sslash>\<^sub>p FALSE # map (\<lambda>t. snd t \<sslash>\<^sub>p fst t) b) = \<Union>\<^sub>p (a' @ snd x \<sslash>\<^sub>p FALSE # b')" by (simp add: o1 o2)
  moreover have "... = \<Union>\<^sub>p a' \<union>\<^sub>p (snd x \<sslash>\<^sub>p FALSE \<union>\<^sub>p \<Union>\<^sub>p b')" using Choice_prop_20
    by (metis length_0_conv length_append length_greater_0_conv less_nat_zero_code local.l1)
  moreover have "... = \<Union>\<^sub>p a' \<union>\<^sub>p (Fail {} \<union>\<^sub>p \<Union>\<^sub>p b')"
    using Choice_prop_21 l2 by auto
  moreover have "... = \<Union>\<^sub>p a' \<union>\<^sub>p \<Union>\<^sub>p b'"
    by (metis choice_idem_5 empty_subsetI fail_union_1)
  moreover have "... = \<Union>\<^sub>p (a'@b')" using Choice_prop_19 l1
    by auto
  moreover have "... = \<Union>\<^sub>p (map (\<lambda>t. snd t \<sslash>\<^sub>p fst t) a @ map (\<lambda>t. snd t \<sslash>\<^sub>p fst t) b)"
    by (simp add: o1 o2)
  ultimately show "\<Union>\<^sub>p (map (\<lambda>t. snd t \<sslash>\<^sub>p fst t) a @ snd x \<sslash>\<^sub>p FALSE # map (\<lambda>t. snd t \<sslash>\<^sub>p fst t) b) = \<Union>\<^sub>p (map (\<lambda>t. snd t \<sslash>\<^sub>p fst t) a @ map (\<lambda>t. snd t \<sslash>\<^sub>p fst t) b)" by force
qed

theorem if_false2: "fst x = FALSE \<Longrightarrow> GC (a@x#b) \<equiv>\<^sub>p GC(a@b)" \<comment> \<open>If_false2\<close>
  apply (cases "size (a@b) = 0") apply (auto simp: guarded_conditional_def restrict_p_def Fail_def) [1] apply (metis FALSE_def Fail_def Program.select_convs(2) equiv_is_symetric inf_bot_right no_pre_is_fail)
proof (cases "size (a@b) = 1")
  case True
  assume a0: "fst x = FALSE"
  assume a1: "length (a @ b) = 1"
  have l1: "snd x \<sslash>\<^sub>p fst x \<equiv>\<^sub>p Fail {}" using a0 by (auto simp: restrict_p_def FALSE_def equiv_def Fail_def restr_post_def restrict_r_def)
  then show ?thesis
  proof (cases "a=[]")
    case True
    assume a2: "a = []"
    obtain b' where o1: "b = [b']"
      by (metis Suc_diff_1 a1 a2 append_self_conv2 diff_is_0_eq' le_cube length_0_conv length_Suc_conv_rev mult.right_neutral zero_less_one)
    have "GC [x, b'] = snd x \<sslash>\<^sub>p fst x \<union>\<^sub>p snd b' \<sslash>\<^sub>p fst b'" by (auto simp: guarded_conditional_def)
    moreover have "... \<equiv>\<^sub>p snd b' \<sslash>\<^sub>p fst b'" using l1 fail_choice_l apply auto
      using equiv_is_reflexive equiv_is_transitive choice_equiv by blast
    moreover have "... = GC [b']" by (auto simp: guarded_conditional_def)
    ultimately have "GC [x, b'] \<equiv>\<^sub>p GC [b']"
      by argo
    then show ?thesis using a2 o1 a0 by auto
  next
    case False
    have a2: "b = []" using False a1 apply auto
      by (metis length_0_conv one_is_add)
    obtain a' where o1: "a = [a']"
      by (metis False One_nat_def a1 a2 card_set_1_iff_replicate le_numeral_extra(4) replicate_Suc replicate_empty rotate1_fixpoint_card rotate1_length01 self_append_conv)
    have "GC [a', x] = snd x \<sslash>\<^sub>p fst x \<union>\<^sub>p snd a' \<sslash>\<^sub>p fst a'" by (auto simp: guarded_conditional_def)
    moreover have "... \<equiv>\<^sub>p snd a' \<sslash>\<^sub>p fst a'" using l1 fail_choice_l apply auto
      using equiv_is_reflexive equiv_is_transitive choice_equiv by blast
    moreover have "... = GC [a']" by (auto simp: guarded_conditional_def)
    ultimately show ?thesis using a2 o1 a0 by auto
  qed
next
  case False
  assume a0: "fst x = FALSE"
  assume a1: "length (a @ b) \<noteq> 0"
  have l1: "GC [x]  \<equiv>\<^sub>p Fail {}" using a0 by (auto simp: guarded_conditional_def restrict_p_def FALSE_def equiv_def Fail_def restr_post_def restrict_r_def)
  have l2: "length (a @ b) > 1" using False a1
    by linarith
  have l3: "GC [x] \<equiv>\<^sub>p Fail {}" using l1 by (auto simp: guarded_conditional_def)
  have "a @ x # b \<in> set (permutations (x#a @ b))"
    by (meson insert_perm_rel l4)
  have "GC (a @ x # b) = GC (x#a @ b)"
    using \<open>a @ x # b \<in> set (permutations (x # a @ b))\<close> cond_commute by blast
  moreover have "... = GC [x] \<union>\<^sub>p GC (a @ b)"
    by (metis a1 cond_helper_2 list.size(3))
  moreover have "... \<equiv>\<^sub>p Fail {} \<union>\<^sub>p GC (a @ b)" using l1 l2
    by (metis equiv_is_reflexive choice_equiv)
  moreover have "... \<equiv>\<^sub>p GC (a @ b)"
    by (simp add: fail_choice_l)
  ultimately show ?thesis using equiv_is_transitive by force
qed

theorem gc_prop4: "S (snd x) \<subseteq> complete_state (map snd (a@b)) \<Longrightarrow> fst x = FALSE \<Longrightarrow> size (a@b) = 0 \<Longrightarrow> GC (a@x#b) = GC(a@b)"
  by (auto simp: guarded_conditional_def Fail_def FALSE_def restrict_p_def complete_state_def S_def Field_def restrict_r_def)

theorem fail_choice: "S q \<subseteq> S p \<Longrightarrow> q \<equiv>\<^sub>p Fail {} \<Longrightarrow> q \<union>\<^sub>p p = Fail {} \<union>\<^sub>p p"
  by (auto simp: choice_def Fail_def equiv_def restr_post_def restrict_r_def S_def)


theorem gc_prop5: "S (snd x) \<subseteq> complete_state (map snd (a@b)) \<Longrightarrow> fst x = FALSE \<Longrightarrow> size (a@b) = 1 \<Longrightarrow> GC (a@x#b) = Fail {} \<union>\<^sub>p GC(a@b)"
proof -
  assume "S (snd x) \<subseteq> complete_state (map snd (a@b))"
  assume "fst x = FALSE"
  assume "size (a@b) = 1"
  have "S (snd x) \<subseteq> S (GC (a@b))" using \<open>S (snd x) \<subseteq> complete_state (map snd (a@b))\<close> gc_S_1 apply (auto simp: )
    by (simp add: gc_S_1 subsetD)
  have "snd x \<sslash>\<^sub>p fst x \<equiv>\<^sub>p Fail {}" using \<open>fst x = FALSE\<close>
    by (metis cond_false_1 equiv_is_transitive fail_equiv)
  have "GC (a@x#b) = GC (x#a@b)"
    by (metis (no_types, opaque_lifting) \<open>length (a @ b) = 1\<close> append_eq_conv_conj cond_helper_1 diff_is_0_eq leI length_0_conv length_drop less_one self_append_conv self_append_conv2)
  obtain xs where o1: "xs=a@b" by simp
  have "GC (x#xs) = snd x \<sslash>\<^sub>p fst x \<union>\<^sub>p GC (xs)" apply (auto simp: guarded_conditional_def)
    by (metis (no_types, lifting) Choice_prop_1_2 \<open>length (a @ b) = 1\<close> list.map_disc_iff list.size(3) o1 zero_neq_one)
  have "... = Fail {} \<union>\<^sub>p GC (xs)"
    using \<open>S (snd x) \<subseteq> S (GC (a @ b))\<close> \<open>fst x = FALSE\<close> o1 restrict_false2 by fastforce
  then show ?thesis
    using \<open>GC (a @ x # b) = GC (x # a @ b)\<close> \<open>GC (x # xs) = snd x \<sslash>\<^sub>p fst x \<union>\<^sub>p GC xs\<close> o1 by auto
qed
  
theorem cond_one: "GC [(C,p)] = p\<sslash>\<^sub>pC" \<comment> \<open>Cond_one\<close>
  by (auto simp: guarded_conditional_def)

theorem gc_prop6: "x \<sslash>\<^sub>p C \<preceq>\<^sub>p GC ((C,x) # xs)"
  apply (induction xs)
  apply (auto simp: guarded_conditional_def)
  apply (simp add: subprogram_is_preorder)
  by (metis (no_types, lifting) choice_commute fold_choice program_is_subprogram_of_choice)



theorem gc_prop7: "GC a \<preceq>\<^sub>p GC (a@b)"
  apply (induction a)
  apply (auto simp: guarded_conditional_def) [1]
   apply (simp add: fail_subprogram3)
proof -
  fix a1 a2 assume "GC a2 \<preceq>\<^sub>p GC (a2 @ b)"
  show "GC (a1 # a2) \<preceq>\<^sub>p GC ((a1 # a2) @ b)"
  proof (cases "a2=[]")
    case True
    then show ?thesis apply auto
      by (metis cond_one gc_prop6 old.prod.exhaust)
  next
    case False
    have "GC (a1 # a2) = GC [a1] \<union>\<^sub>p GC a2"
      by (simp add: False cond_helper_2)
    then show ?thesis
      by (metis append_Nil2 choice_commute choice_decomp_1 cond_helper_3 list.discI program_is_subprogram_of_choice)
  qed
qed

theorem cond_sub3: "(C, x) \<in> set (xs) \<Longrightarrow> x\<sslash>\<^sub>pC \<preceq>\<^sub>p GC xs" \<comment> \<open>Cond_sub3\<close>
proof (induction xs)
  case Nil
  then show ?case by (auto simp: guarded_conditional_def subprogram_def extends_def weakens_def strengthens_def)
next
  case (Cons a xs)
  then show ?case
  proof (cases "a = (C, x)")
    case True
    then show ?thesis
      by (simp add: gc_prop6)
  next
    case False
    have "(C, x) \<in> set xs"
      using Cons.prems False by auto
    have "x \<sslash>\<^sub>p C \<preceq>\<^sub>p GC xs"
      by (simp add: Cons.IH \<open>(C, x) \<in> set xs\<close>)
    then show ?thesis
      by (metis cond_helper_1 gc_prop7 subprogram_is_preorder)
  qed
qed

end