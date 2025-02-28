theory Non_atomic_concurrency
  imports "../T_03_Basic_programs" "Atomic_concurrency" "Big_choice"
begin
section \<open>Non-Atomic concurrency for top\<close>
\<comment> \<open>DEPRECATED. This used an old definition of concurrency\<close>
theorem non_atomic_prop1: "[] \<parallel> x = x" by (auto simp: non_atomic_conc_def complete_state_def)


theorem non_atomic_prop2: "((a # xs) \<parallel> x) \<equiv>\<^sub>p a;(xs \<parallel> x) \<union>\<^sub>p Concat (x#a#xs)"
  apply (cases "xs=[]") apply (auto simp: non_atomic_conc_def) [1]
  apply (simp add: equals_equiv_relation_3)
proof -
  assume a1: "xs \<noteq> []"
  have l1: "size xs > 0" using a1 by auto
  have "a;(xs \<parallel> x) = a;\<Union>\<^sub>p [Concat t. t \<leftarrow> insert_all x (xs)]"
    by (simp add: non_atomic_conc_def)

  have "((a # xs) \<parallel> x) = \<Union>\<^sub>p [Concat t. t \<leftarrow> insert_all x (a#xs)]"
    by (simp add: non_atomic_conc_def)

  have "[Concat t. t \<leftarrow> insert_all x (a#xs)] = Concat (x#a#xs)#[a;(Concat t). t \<leftarrow> insert_all x (xs)]"
    apply (auto simp:)
    by (metis Concat.simps(3) Concat_prop_1 append_is_Nil_conv l14 neq_Nil_conv)

  have "\<Union>\<^sub>p [Concat t. t \<leftarrow> insert_all x (a#xs)] = Concat (x#a#xs) \<union>\<^sub>p \<Union>\<^sub>p [a;(Concat t). t \<leftarrow> insert_all x (xs)]"
    using Choice_prop_1_2 \<open>map Concat (insert_all x (a # xs)) = Concat (x # a # xs) # map (\<lambda>t. a ; Concat t) (insert_all x xs)\<close> l1
    by (metis a1 insert_all.simps(2) list.discI map_is_Nil_conv permutations.elims)

  have "\<Union>\<^sub>p [a;(Concat t). t \<leftarrow> insert_all x (xs)] \<equiv>\<^sub>p a;\<Union>\<^sub>p [(Concat t). t \<leftarrow> insert_all x (xs)]"
  proof -
    obtain q where o1: "q = insert_all x (xs)" by simp
    have "size q > 0" apply (simp add: o1)
      by (metis (no_types) member_rec(2) orig_is_permutation_1)
    then have "\<Union>\<^sub>p [a;(Concat t). t \<leftarrow> q] \<equiv>\<^sub>p a;\<Union>\<^sub>p [(Concat t). t \<leftarrow> q]"
      by (simp add: Choice_prop_13)
    show ?thesis
      using \<open>\<Union>\<^sub>p (map (\<lambda>t. a ; Concat t) q) \<equiv>\<^sub>p a ; \<Union>\<^sub>p (map Concat q)\<close> o1 by auto
  qed

  show ?thesis
    by (metis \<open>(a # xs \<parallel> x) = \<Union>\<^sub>p (map Concat (insert_all x (a # xs)))\<close> \<open>\<Union>\<^sub>p (map (\<lambda>t. a ; Concat t) (insert_all x xs)) \<equiv>\<^sub>p a ; \<Union>\<^sub>p (map Concat (insert_all x xs))\<close> \<open>\<Union>\<^sub>p (map Concat (insert_all x (a # xs))) = Concat (x # a # xs) \<union>\<^sub>p \<Union>\<^sub>p (map (\<lambda>t. a ; Concat t) (insert_all x xs))\<close> \<open>a ; (xs \<parallel> x) = a ; \<Union>\<^sub>p (map Concat (insert_all x xs))\<close> choice_commute equals_equiv_relation_3 choice_equiv)
qed

theorem compose_distrib: "(b \<union>\<^sub>p (a ; c \<union>\<^sub>p a ; d)) = (b \<union>\<^sub>p a ; (c \<union>\<^sub>p d))"
  apply (auto simp add: composition_def choice_def restr_post_def)
  apply (auto simp: restrict_r_def Field_def corestrict_r_def)
   apply (auto simp: S_def) [1]
          apply (auto simp: Field_def)
  apply (auto simp: relcomp_unfold)
  by (simp add: S_def Field_def Domain_iff Range_iff)

theorem concur_two: "[a]\<parallel>b = a;b \<union>\<^sub>p b;a" \<comment> \<open>Concur_two\<close>
  by (auto simp: non_atomic_conc_def)

theorem concur_commute: "[a]\<parallel>b = ([b]\<parallel>a)" \<comment> \<open>Concur_commute\<close>
  by (auto simp: non_atomic_conc_def)

theorem compose_distrib2: "\<forall>x \<in> set xs. x \<noteq> [] \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> b \<union>\<^sub>p \<Union>\<^sub>p [a;(Concat t). t \<leftarrow> xs] = b \<union>\<^sub>p  a;\<Union>\<^sub>p [(Concat t). t \<leftarrow> xs]"
proof (induction xs arbitrary: a b)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have "[a ; Concat t. t \<leftarrow> (x # xs)] = (a ; Concat x)#[a ; Concat t. t \<leftarrow> xs]"
    by simp
  have "b \<union>\<^sub>p \<Union>\<^sub>p [a ; Concat t. t \<leftarrow> (x # xs)] = b \<union>\<^sub>p ((a ; Concat x) \<union>\<^sub>p \<Union>\<^sub>p [a ; Concat t. t \<leftarrow> (xs)])"
    by (metis (no_types, lifting) Choice.simps(1) Choice.simps(2) Choice_prop_1_2 Choice_prop_1_4 Cons.prems(2) \<open>map (\<lambda>t. a ; Concat t) (x # xs) = a ; Concat x # map (\<lambda>t. a ; Concat t) xs\<close> choice_commute fold_choice_inv_1 fold_choice_prop5 map_is_Nil_conv)
  moreover have "... = (b \<union>\<^sub>p (a ; Concat x)) \<union>\<^sub>p \<Union>\<^sub>p [a ; Concat t. t \<leftarrow> (xs)]"
    by simp
  moreover have "... = (b \<union>\<^sub>p (a ; Concat x)) \<union>\<^sub>p a;\<Union>\<^sub>p [Concat t. t \<leftarrow> (xs)]"
    apply (cases "xs=[]") apply (auto simp: Fail_def composition_def choice_def restr_post_def restrict_r_def corestrict_r_def S_def) [1]
    by (simp add: Cons.IH Cons.prems(1))
  moreover have "... = b \<union>\<^sub>p a ; (Concat x \<union>\<^sub>p \<Union>\<^sub>p [Concat t. t \<leftarrow> (xs)])" using compose_distrib
    by auto
  moreover have "... = b \<union>\<^sub>p a ; (\<Union>\<^sub>p [Concat t. t \<leftarrow> (x # xs)])"
    by (metis (no_types, lifting) Choice.simps(2) Choice_prop_1_2 \<open>(b \<union>\<^sub>p a ; Concat x) \<union>\<^sub>p \<Union>\<^sub>p (map (\<lambda>t. a ; Concat t) xs) = (b \<union>\<^sub>p a ; Concat x) \<union>\<^sub>p a ; \<Union>\<^sub>p (map Concat xs)\<close> \<open>(b \<union>\<^sub>p a ; Concat x) \<union>\<^sub>p a ; \<Union>\<^sub>p (map Concat xs) = b \<union>\<^sub>p a ; (Concat x \<union>\<^sub>p \<Union>\<^sub>p (map Concat xs))\<close> \<open>b \<union>\<^sub>p (a ; Concat x \<union>\<^sub>p \<Union>\<^sub>p (map (\<lambda>t. a ; Concat t) xs)) = (b \<union>\<^sub>p a ; Concat x) \<union>\<^sub>p \<Union>\<^sub>p (map (\<lambda>t. a ; Concat t) xs)\<close> \<open>b \<union>\<^sub>p \<Union>\<^sub>p (map (\<lambda>t. a ; Concat t) (x # xs)) = b \<union>\<^sub>p (a ; Concat x \<union>\<^sub>p \<Union>\<^sub>p (map (\<lambda>t. a ; Concat t) xs))\<close> list.simps(9) map_is_Nil_conv)
  ultimately show "b \<union>\<^sub>p \<Union>\<^sub>p [a ; Concat t. t \<leftarrow> (x # xs)] = b \<union>\<^sub>p a ; \<Union>\<^sub>p [Concat t. t \<leftarrow> (x # xs)]"
    by argo
qed

theorem concur_recursive: "((a # xs) \<parallel> x) = a;(xs \<parallel> x) \<union>\<^sub>p Concat (x#a#xs)" \<comment> \<open>Concur_recursive\<close>
  apply (cases "xs=[]") apply (auto simp: non_atomic_conc_def) [1]
proof -
  assume a1: "xs \<noteq> []"
  have l1: "size xs > 0" using a1 by auto
  obtain b where o1: "b = Concat (x#a#xs)" by simp
  have "a;(xs \<parallel> x) = a;\<Union>\<^sub>p [Concat t. t \<leftarrow> insert_all x (xs)]"
    by (simp add: non_atomic_conc_def)

  have "((a # xs) \<parallel> x) = \<Union>\<^sub>p [Concat t. t \<leftarrow> insert_all x (a#xs)]"
    by (simp add: non_atomic_conc_def)

  have "[Concat t. t \<leftarrow> insert_all x (a#xs)] = Concat (x#a#xs)#[a;(Concat t). t \<leftarrow> insert_all x (xs)]"
    apply (auto simp:)
    by (metis Concat.simps(3) Concat_prop_1 append_is_Nil_conv l14 neq_Nil_conv)

  have "\<Union>\<^sub>p [Concat t. t \<leftarrow> insert_all x (a#xs)] = Concat (x#a#xs) \<union>\<^sub>p \<Union>\<^sub>p [a;(Concat t). t \<leftarrow> insert_all x (xs)]"
    using Choice_prop_1_2 \<open>map Concat (insert_all x (a # xs)) = Concat (x # a # xs) # map (\<lambda>t. a ; Concat t) (insert_all x xs)\<close> l1
    by (metis a1 insert_all.simps(2) list.discI map_is_Nil_conv permutations.elims)

  have "b \<union>\<^sub>p \<Union>\<^sub>p [a;(Concat t). t \<leftarrow> insert_all x (xs)] = b \<union>\<^sub>p a;\<Union>\<^sub>p [(Concat t). t \<leftarrow> insert_all x (xs)]"
    by (metis (no_types, lifting) Nil_is_append_conv a1 compose_distrib2 insert_all.simps(2) l10 list.distinct(1) map_eq_conv permutations.elims)

  show ?thesis
    using \<open>(a # xs \<parallel> x) = \<Union>\<^sub>p (map Concat (insert_all x (a # xs)))\<close> \<open>\<Union>\<^sub>p (map Concat (insert_all x (a # xs))) = Concat (x # a # xs) \<union>\<^sub>p \<Union>\<^sub>p (map (\<lambda>t. a ; Concat t) (insert_all x xs))\<close> \<open>a ; (xs \<parallel> x) = a ; \<Union>\<^sub>p (map Concat (insert_all x xs))\<close> \<open>b \<union>\<^sub>p \<Union>\<^sub>p (map (\<lambda>t. a ; Concat t) (insert_all x xs)) = b \<union>\<^sub>p a ; \<Union>\<^sub>p (map Concat (insert_all x xs))\<close> o1 by auto
qed

theorem non_atomic_conc_S: "S (xs\<parallel>x) = complete_state (x#xs)"
proof -
  have "\<And>t. t \<in> set (insert_all x xs) \<Longrightarrow> S (Concat t) = complete_state (x#xs)"
    by (metis Concat_state insert_perm_rel permutation_complete_state_equality)
  have "xs\<parallel>x = \<Union>\<^sub>p [Concat t. t \<leftarrow> (insert_all x xs)]"  by (auto simp: non_atomic_conc_def)
  moreover have "S (\<Union>\<^sub>p [Concat t. t \<leftarrow> (insert_all x xs)]) = \<Union> {S t | t . t \<in> set ([Concat t. t \<leftarrow> (insert_all x xs)])}"
    by (metis Choice_state)
  moreover have "... = \<Union> {t | t . t \<in> set ([S (Concat t). t \<leftarrow> (insert_all x xs)])}" by auto
  moreover have "... = \<Union> {t | t . t \<in> set ([complete_state (x#xs). t \<leftarrow> (insert_all x xs)])}" apply auto
    apply (simp add: \<open>\<And>t. t \<in> set (insert_all x xs) \<Longrightarrow> S (Concat t) = complete_state (x # xs)\<close>)
    by (metis Concat_state l2)
  moreover have "... = complete_state (x#xs)" apply auto
    by (metis concat.simps(1) concat_eq_Nil_conv l2 list.discI)
  ultimately show ?thesis
    by argo
qed

theorem concor_three_1: "[p\<^sub>1, p\<^sub>2] \<parallel> q = ((q;p\<^sub>1);p\<^sub>2 \<union>\<^sub>p ((p\<^sub>1;q);p\<^sub>2)) \<union>\<^sub>p ((p\<^sub>1;p\<^sub>2);q)" \<comment> \<open>Concor_three\<close>
  by (auto simp: non_atomic_conc_def)

lemma concor_three_2: "[p\<^sub>1, p\<^sub>2] \<parallel> q \<triangleq> ((q;p\<^sub>1);p\<^sub>2 \<union>\<^sub>p ((p\<^sub>1;q);p\<^sub>2)) \<union>\<^sub>p ((p\<^sub>1;p\<^sub>2);q)"
  by (simp add: equals_equiv_relation_1 concor_three_1)

lemma concor_three_3: "[p\<^sub>1, p\<^sub>2] \<parallel> q \<equiv>\<^sub>p ((q;p\<^sub>1);p\<^sub>2 \<union>\<^sub>p ((p\<^sub>1;q);p\<^sub>2)) \<union>\<^sub>p ((p\<^sub>1;p\<^sub>2);q)"
  by (simp add: equals_equiv_relation_3 concor_three_1)

theorem Concat_feasible: "all_feasible xs \<Longrightarrow> is_feasible (Concat xs)"
  apply (induction xs) apply auto
  apply (simp add: skip_is_feasible)
  by (metis Concat.simps(2) Concat.simps(3) Concat_prop_1 compose_feasible list.collapse)

theorem Choice_feasible: "all_feasible xs \<Longrightarrow> is_feasible (\<Union>\<^sub>p xs)"
  apply (induction xs) apply auto
  apply (simp add: fail_is_feasible)
  by (metis Choice.simps(2) Choice_prop_1_2 all_feasible.simps(1) all_feasible.simps(2) choice_feasible)

theorem all_feasible_prop: "all_feasible xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> is_feasible x"
  apply (induction xs arbitrary: x)
  by auto

theorem all_feasible_prop_1: "\<forall>x \<in> set xs. is_feasible x \<equiv> all_feasible xs"
  apply (induction xs)
  apply simp
  by auto

theorem all_feasible_prop_2: "xs \<in> set (permutations ys) \<Longrightarrow> all_feasible ys \<Longrightarrow> all_feasible xs"
  using all_feasible_prop_1 permutation_set_equality by blast

theorem non_atomic_conc_feasible_preserving: "all_feasible (x#xs) \<Longrightarrow> is_feasible (xs \<parallel> x)"
proof -
  assume a1: "all_feasible (x#xs)"
  have "xs \<parallel> x = \<Union>\<^sub>p (map Concat (insert_all x xs))" by (auto simp: non_atomic_conc_def)
  have "\<forall>x2 \<in> set (insert_all x xs). \<forall>x1 \<in> set x2. x1 \<in> set (x#xs)"
    by (metis insert_all_set_equality list.simps(15))
  have "\<forall>x1 \<in> set (x#xs). is_feasible x1" using a1 all_feasible_prop by auto
  have "\<forall>x2 \<in> set (insert_all x xs). \<forall>x1 \<in> set x2. x1 \<in> set (x#xs) \<and> is_feasible x1" using a1 apply auto
    apply (simp add: l13)
    using \<open>\<forall>x1\<in>set (x # xs). is_feasible x1\<close> \<open>\<forall>x2\<in>set (insert_all x xs). \<forall>x1\<in>set x2. x1 \<in> set (x # xs)\<close> by blast
  have "\<forall>x2 \<in> set (insert_all x xs). all_feasible x2" using a1 apply auto
    using \<open>\<forall>x2\<in>set (insert_all x xs). \<forall>x1\<in>set x2. x1 \<in> set (x # xs) \<and> is_feasible x1\<close> all_feasible_prop_1 by blast
  have "\<forall>x \<in> set (insert_all x xs). is_feasible (Concat x)"
    by (simp add: Concat_feasible \<open>\<forall>x2\<in>set (insert_all x xs). all_feasible x2\<close>)
  have "all_feasible (map Concat (insert_all x xs))"
    using \<open>\<forall>x\<in>set (insert_all x xs). is_feasible (Concat x)\<close> all_feasible_prop_1 by fastforce
  then have "is_feasible (\<Union>\<^sub>p (map Concat (insert_all x xs)))" using Choice_feasible
    by auto
  then show ?thesis
    by (simp add: \<open>(xs \<parallel> x) = \<Union>\<^sub>p (map Concat (insert_all x xs))\<close>)
qed

theorem atomic_conc_refinement_safe: "q\<^sub>1 \<sqsubseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<sqsubseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> q\<^sub>3 \<sqsubseteq>\<^sub>p p\<^sub>3 \<Longrightarrow> ([q\<^sub>1, q\<^sub>2] \<parallel> q\<^sub>3) \<sqsubseteq>\<^sub>p ([p\<^sub>1, p\<^sub>2] \<parallel> p\<^sub>3)"
  \<comment> \<open>\<close>
  oops \<comment> \<open>Is dependent on refinement safety of composition and choice\<close>

theorem "((ys@[x])@xs) \<parallel>\<^sub>G q \<equiv>\<^sub>p (ys@([x]@xs)) \<parallel>\<^sub>G q"
  by (simp add: equiv_is_reflexive)


theorem atomic_restrict_1: "(xs \<parallel> x) \<sslash>\<^sub>p C \<equiv>\<^sub>p  \<Union>\<^sub>p [Concat t \<sslash>\<^sub>p C. t \<leftarrow> insert_all x xs]"
proof -
  obtain xs' where o1: "xs' = map (Concat) (insert_all x xs)" by simp
  have l1: "\<Union>\<^sub>p [Concat t . t \<leftarrow> insert_all x xs]\<sslash>\<^sub>p C = \<Union>\<^sub>p xs'\<sslash>\<^sub>p C" using o1 by auto
  have l2: "\<Union>\<^sub>p [Concat t \<sslash>\<^sub>p C. t \<leftarrow> insert_all x xs] = \<Union>\<^sub>p [t \<sslash>\<^sub>p C. t \<leftarrow> xs']" using o1 apply auto
    by (metis comp_apply)
  have "\<Union>\<^sub>p [t \<sslash>\<^sub>p C. t \<leftarrow> xs'] \<equiv>\<^sub>p \<Union>\<^sub>p xs'\<sslash>\<^sub>p C" using Choice_prop_14 equiv_is_reflexive by auto
  then have "\<Union>\<^sub>p [Concat t . t \<leftarrow> insert_all x xs]\<sslash>\<^sub>p C \<equiv>\<^sub>p \<Union>\<^sub>p [Concat t \<sslash>\<^sub>p C. t \<leftarrow> insert_all x xs]"
    using equiv_is_symetric local.l2 o1 by auto
  then show ?thesis
    by (simp add: non_atomic_conc_def)
qed

theorem concur_restrict: "(xs \<parallel> x) \<sslash>\<^sub>p C =  \<Union>\<^sub>p [Concat t \<sslash>\<^sub>p C. t \<leftarrow> insert_all x xs]"
  oops


theorem atomic_corestrict_1: "(xs \<parallel> x) \<setminus>\<^sub>p C \<equiv>\<^sub>p  \<Union>\<^sub>p [Concat t \<setminus>\<^sub>p C. t \<leftarrow> insert_all x xs]"
proof -
  obtain xs' where o1: "xs' = map (Concat) (insert_all x xs)" by simp
  have l1: "\<Union>\<^sub>p [Concat t . t \<leftarrow> insert_all x xs]\<setminus>\<^sub>p C = \<Union>\<^sub>p xs'\<setminus>\<^sub>p C" using o1 by auto
  have l2: "\<Union>\<^sub>p [Concat t \<setminus>\<^sub>p C. t \<leftarrow> insert_all x xs] = \<Union>\<^sub>p [t \<setminus>\<^sub>p C. t \<leftarrow> xs']" using o1 apply auto
    by (metis comp_apply)
  have "\<Union>\<^sub>p [t \<setminus>\<^sub>p C. t \<leftarrow> xs'] \<equiv>\<^sub>p \<Union>\<^sub>p xs'\<setminus>\<^sub>p C" using Choice_prop_15 equiv_is_reflexive
    by (metis map_ident)
  then have "\<Union>\<^sub>p [Concat t . t \<leftarrow> insert_all x xs]\<setminus>\<^sub>p C \<equiv>\<^sub>p \<Union>\<^sub>p [Concat t \<setminus>\<^sub>p C. t \<leftarrow> insert_all x xs]"
    using equiv_is_symetric local.l2 o1 by auto
  then show ?thesis
    by (simp add: non_atomic_conc_def)
qed

theorem equiv_list_prop_2: "equiv_list xs ys \<Longrightarrow> \<Union>\<^sub>p xs \<equiv>\<^sub>p \<Union>\<^sub>p ys"
proof (induction "size xs" arbitrary: xs ys)
  case 0
  then show ?case apply auto
    by (metis Choice.simps(1) equiv_is_reflexive equiv_list.simps(3) list.exhaust) 
next
  case (Suc n)
  obtain x xs' where o1: "x#xs'=xs"
    by (metis Suc.hyps(2) Suc_length_conv)
  obtain y ys' where o2: "y#ys'=ys"
    by (metis Suc.prems equiv_list.simps(2) neq_Nil_conv o1)
  have "\<Union>\<^sub>p (x # xs') \<equiv>\<^sub>p x \<union>\<^sub>p \<Union>\<^sub>p (xs')"
    by (metis Choice.simps(1) Choice.simps(2) Choice_prop_1_2 equiv_is_symetric fail_choice_r inverse_equality_2)
  moreover have "... \<equiv>\<^sub>p x \<union>\<^sub>p \<Union>\<^sub>p ys'"
    by (metis Suc.hyps(1) Suc.hyps(2) Suc.prems Suc_inject equiv_is_reflexive equiv_list.simps(4) choice_equiv length_Cons o1 o2)
  moreover have "... \<equiv>\<^sub>p y \<union>\<^sub>p \<Union>\<^sub>p ys'"
    using Suc.prems equiv_is_reflexive equiv_list.simps(4) choice_equiv o1 o2 by blast
  moreover have "... \<equiv>\<^sub>p \<Union>\<^sub>p ys"
    by (metis Choice.simps(1) Choice.simps(2) Choice_prop_1_2 equiv_is_reflexive fail_choice_r o2)
  ultimately show ?case using equiv_is_transitive
    using o1 by blast
qed

theorem equiv_list_prop_1: "\<forall>a \<in> set xs. a \<noteq> [] \<Longrightarrow> equiv_list [Concat t \<sslash>\<^sub>p C. t \<leftarrow> xs] [Concat (hd t \<sslash>\<^sub>p C # tl t). t \<leftarrow> xs]"
proof (induction "size xs" arbitrary: xs)
  case 0
  then show ?case by auto
next
  case (Suc n)
  obtain x xs' where o1: "xs=x#xs'"
    by (meson Suc.hyps(2) Suc_length_conv)
  have "\<forall>a\<in>set xs'. a \<noteq> []"
    by (simp add: Suc.prems o1)
  have "x \<noteq> []"
    by (simp add: Suc.prems o1)
  have "size xs' = n"
    using Suc.hyps(2) o1 by auto
  have "equiv_list [Concat t \<sslash>\<^sub>p C . t \<leftarrow> xs'] [Concat (hd t \<sslash>\<^sub>p C # tl t). t \<leftarrow> xs']" using Suc(1) \<open>size xs' = n\<close> apply auto
    using \<open>\<forall>a\<in>set xs'. a \<noteq> []\<close> by auto
  have "Concat x \<sslash>\<^sub>p C \<equiv>\<^sub>p Concat (hd x \<sslash>\<^sub>p C # tl x)"
    by (simp add: Concat_prop_3 \<open>x \<noteq> []\<close>)
  then show ?case
    by (simp add: \<open>equiv_list (map (\<lambda>t. Concat t \<sslash>\<^sub>p C) xs') (map (\<lambda>t. Concat (hd t \<sslash>\<^sub>p C # tl t)) xs')\<close> o1)
qed


theorem equiv_list_prop_3: "\<forall>a \<in> set xs. a \<noteq> [] \<Longrightarrow> equiv_list [Concat t \<setminus>\<^sub>p C. t \<leftarrow> xs] [Concat (butlast t @ [(last t)\<setminus>\<^sub>p C]). t \<leftarrow> xs]"
proof (induction "size xs" arbitrary: xs)
  case 0
  then show ?case by auto
next
  case (Suc n)
  obtain x xs' where o1: "xs=x#xs'"
    by (meson Suc.hyps(2) Suc_length_conv)
  have "\<forall>a\<in>set xs'. a \<noteq> []"
    by (simp add: Suc.prems o1)
  have "x \<noteq> []"
    by (simp add: Suc.prems o1)
  have "size xs' = n"
    using Suc.hyps(2) o1 by auto
  have "equiv_list [Concat t \<setminus>\<^sub>p C . t \<leftarrow> xs'] [Concat (butlast t @ [(last t)\<setminus>\<^sub>p C]). t \<leftarrow> xs']" using Suc(1) \<open>size xs' = n\<close> apply auto
    using \<open>\<forall>a\<in>set xs'. a \<noteq> []\<close> by auto
  have "Concat x \<setminus>\<^sub>p C \<equiv>\<^sub>p Concat (butlast x @ [(last x)\<setminus>\<^sub>p C])"
    by (simp add: Concat_prop_4 \<open>x \<noteq> []\<close>)
  then show ?case
    by (simp add: \<open>equiv_list (map (\<lambda>t. Concat t \<setminus>\<^sub>p C) xs') (map (\<lambda>t. Concat (butlast t @ [last t \<setminus>\<^sub>p C])) xs')\<close> o1)
qed

theorem concur_restrict: "(xs \<parallel> x) \<sslash>\<^sub>p C \<equiv>\<^sub>p  \<Union>\<^sub>p [Concat (hd t\<sslash>\<^sub>pC#tl t). t \<leftarrow> insert_all x xs]" \<comment> \<open>Concur_restrict\<close>
proof -
  have l1: "(xs \<parallel> x) \<sslash>\<^sub>p C \<equiv>\<^sub>p \<Union>\<^sub>p [Concat t \<sslash>\<^sub>p C. t \<leftarrow> insert_all x xs]" using atomic_restrict_1 by auto
  obtain xs' where o1: "xs' = insert_all x xs" by simp
  have l2: "xs' \<noteq> []" using o1
    by (metis member_rec(2) orig_is_permutation_1)
  have l3: "\<forall>x \<in> set (xs'). x \<noteq> []"
    using empty_iff empty_set l11 o1 by fastforce
  have l5: "equiv_list [Concat t \<sslash>\<^sub>p C. t \<leftarrow> xs'] [Concat (hd t \<sslash>\<^sub>p C # tl t). t \<leftarrow> xs']" using equiv_list_prop_1 l3 by auto
  have "\<Union>\<^sub>p [Concat t \<sslash>\<^sub>p C. t \<leftarrow> xs'] \<equiv>\<^sub>p \<Union>\<^sub>p [Concat (hd t \<sslash>\<^sub>p C # tl t). t \<leftarrow> xs']" using Concat_prop_3 l3 equiv_list_prop_2
    using local.l5 by fastforce
  have "... \<equiv>\<^sub>p \<Union>\<^sub>p [Concat (hd t\<sslash>\<^sub>pC#tl t). t \<leftarrow> insert_all x xs]" using Concat_prop_3
    by (simp add: equiv_is_reflexive o1)
  show ?thesis
    using \<open>\<Union>\<^sub>p (map (\<lambda>t. Concat t \<sslash>\<^sub>p C) xs') \<equiv>\<^sub>p \<Union>\<^sub>p (map (\<lambda>t. Concat (hd t \<sslash>\<^sub>p C # tl t)) xs')\<close> equiv_is_transitive local.l1 o1 by auto
qed

theorem concur_corestrict: "(xs \<parallel> x) \<setminus>\<^sub>p C \<equiv>\<^sub>p  \<Union>\<^sub>p [Concat (butlast t @ [(last t)\<setminus>\<^sub>p C]). t \<leftarrow> insert_all x xs]" \<comment> \<open>Concur_corestrict\<close>
proof -
  have l1: "(xs \<parallel> x) \<setminus>\<^sub>p C \<equiv>\<^sub>p \<Union>\<^sub>p [Concat t \<setminus>\<^sub>p C. t \<leftarrow> insert_all x xs]" using atomic_corestrict_1 by auto
  obtain xs' where o1: "xs' = insert_all x xs" by simp
  have l2: "xs' \<noteq> []" using o1
    by (metis member_rec(2) orig_is_permutation_1)
  have l3: "\<forall>x \<in> set (xs'). x \<noteq> []"
    using empty_iff empty_set l11 o1 by fastforce
  have l5: "equiv_list [Concat t \<setminus>\<^sub>p C. t \<leftarrow> xs'] [Concat (butlast t @ [(last t)\<setminus>\<^sub>p C]). t \<leftarrow> xs']" using equiv_list_prop_3 l3 by auto
  have "\<Union>\<^sub>p [Concat t \<setminus>\<^sub>p C. t \<leftarrow> xs'] \<equiv>\<^sub>p \<Union>\<^sub>p [Concat (butlast t @ [(last t)\<setminus>\<^sub>p C]). t \<leftarrow> xs']" using Concat_prop_3 l3 equiv_list_prop_2
    using local.l5 by fastforce
  have "... \<equiv>\<^sub>p \<Union>\<^sub>p [Concat (butlast t @ [(last t)\<setminus>\<^sub>p C]). t \<leftarrow> insert_all x xs]" using Concat_prop_3
    by (simp add: equiv_is_reflexive o1)
  show ?thesis
    using \<open>\<Union>\<^sub>p (map (\<lambda>t. Concat t \<setminus>\<^sub>p C) xs') \<equiv>\<^sub>p \<Union>\<^sub>p (map (\<lambda>t. Concat (butlast t @ [last t \<setminus>\<^sub>p C])) xs')\<close> equiv_is_transitive local.l1 o1 by auto
qed

theorem concur_specialize1: "p ; q \<subseteq>\<^sub>p ([p] \<parallel> q)" \<comment> \<open>Concur_specialize1\<close>
  apply (auto simp: non_atomic_conc_def)
  by (simp add: program_is_specialize_of_choice)

theorem non_atomic_specialize: "ys \<in> set (insert_all x xs) \<Longrightarrow> (Concat ys) \<subseteq>\<^sub>p (xs \<parallel> x)"
  apply (cases "xs = []") apply (auto simp: non_atomic_conc_def specialize_is_reflexive) [1]
  apply (cases "size xs = 1")
proof -
  assume a0: "length xs = 1"
  assume a1: "ys \<in> set (insert_all x xs)"
  obtain x' where o1: "xs = [x']" using a0 apply auto by (metis Suc_length_conv length_0_conv)
  have l1: "xs \<parallel> x = x;x' \<union>\<^sub>p x';x" by (auto simp: o1 non_atomic_conc_def)
  have l2: "(Concat ys = x;x') \<or> (Concat ys = x';x)" using a1 o1 by auto
  show ?thesis
    by (metis choice_commute local.l1 local.l2 program_is_specialize_of_choice)
next
  obtain xs' where o1: "xs' = insert_all x xs" by simp
  obtain xs'' where o2: "xs'' = [Concat t. t \<leftarrow> xs']" by simp
  assume a1: "ys \<in> set (insert_all x xs)"
  assume a2: "xs \<noteq> []"
  assume a3: "length xs \<noteq> 1"
  have l0: "size xs'' > 1" using a2 a3 apply (auto simp: o2 o1)
    by (metis Suc_eq_plus1 Suc_lessI a1 add_right_cancel length_0_conv length_pos_if_in_set perm_prop4)
  have l1: "xs \<parallel> x = \<Union>\<^sub>p [Concat t. t \<leftarrow> insert_all x xs]"
    by (simp add: non_atomic_conc_def)
  have l2: "Concat ys \<in> set [Concat t. t \<leftarrow> insert_all x xs]"
    by (simp add: a1)
  have l3: "Concat ys \<in> set xs''"
    using local.l2 o1 o2 by auto
  have "\<Union>\<^sub>p xs'' = \<Union>\<^sub>p xs'' \<union>\<^sub>p Concat ys" using l1 l2 Choice_prop_17 l0 apply auto
    using local.l3 by fastforce
  have "Concat ys \<subseteq>\<^sub>p \<Union>\<^sub>p [Concat t. t \<leftarrow> insert_all x xs] \<union>\<^sub>p Concat ys"
    by (simp add: program_is_specialize_of_choice)
  show ?thesis
    using \<open>Concat ys \<subseteq>\<^sub>p \<Union>\<^sub>p (map Concat (insert_all x xs)) \<union>\<^sub>p Concat ys\<close> \<open>\<Union>\<^sub>p xs'' = \<Union>\<^sub>p xs'' \<union>\<^sub>p Concat ys\<close> local.l1 o1 o2 by argo
qed

theorem commute_compose: "commute_programs3 a b \<Longrightarrow> [a] \<parallel> b \<equiv>\<^sub>p a;b" \<comment> \<open>Commute_compose\<close>
  by (auto simp: commute_programs3_def non_atomic_conc_def equiv_def composition_def corestrict_r_def choice_def restr_post_def restrict_r_def)

theorem concur_distrib1: "xs\<parallel>(b \<union>\<^sub>p c) \<equiv>\<^sub>p (xs\<parallel>b) \<union>\<^sub>p (xs\<parallel>c)"
proof (induction xs arbitrary: b c)
  case Nil
  then show ?case by (auto simp: non_atomic_conc_def equiv_is_reflexive)
next
  case (Cons a xs)
  have "a # xs \<parallel> b \<union>\<^sub>p c \<equiv>\<^sub>p Concat (b \<union>\<^sub>p c # a # xs) \<union>\<^sub>p a ; (xs \<parallel> b \<union>\<^sub>p c)"
    using non_atomic_prop2 by auto
  moreover have "... \<equiv>\<^sub>p Concat (b \<union>\<^sub>p c # a # xs) \<union>\<^sub>p a ; ((xs \<parallel> b) \<union>\<^sub>p (xs \<parallel> c))"
    by (meson equals_equiv_relation_3 choice_equiv composition_equiv local.Cons)
  moreover have "... \<equiv>\<^sub>p (Concat (b # a # xs) \<union>\<^sub>p Concat (c # a # xs)) \<union>\<^sub>p a ; ((xs \<parallel> b) \<union>\<^sub>p (xs \<parallel> c))"
    by (metis Concat.simps(3) Concat_prop_1 compose_distrib2_3 equals_equiv_relation_3 choice_equiv list.distinct(1))
  moreover have "... \<equiv>\<^sub>p (Concat (b # a # xs) \<union>\<^sub>p a ; (xs \<parallel> b)) \<union>\<^sub>p (Concat (c # a # xs) \<union>\<^sub>p a ; (xs \<parallel> c))"
    by (smt (verit, del_insts) choice_assoc_1 choice_commute choice_commute_3 compose_distrib1_3 choice_equiv)
  moreover have "... \<equiv>\<^sub>p (a # xs \<parallel> b) \<union>\<^sub>p (a # xs \<parallel> c)"
    by (metis choice_commute equiv_is_symetric choice_equiv non_atomic_prop2)
  ultimately show "a # xs \<parallel> b \<union>\<^sub>p c \<equiv>\<^sub>p (a # xs \<parallel> b) \<union>\<^sub>p (a # xs \<parallel> c)" using equiv_is_transitive by blast
qed

theorem concur_choice1: "[a\<union>\<^sub>pb]\<parallel>(c) = ([a]\<parallel>c) \<union>\<^sub>p ([b]\<parallel>c)" \<comment> \<open>concur_choice1\<close>
  apply (auto simp: non_atomic_conc_def)
  by (metis choice_assoc_1 choice_commute compose_distrib compose_distrib2_1)

theorem concur_choice2: "xs\<parallel>(b \<union>\<^sub>p c) = (xs\<parallel>b) \<union>\<^sub>p (xs\<parallel>c)" \<comment> \<open>Concur_choice2\<close>
proof (induction xs arbitrary: b c)
  case Nil
  then show ?case by (auto simp: non_atomic_conc_def equiv_is_reflexive)
next
  case (Cons a xs)
  have "a # xs \<parallel> b \<union>\<^sub>p c = Concat (b \<union>\<^sub>p c # a # xs) \<union>\<^sub>p a ; (xs \<parallel> b \<union>\<^sub>p c)"
    using concur_recursive by auto
  moreover have "... = Concat (b \<union>\<^sub>p c # a # xs) \<union>\<^sub>p a ; ((xs \<parallel> b) \<union>\<^sub>p (xs \<parallel> c))"
    by (simp add: local.Cons)
  moreover have "... = (Concat (b # a # xs) \<union>\<^sub>p Concat (c # a # xs)) \<union>\<^sub>p a ; ((xs \<parallel> b) \<union>\<^sub>p (xs \<parallel> c))"
    by (metis Concat_prop_6)
  moreover have "... = (Concat (b # a # xs) \<union>\<^sub>p a ; (xs \<parallel> b)) \<union>\<^sub>p (Concat (c # a # xs) \<union>\<^sub>p a ; (xs \<parallel> c))"
    by (smt (verit, ccfv_SIG) choice_assoc_1 choice_commute compose_distrib)
  moreover have "... = (a # xs \<parallel> b) \<union>\<^sub>p (a # xs \<parallel> c)"
    by (simp add: concur_recursive)
  ultimately show "a # xs \<parallel> b \<union>\<^sub>p c = (a # xs \<parallel> b) \<union>\<^sub>p (a # xs \<parallel> c)"
    by argo
qed

theorem concur_specialize2: "([Concat xs] \<parallel> x) \<subseteq>\<^sub>p (xs \<parallel> x)" \<comment> \<open>Concur_specialize2\<close>
proof (cases "xs=[]")
  case True
  then show ?thesis by (auto simp: non_atomic_conc_def specialize_def extends_def weakens_def strengthens_def Skip_def S_def composition_def corestrict_r_def choice_def Field_def restr_post_def restrict_r_def)
next
  case False
  have "[Concat xs] \<parallel> x = x ; (Concat xs) \<union>\<^sub>p (Concat xs) ; x"
    by (simp add: concur_two)
  have "... = (Concat (x#xs)) \<union>\<^sub>p (Concat (xs@[x]))"
    by (simp add: Concat_prop_10 Concat_prop_2 False)
  have "x#xs \<in> set (insert_all x xs)"
    by (simp add: l2)
  have "xs@[x] \<in> set (insert_all x xs)"
    by (simp add: l3)
  then have "Concat (xs@[x]) \<subseteq>\<^sub>p (xs \<parallel> x)"
    by (simp add: non_atomic_specialize)
  show ?thesis using choice_suprogram_prop
    by (metis \<open>([Concat xs] \<parallel> x) = x ; Concat xs \<union>\<^sub>p Concat xs ; x\<close> \<open>Concat (xs @ [x]) \<subseteq>\<^sub>p (xs \<parallel> x)\<close> \<open>x # xs \<in> set (insert_all x xs)\<close> \<open>x ; Concat xs \<union>\<^sub>p Concat xs ; x = Concat (x # xs) \<union>\<^sub>p Concat (xs @ [x])\<close> non_atomic_specialize)
qed

end