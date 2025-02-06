theory Big_choice
  imports 
"../T_03_Basic_programs" "Permutations"
begin
section \<open>Big choice for top\<close>

theorem fold_compose: "foldl (;) (a ; b) xs = a ; (foldl (;) b xs)"
proof (induction "size xs" arbitrary: xs a b)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
  proof (cases "size xs = 1")
    case True
    obtain x where o1: "xs = [x]" using True
      by (metis Suc.hyps(2) diff_Suc_1 diff_is_0_eq' le_numeral_extra(4) length_0_conv length_Suc_conv)
    have "foldl (;) (a ; b) [x] = a ; foldl (;) b [x]"
      by simp
    then show "foldl (;) (a ; b) xs = a ; foldl (;) b xs" using o1
      by simp
  next
    case False
    obtain x xs' where o1: "xs = x#xs'" using False
      by (metis Suc.hyps(2) length_Suc_conv)
    have "foldl (;) (a ; b) (x#xs') = a ; foldl (;) b (x#xs')"
      using Suc.hyps(1) Suc.hyps(2) o1 by auto 
    then show "foldl (;) (a ; b) xs = a ; foldl (;) b xs"
      by (simp add: o1)
  qed
qed

theorem fold_choice: "foldl (\<union>\<^sub>p) (a \<union>\<^sub>p b) xs = a \<union>\<^sub>p (foldl (\<union>\<^sub>p) b xs)"
proof (induction "size xs" arbitrary: xs a b)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
  proof (cases "size xs = 1")
    case True
    obtain x where o1: "xs = [x]" using True
      by (metis Suc.hyps(2) diff_Suc_1 diff_is_0_eq' le_numeral_extra(4) length_0_conv length_Suc_conv)
    have "foldl (\<union>\<^sub>p) (a \<union>\<^sub>p b) [x] = a \<union>\<^sub>p foldl (\<union>\<^sub>p) b [x]"
      using choice_assoc_1 by auto
    then show "foldl (\<union>\<^sub>p) (a \<union>\<^sub>p b) xs = a \<union>\<^sub>p foldl (\<union>\<^sub>p) b xs" using o1
      by simp
  next
    case False
    obtain x xs' where o1: "xs = x#xs'" using False
      by (metis Suc.hyps(2) length_Suc_conv)
    have "foldl (\<union>\<^sub>p) (a \<union>\<^sub>p b) (x#xs') = a \<union>\<^sub>p foldl (\<union>\<^sub>p) b (x#xs')"
      by (metis Suc.hyps(1) Suc.hyps(2) Suc_inject choice_assoc_1 foldl_Cons length_Cons o1)
    then show "foldl (\<union>\<^sub>p) (a \<union>\<^sub>p b) xs = a \<union>\<^sub>p foldl (\<union>\<^sub>p) b xs"
      by (simp add: o1)
  qed
qed

theorem Choice_prop_1_2: "xs \<noteq> [] \<Longrightarrow> \<Union>\<^sub>p (x#xs) = x \<union>\<^sub>p \<Union>\<^sub>p xs"
proof (induction "size xs" arbitrary: xs x)
  case 0
  then show ?case by simp
next
  case (Suc n)
  assume a1: "xs \<noteq> []"
  obtain x' xs' where o1: "xs=x'#xs'" using a1
    using list.exhaust by auto
  then have "\<Union>\<^sub>p (x#xs) = foldl (\<union>\<^sub>p) x xs" by simp
  
  have "... = foldl (\<union>\<^sub>p) (x \<union>\<^sub>p x') xs'" using o1 by auto
  
  have "... = x \<union>\<^sub>p foldl (\<union>\<^sub>p) (x') xs'"
    by (meson fold_choice)
  show ?case
    by (metis Choice.simps(2) Choice.simps(3) \<open>foldl (\<union>\<^sub>p) (x \<union>\<^sub>p x') xs' = x \<union>\<^sub>p foldl (\<union>\<^sub>p) x' xs'\<close> \<open>foldl (\<union>\<^sub>p) x xs = foldl (\<union>\<^sub>p) (x \<union>\<^sub>p x') xs'\<close> foldl_Nil o1 permutations.elims)
qed

theorem Choice_prop_1_3: "a@b \<noteq> [] \<Longrightarrow> \<Union>\<^sub>p (a@x#b) = x \<union>\<^sub>p \<Union>\<^sub>p (a@b)"
  apply (induction a arbitrary: x b) apply auto
  apply (simp add: Choice_prop_1_2)
  by (smt (verit) Choice.simps(2) Choice_prop_1_2 append_Nil2 append_eq_append_conv2 append_is_Nil_conv choice_assoc_1 choice_commute list.distinct(1) self_append_conv2)

theorem Choice_prop_1_1: "ys \<in> set (permutations xs) \<Longrightarrow> \<Union>\<^sub>p xs = \<Union>\<^sub>p ys"
  apply (cases "size xs=0") apply simp
  apply (cases "size xs=1") apply (metis One_nat_def length_0_conv length_Suc_conv perm_inv_3 singleton_permutation)
proof (induction "size xs" arbitrary: xs ys rule: less_induct)
  case less
  obtain x' xs' where "xs=x'#xs'"
    by (metis length_0_conv less.prems(2) permutations.elims)
  have l1: "\<Union>\<^sub>p xs = x' \<union>\<^sub>p \<Union>\<^sub>p xs'"
    using Choice_prop_1_2 \<open>xs = x' # xs'\<close> less.prems(3) by fastforce
  have l2: "... = x' \<union>\<^sub>p \<Union>\<^sub>p xs'"
    by simp
  have l3: "size ys > 0" using length_inv less.prems(1) less.prems(2) by fastforce
  then show ?case
  proof (cases "size xs' = 1")
    case True
    obtain x\<^sub>2 where o2: "xs'=[x\<^sub>2]" using True
      by (metis Suc_le_length_iff diff_Suc_1' le_numeral_extra(4) length_0_conv length_Cons nat_1 nat_one_as_int)
    have l4: "xs = [x',x\<^sub>2]"
      by (simp add: \<open>xs = x' # xs'\<close> o2)
    have l5: "[x',x\<^sub>2] = ys \<or> [x\<^sub>2,x'] = ys" using less l4 by auto
    then show ?thesis
      using local.l1 o2 by auto
  next
    case False
    obtain x'' where o2: "\<exists>t. x'#x''#t = xs"
      by (metis \<open>xs = x' # xs'\<close> gen_length_code(1) gen_length_def length_Cons less.prems(3) neq_Nil_conv plus_1_eq_Suc)
    obtain y\<^sub>s y\<^sub>e where o2: "ys=y\<^sub>s@x'#y\<^sub>e"
      by (metis \<open>xs = x' # xs'\<close> less.prems(1) permutation_split_set)
    have l6: "xs' \<in> set (permutations (y\<^sub>s@y\<^sub>e))"
      by (metis \<open>xs = x' # xs'\<close> less.prems(1) o2 perm_inv_3 perm_split)
    have l7: "\<Union>\<^sub>p xs' = \<Union>\<^sub>p (y\<^sub>s@y\<^sub>e)" using less(1) less(2) False l6 apply auto
      by (metis One_nat_def \<open>xs = x' # xs'\<close> length_Cons length_inv less.prems(3) lessI list.size(3))
    have l8: "\<Union>\<^sub>p (y\<^sub>s @ y\<^sub>e) \<union>\<^sub>p x' = \<Union>\<^sub>p ys"
      by (metis Choice_prop_1_3 Nil_is_append_conv \<open>xs = x' # xs'\<close> append_self_conv2 choice_commute length_0_conv length_inv local.l1 local.l6 o2)
    then show ?thesis
      by (simp add: local.l1 local.l7)
  qed
qed

lemma Choice_prop_1: "xs \<noteq> [] \<Longrightarrow> \<Union>\<^sub>p (xs@[x]) = x \<union>\<^sub>p \<Union>\<^sub>p xs"
  by (simp add: Choice_prop_1_3)

theorem Choice_prop_1_4: "xs \<noteq> [] \<Longrightarrow> foldl (\<union>\<^sub>p) x xs = x \<union>\<^sub>p Choice xs"
proof -
  assume a1: "xs \<noteq> []"
  obtain x' xs' where o1: "xs=x'#xs'" using a1
    using list.exhaust by auto
  have "Choice xs = foldl (\<union>\<^sub>p) x' xs'"
    by (metis Choice.simps(2) Choice.simps(3) foldl_Nil hd_Cons_tl o1)
  have "x \<union>\<^sub>p Choice xs = x \<union>\<^sub>p foldl (\<union>\<^sub>p) x' xs'"
    by (simp add: \<open>\<Union>\<^sub>p xs = foldl (\<union>\<^sub>p) x' xs'\<close>)
  have "... =  foldl (\<union>\<^sub>p) x xs"
    by (metis choice_assoc_1 foldl_Cons o1 simp_2)
  show ?thesis
    by (simp add: \<open>x \<union>\<^sub>p \<Union>\<^sub>p xs = x \<union>\<^sub>p foldl (\<union>\<^sub>p) x' xs'\<close> \<open>x \<union>\<^sub>p foldl (\<union>\<^sub>p) x' xs' = foldl (\<union>\<^sub>p) x xs\<close>)
qed

theorem Choice_prop_2: "\<Union>\<^sub>p [a;t. t \<leftarrow> xs] \<equiv>\<^sub>p a;\<Union>\<^sub>p [t. t \<leftarrow> xs]"
  apply (cases "xs = []") apply (auto simp: composition_def equiv_def Fail_def corestrict_r_def restr_post_def restrict_r_def) [1]
proof (cases "size xs = 1")
  case True
  obtain x where o1: "xs = [x]" using True
    by (metis One_nat_def Suc_length_conv length_0_conv)
  have "[a;t. t \<leftarrow> xs] = [a;x]" by (simp add: o1)
  have "\<Union>\<^sub>p [t. t \<leftarrow> xs] = x"
    by (simp add: o1)
  then show "\<Union>\<^sub>p [a;t. t \<leftarrow> xs] \<equiv>\<^sub>p a;\<Union>\<^sub>p [t. t \<leftarrow> xs]"
    by (simp add: \<open>map ((;) a) xs = [a ; x]\<close> equiv_is_reflexive) 
next
  case False
  then show ?thesis
proof (induction "size xs" arbitrary: a xs)
  case 0
  then show ?case by (auto simp: equiv_def Fail_def composition_def corestrict_r_def restr_post_def restrict_r_def)
next
  case (Suc n)
  assume IH: "\<And>xs' a'. n = length xs' \<Longrightarrow> length  xs' \<noteq> 1 \<Longrightarrow> \<Union>\<^sub>p (map ((;) a') xs') \<equiv>\<^sub>p a' ; \<Union>\<^sub>p (map (\<lambda>t. t) xs')"
  assume a1: "Suc n = length xs"
  have a2: "xs \<noteq> []" using a1 by auto
  assume a3: "length xs \<noteq> 1"
  obtain x' xs' where o1: "xs=x'#xs'"
    by (metis Nitpick.size_list_simp(2) Zero_not_Suc a1 neq_Nil_conv)
  have l0: "length xs' = n"
    using a1 o1 by auto
  have "\<Union>\<^sub>p (map ((;) a) xs) = \<Union>\<^sub>p (map ((;) a) (x'#xs'))" using o1 by simp
  moreover have "... = a;x' \<union>\<^sub>p \<Union>\<^sub>p (map ((;) a) (xs'))" apply auto
    by (metis Choice_prop_1_2 One_nat_def Suc.prems a1 l0 length_map list.size(3))
  moreover have "... \<equiv>\<^sub>p a;x' \<union>\<^sub>p a ; \<Union>\<^sub>p (map (\<lambda>t. t) xs')" using IH o1 l0
    using Suc.hyps(1) equiv_is_reflexive choice_equiv
    by (smt (verit, ccfv_threshold) Choice.simps(2) One_nat_def length_0_conv length_Suc_conv_rev list.simps(8) list.simps(9) self_append_conv2)
  moreover have "... \<equiv>\<^sub>p a;(x' \<union>\<^sub>p \<Union>\<^sub>p (map (\<lambda>t. t) xs'))"
    by (simp add: compose_distrib1_3 equiv_is_symetric)
  moreover have "... = a ; \<Union>\<^sub>p (map (\<lambda>t. t) xs)" apply auto
    using Choice_prop_1_2 a3 o1 by fastforce
  ultimately show "\<Union>\<^sub>p (map ((;) a) xs) \<equiv>\<^sub>p a ; \<Union>\<^sub>p (map (\<lambda>t. t) xs)"
    using equiv_is_transitive by auto
qed
qed

theorem Choice_prop_3: "xs \<noteq> [] \<Longrightarrow> \<Union>\<^sub>p (xs@[x]) = \<Union>\<^sub>p (xs) \<union>\<^sub>p x"
  by (simp add: Choice_prop_1)

theorem Choice_prop_4: "\<Union>\<^sub>p [t;a. t \<leftarrow> xs] \<equiv>\<^sub>p \<Union>\<^sub>p [t. t \<leftarrow> xs];a"
  apply (cases "size xs = 0") apply auto apply (metis compose_empty_2 special_empty1 fail_equiv skip_prop_9)
proof (cases "size xs = 1")
  case True
  obtain x where o1: "xs = [x]" using True
    by (metis One_nat_def Suc_length_conv length_0_conv)
  have "\<Union>\<^sub>p (map (\<lambda>t. t ; a) [x]) \<equiv>\<^sub>p \<Union>\<^sub>p [x] ; a"
    by (simp add: equals_equiv_relation_3)
  then show "\<Union>\<^sub>p (map (\<lambda>t. t ; a) xs) \<equiv>\<^sub>p \<Union>\<^sub>p xs ; a"
    by (simp add: o1)
next
  case False
  assume a1_1: "length xs \<noteq> 1"
  then show "\<Union>\<^sub>p (map (\<lambda>t. t ; a) xs) \<equiv>\<^sub>p \<Union>\<^sub>p xs ; a"
proof (induction "size xs" arbitrary: a xs)
  case 0
  then show ?case by (auto simp: equiv_def Fail_def composition_def corestrict_r_def restr_post_def restrict_r_def)
next
  case (Suc n)
  assume IH: "\<And>xs' a'. n = length xs'\<Longrightarrow> length xs' \<noteq> 1 \<Longrightarrow> \<Union>\<^sub>p (map (\<lambda>t. t ; a') xs') \<equiv>\<^sub>p \<Union>\<^sub>p xs' ; a'"
  assume a1: "Suc n = length xs"
  assume a2: "length xs \<noteq> 1"
  show ?case
  proof (cases "n=1")
    case True
    obtain a b where o1: "xs = [a,b]"
      by (metis (no_types, opaque_lifting) Nitpick.size_list_simp(2) One_nat_def True a1 diff_Suc_1' distinct_adj_conv_length_remdups_adj distinct_adj_conv_nth empty_replicate list.collapse not_add_less1 plus_1_eq_Suc remdups_adj_singleton_iff replicate_Suc)
    then show ?thesis apply (simp add: o1)
      by (metis compose_distrib2_1 compose_distrib2_3)
  next
    case False
    have l1: "n>1"
      using False a1 a2 by linarith
    then show ?thesis
proof -
  have a3: "xs \<noteq> []" using a1 by auto
  obtain x' xs' where o1: "xs=xs'@[x']"
    by (metis a1 length_Suc_conv_rev)
  have a4: "xs' \<noteq> []" using a2 o1 by force
  have l0: "length xs' = n" using a1 o1 by auto
  have l1: "length xs' \<noteq> 1" using False l0 by auto
  have l2: "\<Union>\<^sub>p (map (\<lambda>t. t ; a) xs) = \<Union>\<^sub>p (map (\<lambda>t. t ; a) (xs'@[x']))" using o1 by simp
  have l3: "... = \<Union>\<^sub>p (map (\<lambda>t. t ; a) (xs')) \<union>\<^sub>p x';a"
    by (simp add: Choice_prop_3 a4)
  have l4: "\<Union>\<^sub>p (map (\<lambda>t. t ; a) xs) = \<Union>\<^sub>p (map (\<lambda>t. t ; a) (xs')) \<union>\<^sub>p x';a"
    using local.l2 local.l3 by auto
  have l5: "\<Union>\<^sub>p (map (\<lambda>t. t ; a) xs') \<equiv>\<^sub>p \<Union>\<^sub>p xs' ; a" using a4 l0 IH l1 apply simp
    using False Suc.hyps(1) by presburger
  have l6: "\<Union>\<^sub>p (map (\<lambda>t. t ; a) xs) \<equiv>\<^sub>p \<Union>\<^sub>p xs' ; a \<union>\<^sub>p x';a" apply (simp add: l4) using l5
    by (simp add: equals_equiv_relation_3 choice_equiv)
  show "\<Union>\<^sub>p (map (\<lambda>t. t ; a) xs) \<equiv>\<^sub>p \<Union>\<^sub>p xs ; a"
    by (metis Choice_prop_3 a4 compose_distrib2_1 local.l6 o1)
qed
qed
qed
qed

theorem Choice_state: "S (\<Union>\<^sub>p (xs)) = \<Union> {S x | x . x \<in> set xs}"
proof (induction "size xs" arbitrary: xs)
  case 0
  then show ?case by (auto simp: Fail_def S_def)
next
  case (Suc n)
  obtain x' xs' where o1: "xs=x'#xs'" using Suc
    by (meson Suc_length_conv)
  have l1: "S (\<Union>\<^sub>p xs') = \<Union> {S x |x. x \<in> set xs'}"
    using Suc.hyps(1) Suc.hyps(2) o1 by auto
  have l2: "S (\<Union>\<^sub>p xs) = S (\<Union>\<^sub>p xs') \<union> S x'"
    apply (cases "xs'=[]")
    apply (metis Choice.simps(1) Choice.simps(2) compose_empty_2 empty_subsetI o1 skip_is_idempondent_composition skip_prop_9 sup_absorb2)
    by (simp add: Choice_prop_1_2 o1 sup_commute)
  have l3: "... = \<Union> {S x |x. x \<in> set xs'} \<union> (S x')"
    by (simp add: local.l1)
  have l4: "... = \<Union> {S x |x. x \<in> set xs}" using o1 by auto
  then show "S (\<Union>\<^sub>p xs) = \<Union> {S x |x. x \<in> set xs}"
    by (simp add: local.l2 local.l3)
qed

theorem Union_prop_1: "xs \<noteq> {} \<Longrightarrow> \<Union> {t | x . x \<in> xs} = t"
  by (auto)

theorem Choice_prop_5: "size xs = 1 \<Longrightarrow> set (xs) = {x} \<Longrightarrow> (\<Union>\<^sub>p xs = x)"
  by (metis Choice.simps(2) impossible_Cons insert_not_empty length_0_conv less_one linorder_le_less_linear list.set_intros(1) neq_Nil_conv set_empty singletonD)

theorem Choice_prop_6: "size xs > 1 \<Longrightarrow> set (xs) = {x} \<Longrightarrow> (\<Union>\<^sub>p xs = x \<union>\<^sub>p x)"
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "xs\<noteq>[]"
    using Cons.prems(1) by auto
  then show ?case
  proof (cases "size xs=1")
    case True
    then show ?thesis
    by (metis (no_types, lifting) Choice_prop_1_2 Choice_prop_5 Cons.prems(2) \<open>xs \<noteq> []\<close> insert_absorb insert_eq_iff insert_not_empty list.simps(15) set_ConsD set_empty)
  next
    case False
    then show ?thesis
      apply (cases "a=x")
      apply (metis Choice_prop_1_2 Cons.IH Cons.prems(2) \<open>xs \<noteq> []\<close> choice_idem_2 insert_absorb last_ConsR last_in_set length_0_conv less_one linorder_less_linear list.discI list.simps(15) singletonD)
      using Cons.prems(2) by auto
  qed
qed

theorem Choice_prop_7: "a \<noteq> [] \<Longrightarrow> b \<noteq> [] \<Longrightarrow> \<Union>\<^sub>p a \<union>\<^sub>p \<Union>\<^sub>p b = \<Union>\<^sub>p (a@b)"
  apply (induction a arbitrary: b) apply auto
  by (smt (verit, ccfv_SIG) Choice.simps(2) Choice_prop_1_2 append_is_Nil_conv choice_assoc_1 choice_commute self_append_conv2)

theorem Choice_prop_8: "\<exists>x \<in> set xs. p x \<Longrightarrow> \<exists>x \<in> set xs. \<not>p x \<Longrightarrow> \<Union>\<^sub>p (filter (\<lambda>x. p x) xs) \<union>\<^sub>p \<Union>\<^sub>p (filter (\<lambda>x. \<not>p x) xs) = \<Union>\<^sub>p xs"
proof -
  assume a1: "\<exists>x \<in> set xs. p x" and "\<exists>x \<in> set xs. \<not>p x"
  have "(filter (\<lambda>x. p x) xs) @ (filter (\<lambda>x. \<not>p x) xs) \<in> set (permutations xs)" using perm_prop_1 by auto
  have "\<Union>\<^sub>p (filter (\<lambda>x. p x) xs) \<union>\<^sub>p \<Union>\<^sub>p (filter (\<lambda>x. \<not>p x) xs) = \<Union>\<^sub>p ((filter (\<lambda>x. p x) xs) @ (filter (\<lambda>x. \<not>p x) xs))" using a1
    by (simp add: Choice_prop_7 \<open>\<exists>x\<in>set xs. \<not> p x\<close> filter_empty_conv)
  show ?thesis
    by (metis Choice_prop_1_1 \<open>\<Union>\<^sub>p (filter p xs) \<union>\<^sub>p \<Union>\<^sub>p (filter (\<lambda>x. \<not> p x) xs) = \<Union>\<^sub>p (filter p xs @ filter (\<lambda>x. \<not> p x) xs)\<close> \<open>filter p xs @ filter (\<lambda>x. \<not> p x) xs \<in> set (permutations xs)\<close>)
qed

theorem Choice_prop_9: "size xs>1 \<Longrightarrow> size ys>1 \<Longrightarrow> set xs = set ys \<Longrightarrow> \<Union>\<^sub>p (xs) = \<Union>\<^sub>p (ys)"
proof  (induction "size xs" arbitrary: xs ys rule: less_induct)
  case less
  obtain x xs' where o0: "xs=x#xs'"
    by (metis length_0_conv less.prems(1) less_nat_zero_code neq_Nil_conv)
  obtain xs\<^sub>1 where o1: "xs\<^sub>1 = filter ((=) x) xs" by simp
  obtain xs\<^sub>2 where o2: "xs\<^sub>2 = filter ((\<noteq>) x) xs" by simp
  obtain ys\<^sub>1 where o3: "ys\<^sub>1 = filter ((=) x) ys" by simp
  obtain ys\<^sub>2 where o4: "ys\<^sub>2 = filter ((\<noteq>) x) ys" by simp
  have "set (xs\<^sub>1) = {x}" using o1 less(2) by (auto simp add: o0)
  have "set (xs\<^sub>1) = set (ys\<^sub>1)"
    by (simp add: less.prems(3) o1 o3)
  have "set (xs\<^sub>2) = set (ys\<^sub>2)"
    by (simp add: less.prems(3) o2 o4)
  have "xs\<^sub>1@xs\<^sub>2 \<in> set (permutations xs)"
    by (simp add: o1 o2 perm_prop_1)
  have "ys\<^sub>1@ys\<^sub>2 \<in> set (permutations ys)"
    by (simp add: o3 o4 perm_prop_1)
  have l1: "\<Union>\<^sub>p xs\<^sub>1 = x \<or> \<Union>\<^sub>p xs\<^sub>1 = x \<union>\<^sub>p x"
    apply (cases "size xs\<^sub>1 = 1")
    apply (simp add: Choice_prop_5 \<open>set xs\<^sub>1 = {x}\<close>)
    by (metis Choice_prop_6 One_nat_def Suc_lessI \<open>set xs\<^sub>1 = {x}\<close> insert_not_empty length_greater_0_conv set_empty2)
  have l2: "\<Union>\<^sub>p ys\<^sub>1 = x \<or> \<Union>\<^sub>p ys\<^sub>1 = x \<union>\<^sub>p x"
    apply (cases "size ys\<^sub>1 = 1")
    using Choice_prop_5 \<open>set xs\<^sub>1 = set ys\<^sub>1\<close> \<open>set xs\<^sub>1 = {x}\<close> apply blast
    by (metis Choice_prop_6 One_nat_def Suc_lessI \<open>set xs\<^sub>1 = {x}\<close> \<open>set xs\<^sub>1 = set ys\<^sub>1\<close> insert_not_empty length_greater_0_conv set_empty2)
  then show "\<Union>\<^sub>p xs = \<Union>\<^sub>p ys"
  proof (cases "size xs\<^sub>2 \<le> 1")
    case True
    assume "length xs\<^sub>2 \<le> 1"
    then show ?thesis
    proof (cases "size xs\<^sub>2 = 0")
      case True
      have "xs\<^sub>1 = xs"
        by (metis True \<open>xs\<^sub>1 @ xs\<^sub>2 \<in> set (permutations xs)\<close> filter_True length_0_conv length_filter_less length_inv less_imp_neq o1 self_append_conv)
      have "ys\<^sub>1 = ys"
        by (metis \<open>xs\<^sub>1 = xs\<close> filter_id_conv less.prems(3) o1 o3)
      have "\<Union>\<^sub>p xs = x \<union>\<^sub>p x" using less(2) l1
        by (metis Choice_prop_6 \<open>set xs\<^sub>1 = {x}\<close> \<open>xs\<^sub>1 = xs\<close>)
      have "\<Union>\<^sub>p ys = x \<union>\<^sub>p x" using less(3) l2
        by (metis Choice_prop_6 \<open>set xs\<^sub>1 = {x}\<close> \<open>xs\<^sub>1 = xs\<close> less.prems(3))
      then show ?thesis
        by (simp add: \<open>\<Union>\<^sub>p xs = x \<union>\<^sub>p x\<close>)
    next
      case False
      assume "length xs\<^sub>2 \<noteq> 0"
      then show ?thesis
      proof (cases "length xs\<^sub>2 = 1")
        case True
        assume "length xs\<^sub>2 = 1"
        obtain x' where "xs\<^sub>2 = [x']" using True apply auto
          by (metis Suc_length_conv length_0_conv)
        have "\<Union>\<^sub>p xs\<^sub>2 = x'"
          by (simp add: \<open>xs\<^sub>2 = [x']\<close>)
        then have "\<Union>\<^sub>p ys\<^sub>2 = x' \<or> \<Union>\<^sub>p ys\<^sub>2 = x' \<union>\<^sub>p x'" using less(4) o4 o2
            apply (cases "size xs\<^sub>2 = 1") using Choice_prop_5 apply auto [1]
           apply (smt (verit, del_insts) Choice_prop_5 Choice_prop_6 False Suc_inject True \<open>set xs\<^sub>2 = set ys\<^sub>2\<close> \<open>xs\<^sub>2 = [x']\<close> bot_nat_0.extremum_uniqueI empty_set leI le_Suc_eq length_0_conv less_numeral_extra(1) list.simps(15) o2 o4 set_empty2 singletonD)
          using Choice_prop_6
          using True by linarith
        have "\<Union>\<^sub>p xs = x \<union>\<^sub>p x'"
          by (metis Choice_prop_1_1 Choice_prop_3 \<open>set xs\<^sub>1 = {x}\<close> \<open>xs\<^sub>1 @ xs\<^sub>2 \<in> set (permutations xs)\<close> \<open>xs\<^sub>2 = [x']\<close> choice_idem_6 insert_not_empty local.l1 set_empty)
        have "\<Union>\<^sub>p ys = \<Union>\<^sub>p ys\<^sub>1 \<union>\<^sub>p \<Union>\<^sub>p ys\<^sub>2"
          by (metis Choice_prop_1_1 Choice_prop_7 Cons_eq_append_conv False \<open>set xs\<^sub>1 = set ys\<^sub>1\<close> \<open>set xs\<^sub>1 = {x}\<close> \<open>set xs\<^sub>2 = set ys\<^sub>2\<close> \<open>xs\<^sub>2 = [x']\<close> \<open>ys\<^sub>1 @ ys\<^sub>2 \<in> set (permutations ys)\<close> length_0_conv list.sel(3) list.simps(15) set_empty2)
        then show ?thesis
          by (metis \<open>\<Union>\<^sub>p xs = x \<union>\<^sub>p x'\<close> \<open>\<Union>\<^sub>p ys\<^sub>2 = x' \<or> \<Union>\<^sub>p ys\<^sub>2 = x' \<union>\<^sub>p x'\<close> choice_idem_5 choice_idem_6 local.l2)
      next
        case False
        then show ?thesis
          using True \<open>length xs\<^sub>2 \<noteq> 0\<close> by auto
      qed
    qed
  next
    case False
    have "1 < length xs\<^sub>2" using False by auto
    then show ?thesis
    proof (cases "length ys\<^sub>2 = 1")
      case True
      obtain y where "ys\<^sub>2 = [y]" using True apply auto
        by (metis Suc_length_conv length_0_conv)
      have "\<Union>\<^sub>p xs\<^sub>2 = y \<or> \<Union>\<^sub>p xs\<^sub>2 = y \<union>\<^sub>p y"
        apply (cases "size xs\<^sub>2 = 0")
        using False apply auto[1]
        apply (cases "size xs\<^sub>2 = 1")
        using False apply auto using Choice_prop_6
        using \<open>1 < length xs\<^sub>2\<close> \<open>set xs\<^sub>2 = set ys\<^sub>2\<close> \<open>ys\<^sub>2 = [y]\<close> list.simps(15) by auto
      have "\<Union>\<^sub>p xs = \<Union>\<^sub>p xs\<^sub>1 \<union>\<^sub>p \<Union>\<^sub>p xs\<^sub>2"
        by (metis Choice_prop_1_1 Choice_prop_7 \<open>set xs\<^sub>1 = {x}\<close> \<open>set xs\<^sub>2 = set ys\<^sub>2\<close> \<open>xs\<^sub>1 @ xs\<^sub>2 \<in> set (permutations xs)\<close> \<open>ys\<^sub>2 = [y]\<close> insert_not_empty not_Cons_self2 set_empty2)
      have "... = \<Union>\<^sub>p xs\<^sub>1 \<union>\<^sub>p y"
        by (metis \<open>\<Union>\<^sub>p xs\<^sub>2 = y \<or> \<Union>\<^sub>p xs\<^sub>2 = y \<union>\<^sub>p y\<close> choice_idem_5)
      then show "\<Union>\<^sub>p xs = \<Union>\<^sub>p ys"
        by (metis Choice.simps(2) Choice_prop_1_1 Choice_prop_7 True \<open>\<Union>\<^sub>p xs = \<Union>\<^sub>p xs\<^sub>1 \<union>\<^sub>p \<Union>\<^sub>p xs\<^sub>2\<close> \<open>ys\<^sub>1 @ ys\<^sub>2 \<in> set (permutations ys)\<close> \<open>ys\<^sub>2 = [y]\<close> choice_idem_6 length_inv less.prems(2) linorder_neq_iff list.discI local.l1 local.l2 self_append_conv2)
    next
      case False
      have "1 < length ys\<^sub>2"
        using False \<open>1 < length xs\<^sub>2\<close> \<open>set xs\<^sub>2 = set ys\<^sub>2\<close> nat_neq_iff by auto
      have "\<Union>\<^sub>p xs\<^sub>2 = \<Union>\<^sub>p ys\<^sub>2"
        by (metis (mono_tags, lifting) \<open>1 < length xs\<^sub>2\<close> \<open>1 < length ys\<^sub>2\<close> \<open>set xs\<^sub>2 = set ys\<^sub>2\<close> length_filter_less less.hyps list.set_intros(1) o0 o2)
      
      then show ?thesis
        by (smt (verit) Choice_prop_1_1 Choice_prop_7 One_nat_def Suc_lessD \<open>1 < length xs\<^sub>2\<close> \<open>1 < length ys\<^sub>2\<close> \<open>set xs\<^sub>1 = set ys\<^sub>1\<close> \<open>set xs\<^sub>1 = {x}\<close> \<open>xs\<^sub>1 @ xs\<^sub>2 \<in> set (permutations xs)\<close> \<open>ys\<^sub>1 @ ys\<^sub>2 \<in> set (permutations ys)\<close> choice_idem_6 insert_not_empty length_greater_0_conv local.l1 local.l2 set_empty2)
    qed
  qed
qed

theorem Choice_prop_10: "size xs=1 \<Longrightarrow> size ys=1 \<Longrightarrow> set xs = set ys \<Longrightarrow> \<Union>\<^sub>p (xs) = \<Union>\<^sub>p (ys)"
  apply (induction xs arbitrary: ys) apply auto
  by (metis Choice_prop_5 One_nat_def)

theorem Choice_prop11: "size xs > 1 \<Longrightarrow> \<Union>\<^sub>p (filter (\<lambda>t. P t) xs) \<union>\<^sub>p \<Union>\<^sub>p (filter (\<lambda>t. \<not>P t) xs) = \<Union>\<^sub>p xs"
proof (cases "filter (\<lambda>t. P t) xs = xs")
  case True
  assume a1: "size xs > 1"
  have "(filter (\<lambda>t. \<not>P t) xs) = []"
    by (metis True filter_False filter_id_conv)
  have "\<Union>\<^sub>p (filter (\<lambda>t. \<not>P t) xs) = Fail {}"
    by (simp add: \<open>filter (\<lambda>t. \<not> P t) xs = []\<close>)
  obtain x x' xs' where "xs=x#x'#xs'" using a1 apply auto
    by (metis gen_length_code(1) gen_length_code(2) length_code less_irrefl_nat less_nat_zero_code remdups_adj.cases)
  then show ?thesis
    by (metis Choice_prop_1_2 True \<open>\<Union>\<^sub>p (filter (\<lambda>t. \<not> P t) xs) = Fail {}\<close> choice_commute special_empty1 list.distinct(1) skip_prop_12)
next
  case False
  assume a0: "filter (\<lambda>t. P t) xs \<noteq> xs"
  assume a1: "size xs > 1"
  then show ?thesis
  proof (cases "filter (\<lambda>t. \<not>P t) xs = xs")
    case True
    have "(filter (\<lambda>t. P t) xs) = []"
      by (metis True filter_False filter_id_conv)
    have "\<Union>\<^sub>p (filter (\<lambda>t. P t) xs) = Fail {}"
      by (simp add: \<open>filter (\<lambda>t. P t) xs = []\<close>)
    obtain x x' xs' where "xs=x#x'#xs'" using a1 apply auto
      by (metis gen_length_code(1) gen_length_code(2) length_code less_irrefl_nat less_nat_zero_code remdups_adj.cases)
    then show ?thesis
      by (metis Choice_prop_1_2 True \<open>\<Union>\<^sub>p (filter P xs) = Fail {}\<close> special_empty1 list.distinct(1) skip_prop_12)
  next
    case False
    obtain x q where "x#q=(filter (\<lambda>t. P t) xs)"
      by (metis (no_types, lifting) False filter_True list.set_cases mem_Collect_eq set_filter)
    obtain y p where "y#p=(filter (\<lambda>t. \<not>P t) xs)"
      by (metis a0 empty_filter_conv filter_True neq_Nil_conv)
    then show ?thesis
      by (metis Choice_prop_8 False a0 filter_True)
  qed
qed

theorem Choice_prop12: "x \<in> set xs \<Longrightarrow> \<Union>\<^sub>p (filter ((=) x) (x#xs)) = x \<union>\<^sub>p x"
  apply (induction xs arbitrary: x) apply auto
  apply (smt (verit) Choice_prop_1_4 Choice.elims choice_idem_6 filter_False filter_cong foldl_Nil list.distinct(1) list.sel(1) tl_step)
  by (metis Choice_prop_1_4 Choice_prop_1_2 choice_idem_5 choice_idem_6 foldl_Cons not_Cons_self2)

theorem Choice_state_1: "complete_state xs = S (Choice xs)"
proof (induction "size xs" arbitrary: xs)
  case 0
  then show ?case by (auto simp: complete_state_def Fail_def S_def)
next
  case (Suc n)
  assume IH: "\<And>xs. n = length xs \<Longrightarrow> complete_state xs = S (\<Union>\<^sub>p xs)"
  assume a1: "Suc n = length xs"
  obtain x' xs' where "xs=x'#xs'" using a1
    by (metis Nitpick.size_list_simp(2) nat.distinct(1) neq_Nil_conv)
  have "S (\<Union>\<^sub>p xs) = S (foldl (\<union>\<^sub>p) x' xs')"
    by (metis (no_types) Choice.simps(2) Choice.simps(3) \<open>xs = x' # xs'\<close> foldl_Nil permutations.cases)
  then show "complete_state xs = S (\<Union>\<^sub>p xs)"
  proof (cases "xs' = []")
    case True
    then show ?thesis
      by (metis Choice.simps(1) Suc.hyps(1) Suc_length_conv \<open>S (\<Union>\<^sub>p xs) = S (foldl (\<union>\<^sub>p) x' xs')\<close> \<open>xs = x' # xs'\<close> a1 complete_state_prop special_empty1 foldl_Nil old.nat.inject skip_prop_9 sup_bot_left)
  next
    case False
    have "Choice xs = foldl (\<union>\<^sub>p) x' xs'"
      by (metis Choice.simps(2) Choice.simps(3) \<open>xs = x' # xs'\<close> foldl_Nil permutations.elims)
    have "... = x' \<union>\<^sub>p Choice xs'" using False Choice_prop_1_4
      by blast
    then show "complete_state xs = S (\<Union>\<^sub>p xs)"
      by (metis Suc.hyps(1) Suc_inject \<open>S (\<Union>\<^sub>p xs) = S (foldl (\<union>\<^sub>p) x' xs')\<close> \<open>xs = x' # xs'\<close> a1 choice_commute choice_state complete_state_prop length_Cons)
  qed
qed




theorem Concat_prop_1: "xs \<noteq> [] \<Longrightarrow> foldl (;) x xs = x ; Concat xs"
proof -
  assume a1: "xs \<noteq> []"
  obtain x' xs' where o1: "xs=x'#xs'" using a1
    using list.exhaust by auto
  have "Concat xs = foldl (;) x' xs'"
    by (metis Concat.simps(2) Concat.simps(3) foldl_Nil hd_Cons_tl o1)
  have "x ; Concat xs = x ; foldl (;) x' xs'"
    by (simp add: \<open>Concat xs = foldl (;) x' xs'\<close>)
  have "... =  foldl (;) x xs"
    by (simp add: o1 simp_2)
  show ?thesis
    by (simp add: \<open>x ; Concat xs = x ; foldl (;) x' xs'\<close> \<open>x ; foldl (;) x' xs' = foldl (;) x xs\<close>)
qed

theorem Concat_state: "complete_state xs = S (Concat xs)"
proof (induction "size xs" arbitrary: xs)
  case 0
  then show ?case by (auto simp: complete_state_def Skip_def S_def)
next
  case (Suc n)
  assume IH: "\<And>xs. n = length xs \<Longrightarrow> complete_state xs = S (Concat xs)"
  assume a1: "Suc n = length xs"
  obtain x' xs' where "xs=x'#xs'" using a1
    by (metis Nitpick.size_list_simp(2) nat.distinct(1) neq_Nil_conv)
  have "S (Concat xs) = S (foldl (;) x' xs')"
    by (metis (no_types) Concat.simps(2) Concat.simps(3) \<open>xs = x' # xs'\<close> foldl_Nil permutations.cases)
  then show "complete_state xs = S (Concat xs)"
  proof (cases "xs' = []")
    case True
    then show ?thesis
      by (metis Concat.simps(1) Suc.hyps(1) Suc_length_conv \<open>S (Concat xs) = S (foldl (;) x' xs')\<close> \<open>xs = x' # xs'\<close> a1 complete_state_prop special_empty1 foldl_Nil old.nat.inject skip_prop_9 sup_bot_left)
  next
    case False
    have "Concat xs = foldl (;) x' xs'"
      by (metis Concat.simps(2) Concat.simps(3) \<open>xs = x' # xs'\<close> foldl_Nil permutations.elims)
    have "... = x' ; Concat xs'" using False Concat_prop_1
      by blast
    then show "complete_state xs = S (Concat xs)"
      by (metis \<open>S (Concat xs) = S (foldl (;) x' xs')\<close> \<open>xs = x' # xs'\<close> fold_comp_prop3)
  qed
qed

theorem Choice_prop_13: "size xs > 0 \<Longrightarrow> \<Union>\<^sub>p [a;(Concat t). t \<leftarrow> xs] \<equiv>\<^sub>p a;\<Union>\<^sub>p [(Concat t). t \<leftarrow> xs]"
proof (induction xs arbitrary: a)
  case Nil
  then show ?case by (simp add: equiv_is_reflexive)
next
  case (Cons x xs)
  then show "\<Union>\<^sub>p [a;(Concat t). t \<leftarrow> x#xs] \<equiv>\<^sub>p a;\<Union>\<^sub>p [(Concat t). t \<leftarrow> x#xs]"
  proof (cases "xs = []")
    case True
    then show ?thesis
      by (metis Choice.simps(2) Choice_prop_4 list.simps(9) map_is_Nil_conv)
  next
    case False
    have l1: "\<Union>\<^sub>p [a;(Concat t). t \<leftarrow> x#xs] = a;Concat x \<union>\<^sub>p \<Union>\<^sub>p [a;(Concat t). t \<leftarrow> xs]" apply auto
      by (simp add: Choice_prop_1_2 False)
    moreover have l2: "\<Union>\<^sub>p [a;(Concat t). t \<leftarrow> xs] \<equiv>\<^sub>p a;\<Union>\<^sub>p [(Concat t). t \<leftarrow> xs]" using Cons False by auto
    ultimately have l3: "a;Concat x \<union>\<^sub>p \<Union>\<^sub>p [a;(Concat t). t \<leftarrow> xs] \<equiv>\<^sub>p (a;Concat x) \<union>\<^sub>p (a;\<Union>\<^sub>p [(Concat t). t \<leftarrow> xs])"
      by (smt (verit) choice_idem_6 compose_distrib2_1 compose_distrib2_3 choice_equiv)
    have l4: "... \<equiv>\<^sub>p a;(Concat x \<union>\<^sub>p \<Union>\<^sub>p [(Concat t). t \<leftarrow> xs])"
    proof -
      obtain x1 where "x1=Concat x" by simp
      obtain x2 where "x2=\<Union>\<^sub>p [(Concat t). t \<leftarrow> xs]" by simp
      have "a ; x1 \<union>\<^sub>p a ; x2 \<equiv>\<^sub>p a ; (x1 \<union>\<^sub>p x2)"
        by (simp add: compose_distrib1_3 equiv_is_symetric)
      show "a ; Concat x \<union>\<^sub>p a ; \<Union>\<^sub>p (map Concat xs) \<equiv>\<^sub>p a ; (Concat x \<union>\<^sub>p \<Union>\<^sub>p (map Concat xs))"
        using \<open>a ; x1 \<union>\<^sub>p a ; x2 \<equiv>\<^sub>p a ; (x1 \<union>\<^sub>p x2)\<close> \<open>x1 = Concat x\<close> \<open>x2 = \<Union>\<^sub>p (map Concat xs)\<close> by auto
    qed
    have l5: "... = a;(\<Union>\<^sub>p [(Concat t). t \<leftarrow> x#xs])"
      by (simp add: Choice_prop_1_2 False)
    then show ?thesis using l1 l2 l3 l4 l5 equiv_is_reflexive equiv_is_transitive by auto
  qed
qed

theorem Choice_prop_14: "\<Union>\<^sub>p [t \<sslash>\<^sub>p C . t \<leftarrow> xs] \<equiv>\<^sub>p \<Union>\<^sub>p [t . t \<leftarrow> xs]\<sslash>\<^sub>p C"
  apply auto
proof (induction xs arbitrary: C)
  case Nil
  then show ?case by (auto simp: Fail_def restrict_p_def equiv_def restr_post_def restrict_r_def) [1]
next
  case (Cons x xs)
  assume IH: "\<And>C. \<Union>\<^sub>p (map (\<lambda>t. t \<sslash>\<^sub>p C) xs) \<equiv>\<^sub>p \<Union>\<^sub>p xs \<sslash>\<^sub>p C"
  then show "\<Union>\<^sub>p [t \<sslash>\<^sub>p C . t \<leftarrow> (x # xs)] \<equiv>\<^sub>p \<Union>\<^sub>p (x # xs) \<sslash>\<^sub>p C"
  proof (cases "xs = []")
    case True
    then show ?thesis by (auto simp: equiv_def)
  next
    case False
    have "\<Union>\<^sub>p [t \<sslash>\<^sub>p C . t \<leftarrow> (x # xs)] = x \<sslash>\<^sub>p C \<union>\<^sub>p \<Union>\<^sub>p [t \<sslash>\<^sub>p C . t \<leftarrow> (xs)]"
      by (simp add: Choice_prop_1_2 False)
    have "\<Union>\<^sub>p [t \<sslash>\<^sub>p C . t \<leftarrow> (xs)] \<equiv>\<^sub>p \<Union>\<^sub>p xs \<sslash>\<^sub>p C" using IH by auto
    then have "x \<sslash>\<^sub>p C \<union>\<^sub>p \<Union>\<^sub>p [t \<sslash>\<^sub>p C . t \<leftarrow> (xs)] \<equiv>\<^sub>p x \<sslash>\<^sub>p C \<union>\<^sub>p \<Union>\<^sub>p xs \<sslash>\<^sub>p C"
      by (simp add: equals_equiv_relation_3 choice_equiv) 
    have "... \<equiv>\<^sub>p \<Union>\<^sub>p (x # xs) \<sslash>\<^sub>p C"
      by (simp add: Choice_prop_1_2 False equiv_is_symetric restrict_distrib_3)
    then show "\<Union>\<^sub>p [t \<sslash>\<^sub>p C . t \<leftarrow> (x # xs)] \<equiv>\<^sub>p \<Union>\<^sub>p (x # xs) \<sslash>\<^sub>p C"
      using \<open>\<Union>\<^sub>p (map (\<lambda>t. t \<sslash>\<^sub>p C) (x # xs)) = x \<sslash>\<^sub>p C \<union>\<^sub>p \<Union>\<^sub>p (map (\<lambda>t. t \<sslash>\<^sub>p C) xs)\<close> \<open>x \<sslash>\<^sub>p C \<union>\<^sub>p \<Union>\<^sub>p (map (\<lambda>t. t \<sslash>\<^sub>p C) xs) \<equiv>\<^sub>p x \<sslash>\<^sub>p C \<union>\<^sub>p \<Union>\<^sub>p xs \<sslash>\<^sub>p C\<close> equiv_is_transitive by auto
  qed
qed
theorem "\<Union>\<^sub>p [t \<sslash>\<^sub>p C . t \<leftarrow> xs] = \<Union>\<^sub>p [t . t \<leftarrow> xs]\<sslash>\<^sub>p C"
  oops

theorem Choice_prop_15: "\<Union>\<^sub>p [t \<setminus>\<^sub>p C . t \<leftarrow> xs] = \<Union>\<^sub>p [t . t \<leftarrow> xs]\<setminus>\<^sub>p C"
  apply auto
proof (induction xs arbitrary: C)
  case Nil
  then show ?case by (auto simp: Fail_def corestrict_p_def restrict_r_def equiv_def restr_post_def corestrict_r_def S_def)
next
  case (Cons x xs)
  assume IH: "\<And>C. \<Union>\<^sub>p (map (\<lambda>t. t \<setminus>\<^sub>p C) xs) = \<Union>\<^sub>p xs \<setminus>\<^sub>p C"
  then show ?case
  proof (cases "xs = []")
    case True
    then show ?thesis by (auto simp: equiv_def)
  next
    case False
    have "\<Union>\<^sub>p (map (\<lambda>t. t \<setminus>\<^sub>p C) (x # xs)) = x \<setminus>\<^sub>p C \<union>\<^sub>p \<Union>\<^sub>p (map (\<lambda>t. t \<setminus>\<^sub>p C) (xs))"
      by (metis (no_types, lifting) Choice_prop_1_2 False list.simps(9) map_is_Nil_conv)
    have "\<Union>\<^sub>p (map (\<lambda>t. t \<setminus>\<^sub>p C) (xs)) = \<Union>\<^sub>p xs \<setminus>\<^sub>p C" using Cons by auto
    then have "x \<setminus>\<^sub>p C \<union>\<^sub>p \<Union>\<^sub>p (map (\<lambda>t. t \<setminus>\<^sub>p C) (xs)) \<equiv>\<^sub>p x \<setminus>\<^sub>p C \<union>\<^sub>p \<Union>\<^sub>p xs \<setminus>\<^sub>p C"
      by (simp add: equiv_is_reflexive choice_equiv)
    have "... = \<Union>\<^sub>p (x # xs) \<setminus>\<^sub>p C"
      by (metis Choice_prop_1_2 False corestrict_choice_1)
    then show "\<Union>\<^sub>p (map (\<lambda>t. t \<setminus>\<^sub>p C) (x # xs)) = \<Union>\<^sub>p (x # xs) \<setminus>\<^sub>p C"
      using \<open>\<Union>\<^sub>p (map (\<lambda>t. t \<setminus>\<^sub>p C) (x # xs)) = x \<setminus>\<^sub>p C \<union>\<^sub>p \<Union>\<^sub>p (map (\<lambda>t. t \<setminus>\<^sub>p C) xs)\<close> \<open>\<Union>\<^sub>p (map (\<lambda>t. t \<setminus>\<^sub>p C) xs) = \<Union>\<^sub>p xs \<setminus>\<^sub>p C\<close> by auto
  qed
qed


theorem Concat_prop_2: "xs \<noteq> [] \<Longrightarrow> Concat (xs@[x]) = Concat xs ; x"
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  obtain xs' where o1: "xs' = xs @ [x]" by simp
  have l1: "Concat (a # xs') = a ; Concat (xs')"
    by (metis Concat.simps(3) Concat_prop_1 list.exhaust_sel o1 snoc_eq_iff_butlast)
  then show "Concat ((a # xs) @ [x]) = Concat (a # xs) ; x"
  proof (cases "xs = []")
    case True
    then show ?thesis by auto
  next
    case False
    have l2: "Concat (xs @ [x]) = Concat (xs) ; x" using Cons False by auto
    have l3: "a;Concat (xs @ [x]) = Concat (a#xs @ [x])"
      using local.l1 o1 by force
    have l4: "Concat (a # xs) ; x = (a; Concat (xs)) ; x"
      by (smt (verit) Concat.elims Concat_prop_1 Cons.prems False list.inject)
    then show ?thesis
      using local.l2 local.l3 by auto
  qed
qed


theorem Concat_prop_3: "xs \<noteq> [] \<Longrightarrow> Concat xs \<sslash>\<^sub>p C \<equiv>\<^sub>p Concat (hd xs \<sslash>\<^sub>p C # tl xs)"
proof (induction xs arbitrary: C)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  assume IH: "\<And>C. xs \<noteq> [] \<Longrightarrow> Concat xs \<sslash>\<^sub>p C \<equiv>\<^sub>p Concat (hd xs \<sslash>\<^sub>p C # tl xs)"
  have "hd (x # xs) = x" by auto
  have "tl (x # xs) = xs" by auto
  have "Concat (x # xs) \<sslash>\<^sub>p C \<equiv>\<^sub>p Concat (x \<sslash>\<^sub>p C # xs)"
  proof (induction xs arbitrary: x C rule: rev_induct)
    case Nil
    then show ?case by (auto simp: equiv_def)
  next
    case (snoc y xs)
    assume IH: "\<And>x C. Concat (x # xs) \<sslash>\<^sub>p C \<equiv>\<^sub>p Concat (x \<sslash>\<^sub>p C # xs)"
    have "Concat (x # xs @ [y]) = Concat (x # xs) ; y"
      using Concat_prop_2 by fastforce
    then show "Concat (x # xs @ [y]) \<sslash>\<^sub>p C \<equiv>\<^sub>p Concat (x \<sslash>\<^sub>p C # xs @ [y])"
      by (smt (verit) Concat.elims Concat_prop_1 compose_absorb_3 list.discI list.sel(1) list.sel(3) snoc_eq_iff_butlast)
  qed
  then show "Concat (x # xs) \<sslash>\<^sub>p C \<equiv>\<^sub>p Concat (hd (x # xs) \<sslash>\<^sub>p C # tl (x # xs))"
    by simp
qed

theorem Concat_prop_4: "xs \<noteq> [] \<Longrightarrow> Concat xs \<setminus>\<^sub>p C \<equiv>\<^sub>p Concat (butlast xs @ [(last xs)\<setminus>\<^sub>p C])"
proof (induction xs arbitrary: C rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  assume IH: "\<And>C. xs \<noteq> [] \<Longrightarrow> Concat xs \<setminus>\<^sub>p C \<equiv>\<^sub>p Concat (butlast xs @ [last xs \<setminus>\<^sub>p C])"
  show "Concat (xs @ [x]) \<setminus>\<^sub>p C \<equiv>\<^sub>p Concat (butlast (xs @ [x]) @ [last (xs @ [x]) \<setminus>\<^sub>p C])"
  proof (cases "xs = []")
    case True
    then show ?thesis by (auto simp: equiv_def)
  next
    case False
    have "Concat (xs @ [x]) \<setminus>\<^sub>p C = (Concat (xs) ; x) \<setminus>\<^sub>p C"
      by (simp add: Concat_prop_2 False)
    have "... \<equiv>\<^sub>p Concat (xs) ; (x \<setminus>\<^sub>p C)"
      by (simp add: corestrict_compose equiv_is_reflexive)
    have "... = Concat (xs@[(x \<setminus>\<^sub>p C)])"
      by (simp add: Concat_prop_2 False)
    have "... =  Concat (butlast (xs @ [x]) @ [last (xs @ [x]) \<setminus>\<^sub>p C])"
      by simp
    then show ?thesis
      using \<open>(Concat xs ; x) \<setminus>\<^sub>p C \<equiv>\<^sub>p Concat xs ; x \<setminus>\<^sub>p C\<close> \<open>Concat (xs @ [x]) \<setminus>\<^sub>p C = (Concat xs ; x) \<setminus>\<^sub>p C\<close> \<open>Concat xs ; x \<setminus>\<^sub>p C = Concat (xs @ [x \<setminus>\<^sub>p C])\<close> by auto
  qed
qed


theorem Choice_prop_16: "x \<in> set xs \<Longrightarrow> \<Union>\<^sub>p xs \<equiv>\<^sub>p \<Union>\<^sub>p xs \<union>\<^sub>p x"
  apply (induction xs arbitrary: x)
  apply (auto simp:)
  apply (metis Choice.simps(2) Choice_prop_1_2 choice_commute choice_idem_2 choice_idem_3 equiv_is_symetric)
  by (metis Choice_prop_1_2 choice_assoc_1 choice_commute equals_equiv_relation_3 choice_equiv list.set_cases null_rec(1) null_rec(2))

theorem Choice_prop_17: "size xs > 1 \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<Union>\<^sub>p xs = \<Union>\<^sub>p xs \<union>\<^sub>p x"
  apply (induction xs arbitrary: x)
  apply (auto simp:)
  apply (simp add: Choice_prop_1_2 choice_idem_2)
  by (smt (verit) Choice.simps(2) Choice_prop_1_2 Suc_lessI choice_assoc_1 choice_commute choice_idem_2 length_Suc_conv length_pos_if_in_set less_numeral_extra(3) list.inject list.set_cases)

theorem Concat_prop_5: "xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> Concat (xs@ys) = Concat xs ; Concat ys"
  apply (induction xs arbitrary: ys)
  apply (auto)
  by (smt (verit) Concat.elims Concat_prop_1 foldl_Nil foldl_append list.discI list.inject)

theorem Concat_prop_6: "Concat (a \<union>\<^sub>p b # xs) = Concat (a # xs) \<union>\<^sub>p Concat (b # xs)"
  by (metis Concat.simps(2) Concat_prop_5 Cons_eq_appendI append_self_conv2 compose_distrib2_1 not_Cons_self2)

theorem Concat_prop_7: "Concat (xs@[a \<union>\<^sub>p b]) \<equiv>\<^sub>p Concat (xs@[a]) \<union>\<^sub>p Concat (xs@[b])"
  by (metis Concat.simps(2) Concat_prop_2 append_self_conv2 compose_distrib1_3 equiv_is_reflexive)

theorem Concat_prop_8: "e \<noteq> [] \<Longrightarrow> Concat (s@(a \<union>\<^sub>p b)#e) \<equiv>\<^sub>p Concat (s@a#e) \<union>\<^sub>p Concat (s@b#e)"
  apply (cases "s=[]") apply auto
  using Concat_prop_6 equals_equiv_relation_3 apply blast
  by (simp add: Concat_prop_5 Concat_prop_6 compose_distrib1_3)

theorem Choice_prop_18: "size b > 1 \<Longrightarrow> \<Union>\<^sub>p b = \<Union>\<^sub>p b \<union>\<^sub>p Fail {}"
proof (induction "size b" arbitrary: b)
  case 0
  then show ?case by simp
next
  case (Suc n)
  obtain x b' where o1: "x#b'=b"
    by (metis Suc.hyps(2) add_cancel_left_right length_0_conv length_replicate plus_1_eq_Suc remdups_adj.cases replicate_Suc)
  have "size b' = n"
    using Suc.hyps(2) o1 by auto
  have "\<Union>\<^sub>p (x#b') = x \<union>\<^sub>p \<Union>\<^sub>p b'"
    by (metis Choice.simps(1) Choice.simps(2) Choice_prop_1_2 Cons_nth_drop_Suc Suc.hyps(1) Suc.hyps(2) Suc.prems butlast.simps(1) butlast_snoc length_Cons length_Suc_conv_rev length_butlast length_drop o1)
  moreover have "... = x \<union>\<^sub>p (\<Union>\<^sub>p b' \<union>\<^sub>p Fail {})"
    apply (cases "b' = []")
    apply (simp add: choice_idem_5)
    apply (cases "size b' = 1")
    apply (metis choice_assoc_1 choice_commute special_empty1 skip_prop_12)
    by (metis Suc.hyps(1) Suc.hyps(2) Suc.prems \<open>length b' = n\<close> less_SucE)
  moreover have "... = \<Union>\<^sub>p (x#b') \<union>\<^sub>p Fail {}"
    by (metis calculation(1) choice_assoc_1)
  ultimately show "\<Union>\<^sub>p b = \<Union>\<^sub>p b \<union>\<^sub>p Fail {}" using o1 by simp
qed


theorem Choice_prop_19: "size (a@b) > 1 \<Longrightarrow> \<Union>\<^sub>p a \<union>\<^sub>p \<Union>\<^sub>p b = \<Union>\<^sub>p (a@b)"
  by (metis Choice.simps(1) Choice_prop_18 Choice_prop_7 append.right_neutral append_self_conv2 choice_commute)

theorem Choice_prop_20: "size (a@b) > 0 \<Longrightarrow> \<Union>\<^sub>p a \<union>\<^sub>p (x \<union>\<^sub>p \<Union>\<^sub>p b) = \<Union>\<^sub>p (a@x#b)"
proof -
  assume a1: "size (a@b) > 0"
  obtain b' where o1: "b'=x#b" by simp
  have "size (a@b') > 1" using a1 o1 by auto
  then have "\<Union>\<^sub>p a \<union>\<^sub>p (\<Union>\<^sub>p b') = \<Union>\<^sub>p (a@b')"
    by (simp add: Choice_prop_19)
  show "\<Union>\<^sub>p a \<union>\<^sub>p (x \<union>\<^sub>p \<Union>\<^sub>p b) = \<Union>\<^sub>p (a@x#b)"
    apply (cases "b = []")
    apply (metis Choice.simps(2) Choice_prop_19 \<open>1 < length (a @ b')\<close> append.right_neutral choice_assoc_1 o1)
    by (metis Choice_prop_1_2 \<open>\<Union>\<^sub>p a \<union>\<^sub>p \<Union>\<^sub>p b' = \<Union>\<^sub>p (a @ b')\<close> o1)
qed

theorem Choice_prop_21: "S x \<subseteq> complete_state (a@b) \<Longrightarrow> \<Union>\<^sub>p a \<union>\<^sub>p (x \<sslash>\<^sub>p FALSE \<union>\<^sub>p \<Union>\<^sub>p b) = \<Union>\<^sub>p a \<union>\<^sub>p (Fail {} \<union>\<^sub>p \<Union>\<^sub>p b)"
  apply (induction "size a" arbitrary: a x b)
  apply auto
  apply (metis Choice_state_1 choice_commute restrict_false2)
  by (smt (verit) Choice_prop_7 Choice_state_1 append_eq_append_conv2 choice_assoc_1 choice_commute restrict_false2 self_append_conv2)

theorem list_prop: "1 \<le> i \<Longrightarrow> i \<le> n \<Longrightarrow> [p . t \<leftarrow> [1 .. int n]] = [p . t \<leftarrow> [1 .. int i]] @ [p . t \<leftarrow> [int (Suc i) .. int n]]"
  by (metis int_Suc int_ops(2) map_append nat_leq_as_int upto_split2)

theorem list_prop2: "[p . t \<leftarrow> [1 .. int (Suc n)]] = [p . t \<leftarrow> [1 .. int n]]@[p]"
  apply (cases "n=0")
  apply auto
proof -
  have "[p . t \<leftarrow> [1 .. int (Suc n)]] = [p . t \<leftarrow> [1 .. int n]] @ [p . t \<leftarrow> [int (Suc n) .. int (Suc n)]]"
    by (simp add: upto_rec2)
  have "... = [p . t \<leftarrow> [1 .. int n]] @ [p]"
    by auto
  show "map (\<lambda>t. p) [1..1 + int n] = map (\<lambda>t. p) [1..int n] @ [p]"
    using \<open>map (\<lambda>t. p) [1..int (Suc n)] = map (\<lambda>t. p) [1..int n] @ map (\<lambda>t. p) [int (Suc n)..int (Suc n)]\<close> by auto
qed

theorem list_prop3: "size x = size y \<Longrightarrow> [p. t \<leftarrow> x] = [p. t \<leftarrow> y]"
  by (simp add: map_equality_iff)

theorem list_prop4: "[p . t \<leftarrow> [1 .. int (Suc n)]] = p#[p . t \<leftarrow> [1 .. int n]]"
  apply (cases "n=0")
  apply auto
proof -
  assume "0<n"
  then have l1: "size [2 .. int (Suc n)] = size [1 .. int n]" by auto
  have "[p . t \<leftarrow> [2 .. int (Suc n)]] = [p . t \<leftarrow> [1 .. int n]]" using list_prop3 l1 by fastforce
  have "[p . t \<leftarrow> [1 .. int (Suc n)]] = [p . t \<leftarrow> [1 .. 1]] @ [p . t \<leftarrow> [2 .. int (Suc n)]]"
    by (smt (verit) map_append not_zle_0_negative upto_split2)
  have "... = p# [p . t \<leftarrow> [2 .. int (Suc n)]]"
    by auto
  have "... = p# [p . t \<leftarrow> [1 .. int n]]" using list_prop3
    using \<open>map (\<lambda>t. p) [2..int (Suc n)] = map (\<lambda>t. p) [1..int n]\<close> by blast
  show "map (\<lambda>t. p) [1..1 + int n] = p # map (\<lambda>t. p) [1..int n]"
    using \<open>map (\<lambda>t. p) [1..int (Suc n)] = map (\<lambda>t. p) [1..1] @ map (\<lambda>t. p) [2..int (Suc n)]\<close> \<open>p # map (\<lambda>t. p) [2..int (Suc n)] = p # map (\<lambda>t. p) [1..int n]\<close> by auto
qed


theorem Concat_prop_9: "0<n \<Longrightarrow> Concat [p . t \<leftarrow> [1 .. int n]] ; p = Concat [p . t \<leftarrow> [1 .. int (Suc n)]]"
proof -
  assume a1: "0<n"
  have l5: "[p . t \<leftarrow> [1 .. int (Suc n)]] = [p . t \<leftarrow> [1 .. int n]]@[p]"
    by (metis list_prop2)
  show ?thesis
    by (smt (verit, best) Concat_prop_2 a1 local.l5 map_is_Nil_conv of_nat_0_less_iff upto_Nil2)
qed

theorem Concat_prop_10: "xs \<noteq> [] \<Longrightarrow> Concat (x#xs) = x ; Concat xs"
  by (metis Concat.simps(3) Concat_prop_1 permutations.elims)

theorem Concat_prop_11: "0<n \<Longrightarrow> p ; Concat [p . t \<leftarrow> [1 .. int n]] = Concat [p . t \<leftarrow> [1 .. int (Suc n)]]"
proof -
  assume a1: "0<n"
  have l5: "[p . t \<leftarrow> [1 .. int (Suc n)]] = p#[p . t \<leftarrow> [1 .. int n]]"
    by (metis list_prop4)
  show ?thesis
    by (smt (verit, best) Concat_prop_10 a1 local.l5 map_is_Nil_conv of_nat_0_less_iff upto_Nil2)
qed

theorem Choice_prop_22: "a \<union>\<^sub>p \<Union>\<^sub>p (x#xs) = a \<union>\<^sub>p (x \<union>\<^sub>p \<Union>\<^sub>p xs)"
  apply (induction xs)
  apply auto
  apply (metis choice_assoc_1 choice_commute skip_prop_12 special_empty1)
  by (metis Choice.simps(2) Choice_prop_1_2 Choice_prop_1_4 choice_assoc_1 choice_commute foldl_Nil)

theorem Choice_prop_23: "\<forall>x \<in> set xs. x = y \<Longrightarrow> \<Union>\<^sub>p xs = Fail {} \<or> \<Union>\<^sub>p xs = y \<or> \<Union>\<^sub>p xs = y \<union>\<^sub>p y"
  apply (cases "size xs \<le> 0") apply auto
  apply (cases "size xs \<le> 1") apply auto
  apply (metis Choice.simps(2) append_eq_Cons_conv append_eq_conv_conj append_self_conv2 card_1_singleton_iff drop_all hd_step list.collapse list.set_sel(1) set_to_list_one set_to_list_size)
proof (induction xs arbitrary: y)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
  proof (cases "a=y")
    case t1: True
    then show ?thesis
    proof (cases "xs = []")
      case True
      then show ?thesis using True t1 Cons by auto
    next
      case f1: False
      then show ?thesis
      proof (cases "length xs = 1")
        case True
        then have False
          by (metis Choice.simps(2) Choice_prop_1_2 Cons.prems(1) Cons.prems(4) One_nat_def length_0_conv length_Suc_conv list.set_intros(1) list.set_intros(2) neq_Nil_conv)
        then show ?thesis by simp
      next
        case False
        have "length xs > 1"
          by (meson False f1 length_0_conv less_one linorder_neqE_nat)
        then obtain xs' where o1: "y#(xs')=xs"
          by (metis Cons.prems(1) f1 list.set_intros(1) list.set_intros(2) neq_Nil_conv)
        obtain xs'' where o2: "y#xs''=xs'"
          by (metis Cons.prems(1) False One_nat_def length_0_conv length_Cons list.set_intros(1) list.set_intros(2) neq_Nil_conv o1)
        obtain xs''' where o3: "y#y#xs'''=xs" using o1 o2 by auto
        have "\<Union>\<^sub>p (y#y#xs''') = (y \<union>\<^sub>p y) \<union>\<^sub>p \<Union>\<^sub>p xs'''"
          by (metis Choice_prop_1_2 Choice_prop_22 choice_assoc_1 list.discI)
        then show ?thesis
          by (metis Choice_prop_1_2 Cons.IH Cons.prems(1) Cons.prems(3) Cons.prems(4) One_nat_def \<open>1 < length xs\<close> choice_assoc_1 choice_idem_2 f1 insert_absorb linorder_not_less list.set_intros(1) list.simps(15) o3)
      qed
    qed
  next
    case False
    then show ?thesis using Cons by auto
  qed
qed

theorem Choice_prop_24: "distinct xs \<Longrightarrow> distinct ys \<Longrightarrow> set xs = set ys \<Longrightarrow> size xs = size ys \<Longrightarrow> \<Union>\<^sub>p xs = \<Union>\<^sub>p ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  obtain a b where o1: "ys=a@x#b"
    by (metis Cons.prems(3) in_set_conv_decomp list.set_intros(1))
  obtain ys' where o2: "a@b=ys'" by simp
  have l1: "\<Union>\<^sub>p (a@x#b) = \<Union>\<^sub>p (x#a@b)"
    by (metis Choice_prop_1_3 Nil_is_append_conv append_self_conv2)
  have "distinct xs"
    using Cons.prems(1) by auto
  have "distinct ys'" using Cons o1 o2 by auto
  have "set xs = set ys'" using Cons o1 o2 apply simp
    by (metis Un_iff Un_insert_right distinct.simps(2) distinct_append insert_ident list.simps(15) set_append)
  have "\<Union>\<^sub>p ys' = \<Union>\<^sub>p xs"
    by (metis Cons.IH \<open>distinct xs\<close> \<open>distinct ys'\<close> \<open>set xs = set ys'\<close> distinct_card)
  then show ?case
  proof (cases "xs=[]")
    case True
    then show ?thesis using Cons apply simp
      by (metis Choice_prop_5 One_nat_def)
  next
    case False
    then show ?thesis
      by (metis Choice_prop_1_2 Cons.prems(4) Nil_is_append_conv \<open>\<Union>\<^sub>p ys' = \<Union>\<^sub>p xs\<close> append_self_conv2 length_0_conv length_Cons local.l1 nat.inject o1 o2) 
  qed
qed

theorem atomic_prop_1: "finite F \<Longrightarrow> \<forall>x \<in> F. is_atomic x \<Longrightarrow> get_atomic (\<Union>\<^sub>p (set_to_list F)) = F"
proof (induction F rule: "finite_induct")
  case empty
  then show ?case apply (auto simp: set_to_list_def)
    by (metis (mono_tags, lifting) Choice.simps(1) distinct.simps(1) empty_iff fail_atomic someI_ex)
next
  case (insert x F)
  then have IH: "get_atomic (\<Union>\<^sub>p (set_to_list F)) = F"
    by simp
  from insert show "get_atomic (\<Union>\<^sub>p (set_to_list (insert x F))) = insert x F"
  proof (cases "F={}")
    case True
    have "set_to_list {x} = [x]"
      by (simp add: set_to_list_one)
    have "\<Union>\<^sub>p (set_to_list {x}) = x"
      by (simp add: \<open>set_to_list {x} = [x]\<close>)
    moreover have "is_atomic x"
      by (simp add: insert.prems)
    ultimately show ?thesis using True apply simp
      using atomic_prop_1 by auto
  next
    case f1: False
    obtain a b where o1: "a@x#b = set_to_list (insert x F)"
      by (meson insert.hyps(1) set_list_prop)
    have "set a \<union> set b = F" using o1
      by (smt (verit) UnE Un_insert_right disjoint_iff_not_equal distinct.simps(2) distinct_append finite.insertI insert.hyps(1) insert.hyps(2) insert_eq_iff list.set_intros(1) list.simps(15) set_append set_list_set set_to_list_distinct)
    then have "set (a@b) = F"
      by simp
    have d1: "distinct a" using o1 apply (auto simp: set_to_list_def)
      using distinct_append o1 set_to_list_distinct by blast
    have d2: "distinct b" using o1 apply (auto simp: set_to_list_def)
      by (metis distinct.simps(2) distinct_append o1 set_to_list_distinct)
    have "set a \<inter> set b = {}" using o1
      by (metis Int_insert_right_if0 UnI1 \<open>set a \<union> set b = F\<close> distinct_append insert.hyps(2) list.simps(15) set_to_list_distinct)
    have "distinct (a@b)"
      by (simp add: \<open>set a \<inter> set b = {}\<close> d1 d2)
    have "size (a@b) = size (set_to_list F)"
      by (metis \<open>distinct (a @ b)\<close> \<open>set (a @ b) = F\<close> distinct_card set_to_list_size)
    then have "\<Union>\<^sub>p (a@b) = \<Union>\<^sub>p (set_to_list F)"
      by (metis Choice_prop_24 \<open>distinct (a @ b)\<close> \<open>set (a @ b) = F\<close> insert.hyps(1) set_list_set set_to_list_distinct)
    have "\<Union>\<^sub>p (set_to_list (insert x F)) = x \<union>\<^sub>p \<Union>\<^sub>p (set_to_list F)"
      by (metis Choice_prop_1_3 \<open>\<Union>\<^sub>p (a @ b) = \<Union>\<^sub>p (set_to_list F)\<close> \<open>set (a @ b) = F\<close> empty_set f1 o1)
    have "get_atomic (\<Union>\<^sub>p (set_to_list (insert x F))) = get_atomic (x \<union>\<^sub>p \<Union>\<^sub>p (set_to_list F))"
      by (simp add: \<open>\<Union>\<^sub>p (set_to_list (insert x F)) = x \<union>\<^sub>p \<Union>\<^sub>p (set_to_list F)\<close>)
    have "... = insert x (get_atomic (\<Union>\<^sub>p (set_to_list F)))"
      by (metis IH UnCI atomic_prop_1 atomic_split finite.emptyI finite_insert insert.hyps(1) insert.prems insert_is_Un singletonI)
    have "... = insert x F"
      by (simp add: IH)
    then show "get_atomic (\<Union>\<^sub>p (set_to_list (insert x F))) = insert x F"
      by (simp add: \<open>get_atomic (\<Union>\<^sub>p (set_to_list (insert x F))) = get_atomic (x \<union>\<^sub>p \<Union>\<^sub>p (set_to_list F))\<close> \<open>get_atomic (x \<union>\<^sub>p \<Union>\<^sub>p (set_to_list F)) = insert x (get_atomic (\<Union>\<^sub>p (set_to_list F)))\<close>)
  qed
qed

theorem decomp_programs:
  assumes "Pre a = Pre p - {y}"
  and "post b = {t. t \<in> post p \<and> (fst t=y \<or> snd t=y)}"
  and "Pre b = Pre p \<inter> ({y} \<union> Domain (post p \<setminus>\<^sub>r {y}))"
  and "post a = {t. t \<in> post p \<and> (fst t \<noteq> y \<and> snd t \<noteq> y)}"
shows "a \<union>\<^sub>p b \<equiv>\<^sub>p p"
proof -
  have l1: "Pre a \<union> Pre b = Pre p"
    by (metis Int_Un_distrib Int_Un_eq(3) Un_Diff_Int Un_assoc assms(1) assms(3))
  have l2: "post a \<union> post b = post p" using assms (2) assms (4) by auto
  have "restr_post a \<union> restr_post b \<subseteq> restr_post p" apply (auto simp: restr_post_def restrict_r_def)
    using \<open>Pre a \<union> Pre b = Pre p\<close> apply auto using l1 l2 by (auto simp: Un_def)
  have l3: "\<forall>r. r \<in> restr_post p \<and> (fst r \<noteq> y \<and> snd r \<noteq> y) \<longrightarrow> r \<in> restr_post a" using assms(4) assms(1) by (auto simp: restr_post_def restrict_r_def)
  have l4: "\<forall>r. r \<in> restr_post p \<and> (fst r = y \<or> snd r = y) \<longrightarrow> r \<in> restr_post b" using assms(2) assms(3) by (auto simp: restr_post_def restrict_r_def corestrict_r_def)
  have "restr_post p \<subseteq> restr_post a \<union> restr_post b" using l3 l4 by auto
  show "a \<union>\<^sub>p b \<equiv>\<^sub>p p" apply (auto simp: equiv_def)
    using local.l1 apply auto[1]
    apply (simp add: assms(3))
    using local.l1 apply auto[1]
    apply (metis \<open>restr_post a \<union> restr_post b \<subseteq> restr_post p\<close> choice_idem_2 choice_post_2 le_sup_iff subsetD)
    using \<open>restr_post p \<subseteq> restr_post a \<union> restr_post b\<close> char_rel_choice char_rel_def restr_post_def by blast
qed

theorem "is_feasible p \<Longrightarrow> finite (S p) \<Longrightarrow> \<exists>xs. \<Union>\<^sub>p xs \<equiv>\<^sub>p p \<and> (\<forall>x \<in> set xs. is_atomic x)"
proof -
  assume a1: "finite (S p)"
  assume a2: "is_feasible p"
  have l1: "finite (post p)"
    by (metis S_def a1 finite_Un finite_relation)
  from l1 show "finite (S p) \<Longrightarrow> is_feasible p \<Longrightarrow> \<exists>xs. \<Union>\<^sub>p xs \<equiv>\<^sub>p p \<and> (\<forall>x\<in>set xs. is_atomic x)"
    using l1 proof (induction "post p" arbitrary: p rule: "finite_induct")
    case empty
  then show ?case using a2 apply (auto simp: equiv_def restr_post_def restrict_r_def is_feasible_def)
    by (metis Choice.simps(1) empty_iff empty_prop2 empty_set fail_atomic fail_is_feasible)
next
  case (insert x F)
  then show ?case
  proof (cases "fst x \<in> Pre p")
    case t1: True
    then show ?thesis
    proof (cases "fst x \<in> Domain F")
      case True
      obtain p' where o1: "p' = \<lparr>State=State p, Pre=Pre p, post=F\<rparr>" by simp
      have "F = post p' \<and> finite (S p') \<and> finite (post p') \<and> is_feasible p'" using o1 True insert(6) apply (auto simp: is_feasible_def)
        apply (metis Program.select_convs(1) Program.select_convs(2) Program.select_convs(3) S_def finite_Field finite_Un insert.hyps(1) insert.prems(1))
        using insert.hyps(1) apply auto
        by (metis (no_types, opaque_lifting) Domain_insert fst_conv insert.hyps(4) insert_absorb insert_subset surj_pair)
      obtain xs where o2: "\<Union>\<^sub>p xs \<equiv>\<^sub>p p' \<and> (\<forall>x\<in>set xs. is_atomic x)"
        using \<open>F = post p' \<and> finite (S p') \<and> finite (post p') \<and> is_feasible p'\<close> insert.hyps(3) by blast
      obtain p'' where o3: "p'' = \<lparr>State={fst x, snd x}, Pre={fst x}, post={x}\<rparr>" by simp
      have "is_atomic p''" using o3 by (auto simp: is_atomic_def S_def Field_def)
      have l3: "\<forall>r. r \<in> restr_post p \<and> r=x \<longrightarrow> r \<in> restr_post p''"
        using \<open>is_atomic p''\<close> atomic_post o3 singletonI by force
      have l4: "\<forall>r. r \<in> restr_post p \<and> r\<noteq>x \<longrightarrow> r \<in> restr_post p'" using o1 apply (auto simp: restr_post_def restrict_r_def)
        using insert.hyps(4) by blast
      have "restr_post p \<subseteq> restr_post p' \<union> restr_post p''" using l3 l4 by auto
      have "restr_post p' \<subseteq> restr_post p" using o1 apply (auto simp: restr_post_def restrict_r_def)
        using insert.hyps(4) by auto
      have "restr_post p'' = {x}"
        by (metis Program.select_convs(3) \<open>is_atomic p''\<close> atomic_post o3)
      have "{x} \<subseteq> restr_post p" using o3 apply (auto simp: restr_post_def restrict_r_def)
        using insert.hyps(4) apply blast
        by (simp add: t1)
      have "p' \<union>\<^sub>p p'' \<equiv>\<^sub>p p" using o1 o3 True apply (auto simp: equiv_def restr_post_def restrict_r_def t1)
        using insert.hyps(4) apply auto
        using t1 apply auto
        by (metis insert_iff split_pairs)
      then have "p'' \<union>\<^sub>p \<Union>\<^sub>p (xs) \<equiv>\<^sub>p p" using o2 apply auto
        using choice_equiv equiv_is_reflexive equiv_is_transitive by blast
      then have "\<Union>\<^sub>p (p''#xs) \<equiv>\<^sub>p p"
        by (metis Choice.simps(1) Choice_prop_1_2 Definitions.equiv_def Fail_def Program.select_convs(2) empty_iff o1 o2 t1)
      then show ?thesis
        by (metis \<open>is_atomic p''\<close> o2 set_ConsD) 
    next
      case False
      obtain p' where o1: "p' = \<lparr>State=State p, Pre=Pre p - {fst x}, post=F\<rparr>" by simp
      have "F = post p'"
        by (simp add: o1)
      have "finite (S p')"
        by (metis Program.select_convs(1) Program.select_convs(2) S_def \<open>F = post p'\<close> finite.emptyI finite.insertI finite_Diff2 finite_Field finite_Un insert.hyps(1) insert.prems(1) o1)
      have "finite (post p')"
        using \<open>F = post p'\<close> insert.hyps(1) by auto
      have "Pre p \<subseteq> Domain (insert x F)"
        by (metis insert.hyps(4) insert.prems(2) is_feasible_def)
      then have "Pre p - {fst x} \<subseteq> Domain F" by auto
      then have "Pre p' \<subseteq> Domain F" using o1 insert(6) by (simp add: is_feasible_def)
      then have "is_feasible p'" using o1 t1 False insert by (auto simp: is_feasible_def)
      obtain xs where o2: "\<Union>\<^sub>p xs \<equiv>\<^sub>p p' \<and> (\<forall>x\<in>set xs. is_atomic x)"
        using \<open>F = post p'\<close> \<open>finite (S p')\<close> \<open>finite (post p')\<close> \<open>is_feasible p'\<close> insert.hyps(3) by auto
      obtain p'' where o3: "p'' = \<lparr>State={fst x, snd x}, Pre={fst x}, post={x}\<rparr>" by simp
      have "is_atomic p''" using o3 by (auto simp: is_atomic_def S_def Field_def)
      have l3: "\<forall>r. r \<in> restr_post p \<and> r=x \<longrightarrow> r \<in> restr_post p''"
        using \<open>is_atomic p''\<close> atomic_post o3 singletonI by force
      have l4: "\<forall>r. r \<in> restr_post p \<and> r\<noteq>x \<longrightarrow> r \<in> restr_post p'" using o1 apply (auto simp: restr_post_def restrict_r_def)
        using insert.hyps(4) apply blast
        using False insert.hyps(4) by auto
      have "restr_post p \<subseteq> restr_post p' \<union> restr_post p''" using l3 l4 by auto
      have "restr_post p' \<subseteq> restr_post p" using o1 apply (auto simp: restr_post_def restrict_r_def)
        using insert.hyps(4) by auto
      have "restr_post p'' = {x}"
        by (metis Program.select_convs(3) \<open>is_atomic p''\<close> atomic_post o3)
      have "{x} \<subseteq> restr_post p" using o3 apply (auto simp: restr_post_def restrict_r_def)
        using insert.hyps(4) apply blast
        by (simp add: t1)
      have "p' \<union>\<^sub>p p'' \<equiv>\<^sub>p p" using o1 o3 t1 apply (auto simp: equiv_def restr_post_def restrict_r_def t1)
        using o1 o3 t1 apply auto
        using insert.hyps(4) False apply auto
        by (metis fst_conv insertE)
      then have "p'' \<union>\<^sub>p \<Union>\<^sub>p (xs) \<equiv>\<^sub>p p" using o2 apply auto
        using choice_equiv equiv_is_reflexive equiv_is_transitive by blast
      then have "\<Union>\<^sub>p (p''#xs) \<equiv>\<^sub>p p"
        by (metis Choice_prop_16 Choice_prop_22 choice_commute choice_idem_2 equiv_is_transitive list.set_intros(1))
      then show ?thesis
        by (metis \<open>is_atomic p''\<close> o2 set_ConsD) 
    qed
  next
    case False
    obtain p' where o1: "p' = \<lparr>State=State p, Pre=Pre p, post=F\<rparr>" by simp
    have "x \<notin> restr_post p" using False insert(4) by (auto simp: restr_post_def restrict_r_def)
    have "F = post p' \<and> finite (S p') \<and> finite (post p') \<and> is_feasible p'" using o1 False insert(6) apply (auto simp: is_feasible_def)
      apply (metis Program.select_convs(1) Program.select_convs(2) Program.select_convs(3) S_def finite_Field finite_Un insert.hyps(1) insert.prems(1))
      apply (simp add: insert.hyps(1))
      by (metis Domain_insert fst_conv insert.hyps(4) insertE old.prod.exhaust subset_iff)
    obtain xs where o2: "\<Union>\<^sub>p xs \<equiv>\<^sub>p p' \<and> (\<forall>x\<in>set xs. is_atomic x)"
      using \<open>F = post p' \<and> finite (S p') \<and> finite (post p') \<and> is_feasible p'\<close> insert.hyps(3) by blast
    have l4: "\<forall>r. r \<in> restr_post p \<and> r\<noteq>x \<longrightarrow> r \<in> restr_post p'" using o1 apply (auto simp: restr_post_def restrict_r_def)
      using insert.hyps(4) by blast
    have "restr_post p \<subseteq> restr_post p'" using l3 l4
      using \<open>x \<notin> restr_post p\<close> by auto 
    have "restr_post p' \<subseteq> restr_post p" using o1 apply (auto simp: restr_post_def restrict_r_def)
      using insert.hyps(4) by auto
    have "p' \<equiv>\<^sub>p p"
      by (metis Definitions.equiv_def Program.select_convs(2) \<open>restr_post p \<subseteq> restr_post p'\<close> \<open>restr_post p' \<subseteq> restr_post p\<close> dual_order.eq_iff o1)
    then show ?thesis
      using equiv_is_transitive o2 by blast
  qed
qed
qed




theorem civilized_finite: "civilized_n x B n \<Longrightarrow> finite B"
  apply (induction n)
  by auto

theorem civilized_ind: "civilized_n x B n \<Longrightarrow> civilized_n x B (Suc n)"
  apply (induction n) by auto

theorem civilized_ind2: "\<And>m. n\<le>m \<Longrightarrow> civilized_n x B n \<Longrightarrow> civilized_n x B m"
  apply (induction n) apply auto [1]
  apply (simp add: nat_induct)
  apply (simp add: nat_induct)
  by (metis civilized_ind nat_induct_at_least)

theorem civilized_generic: "civilized_n x B n = ((\<exists>a b m m'. m<n \<and> m'<n \<and> civilized_n a B m \<and> civilized_n b B m' \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x)) \<and> finite B) \<or> civilized_n x B 0"
proof (induction n arbitrary: x B rule: less_induct)
  case (less n)
  assume IH: "\<And>n' x B. n' < n \<Longrightarrow> civilized_n x B n' = ((\<exists>a b m m'. m < n' \<and> m' < n' \<and> civilized_n a B m \<and> civilized_n b B m' \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x)) \<and> finite B) \<or> civilized_n x B 0"
  then show ?case
  proof (cases "n=0")
    case zero: True
    then show ?thesis by auto
  next
    case cons: False
    then show "civilized_n x B n = ((\<exists>a b m m'. m < n \<and> m' < n \<and> civilized_n a B m \<and> civilized_n b B m' \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x)) \<and> finite B) \<or> civilized_n x B 0"
    proof (cases "civilized_n x B 0")
      case is_atomic: True
      then show ?thesis by auto
    next
      case not_atomic: False
      have "civilized_n x B n = ((\<exists>a b m m'. m < n \<and> m' < n \<and> civilized_n a B m \<and> civilized_n b B m' \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x)) \<and> finite B)"
      proof (cases "finite B")
        case finite_b: True
        have "civilized_n x B n = (\<exists>a b m m'. m < n \<and> m' < n \<and> civilized_n a B m \<and> civilized_n b B m' \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x))"
        proof (cases "civilized_n x B n")
          case is_civil: True
          then show ?thesis 
          proof -
            have "((\<exists>a b. civilized_n a B (n-1) \<and> civilized_n b B (n-1) \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x)) \<and> finite B) \<or> civilized_n x B (n-1)"
              by (metis Suc_diff_1 civilized_n.simps(2) cons is_civil not_gr_zero)
            have "((\<exists>a b. civilized_n a B (n-1) \<and> civilized_n b B (n-1) \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x))) \<or> civilized_n x B (n-1)"
              using \<open>(\<exists>a b. civilized_n a B (n - 1) \<and> civilized_n b B (n - 1) \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x)) \<and> finite B \<or> civilized_n x B (n - 1)\<close> by auto
            show "civilized_n x B n = (\<exists>a b m m'. m < n \<and> m' < n \<and> civilized_n a B m \<and> civilized_n b B m' \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x))"
            proof (cases "civilized_n x B (n-1)")
              case True
              have "(\<exists>a b m m'. m < (n-1) \<and> m' < (n-1) \<and> civilized_n a B m \<and> civilized_n b B m' \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x))"
                using True cons diff_less less less_numeral_extra(1) not_atomic by blast
              then show ?thesis
                by (metis Suc_less_eq diff_less_Suc is_civil less_trans_Suc)
            next
              case False
              have "(\<exists>a b. civilized_n a B (n-1) \<and> civilized_n b B (n-1) \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x))"
                using False \<open>(\<exists>a b. civilized_n a B (n - 1) \<and> civilized_n b B (n - 1) \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x)) \<or> civilized_n x B (n - 1)\<close> by auto
              then show ?thesis
                by (metis cons diff_less is_civil less_numeral_extra(1) neq0_conv)
            qed
          qed
        next
          case not_civil: False
          have "\<not>(((\<exists>a b. civilized_n a B (n-1) \<and> civilized_n b B (n-1) \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x)) \<and> finite B) \<or> civilized_n x B (n-1))"
            by (metis Suc_diff_1 civilized_n.simps(2) cons not_civil not_gr_zero)
          then have l0: "\<not>(\<exists>a b. civilized_n a B (n-1) \<and> civilized_n b B (n-1) \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x))"
            using finite_b by argo
          have l1: "\<not>(\<exists>a b m m'. m < (n-1) \<and> m' < (n-1) \<and> civilized_n a B m \<and> civilized_n b B m' \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x))"
          proof -
            { fix pp :: "'a Program" and nn :: nat and ppa :: "'a Program" and nna :: nat
              have "\<And>n na. \<not> (n::nat) < 1 \<or> \<not> na < n \<or> (0::nat) < 0"
                by linarith
              moreover
              { assume "0 \<noteq> n"
                then have "n - 1 < n"
                  by simp
                then have "\<not> civilized_n pp B nn \<or> \<not> civilized_n ppa B nna \<or> \<not> nn < n - 1 \<or> \<not> nna < n - 1 \<or> pp \<union>\<^sub>p ppa \<noteq> x \<and> pp ; ppa \<noteq> x"
                  using \<open>\<not> ((\<exists>a b. civilized_n a B (n - 1) \<and> civilized_n b B (n - 1) \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x)) \<and> finite B \<or> civilized_n x B (n - 1))\<close> finite_b less not_atomic by blast }
              ultimately have "\<not> civilized_n pp B nn \<or> \<not> civilized_n ppa B nna \<or> \<not> nn < n - 1 \<or> \<not> nna < n - 1 \<or> pp \<union>\<^sub>p ppa \<noteq> x \<and> pp ; ppa \<noteq> x"
                by (metis less_imp_diff_less less_one not_gr_zero) }
            then show ?thesis
              by presburger
          qed
          have l2: "\<not>(\<exists>a b. civilized_n a B (n-1) \<and> civilized_n b B (n-1) \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x))" using not_civil finite_b
            using \<open>\<nexists>a b. civilized_n a B (n - 1) \<and> civilized_n b B (n - 1) \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x)\<close> by blast
          have "\<not>(\<exists>a b m m'. m < n \<and> m' < n \<and> civilized_n a B m \<and> civilized_n b B m' \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x))"
          proof (cases "(\<exists>a b m m'. m < n \<and> m' < n \<and> civilized_n a B m \<and> civilized_n b B m' \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x))")
            case contra: True
            obtain a b m m' where o1: "m < n \<and> m' < n \<and> civilized_n a B m \<and> civilized_n b B m' \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x)"
              using contra by auto
            have "civilized_n a B m" using o1 by auto
            moreover have "m < n" using o1 by auto
            moreover have "m \<le> (n-1)"
              using calculation(2) by auto
            ultimately have "civilized_n a B (n-1)" using civilized_ind2 by auto
            have "civilized_n b B m'" using o1 by auto
            moreover have "m' < n" using o1 by auto
            moreover have "m' \<le> (n-1)"
              using calculation(2) by auto
            ultimately have "civilized_n b B (n-1)" using civilized_ind2 by auto
            have "civilized_n a B (n-1) \<and> civilized_n b B (n-1) \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x)"
              using \<open>civilized_n a B (n - 1)\<close> \<open>civilized_n b B (n - 1)\<close> o1 by auto
            then have False using l0
              by blast
            then show ?thesis by simp
          next
            case False
            then show ?thesis by auto
          qed
          then show ?thesis using not_civil
            by blast
        qed
        then show ?thesis using finite_b by auto
      next
        case infinite_b: False
        then show ?thesis apply auto
          apply (induction n) by auto
      qed
      then show ?thesis using not_atomic by auto
    qed
  qed
qed



theorem civ_prop_1: "civilized_n p B n \<Longrightarrow> civilized p B"
  apply (auto simp: civilized_def)
  by (simp add: civilized_finite)

theorem civ_prop_2: "civilized p B \<Longrightarrow> civilized q B \<Longrightarrow> civilized (p;q) B" apply (auto simp: civilized_def)
  by (metis civilized_ind2 civilized_n.simps(2) nat_le_linear)

theorem civ_prop_3: "civilized p B \<Longrightarrow> civilized q B \<Longrightarrow> civilized (p \<union>\<^sub>p q) B" 
  apply (auto simp: civilized_def)
proof -
  fix x n
  assume a1: "civilized_n q B x"
  assume a2: "finite B"
  assume a3: "civilized_n p B n"
  have "civilized_n q B (x+n)"
    using a1 civilized_ind2 le_add1 by blast
  have "civilized_n p B (x+n)"
    using a3 civilized_ind2 le_add2 by blast
  have "civilized_n (p \<union>\<^sub>p q) B (Suc (x+n))"
    using \<open>civilized_n p B (x + n)\<close> \<open>civilized_n q B (x + n)\<close> a2 civilized_n.simps(2) by blast
  show "Ex (civilized_n (p \<union>\<^sub>p q) B)"
    using \<open>civilized_n (p \<union>\<^sub>p q) B (Suc (x + n))\<close> by blast
qed

theorem fold_prop: "foldl (\<union>) {} xs = {} \<Longrightarrow> t \<in> set xs \<Longrightarrow> t = {}"
  apply (induction xs arbitrary: t) apply auto
  apply (metis (no_types, opaque_lifting) all_not_in_conv simp_2 sup.idem sup_assoc sup_bot_right)
  by (metis (no_types, opaque_lifting) insert_absorb insert_not_empty simp_2 sup.idem sup_assoc sup_bot_right)

theorem fold_prop2: "x \<in> tr \<Longrightarrow> tr \<in> set xs \<Longrightarrow> foldl (\<union>) {} xs \<subseteq> B \<Longrightarrow> x \<in> B"
proof (induction xs arbitrary: x tr)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  have IH: "tr \<in> set xs \<Longrightarrow> foldl (\<union>) {} xs \<subseteq> B \<Longrightarrow> x \<in> B"
    using Cons.IH Cons.prems(1) Cons.prems(2) by auto
  have "foldl (\<union>) {} xs \<subseteq> B" using Cons(4) apply auto
    by (smt (z3) Cons.prems(3) Un_iff simp_2 sup.absorb_iff1 sup_assoc sup_commute sup_idem)
  have "a \<subseteq> B" using Cons(4)
  proof -
    assume "foldl (\<union>) {} (a # xs) \<subseteq> B"
    then have "foldl (\<union>) a (xs) \<subseteq> B" by auto
    then have "a \<union> foldl (\<union>) {} (xs) \<subseteq> B"
      by (metis simp_2 sup_assoc sup_bot_right)
    then show ?thesis
      by simp
  qed
  then show ?case
    proof (cases "tr \<in> set xs")
      case True
      then show ?thesis
        by (simp add: IH \<open>foldl (\<union>) {} xs \<subseteq> B\<close>)
    next
      case False
      have "tr = a"
        using Cons.prems(2) False by auto
      then show ?thesis
        using Cons.prems(1) \<open>a \<subseteq> B\<close> by blast
    qed
  qed

lemma normal_prop1: "set x \<subseteq> {p} \<Longrightarrow> \<exists>n. x = replicate n p"
  apply (induction x) apply auto
  by (metis replicate_Suc)

theorem normal_prop: "normal_of p B \<Longrightarrow> B = {} \<Longrightarrow> set p \<subseteq> {replicate n \<lparr>State={},Pre={},post={}\<rparr> | n. n \<ge> 0}"
proof
  fix x
  assume a1: "normal_of p B" and "B = {}" and "x \<in> set p"
  have "foldl (\<union>) {} (map set p) \<subseteq> {\<lparr>State={},Pre={},post={}\<rparr>}"
    using \<open>B = {}\<close> a1 basic_def normal_of_def by blast
  have "\<forall>x \<in> set (map set p). x \<subseteq> {\<lparr>State={},Pre={},post={}\<rparr>}"
    by (meson \<open>foldl (\<union>) {} (map set p) \<subseteq> {\<lparr>State = {}, Pre = {}, post = {}\<rparr>}\<close> fold_prop2 subsetI)
  then have "set x \<subseteq> {\<lparr>State={},Pre={},post={}\<rparr>}" apply auto
    using \<open>x \<in> set p\<close> by blast
  then show "x \<in> {replicate n \<lparr>State={},Pre={},post={}\<rparr> | n. n \<ge> 0}"
    by (simp add: normal_prop1)
qed

theorem basic_normal: "basic a = basic b \<Longrightarrow> normal_of a B = normal_of b B"
proof-
  assume "basic a = basic b"
  show "normal_of a B = normal_of b B"
  proof (cases "finite B")
    case finite_b: True
    then show ?thesis
    proof (induction B rule: finite_induct)
      case empty
      then show ?case apply (simp add: normal_of_def)
        using \<open>basic a = basic b\<close> by auto
    next
      case (insert x F)
      then show ?case apply (simp add: normal_of_def)
        by (simp add: \<open>basic a = basic b\<close>)
    qed
  next
    case False
    then show ?thesis by (simp add: normal_of_def)
  qed
qed

theorem basic_normal2: "basic a = insert (Fail {}) (basic b) \<Longrightarrow> normal_of a B = normal_of b B"
proof-
  assume "basic a = insert (Fail {}) (basic b)"
  show "normal_of a B = normal_of b B"
  proof (cases "finite B")
    case finite_b: True
    then show ?thesis
    proof (induction B rule: finite_induct)
      case empty
      then show ?case 
        apply (simp add: normal_of_def)
        by (simp add: Fail_def \<open>basic a = insert (Fail {}) (basic b)\<close>)
    next
      case (insert x F)
      then show ?case apply (simp add: normal_of_def)
        by (simp add: Fail_def \<open>basic a = insert (Fail {}) (basic b)\<close>)
    qed
  next
    case False
    then show ?thesis by (simp add: normal_of_def)
  qed
qed

theorem normal_prop2: "finite B \<Longrightarrow> normal_of [[]] B"
  by (auto simp: normal_of_def basic_def)

theorem normal_prop3: "finite B \<Longrightarrow> normal_of [[\<lparr>State = {}, Pre = {}, post = {}\<rparr>]] B"
  by (auto simp: normal_of_def basic_def)

theorem normal_prop4: "infinite B \<Longrightarrow> \<not>normal_of xs B"
  by (auto simp: normal_of_def)

theorem normal_prop5: "finite B \<Longrightarrow> normal_of xs B \<Longrightarrow> normal_of ([]#xs) B"
  apply (induction xs)
  by (auto simp: normal_of_def basic_def)

theorem normal_prop6: "finite B \<Longrightarrow> normal_of ([]#xs) B \<Longrightarrow> normal_of xs B"
  apply (induction xs)
  by (auto simp: normal_of_def basic_def)

theorem normal_prop7: "normal_of [x#xs] B = (normal_of [[x]] B \<and> normal_of [xs] B)"
  apply (cases "infinite B") by (auto simp: normal_of_def basic_def)

theorem basic_prop0: "basic [[x]] \<union> basic [xs] = basic [x#xs]"
  by (auto simp: basic_def)

theorem basic_prop1: "basic [x] \<union> basic xs = basic (x#xs)"
  apply (auto simp: basic_def)
  apply (metis UnCI simp_2 sup.idem sup_assoc)
  apply (metis (no_types, opaque_lifting) in_mono inf_sup_ord(4) simp_2 sup_assoc sup_bot_right)
  by (metis (mono_tags, lifting) UnE boolean_algebra.disj_zero_right boolean_algebra_cancel.sup1 simp_2)

theorem basic_prop2: "basic xs \<union> basic ys = basic (xs@ys)"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case apply (auto simp: basic_def) [1] done
next
  case (Cons a xs)
  then show "basic (a # xs) \<union> basic ys = basic ((a # xs) @ ys)"
    by (metis Cons_eq_appendI basic_prop1 local.Cons sup_assoc)
qed
  

theorem normal_prop8: "trace \<in> set xs \<Longrightarrow> normal_of xs B \<Longrightarrow> normal_of [trace] B"
proof -
  assume a1: "trace \<in> set xs"
  assume a2: "normal_of xs B"
  obtain B' where o2: "B' = insert \<lparr>State = {}, Pre = {}, post = {}\<rparr> B" by simp
  obtain a b where o1: "xs=a@trace#b"
    by (meson \<open>trace \<in> set xs\<close> split_list)
  have "basic (a@trace#b) \<subseteq> B'" using a2 o2 apply (auto simp: normal_of_def)
    using o1 by auto
  have "basic (a@trace#b) = basic a \<union> basic [trace] \<union> basic b"
    by (simp add: basic_prop2)
  show "normal_of [trace] B" apply (simp add: normal_of_def)
    using \<open>basic (a @ trace # b) = basic a \<union> basic [trace] \<union> basic b\<close> \<open>basic (a @ trace # b) \<subseteq> B'\<close> a2 normal_prop4 o2 by auto
qed

theorem normal_prop9: "normal_of ((a # x) # xs) B \<Longrightarrow> normal_of [[a]] B"
proof -
  assume a1: "normal_of ((a # x) # xs) B"
  then have "finite B"
    using normal_prop4 by auto
  then show ?thesis
  using a1 proof (induction B rule: finite_induct)
    case empty
    then show ?case 
      apply (auto simp: normal_of_def) 
      apply (induction xs) 
       apply (auto simp: basic_def) [1]
      by (smt (z3) Un_empty basic_prop1 singleton_Un_iff sup.absorb_iff2)
  next
    case (insert x F)
    then show ?case
      by (metis insertCI list.simps(15) normal_prop7 normal_prop8)
  qed
qed

theorem basic_prop3: "trace \<in> set xs \<Longrightarrow> basic [trace] \<subseteq> basic xs"
  apply (induction xs)
  apply simp
  using basic_prop1 by auto

theorem basic_prop4: "x \<in> set trace \<Longrightarrow> basic [[x]] \<subseteq> basic [trace]"
  apply (induction trace)
  apply simp
  using basic_prop0 by fastforce

theorem normal_prop10: "x \<in> set trace \<Longrightarrow> trace \<in> set xs \<Longrightarrow> normal_of xs B \<Longrightarrow> normal_of [[x]] B"
proof -
  assume "x \<in> set trace"
  assume "trace \<in> set xs"
  assume "normal_of xs B"
  then have "finite B" apply (auto simp: normal_of_def) done
  obtain B' where o1: "B' = insert \<lparr>State = {}, Pre = {}, post = {}\<rparr> B" by simp
  have "basic xs \<subseteq> B'"
    using \<open>normal_of xs B\<close> normal_of_def o1 by auto
  have "basic [trace] \<subseteq> basic xs"
    by (simp add: \<open>trace \<in> set xs\<close> basic_prop3)
  have "basic [[x]] \<subseteq> basic [trace]"
    by (simp add: \<open>x \<in> set trace\<close> basic_prop4)
  show "normal_of [[x]] B" apply (auto simp: normal_of_def)
    using \<open>basic [[x]] \<subseteq> basic [trace]\<close> \<open>basic [trace] \<subseteq> basic xs\<close> \<open>basic xs \<subseteq> B'\<close> o1 apply blast
    by (simp add: \<open>finite B\<close>)
qed

theorem normal_prop11: "normal_of ((a#x)#xs) B = (normal_of [[a]] B \<and> normal_of (x#xs) B)"
proof (cases "infinite B")
  case True
  then show ?thesis by (auto simp: normal_of_def)
next
  case False
  have "basic ((a # x) # xs) = (basic [[a]] \<union> basic (x # xs))"
    by (metis Un_assoc basic_prop0 basic_prop1)
  then show ?thesis
    by (metis le_sup_iff normal_of_def)
qed

theorem normal_prop12: "normal_of (x#xs) B = (normal_of [x] B \<and> normal_of xs B)"
proof (cases "infinite B")
  case infinite: True
  then show ?thesis by (auto simp: normal_of_def)
next
  case False
  then have finite: "finite B" by simp
  then show ?thesis
  proof (induction x arbitrary: B xs)
    case Nil
    then show ?case apply auto
      apply (simp add: normal_prop2)
      apply (simp add: normal_prop6)
      by (simp add: normal_prop5)
  next
    case (Cons a x)
    have "\<And>xs B. normal_of (x # xs) B = (normal_of [x] B \<and> normal_of xs B)"
      by (meson Cons.IH normal_prop4)
    have "(normal_of [a # x] B \<and> normal_of xs B) = ((normal_of [[a]] B \<and> normal_of [x] B) \<and> normal_of xs B)"
      using normal_prop7 by blast
    have "... = (normal_of [[a]] B \<and> normal_of (x#xs) B)"
      using \<open>\<And>xs B. normal_of (x # xs) B = (normal_of [x] B \<and> normal_of xs B)\<close> by blast
    then show "normal_of ((a # x) # xs) B = (normal_of [a # x] B \<and> normal_of xs B)" using normal_prop11
      by auto
  qed
qed

theorem normal_prop13: "normal_of (a#p) B = normal_of ((\<lparr>State = {}, Pre = {}, post = {}\<rparr>#a)#p) B"
proof -
  show "normal_of (a#p) B = normal_of ((\<lparr>State = {}, Pre = {}, post = {}\<rparr>#a)#p) B"
  proof (cases "finite B")
    case finite_B: True
    then show ?thesis
    proof (induction a arbitrary: p B)
      case Nil
      then show ?case apply (induction p) apply (auto simp: basic_def normal_of_def) [1]
        using normal_prop11 normal_prop3 by blast
    next
      case (Cons a as)
      then show ?case
        by (meson normal_prop11)
    qed
  next
    case False
    then show ?thesis apply auto
      apply (simp add: normal_of_def)
      by (simp add: normal_of_def)
  qed
qed

theorem fold_prop1: "trace \<in> set p \<Longrightarrow> x \<in> set trace \<Longrightarrow> x \<in> foldl (\<union>) {} (map set p)"
  apply (induction p arbitrary: trace x)
  apply simp
  by (smt (z3) UnCI foldl_Cons list.simps(9) set_ConsD simp_2 sup_assoc sup_commute)

theorem normal_prop14: "normal_of p B \<Longrightarrow> trace \<in> set p \<Longrightarrow> x \<in> set trace \<Longrightarrow> x \<in> insert (Fail {}) B"
proof -
  assume a1: "normal_of p B" assume a2: "trace \<in> set p" assume a3: "x \<in> set trace"
  have "finite B"
    using \<open>normal_of p B\<close> normal_prop4 by auto
  obtain B' where o1: "B' = insert \<lparr>State = {}, Pre = {}, post = {}\<rparr> B" by simp
  have "x \<in> basic p" using a2 a3 apply (auto simp: basic_def)
    by (simp add: fold_prop1)
  show ?thesis apply (simp add: Fail_def)
    by (metis (no_types, opaque_lifting) Un_empty_right Un_insert_right \<open>x \<in> basic p\<close> a1 in_mono insert_iff normal_of_def)
qed

lemma basic_monotone1: "basic a \<subseteq> basic (x#a)"
proof (auto simp: basic_def)
  fix y
  assume "y \<in> foldl (\<union>) {} (map set a)"
  have "foldl (\<union>) (set x) (map set a) = set x \<union> foldl (\<union>) {} (map set a)"
    by (metis simp_2 sup_assoc sup_bot_right)
  show "y \<in> foldl (\<union>) (set x) (map set a)"
    by (simp add: \<open>foldl (\<union>) (set x) (map set a) = set x \<union> foldl (\<union>) {} (map set a)\<close> \<open>y \<in> foldl (\<union>) {} (map set a)\<close>)
qed 

lemma basic_monotone2: "x \<in> set p \<Longrightarrow> basic [x] \<subseteq> basic p"
  apply (induction p)
  apply (auto simp: basic_def)
  apply (metis Un_iff simp_2 sup_assoc sup_bot_right)
  by (metis (no_types, opaque_lifting) basic_def basic_monotone1 foldl_Cons map_eq_Cons_conv subset_iff sup_bot_left)

lemma basic_decomp1: "basic [x] \<union> basic xs = basic (x#xs)"
  apply (induction xs)
  apply (auto simp: basic_def)
  apply (simp add: simp_2 sup_assoc)
  apply (simp add: simp_2 sup_assoc)
  by (simp add: simp_2 sup_assoc)

lemma basic_decomp2: "basic [x] \<union> basic xs = basic (xs@[x])"
  apply (induction xs)
  by (auto simp: basic_def)

lemma fold_prop3: "foldl (\<union>) (foldl (\<union>) {} xs) ys = foldl (\<union>) {} xs \<union> foldl (\<union>) {} ys"
  apply auto
  apply (smt (verit) simp_2 subset_Compl_singleton sup.absorb_iff1 sup_assoc sup_bot_right)
  apply (smt (verit) Un_iff simp_2 sup_assoc sup_commute)
  by (metis insert_absorb insert_subset simp_2 sup.cobounded2 sup_assoc sup_bot_right)

theorem basic_decomp: "basic a \<union> basic b = basic (a@b)"
  apply (auto simp: basic_def)
  apply (simp add: fold_prop3)
  apply (simp add: fold_prop3)
  by (simp add: fold_prop3)

theorem basic_monotone: "set a \<subseteq> set b \<Longrightarrow> basic a \<subseteq> basic b"
proof (induction a arbitrary: b)
  case Nil
  then show ?case by (auto simp: basic_def)
next
  case (Cons x a)
  have "x \<in> set b" using Cons(2) by auto
  have "basic a \<subseteq> basic b"
    using Cons.IH Cons.prems by auto
  have "basic [x] \<subseteq> basic b" using Cons(2) \<open>x \<in> set b\<close> apply auto
    apply (induction b) apply auto
    apply (meson basic_monotone2 list.set_intros(1) subset_iff)
    by (metis Diff_insert_absorb basic_monotone1 basic_monotone2 subset_Diff_insert)
  then show ?case
    by (metis Un_least \<open>basic a \<subseteq> basic b\<close> basic_decomp1)
qed

theorem basic_prop: "basic (a@b) \<subseteq> B \<Longrightarrow> basic b \<subseteq> B"
proof -
  assume "basic (a@b) \<subseteq> B"
  have "basic b \<subseteq> basic (a@b)"
    by (simp add: basic_monotone)
  show ?thesis
    using \<open>basic (a @ b) \<subseteq> B\<close> \<open>basic b \<subseteq> basic (a @ b)\<close> by auto
qed

theorem basic_prop5: "basic (a@b) \<subseteq> B \<Longrightarrow> basic a \<subseteq> B"
proof -
  assume "basic (a@b) \<subseteq> B"
  have "basic a \<subseteq> basic (a@b)"
    by (simp add: basic_monotone)
  show ?thesis
    using \<open>basic (a @ b) \<subseteq> B\<close> \<open>basic a \<subseteq> basic (a @ b)\<close> by auto
qed

theorem basic_monotone3: "basic [a] \<subseteq> basic [a@b]"
  apply (induction b) by (auto simp: basic_def)

theorem basic_monotone4: "basic [b] \<subseteq> basic [a@b]"
  apply (induction b) by (auto simp: basic_def)

theorem basic_monotone5: "basic [b] \<union> basic [a] = basic [a@b]"
  apply (induction b) by (auto simp: basic_def)

theorem civilized_empty1: "finite B \<Longrightarrow> civilized_n (Concat []) B 0" by (auto simp: Skip_def Fail_def)
theorem civilized_empty2: "finite B \<Longrightarrow> civilized_n (\<Union>\<^sub>p []) B 0" by (auto simp: Skip_def Fail_def)
theorem civilized_empty3: "finite B \<Longrightarrow> civilized_n (Fail {}) B 0" by (auto simp: Skip_def Fail_def)
theorem civilized_empty4: "finite B \<Longrightarrow> civilized_n (Skip {}) B 0" by (auto simp: Skip_def Fail_def)

theorem normal_civilized: "normal_of p B \<Longrightarrow> civilized (evaluate p) B"
proof -
  assume a0: "normal_of p B"
  show "normal_of p B \<Longrightarrow> civilized (evaluate p) B"
  apply (auto simp: civilized_def evaluate_def)
  proof -
    obtain B' where o0: "B' = insert (Fail{}) B" by simp
    assume a0: "normal_of p B"
    have a1: "basic p \<subseteq> B'" using a0 apply auto
      using normal_of_def o0 apply (auto simp: Fail_def) done
    have a2: "finite B" using a0
      by (simp add: normal_of_def)
    from a1 have "\<forall>x \<in> set p. civilized (Concat x) B" 
      apply auto
    proof -
      fix trace 
      assume "trace \<in> set p"
      show "civilized (Concat trace) B"
    proof (cases "p = []")
      case True
      then show "civilized (Concat trace) B"
        using \<open>trace \<in> set p\<close> by auto
    next
      case False
      then have l0: "set trace \<subseteq> B'" using a1 apply (auto simp: basic_def)
        using a0 a1 a2
        by (metis \<open>trace \<in> set p\<close> normal_prop14 o0)
      \<comment> \<open>have l1: "trace \<noteq> []" using \<open>trace \<in> set p\<close> a0 normal_of_def by auto\<close>
      from l0 show "civilized (Concat trace) B" apply (auto simp: civilized_def basic_def)
      proof (induction trace)
        case Nil
        have "civilized_n (Skip {}) B 0" apply (auto simp: Skip_def Fail_def)
          by (simp add: a2)
        then show ?case apply auto
          using \<open>civilized_n (Skip {}) B 0\<close> apply blast
          by (metis \<open>civilized_n (Skip {}) B 0\<close>)
      next
        case (Cons a trace)
        then show ?case
        proof (cases "trace = []")
          case True
          have "civilized_n a B 0" apply auto
            using Cons.prems(1) apply auto[1]
            apply (simp add: o0)
            by (simp add: a2)
          then show ?thesis apply auto
            apply (metis Concat.simps(2) True \<open>civilized_n a B 0\<close>)
            by (metis Concat.simps(2) True \<open>civilized_n a B 0\<close>)
        next
          case False
          have "Concat (a # trace) = a ; Concat (trace)"
            by (simp add: Concat_prop_10 False)
          have "civilized_n a B 0"
            using Cons.prems(1) a2 o0 by auto
          obtain n where "civilized_n (Concat trace) B n"
            using Cons.IH Cons.prems(1) False by auto
          then show ?thesis
            by (metis \<open>Concat (a # trace) = a ; Concat trace\<close> \<open>civilized_n a B 0\<close> civ_prop_1 civ_prop_2 civilized_def)
        qed
      next
        show "finite B"
          by (simp add: a2)
      qed
    qed
  qed
  show lem_p: "normal_of p B \<Longrightarrow> Ex (civilized_n (\<Union>\<^sub>p (map Concat p)) B)"
  proof (induction p)
    case Nil
    then show ?case apply auto
      by (meson a2 civilized_n.simps(1))
  next
    case (Cons a p)
    have "basic (a # p) \<subseteq> B'"
      using Cons.prems normal_of_def o0
      by (metis Fail_def Un_absorb2 Un_insert_right empty_subsetI)
    have "basic p \<subseteq> basic (a # p)"
      by (simp add: basic_monotone1)
    have l1: "basic [a] \<subseteq> B'"
      using \<open>basic (a # p) \<subseteq> B'\<close> basic_decomp1 by auto
    have "basic p \<subseteq> B'" using Cons(2) apply (simp add: basic_def) apply auto
      using Cons.prems \<open>basic p \<subseteq> basic (a # p)\<close> basic_def
      using \<open>basic (a # p) \<subseteq> B'\<close> by auto
    obtain n where "civilized_n (\<Union>\<^sub>p (map Concat p)) B n"
      using Cons.IH Cons.prems normal_prop12 by auto
    have "map Concat [a] = [Concat a]" by auto
    have "\<Union>\<^sub>p (map Concat [a]) = \<Union>\<^sub>p [Concat a]" by simp
    have "... = Concat a" by simp
    then have lem_a: "\<exists>m. civilized_n (Concat a) B m"
    using l1 proof (induction a)
      case Nil
      then show ?case
        using a2 civilized_empty1 by blast
    next
      case (Cons a' as)
      then have "civilized_n a' B 0" using Cons(3) apply (auto simp: basic_def) using a2 o0 by auto
      from Cons(3) have "basic [as] \<subseteq> B'"
      proof -
        assume "basic [a' # as] \<subseteq> B'"
        have "basic [as] \<subseteq> basic [a' # as]" using basic_monotone3 apply auto
          by (smt (verit, del_insts) Cons_eq_appendI append_self_conv2 basic_decomp2 basic_monotone5 basic_prop dual_order.refl in_mono)
        show "basic [as] \<subseteq> B'"
          using Cons.prems(2) \<open>basic [as] \<subseteq> basic [a' # as]\<close> by auto
      qed
      then show ?case
      proof (cases "as = []")
        case True
        then show ?thesis using Cons(3) apply (auto simp: basic_def)
          by (metis \<open>civilized_n a' B 0\<close>)
      next
        case False
        from Cons obtain n where "civilized_n (Concat as) B n" using False apply auto
          using \<open>basic [as] \<subseteq> B'\<close> by auto
        have "Concat (a' # as) = a' ; Concat as"
          by (simp add: Concat_prop_10 False)
        then show ?thesis
          by (metis \<open>civilized_n (Concat as) B n\<close> \<open>civilized_n a' B 0\<close> civ_prop_1 civ_prop_2 civilized_def)
      qed
    qed
    have lem_p: "\<exists>b. civilized_n (\<Union>\<^sub>p (map Concat p)) B b"
      using \<open>\<And>thesis. (\<And>n. civilized_n (\<Union>\<^sub>p (map Concat p)) B n \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast
    obtain m where o1: "civilized_n (Concat a) B m"
      using lem_a by auto
    obtain n where o2: "civilized_n (\<Union>\<^sub>p (map Concat p)) B n"
      using \<open>\<And>thesis. (\<And>n. civilized_n (\<Union>\<^sub>p (map Concat p)) B n \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by auto
    show ?case
    proof (cases "p = []")
      case True
      then show ?thesis apply auto
        by (meson \<open>\<And>thesis. (\<And>m. civilized_n (Concat a) B m \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>)
    next
      case False
      have "\<Union>\<^sub>p (map Concat (a # p)) = Concat a \<union>\<^sub>p \<Union>\<^sub>p (map Concat (p))"
        by (simp add: Choice_prop_1_2 False)
      have "civilized (Concat a \<union>\<^sub>p \<Union>\<^sub>p (map Concat (p))) B" using o1 o2 civ_prop_1 civ_prop_3
        by blast
      then show ?thesis
        using \<open>\<Union>\<^sub>p (map Concat (a # p)) = Concat a \<union>\<^sub>p \<Union>\<^sub>p (map Concat p)\<close> civilized_def by auto
    qed
  qed
next
  show "finite B"
    using a0 normal_of_def by auto
qed
qed

theorem concat_prop1: "evaluate ([] ;\<^sub>c b) = Fail {}"
  by (auto simp: evaluate_def composition_cnf_def non_empty_def)
  
  
theorem concat_prop2: "evaluate [] = Fail {}"
  by (auto simp: Fail_def evaluate_def)

theorem concat_prop3: "xs \<noteq> [] \<Longrightarrow> evaluate (x#xs) = evaluate [x] \<union>\<^sub>p evaluate xs"
proof (auto simp: evaluate_def)
  assume False: "xs \<noteq> []"
    have "\<Union>\<^sub>p (Concat x # map Concat xs) = \<Union>\<^sub>p (map Concat (x#xs))"
      by simp
    have "... = Concat x \<union>\<^sub>p \<Union>\<^sub>p (map Concat xs)"
      using Choice_prop_1_2 False by auto
    show "\<Union>\<^sub>p (Concat x # map Concat xs) = Concat x \<union>\<^sub>p \<Union>\<^sub>p (map Concat xs)"
      using \<open>\<Union>\<^sub>p (map Concat (x # xs)) = Concat x \<union>\<^sub>p \<Union>\<^sub>p (map Concat xs)\<close> equiv_is_reflexive by auto
  qed

theorem concat_prop4: "evaluate (x#xs) \<equiv>\<^sub>p evaluate [x] \<union>\<^sub>p evaluate xs"
proof (cases "xs=[]")
  case True
  then show ?thesis apply (auto simp: evaluate_def)
    by (simp add: equiv_is_symetric fail_choice_r)
next
  case False
  then show ?thesis
    using concat_prop3 equals_equiv_relation_3 by blast
qed

theorem fail_compose: "Fail {} ; p \<equiv>\<^sub>p Fail {}" by (auto simp: equiv_def composition_def restr_post_def Fail_def)

theorem concat_prop5: "evaluate (a@b) \<equiv>\<^sub>p evaluate a \<union>\<^sub>p evaluate b"
  apply (induction a arbitrary: b)
  apply auto
  apply (simp add: concat_prop2 equiv_is_symetric fail_choice_l)
  by (smt (verit) Nil_is_append_conv append_self_conv2 choice_assoc_1 choice_commute choice_equiv concat_prop3 equals_equiv_relation_3)

theorem concat_prop6: "evaluate ([]#xs) \<equiv>\<^sub>p evaluate xs"
proof (induction xs)
  case Nil
  then show ?case apply (auto simp: evaluate_def Fail_def Skip_def equiv_def) done
next
  case (Cons a xs)
  have "evaluate (a # xs) \<equiv>\<^sub>p evaluate (xs) \<union>\<^sub>p evaluate [a]"
    using concat_prop4 by auto
  moreover have "... \<equiv>\<^sub>p evaluate ([]#xs) \<union>\<^sub>p evaluate [a]"
    by (simp add: choice_equiv equiv_is_reflexive equiv_is_symetric local.Cons)
  moreover have "... \<equiv>\<^sub>p (evaluate [[]] \<union>\<^sub>p evaluate (xs)) \<union>\<^sub>p evaluate [a]"
    using choice_equiv concat_prop4 equiv_is_reflexive by blast
  ultimately show ?case using equiv_is_transitive
    by (smt (verit, del_insts) choice_assoc_1 choice_commute concat_prop3 equiv_is_symetric local.Cons tl_base tl_step)
qed

theorem non_empty0: "non_empty (non_empty xs) = non_empty xs"
  apply (induction xs)
  by (auto simp: non_empty_def)
theorem non_empty1: "non_empty [] = []"
  by (auto simp: non_empty_def)
theorem non_empty2: "non_empty [[]] = []"
  by (auto simp: non_empty_def)
theorem cnf_choice1: "[] \<union>\<^sub>c p = non_empty p"
  by (auto simp: non_empty_def choice_cnf_def)
theorem non_empty3: "non_empty ([]#xs) = non_empty xs"
  by (auto simp: non_empty_def)
theorem non_empty4: "non_empty (a@b) = non_empty a @ non_empty b"
  apply (induction a arbitrary: b)
  by (auto simp: non_empty_def)
theorem cnf_choice2: "non_empty (x#xs) = [x] \<union>\<^sub>c xs"
  apply (induction xs arbitrary: x)
  by (auto simp: non_empty_def choice_cnf_def)
theorem cnf_choice3: "ys \<union>\<^sub>c (x#xs) = (ys@[x]) \<union>\<^sub>c xs"
  apply (induction ys arbitrary: x xs)
  by (auto simp: choice_cnf_def non_empty_def)
theorem non_empty5: "non_empty ((xx # x) # b) = (xx#x) # (non_empty b)"
  by (auto simp: non_empty_def)
theorem non_empty6: "non_empty ((xx # x) # b) = [xx#x] \<union>\<^sub>c (non_empty b)"
  using non_empty5 apply (auto simp: choice_cnf_def)
  by (smt (verit, del_insts) choice_cnf_def cnf_choice2 non_empty0)
theorem non_empty7: "non_empty ((x#xs)@(y#ys)) = (x#xs) \<union>\<^sub>c (y#ys)"
  by (metis choice_cnf_def non_empty4)

theorem non_empty8: "a \<union>\<^sub>c b \<noteq> [[]] \<Longrightarrow> a \<union>\<^sub>c b = (non_empty a) \<union>\<^sub>c (non_empty b)"
  by (simp add: choice_cnf_def non_empty0)

theorem cnf_choice_4: "evaluate (a \<union>\<^sub>c b) = evaluate (non_empty a \<union>\<^sub>c non_empty b)"
  by (simp add: choice_cnf_def non_empty0)

theorem concat_prop7: "evaluate xs \<equiv>\<^sub>p evaluate (non_empty xs)"
  apply (simp add: non_empty_def)
proof (induction xs)
  case Nil
  then show ?case apply auto
    by (simp add: equiv_is_reflexive)
next
  case (Cons a xs)
  then show ?case
  proof (cases "a = []")
    case True
    have "evaluate (a # xs) \<equiv>\<^sub>p evaluate (xs)"
      by (simp add: True concat_prop6)
    moreover have "... \<equiv>\<^sub>p evaluate (concat (map (\<lambda>x. if x \<noteq> [] then [x] else []) xs))"
      by (simp add: local.Cons)
    moreover have "... = evaluate (concat (map (\<lambda>x. if x \<noteq> [] then [x] else []) (a#xs)))" using True by auto
    ultimately show ?thesis using equiv_is_transitive
      by (metis (no_types, lifting))
  next
    case False
    have l1: "[x . x \<leftarrow> [a], x \<noteq> []] @ [x . x \<leftarrow> xs, x \<noteq> []] = [x . x \<leftarrow> a#xs, x \<noteq> []]"
      by simp
    have "evaluate (a # xs) \<equiv>\<^sub>p evaluate [a] \<union>\<^sub>p evaluate (xs)"
      using concat_prop4 by auto
    moreover have "... \<equiv>\<^sub>p evaluate [a] \<union>\<^sub>p (evaluate [x . x \<leftarrow> xs, x \<noteq> []])"
      by (metis (no_types, lifting) choice_equiv choice_idem_3 choice_idem_6 local.Cons)
    moreover have "... \<equiv>\<^sub>p evaluate [x . x \<leftarrow> [a], x \<noteq> []] \<union>\<^sub>p evaluate [x . x \<leftarrow> xs, x \<noteq> []]" using False
      using choice_commute_3 by auto
    moreover have "... \<equiv>\<^sub>p evaluate [x . x \<leftarrow> a#xs, x \<noteq> []]" using concat_prop5 l1
      by (smt (verit) Cons_eq_appendI append_eq_append_conv2 choice_commute concat.simps(1) concat.simps(2) concat_prop2 concat_prop3 fail_choice_r hd_base l8 list.map_disc_iff list.simps(9) same_append_eq tl_base)
    ultimately show ?thesis using equiv_is_transitive
      by blast
  qed
qed

theorem concat_prop8: "evaluate [[]] ; evaluate [y] \<equiv>\<^sub>p evaluate ([[]] ;\<^sub>c [y])"
proof -
  have "evaluate [[]] = Fail {}" apply (auto simp: evaluate_def Fail_def Skip_def) done
  have "[[]] ;\<^sub>c [y] = []" by (auto simp: composition_cnf_def non_empty_def)
  have "evaluate [] = Fail {}" apply (auto simp: evaluate_def Fail_def Skip_def) done
  show ?thesis
    by (simp add: Big_choice.fail_compose \<open>[[]] ;\<^sub>c [y] = []\<close> \<open>evaluate [[]] = Fail {}\<close> \<open>evaluate [] = Fail {}\<close>)
qed

theorem concat_prop9: "x \<noteq> [] \<Longrightarrow> y \<noteq> [] \<Longrightarrow> [x] ;\<^sub>c [y] = [x@y]" by (auto simp: composition_cnf_def non_empty_def)

theorem concat_prop10: "evaluate [a # x] ; evaluate [y] \<equiv>\<^sub>p evaluate ([a # x] ;\<^sub>c [y])"
proof (cases "x=[]")
  case t1: True
  then show ?thesis
  proof (cases "y=[]")
    case t2: True
    then show ?thesis using t1 t2 apply (auto simp: evaluate_def equiv_def composition_cnf_def Fail_def Skip_def composition_def corestrict_r_def restr_post_def restrict_r_def non_empty_def) done
  next
    case f2: False
    then show ?thesis using t1 apply (auto simp: evaluate_def composition_cnf_def Fail_def Skip_def)
      by (simp add: Concat_prop_10 equals_equiv_relation_3  non_empty_def)
  qed
next
  case f1: False
  then show ?thesis
  proof (cases "y=[]")
    case t2: True
    have "[a # x] ;\<^sub>c [[]] = []" by (auto simp: evaluate_def composition_cnf_def Fail_def Skip_def  non_empty_def)
    moreover have "evaluate [[]] = Fail{}"  by (auto simp: evaluate_def composition_cnf_def Fail_def Skip_def)
    moreover have "evaluate [] = Fail{}"  by (auto simp: evaluate_def composition_cnf_def Fail_def Skip_def)
    ultimately show ?thesis using f1 t2 apply (auto simp: )
      by (simp add: \<open>evaluate [[]] = Fail {}\<close> concat_prop2 fail_compose_r)
  next
    case f2: False
    have "[a # x] ;\<^sub>c [y] = [a # x @ y]" using f1 f2 concat_prop9
      by (metis Cons_eq_appendI list.discI)
    have "evaluate [a # x] ; evaluate [y] = Concat (a # x) ; Concat y" by (auto simp: evaluate_def)
    have "... = Concat (a#x@y)"
      by (simp add: Concat_prop_10 Concat_prop_5 f1 f2)
    have "... = evaluate [a#x@y]" by (auto simp: evaluate_def)
    then show ?thesis
      by (simp add: \<open>Concat (a # x) ; Concat y = Concat (a # x @ y)\<close> \<open>[a # x] ;\<^sub>c [y] = [a # x @ y]\<close> \<open>evaluate [a # x] ; evaluate [y] = Concat (a # x) ; Concat y\<close> equals_equiv_relation_3)
  qed
qed

theorem concat_prop11: "evaluate [x] ; evaluate [y] \<equiv>\<^sub>p evaluate ([x] ;\<^sub>c [y])"
  apply (induction x arbitrary: y)
  apply (simp add: concat_prop8)
  by (simp add: concat_prop10)

theorem comp_non_empty: "non_empty a ;\<^sub>c b = a ;\<^sub>c b" 
  apply (induction a arbitrary: b)
  by (auto simp: composition_cnf_def non_empty_def)

theorem choice_non_empty: "non_empty a \<union>\<^sub>c b = a \<union>\<^sub>c b"
  apply (induction a arbitrary: b)
  by (auto simp: choice_cnf_def non_empty_def)

theorem comp_non_empty2: "non_empty x ;\<^sub>c non_empty b = x ;\<^sub>c b"
proof (induction x arbitrary: b)
  case Nil
  then show ?case  apply (auto simp: composition_cnf_def  non_empty_def) done
next
  case (Cons a x)
  then show "non_empty (a # x) ;\<^sub>c non_empty b = (a # x) ;\<^sub>c b"
  proof (induction a)
    case Nil
    have "([] # x) ;\<^sub>c b = x ;\<^sub>c b"
      by (simp add: Nil composition_cnf_def non_empty3)
    then show ?case
      by (simp add: local.Nil non_empty3)
  next
    case (Cons aa a)
    then show "non_empty ((aa # a) # x) ;\<^sub>c non_empty b = ((aa # a) # x) ;\<^sub>c b"
    proof (induction b)
      case Nil
      then show ?case apply auto
        by (simp add: comp_non_empty non_empty1)
    next
      case (Cons bb b)
      then show ?case
        by (simp add: composition_cnf_def non_empty0)
    qed
  qed
qed

theorem choice_non_empty2: "non_empty a \<union>\<^sub>c non_empty b = a \<union>\<^sub>c b"
  apply (auto simp: choice_cnf_def)
  by (simp add: non_empty0)

theorem non_empty9: "x \<in> set (non_empty xs) \<Longrightarrow> x \<in> set xs"
  apply (induction xs arbitrary: x)
  by (auto simp: non_empty_def)

theorem non_empty10: "non_empty xs = [y] \<Longrightarrow> \<exists>a b. a@y#b = xs"
  by (metis list.set_intros(1) non_empty9 split_list)

theorem non_empty11: "non_empty xs = [] \<Longrightarrow> evaluate xs = Skip {}"
  apply (induction xs)
  apply (simp add: concat_prop2 special_empty1)
  apply (auto simp: evaluate_def)
  by (smt (verit) Choice.simps(2) Choice_prop_1_2 Concat.elims Un_empty_right append_is_Nil_conv choice_cnf_def cnf_choice2 non_empty5 not_Cons_self2 skip_prop_10)

theorem non_empty12: "non_empty xs = [x] \<Longrightarrow> non_empty xs = xs \<Longrightarrow>  evaluate xs = evaluate [x]"
  by simp
theorem non_empty13: "non_empty xs = [x] \<Longrightarrow> non_empty xs \<noteq> xs \<Longrightarrow>  evaluate xs = evaluate [x] \<union>\<^sub>p Skip {}"
proof (induction xs arbitrary: x)
  case Nil
  then show ?case apply (metis list.distinct(1) non_empty0 non_empty2) done
next
  case (Cons a xs)
  have "evaluate (a # xs) = evaluate [a] \<union>\<^sub>p evaluate (xs)"
    by (metis (no_types, lifting) Cons.prems(1) Cons.prems(2) append_is_Nil_conv butlast.simps(2) butlast_append concat_prop3 list.distinct(1) non_empty10 self_append_conv2)
  then show "evaluate (a # xs) = evaluate [x] \<union>\<^sub>p Skip {}"
  proof (cases "a = x")
    case True
    have "non_empty xs = []"
      by (metis Cons.prems(1) True choice_cnf_def cnf_choice2 non_empty0 self_append_conv)
    then show "evaluate (a # xs) = evaluate [x] \<union>\<^sub>p Skip {}"
      using True \<open>evaluate (a # xs) = evaluate [a] \<union>\<^sub>p evaluate xs\<close> non_empty11 by fastforce
  next
    case f1: False
    from f1 Cons(2) have "non_empty xs = [x]" apply (induction xs) apply auto
      apply (metis (no_types, lifting) Nil_is_append_conv append_self_conv2 butlast.simps(2) butlast_append list.distinct(1) list.inject non_empty10)
      by (metis empty_iff list.exhaust list.set_intros(1) non_empty3 non_empty5 set_ConsD set_empty)
    then show ?thesis
    proof (cases "non_empty xs \<noteq> xs")
      case True
      then show ?thesis
        by (metis Cons.IH Cons.prems(1) \<open>evaluate (a # xs) = evaluate [a] \<union>\<^sub>p evaluate xs\<close> \<open>non_empty xs = [x]\<close> append_self_conv2 choice_cnf_def cnf_choice2 non_empty11 skip_prop_12)
    next
      case False
      then show ?thesis
        by (metis Cons.prems(1) \<open>evaluate (a # xs) = evaluate [a] \<union>\<^sub>p evaluate xs\<close> \<open>non_empty xs = [x]\<close> append_self_conv2 choice_cnf_def choice_commute cnf_choice2 non_empty11)
    qed
  qed
qed

theorem nonempty_monotonic: "size (non_empty (x#xs)) \<ge> size (non_empty xs)"
  by (auto simp: non_empty_def)

theorem eval_prop: "size (non_empty b) \<noteq> 1 \<Longrightarrow> evaluate b = evaluate (non_empty b)"
proof (induction b)
  case Nil
  then show ?case by (auto simp: evaluate_def non_empty_def)
next
  case Cons1: (Cons a b)
  then show ?case
  proof (induction a)
    case Nil
    have "evaluate ([] # b) = evaluate [[]] \<union>\<^sub>p evaluate b"
      apply (auto simp: evaluate_def)
      by (metis Choice.simps(1) Choice.simps(2) Choice_prop_1_2 Choice_state_1 complete_state_prop skip_prop_10 skip_prop_9 special_empty1)
    then show "evaluate ([] # b) = evaluate (non_empty ([] # b))"
    proof (cases "b=[]")
      case True
      then show ?thesis apply auto by (auto simp: evaluate_def non_empty_def Fail_def Skip_def)
    next
      case False
      obtain aa b' where o1: "b=aa#b'"
        by (meson False list.exhaust)
      have "evaluate ([] # b) = evaluate ([] # aa#b')"
        by (simp add: \<open>b = aa # b'\<close>)
      have "... = evaluate [[]] \<union>\<^sub>p evaluate (aa#b')"
        using \<open>b = aa # b'\<close> \<open>evaluate ([] # b) = evaluate [[]] \<union>\<^sub>p evaluate b\<close> by blast
      have "... = evaluate [[]] \<union>\<^sub>p evaluate (b)"
        by (simp add: \<open>b = aa # b'\<close>)
      have  "... = evaluate [[]] \<union>\<^sub>p evaluate (non_empty b)"
        by (metis Cons1.IH Nil.prems(2) non_empty3)
      have  "... = Skip{} \<union>\<^sub>p evaluate (non_empty b)" by (auto simp: evaluate_def)
      have "... = evaluate (non_empty (b))" apply (auto simp: evaluate_def) apply (cases "non_empty b=[]")
        apply (metis Un_empty concat_prop2 evaluate_def skip_prop_10 special_empty1)
        by (metis Choice_prop_18 Nil.prems(2) choice_commute length_0_conv length_map less_one linorder_less_linear non_empty3 special_empty1)
      have "... = evaluate (non_empty ([] # b))"
        by (simp add: non_empty3)
      then show "evaluate ([] # b) = evaluate (non_empty ([] # b))"
        by (metis Cons1.IH Nil.prems(2) \<open>Skip {} \<union>\<^sub>p evaluate (non_empty b) = evaluate (non_empty b)\<close> \<open>evaluate ([] # aa # b') = evaluate [[]] \<union>\<^sub>p evaluate (aa # b')\<close> \<open>evaluate [[]] \<union>\<^sub>p evaluate (non_empty b) = Skip {} \<union>\<^sub>p evaluate (non_empty b)\<close> non_empty3 o1)
    qed
  next
    case (Cons aa a')
    have f1: "size (non_empty b) \<noteq> 0"
    proof -
      have "size (non_empty b) = 0 \<Longrightarrow> False"
      proof-
        assume t1: "size (non_empty b) = 0"
        have "\<forall>x \<in> set b. x = []" using t1 by (auto simp: non_empty_def evaluate_def)
        then have "\<forall>x \<in> set b. Concat x = Skip {}" by auto
        then have "map Concat b = [Skip {}. _ \<leftarrow> b]" by auto
        then have "\<Union>\<^sub>p [Skip {}. _ \<leftarrow> b] = Skip {}" apply (induction b) apply (auto simp: Skip_def Fail_def) [1] apply auto
          by (metis Choice.simps(2) Choice_prop_1_2 Un_empty_right skip_prop_10)
        then have "\<Union>\<^sub>p (map Concat b) = Skip {}"
          by (metis \<open>map Concat b = map (\<lambda>_. Skip {}) b\<close>)
        then have "evaluate b = Skip {}"
          by (simp add: evaluate_def) 
        then have "evaluate(non_empty b) = Skip {}"
          by (simp add: Cons1.IH t1)
        show "False"
          by (metis Cons.prems(2) Suc_length_conv t1 nat_1 nat_one_as_int non_empty5)
      qed
      then show "size (non_empty b) \<noteq> 0" by auto
    qed
    then show "evaluate ((aa # a') # b) = evaluate (non_empty ((aa # a') # b))"
    proof- 
      have "size (non_empty ((aa # a') # b)) = Suc (size (non_empty b))" by (auto simp: non_empty_def)
      show ?thesis
      proof (cases "size (non_empty b) = 1")
        case t2: True
        obtain b2 where o1:"[b2] = non_empty b" using t2
          by (metis One_nat_def Suc_length_conv length_0_conv)
        then obtain bs be where "b=bs@b2#be"
          by (metis non_empty10)
        have "non_empty ((aa # a') # b) = non_empty [(aa # a'), b2]"
          by (simp add: \<open>[b2] = non_empty b\<close> non_empty0 non_empty5)
        have "evaluate ((aa # a') # b) = evaluate [(aa # a')] \<union>\<^sub>p evaluate b"
          by (metis concat_prop3 list.size(3) non_empty1 t2 zero_neq_one)
        have "evaluate (non_empty [(aa # a'), b2]) = evaluate [(aa # a')] \<union>\<^sub>p evaluate [b2]"
          by (metis \<open>[b2] = non_empty b\<close> \<open>non_empty ((aa # a') # b) = non_empty [aa # a', b2]\<close> concat_prop3 list.distinct(1) non_empty5)
        have "evaluate [(aa # a')] \<union>\<^sub>p evaluate b = evaluate [(aa # a')] \<union>\<^sub>p evaluate [b2]"
          apply (cases "b = [b2]")
          apply simp using non_empty13 o1 apply auto
          by (smt (verit, ccfv_SIG) choice_assoc_1 choice_commute non_empty13 skip_prop_12)
        then show "evaluate ((aa # a') # b) = evaluate (non_empty ((aa # a') # b))"
          by (simp add: \<open>evaluate ((aa # a') # b) = evaluate [aa # a'] \<union>\<^sub>p evaluate b\<close> \<open>evaluate (non_empty [aa # a', b2]) = evaluate [aa # a'] \<union>\<^sub>p evaluate [b2]\<close> \<open>non_empty ((aa # a') # b) = non_empty [aa # a', b2]\<close>)
      next
        case f2: False
        then show ?thesis
          by (metis Cons1.IH concat_prop3 f1 length_0_conv non_empty1 non_empty5)
      qed
    qed
  qed
qed
  
theorem eval_prop2: "size b \<noteq> 1 \<Longrightarrow> size (non_empty b) = 1 \<Longrightarrow> evaluate b = evaluate (non_empty b) \<union>\<^sub>p Skip {}"
proof (induction b)
  case Nil
  then show ?case by (simp add: non_empty1)
next
  case (Cons a b)
  then show "evaluate (a # b) = evaluate (non_empty (a # b)) \<union>\<^sub>p Skip {}"
  proof (cases "a = []")
    case True
    then show ?thesis using Cons.IH Cons.prems concat_prop3 non_empty11 non_empty2 non_empty3 skip_prop_12 apply auto
      by (smt (verit) Cons.prems(1) Cons.prems(2) append_eq_append_conv choice_commute choice_non_empty2 cnf_choice2 length_Suc_conv_rev list.size(3) non_empty13 non_empty2 non_empty3 non_empty4 non_empty7)
  next
    case False
    have "non_empty b = []" using Cons(3) False by (auto simp: non_empty_def)
    then have "non_empty (a # b) = [a]"
      by (metis False list.exhaust non_empty5)
    have "evaluate (a # b) = evaluate ([a]) \<union>\<^sub>p Skip {}"
      using Cons.prems(1) Cons.prems(2) \<open>non_empty (a # b) = [a]\<close> non_empty13 by fastforce
    then show "evaluate (a # b) = evaluate (non_empty (a # b)) \<union>\<^sub>p Skip {}"
      by (simp add: \<open>non_empty (a # b) = [a]\<close>)
  qed
qed

theorem non_empty_reduces_size: "size (non_empty xs) \<le> size xs"
proof (induction xs)
  case Nil
  then show ?case apply (simp add: non_empty1) done
next
  case (Cons a xs)
  then show ?case
  proof (cases "a=[]")
    case True
    then show ?thesis
      by (metis impossible_Cons le_trans linorder_le_cases local.Cons non_empty3)
  next
    case False
    have "length (non_empty (a # xs)) = length (non_empty xs) + 1" using False by (auto simp: non_empty_def)
    then show ?thesis
      by (simp add: local.Cons)
  qed
qed
  

theorem non_empty_13: "size (x#xs) = size (non_empty (x#xs)) \<Longrightarrow> x \<noteq> []"
proof -
  assume a1: "size (x#xs) = size (non_empty (x#xs))"
  have "x = [] \<Longrightarrow> size (x#xs) > size (non_empty (x#xs))" proof (induction x arbitrary: xs)
    case Nil
    have "non_empty ([] # xs) = non_empty xs"
      by (simp add: non_empty3)
    have "length ([] # xs) > length (non_empty xs)"
      by (metis \<open>non_empty ([] # xs) = non_empty xs\<close> impossible_Cons le_neq_implies_less non_empty_reduces_size)
    then show "length ([] # xs) > length (non_empty ([] # xs))" apply (auto)
      by (simp add: \<open>non_empty ([] # xs) = non_empty xs\<close>)
  next
    case (Cons a x)
    then show ?case
      by simp 
  qed
  then show ?thesis
    using a1 by auto
qed
  

theorem non_empty_14: "size b = size (non_empty b) \<Longrightarrow> b = (non_empty b)"
proof (induction b)
  case Nil
  then show ?case apply (auto simp: non_empty_def) done
next
  case (Cons a b)
  have "a \<noteq> []" using Cons(2)
    by (simp add: non_empty_13)
  then have "non_empty (a # b) = a # non_empty (b)" by (auto simp: non_empty_def)
  then show ?case
    using Cons.IH Cons.prems by auto
qed

theorem eval_prop3: "size b = 1 \<Longrightarrow> size (non_empty b) = 1 \<Longrightarrow> evaluate b = evaluate (non_empty b)"
  by (metis non_empty_14)

theorem comp_cnf1: "non_empty xs = [] \<Longrightarrow> ys ;\<^sub>c xs = []"
  apply (induction xs arbitrary: ys)
  by (auto simp: non_empty_def composition_cnf_def)

theorem comp_cnf2: "non_empty ys = [] \<Longrightarrow> ys ;\<^sub>c xs = []"
  apply (induction ys arbitrary: xs)
  apply (simp add: non_empty_def composition_cnf_def)
  by (metis comp_non_empty list.distinct(1) list.exhaust non_empty3 non_empty5)

theorem comp_cnf3: "x \<noteq> [] \<Longrightarrow> y \<noteq> [] \<Longrightarrow> Concat x ; Concat y = Concat (x @ y)"
  apply (induction x) apply auto
  by (metis (full_types) Concat.simps(2) Concat_prop_10 Nil_is_append_conv append_self_conv2 compose_assoc)

theorem comp_cnf4: "a ;\<^sub>c b = a ;\<^sub>c non_empty b"
proof (induction a arbitrary: b)
  case Nil
  then show ?case apply (auto simp: non_empty_def composition_cnf_def) done
next
  case (Cons a1 a)
  then show ?case
  proof (induction a1)
    case Nil
    then show ?case by (auto simp: composition_cnf_def non_empty_def)
  next
    case (Cons a2 a1)
    then show ?case
      by (metis comp_non_empty2 non_empty0)
  qed
qed

theorem comp_cnf5: "a ;\<^sub>c b = non_empty a ;\<^sub>c b"
proof (induction a arbitrary: b)
  case Nil
  then show ?case apply (auto simp: non_empty_def composition_cnf_def) done
next
  case (Cons a1 a)
  then show ?case
  proof (induction a1)
    case Nil
    then show ?case by (auto simp: composition_cnf_def non_empty_def)
  next
    case (Cons a2 a1)
    then show ?case
      by (metis comp_non_empty2 non_empty0)
  qed
qed

theorem comp_prop1: "x ; (y \<union>\<^sub>p Skip {}) \<equiv>\<^sub>p x ; y" 
  by (auto simp: equiv_def composition_def corestrict_r_def Skip_def restr_post_def restrict_r_def)

theorem evaluate_equiv: "evaluate (non_empty xs) \<equiv>\<^sub>p evaluate xs"
proof (induction xs)
  case Nil
  then show ?case by (auto simp: evaluate_def non_empty_def equiv_def)
next
  case (Cons x xs)
  then show ?case
  proof (cases "x = []")
    case True
    have "non_empty (x # xs) = non_empty xs"
      by (simp add: True non_empty3)
    have "evaluate (non_empty xs) \<equiv>\<^sub>p evaluate xs"
      by (simp add: local.Cons)
    have "evaluate xs \<equiv>\<^sub>p evaluate (x # xs)" using concat_prop6 True apply auto
      using equiv_is_symetric by blast
    then show "evaluate (non_empty (x # xs)) \<equiv>\<^sub>p evaluate (x # xs)"
      using \<open>non_empty (x # xs) = non_empty xs\<close> equiv_is_transitive local.Cons by auto
  next
    case False
    have "non_empty (x # xs) = x # (non_empty xs)"
      by (metis False list.exhaust non_empty5)
    have "evaluate (x # non_empty xs) \<equiv>\<^sub>p evaluate [x] \<union>\<^sub>p evaluate (non_empty xs)" apply (auto simp: evaluate_def)
      by (metis Choice.simps(2) Choice_prop_1_2 Choice_prop_22 choice_idem_2 choice_idem_3 equals_equiv_relation_3 equiv_is_symetric)
    have "evaluate (non_empty xs) \<equiv>\<^sub>p evaluate xs"
      by (simp add: local.Cons)
    have "evaluate [x] \<union>\<^sub>p evaluate xs \<equiv>\<^sub>p evaluate (x # xs)"
      using concat_prop4 equiv_is_symetric by auto
    then show "evaluate (non_empty (x # xs)) \<equiv>\<^sub>p evaluate (x # xs)"
      using concat_prop7 equiv_is_symetric by auto
  qed
qed

theorem choice_cnf_thm: "evaluate xs \<union>\<^sub>p evaluate ys \<equiv>\<^sub>p evaluate (xs \<union>\<^sub>c ys)"
proof -
  have "xs \<union>\<^sub>c ys = non_empty xs @ non_empty ys" by (auto simp: choice_cnf_def)
  have "... = non_empty (xs@ys)" by (auto simp: non_empty_def)
  have "evaluate (non_empty (xs@ys)) \<equiv>\<^sub>p evaluate (xs@ys)"
    by (simp add: evaluate_equiv)
  have "... \<equiv>\<^sub>p evaluate xs \<union>\<^sub>p evaluate ys"
    by (simp add: concat_prop5)
  show ?thesis
    by (metis \<open>evaluate (non_empty (xs @ ys)) \<equiv>\<^sub>p evaluate (xs @ ys)\<close> \<open>evaluate (xs @ ys) \<equiv>\<^sub>p evaluate xs \<union>\<^sub>p evaluate ys\<close> \<open>non_empty xs @ non_empty ys = non_empty (xs @ ys)\<close> \<open>xs \<union>\<^sub>c ys = non_empty xs @ non_empty ys\<close> equiv_is_symetric equiv_is_transitive)
qed

theorem non_empty14: "\<forall>t \<in> set xs. t \<noteq> [] \<Longrightarrow> non_empty xs = xs"
  apply (induction xs)
  apply (auto simp: non_empty_def) [1]
  by (metis list.exhaust list.set_intros(1) list.set_intros(2) non_empty5)

theorem non_empty15: "xs ;\<^sub>c ys = non_empty (xs ;\<^sub>c ys)"
proof -
  have "xs ;\<^sub>c ys = non_empty xs ;\<^sub>c non_empty ys"
    by (simp add: comp_non_empty2)
  have "\<forall>t \<in> set (non_empty xs ;\<^sub>c non_empty ys). t \<noteq> []"
    by (auto simp: composition_cnf_def non_empty_def)
  show ?thesis
    using \<open>\<forall>t\<in>set (non_empty xs ;\<^sub>c non_empty ys). t \<noteq> []\<close> \<open>xs ;\<^sub>c ys = non_empty xs ;\<^sub>c non_empty ys\<close> non_empty14 by fastforce  
qed

theorem choic_cnf1: "(x#xs) ;\<^sub>c ys = ([x] ;\<^sub>c ys) \<union>\<^sub>c (xs ;\<^sub>c ys)"
proof -
  have "([x] ;\<^sub>c ys) \<union>\<^sub>c (xs ;\<^sub>c ys) = non_empty (([x] ;\<^sub>c ys) @ (xs ;\<^sub>c ys))"
    by (simp add: choice_cnf_def non_empty4)
  show ?thesis
  proof (cases "x = []")
    case True
    then show ?thesis
      by (metis \<open>([x] ;\<^sub>c ys) \<union>\<^sub>c (xs ;\<^sub>c ys) = non_empty ([x] ;\<^sub>c ys @ xs ;\<^sub>c ys)\<close> comp_cnf2 comp_non_empty non_empty15 non_empty2 non_empty3 self_append_conv2)
  next
    case False
    have "non_empty [x] = [x]"
      by (metis False list.exhaust non_empty1 non_empty5)
    have "[x @ y. y \<leftarrow> non_empty ys] = [x @ y. x \<leftarrow> non_empty [x], y \<leftarrow> non_empty ys]"
      by (simp add: \<open>non_empty [x] = [x]\<close>)
    have "[x] ;\<^sub>c ys = [x @ y. y \<leftarrow> non_empty ys]" using False apply (auto simp: composition_cnf_def)
      by (simp add: \<open>map ((@) x) (non_empty ys) = concat (map (\<lambda>x. map ((@) x) (non_empty ys)) (non_empty [x]))\<close>)
    have "\<forall>t \<in> set [x @ y. y \<leftarrow> non_empty ys]. t \<noteq> []" by (auto simp: non_empty_def)
    then have "[x @ y. y \<leftarrow> non_empty ys] = non_empty [x @ y. y \<leftarrow> non_empty ys]" 
      apply (auto simp: non_empty_def)
      by (metis \<open>\<forall>t\<in>set (map ((@) x) (non_empty ys)). t \<noteq> []\<close> list.map_comp non_empty14 non_empty_def)
    have "([x @ y. y \<leftarrow> non_empty ys]) \<union>\<^sub>c (xs ;\<^sub>c ys) = ([x @ y. y \<leftarrow> non_empty ys]) @ non_empty (xs ;\<^sub>c ys)"
      by (metis \<open>map ((@) x) (non_empty ys) = non_empty (map ((@) x) (non_empty ys))\<close> choice_cnf_def)
    have "([x @ y. y \<leftarrow> non_empty ys]) @ non_empty (xs ;\<^sub>c ys) = ([x @ y. y \<leftarrow> non_empty ys]) @ (xs ;\<^sub>c ys)"
      by (metis non_empty15)
    have "([x @ y. y \<leftarrow> non_empty ys]) @ (xs ;\<^sub>c ys) = ([x @ y. y \<leftarrow> non_empty ys]) @ [a @ b. a \<leftarrow> non_empty xs, b \<leftarrow> non_empty ys]"
      by (auto simp: composition_cnf_def)
    have "([x @ y. y \<leftarrow> non_empty ys]) @ [a @ b. a \<leftarrow> non_empty xs, b \<leftarrow> non_empty ys] = [a @ b. a \<leftarrow> non_empty (x#xs), b \<leftarrow> non_empty ys]"
      by (metis \<open>map ((@) x) (non_empty ys) = concat (map (\<lambda>x. map ((@) x) (non_empty ys)) (non_empty [x]))\<close> choice_cnf_def cnf_choice2 concat_append map_append)
    have "[a @ b. a \<leftarrow> non_empty (x#xs), b \<leftarrow> non_empty ys] = (x # xs) ;\<^sub>c ys"
      by (simp add: composition_cnf_def)
    have "non_empty (x # xs) ;\<^sub>c ys = (x # xs) ;\<^sub>c ys"
      by (simp add: comp_non_empty)
    then show "(x # xs) ;\<^sub>c ys = ([x] ;\<^sub>c ys) \<union>\<^sub>c (xs ;\<^sub>c ys)"
      by (simp add: \<open>[x] ;\<^sub>c ys = map ((@) x) (non_empty ys)\<close> \<open>concat (map (\<lambda>a. map ((@) a) (non_empty ys)) (non_empty (x # xs))) = (x # xs) ;\<^sub>c ys\<close> \<open>map ((@) x) (non_empty ys) @ concat (map (\<lambda>a. map ((@) a) (non_empty ys)) (non_empty xs)) = concat (map (\<lambda>a. map ((@) a) (non_empty ys)) (non_empty (x # xs)))\<close> \<open>map ((@) x) (non_empty ys) @ non_empty (xs ;\<^sub>c ys) = map ((@) x) (non_empty ys) @ xs ;\<^sub>c ys\<close> \<open>map ((@) x) (non_empty ys) @ xs ;\<^sub>c ys = map ((@) x) (non_empty ys) @ concat (map (\<lambda>a. map ((@) a) (non_empty ys)) (non_empty xs))\<close> \<open>map ((@) x) (non_empty ys) \<union>\<^sub>c (xs ;\<^sub>c ys) = map ((@) x) (non_empty ys) @ non_empty (xs ;\<^sub>c ys)\<close>)
  qed
qed

theorem comp_distrib_r: "(b \<union>\<^sub>c c) ;\<^sub>c a = (b ;\<^sub>c a) \<union>\<^sub>c (c ;\<^sub>c a)"
proof (induction b)
  case Nil
  have "non_empty [] @ non_empty c = non_empty c"
    by (simp add: non_empty1)
  have "non_empty c ;\<^sub>c a = c ;\<^sub>c a"
    by (simp add: comp_non_empty)
  have "[] ;\<^sub>c a = []" 
    by (auto simp: composition_cnf_def non_empty_def)
  have "non_empty ([]) = []"
    by (simp add: non_empty1)
  have "c ;\<^sub>c a = non_empty (c ;\<^sub>c a)"
    using non_empty15 by auto
  then show ?case
    apply (auto simp: choice_cnf_def)
    by (metis \<open>[] ;\<^sub>c a = []\<close> \<open>non_empty c ;\<^sub>c a = c ;\<^sub>c a\<close> choice_cnf_def cnf_choice1)
next
  case (Cons b bs)
  then show "((b # bs) \<union>\<^sub>c c) ;\<^sub>c a = ((b # bs) ;\<^sub>c a) \<union>\<^sub>c (c ;\<^sub>c a)"
  proof (cases "b=[]")
    case True
    have "([] # bs) \<union>\<^sub>c c = bs \<union>\<^sub>c c"
      by (metis choice_non_empty2 non_empty3)
    have "(([] # bs) ;\<^sub>c a) = bs ;\<^sub>c a"
      by (simp add: composition_cnf_def non_empty3)

    have "(bs \<union>\<^sub>c c) ;\<^sub>c a = (bs ;\<^sub>c a) \<union>\<^sub>c (c ;\<^sub>c a)"
      by (simp add: local.Cons)
    from True show ?thesis apply auto
      by (simp add: \<open>([] # bs) ;\<^sub>c a = bs ;\<^sub>c a\<close> \<open>([] # bs) \<union>\<^sub>c c = bs \<union>\<^sub>c c\<close> local.Cons)
  next
    case False
    then show "((b # bs) \<union>\<^sub>c c) ;\<^sub>c a = ((b # bs) ;\<^sub>c a) \<union>\<^sub>c (c ;\<^sub>c a)" 
      by (metis choice_cnf_def composition_cnf_def concat_append map_append non_empty0 non_empty15 non_empty4)
  qed
qed

theorem choice_cnf_commute: "a \<union>\<^sub>c (b \<union>\<^sub>c c) = (a \<union>\<^sub>c b) \<union>\<^sub>c c"
  by (simp add: choice_cnf_def non_empty0 non_empty4)


theorem equal_sym: "equal_cnf a b = equal_cnf b a"
  by (auto simp: equal_cnf_def)

theorem equal_empty: "equal_cnf a [] \<Longrightarrow> a = []"
  by (auto simp: equal_cnf_def)

theorem eval_prop1: "e \<noteq>[] \<Longrightarrow> evaluate (e @ [x]) = evaluate e \<union>\<^sub>p evaluate [x]"
  apply (auto simp: evaluate_def choice_def)
  by (simp add: Choice_prop_3 choice_def)

theorem evaluate_split: "size xs \<noteq>1 \<Longrightarrow> evaluate xs = evaluate [t. t \<leftarrow> xs, t =x] \<union>\<^sub>p evaluate [t. t \<leftarrow> xs, t\<noteq>x]"
proof (cases "xs=[]")
  case True
  then show ?thesis by (auto simp: evaluate_def Fail_def choice_def S_def restr_post_def restrict_r_def)
next
  case False
  assume a1: "size xs \<noteq>1"
  from False a1 show ?thesis
  proof (induction xs arbitrary: x)
    case Nil
    then show ?case by simp
  next
    case (Cons y ys)
    have l1: "evaluate (y#ys) = evaluate [y] \<union>\<^sub>p evaluate ys"
      by (metis Cons.prems(2) One_nat_def concat_prop3 length_Cons list.size(3))
    then show "evaluate (y#ys) = evaluate [t. t \<leftarrow> (y#ys), t =x] \<union>\<^sub>p evaluate [t. t \<leftarrow> (y#ys), t\<noteq>x]"
    proof (cases "size ys=1")
      case True
      then show ?thesis apply (auto simp: evaluate_def)
        apply (smt (verit) Choice.simps(2) Choice_prop_1_2 Choice_prop_22 Cons_eq_append_conv True append.right_neutral choice_assoc_1 choice_commute concat.simps(1) concat.simps(2) length_0_conv length_Suc_conv_rev list.map_disc_iff list.simps(9) zero_neq_one)
        by (smt (verit) Choice.simps(2) Choice_prop_1_2 Choice_prop_22 Cons_eq_append_conv True append.right_neutral choice_assoc_1 choice_commute concat.simps(1) concat.simps(2) length_0_conv length_Suc_conv_rev list.map_disc_iff list.simps(9) zero_neq_one)
    next
      case f2: False
      have l2: "size ys>1"
        using Cons.prems(2) f2 nat_neq_iff by auto
      have " evaluate ys = (evaluate [t. t \<leftarrow> (ys), t=x] \<union>\<^sub>p evaluate [t. t \<leftarrow> (ys), t\<noteq>x])"
        using Cons.IH False \<open>1 < length ys\<close> gr_implies_not_zero by auto
      then show ?thesis
      proof (cases "x=y")
        case t3: True
        have "[t. t \<leftarrow> (y#ys), t =x] = y#[t. t \<leftarrow> ys, t =x]" using t3 by auto
        then show "evaluate (y#ys) = evaluate [t. t \<leftarrow> (y#ys), t=x] \<union>\<^sub>p evaluate [t. t \<leftarrow> (y#ys), t\<noteq>x]"
        proof (cases "[t. t \<leftarrow> ys, t=x] = []")
          case t4: True
          then show ?thesis apply auto 
            apply (smt (verit) \<open>evaluate ys = evaluate (concat (map (\<lambda>t. if t = x then [t] else []) ys)) \<union>\<^sub>p evaluate (concat (map (\<lambda>t. if t \<noteq> x then [t] else []) ys))\<close> choice_assoc_1 choice_commute concat_prop3 local.l1 non_empty1 non_empty11 skip_prop_12)
            by (metis (no_types, lifting) \<open>evaluate ys = evaluate (concat (map (\<lambda>t. if t = x then [t] else []) ys)) \<union>\<^sub>p evaluate (concat (map (\<lambda>t. if t \<noteq> x then [t] else []) ys))\<close> choice_assoc_1 choice_commute local.l1 non_empty1 non_empty11 skip_prop_12 t4)
        next
          case f4: False
          have "evaluate [t. t \<leftarrow> (y#ys), t=x] = evaluate [y] \<union>\<^sub>p evaluate [t. t \<leftarrow> ys, t=x]"
            by (metis (no_types, lifting) \<open>concat (map (\<lambda>t. if t = x then [t] else []) (y # ys)) = y # concat (map (\<lambda>t. if t = x then [t] else []) ys)\<close> concat_prop3 f4)
          moreover have "evaluate [t. t \<leftarrow> (y#ys), t\<noteq>x] = evaluate [t. t \<leftarrow> ys, t\<noteq>x]" using t3
            by simp
          ultimately show ?thesis
            by (smt (verit) \<open>evaluate ys = evaluate (concat (map (\<lambda>t. if t = x then [t] else []) ys)) \<union>\<^sub>p evaluate (concat (map (\<lambda>t. if t \<noteq> x then [t] else []) ys))\<close> append.left_neutral choice_assoc_1 concat.simps(2) list.simps(9) local.l1 t3)
        qed
      next
        case f3: False
        have "[t. t \<leftarrow> (y#ys), t\<noteq>x] = y#[t. t \<leftarrow> ys, t\<noteq>x]" using f3 by auto
        then show "evaluate (y#ys) = evaluate [t. t \<leftarrow> (y#ys), t=x] \<union>\<^sub>p evaluate [t. t \<leftarrow> (y#ys), t\<noteq>x]"
        proof (cases "[t. t \<leftarrow> ys, t\<noteq>x] = []")
          case t4: True
          then show ?thesis apply auto
            apply (metis (no_types, lifting) \<open>evaluate ys = evaluate (concat (map (\<lambda>t. if t = x then [t] else []) ys)) \<union>\<^sub>p evaluate (concat (map (\<lambda>t. if t \<noteq> x then [t] else []) ys))\<close> choice_assoc_1 choice_commute local.l1 non_empty1 non_empty11 skip_prop_12 t4) 
            by (smt (verit) \<open>evaluate ys = evaluate (concat (map (\<lambda>t. if t = x then [t] else []) ys)) \<union>\<^sub>p evaluate (concat (map (\<lambda>t. if t \<noteq> x then [t] else []) ys))\<close> choice_assoc_1 choice_commute concat_prop3 local.l1 non_empty1 non_empty11 skip_prop_12)
        next
          case f4: False
          have "evaluate [t. t \<leftarrow> (y#ys), t\<noteq>x] = evaluate [y] \<union>\<^sub>p evaluate [t. t \<leftarrow> ys, t\<noteq>x]"
            by (metis (mono_tags, lifting) \<open>concat (map (\<lambda>t. if t \<noteq> x then [t] else []) (y # ys)) = y # concat (map (\<lambda>t. if t \<noteq> x then [t] else []) ys)\<close> concat_prop3 f4)
          moreover have "evaluate [t. t \<leftarrow> (y#ys), t=x] = evaluate [t. t \<leftarrow> ys, t=x]" using f3
            by simp
          ultimately show ?thesis
            using \<open>evaluate ys = evaluate (concat (map (\<lambda>t. if t = x then [t] else []) ys)) \<union>\<^sub>p evaluate (concat (map (\<lambda>t. if t \<noteq> x then [t] else []) ys))\<close> choice_assoc_1 local.l1 by force
        qed
      qed
    qed
  qed
qed

theorem size_prop: "size [t. t\<leftarrow>a, t=x] + size [t. t\<leftarrow>a, t\<noteq>x] = size a"
proof (induction a)
  case Nil
  then show ?case by auto
next
  case (Cons y ys)
  have "size (y#ys) = size ys + 1"
      by simp
  then show ?case
  proof (cases "y=x")
    case True
    have "size [t. t\<leftarrow>(y#ys), t=x] = size [t. t\<leftarrow>ys, t=x] + 1" using True by auto
    have "size [t. t\<leftarrow>(y#ys), t\<noteq>x] = size [t. t\<leftarrow>ys, t\<noteq>x]" using True by auto
    then show ?thesis
      using \<open>length (concat (map (\<lambda>t. if t = x then [t] else []) (y # ys))) = length (concat (map (\<lambda>t. if t = x then [t] else []) ys)) + 1\<close> local.Cons by auto
  next
    case False
    have "size [t. t\<leftarrow>(y#ys), t=x] = size [t. t\<leftarrow>ys, t=x]" using False by auto
    have "size [t. t\<leftarrow>(y#ys), t\<noteq>x] = size [t. t\<leftarrow>ys, t\<noteq>x] + 1" using False by auto
    then show ?thesis
      using local.Cons by auto
  qed
qed

theorem evaluate_prop: "size xs = 1 \<Longrightarrow> \<forall>t \<in> set xs. t=x \<Longrightarrow> evaluate xs = evaluate [x]"
  by (metis impossible_Cons length_0_conv less_one linorder_le_less_linear list.set_intros(1) neq_Nil_conv zero_neq_one)

theorem evaluate_prop2: "size xs > 1 \<Longrightarrow> \<forall>t \<in> set xs. t=x \<Longrightarrow> evaluate xs = evaluate [x] \<union>\<^sub>p evaluate [x]"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "a = x"
    by (simp add: Cons.prems(2))
  then show ?case
  proof (cases "xs = []")
    case True
    then show ?thesis using Cons by auto
  next
    case f1: False
    have "evaluate (a # xs) = evaluate [x] \<union>\<^sub>p evaluate xs"
      by (simp add: f1 \<open>a = x\<close> concat_prop3)
    then show ?thesis
    proof (cases "size xs=1")
      case True
      then show ?thesis
        by (metis Cons.prems(1) Cons.prems(2) One_nat_def Suc_length_conv \<open>evaluate (a # xs) = evaluate [x] \<union>\<^sub>p evaluate xs\<close> diff_Suc_1' length_0_conv nth_Cons_0 nth_Cons_pos nth_mem zero_less_one)
    next
      case False
      have "evaluate xs = evaluate [x] \<union>\<^sub>p evaluate [x]"
        by (meson Cons.IH Cons.prems(2) False f1 length_0_conv less_one linorder_neqE_nat list.set_intros(2))
      then show ?thesis
        by (simp add: \<open>evaluate (a # xs) = evaluate [x] \<union>\<^sub>p evaluate xs\<close> choice_idem_5)
    qed
  qed
qed

theorem equal_eval: "equal_cnf a b \<Longrightarrow> evaluate a = evaluate b"
proof (induction "size a" arbitrary: b a rule: less_induct)
      case less
  assume a1: "equal_cnf a b"
  show ?case
  proof (cases "size a = 0")
    case zero: True
    then show ?thesis using a1 by (auto simp: evaluate_def equal_cnf_def)
next
  case ge0: False
  then show ?thesis
  proof (cases "size a = 1")
    case one: True
    obtain a' where "a=[a']" using one apply auto
      by (metis Suc_length_conv length_0_conv)
    obtain b' where "b=[b']"
      by (metis (no_types, lifting) equal_cnf_def One_nat_def a1 add_diff_cancel_left' append_butlast_last_id ge0 length_0_conv length_butlast one plus_1_eq_Suc self_append_conv2)
    show ?thesis using a1
      by (simp add: equal_cnf_def \<open>a = [a']\<close> \<open>b = [b']\<close>)
  next
    case ge1: False

    from a1 ge0 ge1 show ?thesis
    proof -
      have l1: "size a > 1"
        using ge0 nat_neq_iff
        using ge1 by auto
      have "size a \<noteq> 1"
        using ge1 by auto
      have "size b \<noteq> 1"
        using equal_cnf_def a1 ge1 by auto
      obtain x xs where o1: "a=x#xs"
        by (metis \<open>1 < length a\<close> length_0_conv less_nat_zero_code neq_Nil_conv)
      obtain ax where o2: "ax = [t. t\<leftarrow>a, t=x]" by simp
      have "\<forall>t \<in> set ax. t = x" using o2 by auto
      obtain anx where o3: "anx = [t. t\<leftarrow>a, t\<noteq>x]" by simp
      have "size a = size ax + size anx" using o2 o3
        by (simp add: size_prop)
      obtain bx where o4: "bx = [t. t\<leftarrow>b, t=x]" by simp
      have "\<forall>t \<in> set bx. t = x" using o4 by auto
      obtain bnx where o5: "bnx = [t. t\<leftarrow>b, t\<noteq>x]" by simp
      have "size b = size bx + size bnx" using o4 o5
        by (simp add: size_prop)
      have l2: "ax\<noteq>[]" by (simp add: \<open>ax = concat (map (\<lambda>t. if t = x then [t] else []) a)\<close> o1)
      have l3: "bx\<noteq>[]" using a1 \<open>bx = [t. t\<leftarrow>b, t=x]\<close> apply (auto simp: equal_cnf_def)
        using ge1 apply presburger
        by (metis (no_types, lifting) Un_iff image_insert insert_iff insert_inter_insert list.simps(15) not_Cons_self2 o1)
      have l4: "set anx = set bnx" using less(2) \<open>anx = [t. t\<leftarrow>a, t\<noteq>x]\<close> \<open>bnx = [t. t\<leftarrow>b, t\<noteq>x]\<close> by (auto simp: equal_cnf_def)
      have l5: "evaluate a = evaluate ax \<union>\<^sub>p evaluate anx" using o2 o3 \<open>size a \<noteq> 1\<close> evaluate_split by blast
      have l6: "evaluate b = evaluate bx \<union>\<^sub>p evaluate bnx" using o4 o5 \<open>size b \<noteq> 1\<close> evaluate_split by blast
      then show ?thesis
      proof (cases "anx=[]")
        case True
        have l1: "\<forall>t \<in> set a. t = x" using True o3 less by auto
        have l2: "\<forall>t \<in> set ax. t = x" using True o2 less l1 by auto
        have l3: "size ax > 1" using l1 o2 o3 True apply auto
          by (metis One_nat_def Suc_lessI \<open>length a = length ax + length anx\<close> add.right_neutral ge0 ge1 length_greater_0_conv list.size(3))
        have "evaluate ax = evaluate [x] \<union>\<^sub>p evaluate [x]" using l3 l2 evaluate_prop2 by auto
        have "bnx = []"
          using True local.l4 by auto
        have l1: "\<forall>t \<in> set b. t = x" using True o3 less
          by (simp add: equal_cnf_def local.l1)
        have l2: "\<forall>t \<in> set bx. t = x" using True o4 less l1 by auto
        have l3: "size bx > 1" using l1 o2 o3 True
          by (metis One_nat_def Suc_lessI \<open>bnx = []\<close> \<open>length b = length bx + length bnx\<close> \<open>length b \<noteq> 1\<close> a1 add.right_neutral equal_empty ge0 length_greater_0_conv list.size(3)) 
        have "evaluate bx = evaluate [x] \<union>\<^sub>p evaluate [x]"
          using evaluate_prop2 local.l2 local.l3 by auto
        then show ?thesis
          by (simp add: True \<open>bnx = []\<close> \<open>evaluate ax = evaluate [x] \<union>\<^sub>p evaluate [x]\<close> local.l5 local.l6)
      next
        case f1: False
        have "bnx \<noteq> []"
          using f1 local.l4 by auto
        have "evaluate ax = evaluate [x] \<or> evaluate ax = evaluate [x] \<union>\<^sub>p evaluate [x]"
        proof (cases "size ax=1")
          case True
          have "evaluate ax = evaluate [x]" using o2
            by (smt (verit) True card_length ge0 hd_concat length_Cons length_greater_0_conv list.sel(1) list.simps(9) list.size(3) local.l2 map_is_Nil_conv map_nth o1 rotate1.simps(2) rotate1_fixpoint_card self_append_conv2 upt_conv_Cons upt_eq_Nil_conv)
          then show ?thesis
            by simp
        next
          case False
          have "size ax>1"
            using False local.l2 nat_neq_iff by auto
          then have "evaluate ax = evaluate [x] \<union>\<^sub>p evaluate [x]" using o2 evaluate_prop2
            using \<open>\<forall>t\<in>set ax. t = x\<close> by blast
          then show ?thesis
            by simp
        qed
        have "evaluate bx = evaluate [x] \<or> evaluate bx = evaluate [x] \<union>\<^sub>p evaluate [x]"
        proof (cases "size bx=1")
          case True
          have "evaluate bx = evaluate [x]" using o4
            using True \<open>\<forall>t\<in>set bx. t = x\<close> evaluate_prop by blast
          then show ?thesis
            by simp
        next
          case False
          have "size bx>1"
            by (meson False length_0_conv less_one linorder_neqE_nat local.l3)
          then have "evaluate bx = evaluate [x] \<union>\<^sub>p evaluate [x]" using o2 evaluate_prop2
            using \<open>\<forall>t\<in>set bx. t = x\<close> by blast
          then show ?thesis
            by simp
        qed
        then show ?thesis
        proof (cases "size anx = 1")
          case True
          obtain y where "anx=[y]" using True apply auto
            by (metis Suc_length_conv length_0_conv)
          have "\<forall>t \<in> set bnx. t = y"
            using \<open>anx = [y]\<close> local.l4 by auto

          have "evaluate bnx = evaluate [y] \<or> evaluate bnx = evaluate [y] \<union>\<^sub>p evaluate [y]"
          proof (cases "size bnx=1")
            case True
            have "evaluate bnx = evaluate [y]" using o4
              using True \<open>\<forall>t\<in>set bnx. t = y\<close> evaluate_prop by blast
            then show ?thesis
              by simp
          next
            case False
            have "size bnx>1"
              by (meson False \<open>bnx \<noteq> []\<close> length_0_conv less_one linorder_neqE_nat)
            then have "evaluate bnx = evaluate [y] \<union>\<^sub>p evaluate [y]" using o2 evaluate_prop2
              using \<open>\<forall>t\<in>set bnx. t = y\<close> by blast
            then show ?thesis
              by simp
          qed
          have "evaluate ax \<union>\<^sub>p evaluate anx = evaluate bx \<union>\<^sub>p evaluate bnx"
            by (metis \<open>anx = [y]\<close> \<open>evaluate ax = evaluate [x] \<or> evaluate ax = evaluate [x] \<union>\<^sub>p evaluate [x]\<close> \<open>evaluate bnx = evaluate [y] \<or> evaluate bnx = evaluate [y] \<union>\<^sub>p evaluate [y]\<close> \<open>evaluate bx = evaluate [x] \<or> evaluate bx = evaluate [x] \<union>\<^sub>p evaluate [x]\<close> choice_idem_5 choice_idem_6)
          then show ?thesis
            by (simp add: local.l5 local.l6)
        next
          case False
          have "size anx > 1"
            using False f1 nat_neq_iff by auto
          have "evaluate ax \<union>\<^sub>p evaluate anx = evaluate bx \<union>\<^sub>p evaluate bnx"
          proof (cases "size bnx = 1")
            case True
            obtain y where "bnx=[y]" using True apply auto
              by (metis Suc_length_conv length_0_conv)
            have "\<forall>t \<in> set anx. t = y"
              using \<open>bnx = [y]\<close> local.l4 by auto
  
            have "evaluate anx = evaluate [y] \<or> evaluate anx = evaluate [y] \<union>\<^sub>p evaluate [y]"
            proof (cases "size anx=1")
              case True
              have "evaluate anx = evaluate [y]" using o4
                using True \<open>\<forall>t\<in>set anx. t = y\<close> evaluate_prop by blast
              then show ?thesis
                by simp
            next
              case False
              have "size anx>1"
                by (meson False \<open>anx \<noteq> []\<close> length_0_conv less_one linorder_neqE_nat)
              then have "evaluate anx = evaluate [y] \<union>\<^sub>p evaluate [y]" using o2 evaluate_prop2
                using \<open>\<forall>t\<in>set anx. t = y\<close> by blast
              then show ?thesis
                by simp
            qed
            then show ?thesis
              by (metis \<open>bnx = [y]\<close> \<open>evaluate ax = evaluate [x] \<or> evaluate ax = evaluate [x] \<union>\<^sub>p evaluate [x]\<close> \<open>evaluate bx = evaluate [x] \<or> evaluate bx = evaluate [x] \<union>\<^sub>p evaluate [x]\<close> choice_idem_5 choice_idem_6)
          next
            case False
            have "size bnx > 1"
              using False \<open>bnx \<noteq> []\<close> nat_neq_iff by auto
            have "equal_cnf anx bnx"
              using equal_cnf_def False \<open>1 < length anx\<close> local.l4 by fastforce
            have "evaluate anx = evaluate bnx"
              by (simp add: \<open>equal_cnf anx bnx\<close> \<open>length a = length ax + length anx\<close> less.hyps local.l2)
            then show ?thesis
              by (metis \<open>evaluate ax = evaluate [x] \<or> evaluate ax = evaluate [x] \<union>\<^sub>p evaluate [x]\<close> \<open>evaluate bx = evaluate [x] \<or> evaluate bx = evaluate [x] \<union>\<^sub>p evaluate [x]\<close> choice_idem_6)
          qed
          then show ?thesis
            by (simp add: local.l5 local.l6) 
        qed
      qed
    qed
  qed
qed
qed

theorem eq_reflexive: "equal xs xs"
  by (auto simp: equal_def)

theorem comp_prop: "tr \<in> set (xs ;\<^sub>c ys) \<Longrightarrow> \<exists>x y. x \<in> set xs \<and> y \<in> set ys \<and> x@y = tr \<and> x \<noteq> [] \<and> y \<noteq> []"
  by (auto simp: composition_cnf_def non_empty_def)

theorem comp_prop2: "x \<noteq> [] \<Longrightarrow> y \<noteq> [] \<Longrightarrow> x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> x@y \<in> set (xs ;\<^sub>c ys)"
  by (auto simp: composition_cnf_def non_empty_def)

theorem choice_prop: "tr \<in> set (xs \<union>\<^sub>c ys) \<Longrightarrow> (tr \<in> set xs \<or> tr \<in> set ys) \<and> tr \<noteq> []"
  by (auto simp: choice_cnf_def non_empty_def)

theorem same_traces_size_equal: "\<forall>tr \<in> set xs. tr \<in> set ys \<Longrightarrow> \<forall>tr \<in> set ys. tr \<in> set xs \<Longrightarrow> size xs = size ys \<Longrightarrow> equal_cnf xs ys"
  by (auto simp: equal_cnf_def)

theorem same_traces_size_equal2: "size xs = size ys \<Longrightarrow> equal_cnf xs ys \<Longrightarrow> \<forall>tr \<in> set xs. tr \<in> set ys"
  by (auto simp: equal_cnf_def)

theorem same_traces_size_equal3: "size xs = size ys \<Longrightarrow> equal_cnf xs ys \<Longrightarrow> \<forall>tr \<in> set ys. tr \<in> set xs"
  by (auto simp: equal_cnf_def)

theorem comp_prop3: "\<exists>q w. q \<in> set a \<and> w \<in> set b \<and> tr = q @ w \<and> q \<noteq> [] \<and> w \<noteq> [] \<Longrightarrow> tr \<in> set (a ;\<^sub>c b)"
  using comp_prop2 by blast

theorem choice_prop2: "\<exists>q. (q \<in> set a \<or> q \<in> set b) \<and> tr = q \<and> q \<noteq> [] \<Longrightarrow> tr \<in> set (a \<union>\<^sub>c b)"
  by (auto simp: choice_cnf_def non_empty_def)

theorem "size (a \<union>\<^sub>c b) = size (non_empty a) + size (non_empty b)"
  by (simp add: choice_cnf_def)

theorem comp_size: "x \<noteq> [] \<Longrightarrow> length (((xx # x) # xs) ;\<^sub>c b) = length ((x # xs) ;\<^sub>c b)"
  apply (induction b) by (auto simp: composition_cnf_def non_empty_def)

theorem comp_size2: "size ([[a]] ;\<^sub>c b) = size (non_empty b)"
  by (auto simp: composition_cnf_def non_empty_def)

theorem comp_size3: "size (a ;\<^sub>c b) = size (non_empty a) * size (non_empty b)"
proof (induction a)
  case Nil
  then show ?case by (auto simp: composition_cnf_def non_empty_def)
next
  case (Cons x xs)
  then show "length ((x # xs) ;\<^sub>c b) = length (non_empty (x # xs)) * length (non_empty b)"
  proof (induction x)
    case Nil
    then show ?case by (auto simp: composition_cnf_def non_empty_def)
  next
    case (Cons xx x)
    then show ?case
    proof (cases "x=[]")
      case True
      have "length (non_empty ([xx] # xs)) = length (non_empty xs) + 1" by (auto simp: non_empty_def)
      have "([xx] # xs) ;\<^sub>c b = [xs @ ys. xs \<leftarrow> non_empty ([xx] # xs), ys \<leftarrow> non_empty b]" by (auto simp: composition_cnf_def)
      have "... = [xs @ ys. xs \<leftarrow> non_empty [[xx]], ys \<leftarrow> non_empty b] @ [xs @ ys. xs \<leftarrow> non_empty xs, ys \<leftarrow> non_empty b]"
        by (metis choice_cnf_def cnf_choice2 concat_append map_append)
      have "... = ([[xx]] ;\<^sub>c b) @ (xs ;\<^sub>c b)"
        by (simp add: composition_cnf_def)
      have "size ([[xx]] ;\<^sub>c b) = size (non_empty b)"
        by (simp add: comp_size2)
      have "size (non_empty (xs ;\<^sub>c b)) = length (non_empty xs) * length (non_empty b)"
        by (metis Cons.prems non_empty15)
      have "length (([xx] # xs) ;\<^sub>c b) = size (non_empty b) + length (non_empty xs) * length (non_empty b)"
        by (simp add: Cons.prems \<open>([xx] # xs) ;\<^sub>c b = concat (map (\<lambda>xs. map ((@) xs) (non_empty b)) (non_empty ([xx] # xs)))\<close> \<open>concat (map (\<lambda>xs. map ((@) xs) (non_empty b)) (non_empty ([xx] # xs))) = concat (map (\<lambda>xs. map ((@) xs) (non_empty b)) (non_empty [[xx]])) @ concat (map (\<lambda>xs. map ((@) xs) (non_empty b)) (non_empty xs))\<close> \<open>concat (map (\<lambda>xs. map ((@) xs) (non_empty b)) (non_empty [[xx]])) @ concat (map (\<lambda>xs. map ((@) xs) (non_empty b)) (non_empty xs)) = [[xx]] ;\<^sub>c b @ xs ;\<^sub>c b\<close> \<open>length ([[xx]] ;\<^sub>c b) = length (non_empty b)\<close>)
      have "... = (1 + length (non_empty xs)) * length (non_empty b)"
        by simp
      have "... = length (non_empty ([xx] # xs)) * length (non_empty b)"
        using \<open>length (non_empty ([xx] # xs)) = length (non_empty xs) + 1\<close> by fastforce
      have "length (([xx] # xs) ;\<^sub>c b) = length (non_empty ([xx] # xs)) * length (non_empty b)"
        using \<open>(1 + length (non_empty xs)) * length (non_empty b) = length (non_empty ([xx] # xs)) * length (non_empty b)\<close> \<open>length (([xx] # xs) ;\<^sub>c b) = length (non_empty b) + length (non_empty xs) * length (non_empty b)\<close> \<open>length (non_empty b) + length (non_empty xs) * length (non_empty b) = (1 + length (non_empty xs)) * length (non_empty b)\<close> by argo
      then show ?thesis
        by (simp add: True)
    next
      case False
      have "length (non_empty ((xx # x) # xs)) = length (non_empty (x # xs))"
        apply (induction xs) using False by (auto simp: non_empty_def)
      
      have "length (((xx # x) # xs) ;\<^sub>c b) = length ((x # xs) ;\<^sub>c b)"
        by (simp add: False comp_size)
      have "... = length (non_empty (x # xs)) * length (non_empty b)"
        by (simp add: Cons.IH Cons.prems)
      have "... = length (non_empty ((xx # x) # xs)) * length (non_empty b)" using comp_size False apply auto
        by (simp add: \<open>length (non_empty ((xx # x) # xs)) = length (non_empty (x # xs))\<close>)
      then show "length (((xx # x) # xs) ;\<^sub>c b) = length (non_empty ((xx # x) # xs)) * length (non_empty b)"
        by (simp add: Cons.IH Cons.prems \<open>length (((xx # x) # xs) ;\<^sub>c b) = length ((x # xs) ;\<^sub>c b)\<close>)
    qed
  qed
qed

theorem comp_distrib_l: "equal_cnf (a ;\<^sub>c (b \<union>\<^sub>c c))  ((a ;\<^sub>c b) \<union>\<^sub>c (a ;\<^sub>c c))"
proof-
  have "set (a ;\<^sub>c (b \<union>\<^sub>c c)) \<subseteq> set ((a ;\<^sub>c b) \<union>\<^sub>c (a ;\<^sub>c c))"
    by (smt (verit) append_is_Nil_conv choice_prop choice_prop2 comp_prop comp_prop2 subsetI)
  have "set ((a ;\<^sub>c b) \<union>\<^sub>c (a ;\<^sub>c c)) \<subseteq> set (a ;\<^sub>c (b \<union>\<^sub>c c))" apply auto using choice_prop choice_prop2 comp_prop comp_prop2
    by (smt (verit, del_insts))
  have "size (a ;\<^sub>c (b \<union>\<^sub>c c)) = size ((a ;\<^sub>c b) \<union>\<^sub>c (a ;\<^sub>c c))"
    by (metis (no_types, lifting) choice_cnf_def choice_prop comp_size3 distrib_right length_append mult.commute non_empty14 non_empty15)
  show ?thesis
    by (simp add: equal_cnf_def \<open>length (a ;\<^sub>c (b \<union>\<^sub>c c)) = length ((a ;\<^sub>c b) \<union>\<^sub>c (a ;\<^sub>c c))\<close> \<open>set ((a ;\<^sub>c b) \<union>\<^sub>c (a ;\<^sub>c c)) \<subseteq> set (a ;\<^sub>c (b \<union>\<^sub>c c))\<close> \<open>set (a ;\<^sub>c (b \<union>\<^sub>c c)) \<subseteq> set ((a ;\<^sub>c b) \<union>\<^sub>c (a ;\<^sub>c c))\<close> subset_antisym)
qed

theorem compose_equiv: "evaluate [x] ; evaluate b \<equiv>\<^sub>p evaluate ([x] ;\<^sub>c b)"
proof -
  obtain x' where o1: "non_empty [x] = x'" by simp
  obtain b' where o2: "non_empty b = b'" by simp
  have "evaluate x' \<equiv>\<^sub>p evaluate [x]" using concat_prop7 o1
    using equiv_is_symetric by blast
  have "evaluate b' \<equiv>\<^sub>p evaluate b" using o2 concat_prop7
    using equiv_is_symetric by auto
  show ?thesis
proof (cases "x=[]")
  case True
  then have "evaluate [x] = Fail {}" apply (auto simp: Fail_def evaluate_def Skip_def) done
  from True have "[x] ;\<^sub>c b = []" apply (auto simp: composition_cnf_def)
    by (simp add: non_empty2) 
  have "evaluate ([x] ;\<^sub>c b) = Fail {}"
    by (simp add: \<open>[x] ;\<^sub>c b = []\<close> concat_prop2)
  then show ?thesis
    by (simp add: Big_choice.fail_compose \<open>evaluate [x] = Fail {}\<close>)
next
  case x_non: False
  have "evaluate [x] = Concat x" by (auto simp: evaluate_def)
  then show ?thesis using x_non
proof (induction "size (non_empty b)" arbitrary: x b rule: less_induct)
  case less
  then show ?case
  proof(cases "non_empty b=[]")
    case True
    then show ?thesis
      by (metis comp_cnf1 concat_prop11 eval_prop list.size(3) non_empty2 zero_neq_one)
  next
    case ge0: False
    obtain b1 b' where o2: "non_empty b = b1#b'" using ge0
      using list.exhaust by auto
    then have "evaluate [x] ; evaluate (b1#b') \<equiv>\<^sub>p evaluate [x] ; (evaluate [b1] \<union>\<^sub>p evaluate b')" using composition_equiv equals_equiv_relation_3
      by (metis concat_prop4)
    have "... \<equiv>\<^sub>p (evaluate [x] ; evaluate [b1] \<union>\<^sub>p evaluate [x] ; evaluate b')"
      using compose_distrib1_3 by blast
    have "... \<equiv>\<^sub>p Concat x ; Concat b1 \<union>\<^sub>p evaluate [x] ; evaluate b'" apply (auto simp: evaluate_def)
      using choice_commute_3 by auto
    then show ?thesis using less
    proof(cases "size (non_empty b)=1")
      case True
      obtain y where o1: "non_empty b=[y]"
        by (metis One_nat_def True length_0_conv length_Suc_conv)
      then show ?thesis
      proof (cases "size y=0")
        case True
        then have "evaluate [x] ; evaluate [y] \<equiv>\<^sub>p evaluate ([x] ;\<^sub>c [y])" apply (auto simp: composition_cnf_def evaluate_def Fail_def Skip_def)
          by (metis ge0 non_empty0 non_empty2 o1)
        then have False using True ge0 length_0_conv non_empty0 non_empty2 o1
          by metis
        then show ?thesis by simp
      next
        case False
        have "[x] ;\<^sub>c [y] = [x@y]" using less(3) False apply auto
          by (simp add: concat_prop9)
        then have "evaluate [x] ; evaluate [y] \<equiv>\<^sub>p evaluate ([x] ;\<^sub>c [y])"
          using less(3) False apply (auto simp: evaluate_def)
          using Concat_prop_5 equals_equiv_relation_3 apply auto
          by (simp add: Concat_prop_5 equals_equiv_relation_3 concat_prop9)
        have "[x] ;\<^sub>c b = [x] ;\<^sub>c [y]" using comp_cnf4 o1
          by metis
        have "size b = 1 \<Longrightarrow> evaluate b = evaluate [y]"
          by (simp add: eval_prop3 o1)
        moreover have "size b > 1 \<Longrightarrow> evaluate b = evaluate [y] \<union>\<^sub>p Skip {}"
          by (simp add: eval_prop2 o1)
        moreover have "size b \<ge> 1" using True
          by (metis non_empty_reduces_size)
        ultimately have "evaluate [x] ; evaluate b \<equiv>\<^sub>p evaluate [x] ; (evaluate [y] \<union>\<^sub>p Skip {})"
          by (metis \<open>evaluate [x] ; evaluate (b1 # b') \<equiv>\<^sub>p evaluate [x] ; (evaluate [b1] \<union>\<^sub>p evaluate b')\<close> concat_prop2 equals_equiv_relation_3 list.inject nless_le o1 o2 special_empty1)
        have "... \<equiv>\<^sub>p evaluate [x] ; evaluate [y]" using comp_prop1 by blast
        then have "evaluate [x] ; evaluate b \<equiv>\<^sub>p evaluate ([x] ;\<^sub>c [y])"
          by (metis (mono_tags, lifting) \<open>1 < length b \<Longrightarrow> evaluate b = evaluate [y] \<union>\<^sub>p Skip {}\<close> \<open>1 \<le> length b\<close> \<open>evaluate [x] ; evaluate [y] \<equiv>\<^sub>p evaluate ([x] ;\<^sub>c [y])\<close> \<open>length b = 1 \<Longrightarrow> evaluate b = evaluate [y]\<close> equiv_is_transitive nless_le)
        then show "evaluate [x] ; evaluate b \<equiv>\<^sub>p evaluate ([x] ;\<^sub>c b)"
          using \<open>[x] ;\<^sub>c b = [x] ;\<^sub>c [y]\<close> by force
      qed
      have "evaluate [x] ; evaluate [y] \<equiv>\<^sub>p evaluate ([x] ;\<^sub>c [y])"
        apply (auto simp: evaluate_def Fail_def)
        by (metis Choice.simps(2) concat_prop11 evaluate_def list.simps(8) list.simps(9))
    next
      case False
      have "length (non_empty b) > 1"
        using False o2 by force
      obtain b1 b2 nb where "b1#b2#nb = non_empty b"
        by (metis False One_nat_def Suc_length_conv length_0_conv neq_Nil_conv o2)
      have "evaluate [x] ; evaluate b = evaluate [x] ; evaluate (b1#b2#nb)"
        using False \<open>b1#b2#nb = non_empty b\<close> eval_prop by fastforce
      have "[x] ;\<^sub>c b = [x] ;\<^sub>c (b1#b2#nb)"
        using \<open>b1#b2#nb = non_empty b\<close> comp_cnf4 by auto
      have "evaluate (b1#b2#nb) = evaluate [b1] \<union>\<^sub>p evaluate (b2#nb)" apply (auto simp: evaluate_def)
        using Choice_prop_1_4 by force
      have "evaluate [x] ; (evaluate [b1] \<union>\<^sub>p evaluate (b2#nb)) \<equiv>\<^sub>p (evaluate [x] ; evaluate [b1] \<union>\<^sub>p evaluate [x] ; evaluate (b2#nb))"
        using compose_distrib1_3 by auto
      have "evaluate [x] ; evaluate [b1] \<equiv>\<^sub>p evaluate ([x] ;\<^sub>c [b1])" using less
        apply (cases "non_empty nb \<noteq> []")
        apply (meson concat_prop11)
        using concat_prop11 by blast
      have "length (non_empty (b2#nb)) < length (non_empty b)"
        by (metis \<open>b1 # b2 # nb = non_empty b\<close> impossible_Cons le_neq_implies_less non_empty0 non_empty_reduces_size nonempty_monotonic)
      have "evaluate [x] ; evaluate (b2#nb) \<equiv>\<^sub>p evaluate ([x] ;\<^sub>c (b2#nb))" using less
        using \<open>length (non_empty (b2 # nb)) < length (non_empty b)\<close> by blast
      have "evaluate ([x] ;\<^sub>c [b1]) \<union>\<^sub>p evaluate ([x] ;\<^sub>c (b2 # nb)) \<equiv>\<^sub>p evaluate (([x] ;\<^sub>c [b1]) \<union>\<^sub>c ([x] ;\<^sub>c (b2 # nb)))"
        by (simp add: choice_cnf_thm)
      have "(evaluate ([x] ;\<^sub>c [b1]) \<union>\<^sub>p evaluate ([x] ;\<^sub>c (b2#nb))) \<equiv>\<^sub>p evaluate ([x] ;\<^sub>c (b1#b2#nb))"
        by (metis \<open>b1 # b2 # nb = non_empty b\<close> \<open>evaluate ([x] ;\<^sub>c [b1]) \<union>\<^sub>p evaluate ([x] ;\<^sub>c (b2 # nb)) \<equiv>\<^sub>p evaluate (([x] ;\<^sub>c [b1]) \<union>\<^sub>c ([x] ;\<^sub>c (b2 # nb)))\<close> cnf_choice2 comp_distrib_l equal_eval non_empty0)
      
      then show "evaluate [x] ; evaluate b \<equiv>\<^sub>p evaluate ([x] ;\<^sub>c b)" using equiv_is_transitive equiv_is_symetric equiv_is_reflexive
        by (smt (verit, best) \<open>[x] ;\<^sub>c b = [x] ;\<^sub>c (b1 # b2 # nb)\<close> \<open>evaluate (b1 # b2 # nb) = evaluate [b1] \<union>\<^sub>p evaluate (b2 # nb)\<close> \<open>evaluate [x] ; (evaluate [b1] \<union>\<^sub>p evaluate (b2 # nb)) \<equiv>\<^sub>p evaluate [x] ; evaluate [b1] \<union>\<^sub>p evaluate [x] ; evaluate (b2 # nb)\<close> \<open>evaluate [x] ; evaluate (b2 # nb) \<equiv>\<^sub>p evaluate ([x] ;\<^sub>c (b2 # nb))\<close> \<open>evaluate [x] ; evaluate [b1] \<equiv>\<^sub>p evaluate ([x] ;\<^sub>c [b1])\<close> \<open>evaluate [x] ; evaluate b = evaluate [x] ; evaluate (b1 # b2 # nb)\<close> choice_equiv) 
    qed
  qed
qed
qed
qed

theorem comp_prop4: "evaluate (a ;\<^sub>c b) \<equiv>\<^sub>p evaluate a ; evaluate b"
proof (induction "size a" arbitrary: a b rule: less_induct)
  case less
  then show ?case
  proof (cases "size a = 0")
  case 0: True
  then show "evaluate (a ;\<^sub>c b) \<equiv>\<^sub>p evaluate a ; evaluate b" apply auto
    by (metis concat_prop1 concat_prop2 equals_equiv_relation_2 equiv_is_symetric equiv_is_transitive fail_compose_l fail_equiv)
next
  case Suc: False
  obtain x a' where o1: "x#a'=a"
    by (metis Suc length_0_conv list.exhaust)
  have l1: "evaluate [x] ; evaluate b \<equiv>\<^sub>p evaluate ([x] ;\<^sub>c b)"
    by (simp add: compose_equiv)
  have l2: "evaluate a' ; evaluate b \<equiv>\<^sub>p evaluate (a' ;\<^sub>c b)"
    using equiv_is_symetric less o1 by fastforce
  have l3: "equal_cnf (([x] ;\<^sub>c b) \<union>\<^sub>c (a' ;\<^sub>c b)) ((x#a') ;\<^sub>c b)"
    by (metis choic_cnf1 equal_cnf_def)
  have "evaluate (x # a') ; evaluate b \<equiv>\<^sub>p (evaluate [x] \<union>\<^sub>p evaluate a') ; evaluate b"
    using composition_equiv concat_prop4 equiv_is_reflexive by blast
  have "... \<equiv>\<^sub>p (evaluate [x] ; evaluate b \<union>\<^sub>p evaluate a' ; evaluate b)"
    by (simp add: compose_distrib2_3)
  have "... \<equiv>\<^sub>p (evaluate [x] ; evaluate b \<union>\<^sub>p evaluate (a' ;\<^sub>c b)) " using less l1 l2
    by (smt (verit) choice_equiv choice_idem_6 compose_distrib2_1 compose_distrib2_3)
  have "... \<equiv>\<^sub>p (evaluate ([x] ;\<^sub>c b) \<union>\<^sub>p evaluate (a' ;\<^sub>c b))"
    by (metis choice_equiv evaluate_equiv local.l1 non_empty15)
  have "... \<equiv>\<^sub>p evaluate (([x] ;\<^sub>c b) \<union>\<^sub>c (a' ;\<^sub>c b))"
    using choice_cnf_thm by blast
  have "... \<equiv>\<^sub>p evaluate ((x#a') ;\<^sub>c b)"
    by (metis choic_cnf1 concat_prop7 non_empty15)
  have "... = evaluate (a ;\<^sub>c b)"
    by (simp add: o1)
  then show "evaluate (a ;\<^sub>c b) \<equiv>\<^sub>p evaluate a ; evaluate b" using equiv_is_transitive
    by (smt (verit, best) \<open>evaluate ([x] ;\<^sub>c b) \<union>\<^sub>p evaluate (a' ;\<^sub>c b) \<equiv>\<^sub>p evaluate (([x] ;\<^sub>c b) \<union>\<^sub>c (a' ;\<^sub>c b))\<close> choic_cnf1 choice_equiv compose_distrib2_1 concat_prop3 equiv_is_symetric local.l1 local.l2 o1)
qed
qed

theorem normal_prop15: "set a = set b \<Longrightarrow> normal_of a B = normal_of b B"
proof (induction a)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have "normal_of (x # xs) B = (normal_of [x] B \<and> normal_of xs B)"
    using normal_prop12 by auto
  then show "normal_of (x # xs) B = normal_of b B"
  proof (cases "x \<in> set xs")
    case True
    then show ?thesis
      by (metis Cons.IH Cons.prems \<open>normal_of (x # xs) B = (normal_of [x] B \<and> normal_of xs B)\<close> insert_absorb list.simps(15) normal_prop8)
  next
    case False
    then show ?thesis
      by (metis Cons.prems basic_monotone basic_normal dual_order.eq_iff)
  qed
qed

theorem normal_prop16: "set a \<subseteq> set b \<Longrightarrow> normal_of b B \<longrightarrow> normal_of a B"
proof (induction a)
  case Nil
  then show ?case by (auto simp: normal_of_def basic_def)
next
  case (Cons x xs)
  have "normal_of (x # xs) B = (normal_of [x] B \<and> normal_of xs B)"
    using normal_prop12 by auto
  then show "normal_of b B \<longrightarrow> normal_of (x # xs) B"
  proof (cases "x \<in> set xs")
    case True
    then show ?thesis
      by (metis Cons.IH Cons.prems \<open>normal_of (x # xs) B = (normal_of [x] B \<and> normal_of xs B)\<close> insert_absorb list.simps(15) normal_prop8)
  next
    case False
    then show ?thesis
      using Cons.IH Cons.prems \<open>normal_of (x # xs) B = (normal_of [x] B \<and> normal_of xs B)\<close> normal_prop8 by auto
  qed
qed

theorem non_empty_is_smaller: "set (non_empty xs) \<subseteq> set xs"
  by (auto simp: non_empty_def)

theorem normal_prop17: "normal_of a B \<Longrightarrow> normal_of (non_empty a) B"
  using non_empty_is_smaller normal_prop16 by blast

theorem normal_prop18: "normal_of a B \<Longrightarrow> normal_of b B \<Longrightarrow> normal_of (a \<union>\<^sub>c b) B"
proof (induction "size a" arbitrary: a rule: "less_induct")
  case less
  have "finite B" using less
    using normal_prop4 by auto
  then show ?case
  proof (cases "a = []")
    case True
    have "a \<union>\<^sub>c b = non_empty b"
      by (simp add: True cnf_choice1)
    have "normal_of (non_empty b) B"
      using less.prems(2) non_empty_is_smaller normal_prop16 by blast
    then show "normal_of (a \<union>\<^sub>c b) B" apply (auto simp: normal_of_def non_empty_def basic_def choice_cnf_def)
      using True by auto
  next
    case False
    have "a \<union>\<^sub>c b = non_empty a @ non_empty b"
      by (simp add: choice_cnf_def)
    have "normal_of (non_empty b) B"
      using less.prems(2) non_empty_is_smaller normal_prop16 by blast
    have "normal_of (non_empty a) B"
      using less.prems(1) non_empty_is_smaller normal_prop16 by blast
    then show "normal_of (a \<union>\<^sub>c b) B" apply (auto simp: normal_of_def non_empty_def basic_def choice_cnf_def)
      by (smt (verit) Un_commute Un_iff \<open>normal_of (non_empty b) B\<close> basic_def fold_prop3 insert_def insert_iff non_empty_def normal_of_def singleton_conv sup.absorb_iff2)
  qed
qed

theorem normal_prop19: "normal_of [x] B \<Longrightarrow> normal_of b B \<Longrightarrow> normal_of [x@ys. ys \<leftarrow> non_empty b] B"
proof -
  assume a1: "normal_of [x] B" and  "normal_of b B"
  have "basic [x@ys. ys \<leftarrow> non_empty b] \<subseteq> basic [x] \<union> basic b" proof (induction b)
    case Nil
    then show ?case apply (auto simp: basic_def non_empty_def) done
  next
    case (Cons bb bs)
    then show ?case
    proof (cases "bb = []")
      case True
      then show ?thesis
        by (metis (no_types, lifting) Un_mono basic_monotone1 basic_monotone2 dual_order.trans list.set_intros(1) local.Cons non_empty3)
    next
      case f1: False
      then show ?thesis
      proof (cases "x=[]")
        case True
        then show ?thesis
          by (metis append_self_conv2 basic_monotone le_supI2 map_idI non_empty_is_smaller) 
      next
        case f2: False
        then show ?thesis
        proof (cases "bs=[]")
          case True
          then show ?thesis apply auto
            by (metis (no_types, lifting) Un_iff basic_monotone5 f1 list.exhaust list.simps(9) map_is_Nil_conv non_empty1 non_empty5)
        next
          case False
          have "map ((@) x) (non_empty (bb # bs)) = (x@bb)#map ((@) x) (non_empty (bs))"
            by (metis (no_types, lifting) f1 list.exhaust map_eq_Cons_conv non_empty5)
          have "basic (map ((@) x) (non_empty (bb # bs))) = basic [x @ bb] \<union> basic (map ((@) x) (non_empty bs))"
            using \<open>map ((@) x) (non_empty (bb # bs)) = (x @ bb) # map ((@) x) (non_empty bs)\<close> basic_decomp1 by auto
          have "... \<subseteq> basic [x @ bb] \<union> basic [x] \<union> basic bs"
            using Un_mono local.Cons by blast
          have "... = basic [x] \<union> basic [bb] \<union> basic bs"
            using basic_monotone5 by auto
          have "... = basic [x] \<union> basic (bb#bs)"
            using basic_decomp1 by auto
          then show ?thesis
            using \<open>basic (map ((@) x) (non_empty (bb # bs))) = basic [x @ bb] \<union> basic (map ((@) x) (non_empty bs))\<close> \<open>basic [x @ bb] \<union> basic (map ((@) x) (non_empty bs)) \<subseteq> basic [x @ bb] \<union> basic [x] \<union> basic bs\<close> \<open>basic [x @ bb] \<union> basic [x] \<union> basic bs = basic [x] \<union> basic [bb] \<union> basic bs\<close> by blast
        qed
      qed
    qed
  qed
  have "basic [x] \<union> basic b \<subseteq> insert \<lparr>State = {}, Pre = {}, post = {}\<rparr> B" using a1 apply (auto simp: normal_of_def)
    by (metis (no_types, lifting) Un_commute \<open>normal_of b B\<close> insert_iff insert_is_Un normal_of_def subsetD)
  show ?thesis apply (auto simp: normal_of_def)
    using \<open>basic (map ((@) x) (non_empty b)) \<subseteq> basic [x] \<union> basic b\<close> \<open>basic [x] \<union> basic b \<subseteq> insert \<lparr>State = {}, Pre = {}, post = {}\<rparr> B\<close> insertE subsetD apply auto[1]
    using \<open>normal_of b B\<close> normal_prop4 by auto
qed

theorem normal_prop20: "normal_of a B \<Longrightarrow> normal_of b B \<Longrightarrow> normal_of (a ;\<^sub>c b) B"
proof (induction "size a" arbitrary: a rule: "less_induct")
  case less
  have "finite B" using less
    using normal_prop4 by auto
  then show ?case
  proof (cases "a = []")
    case t1: True
    then show ?thesis
      by (metis comp_cnf2 less.prems(1) non_empty1)
  next
    case f1: False
    obtain x xs where o1: "a=x#xs"
      using f1 list.exhaust by auto
    then show "normal_of (a ;\<^sub>c b) B"
    proof (cases "size a = 1")
      case t2: True
      have "normal_of ([x] ;\<^sub>c b) B" proof (cases "non_empty b=[]")
        case t3: True
        then show ?thesis apply (metis comp_cnf1 less.prems(1) normal_prop12 o1) done
      next
        case f3: False
        have "[x] ;\<^sub>c b = [xs @ ys. xs \<leftarrow> non_empty [x], ys \<leftarrow> non_empty b]"
          by (simp add: composition_cnf_def)
        then show "normal_of ([x] ;\<^sub>c b) B"
        proof (cases "x=[]")
          case t4: True
          then show ?thesis apply auto
            by (metis \<open>finite B\<close> comp_cnf2 non_empty2 normal_prop17 normal_prop2)
        next
          case f4: False
          have "[xs @ ys. xs \<leftarrow> non_empty [x], ys \<leftarrow> non_empty b] = [x@ys. ys \<leftarrow> non_empty b]" using f4 by (auto simp: non_empty_def)
          have "normal_of [x] B"
            using less.prems(1) normal_prop12 o1 by auto
          have "normal_of ([x@ys. ys \<leftarrow> non_empty b]) B"
            by (simp add: \<open>normal_of [x] B\<close> less.prems(2) normal_prop19)
          then show ?thesis
            by (simp add: \<open>[x] ;\<^sub>c b = concat (map (\<lambda>xs. map ((@) xs) (non_empty b)) (non_empty [x]))\<close> \<open>concat (map (\<lambda>xs. map ((@) xs) (non_empty b)) (non_empty [x])) = map ((@) x) (non_empty b)\<close>)
        qed
      qed
      then show ?thesis
        using o1 t2 by auto
    next
      case False
      have "(x # xs) ;\<^sub>c b = [x] ;\<^sub>c b @ xs ;\<^sub>c b"
        by (metis choic_cnf1 choice_cnf_def non_empty15)
      have "normal_of ([x] ;\<^sub>c b) B"
        by (metis False One_nat_def Suc_lessI f1 length_Cons length_greater_0_conv less.hyps less.prems(1) less.prems(2) list.size(3) normal_prop12 o1) 
      have "normal_of ((x#xs) ;\<^sub>c b) B"
        by (metis \<open>normal_of ([x] ;\<^sub>c b) B\<close> choic_cnf1 impossible_Cons leI less.hyps less.prems(1) less.prems(2) normal_prop12 normal_prop18 o1)
      then show ?thesis
        by (simp add: o1)
    qed
  qed
qed

theorem civilized_thm1: "civilized_n p B n \<Longrightarrow> \<exists>(y::'a Normal_form). evaluate y \<equiv>\<^sub>p p \<and> normal_of y B"
proof -
  assume a1: "civilized_n p B n"
  have finite_b: "finite B"
    using a1 civilized_finite by auto 
  from a1 finite_b show "\<exists>(y::'a Normal_form). evaluate y \<equiv>\<^sub>p p \<and> normal_of y B"
  proof (induction n arbitrary: p B)
    case 0
    obtain B' where o0: "B' = insert (Fail{}) B" by simp
    show ?case
    proof (cases "p \<in> B'")
      case True
    then have "normal_of [[p]] B" using 0 o0 normal_prop3 apply (simp add: Fail_def) by (auto simp: normal_of_def basic_def)
    moreover have "evaluate [[p]] = p" by (auto simp: evaluate_def)
    ultimately show ?thesis
      by (metis equiv_is_reflexive)
    next
      case False
      have "p = Fail {}" using 0 
        apply (simp add: False Fail_def)
        using False o0 by auto
      then show ?thesis
        using False o0 by auto
    qed
    have a2: "p \<in> B'"
      using "0.prems"(1)
      using o0 by auto
  next
    case (Suc n)
    have IH: "\<And>p. civilized_n p B n \<Longrightarrow> \<exists>y. evaluate y \<equiv>\<^sub>p p \<and> normal_of y B"
      by (simp add: Suc.IH Suc.prems(2))
    assume a3: "civilized_n p B (Suc n)"
    then show "\<exists>y. evaluate y \<equiv>\<^sub>p p \<and> normal_of y B"
    proof (cases "civilized_n p B n")
      case True
      then show ?thesis
        by (simp add: IH)
    next
      case False
      have "civilized_n p B (Suc n)"
        using a3 by auto
      obtain a b where o1: "civilized_n a B n \<and> civilized_n b B n \<and> (a ; b = p \<or> a \<union>\<^sub>p b = p)"
        using False a3 by auto
      obtain a_y where o2: "evaluate a_y \<equiv>\<^sub>p a \<and> normal_of a_y B" using o1 IH by auto
      obtain b_y where o3: "evaluate b_y \<equiv>\<^sub>p b \<and> normal_of b_y B" using o1 IH by auto
      then show ?thesis
      proof (cases "a ; b = p")
        case True
        have "normal_of (a_y ;\<^sub>c b_y) B"
          by (simp add: normal_prop20 o2 o3)
        have "evaluate (a_y ;\<^sub>c b_y) \<equiv>\<^sub>p a ; b" using o2 o3
          using comp_prop4 composition_equiv equiv_is_transitive by blast
        have "\<exists>y. evaluate y \<equiv>\<^sub>p a ; b \<and> normal_of y B"
          using \<open>evaluate (a_y ;\<^sub>c b_y) \<equiv>\<^sub>p a ; b\<close> \<open>normal_of (a_y ;\<^sub>c b_y) B\<close> by auto 
        then show "\<exists>y. evaluate y \<equiv>\<^sub>p p \<and> normal_of y B"
          by (simp add: True) 
      next
        case False
        have "a \<union>\<^sub>p b = p"
          using False o1 by auto
        have "normal_of (a_y \<union>\<^sub>c b_y) B"
          by (simp add: normal_prop18 o2 o3)
        have "evaluate (a_y \<union>\<^sub>c b_y) \<equiv>\<^sub>p a \<union>\<^sub>p b" using o2 o3
          by (meson choice_cnf_thm choice_equiv equiv_is_symetric equiv_is_transitive)
        have "\<exists>y. evaluate y \<equiv>\<^sub>p a \<union>\<^sub>p b \<and> normal_of y B"
          using \<open>evaluate (a_y \<union>\<^sub>c b_y) \<equiv>\<^sub>p a \<union>\<^sub>p b\<close> \<open>normal_of (a_y \<union>\<^sub>c b_y) B\<close> by auto 
        then show "\<exists>y. evaluate y \<equiv>\<^sub>p p \<and> normal_of y B"
          by (simp add: \<open>a \<union>\<^sub>p b = p\<close>)
      qed
    qed
  qed
qed

theorem civilized_thm2: "civilized p B \<Longrightarrow> \<exists>(y::'a Normal_form). evaluate y \<equiv>\<^sub>p p \<and> normal_of y B"
  using civilized_def civilized_thm1 by blast


theorem fail_is_civilized: "finite B \<Longrightarrow> civilized (Fail{}) B"
  apply (induction B rule: "finite_induct")
  using civ_prop_1 civilized_empty3 apply blast
  by (meson civ_prop_1 civilized_empty3 finite_insert)

theorem civilized_thm3: "\<exists>(y::'a Normal_form). evaluate y = p \<and> normal_of y B \<Longrightarrow> civilized p B"
proof -
  assume a1: "\<exists>(y::'a Normal_form). evaluate y = p \<and> normal_of y B"
  have "finite B"
    using a1 normal_prop4 by auto
  obtain y where "evaluate y = p \<and> normal_of y B"
    using a1 by auto
  then show "civilized p B"
  proof (induction y)
    case Nil
    then show ?case apply (auto simp: evaluate_def normal_of_def civilized_def Fail_def basic_def)
      by (metis \<open>evaluate y = p \<and> normal_of y B\<close> civilized_def normal_civilized)
  next
    case (Cons a y)
    then show "civilized p B"
    proof (induction a)
      case Nil
      then show ?case apply (auto simp: )
        by (simp add: normal_civilized)
    next
      case (Cons a1 a2)
      assume "evaluate ((a1 # a2) # y) = p \<and> normal_of ((a1 # a2) # y) B"
      then show "civilized p B"
      proof (cases "y = []")
        case True
        from Cons True show ?thesis apply (auto simp: civilized_def)
          using civilized_def normal_civilized apply blast
          using \<open>finite B\<close> by blast
      next
        case False
        from Cons False show ?thesis
          using normal_civilized by blast
      qed
    qed
  qed
qed

theorem composition_cnf_prop1: "[[x]] ;\<^sub>c xs = [x#ys. ys \<leftarrow> non_empty xs]"
  by (auto simp: composition_cnf_def non_empty_def)


theorem composition_cnf_prop2: "[y#ys] ;\<^sub>c xs = [( y#ys)@t. t \<leftarrow> non_empty xs]"
  by (auto simp: composition_cnf_def non_empty_def)


theorem Para_basic: "x \<parallel> [[]] = x" by (auto simp: cnf_concurrency_def)

theorem non2_prop1: "non_empty x = [] \<Longrightarrow> non_empty2 (x # xs) = non_empty2 xs"
  by (auto simp: non_empty2_def)

theorem non2_prop2: "non_empty x \<noteq> [] \<Longrightarrow> non_empty2 (x # xs) = non_empty x # non_empty2 xs"
  by (auto simp: non_empty2_def)

theorem non2_prop3: "non_empty2 (xs @ ys) = non_empty2 xs @ non_empty2 ys"
proof (induction xs)
  case Nil
  then show ?case apply (simp add: non_empty2_def) done
next
  case (Cons prog' xs)
  then show "non_empty2 ((prog' # xs) @ ys) = non_empty2 (prog' # xs) @ non_empty2 ys"
  proof (cases "non_empty prog' = []")
    case True
    then show ?thesis
      by (simp add: local.Cons non2_prop1)
  next
    case False
    then show ?thesis
      by (simp add: local.Cons non2_prop2)
  qed
qed

theorem non2_prop4: "size (non_empty2 xs) \<le> size xs"
  apply (induction xs)
  by (auto simp: non_empty2_def)

theorem non2_prop5: "non_empty2 (x#xs) = x#xs \<Longrightarrow> non_empty2 xs = xs"
  by (metis impossible_Cons list.inject non2_prop1 non2_prop2 non2_prop4)

theorem non2_prop6: "non_empty2 xs = xs \<Longrightarrow> \<forall>prog \<in> set xs. prog \<noteq> [] \<and> (\<forall>path \<in> set prog. path \<noteq> [])"
  apply (induction xs)
  apply simp
  by (metis choice_prop cnf_choice2 list.set_cases non2_prop1 non2_prop2 non2_prop5 set_ConsD)

theorem non_prop1: "non_empty xs = xs \<Longrightarrow> \<forall>path \<in> set xs. path \<noteq> []"
  by (metis choice_prop cnf_choice1)

theorem non2_prop7: "non_empty2 xs = xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> non_empty x = x"
  by (simp add: non2_prop6 non_empty14)

theorem non2_idem: "non_empty2 xs = non_empty2 (non_empty2 xs)"
proof (induction xs)
  case Nil
  then show ?case  apply (auto simp: non_empty2_def non_empty_def) done
next
  case (Cons prog xs)
  assume "non_empty2 xs = non_empty2 (non_empty2 xs)"
  then show "non_empty2 (prog # xs) = non_empty2 (non_empty2 (prog # xs))"
  proof (cases "non_empty prog = []")
    case True
    then show ?thesis
      using local.Cons non2_prop1 by force
  next
    case False
    then show ?thesis
      by (metis local.Cons non2_prop2 non_empty0)
  qed
qed

theorem inter_head: "p \<in> set ((x#xs) \<interleave> (y#ys)) \<Longrightarrow> hd p = x \<or> hd p = y"
proof -
  assume "p \<in> set ((x#xs) \<interleave> (y#ys))"
  obtain p' where "p' \<in> set ((x#xs) \<interleave> (y#ys))"
    using \<open>p \<in> set ((x # xs) \<interleave> (y # ys))\<close> by blast
  have "interleave (x#xs) (y#ys) = 
     map ((#) x) (xs \<interleave> (y#ys)) @
     map ((#) y) ((x#xs) \<interleave> ys)" by simp
  have "set ((x#xs) \<interleave> (y#ys)) = set (map ((#) x) (xs \<interleave> (y#ys))) \<union> set (map ((#) y) ((x#xs) \<interleave> ys))"
    by auto
  have "\<forall>q \<in> set (map ((#) x) (xs \<interleave> (y#ys))). hd q = x"
    by simp
  have "\<forall>q \<in> set (map ((#) y) ((x#xs) \<interleave> ys)). hd q = y"
    by simp
  show "hd p = x \<or> hd p = y"
    using \<open>p \<in> set ((x # xs) \<interleave> (y # ys))\<close> by auto
qed

theorem count_prop: "count_list (map ((#) x) xs) (x#p) = count_list xs p"
  apply (induction xs arbitrary: x p)
  by auto

theorem count_prop2: "x\<noteq>y \<Longrightarrow> count_list (map ((#) x) xs) (y#p) = 0"
  using count_notin by force

theorem interleave_non_empty: "p \<in> set ((x#xs) \<interleave> (y#ys)) \<Longrightarrow> p \<noteq> []"
  apply (simp) by auto

theorem inter2: "count_list (ys \<interleave> xs) p = count_list (xs \<interleave> ys) p"
proof (induction p arbitrary: xs ys)
  case Nil
  then show ?case apply (cases "xs = []")
    apply simp apply (cases "ys = []") apply simp
    by (smt (verit) count_notin interleave.elims interleave_non_empty)
next
  case Cons0: (Cons a p)
  then show ?case
  proof (induction xs arbitrary: ys)
    case Nil
    then show ?case
      by simp
  next
    case Cons1: (Cons x xs')
    then show ?case
    proof (induction ys)
      case Nil
      then show ?case by simp
    next
      case Cons2: (Cons y ys')
      have "count_list (ys' \<interleave> (x # xs')) (a#p) = count_list ((x # xs') \<interleave> ys') (a#p)"
        by (simp add: Cons1 Cons2.IH)
      have "(x # xs') \<interleave> (y # ys') =  map ((#) x) (xs' \<interleave> (y#ys')) @ map ((#) y) ((x#xs') \<interleave> ys')" by simp
      have "(y # ys') \<interleave> (x # xs') =  map ((#) y) (ys' \<interleave> (x#xs')) @ map ((#) x) ((y#ys') \<interleave> xs')" by simp
  
      have "count_list ((x # xs') \<interleave> (y # ys')) (a#p) = 
            count_list (map ((#) x) (xs' \<interleave> (y#ys'))) (a#p) + 
            count_list (map ((#) y) ((x#xs') \<interleave> ys')) (a#p)"
        by simp
  
      show ?case
      proof (cases "count_list ((x#xs') \<interleave> (y#ys')) (a#p) = 0")
        case t1: True
        have "(a#p) \<notin> set ((x#xs')\<interleave> (y#ys'))"
          by (meson count_list_0_iff t1)
        have "count_list (map ((#) x) ( xs' \<interleave>(y#ys'))        @             map ((#) y) ( (x#xs') \<interleave>ys')) (a#p) = 
              count_list (map ((#) x) ( xs' \<interleave>(y#ys'))) (a#p) + count_list (map ((#) y) ( (x#xs') \<interleave>ys')) (a#p)"
          by simp
        then show ?thesis
        proof (cases "a=x")
          case t2: True
          have "count_list (map ((#) x) ( xs'\<interleave> (y#ys'))) (a#p) = count_list (( xs' \<interleave>(y#ys'))) p"
            by (simp add: t2 count_prop)
          have "x=y \<Longrightarrow> count_list (map ((#) y) ( (x#xs') \<interleave>ys')) (x#p) = count_list (( (x#xs') \<interleave>ys')) p"
            by (simp add: count_prop)
          have "x\<noteq>y \<Longrightarrow> count_list (map ((#) y) ( (x#xs')\<interleave> ys')) (x#p) = 0"
            by (simp add: count_prop2)
          have "count_list (( (x#xs') \<interleave>ys')) p = count_list (( ys' \<interleave>(x#xs') )) p"
            by (simp add: Cons0)
          have "count_list (( xs' \<interleave>(y#ys'))) p = count_list (( (y#ys') \<interleave>xs' )) p"
            by (simp add: Cons0)
          then show ?thesis apply (cases "x=y")
            apply (metis \<open>count_list ( (x # xs') \<interleave>(y # ys')) (a # p) = count_list (map ((#) x) ( xs' \<interleave>(y # ys'))) (a # p) + count_list (map ((#) y) ( (x # xs') \<interleave>ys')) (a # p)\<close> \<open>count_list ( (x # xs') \<interleave>ys') p = count_list ( ys'\<interleave> (x # xs')) p\<close> \<open> (y # ys') \<interleave>(x # xs') = map ((#) y) ( ys'\<interleave> (x # xs')) @ map ((#) x) ( (y # ys')\<interleave> xs')\<close> add_is_0 count_list_append count_prop t1 t2)
            by (simp add: count_prop count_prop2 t2)
        next
          case f2: False
          then show ?thesis
          proof (cases "a=y")
            case t3: True
            have "count_list (map ((#) y) ( (x#xs') \<interleave>ys')) (a#p) = count_list (( (x#xs') \<interleave>ys')) p"
              by (simp add: count_prop t3)
            have "x=y \<Longrightarrow> count_list (map ((#) x) ( xs' \<interleave>(y#ys'))) (y#p) = count_list (( xs'\<interleave> (y#ys'))) p"
              by (simp add: count_prop)
            have "x\<noteq>y \<Longrightarrow> count_list (map ((#) x) ( xs'\<interleave> (y#ys'))) (y#p) = 0"
              by (simp add: count_prop2)
            have "count_list (( (x#xs')\<interleave> ys')) p = count_list (( ys' \<interleave>(x#xs') )) p"
              by (simp add: Cons0)
            have "count_list (( xs'\<interleave> (y#ys'))) p = count_list (( (y#ys')\<interleave> xs' )) p"
              by (simp add: Cons0)
              then show ?thesis
                by (smt (verit, best) \<open>(y # ys') \<interleave> (x # xs') = map ((#) y) (ys' \<interleave> (x # xs')) @ map ((#) x) ((y # ys') \<interleave> xs')\<close> \<open>count_list ((x # xs') \<interleave> (y # ys')) (a # p) = count_list (map ((#) x) (xs' \<interleave> (y # ys'))) (a # p) + count_list (map ((#) y) ((x # xs') \<interleave> ys')) (a # p)\<close> \<open>count_list ((x # xs') \<interleave> ys') p = count_list (ys' \<interleave> (x # xs')) p\<close> add_is_0 count_list_append count_prop count_prop2 t1)
            next
            case f3: False
            then show ?thesis
              by (metis \<open>count_list ( (x # xs') \<interleave>(y # ys')) (a # p) = count_list (map ((#) x) ( xs' \<interleave>(y # ys'))) (a # p) + count_list (map ((#) y) ( (x # xs')\<interleave> ys')) (a # p)\<close> \<open> (y # ys') \<interleave>(x # xs') = map ((#) y) (ys' \<interleave>(x # xs')) @ map ((#) x) ( (y # ys')\<interleave> xs')\<close> count_list_append count_prop2 f2 t1)
          qed
        qed
      next
        case f1: False
        have "(a#p) \<in> set ((x#xs') \<interleave> (y#ys'))"
          by (meson count_notin f1)
        then show ?thesis 
        proof (cases "x=y")
          case t2:True
          have "a = x"
            using t2 \<open>(a#p) \<in> set ( (x # xs') \<interleave>(y # ys'))\<close> by auto
          have " (x # xs') \<interleave>(y # ys) =  map ((#) x) (( xs'\<interleave> (x#ys)) @ ( (x#xs') \<interleave>ys))"
            using t2 by auto
          have "count_list (map ((#) x) ( xs' \<interleave>(x # ys) @  (x # xs') \<interleave>ys)) (a#p) = count_list ( xs' \<interleave>(x # ys) @  (x # xs') \<interleave>ys) p"
            by (simp add: \<open>a = x\<close> count_prop)
          have "count_list ( (x # ys')\<interleave> (x # xs')) (a#p) = count_list ( (ys')\<interleave> (x # xs')) p + count_list ( (x # ys') \<interleave>(xs')) p"
            by (simp add: \<open>a = x\<close> count_prop)
          have "count_list ( (ys')\<interleave> (x # xs')) p = count_list ( (x # xs') \<interleave>(ys')) p"
            using Cons0 by auto
          then show "count_list ( (y # ys') \<interleave>(x # xs')) (a # p) = count_list ( (x # xs') \<interleave>(y # ys')) (a # p)"
            by (simp add: Cons0 t2 \<open>a = x\<close> count_prop)
        next
          case f2: False
          then show ?thesis
          proof (cases "a = x")
            case t3: True
            have "count_list (map ((#) y) ( (x#xs) \<interleave>ys)) (x#p) = 0" using f2 count_prop2
              by metis
            have "count_list (map ((#) x) ( xs\<interleave> (y#ys))) (x#p) = count_list ( xs \<interleave>(y#ys)) (p)"
              by (simp add: count_prop)
            have "count_list (map ((#) x) ( xs \<interleave>(y#ys))) (x#p) + count_list (map ((#) y) ( (x#xs)\<interleave> ys)) (x#p) = count_list ( (y#ys) \<interleave>xs) p"
              by (simp add: Cons0 \<open>count_list (map ((#) x) ( xs \<interleave>(y # ys))) (x # p) = count_list ( xs \<interleave>(y # ys)) p\<close> \<open>count_list (map ((#) y) ( (x # xs)\<interleave> ys)) (x # p) = 0\<close>)
            have "count_list ( (y#ys)\<interleave> xs) p = count_list ( xs \<interleave>(y#ys)) p"
              by (simp add: Cons0)
    
    
            have "count_list (map ((#) y) ( ys \<interleave>(x#xs))) (x#p) = 0" using f2 count_prop2
              by metis
            have "count_list (map ((#) x) ( (y#ys) \<interleave>xs)) (x#p) = count_list ( (y#ys) \<interleave>xs) (p)"
              by (simp add: count_prop)
            have "count_list (map ((#) x) ( (y#ys)\<interleave> xs)) (x#p) + count_list (map ((#) y) ( ys \<interleave>(x#xs))) (x#p) = count_list ( xs\<interleave> (y#ys)) p"
              by (simp add: Cons0 \<open>count_list (map ((#) x) ( (y # ys)\<interleave> xs)) (x # p) = count_list ( (y # ys) \<interleave>xs) p\<close> \<open>count_list (map ((#) y) ( ys \<interleave>(x # xs))) (x # p) = 0\<close>)
            have "count_list ( xs \<interleave>(y#ys)) p = count_list ( (y#ys) \<interleave>xs) p"
              by (simp add: Cons0)
    
            then show "count_list ( (y # ys')\<interleave> (x # xs')) (a # p) = count_list ( (x # xs') \<interleave>(y # ys')) (a # p)"
              by (smt (verit, del_insts) Cons0 Nat.add_0_right \<open>count_list ( (x # xs') \<interleave>(y # ys')) (a # p) = count_list (map ((#) x) ( xs' \<interleave>(y # ys'))) (a # p) + count_list (map ((#) y) ( (x # xs') \<interleave>ys')) (a # p)\<close> \<open> (y # ys')\<interleave> (x # xs') = map ((#) y) ( ys' \<interleave>(x # xs')) @ map ((#) x) ( (y # ys')\<interleave> xs')\<close> add_cancel_left_left count_list_append count_prop count_prop2 f2)
          next
            case f3: False
            have f3: "a = y"
              using \<open>a # p \<in> set ( (x # xs') \<interleave> (y # ys'))\<close> f2 f3 by auto
            have "count_list (map ((#) x) ( xs \<interleave> (y#ys))) (y#p) = 0" using f3 count_prop2
              by (metis f2)
            have "count_list (map ((#) y) ( (x#xs) \<interleave> ys)) (y#p) = count_list ((x#xs) \<interleave> ys) (p)"
              by (simp add: count_prop)
            have "count_list (map ((#) x) ( xs \<interleave> (y#ys))) (y#p) + count_list (map ((#) y) ( (x#xs)\<interleave> ys)) (y#p) = count_list ( (x#xs) \<interleave> ys) (p)"
              using \<open>count_list (map ((#) x) ( xs \<interleave> (y # ys))) (y # p) = 0\<close> \<open>count_list (map ((#) y) ( (x # xs) \<interleave> ys)) (y # p) = count_list ( (x # xs) \<interleave> ys) p\<close> add_0 f3 map_eq_map_tailrec by auto
            have "count_list ((y#ys) \<interleave>xs) p = count_list ( xs \<interleave> (y#ys)) p"
              by (simp add: Cons0)
    
    
            have "count_list (map ((#) x) ( (y#ys) \<interleave>xs)) (y#p) = 0" using f3 count_prop2
              by (metis f2)
            have "count_list (map ((#) y) (ys \<interleave> (x#xs))) (y#p) = count_list ( ys \<interleave> (x#xs)) (p)"
              by (simp add: count_prop)
            have "count_list (map ((#) x) ((y#ys) \<interleave> xs)) (y#p) + count_list (map ((#) y) ( ys \<interleave> (x#xs))) (y#p) = count_list ( ys \<interleave> (x#xs)) (p)"
              by (simp add: \<open>count_list (map ((#) x) ( (y # ys) \<interleave> xs)) (y # p) = 0\<close> \<open>count_list (map ((#) y) ( ys \<interleave> (x # xs))) (y # p) = count_list ( ys \<interleave> (x # xs)) p\<close>)
            have "count_list ( xs \<interleave>(y#ys)) p = count_list ( (y#ys) \<interleave> xs) p"
              by (simp add: Cons0)
    
            then show "count_list ( (y # ys') \<interleave> (x # xs')) (a # p) = count_list ( (x # xs') \<interleave> (y # ys')) (a # p)"
              by (smt (verit, del_insts) Cons0 Nat.add_0_right \<open>count_list ((x # xs') \<interleave> (y # ys')) (a # p) = count_list (map ((#) x) ( xs' \<interleave> (y # ys'))) (a # p) + count_list (map ((#) y) ((x # xs') \<interleave> ys')) (a # p)\<close> \<open> (y # ys')  \<interleave>(x # xs') = map ((#) y) ( ys' \<interleave> (x # xs')) @ map ((#) x) ( (y # ys') \<interleave> xs')\<close> add_cancel_left_left count_list_append count_prop count_prop2 f2)
          qed
        qed
      qed
    qed
  qed
qed

theorem inter_perm: "ys \<interleave> xs \<in> set (permutations (xs \<interleave> ys))"
  using inter2
  by (metis count_invariant_3)

theorem t1: "size xs = size ys \<Longrightarrow> \<forall>t\<in>set (zip xs ys). fst t \<in> set (permutations (snd t)) \<Longrightarrow> concat xs \<in> set (permutations (concat ys))"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by auto
next
  case Cons_x: (Cons x xss)
  then show ?case
  proof -
    obtain y yss where "y#yss=ys"
      by (metis Cons_x.prems(1) Suc_length_conv)
    have "length xss = length yss"
      using Cons_x.prems(1) \<open>y # yss = ys\<close> by auto
    have "\<forall>t\<in>set (zip xss yss). fst t \<in> set (permutations (snd t))"
      using Cons_x.prems(2) \<open>y # yss = ys\<close> by auto
    then have l2: "concat xss \<in> set (permutations (concat yss))" using Cons_x(1)[of yss]
      using \<open>length xss = length yss\<close> by linarith
    have "\<forall>t\<in>set (zip (x # xss) (y # yss)). fst t \<in> set (permutations (snd t))"
      using Cons_x.prems(2) \<open>y # yss = ys\<close> by auto
    moreover have "(x,y) \<in> set (zip (x # xss) (y # yss))"
      by simp
    ultimately have l1: "x \<in> set (permutations y)" by auto
    have "concat (x # xss) \<in> set (permutations (concat (y # yss)))" using l1 l2 proof (induction x arbitrary: y)
      case Nil
      then show ?case
        using length_inv by fastforce
    next
      case (Cons xx x)
      obtain y_s y_e where "y_s@xx#y_e=y \<and> (y_s@y_e) \<in> set (permutations x)"
        by (metis Cons.prems(1) perm_inv_3 permutation_split_set)
      have "concat ((xx # x) # xss) = (xx # x) @ concat xss" by simp
      have "x @ concat xss \<in> set (permutations (concat ((y_s@y_e)#yss)))"
        by (metis Cons.IH \<open>y_s @ xx # y_e = y \<and> y_s @ y_e \<in> set (permutations x)\<close> concat.simps(2) local.l2 perm_inv_3)
      have "xx # x @ concat xss \<in> set (permutations (concat ((xx#y_s@y_e)#yss)))"
        by (metis \<open>x @ concat xss \<in> set (permutations (concat ((y_s @ y_e) # yss)))\<close> append_Cons concat.simps(2) perm_1)
      have "concat ((xx#y_s@y_e)#yss) \<in> set (permutations (concat ((y_s@xx#y_e)#yss)))" apply auto
        by (metis \<open>x @ concat xss \<in> set (permutations (concat ((y_s @ y_e) # yss)))\<close> append_assoc concat.simps(2) perm_inv_2 perm_inv_3 permutations_set_equality)
      then show "concat ((xx # x) # xss) \<in> set (permutations (concat (y # yss)))"
        by (metis Cons_eq_appendI \<open>concat ((xx # x) # xss) = (xx # x) @ concat xss\<close> \<open>xx # x @ concat xss \<in> set (permutations (concat ((xx # y_s @ y_e) # yss)))\<close> \<open>y_s @ xx # y_e = y \<and> y_s @ y_e \<in> set (permutations x)\<close> permutations_set_equality)
    qed
    then show "concat (x # xss) \<in> set (permutations (concat ys))"
      by (simp add: \<open>y # yss = ys\<close>)
  qed
qed


theorem t15: "size xs = size ys \<Longrightarrow> \<exists>xs'. xs' \<in> set (permutations xs) \<and> (\<forall>t\<in>set (zip xs' ys). fst t \<in> set (permutations (snd t))) \<Longrightarrow> concat xs \<in> set (permutations (concat ys))"
proof (induction "size xs" arbitrary: xs ys rule: less_induct)
  case less
  obtain xs'' where o2: "xs'' \<in> set (permutations xs) \<and> (\<forall>t\<in>set (zip xs'' ys). fst t \<in> set (permutations (snd t)))"
    using less.prems(2) by auto
  then have "xs'' \<in> set (permutations xs)" by simp
  then have "concat xs'' \<in> set (permutations (concat xs))" proof (induction xs arbitrary: xs'')
    case Nil
    then show ?case by auto
  next
    case (Cons x xss)
    obtain x_s x_e where "x_s@x#x_e=xs'' \<and> x_s@x_e \<in> set (permutations xss)"
      by (metis Cons.prems permutation_split_set)
    have "concat (x_s@x_e) \<in> set (permutations (concat xss))"
      using Cons.IH \<open>x_s @ x # x_e = xs'' \<and> x_s @ x_e \<in> set (permutations xss)\<close> by blast
    then have "x @ concat (x_s @ x_e) \<in> set (permutations (concat (x#xss)))"apply (induction x) apply auto
      by (meson l2)
    have "x @ concat (x_s @ x_e) \<in> set (permutations (concat (x_s @ x # x_e)))" apply (induction x) apply auto
      apply (simp add: in_set_member permutation_reflexive)
      by (meson perm_inv_2 perm_inv_3)
    then show "concat xs'' \<in> set (permutations (concat (x # xss)))"
      using \<open>x @ concat (x_s @ x_e) \<in> set (permutations (concat (x # xss)))\<close> \<open>x_s @ x # x_e = xs'' \<and> x_s @ x_e \<in> set (permutations xss)\<close> perm_inv_3 permutations_set_equality by blast
  qed
  have "size xs'' = size xs"
    by (simp add: \<open>xs'' \<in> set (permutations xs)\<close> length_inv)
  from o2 show ?case
  proof (cases xs'')
    case Nil
    then show ?thesis using o2 apply auto
      by (metis concat.simps(1) in_set_member length_0_conv less.prems(1) permutation_size permutations.simps(1) subseqs.simps(1) subseqs_refl)
  next
    case (Cons x xss)
    then have "length xss < length xs"
      using \<open>length xs'' = length xs\<close> by fastforce
    obtain y yss where o1: "y#yss=ys \<and> (\<forall>t\<in>set (zip xss yss). fst t \<in> set (permutations (snd t)))"
    proof -
      obtain y yss where "y#yss=ys"
        by (metis Suc_length_conv \<open>length xs'' = length xs\<close> less.prems(1) local.Cons)
      have "(\<forall>t\<in>set (zip xs'' ys). fst t \<in> set (permutations (snd t)))"
        using o2 by fastforce
      have "set (zip xss yss) \<union> {(x,y)} = set (zip xs'' ys)"
        using \<open>y # yss = ys\<close> local.Cons by auto
      show "(\<And>y yss. y # yss = ys \<and> (\<forall>t\<in>set (zip xss yss). fst t \<in> set (permutations (snd t))) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
        using \<open>\<forall>t\<in>set (zip xs'' ys). fst t \<in> set (permutations (snd t))\<close> \<open>y # yss = ys\<close> list.set_intros(2) local.Cons zip_Cons_Cons by force
    qed
    then have "length xss = length yss" using Cons less(2) o1 o2 apply auto
      by (metis length_Cons length_inv old.nat.inject)
    then have "concat xss \<in> set (permutations (concat yss))" using less(1)[of xss yss]
      by (simp add: o1 t1)
    have "(x, y) \<in> set (zip xs'' ys)"
      using local.Cons o1 by force
    then have "x \<in> set (permutations y)"
      using o2 by auto
    have "concat (x#xss) \<in> set (permutations (concat (y#yss)))" apply auto
      by (metis \<open>length xs'' = length xs\<close> concat.simps(2) less.prems(1) local.Cons o1 o2 t1)
    have "concat xs'' \<in> set (permutations (concat ys))"
      using \<open>concat (x # xss) \<in> set (permutations (concat (y # yss)))\<close> local.Cons o1 by auto
    then show ?thesis
      using \<open>concat xs'' \<in> set (permutations (concat xs))\<close> perm_inv_3 permutations_set_equality by blast
  qed
qed

theorem t2: "size [f x y. x \<leftarrow> xs, y \<leftarrow> ys] = size xs * size ys"
  apply (induction xs)
  by (auto)

theorem t3: "size [path_m \<interleave> path_n. path_m \<leftarrow> xs, path_n \<leftarrow> ys] = size [path_m \<interleave> path_n. path_m \<leftarrow> ys, path_n \<leftarrow> xs]"
proof -
  have "size [path_m \<interleave> path_n. path_m \<leftarrow> xs, path_n \<leftarrow> ys] = size xs * size ys"
    by (simp add: t2)
  have "size [path_m \<interleave> path_n. path_m \<leftarrow> ys, path_n \<leftarrow> xs] = size ys * size xs"
    by (simp add: t2)
  show ?thesis
    by (simp add: \<open>length (concat (map (\<lambda>path_m. map ((\<interleave>) path_m) xs) ys)) = length ys * length xs\<close> \<open>length (concat (map (\<lambda>path_m. map ((\<interleave>) path_m) ys) xs)) = length xs * length ys\<close>)
qed




value "[path_m \<interleave> path_n. path_m \<leftarrow> [[], []], path_n \<leftarrow> [[a\<^sub>1], [], []]]"
value "[path_m \<interleave> path_n. path_m \<leftarrow> [[a\<^sub>1], [], []], path_n \<leftarrow> [[], []]]"
value "[path_m \<interleave> path_n. path_m \<leftarrow> [[], []], path_n \<leftarrow> [[a\<^sub>1], [], []]]"
value "[path_m \<interleave> path_n. path_m \<leftarrow> [[a\<^sub>1], [], []], path_n \<leftarrow> [[], []]] !1"


theorem index_prop: "length xs = a \<Longrightarrow> (xs@ys)!(a+b) = ys!b"
  apply (induction xs)
  apply simp
  by auto

theorem index_prop2: "a < length xs \<Longrightarrow> xs!a = (xs@ys)!a"
  apply (induction ys)
  apply auto
  by (simp add: nth_append)

theorem index_prop3: "size (concat (map (\<lambda>x. f x y # map (f x) ys) xs)) = size xs * size (y#ys)"
  apply (induction xs) by auto

lemma list_comp_index_1: \<comment> \<open>x_ind = size xs\<close>
  "y_ind < size ys \<Longrightarrow> 
   [f x y. x \<leftarrow> (xs@[x]), y \<leftarrow> ys] ! (size xs * size ys + y_ind) = f ((xs@[x]) ! size xs) (ys ! y_ind)"
proof -
  assume "y_ind < size ys"
  have "[f x y. x \<leftarrow> (xs@[x]), y \<leftarrow> ys] = [f x y. x \<leftarrow> (xs), y \<leftarrow> ys] @ [f x y. x \<leftarrow> [x], y \<leftarrow> ys]"
    by simp
  have "size ([f x y. x \<leftarrow> (xs), y \<leftarrow> ys]) = size xs * size ys"
    by (simp add: t2)
  have "[f x y. x \<leftarrow> (xs@[x]), y \<leftarrow> ys] ! (size xs * size ys + y_ind) = [f x y. x \<leftarrow> [x], y \<leftarrow> ys] ! y_ind"
    by (simp add: \<open>length (concat (map (\<lambda>x. map (f x) ys) xs)) = length xs * length ys\<close> index_prop)
  have "(xs@[x]) ! size xs = x"
    by simp
  have "[f x y. y \<leftarrow> ys] ! y_ind = f x (ys ! y_ind)" using \<open>y_ind < size ys\<close> apply (induction ys) apply auto
    by (metis Suc_length_conv list.simps(9) nth_map)
  have "[f x y. x \<leftarrow> [x], y \<leftarrow> ys] ! y_ind = f x (ys ! y_ind)"
    by (simp add: \<open>map (f x) ys ! y_ind = f x (ys ! y_ind)\<close>)
  show ?thesis
    using \<open>concat (map (\<lambda>x. map (f x) ys) (xs @ [x])) ! (length xs * length ys + y_ind) = concat (map (\<lambda>x. map (f x) ys) [x]) ! y_ind\<close> \<open>concat (map (\<lambda>x. map (f x) ys) [x]) ! y_ind = f x (ys ! y_ind)\<close> by auto
qed


lemma list_comp_index_2: \<comment> \<open>x_ind = 0\<close>
  "y_ind < size ys \<Longrightarrow> [f x y. x \<leftarrow> (x#xs), y \<leftarrow> ys] ! (0 * size ys + y_ind) = f ((x#xs) ! 0) (ys ! y_ind)"
proof -
  assume "y_ind < size ys"
  have "[f x y. x \<leftarrow> (x#xs), y \<leftarrow> ys] ! (y_ind) = f x (ys ! y_ind)"
    by (smt (verit) \<open>y_ind < length ys\<close> concat.simps(2) index_prop2 length_map list.simps(9) nth_map)
  show "[f x y. x \<leftarrow> (x#xs), y \<leftarrow> ys] ! (0 * size ys + y_ind) = f ((x#xs) ! 0) (ys ! y_ind)"
    using \<open>concat (map (\<lambda>x. map (f x) ys) (x # xs)) ! y_ind = f x (ys ! y_ind)\<close> by auto
qed

lemma list_comp_index_3: \<comment> \<open>y_ind = 0\<close>
  "x_ind < size xs \<Longrightarrow> 
   [f x y. x \<leftarrow> xs, y \<leftarrow> (y#ys)] ! (x_ind * size (y#ys) + 0) = f (xs ! x_ind) ((y#ys) ! 0)"
proof -
  assume "x_ind < size xs"
  then have "[f x y. x \<leftarrow> xs, y \<leftarrow> (y#ys)] ! (x_ind * size (y#ys)) = f (xs ! x_ind) y"
  proof (induction xs rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc x xs)
    have "concat (map (\<lambda>x. map (f x) (y # ys)) (xs @ [x])) = concat (map (\<lambda>x. map (f x) (y # ys)) (xs)) @ concat (map (\<lambda>x. map (f x) (y # ys)) ([x]))" by auto
    have "size (concat (map (\<lambda>x. map (f x) (y # ys)) (xs))) = size xs * size (y#ys)" apply auto apply (induction xs) by auto
    have "length xs * length (y # ys) = length xs * length ys + length xs"
      by auto
    then show "concat (map (\<lambda>x. map (f x) (y # ys)) (xs @ [x])) ! (x_ind * length (y # ys)) = f ((xs @ [x]) ! x_ind) y"
    proof (cases "x_ind = size xs")
      case True
      have "(concat (map (\<lambda>x. map (f x) (y # ys)) xs) @ concat (map (\<lambda>x. map (f x) (y # ys)) [x])) ! (length xs * length (y # ys)) =
            (concat (map (\<lambda>x. map (f x) (y # ys)) xs) @ concat (map (\<lambda>x. map (f x) (y # ys)) [x])) ! (length xs * length (ys) + length xs)"
        using \<open>length xs * length (y # ys) = length xs * length ys + length xs\<close> by presburger
      then show ?thesis
        by (smt (verit) True \<open>concat (map (\<lambda>x. map (f x) (y # ys)) (xs @ [x])) = concat (map (\<lambda>x. map (f x) (y # ys)) xs) @ concat (map (\<lambda>x. map (f x) (y # ys)) [x])\<close> \<open>length (concat (map (\<lambda>x. map (f x) (y # ys)) xs)) = length xs * length (y # ys)\<close> concat.simps(1) concat.simps(2) list.simps(8) list.simps(9) nth_append_length self_append_conv)
    next
      case False
      have "x_ind < length xs" using False snoc(2) by auto
      then have "(x_ind * length (y # ys)) < (length xs * length (y # ys))" apply auto
        by (simp add: add_less_le_mono)
      then have "(x_ind * length (y # ys)) \<le> size (concat (map (\<lambda>x. map (f x) (y # ys)) (xs)))" apply auto
        using \<open>length (concat (map (\<lambda>x. map (f x) (y # ys)) xs)) = length xs * length (y # ys)\<close> by fastforce
      have "(concat (map (\<lambda>x. map (f x) (y # ys)) (xs)) @ concat (map (\<lambda>x. map (f x) (y # ys)) ([x]))) ! (x_ind * length (y # ys)) = concat (map (\<lambda>x. map (f x) (y # ys)) xs) ! (x_ind * length (y # ys))"
        by (metis \<open>length (concat (map (\<lambda>x. map (f x) (y # ys)) xs)) = length xs * length (y # ys)\<close> \<open>x_ind * length (y # ys) < length xs * length (y # ys)\<close> index_prop2)
      then show "concat (map (\<lambda>x. map (f x) (y # ys)) (xs @ [x])) ! (x_ind * length (y # ys)) = f ((xs @ [x]) ! x_ind) y"
        using \<open>x_ind < length xs\<close> index_prop2 snoc.IH by fastforce
    qed
  qed
  then show "[f x y. x \<leftarrow> xs, y \<leftarrow> (y#ys)] ! (x_ind * size (y#ys) + 0) = f (xs ! x_ind) ((y#ys) ! 0)"
    by auto
qed

theorem list_comp_index_4: \<comment> \<open>y_ind = size ys\<close>
  "x_ind < size xs \<Longrightarrow> 
   [f x y. x \<leftarrow> xs, y \<leftarrow> (ys@[y])] ! (x_ind * size (ys@[y]) + (size ys)) = f (xs ! x_ind) ((ys@[y]) ! (size ys))"
proof -
  assume a1: "x_ind < size xs"
  obtain x xss where "xs=x#xss"
    by (metis \<open>x_ind < length xs\<close> length_0_conv less_nat_zero_code neq_Nil_conv)
  obtain x' xss' where "xs=xss'@[x']"
    by (metis \<open>xs = x # xss\<close> append_butlast_last_id list.discI)
  have "[f x y. x \<leftarrow> xs, y \<leftarrow> (ys@[y])] ! (x_ind * size (ys@[y]) + (size ys)) = f (xs ! x_ind) y"
    using a1 proof (induction xs rule: rev_induct)
    case Nil
    then show ?case
      by simp
  next
    case (snoc x xs)
    have dec: "concat (map (\<lambda>x. map (f x) (ys @ [y])) (xs @ [x])) = concat (map (\<lambda>x. map (f x) (ys @ [y])) (xs)) @ concat (map (\<lambda>x. map (f x) (ys @ [y])) ([x]))" by auto
    show ?case
    proof (cases "x_ind = length xs")
      case True
      have "size (concat (map (\<lambda>x. map (f x) (ys @ [y])) (xs))) = size xs * size (ys@[y])" apply (induction xs) by auto
      have "(concat (map (\<lambda>x. map (f x) (ys @ [y])) ([x]))) ! (length ys) = f x y" using append_eq_append_conv2 concat.simps(2) concat_eq_append_conv length_map list.simps(8) list.simps(9) map_append nth_append_length
        apply auto
        by (metis (no_types) length_map nth_append_length)
      then have "(concat (map (\<lambda>x. map (f x) (ys @ [y])) (xs)) @ concat (map (\<lambda>x. map (f x) (ys @ [y])) ([x]))) ! (size xs * length (ys @ [y]) + length ys) = f x y"
        by (metis \<open>length (concat (map (\<lambda>x. map (f x) (ys @ [y])) xs)) = length xs * length (ys @ [y])\<close> index_prop)
      then have "concat (map (\<lambda>x. map (f x) (ys @ [y])) (xs @ [x])) ! (size xs * length (ys @ [y]) + length ys) = f x y" using dec by auto
      then have "concat (map (\<lambda>x. map (f x) (ys @ [y])) (xs @ [x])) ! (size xs * length (ys @ [y]) + length ys) = f ((xs @ [x]) ! size xs) y" by auto
      then show "concat (map (\<lambda>x. map (f x) (ys @ [y])) (xs @ [x])) ! (x_ind * length (ys @ [y]) + length ys) = f ((xs @ [x]) ! x_ind) y" using True by simp
    next
      case False
      have "x_ind < length xs"
        using False snoc.prems by auto
      have "0 < length xs"
        using \<open>x_ind < length xs\<close> by auto
      have "(xs @ [x]) ! x_ind = xs ! x_ind"
        using \<open>x_ind < length xs\<close> index_prop2 by fastforce
      have l1: "size (concat (map (\<lambda>x. map (f x) (ys @ [y])) xs)) = (length xs) * length (ys @ [y])" apply auto apply (induction xs) by auto
      have "(x_ind * length (ys @ [y]) + length ys) \<le> ((length xs - 1) * length (ys @ [y]) + length ys)"
        by (meson \<open>x_ind < length xs\<close> add_le_imp_le_diff le_add2 less_iff_succ_less_eq nat_le_add_iff2)
      have "... = (length xs - 1) * length (ys @ [y]) + length (ys @ [y]) - 1" by auto
      have "... = ((length xs) * length (ys @ [y])) - 1" apply auto using \<open>0 < length xs\<close> apply (induction xs) by auto
      have "... < (length xs) * length (ys @ [y])" apply auto
        using \<open>0 < length xs\<close> by auto
      have "(x_ind * length (ys @ [y]) + length ys) < (length xs) * length (ys @ [y])"
        using \<open>(length xs - 1) * length (ys @ [y]) + length (ys @ [y]) - 1 = length xs * length (ys @ [y]) - 1\<close> \<open>(length xs - 1) * length (ys @ [y]) + length ys = (length xs - 1) * length (ys @ [y]) + length (ys @ [y]) - 1\<close> \<open>length xs * length (ys @ [y]) - 1 < length xs * length (ys @ [y])\<close> \<open>x_ind * length (ys @ [y]) + length ys \<le> (length xs - 1) * length (ys @ [y]) + length ys\<close> add_lessD1 ordered_cancel_comm_monoid_diff_class.add_diff_inverse by linarith
      then have "(concat (map (\<lambda>x. map (f x) (ys @ [y])) xs) @ concat (map (\<lambda>x. map (f x) (ys @ [y])) [x])) ! (x_ind * length (ys @ [y]) + length ys) = 
                 (concat (map (\<lambda>x. map (f x) (ys @ [y])) xs)) ! (x_ind * length (ys @ [y]) + length ys)" using l1 apply auto
        by (metis (no_types, lifting) index_prop2)
      have "(concat (map (\<lambda>x. map (f x) (ys @ [y])) xs) @ concat (map (\<lambda>x. map (f x) (ys @ [y])) [x])) ! (x_ind * length (ys @ [y]) + length ys) = f ((xs @ [x]) ! x_ind) y"
        using \<open>(concat (map (\<lambda>x. map (f x) (ys @ [y])) xs) @ concat (map (\<lambda>x. map (f x) (ys @ [y])) [x])) ! (x_ind * length (ys @ [y]) + length ys) = concat (map (\<lambda>x. map (f x) (ys @ [y])) xs) ! (x_ind * length (ys @ [y]) + length ys)\<close> \<open>(xs @ [x]) ! x_ind = xs ! x_ind\<close> \<open>x_ind < length xs\<close> snoc.IH by auto
      then show "concat (map (\<lambda>x. map (f x) (ys @ [y])) (xs @ [x])) ! (x_ind * length (ys @ [y]) + length ys) = f ((xs @ [x]) ! x_ind) y" by auto
    qed
  qed
  then show ?thesis
    by simp
qed

theorem list_comp_index:
  "x_ind < size xs \<Longrightarrow> y_ind < size ys \<Longrightarrow> 
   [f x y. x \<leftarrow> xs, y \<leftarrow> ys] ! (x_ind * size ys + y_ind) = f (xs ! x_ind) (ys ! y_ind)"
proof -
  assume m_bound: "x_ind < size xs"
  assume n_bound: "y_ind < size ys"

  from m_bound n_bound show "concat (map (\<lambda>x. map (f x) ys) xs) ! (x_ind * length ys + y_ind) = f (xs ! x_ind) (ys ! y_ind)"
  proof (induction xs rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc x xs)
    have "concat (map (\<lambda>x. map (f x) ys) (xs @ [x])) = concat (map (\<lambda>x. map (f x) ys) xs) @ concat (map (\<lambda>x. map (f x) ys) [x])" by auto
    then show "concat (map (\<lambda>x. map (f x) ys) (xs @ [x])) ! (x_ind * length ys + y_ind) = f ((xs @ [x]) ! x_ind) (ys ! y_ind)"
    proof (cases "x_ind = size xs")
      case True
      have "concat (map (\<lambda>x. map (f x) ys) (xs @ [x])) ! (length xs * length ys + y_ind) = f ((xs @ [x]) ! length xs) (ys ! y_ind)" using list_comp_index_1 snoc(3) apply simp
        by (simp add: index_prop t2)
      then show "concat (map (\<lambda>x. map (f x) ys) (xs @ [x])) ! (x_ind * length ys + y_ind) = f ((xs @ [x]) ! x_ind) (ys ! y_ind)"
        by (simp add: True)
    next
      case False
      have l1: "x_ind < size xs" using False snoc(2) by auto
      then have l2: "0 < size xs" by auto
      have "concat (map (\<lambda>x. map (f x) ys) (xs @ [x])) = concat (map (\<lambda>x. map (f x) ys) xs) @ concat (map (\<lambda>x. map (f x) ys) [x])" by simp
      have "(x_ind * length ys + y_ind) < size (concat (map (\<lambda>x. map (f x) ys) xs))"
      proof -
        have "size (concat (map (\<lambda>x. map (f x) ys) xs)) = size xs * size ys" using l2 apply (induction xs) apply auto by (simp add: t2)
        have "(x_ind * length ys + y_ind) \<le> ((size xs - 1) * length ys + (size ys -1))"
          by (metis add_leD2 add_mono less_iff_succ_less_eq local.l1 mult.commute mult_le_mono2 n_bound ordered_cancel_comm_monoid_diff_class.le_diff_conv2)
        have "... < size xs * size ys"
          using add.commute add_less_cancel_right diff_less less_nat_zero_code less_numeral_extra(1) local.l2 mult_eq_if n_bound nat_neq_iff by auto
        show ?thesis
          using \<open>(length xs - 1) * length ys + (length ys - 1) < length xs * length ys\<close> \<open>length (concat (map (\<lambda>x. map (f x) ys) xs)) = length xs * length ys\<close> \<open>x_ind * length ys + y_ind \<le> (length xs - 1) * length ys + (length ys - 1)\<close> order.strict_trans1 by linarith
      qed
      have "(concat (map (\<lambda>x. map (f x) ys) xs) @ concat (map (\<lambda>x. map (f x) ys) [x])) ! (x_ind * length ys + y_ind) = (concat (map (\<lambda>x. map (f x) ys) xs)) ! (x_ind * length ys + y_ind)"
        using \<open>x_ind * length ys + y_ind < length (concat (map (\<lambda>x. map (f x) ys) xs))\<close> index_prop2 by fastforce
      then show "concat (map (\<lambda>x. map (f x) ys) (xs @ [x])) ! (x_ind * length ys + y_ind) = f ((xs @ [x]) ! x_ind) (ys ! y_ind)"
        using \<open>x_ind < length xs\<close> index_prop2 n_bound snoc.IH by fastforce
    qed
  qed
qed

theorem interleave_ind_comp: "x_ind<size xs \<Longrightarrow> y_ind<size ys \<Longrightarrow> [path_m \<interleave> path_n. path_m \<leftarrow> xs, path_n \<leftarrow> ys] ! ((x_ind* (size ys))+y_ind) = (xs ! x_ind) \<interleave> (ys ! y_ind)"
  by (simp add: list_comp_index)

theorem "x_ind < size xs \<Longrightarrow> y_ind < size ys \<Longrightarrow> [path_m \<interleave> path_n. path_m \<leftarrow> xs, path_n \<leftarrow> ys] ! ((x_ind* (size ys))+y_ind) = [path_m \<interleave> path_n. path_m \<leftarrow> ys, path_n \<leftarrow> xs] ! ((y_ind* (size xs))+x_ind)"
  oops

theorem all_elements_have_permutation: "x_ind < size xs \<Longrightarrow> y_ind < size ys \<Longrightarrow> [path_m \<interleave> path_n. path_m \<leftarrow> xs, path_n \<leftarrow> ys] ! ((x_ind* (size ys))+y_ind) \<in> set (permutations ([path_m \<interleave> path_n. path_m \<leftarrow> ys, path_n \<leftarrow> xs] ! ((y_ind* (size xs))+x_ind)))"
proof -
  fix x_ind y_ind
  assume "x_ind<size xs"
  assume "y_ind<size ys"
  have "[path_m \<interleave> path_n. path_m \<leftarrow> xs, path_n \<leftarrow> ys] ! ((x_ind* (size ys))+y_ind) = (xs ! x_ind) \<interleave> (ys ! y_ind)"
    by (simp add: \<open>x_ind < length xs\<close> \<open>y_ind < length ys\<close> interleave_ind_comp)
  have "[path_m \<interleave> path_n. path_m \<leftarrow> ys, path_n \<leftarrow> xs] ! ((y_ind* (size xs))+x_ind) = (ys ! y_ind) \<interleave> (xs ! x_ind)"
    by (simp add: \<open>x_ind < length xs\<close> \<open>y_ind < length ys\<close> interleave_ind_comp)
  show "[path_m \<interleave> path_n. path_m \<leftarrow> xs, path_n \<leftarrow> ys] ! ((x_ind* (size ys))+y_ind) \<in> set (permutations ([path_m \<interleave> path_n. path_m \<leftarrow> ys, path_n \<leftarrow> xs] ! ((y_ind* (size xs))+x_ind)))"
    by (simp add: \<open>concat (map (\<lambda>path_m. map ((\<interleave>) path_m) xs) ys) ! (y_ind * length xs + x_ind) = (ys ! y_ind) \<interleave> (xs ! x_ind)\<close> \<open>concat (map (\<lambda>path_m. map ((\<interleave>) path_m) ys) xs) ! (x_ind * length ys + y_ind) = (xs ! x_ind) \<interleave> (ys ! y_ind)\<close> inter_perm)
qed

theorem perm_prop: "xs \<in> set (permutations xs') \<Longrightarrow> ys  \<in> set (permutations ys') \<Longrightarrow> xs@ys \<in> set (permutations (xs'@ys'))"
proof (induction xs arbitrary: xs')
  case Nil
  then show ?case
    by (metis append_self_conv2 in_set_member last_in_set member_rec(2) permutation_set_equality)
next
  case (Cons x xs)
  obtain x_s x_e where "x_s@x#x_e=xs'"
    by (metis Cons.prems(1) perm_inv_3 permutation_split_set)
  have "x#xs \<in> set (permutations (x_s@x#x_e))"
    by (simp add: Cons.prems(1) \<open>x_s @ x # x_e = xs'\<close>)
  have "xs \<in> set (permutations (x_s@x_e))"
    by (meson \<open>x # xs \<in> set (permutations (x_s @ x # x_e))\<close> perm_split)
  have "(xs) @ ys \<in> set (permutations ((x_s@x_e) @ ys'))"
    using Cons.IH Cons.prems(2) \<open>xs \<in> set (permutations (x_s @ x_e))\<close> by blast
  have "(x # xs) @ ys \<in> set (permutations ((x#x_s@x_e) @ ys'))"
    by (metis \<open>xs @ ys \<in> set (permutations ((x_s @ x_e) @ ys'))\<close> append_Cons perm_1)
  then show "(x # xs) @ ys \<in> set (permutations (xs' @ ys'))"
    by (metis Cons_eq_appendI \<open>x_s @ x # x_e = xs'\<close> append_Nil append_assoc perm_3)
qed

theorem is_perm: "size xy = sx * sy \<Longrightarrow> [xy ! ((x_ind*sy)+y_ind). x_ind \<leftarrow> [0..<sx], y_ind \<leftarrow> [0..<sy]] \<in> set (permutations xy)"
proof (induction sx arbitrary: xy)
  case 0
  then show ?case by auto
next
  case (Suc sx)
  have l0: "concat (map (\<lambda>x_ind. map (\<lambda>y_ind. xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<Suc sx]) = 
        concat (map (\<lambda>x_ind. map (\<lambda>y_ind. xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<sx]) @ concat (map (\<lambda>x_ind. map (\<lambda>y_ind. xy ! (x_ind * sy + y_ind)) [0..<sy]) [sx..<Suc sx])" by simp
  obtain old_xy where o1: "old_xy = take (sx*sy) xy" by simp
  obtain new_xy where o2: "new_xy = drop (sx*sy) xy" by simp
  obtain xs where o3: "xs = [0..<sx]" by simp
  obtain ys where o4: "ys = [0..<sy]" by simp
  have l1: "xy = old_xy @ new_xy"
    by (simp add: \<open>new_xy = drop (sx * sy) xy\<close> \<open>old_xy = take (sx * sy) xy\<close>)
  have l2: "size (old_xy) = sx * sy"
    by (simp add: Suc.prems \<open>old_xy = take (sx * sy) xy\<close>)
  have l3: "size (new_xy) = sy"
    by (simp add: Suc.prems \<open>new_xy = drop (sx * sy) xy\<close>)
  have l4: "size (concat (map (\<lambda>x_ind. map (\<lambda>y_ind. xy ! (x_ind * sy + y_ind)) ys) xs)) = size xs * size ys" using t2 by fastforce
  then have "size (concat (map (\<lambda>x_ind. map (\<lambda>y_ind. xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<sx])) = sx * sy"
    by (simp add: o3 o4)
  have l5: "size (concat (map (\<lambda>x_ind. map (\<lambda>y_ind. xy ! (x_ind * sy + y_ind)) [0..<sy]) [sx..<Suc sx])) = sy"
    by (metis (no_types, lifting) Ex_list_of_length append.right_neutral concat.simps(2) length_map lessI less_irrefl_nat list.simps(9) map_is_Nil_conv map_nth mult_is_0 t2 upt_0 upt_rec)
  have f1: "concat (map (\<lambda>x_ind. map (\<lambda>y_ind. old_xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<sx]) \<in> set (permutations (old_xy))" using l1 Suc(1)
    by (simp add: local.l2)
  have l6: "concat (map (\<lambda>x_ind. map (\<lambda>y_ind. xy ! (x_ind * sy + y_ind)) [0..<sy]) [sx..<Suc sx]) = concat (map (\<lambda>x_ind. map (\<lambda>y_ind. new_xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<1])" using o2 l1 l2 l3 l4 apply auto
    using index_prop by auto
  have "... = new_xy" apply auto
    using local.l3 map_nth by auto
  have f2: "concat (map (\<lambda>x_ind. map (\<lambda>y_ind. xy ! (x_ind * sy + y_ind)) [0..<sy]) [sx..<Suc sx]) \<in> set (permutations (new_xy))" using l1 Suc(1)
    by (metis \<open>concat (map (\<lambda>x_ind. map (\<lambda>y_ind. new_xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<1]) = new_xy\<close> \<open>concat (map (\<lambda>x_ind. map (\<lambda>y_ind. xy ! (x_ind * sy + y_ind)) [0..<sy]) [sx..<Suc sx]) = concat (map (\<lambda>x_ind. map (\<lambda>y_ind. new_xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<1])\<close> in_set_member permutation_reflexive)
  have "(concat (map (\<lambda>x_ind. map (\<lambda>y_ind. old_xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<sx])@concat (map (\<lambda>x_ind. map (\<lambda>y_ind. new_xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<1])) \<in> set (permutations (old_xy@new_xy))" using f1 f2 perm_prop
    by (metis \<open>concat (map (\<lambda>x_ind. map (\<lambda>y_ind. xy ! (x_ind * sy + y_ind)) [0..<sy]) [sx..<Suc sx]) = concat (map (\<lambda>x_ind. map (\<lambda>y_ind. new_xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<1])\<close>)
  then have "concat (map (\<lambda>x_ind. map (\<lambda>y_ind. old_xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<sx]) =
             concat (map (\<lambda>x_ind. map (\<lambda>y_ind.     xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<sx])"
    apply (cases "sx=0") apply auto apply (cases "sy=0") apply auto
  proof -
    assume "0 < sx"
    assume "0 < sy"
    have "\<forall>x_ind < sx. \<forall>y_ind < sy. (x_ind * sy + y_ind) \<le> (sx-1)*sy+(sy-1)"
      by (metis add_le_imp_le_diff add_le_mono less_iff_succ_less_eq mult.commute mult_le_mono2)
    moreover have "(sx-1)*sy+(sy-1) < sx*sy" by (simp add: \<open>0 < sx\<close> \<open>0 < sy\<close> mult_eq_if)
    ultimately have "\<forall>x_ind < sx. \<forall>y_ind < sy. (x_ind * sy + y_ind) < sx*sy"
      by (smt (verit) add_diff_cancel_left' add_increasing2 canonically_ordered_monoid_add_class.lessE le_antisym nat_less_le zero_less_diff)
    then have "\<forall>x_ind < sx. \<forall>y_ind < sy. old_xy ! (x_ind * sy + y_ind) = xy ! (x_ind * sy + y_ind)" by (simp add: o1)
    then have "\<forall>x_ind < sx. map (\<lambda>y_ind. old_xy ! (x_ind * sy + y_ind)) [0..<sy] = map (\<lambda>y_ind. xy ! (x_ind * sy + y_ind)) [0..<sy]" by auto
    then have "map (\<lambda>x_ind. map (\<lambda>y_ind. old_xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<sx] = map (\<lambda>x_ind. map (\<lambda>y_ind. xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<sx]" by auto
    then show ?thesis
      by presburger
  qed
  then have "(concat (map (\<lambda>x_ind. map (\<lambda>y_ind. old_xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<sx])@concat (map (\<lambda>x_ind. map (\<lambda>y_ind. new_xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<1])) =
        concat (map (\<lambda>x_ind. map (\<lambda>y_ind. xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<Suc sx])" using l1 o1 o2 l2 l3 l6
    by fastforce
  then show "concat (map (\<lambda>x_ind. map (\<lambda>y_ind. xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<Suc sx]) \<in> set (permutations xy)"
    using \<open>concat (map (\<lambda>x_ind. map (\<lambda>y_ind. old_xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<sx]) @ concat (map (\<lambda>x_ind. map (\<lambda>y_ind. new_xy ! (x_ind * sy + y_ind)) [0..<sy]) [0..<1]) \<in> set (permutations (old_xy @ new_xy))\<close> local.l1 by argo
qed

theorem is_perm2: "size xy = size xs * size ys \<Longrightarrow> [xy ! ((x_ind*(size ys))+y_ind). x_ind \<leftarrow> [0..<size xs], y_ind \<leftarrow> [0..<size ys]] \<in> set (permutations xy)"
  by (simp add: is_perm)
                 (*size xy = sx * sy \<Longrightarrow> [xy ! ((x_ind*sy)+y_ind). x_ind \<leftarrow> [0..<sx], y_ind \<leftarrow> [0..<sy]] \<in> set (permutations xy)*)


value "1 div 2::nat"
value "[(x, y). x \<leftarrow> [a,b], y \<leftarrow> [c,d,e]]"
value "[a,b] ! (5 div (size [c,d,e]))"
value "[c,d,e] ! (3 mod (size [c,d,e]))"

theorem index_prop4: "i < size xs * size ys \<Longrightarrow> concat (map (\<lambda>x. map (f x) ys) xs) ! i = f (xs ! (i div length ys)) (ys ! (i mod length ys))"
proof (induction xs arbitrary: i rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  have "concat (map (\<lambda>x. map (f x) ys) (xs@[x])) = concat (map (\<lambda>x. map (f x) ys) xs) @ concat (map (\<lambda>x. map (f x) ys) [x])" by auto
  have "size (concat (map (\<lambda>x. map (f x) ys) xs)) = size xs * size ys" using t2 by auto
  then show "concat (map (\<lambda>x. map (f x) ys) (xs @ [x])) ! i = f ((xs @ [x]) ! (i div length ys)) (ys ! (i mod length ys))"
  proof (cases "i < length xs * length ys")
    case True
    have "concat (map (\<lambda>x. map (f x) ys) (xs @ [x])) ! i = concat (map (\<lambda>x. map (f x) ys) xs) ! i" using \<open>size (concat (map (\<lambda>x. map (f x) ys) xs)) = size xs * size ys\<close>
      by (metis True \<open>concat (map (\<lambda>x. map (f x) ys) (xs @ [x])) = concat (map (\<lambda>x. map (f x) ys) xs) @ concat (map (\<lambda>x. map (f x) ys) [x])\<close> index_prop2)
    have "... = f (xs ! (i div length ys)) (ys ! (i mod length ys))"
      using True snoc.IH by blast
    have "... = f ((xs@[x]) ! (i div length ys)) (ys ! (i mod length ys))"
      by (metis True index_prop2 less_mult_imp_div_less)
    then show ?thesis
      using \<open>concat (map (\<lambda>x. map (f x) ys) (xs @ [x])) ! i = concat (map (\<lambda>x. map (f x) ys) xs) ! i\<close> \<open>concat (map (\<lambda>x. map (f x) ys) xs) ! i = f (xs ! (i div length ys)) (ys ! (i mod length ys))\<close> by argo
  next
    case False
    obtain j where o1: "j = (i-(size xs * size ys))" by simp
    have "j < size ys" using o1 False snoc(2) by auto
    have "concat (map (\<lambda>x. map (f x) ys) (xs @ [x])) ! i = concat (map (\<lambda>x. map (f x) ys) [x]) ! j"
      by (simp add: o1 False \<open>length (concat (map (\<lambda>x. map (f x) ys) xs)) = length xs * length ys\<close> nth_append)
    have "... = f x (ys ! j)"
      using \<open>j < length ys\<close> by force
    have "i div length ys = size xs" using False snoc(2) apply auto
      by (metis \<open>j < length ys\<close> add.commute add_cancel_right_left add_diff_inverse_nat div_less div_mult_self4 mult.commute o1)
    have "(xs @ [x]) ! (i div length ys) = x"
      by (simp add: \<open>i div length ys = length xs\<close>)
    have "(ys ! j) = ys ! (i mod length ys)" using o1
      by (simp add: \<open>i div length ys = length xs\<close> modulo_nat_def)
    have "f x (ys ! j) = f ((xs @ [x]) ! (i div length ys)) (ys ! (i mod length ys))"
      by (simp add: \<open>(xs @ [x]) ! (i div length ys) = x\<close> \<open>ys ! j = ys ! (i mod length ys)\<close>)
    then show ?thesis
      using \<open>concat (map (\<lambda>x. map (f x) ys) (xs @ [x])) ! i = concat (map (\<lambda>x. map (f x) ys) [x]) ! j\<close> \<open>concat (map (\<lambda>x. map (f x) ys) [x]) ! j = f x (ys ! j)\<close> by presburger
  qed
qed

theorem index_prop5: "concat (map (\<lambda>x. map (f x) ys) xs) = [f (xs ! (i div length ys)) (ys ! (i mod length ys)). i \<leftarrow> [0..<size xs * size ys]]"
proof -
  have "size (concat (map (\<lambda>x. map (f x) ys) xs)) = size xs * size ys" by (simp add: t2)
  have "size [f (xs ! (i div length ys)) (ys ! (i mod length ys)). i \<leftarrow> [0..<size xs * size ys]] = size xs * size ys" by auto
  have "\<forall>j < size xs * size ys. concat (map (\<lambda>x. map (f x) ys) xs) ! j = [f (xs ! (i div length ys)) (ys ! (i mod length ys)). i \<leftarrow> [0..<size xs * size ys]] ! j" apply auto using index_prop4 by auto
  then show "concat (map (\<lambda>x. map (f x) ys) xs) = [f (xs ! (i div length ys)) (ys ! (i mod length ys)). i \<leftarrow> [0..<size xs * size ys]]" apply auto
    by (metis (mono_tags, lifting) \<open>\<forall>j<length xs * length ys. concat (map (\<lambda>x. map (f x) ys) xs) ! j = map (\<lambda>i. f (xs ! (i div length ys)) (ys ! (i mod length ys))) [0..<length xs * length ys] ! j\<close> \<open>length (concat (map (\<lambda>x. map (f x) ys) xs)) = length xs * length ys\<close> \<open>length (map (\<lambda>i. f (xs ! (i div length ys)) (ys ! (i mod length ys))) [0..<length xs * length ys]) = length xs * length ys\<close> nth_equalityI)
qed

(*
definition xs :: "nat list"  where "xs \<equiv> [1,2,3]"
definition ys :: "nat list"  where "ys \<equiv> [4,5]"
definition xy :: "(nat \<times> nat) list" where "xy = [(path_m, path_n). path_m \<leftarrow> xs, path_n \<leftarrow> ys]"
definition yx :: "(nat \<times> nat) list" where "yx = [(path_m, path_n). path_m \<leftarrow> ys, path_n \<leftarrow> xs]"
value "xy"

value "yx"
value "[xy ! ((x_ind* (size ys))+y_ind). x_ind \<leftarrow> [0..<size xs], y_ind \<leftarrow> [0..<size ys]]"

value "yx"
value "[xy ! ((x_ind* (size ys))+y_ind). y_ind \<leftarrow> [0..<size ys], x_ind \<leftarrow> [0..<size xs]]"
*)

theorem perm_prop2: "[] \<in> set (permutations xy) \<Longrightarrow> xy = []"
  apply (induction xy) apply auto
  by (metis append_is_Nil_conv l11 split_list_first)

theorem perm_prop5: "concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) (ys)) @ concat (map (\<lambda>y. map (\<lambda>x. f x y) xs) (ys)) \<in> set (permutations (concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) (ys))))"
proof (induction "size ys" arbitrary: ys rule: "less_induct")
  case less
  then show ?case 
proof (cases "ys")
  case Nil
  then show ?thesis by auto
next
  case (Cons y yss)
  show ?thesis
  proof (cases "yss = []")
    case True
    have "ys = [y]"
      by (simp add: True local.Cons)
    have "concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) [y]) @ concat (map (\<lambda>y. map (\<lambda>x. f x y) xs) [y]) \<in> set (permutations (concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) [y])))" apply auto
      by (meson insert_perm_rel l2 perm_lemma_1)
    then show ?thesis
      using True local.Cons by blast
  next
    case False
    have "size yss < size ys"
      by (simp add: local.Cons)
    have "size [y] < size ys"
      by (simp add: False local.Cons)
  have "concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) (y # yss)) = concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) [y]) @ concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) yss)" by simp
  have "concat (map (\<lambda>y. map (\<lambda>x. f x y) xs) (y # yss)) = concat (map (\<lambda>y. map (\<lambda>x. f x y) xs) [y]) @ concat (map (\<lambda>y. map (\<lambda>x. f x y) xs) yss)" by simp
  have "concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) (y # yss)) = concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) [y]) @ concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) yss)" by simp

  obtain a where "a = concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) [y])" by simp
  obtain b where "b = concat (map (\<lambda>y. map (\<lambda>x. f x y) xs) [y])" by simp
  obtain c where "c = concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) yss)" by simp
  obtain d where "d = concat (map (\<lambda>y. map (\<lambda>x. f x y) xs) yss)" by simp
  obtain g where "g = concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) [y])" by simp
  obtain h where "h = concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) yss)" by simp

  have "g@h = concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) (y # yss))"
    by (simp add: \<open>g = concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) [y])\<close> \<open>h = concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) yss)\<close>)
  have "a @ c @ b @ d \<in> set (permutations (a @ b @ c @ d))" apply (induction a) apply auto apply (induction c)
    apply (simp add: in_set_member permutation_reflexive)
    apply (metis Cons_eq_appendI perm_inv_2 perm_inv_3)
    by (metis l2)
  have "a @ b \<in> set (permutations (g))"
    using \<open>length [y] < length ys\<close> less
    using \<open>a = concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) [y])\<close> \<open>b = concat (map (\<lambda>y. map (\<lambda>x. f x y) xs) [y])\<close>
    using \<open>g = concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) [y])\<close> by blast
  moreover have "c @ d \<in> set (permutations (h))"
    using \<open>length yss < length ys\<close> less
    using \<open>c = concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) yss)\<close> \<open>d = concat (map (\<lambda>y. map (\<lambda>x. f x y) xs) yss)\<close>
    using \<open>h = concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) yss)\<close> by auto
  ultimately have "a @ c @ b @ d \<in> set (permutations (g@h))"
    by (metis \<open>a @ c @ b @ d \<in> set (permutations (a @ b @ c @ d))\<close> append.assoc perm_inv_3 perm_prop permutations_set_equality)
  then have "concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) [y]) @ concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) yss) @ concat (map (\<lambda>y. map (\<lambda>x. f x y) xs) [y]) @ concat (map (\<lambda>y. map (\<lambda>x. f x y) xs) yss) \<in> 
        set (permutations (concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) (y # yss))))"
    using \<open>a = concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) [y])\<close> \<open>b = concat (map (\<lambda>y. map (\<lambda>x. f x y) xs) [y])\<close> \<open>c = concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) yss)\<close> \<open>d = concat (map (\<lambda>y. map (\<lambda>x. f x y) xs) yss)\<close>
    using \<open>concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) (y # yss)) = concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) [y]) @ concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) yss)\<close> \<open>g = concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) [y])\<close> \<open>h = concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) yss)\<close> by argo
  then show "concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) ys) @ concat (map (\<lambda>y. map (\<lambda>x. f x y) xs) ys) \<in> set (permutations (concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xs)) ys)))" using Cons by simp
qed
qed
qed

theorem perm_prop1: "[f x y. x \<leftarrow> xs, y \<leftarrow> ys] \<in> set (permutations xy) \<Longrightarrow> [f x y. y \<leftarrow> ys, x \<leftarrow> xs] \<in> set (permutations xy)"
proof (induction "size xs" arbitrary: xy xs rule: "less_induct")
  case less1: less
  then show ?case
  proof (cases "xs = []")
    case x_0: True
    then show ?thesis apply auto
      by (smt (verit) Nil_eq_concat_conv in_set_conv_nth length_map less1.prems list.map_disc_iff nth_map)
  next
    case suc_x: False
    obtain x xss where "xs=x#xss"
      by (metis neq_Nil_conv suc_x)
    have "length xss < length xs"
      by (simp add: \<open>xs = x # xss\<close>)
    show ?thesis
    proof (cases "size xss")
      case 0
      have "concat (map (\<lambda>x. map (\<lambda>y. f x y) ys) [x]) \<in> set (permutations xy)"
        using "0" \<open>xs = x # xss\<close> less1.prems by auto
      have "concat (map (\<lambda>x. map (\<lambda>y. f x y) ys) [x]) = map (\<lambda>y. f x y) ys" by auto
      have "concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) ys) = map (\<lambda>y. f x y) ys" by auto
      have "map (\<lambda>y. f x y) ys \<in> set (permutations xy)"
        using \<open>concat (map (\<lambda>x. map (f x) ys) [x]) \<in> set (permutations xy)\<close> by auto
      then show ?thesis
        using "0" \<open>xs = x # xss\<close> by auto
    next
      case (Suc nat)
      have "size [x] < size xs"
        by (simp add: Suc \<open>xs = x # xss\<close>)
    have "concat (map (\<lambda>y. map (\<lambda>x. f x y) (x#xss)) ys) \<in> set (permutations xy)"
    using suc_x less1 proof (induction "size ys" arbitrary: ys rule: "less_induct")
    case less
    from less show ?case
    proof (cases "ys = []")
      case True
      then show "concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xss)) ys) \<in> set (permutations xy)" using less
        by (smt (z3) concat_eq_Nil_conv in_set_conv_nth length_map list.simps(8) nth_map)
    next
      case False
      obtain y yss where "ys=y#yss"
        by (metis False neq_Nil_conv)
      have "size [f x y. x \<leftarrow> xs, y \<leftarrow> ys] = size xs * size ys"
        by (simp add: t2)
      have "size [f x y. x \<leftarrow> xs, y \<leftarrow> ys] = size xy"
        by (simp add: length_inv less.prems(3))
      have "size xs * size ys = size xy"
        using \<open>length (concat (map (\<lambda>x. map (f x) ys) xs)) = length xs * length ys\<close> \<open>length (concat (map (\<lambda>x. map (f x) ys) xs)) = length xy\<close> by auto
      have "concat (map (\<lambda>x. map (\<lambda>y. f x y) (y#yss)) (x#xss)) \<in> set (permutations xy)"
        using \<open>xs = x # xss\<close> \<open>ys = y # yss\<close> less.prems(3) by auto
      obtain xy' where "xy' = concat (map (\<lambda>x. map (\<lambda>y. f x y) (y#yss)) xss)" by simp
      have "concat (map (\<lambda>x. map (f x) ys) xss) \<in> set (permutations xy')"
        by (metis \<open>xy' = concat (map (\<lambda>x. map (f x) (y # yss)) xss)\<close> \<open>ys = y # yss\<close> insert_perm_rel l2 perm_lemma_1)
      then have "concat (map (\<lambda>y. map (\<lambda>x. f x y) xss) (y#yss)) \<in> set (permutations xy')" using \<open>ys=y#yss\<close> less(3)[of xss xy'] \<open>length xss < length xs\<close>
        by blast
      obtain xy'' where "xy'' = concat (map (\<lambda>x. map (\<lambda>y. f x y) (y#yss)) [x])" by simp
      have "concat (map (\<lambda>x. map (f x) ys) [x]) \<in> set (permutations xy'')" using insert_perm_rel l2 perm_lemma_1
        using \<open>xy'' = concat (map (\<lambda>x. map (f x) (y # yss)) [x])\<close> \<open>ys = y # yss\<close> by fastforce
      have "concat (map (\<lambda>x. map (\<lambda>y. f x y) (y#yss)) [x]) \<in> set (permutations xy'')" using \<open>ys=y#yss\<close> less(3)[of "[x]" xy''] \<open>length [x] < length xs\<close>
        using \<open>concat (map (\<lambda>x. map (f x) ys) [x]) \<in> set (permutations xy'')\<close> by blast
      have "xy'' @ xy' = concat (map (\<lambda>x. map (f x) ys) xs)" by (simp add: \<open>xy' = concat (map (\<lambda>x. map (\<lambda>y. f x y) (y#yss)) xss)\<close> \<open>xy'' = concat (map (\<lambda>x. map (\<lambda>y. f x y) (y#yss)) [x])\<close> \<open>ys=y#yss\<close> \<open>xs=x#xss\<close>)
      have "xy'' @ xy' \<in> set (permutations xy)"
        by (simp add: \<open>xy'' @ xy' = concat (map (\<lambda>x. map (f x) ys) xs)\<close> less.prems(3))

      have "concat (map (\<lambda>y. map (\<lambda>x. f x y) xss) (y#yss)) \<in> set (permutations (concat (map (\<lambda>x. map (\<lambda>y. f x y) ys) (xss))))"
        using \<open>concat (map (\<lambda>y. map (\<lambda>x. f x y) xss) (y # yss)) \<in> set (permutations xy')\<close> \<open>xy' = concat (map (\<lambda>x. map (f x) (y # yss)) xss)\<close> \<open>ys = y # yss\<close> by blast
      moreover have "concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) (y#yss)) \<in> set (permutations (concat (map (\<lambda>x. map (\<lambda>y. f x y) ys) [x])))"
        using \<open>concat (map (\<lambda>x. map (f x) (y # yss)) [x]) \<in> set (permutations xy'')\<close> \<open>length [x] < length xs\<close> \<open>xy'' = concat (map (\<lambda>x. map (f x) (y # yss)) [x])\<close> \<open>ys = y # yss\<close> less.prems(2) by blast

      ultimately have "concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) (y#yss)) @ concat (map (\<lambda>y. map (\<lambda>x. f x y) xss) (y#yss)) \<in> set (permutations (concat (map (\<lambda>x. map (\<lambda>y. f x y) ys) xs)))"
        by (smt (z3) \<open>concat (map (\<lambda>y. map (\<lambda>x. f x y) xss) (y # yss)) \<in> set (permutations xy')\<close> \<open>xy'' = concat (map (\<lambda>x. map (f x) (y # yss)) [x])\<close> \<open>xy'' @ xy' = concat (map (\<lambda>x. map (f x) ys) xs)\<close> \<open>ys = y # yss\<close> map_eq_conv perm_prop)
      have "concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) (y # yss)) @ concat (map (\<lambda>y. map (\<lambda>x. f x y) xss) (y # yss)) \<in> set (permutations (concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xss)) (y # yss))))"
        by (metis perm_prop5)
      have "concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xss)) (y#yss)) \<in> set (permutations xy)" using less(4)
        by (metis \<open>concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) (y # yss)) @ concat (map (\<lambda>y. map (\<lambda>x. f x y) xss) (y # yss)) \<in> set (permutations (concat (map (\<lambda>x. map (f x) ys) xs)))\<close> \<open>concat (map (\<lambda>y. map (\<lambda>x. f x y) [x]) (y # yss)) @ concat (map (\<lambda>y. map (\<lambda>x. f x y) xss) (y # yss)) \<in> set (permutations (concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xss)) (y # yss))))\<close> perm_inv_3 permutations_set_equality)
      then show "concat (map (\<lambda>y. map (\<lambda>x. f x y) (x # xss)) ys) \<in> set (permutations xy)"
        by (simp add: \<open>ys = y # yss\<close>)
    qed
  qed
    then show ?thesis
      by (simp add: \<open>xs = x # xss\<close>)
  qed
qed
qed

theorem is_perm4: "size xy = sx * sy \<Longrightarrow> [xy ! ((x_ind*sy)+y_ind). y_ind \<leftarrow> [0..<sy], x_ind \<leftarrow> [0..<sx]] \<in> set (permutations xy)"
proof -
  assume "size xy = sx * sy"
  obtain f where "f = (\<lambda>x y. xy ! ((x*sy)+y))" by simp
  have "[xy ! ((x_ind*sy)+y_ind). x_ind \<leftarrow> [0..<sx], y_ind \<leftarrow> [0..<sy]] = [f x_ind y_ind. x_ind \<leftarrow> [0..<sx], y_ind \<leftarrow> [0..<sy]]"
    by (simp add: \<open>f = (\<lambda>x y. xy ! (x * sy + y))\<close>)
  have "[f x_ind y_ind. x_ind \<leftarrow> [0..<sx], y_ind \<leftarrow> [0..<sy]] \<in> set (permutations xy)" apply (simp add: \<open>f = (\<lambda>x y. xy ! ((x*sy)+y))\<close>) using \<open>size xy = sx * sy\<close> is_perm[of xy sx sy] by simp
  then have "[f x_ind y_ind. y_ind \<leftarrow> [0..<sy], x_ind \<leftarrow> [0..<sx]] \<in> set (permutations xy)" using perm_prop1[of f "[0..<sy]" "[0..<sx]" xy] by simp
  show ?thesis
    using \<open>concat (map (\<lambda>y_ind. map (\<lambda>x_ind. f x_ind y_ind) [0..<sx]) [0..<sy]) \<in> set (permutations xy)\<close> \<open>f = (\<lambda>x y. xy ! (x * sy + y))\<close> by auto
qed

theorem perm_exists:
  assumes
    "xy = [path_m \<interleave> path_n. path_m \<leftarrow> xs, path_n \<leftarrow> ys]" and  
    "yx = [path_m \<interleave> path_n. path_m \<leftarrow> ys, path_n \<leftarrow> xs]"
  shows "\<exists>xy'. xy' \<in> set (permutations xy) \<and> (\<forall>t\<in>set (zip xy' yx). fst t \<in> set (permutations (snd t)))"
proof (cases "xs =[]")
  case True
  then show ?thesis using assms by auto
next
  case f1: False
  then show ?thesis
  proof (cases "ys = []")
    case True
    then show ?thesis using assms apply auto
      by (meson in_set_member permutation_reflexive)
  next
    case False

  obtain xy' where o1: "xy' = [xy ! ((x_ind* (size ys))+y_ind). y_ind \<leftarrow> [0..<size ys], x_ind \<leftarrow> [0..<size xs]]" by simp
  have l1: "size xy' = size xs * size ys" using o1 apply (induction ys) apply auto
    by (simp add: t2)
  have l2: "size xy = size xs * size ys" using assms(1) t2 by auto
  then have l2_5: "size xy = size ys * size xs" by auto
  have l3: "size yx = size xs * size ys" using assms(2) t2 by (metis t3)
  have "xy' \<in> set (permutations xy)" apply (simp add: o1) using is_perm4[of xy "size xs" "size ys"] l2 by blast
  have "\<And>a b. (a, b) \<in> set (zip xy' yx) \<Longrightarrow> a \<in> set (permutations b)"
  proof -
    fix a b
    assume a1: "(a, b) \<in> set (zip xy' yx)"
    then obtain i where o2: "xy'!i=a \<and> yx!i=b \<and> i < size yx" using False f1 apply (induction xy' arbitrary: yx) apply auto
      by (smt (verit, del_insts) in_set_conv_nth length_zip min.strict_boundedE nth_zip old.prod.inject)
    have l4: "i < size xs * size ys" using l3 o2 by auto
    moreover have "... = (size xs - 1) * size ys + size ys"
      by (simp add: f1 mult_eq_if)
    ultimately have "i \<le> ((size xs - 1) * (size ys))+(size ys - 1)" by auto
    have "b = (ys ! (i div length xs)) \<interleave> (xs ! (i mod length xs))"
    proof -
      have "b=[path_m \<interleave> path_n. path_m \<leftarrow> ys, path_n \<leftarrow> xs]!i" using assms(2) o2 by auto
      have "i < size ys * size xs" using local.l3
        by (simp add: local.l4 mult.commute)
      then have "[path_m \<interleave> path_n. path_m \<leftarrow> ys, path_n \<leftarrow> xs]!i = (ys ! (i div length xs)) \<interleave> (xs ! (i mod length xs))" using index_prop4
        by blast
      show "b = (ys ! (i div length xs)) \<interleave> (xs ! (i mod length xs))"
        using \<open>b = concat (map (\<lambda>path_m. map ((\<interleave>) path_m) xs) ys) ! i\<close> \<open>concat (map (\<lambda>path_m. map ((\<interleave>) path_m) xs) ys) ! i = (ys ! (i div length xs)) \<interleave> (xs ! (i mod length xs))\<close> by blast
    qed
    have l5: "i < size [0..<length xs] * size [0..<length ys]"
      by (simp add: local.l4)
    obtain f where o3: "f = (\<lambda>y_ind x_ind.  xy ! (x_ind * length ys + y_ind))" by simp

    have l5_1: "\<forall>i < size xs * size ys. [0..<length ys] ! (i div length xs) = (i div length xs)"
      by (metis add_0 l2_5 less_mult_imp_div_less local.l2 nth_upt)
    have l5_2: "\<forall>i < size xs * size ys. [0..<length xs] ! (i mod length xs) = (i mod length xs)"
      by (simp add: f1)

    have "((i mod length xs * length ys + i div length xs) div length ys) = i mod length xs"
    proof -
      have "(i mod length xs * length ys + i div length xs) div length ys = i mod length xs * length ys div length ys + i div length xs div length ys" by auto
      moreover have "... = i mod length xs + i div length xs div length ys"
        by (simp add: False)
      moreover have "... = i mod length xs"
        by (metis add_cancel_right_right div_less div_mult2_eq local.l4)
      ultimately show ?thesis by presburger
    qed

    have "(i mod length xs * length ys + i div length xs) mod length ys = i div length xs"
    proof -
      have "(i mod length xs * length ys + i div length xs) mod length ys = i mod length xs * length ys mod length ys + i div length xs mod length ys"
        by simp
      moreover have "... = i div length xs mod length ys"
        by auto
      moreover have "... = i div length xs"
        using l2_5 less_mult_imp_div_less local.l2 local.l4 mod_less by presburger
      ultimately show ?thesis by argo
    qed

    obtain j where o4: "j = (i mod length xs * length ys + i div length xs)" by simp
    have "j < size xs * size ys"
      by (smt (verit, ccfv_SIG) Euclidean_Rings.div_eq_0_iff False add_cancel_right_right div_less_iff_less_mult div_mult2_eq div_mult_self3 f1 length_greater_0_conv local.l4 mod_less_divisor o4)
    have "xy' = concat (map (\<lambda>y_ind. map (\<lambda>x_ind. xy ! (x_ind * length ys + y_ind)) [0..<length xs]) [0..<length ys])" using o1 by auto
    moreover have "... = concat (map (\<lambda>x. map (f x) [0..<length xs]) [0..<length ys])" by (auto simp: o3)
    moreover have "... = [f ([0..<length ys] ! (i div length [0..<length xs])) ([0..<length xs] ! (i mod length [0..<length xs])). i \<leftarrow> [0..<size [0..<length ys] * size [0..<length xs]]]" using index_prop5[of f "[0..<length xs]" "[0..<length ys]"] by auto
    moreover have "... = [f ([0..<length ys] ! (i div length xs)) ([0..<length xs] ! (i mod length xs)). i \<leftarrow> [0..<size ys * size xs]]" by auto
    moreover have "... = [f (i div length xs) (i mod length xs). i \<leftarrow> [0..<size ys * size xs]]" using l5_1 l5_2
      by (smt (verit) add_0 calculation(2) calculation(3) calculation(4) l2_5 length_map local.l1 local.l2 map_equality_iff nth_upt o1)
    ultimately have "xy' = [f (i div length xs) (i mod length xs). i \<leftarrow> [0..<size ys * size xs]]"
      by presburger
    then have "xy' ! i = f (i div length xs) (i mod length xs)"
      by (metis (no_types, lifting) l2_5 length_map local.l1 local.l2 local.l4 nth_map nth_upt plus_nat.add_0)
    have "... = xy ! (i mod length xs * length ys + i div length xs)" by (auto simp add: o3)
    have "... = [path_m \<interleave> path_n. path_m \<leftarrow> xs, path_n \<leftarrow> ys] ! (i mod length xs * length ys + i div length xs)" by (simp add: assms)
    have "... = [path_m \<interleave> path_n. path_m \<leftarrow> xs, path_n \<leftarrow> ys] ! j" by (simp add: o4)
    have "... = (xs ! (j div length ys)) \<interleave> (ys ! (j mod length ys))" using index_prop4[of j xs ys "(\<interleave>)"] by (simp add: \<open>j < length xs * length ys\<close>)
    have "... = (xs ! ((i mod length xs * length ys + i div length xs) div length ys)) \<interleave> (ys ! ((i mod length xs * length ys + i div length xs) mod length ys))" using o4 by blast
    have "... = (xs ! (i mod length xs)) \<interleave> (ys ! (i div length xs))"
      using \<open>(i mod length xs * length ys + i div length xs) div length ys = i mod length xs\<close> \<open>(i mod length xs * length ys + i div length xs) mod length ys = i div length xs\<close> by presburger
    have "a = (xs ! (i mod length xs)) \<interleave> (ys ! (i div length xs))"
      using \<open>(xs ! ((i mod length xs * length ys + i div length xs) div length ys)) \<interleave> (ys ! ((i mod length xs * length ys + i div length xs) mod length ys)) = (xs ! (i mod length xs)) \<interleave> (ys ! (i div length xs))\<close> \<open>(xs ! (j div length ys)) \<interleave> (ys ! (j mod length ys)) = (xs ! ((i mod length xs * length ys + i div length xs) div length ys)) \<interleave> (ys ! ((i mod length xs * length ys + i div length xs) mod length ys))\<close> \<open>concat (map (\<lambda>path_m. map ((\<interleave>) path_m) ys) xs) ! (i mod length xs * length ys + i div length xs) = concat (map (\<lambda>path_m. map ((\<interleave>) path_m) ys) xs) ! j\<close> \<open>concat (map (\<lambda>path_m. map ((\<interleave>) path_m) ys) xs) ! j = (xs ! (j div length ys)) \<interleave> (ys ! (j mod length ys))\<close> \<open>f (i div length xs) (i mod length xs) = xy ! (i mod length xs * length ys + i div length xs)\<close> \<open>xy ! (i mod length xs * length ys + i div length xs) = concat (map (\<lambda>path_m. map ((\<interleave>) path_m) ys) xs) ! (i mod length xs * length ys + i div length xs)\<close> \<open>xy' ! i = f (i div length xs) (i mod length xs)\<close> o2 by presburger
    show " a \<in> set (permutations b)"
      by (simp add: \<open>a = (xs ! (i mod length xs)) \<interleave> (ys ! (i div length xs))\<close> \<open>b = (ys ! (i div length xs)) \<interleave> (xs ! (i mod length xs))\<close> inter_perm)
  qed
  then show ?thesis
    by (metis \<open>xy' \<in> set (permutations xy)\<close> prod.collapse)
qed
qed


theorem is_permutation: "(xs \<parallel> ys) \<in> set (permutations (ys \<parallel> xs))"
proof -
  obtain xy where o1: "xy = [path_m \<interleave> path_n. path_m \<leftarrow> xs, path_n \<leftarrow> ys]" by simp
  obtain yx where o2: "yx = [path_m \<interleave> path_n. path_m \<leftarrow> ys, path_n \<leftarrow> xs]" by simp
  
  have size_eq: "size xy = size yx" using o1 o2 by (simp add: t3)
  
  have perm_exists: "\<exists>xy'. xy' \<in> set (permutations yx) \<and> (\<forall>t\<in>set (zip xy' xy). fst t \<in> set (permutations (snd t)))" using perm_exists[of yx xs ys xy] o1 o2  by (simp)
  
  from perm_exists obtain xy' where 
    xy'_def: "xy' \<in> set (permutations yx) \<and> (\<forall>t\<in>set (zip xy' xy). fst t \<in> set (permutations (snd t)))"
    by auto
  
  thus ?thesis
    by (smt (verit) cnf_concurrency_def map_eq_conv o1 o2 perm_inv_3 size_eq t15)
qed

theorem t4: "size (xs \<parallel> ys) = size (ys \<parallel> xs)"
  by (simp add: is_permutation length_inv)

theorem inter_prop1: "xs \<noteq> [] \<Longrightarrow> interleave xs ys \<noteq> []"
  apply (induction ys)
  apply simp
  using interleave.elims by blast

theorem perm_is_equal: "xs \<in> set (permutations ys) \<Longrightarrow> evaluate xs = evaluate ys"
  apply (auto simp: evaluate_def)
  by (metis Choice_prop_1_1 perm_prop_2)

theorem "evaluate (xs \<parallel> ys) = evaluate (ys \<parallel> xs)"
  using is_permutation perm_is_equal
  by blast


end