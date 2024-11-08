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
  then show ?case by (auto simp: Fail_def restrict_p_def equiv_def restr_post_def) [1]
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

end