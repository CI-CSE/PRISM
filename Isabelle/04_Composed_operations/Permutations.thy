theory Permutations
  imports "../T_03_Basic_programs"
begin
section \<open>Permutations for top\<close>

lemma simp_2: "\<forall>x\<^sub>1 x\<^sub>2 x\<^sub>3. f (f x\<^sub>1 x\<^sub>2) x\<^sub>3 = f  x\<^sub>1 (f x\<^sub>2 x\<^sub>3) \<Longrightarrow> foldl f (f a x) xs = f a (foldl f x xs)"
  apply (induct xs rule: rev_induct)
  apply simp
  by simp

lemma fold_composition_assoc: "foldl (;) x (as @ [a]) = (foldl (;) x as) ; a"
proof (induction as arbitrary: x)
  case Nil
  show ?case by simp
next
  case (Cons b bs)
  have "foldl (;) x ((b # bs) @ [a]) = foldl (;) (x ; b) (bs @ [a])" by simp
  also have "... = (foldl (;) (x ; b) bs) ; a" using Cons.IH by simp
  also have "... = (foldl (;) x (b # bs)) ; a" by simp
  finally show ?case .
qed

theorem S_foldl_composition: "S (foldl (;) x as) = \<Union> (S ` (set (x # as)))"
proof (induction as arbitrary: x)
  case Nil
  show ?case by simp
next
  case (Cons a as)
  have "S (foldl (;) x (a # as)) = S ((x ; a) ; (foldl (;) (Skip (complete_state [x, a])) as))"
    using fold_composition_assoc apply (auto simp: complete_state_def)
    using UN_iff Un_iff composition_state list.set_intros(2) local.Cons set_ConsD apply auto[3]
    by (simp add: list.set_intros(1) list.set_intros(2) local.Cons skip_prop_9 sup_commute)
  also have "... = S x \<union> S a \<union> S (foldl (;) (Skip (complete_state [x, a])) as)"
    by auto
  also have "... = S x \<union> S a \<union> (\<Union> (S ` (set as)))"
    using \<open>S (foldl (;) x (a # as)) = S ((x ; a) ; foldl (;) (Skip (complete_state [x, a])) as)\<close> foldl_Cons image_insert local.Cons by force
  finally show ?case
    by (simp add: sup_assoc)
qed

theorem main_theorem: "S (foldl (;) x (a # as)) = S ((foldl (;) x as) ; a)"
proof -
  have "S (foldl (;) x (a # as)) = \<Union> (S ` (set (x # a # as)))"
    by (meson S_foldl_composition)
  also have "... = S x \<union> S a \<union> (\<Union> (S ` (set as)))"
    by (simp add: Un_assoc)
  also have "... = S x \<union> (\<Union> (S ` (set as))) \<union> S a"
    by auto
  also have "... = S (foldl (;) x as) \<union> S a"
    by (simp add: S_foldl_composition)
  also have "... = S ((foldl (;) x as) ; a)"
    by simp
  finally show ?thesis .
qed

theorem skip_fold_complete_state: "S (Skip (complete_state (x # xs))) \<union> S x \<union> S (foldl (;) x xs) = complete_state (x # xs) \<union> S x \<union> complete_state xs"
proof -
  have complete_state_cons: "complete_state (x # xs) = S x \<union> complete_state xs"
    by (simp add: complete_state_prop sup_commute)

  have skip_state: "\<And>s. S (Skip s) = s"
    by (simp add: skip_prop_9)

  have fold_subset: "S (foldl (;) x xs) \<subseteq> S x \<union> complete_state xs"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a as)
    have "S (foldl (;) x (a # as)) = S ((foldl (;) x as) ; a)"
      by (meson main_theorem)
    also have "... \<subseteq> S (foldl (;) x as) \<union> S a"
      by simp
    also have "... \<subseteq> S x \<union> complete_state as \<union> S a"
      using Cons.IH by auto
    also have "... \<subseteq> S x \<union> complete_state (a # as)"
      by (simp add: complete_state_prop sup_assoc)
    finally show ?case
      by (simp add: complete_state_prop subsetI)
  qed

  have "S (Skip (complete_state (x # xs))) \<union> S x \<union> S (foldl (;) x xs)
      = complete_state (x # xs) \<union> S x \<union> S (foldl (;) x xs)"
    using skip_state complete_state_cons
    by metis
  also have "... = complete_state (x # xs) \<union> S x \<union> complete_state xs"
    using fold_subset complete_state_cons by auto
  finally show ?thesis .
qed

theorem simp_5: "S (foldl (;) (Skip (complete_state xs)) xs) = complete_state xs"
proof (induction xs)
  case Nil
  show ?case
    by (simp add: skip_prop_9)
next
  case (Cons x xs)
  have "S (foldl (;) (Skip (complete_state (x # xs))) (x # xs)) = 
        S ((Skip (complete_state (x # xs)) ; x) ; foldl (;) x xs)"
    by (metis (no_types, lifting) complete_state_prop compose_assoc composition_state foldl_Cons simp_2 skip_prop_9 sup.right_idem)
  also have "... = S (Skip (complete_state (x # xs)) ; x) \<union> S (foldl (;) x xs)"
    by auto
  also have "... = S (Skip (complete_state (x # xs))) \<union> S x \<union> S (foldl (;) x xs)"
    by (simp)
  also have "... = complete_state (x # xs) \<union> S x \<union> complete_state xs"
    by (simp add: skip_fold_complete_state)
  also have "... = S x \<union> complete_state xs \<union> S x \<union> complete_state xs"
    by (simp add: complete_state_prop sup_commute)
  also have "... = S x \<union> complete_state xs"
    by auto
  also have "... = complete_state (x # xs)"
    by (simp add: complete_state_prop sup_commute)
  finally show ?case .
qed

theorem simp_4_right: "S (foldl (;) (Skip (complete_state xs)) xs) \<subseteq> complete_state xs"
proof (induct xs)
  case Nil
  then show ?case by (auto simp: Skip_def S_def complete_state_def)
next
  case (Cons a xs)
  assume IH: "S (foldl (;) (Skip (complete_state xs)) xs) \<subseteq> complete_state xs"
  have "Skip (complete_state (a # xs)) = Skip (complete_state (xs)) \<union>\<^sub>p Skip (complete_state ([a]))"
  proof -
    have "complete_state (a # xs) = complete_state (xs) \<union> complete_state ([a])"
      by (meson complete_state_union_1)
    then show "Skip (complete_state (a # xs)) = Skip (complete_state (xs)) \<union>\<^sub>p Skip (complete_state ([a]))"
      by (simp add: skip_prop_10)
  qed
  then show "S (foldl (;) (Skip (complete_state (a # xs))) (a # xs)) \<subseteq> complete_state (a # xs)"
    by (metis order_refl simp_5)
qed



theorem fold_composition_state_inv: "S (fold (;) t b) = S (foldl (;) b t)"
  apply (induction t arbitrary: b)
  apply simp
  by (metis Un_commute compose_assoc composition_state fold_simps(2) main_theorem simp_2)

theorem "S (fold (;) t (Skip (complete_state t))) = S (foldl (;) (Skip (complete_state t)) t)"
  by (simp add: fold_composition_state_inv)

theorem permutation_fold_subset_complete_state:
  assumes "t \<in> set (permutations xs)"
  shows "S (fold (;) t (Skip (complete_state t))) \<subseteq> complete_state xs"
proof -
  have perm_set_eq: "set t = set xs"
    using assms permutation_set_equality by blast

  have complete_state_eq: "complete_state t = complete_state xs"
    using assms permutation_complete_state_equality by blast

  have fold_subset: "S (fold (;) t (Skip (complete_state t))) \<subseteq> complete_state t"
  proof -
    have "S (fold (;) t (Skip (complete_state t))) = 
          S (foldl (;) (Skip (complete_state t)) t)"
      by (simp add: fold_composition_state_inv)
    also have "... \<subseteq> complete_state t"
      by (rule simp_4_right)
    finally show ?thesis .
  qed

  show ?thesis
    using fold_subset complete_state_eq by simp
qed



lemma state_composition: "x \<in> S a \<Longrightarrow> x \<in> S (a ; b)"
  by (auto simp: S_def composition_def)

lemma state_composition_1: "x \<in> S p \<Longrightarrow> x \<in> S (foldl (;) p (xs))"
  apply (induction xs)
  apply simp
  using main_theorem by fastforce

lemma state_composition_2: "x \<in> S a \<Longrightarrow> x \<in> S (foldl (;) p (a#xs))"
  using main_theorem by fastforce

lemma state_composition_3: "x \<in> S a \<Longrightarrow> x \<in> S (foldl (;) p (ys@a#xs))"
  using state_composition_2 by fastforce

lemma complete_state_subset: "complete_state xs \<subseteq> S (Skip (complete_state xs))"
proof -
  have "complete_state xs \<subseteq> State (Skip (complete_state xs))"
    unfolding Skip_def by simp
  thus ?thesis
    unfolding S_def by blast
qed

lemma foldl_composition_preserves_state: "S p \<subseteq> S (foldl (;) p xs)"
proof (induction xs arbitrary: p)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "S p \<subseteq> S (p ; a)"
    unfolding S_def composition_def by auto
  moreover have "S (p ; a) \<subseteq> S (foldl (;) (p ; a) xs)"
    using Cons.IH by blast
  ultimately show ?case
    by auto
qed

lemma Union_prop_1: "\<Union> (set (xs@[x])) = x \<union> \<Union> (set xs)"
  by simp

lemma Union_prop_2: "\<Union> (xs \<union> {x}) = x \<union> \<Union> xs"
  by simp

theorem fold_comp_prop1: "xs \<noteq> [] \<Longrightarrow> foldl (;) x xs = foldl (;) (x;Skip (S x)) xs"
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "foldl (;) x (a # xs) = foldl (;) (x;a) (xs)" by simp
  moreover have "... = foldl (;) (x;((Skip (S x));a)) (xs)" by (metis compose_assoc skip_prop_14)
  moreover have "... = foldl (;) (x;((Skip (S x)))) (a#xs)" by simp
  then show "foldl (;) x (a # xs) = foldl (;) (x ; Skip (S x)) (a # xs)" by (simp add: calculation(2))
qed

theorem fold_comp_prop2: "xs \<noteq> [] \<Longrightarrow> foldl (;) x xs = foldl (;) (x;Skip (complete_state (x#xs))) xs"
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "foldl (;) x (a # xs) = foldl (;) (x;a) (xs)" by simp
  moreover have "... = foldl (;) (x;((Skip (complete_state (x#a#xs)));a)) (xs)"
    apply (induction xs arbitrary: a x) apply (auto simp: ) apply (auto simp: complete_state_def) [1]
    apply (metis compose_assoc skip_prop_13 sup_commute)
    by (metis (no_types, opaque_lifting) Un_assoc Un_left_commute complete_state_prop composition_state)
  moreover have "... = foldl (;) (x;((Skip (complete_state (x#a#xs))))) (a#xs)" by simp
  then show "foldl (;) x (a # xs) = foldl (;) (x ; Skip (complete_state (x#a#xs))) (a # xs)" by (simp add: calculation(2))
qed
theorem fold_comp_prop3: "S (foldl (;) x xs) = complete_state (x # xs)"
  apply (induction xs arbitrary: x) apply (auto simp: complete_state_def)
  by (auto simp add: sup_commute)
theorem fold_comp_prop4: "xs \<noteq> [] \<Longrightarrow> foldl (;) x xs = foldl (;) (x;Skip (complete_state (xs))) xs"
proof -
  assume a1: "xs \<noteq> []"
  obtain x' xs' where o1: "x'#xs'=xs" using a1
    by (metis list.exhaust)
  have l1: "foldl (;) (x;Skip (complete_state xs)) xs = x; foldl (;) (Skip (complete_state xs)) xs"
    by (simp add: simp_2)
  moreover have "... = (x; Skip (complete_state xs)) ; foldl (;) (x') xs'"
    by (metis compose_assoc foldl_Cons o1 simp_2)
  moreover have "... = x ; foldl (;) (x') xs'"
    by (metis fold_comp_prop3 o1 skip_prop_15)
  moreover have "... = foldl (;) (x) xs"
    by (metis compose_assoc foldl_Cons o1 simp_2)
  ultimately show ?thesis by simp
qed

theorem perm_prop_1: "(filter (p) xs) @ (filter (\<lambda>x. \<not>p x) xs) \<in> set (permutations xs)"
proof (induction "size xs" arbitrary: p xs rule: less_induct)
  case less
  then show ?case
  proof (cases "size xs = 0")
    case True
    then show ?thesis
      by simp
  next
    case False
    obtain x xs' where o1: "xs=x#xs'" using False
      using list.exhaust by auto
    
    then show "filter p xs @ filter (\<lambda>x. \<not> p x) xs \<in> set (permutations xs)"
    proof (cases "p x")
      case True
      have "filter (\<lambda>x. \<not> p x) xs = filter (\<lambda>x. \<not> p x) xs'"
        by (simp add: True o1)
      have "filter p xs' @ filter (\<lambda>x. \<not> p x) xs' \<in> set (permutations xs')" using o1 less
        by simp
      then show ?thesis
        by (smt (verit) append_Cons append_Nil2 filter.simps(2) o1 perm_2 perm_inv_2 perm_inv_3)
    next
      case False
      have "filter p xs = filter p xs'"
        by (simp add: False o1)
      have "filter p xs' @ filter (\<lambda>x. \<not> p x) xs' \<in> set (permutations xs')" using o1 less
        by simp
      then show ?thesis 
        by (smt (verit) append_Cons append_Nil2 filter.simps(2) o1 perm_2 perm_inv_2 perm_inv_3)
    qed
  qed
qed

theorem perm_prop_2: "xs \<in> set (permutations ys) \<Longrightarrow> map p xs \<in> set (permutations (map p ys))"
proof (induction "size xs" arbitrary: xs ys p rule: less_induct)
  case less
  then show ?case
  proof (cases "size xs")
    case 0
    then show ?thesis
      using length_inv less.prems by fastforce
  next
    case (Suc n)
    obtain x xs' where o1: "xs=x#xs'" by (metis Suc Suc_length_conv)
    obtain ys' where o2: "\<exists>a b. a@b=ys' \<and> a@x#b=ys"
      by (metis in_set_conv_decomp less.prems list.set_intros(1) o1 permutation_set_equality)
    have "map p xs' \<in> set (permutations (map p ys'))" using o2 o1
      by (metis length_Cons less.hyps less.prems less_Suc_eq perm_split)
    then show "map p xs \<in> set (permutations (map p ys))" using less
      by (metis (mono_tags, lifting) list.simps(9) map_append o1 o2 perm_inv_2 perm_inv_3)
  qed
qed

end