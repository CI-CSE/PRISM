theory Atomic_concurrency
  imports "../T_03_Basic_programs" "Permutations" "Big_choice"
begin
section \<open>Atomic concurrency for top\<close>



theorem "foldl (f::'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program) (f a x) xs = f a (foldl f x xs)"
  nitpick
  oops

theorem complete_state_subset_fold_composition: "x \<in> complete_state xs \<Longrightarrow> x \<in> S (foldl (;) (Skip (complete_state xs)) xs)"
proof (induction xs)
  case Nil
  then show ?case
    by (simp add: complete_state_def S_def Skip_def)
next
  case (Cons a xs)
  show ?case
  proof -
    have "x \<in> complete_state (a # xs)"
      using Cons.prems by simp
    then have "x \<in> S a \<or> x \<in> complete_state xs"
      unfolding complete_state_def
      by (metis Un_iff complete_state_def complete_state_prop)
    thus ?thesis
    proof
      assume "x \<in> S a"
      then show ?thesis
        by (simp add: S_foldl_composition)
    next
      assume "x \<in> complete_state xs"
      then have "x \<in> S (foldl (;) (Skip (complete_state xs)) xs)"
        using Cons.IH by simp
      moreover have "S (foldl (;) (Skip (complete_state xs)) xs) \<subseteq> S (foldl (;) (Skip (complete_state (a # xs))) (a # xs))"
        by (metis UnCI complete_state_prop simp_5 subsetI)
      ultimately show ?thesis
        by auto
    qed
  qed
qed



theorem fold_choice_inv_1: "foldl (\<union>\<^sub>p) (Fail {}) (a # xs)  = a \<union>\<^sub>p foldl (\<union>\<^sub>p) (Fail {}) (xs) "
  apply (induction xs arbitrary: a)
  apply (auto)
  by (metis choice_assoc_1 choice_commute)

theorem fold_choice_inv_2: "S (foldl (\<union>\<^sub>p) (Fail {}) xs ) = \<Union> (set (map (S) xs))"
proof (induction xs)
  case Nil
  then show ?case by (auto simp: Fail_def S_def)
next
  case (Cons a xs)
  assume IH: "S (foldl (\<union>\<^sub>p) (Fail {}) xs ) = \<Union> (set (map S xs))"
  have l1: "foldl (\<union>\<^sub>p) (Fail {}) (a # xs)  = a \<union>\<^sub>p foldl (\<union>\<^sub>p) (Fail {}) (xs) "
    using fold_choice_inv_1 by auto
  then show "S (foldl (\<union>\<^sub>p) (Fail {}) (a # xs) ) = \<Union> (set (map S (a # xs)))"
    by (simp add: local.Cons) 
qed


theorem conc_elems_state: "x \<in> set (conc_elems xs) \<Longrightarrow> S x = complete_state xs"
  apply (simp add: conc_elems_def)
  by (metis Concat_state imageE permutation_complete_state_equality)


theorem atomic_conc_complete_state: "S (atomic_conc xs) = complete_state xs"
  apply (cases "xs = []") apply (auto simp: atomic_conc_def conc_elems_def complete_state_def Skip_def S_def)[1]
proof -
  assume a1: "xs \<noteq> []"
  have l1: "set (conc_elems xs) \<noteq> {}" using a1 apply (auto simp: conc_elems_def)
    by (metis member_rec(2) permutation_reflexive)
  have l2: "atomic_conc xs = \<Union>\<^sub>p (conc_elems xs)" by (auto simp: atomic_conc_def)
  have l3: "S (\<Union>\<^sub>p (conc_elems xs)) = \<Union> {S x | x . x \<in> set (conc_elems xs)}"
    by (metis Big_choice.Choice_state)
  have l4: "... = \<Union> {complete_state xs | x . x \<in> set (conc_elems xs)}" using conc_elems_state by auto
  have l5: "... = complete_state xs" using Union_prop_1 l1
    by metis
  show ?thesis using l1 l2 l3 l4 l5 by simp
qed

theorem atomic_conc_equivalence: "S (Concat xs) = S (atomic_conc xs)"
proof -
  have fold_eq: "\<forall>p\<in>set (permutations xs). S (Concat p) = complete_state xs"
    by (metis Concat_state permutation_complete_state_equality)
  have "S (atomic_conc xs) = complete_state xs"
    by (simp add: atomic_conc_complete_state)
  moreover have "S (Concat xs) = complete_state xs"
    by (simp add: Concat_state)
  ultimately show ?thesis by simp
qed


theorem pre_zero: "Pre (atomic_conc []) = {}"
  by (auto simp: atomic_conc_def conc_elems_def Fail_def complete_state_def Skip_def)

theorem pre_one: "is_feasible x \<Longrightarrow> Pre (atomic_conc [x]) = Pre x"
  apply auto
  apply (auto simp: atomic_conc_def  Fail_def Skip_def composition_def) [1]
  by (auto simp: atomic_conc_def conc_elems_def is_feasible_def Fail_def composition_def corestrict_r_def complete_state_def Skip_def subset_iff Domain_iff S_def Field_def Range_iff) [2]

theorem lemma_pre_1: "Pre (atomic_conc (a#[b])) \<subseteq> Pre a \<union> Pre b"
  by (auto simp: atomic_conc_def conc_elems_def complete_state_def composition_def Fail_def corestrict_r_def Skip_def S_def Field_def)

fun list_equiv :: "'a Program list \<Rightarrow> 'a Program list \<Rightarrow> bool" where
  "list_equiv [] [] = True" | 
  "list_equiv (x#xs) (y#ys) = ((x \<equiv>\<^sub>p y) \<and> list_equiv xs ys)" |
  "list_equiv _ _ = False"

theorem list_equiv_reflexive: "list_equiv xs xs"
  apply (induction xs)
  by (auto simp: equiv_def)

theorem list_equiv_comp_equiv: "list_equiv xs ys \<Longrightarrow> b \<equiv>\<^sub>p b' \<Longrightarrow> fold (;) xs b \<equiv>\<^sub>p fold (;) ys b'"
proof (induction xs arbitrary: ys b b')
  case Nil
  then show ?case
    apply (cases "ys = []")
    apply auto
    using list_equiv.elims(2) by fastforce
next
  case (Cons a xs)
  assume IH: "\<And> ys b b'. list_equiv xs ys \<Longrightarrow> b \<equiv>\<^sub>p b' \<Longrightarrow> fold (;) xs b \<equiv>\<^sub>p fold (;) ys b'"
  assume a1: "list_equiv (a # xs) ys"
  assume a2: "b \<equiv>\<^sub>p b'"
  then show "fold (;) (a # xs) b \<equiv>\<^sub>p fold (;) ys b'"
    by (smt (verit, ccfv_threshold) IH a1 composition_equiv fold_simps(2) list.distinct(1) list.sel(3) list_equiv.elims(2))
qed


theorem skip_prop_1: "is_feasible a \<Longrightarrow> S a \<subseteq> C \<Longrightarrow> a ; Skip C \<equiv>\<^sub>p a"
  by (smt (verit) Skip_comprestrict compose_assoc composition_equiv equiv_is_transitive skip_compose2 skip_prop_14 skip_prop_5)

theorem skip_prop_2: "is_feasible a \<Longrightarrow>a ; Skip (complete_state (a # xs)) \<equiv>\<^sub>p a"
  by (simp add: complete_state_prop skip_prop_1)

theorem skip_restrict: "is_feasible a \<Longrightarrow> fold (;) xs (a ; Skip (complete_state (a # xs))) \<equiv>\<^sub>p fold (;) xs a"
proof -
  assume a1: "is_feasible a"
  have l1: "a ; Skip (complete_state (a # xs)) \<equiv>\<^sub>p a" using a1 skip_prop_2
    by auto
  show "fold (;) xs (a ; Skip (complete_state (a # xs))) \<equiv>\<^sub>p fold (;) xs a" using l1 list_equiv_reflexive list_equiv_comp_equiv
    by blast
  qed

definition feas_of :: "'a Program \<Rightarrow> 'a Program" where
  "feas_of p \<equiv> \<lparr>State=S p, Pre=Pre p \<inter> Domain (post p), post=post p\<rparr>"

theorem feas_of_prop: "is_feasible (feas_of p)" by (auto simp: is_feasible_def feas_of_def)

theorem feas_of_prop2: "is_feasible p \<Longrightarrow> feas_of p \<triangleq> p"
proof -
  assume a1: "is_feasible p"
  have l1: "S (feas_of p) = S p" by (auto simp: feas_of_def S_def Field_def)
  have l2: "Pre (feas_of p) = Pre p" using a1 by (auto simp: feas_of_def is_feasible_def)
  have l3: "post (feas_of p) = post p" by (auto simp: feas_of_def)
  show ?thesis using l1 l2 l3 by (auto simp: Definitions.equal_def)
qed

theorem skip_prop_4: "a ; Skip (S a) \<equiv>\<^sub>p feas_of a"
  by (auto simp: equiv_def composition_def Skip_def feas_of_def corestrict_r_def S_def Domain_iff Field_def Range_iff restr_post_def restrict_r_def)

theorem skip_prop_5: "fold (;) xs (Skip (complete_state (a # xs)) ; a) \<equiv>\<^sub>p fold (;) xs a"
  by (simp add: complete_state_prop list_equiv_comp_equiv list_equiv_reflexive skip_prop_6)


theorem get_trace: "x \<in> set (conc_elems xs) \<Longrightarrow> \<exists>tr. tr \<in> set (permutations xs) \<and> x = Concat tr"
  by (auto simp: conc_elems_def)


theorem skip_prop_6: "Skip (S p \<union> x) ; p \<equiv>\<^sub>p Skip (S p) ; p"
  by (auto simp: Skip_def composition_def S_def corestrict_r_def restr_post_def restrict_r_def relcomp_unfold Field_def Domain_iff Range_iff Un_def equiv_def)

theorem no_right_neutral: "\<exists>t. p;t \<equiv>\<^sub>p p"
  oops

theorem corestrict_skip: "(a; Skip (S a \<union> S b)) ; b \<equiv>\<^sub>p a ; b"
proof -
  have l1: "Skip (S a \<union> S b) ; b \<equiv>\<^sub>p b"
    by (simp add: Skip.skip_prop_6)
  show ?thesis
    by (simp add: equals_equiv_relation_3 composition_equiv local.l1)
qed

theorem skip_prop_8: "(a; Skip (S a)) ; b \<equiv>\<^sub>p a ; b"
  by (metis equals_equiv_relation_3 skip_prop_14)

theorem skip_prop_9: "(a; Skip (S b)) ; b \<equiv>\<^sub>p a ; b"
  by (simp add: equals_equiv_relation_3 composition_equiv skip_compose3)

theorem fold_decomp: "xs \<noteq> [] \<Longrightarrow> (foldl (;) (a) (xs)) \<equiv>\<^sub>p a; (foldl (;) (Skip (complete_state xs)) (xs))"
proof -
  assume a1: "xs \<noteq> []"
  obtain x xss where o1: "x#xss =xs"
    by (metis a1 list.exhaust)
  have l1: "a; (foldl (;) (Skip (complete_state xs)) (xs)) = a; (Skip (complete_state xs); (foldl (;) (x) (xss)))"
    by (metis compose_assoc foldl_Cons o1 simp_2)
  moreover have l2: "... = a;  (foldl (;) (Skip (complete_state xs);x) xss)"
    using equiv_is_reflexive local.l1 o1 by fastforce
  moreover have l3: "... \<equiv>\<^sub>p a;  (foldl (;) (x) xss)"
    by (simp add: Skip.skip_prop_6 equiv_is_reflexive composition_equiv fold_comp_prop3 fold_compose o1)
  moreover have l4: "... \<equiv>\<^sub>p (foldl (;) (a) xs)"
    by (metis compose_assoc equiv_is_reflexive foldl_Cons o1 simp_2)
  ultimately show ?thesis
    using equiv_is_symetric equiv_is_transitive by fastforce
qed

theorem fold_decomp2: "xs \<noteq> [] \<Longrightarrow> (foldl (;) (a) (xs)) \<equiv>\<^sub>p a; (foldl (;) (Skip (S a)) (xs))"
proof -
  assume a1: "xs \<noteq> []"
  obtain x xss where o1: "x#xss =xs"
    by (metis a1 list.exhaust)
  have l1: "a;(foldl (;) (Skip (S a)) (xs)) = a; (Skip (S a); (foldl (;) (x) (xss)))"
    by (metis compose_assoc foldl_Cons o1 simp_2)
  have l2: "... \<equiv>\<^sub>p a; (foldl (;) (x) (xss))"
    by (metis compose_assoc equals_equiv_relation_2 equiv_is_reflexive composition_equiv skip_unsafe_compose_r_1 unsafe_gets_safe_1)
  have l3: "... \<equiv>\<^sub>p foldl (;) (a) (xs)"
    by (metis compose_assoc equiv_is_reflexive foldl_Cons o1 simp_2)
  show ?thesis
    using equiv_is_symetric equiv_is_transitive local.l1 local.l2 local.l3 by fastforce
qed

theorem fold_equiv_maintained: "a \<equiv>\<^sub>p b \<Longrightarrow> foldl (;) a xs \<equiv>\<^sub>p foldl (;) b xs"
  apply (induction xs arbitrary: a b)
  apply simp
  by (simp add: equiv_is_reflexive composition_equiv)

theorem fold_compress_1: "ys \<noteq> [] \<Longrightarrow> \<exists>e'. (a);e' \<equiv>\<^sub>p (foldl (;) (Skip (complete_state ([a]@ys))) ([a]@ys))"
proof (induction ys arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons b ys)
  have "(foldl (;) (Skip (complete_state ([a]@(b#ys)))) ([a]@(b#ys))) = Skip (complete_state ([a]@(b#ys))) ; (foldl (;) (a)) (b#ys)"
    by (simp add: simp_2)
  moreover have "... = (foldl (;) (Skip (complete_state ([a]@(b#ys))) ;a)) (b#ys)"
    by (simp add: simp_2)
  moreover have "... = (foldl (;) ((Skip (complete_state ([a]@(b#ys))) ;a);b)) (ys)"
    by simp
  moreover have "... = (Skip (complete_state ([a]@(b#ys))) ;a); (foldl (;) b ys)"
    by (simp add: simp_2)
  moreover have "... \<equiv>\<^sub>p a; (foldl (;) b ys)"
    by (metis Cons_eq_appendI Skip.skip_prop_6 complete_state_prop compose_assoc fold_equiv_maintained foldl_Cons simp_2 sup.cobounded2)
  ultimately show ?case
    using equiv_is_symetric by auto
qed

theorem fold_compress_2: "\<exists>e'. e';a \<equiv>\<^sub>p (foldl (;) (Skip (complete_state (ys@[a]))) (ys@[a]))"
  using equals_equiv_relation_3 by auto

theorem fold_compress_3: "\<exists>s' e'. (s';a);e' \<equiv>\<^sub>p (foldl (;) (Skip (complete_state (xs@[a]@ys))) (xs@[a]@ys)) \<or> s';a=(foldl (;) (Skip (complete_state (xs@[a]@ys))) (xs@[a]@ys))"
  proof (cases "ys = []")
    case True
    then show ?thesis
      by auto
  next
    case False
    assume a1: "ys \<noteq> []"
    then show ?thesis
    proof (cases "xs = []")
      case True
      have l1: "\<And> a .ys \<noteq> [] \<Longrightarrow> \<exists>e'. a ; e' \<equiv>\<^sub>p foldl (;) (Skip (complete_state ([a] @ ys))) ([a] @ ys)" using fold_compress_1 by simp
      then have "ys \<noteq> [] \<Longrightarrow> \<exists>e'. a ; e' \<equiv>\<^sub>p foldl (;) (Skip (complete_state ([a] @ ys))) ([a] @ ys)"
        by auto
      then obtain e' where o1: "foldl (;) (Skip (complete_state ([a] @ ys))) ([a] @ ys) \<equiv>\<^sub>p a ; e'"
        using a1 equiv_is_symetric by blast
      have "... \<equiv>\<^sub>p (Skip (S a); a) ; e'"
        by (meson equals_equiv_relation_3 equiv_is_symetric composition_equiv skip_compose3)
      then show ?thesis
        using \<open>a ; e' \<equiv>\<^sub>p (Skip (S a) ; a) ; e'\<close> equiv_is_symetric equiv_is_transitive o1
        by (metis (no_types, lifting) True eq_Nil_appendI) 
    next
      case False
      obtain x xss where o1: "x@xss=xs" by auto
      obtain y yss where o2: "y@yss=ys" by auto
      obtain sk where o3: "Skip (complete_state (xs @ [a] @ ys)) = sk" by simp
      have l1: "foldl (;) (sk) (xs @ [a] @ ys) = foldl (;) (sk;foldl (;) (sk) (xs)) ([a] @ ys)"
        by (metis compose_assoc foldl_append o3 simp_2 skip_is_idempondent_composition)
      have l2: "... = foldl (;) ((sk;foldl (;) (sk) (xs)) ; a) (ys)"
        by simp
      have l3: "... = (sk;foldl (;) (sk) (xs)) ; foldl (;) (a) (ys)"
        by (simp add: simp_2)
      then show ?thesis
        by (metis a1 equiv_is_symetric fold_decomp local.l1 local.l2 o3) 
    qed
  qed

theorem conc_elems_dec:"x \<in> set (conc_elems (a # xs)) \<Longrightarrow> \<exists>s' e'. (s';a);e' = x \<or> s';a=x \<or> a = x\<or> a;e' = x"
proof -
  fix x xs assume a1: "x \<in> set (conc_elems (a # xs))"
  obtain tr where o1: "tr \<in> set (permutations (a # xs)) \<and> x = Concat tr" using get_trace a1 by blast
  obtain x\<^sub>s x\<^sub>e where o2: "x\<^sub>s@[a]@x\<^sub>e = tr"
    by (metis Cons_eq_appendI append_eq_append_conv2 append_self_conv o1 permutation_split_set)
  show "\<exists>s' e'. (s';a);e' = x \<or> s';a=x \<or> a = x\<or> a;e' = x"
  proof (cases "x\<^sub>s = []")
    case True
    have l1: "a#x\<^sub>e = tr"
      using True o2 by auto
    have l2: "x = Concat (a#x\<^sub>e)"
      by (simp add: local.l1 o1)
    have l3: "(foldl (;) (Skip (complete_state (a#x\<^sub>e))) (a#x\<^sub>e)) = Skip (complete_state (a#x\<^sub>e)) ; (foldl (;) (a) (x\<^sub>e))"
      by (simp add: simp_2)
    then show ?thesis
    proof (cases "x\<^sub>e = []")
      case True
      then show ?thesis
        using True local.l2 by auto
    next
      case False
      obtain x1\<^sub>e xt\<^sub>e where o2: "x1\<^sub>e#xt\<^sub>e = x\<^sub>e"
        by (metis False permutations.elims)
      have l4: "(foldl (;) (Skip (complete_state tr)) tr) = Skip (complete_state tr) ; (foldl (;) (a) x\<^sub>e)"
        using local.l1 local.l3 by auto
      have l5: "... = (Skip (complete_state tr) ; a) ; (foldl (;) (x1\<^sub>e) xt\<^sub>e)"
        by (metis compose_assoc foldl_Cons o2 simp_2)
      then show ?thesis
        by (metis Concat.simps(3) Concat_prop_1 False local.l2 o2)
    qed
  next
    case False
    obtain x1\<^sub>s xt\<^sub>s where o3: "x1\<^sub>s#xt\<^sub>s = x\<^sub>s"
      using False hd_Cons_tl by auto
    have l1: "tr = (x1\<^sub>s#xt\<^sub>s)@[a]@x\<^sub>e" using o2 o3 by simp
    have l2: "(foldl (;) (Skip (complete_state tr)) tr) = Skip (complete_state tr); (foldl (;) (x1\<^sub>s) (xt\<^sub>s@[a]@x\<^sub>e))"
      by (metis (mono_tags, lifting) Cons_eq_appendI compose_assoc foldl_Cons o2 o3 simp_2)
    have l3: "... = (foldl (;) (Skip (complete_state tr);x1\<^sub>s) (xt\<^sub>s@[a]@x\<^sub>e))"
      by (simp add: simp_2)
    have l4: "... \<equiv>\<^sub>p (foldl (;) (Skip (S x1\<^sub>s);x1\<^sub>s) (xt\<^sub>s@[a]@x\<^sub>e))"
    proof -
      have l1: "Skip (S x1\<^sub>s);x1\<^sub>s \<equiv>\<^sub>p Skip (complete_state tr);x1\<^sub>s"
        by (metis (no_types, lifting) Definitions.equiv_def Skip.skip_prop_6 composition_state foldl_composition_preserves_state local.l2 local.l3 simp_5 skip_compose3 sup.bounded_iff)
      show ?thesis
        using equiv_is_symetric fold_equiv_maintained local.l1 by blast
    qed
    have l5: "... \<equiv>\<^sub>p (foldl (;) (Skip (S x1\<^sub>s);x1\<^sub>s) (xt\<^sub>s@[a]@x\<^sub>e))"
      by (simp add: equiv_is_reflexive)
    have l6: "... \<equiv>\<^sub>p (foldl (;) (x1\<^sub>s) (xt\<^sub>s@[a]@x\<^sub>e))"
      using fold_equiv_maintained skip_compose3 by blast
    then show ?thesis
    proof (cases "x\<^sub>e = []")
      case True
      then show ?thesis apply auto
        by (smt (verit) Concat.elims append_Cons concat.simps(1) concat_eq_append_conv fold_composition_assoc list.distinct(1) list.inject o1 o2 o3)
    next
      case False
      obtain x1\<^sub>e xt\<^sub>e where o4: "x1\<^sub>e#xt\<^sub>e = x\<^sub>e"
        by (metis False permutations.elims)
      have l7: "Concat tr = Concat (x\<^sub>s@(a#x\<^sub>e))"
        using o2 by auto
      have l8: "... = (Concat x\<^sub>s ; a) ; Concat x\<^sub>e"
        by (smt (verit) Concat.elims Concat.simps(2) Concat_prop_1 False Nil_is_append_conv \<open>\<And>thesis. (\<And>x1\<^sub>e xt\<^sub>e. x1\<^sub>e # xt\<^sub>e = x\<^sub>e \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>\<And>thesis. (\<And>x1\<^sub>s xt\<^sub>s. x1\<^sub>s # xt\<^sub>s = x\<^sub>s \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>\<And>thesis. (\<And>x\<^sub>s x\<^sub>e. x\<^sub>s @ [a] @ x\<^sub>e = tr \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> append_Cons append_eq_append_conv2 append_self_conv2 foldl_Cons foldl_Nil foldl_append list.distinct(1) list.inject local.l7 not_Cons_self2 o2 o3)
      show ?thesis
        using local.l7 local.l8 o1 by auto
    qed
  qed
qed

theorem concat_prop_1: "tr \<in> set (permutations xs) \<Longrightarrow> Concat tr \<in> set (conc_elems xs)"
  by (auto simp: conc_elems_def)



theorem fold_choice_inv: "t \<in> set (xs) \<Longrightarrow> foldl (\<union>\<^sub>p) (x) (xs) = t \<union>\<^sub>p (foldl (\<union>\<^sub>p) (x) (xs))"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  assume IH: "t \<in> set xs \<Longrightarrow> foldl (\<union>\<^sub>p) x xs = t \<union>\<^sub>p foldl (\<union>\<^sub>p) x xs"
  assume a1: "t \<in> set (a # xs)"
  have "foldl (\<union>\<^sub>p) x (a # xs) = foldl (\<union>\<^sub>p) (x \<union>\<^sub>p a) (xs)"
    by simp
  moreover have "... = a \<union>\<^sub>p foldl (\<union>\<^sub>p) (x ) (xs)"
    by (metis choice_assoc_1 choice_commute simp_2)
  ultimately show "foldl (\<union>\<^sub>p) x (a # xs) = t \<union>\<^sub>p foldl (\<union>\<^sub>p) x (a # xs)"
  proof (cases "t = a")
    case True
    have "a \<union>\<^sub>p foldl (\<union>\<^sub>p) (x) (xs) = (t \<union>\<^sub>p a) \<union>\<^sub>p foldl (\<union>\<^sub>p) (x) (xs)"
      by (simp add: choice_idem_2 True)
    then show ?thesis
      using True \<open>foldl (\<union>\<^sub>p) (x \<union>\<^sub>p a) xs = a \<union>\<^sub>p foldl (\<union>\<^sub>p) x xs\<close> by auto
  next
    case False
    have "t \<in> set (xs)"
      using False a1 by auto
    have "a \<union>\<^sub>p foldl (\<union>\<^sub>p) (x ) (xs) = a \<union>\<^sub>p (t \<union>\<^sub>p foldl (\<union>\<^sub>p) x (xs))"
      using Cons.IH \<open>t \<in> set xs\<close> by auto
    have "... = (t \<union>\<^sub>p foldl (\<union>\<^sub>p) x (a#xs))"
      using \<open>foldl (\<union>\<^sub>p) (x \<union>\<^sub>p a) xs = a \<union>\<^sub>p foldl (\<union>\<^sub>p) x xs\<close> choice_assoc_1 choice_commute by fastforce
    then show "foldl (\<union>\<^sub>p) x (a # xs) = t \<union>\<^sub>p foldl (\<union>\<^sub>p) x (a # xs)"
      using \<open>a \<union>\<^sub>p foldl (\<union>\<^sub>p) x xs = a \<union>\<^sub>p (t \<union>\<^sub>p foldl (\<union>\<^sub>p) x xs)\<close> \<open>foldl (\<union>\<^sub>p) (x \<union>\<^sub>p a) xs = a \<union>\<^sub>p foldl (\<union>\<^sub>p) x xs\<close> by auto
  qed
qed

theorem atomic_conc_inv: "tr \<in> set (conc_elems xs) \<Longrightarrow> tr \<union>\<^sub>p atomic_conc xs \<equiv>\<^sub>p atomic_conc xs"
  apply (auto simp: atomic_conc_def)
  by (smt (verit, ccfv_threshold) Choice.simps(2) Choice_prop_1_3 Nil_is_append_conv append_self_conv2 choice_commute choice_decomp_1 in_set_conv_decomp_first program_is_subprogram_of_choice subprogram_is_order)

theorem atomic_conc_inv2: "x \<in> set (conc_elems xs) \<Longrightarrow> x \<preceq>\<^sub>p atomic_conc xs"
proof -
  assume "x \<in> set (conc_elems xs)"
  then obtain pps :: "'a Program \<Rightarrow> 'a Program list \<Rightarrow> 'a Program list" and ppsa :: "'a Program \<Rightarrow> 'a Program list \<Rightarrow> 'a Program list" and ppsb :: "'a Program \<Rightarrow> 'a Program list \<Rightarrow> 'a Program list" and ppsc :: "'a Program \<Rightarrow> 'a Program list \<Rightarrow> 'a Program list" where
    f1: "conc_elems xs = pps x (conc_elems xs) @ x # ppsa x (conc_elems xs)"
    by (meson in_set_conv_decomp)
  then have f2: "x \<preceq>\<^sub>p \<Union>\<^sub>p (conc_elems xs) \<or> [] = pps x (conc_elems xs) @ ppsa x (conc_elems xs)"
    by (metis (no_types) Choice_prop_1_3 program_is_subprogram_of_choice)
  { assume "x \<noteq> \<Union>\<^sub>p (conc_elems xs)"
    then have "\<not> List.member (insert_all x []) (conc_elems xs)"
      by (metis (no_types) Choice.simps(2) Un_iff append.right_neutral in_set_member insert_all.simps(1) member_rec(1) perm_inv_3 set_append singleton_permutation)
    then have "x \<preceq>\<^sub>p \<Union>\<^sub>p (conc_elems xs)"
      using f2 f1 in_set_member by fastforce }
  then show ?thesis
    by (metis (full_types) atomic_conc_def subprogram_is_preorder)
qed

theorem atomic_conc_inv3: "Concat xs \<preceq>\<^sub>p atomic_conc xs"
  by (meson atomic_conc_inv2 concat_prop_1 in_set_member permutation_reflexive)

theorem perm_prop: "set (permutations (a@b)) = set (permutations (b@a))"
  apply (induction a arbitrary: b)
  apply simp
  by (metis Cons_eq_appendI append_assoc append_self_conv2 perm_2)

theorem perm_prop2: "x \<in> set (permutations y) \<Longrightarrow> set (conc_elems (y)) = set (conc_elems (x))"
proof (induction x arbitrary: y)
  case Nil
  then show ?case by (metis permutation_set_equality set_empty)
next
  case (Cons a x)
  assume IH: "\<And>y. x \<in> set (permutations y) \<Longrightarrow> set (conc_elems y) = set (conc_elems x)"
  assume a1: "a # x \<in> set (permutations y)"
  obtain y' where o1: "\<exists>s e. y'=s@e \<and> s@a#e=y"
    by (metis a1 perm_inv_3 permutation_split_set)
  have l1: "x \<in> set (permutations y')"
    using a1 o1 perm_split by force
  have l2: "set (conc_elems y') = set (conc_elems x)"
    by (simp add: IH local.l1)
  then show "set (conc_elems y) = set (conc_elems (a # x))"
    by (metis (mono_tags, lifting) a1 conc_elems_def list.set_map permutations_set_equality)
qed

theorem perm_prop3: "set (conc_elems (a@b)) = set (conc_elems (b@a))"
  apply (induction a arbitrary: b)
   apply auto[1]
  by (metis insert_perm_rel l4 perm_prop perm_prop2 permutations_set_equality)

theorem perm_prop4: "size (insert_all x xs) = size xs + 1"
  apply (induction xs)
  by auto

theorem perm_prop5: "size (concat []) = 0 " by simp
theorem perm_prop6: "size (concat (x#xs)) = size x + size (concat (xs))" by simp

theorem perm_prop7: "size (concat xs) = foldl (\<lambda>a b. a + (size b)) 0 xs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume IH: "length (concat xs) = foldl (\<lambda>a b. a + length b) 0 xs"
  have "length (concat (a # xs)) = length a + length (concat xs)"
    by simp
  moreover have "... = length a + foldl (\<lambda>a b. a + length b) 0 xs"
    by (simp add: IH)
  moreover have "... = foldl (\<lambda>a b. a + length b) (length a) xs"
    apply (induction xs arbitrary: a)
    apply auto
    by (metis (mono_tags, lifting) Ex_list_of_length add.assoc)
  moreover have "... = foldl (\<lambda>a b. a + length b) 0 (a#xs)"
    by auto
  ultimately show ?case
    by argo 
qed

theorem perm_prop8: "a \<in> set (map (insert_all x) (permutations xs)) \<Longrightarrow> b \<in> set a \<Longrightarrow> size b = size xs + 1"
  apply (induction xs) 
   apply auto
  by (metis insert_perm_rel length_Cons length_inv)

theorem perm_prop9: "a \<in> set (map (insert_all x) (permutations xs)) \<Longrightarrow> size a = size xs + 1"
proof -
  assume a1: "a \<in> set (map (insert_all x) (permutations xs))"
  have l1: "set (map (insert_all x) (permutations xs)) = {insert_all x y | y. y \<in> set (permutations xs)}" by auto
  obtain y where o1: "a = insert_all x y \<and> y \<in> set (permutations xs)"
    using a1 by auto
  have l2: "size y = size xs"
    by (simp add: length_inv o1)
  show "size a = size xs + 1"
    by (simp add: local.l2 o1 perm_prop4)
qed

lemma size_concat: "size (concat xss) = sum_list (map size xss)"
  by (simp add: length_concat)

value "concat (map (insert_all (1::nat)) [[2,3], [7]])"

theorem insert_all_prop: "size (concat (map (insert_all x) xss)) = sum_list (map (\<lambda>y. Suc (size y)) xss)"
  apply (induction xss arbitrary: x)
  apply simp
  by (simp add: perm_prop4)

theorem "x \<in> set (permutations xs) \<Longrightarrow> y \<in> set (permutations xs) \<Longrightarrow> size x = size y"
  by (simp add: length_inv)

theorem sum_list_simp: "(\<forall>x \<in> set xss. \<forall> y \<in> set xss. size x = size y) \<Longrightarrow> sum_list (map size xss) = size xss * size (hd xss)"
  apply (induction xss)
  by auto

theorem size_lemma: "\<forall>x \<in> set xs. size x = n \<Longrightarrow> size (concat xs) = size xs * n"
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume IH: "\<And>n. \<forall>x\<in>set xs. length x = n \<Longrightarrow> length (concat xs) = length xs * n"
  assume a1: "\<forall>x\<in>set (a # xs). length x = n"
  have l2: "length (concat xs) = length xs * n"
    by (simp add: IH a1)
  have l4: "length a = n"
    by (simp add: a1)
  then show "length (concat (a # xs)) = length (a # xs) * n"
    by (simp add: local.l2)
qed

lemma length_concat_insert_all: "length (concat (map (insert_all x) (permutations xs))) = (length xs + 1) * length (permutations xs)"
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by auto
next
  case (Cons y ys)
  then show ?case
  proof -
    assume IH: "\<And>x. length (concat (map (insert_all x) (permutations ys))) = (length ys + 1) * length (permutations ys)"
    have l1: "permutations (y # ys) = concat (map (insert_all y) (permutations ys))"
      by simp
    hence "length (concat (map (insert_all x) (concat (map (insert_all y) (permutations ys))))) = (length (y # ys) + 1) * length (permutations (y # ys))"
      by (metis l1 length_map mult.commute perm_prop9 size_lemma)
    thus ?thesis
      by simp
  qed
qed

theorem size_permutations_fact: "length (permutations xs) = fact (length xs)"
proof (induction xs)
  case Nil
  then show ?case 
  proof -
    have "permutations [] = [[]]" by simp
    thus "length (permutations []) = fact (length [])"
      by simp
  qed
next
  case (Cons x xs)
  then show ?case
  proof -
    assume IH: "length (permutations xs) = fact (length xs)"
    have "length (permutations (x # xs)) = length (concat (map (insert_all x) (permutations xs)))"
      by simp
    have "\<forall>ys. length (insert_all x ys) = length ys + 1"
      by (simp add: perm_prop4)
    hence "length (concat (map (insert_all x) (permutations xs))) = (length xs + 1) * length (permutations xs)"
      by (simp add: length_concat_insert_all)
    with IH have "length (concat (map (insert_all x) (permutations xs))) = (length xs + 1) * fact (length xs)"
      by simp
    also have "... = fact (length (x # xs))"
      by simp
    finally show "length (permutations (x # xs)) = fact (length (x # xs))"
      by simp
  qed
qed

theorem perm_size_eq: "size xs = size ys \<Longrightarrow> size (permutations xs) = size (permutations ys)"
  by (simp add: size_permutations_fact)

theorem perm_prop10: "size (permutations (x#xs)) = size (permutations (xs)) * size (x#xs)"
  by (simp add: length_concat_insert_all)

lemma fold_choice_prop1: "permutations a = permutations b \<Longrightarrow> set (conc_elems a) = set (conc_elems b)"
  by (simp add: conc_elems_def)

lemma "size xs > 0\<Longrightarrow> size (conc_elems xs) > 0"
  apply (auto simp: conc_elems_def)
  by (metis member_rec(2) permutation_reflexive)


lemma fold_choice_prop2: "a \<in> set xs \<Longrightarrow> foldl (\<union>\<^sub>p) a xs = foldl (\<union>\<^sub>p) (Skip {}) xs"
proof (induction xs arbitrary: a)
  case Nil
  then show ?case
    by force
next
  case (Cons x xs)
  assume IH: "\<And>a. a \<in> set xs \<Longrightarrow> foldl (\<union>\<^sub>p) a xs = foldl (\<union>\<^sub>p) (Skip {}) xs"
  assume a1: "a \<in> set (x # xs)"
  have l1: "foldl (\<union>\<^sub>p) a (x # xs) = x \<union>\<^sub>p foldl (\<union>\<^sub>p) a (xs)"
    by (metis (no_types, lifting) choice_assoc_1 choice_commute foldl_Cons simp_2)
  have l2: "foldl (\<union>\<^sub>p) (Skip {}) (x # xs) = x \<union>\<^sub>p foldl (\<union>\<^sub>p) (Skip {}) (xs)"
    by (metis special_empty1 fold_choice_inv_1)
  then show "foldl (\<union>\<^sub>p) a (x # xs) = foldl (\<union>\<^sub>p) (Skip {}) (x # xs)"
  proof (cases "a = x")
    case True
    then show ?thesis
      by (metis Skip.skip_prop_9 choice_idem_4 special_empty1 empty_is_neutral foldl_Cons)
  next
    case False
    then show ?thesis
      using IH a1 local.l1 local.l2 by auto
  qed
qed

lemma fold_choice_prop3: "a \<in> set (conc_elems (xs)) \<Longrightarrow> foldl (\<union>\<^sub>p) (a) (conc_elems (xs)) = foldl (\<union>\<^sub>p) (Skip {}) (conc_elems (xs))"
  by (simp add: fold_choice_prop2)

theorem fold_choice_prop5: "foldl (\<union>\<^sub>p) x (x'#xs) = foldl (\<union>\<^sub>p) (Fail {}) (x#x'#xs)"
proof -
  have l1: "foldl (\<union>\<^sub>p) x (x'#xs) = Fail {} \<union>\<^sub>p foldl (\<union>\<^sub>p) x (x'#xs)"
    by (metis Skip.skip_prop_9 special_empty1 empty_is_neutral fold_choice_inv list.set_intros(1))
  have l2: "... = foldl (\<union>\<^sub>p) (Fail {} \<union>\<^sub>p x) (x'#xs)"
    by (metis choice_assoc_1 simp_2)
  have l3: "... = foldl (\<union>\<^sub>p) (Fail {}) (x#x'#xs)"
    by simp
  show ?thesis
    using local.l1 local.l2 local.l3 by presburger
qed



theorem atomic_prop2: "ys \<in> set (permutations xs) \<Longrightarrow> Concat ys \<preceq>\<^sub>p atomic_conc xs"
  by (simp add: atomic_conc_inv2 concat_prop_1)

theorem atomic_prop3: "atomic_conc [a,b] \<equiv>\<^sub>p a ; b \<union>\<^sub>p b ; a"
proof -
  obtain St where o1: "complete_state [a,b] = St" by simp
  have l0: "St = complete_state [a,b]" by (simp add: o1)
  have l1: "complete_state [b,a] = St"
    by (metis complete_state_union_1 o1 sup_commute)
  have l2: "S (a ; b \<union>\<^sub>p b ; a) = St"
    by (auto simp add: l1 l0 complete_state_def)
  have l6: "atomic_conc [a, b] \<equiv>\<^sub>p a;b \<union>\<^sub>p b;a"
    apply (auto simp: atomic_conc_def conc_elems_def)
    by (simp add: equals_equiv_relation_3)
  show ?thesis
    by (simp add: local.l6)
qed

theorem equiv_to_equal: "S a = S b \<Longrightarrow> post a = post b \<Longrightarrow> a \<equiv>\<^sub>p b \<Longrightarrow> a \<triangleq> b"
  by (auto simp: Definitions.equal_def equiv_def)

theorem atomic_prop4: "atomic_conc [a, b \<union>\<^sub>p c] \<equiv>\<^sub>p atomic_conc [a,b] \<union>\<^sub>p atomic_conc [a,c]"
proof -
  obtain St where o1: "St = complete_state [a,b,c]" by simp
  have l1: "complete_state [b \<union>\<^sub>p c, a] = St" using o1 by (auto simp: complete_state_def S_def Field_def choice_def composition_def Range_iff Domain_iff Un_def restr_post_def restrict_r_def)
  have l2: "complete_state [a, b \<union>\<^sub>p c] = St" using o1 by (auto simp: complete_state_def S_def Field_def choice_def composition_def Range_iff Domain_iff Un_def restr_post_def restrict_r_def)
  have l3: "S (a ; (b \<union>\<^sub>p c) \<union>\<^sub>p (b \<union>\<^sub>p c) ; a) = St" using o1 by (auto simp: complete_state_def)
  have l4: "Skip St ; ((b \<union>\<^sub>p c) ; a) \<equiv>\<^sub>p (b \<union>\<^sub>p c) ; a" using l3
    by (metis Skip.skip_prop_6 Skip.skip_prop_9 choice_state complete_state_subset local.l1 sup.bounded_iff)
  have l5: "(Fail {} \<union>\<^sub>p Skip St ; (a ; (b \<union>\<^sub>p c))) \<equiv>\<^sub>p a ; (b \<union>\<^sub>p c)"
    by (metis Definitions.equiv_def Skip.skip_prop_6 Un_upper1 choice_state fail_choice_l local.l3)
  have l6: "atomic_conc [a, b \<union>\<^sub>p c] \<equiv>\<^sub>p a;(b \<union>\<^sub>p c) \<union>\<^sub>p (b \<union>\<^sub>p c);a"
    apply (auto simp: atomic_conc_def conc_elems_def)
    by (simp add: equiv_is_reflexive)
  have l7: "atomic_conc [a,b] \<union>\<^sub>p atomic_conc [a,c] \<equiv>\<^sub>p (a ; b \<union>\<^sub>p b ; a) \<union>\<^sub>p (a ; c \<union>\<^sub>p c ; a)"
    using atomic_prop3 choice_equiv by blast
  have l8: "a;(b \<union>\<^sub>p c) \<equiv>\<^sub>p (a;b) \<union>\<^sub>p (a;c)" using compose_distrib1_3 by auto
  have l9: "(b \<union>\<^sub>p c);a \<equiv>\<^sub>p (b;a) \<union>\<^sub>p (c;a)" using compose_distrib2_3 by auto
  have l10: "a;(b \<union>\<^sub>p c) \<union>\<^sub>p (b \<union>\<^sub>p c);a \<equiv>\<^sub>p (a ; b \<union>\<^sub>p b ; a) \<union>\<^sub>p (a ; c \<union>\<^sub>p c ; a)"
    using l8 l9
    by (metis choice_assoc_1 choice_commute choice_equiv)
  show ?thesis
    by (meson equiv_is_symetric equiv_is_transitive local.l10 local.l6 local.l7)
qed

theorem atomic_prop5: "atomic_conc [a \<union>\<^sub>p b] = atomic_conc [a] \<union>\<^sub>p atomic_conc [b]"
  by (auto simp: atomic_conc_def conc_elems_def)

definition set_to_list :: "'a set \<Rightarrow> 'a list" where
  "set_to_list s = (SOME l. set l = s)"

lemma set_to_list_set: "finite xs \<Longrightarrow> set (set_to_list xs) = xs"
  by (metis (mono_tags, lifting) finite_distinct_list set_to_list_def some_eq_imp)

value "drop 3 [1::nat, 2,3,4,5,6,7]"

theorem subprogram_prop: "a \<triangleq> b \<Longrightarrow> b \<preceq>\<^sub>p a \<and> a \<preceq>\<^sub>p b"
  by (auto simp: subprogram_def extends_def Definitions.equal_def weakens_def strengthens_def restrict_r_def S_def Field_def)

theorem atomic_prop6: "atomic_conc [a \<union>\<^sub>p b, c] \<equiv>\<^sub>p atomic_conc [a,c] \<union>\<^sub>p atomic_conc [b,c]"
proof -
  obtain St where o1: "St = complete_state [a,b,c]" by simp
  have l1: "complete_state [a \<union>\<^sub>p b, c] = St" using o1 by (auto simp: complete_state_def S_def Field_def choice_def composition_def Range_iff Domain_iff Un_def restr_post_def restrict_r_def)
  have l2: "complete_state [c, a \<union>\<^sub>p b] = St" using o1 by (auto simp: complete_state_def S_def Field_def choice_def composition_def Range_iff Domain_iff Un_def restr_post_def restrict_r_def)
  have l3: "S ((a \<union>\<^sub>p b) ; c \<union>\<^sub>p c ; (a \<union>\<^sub>p b)) = St" using o1 by (auto simp: complete_state_def)
  have l4: "Skip St ; ((a \<union>\<^sub>p b) ; c) \<equiv>\<^sub>p (a \<union>\<^sub>p b) ; c" using l3
    by (metis Skip.skip_prop_6 Skip.skip_prop_9 choice_state complete_state_subset local.l1 sup.bounded_iff)
  have l5: "(Fail {} \<union>\<^sub>p Skip St ; (c ; (a \<union>\<^sub>p b))) \<equiv>\<^sub>p c ; (a \<union>\<^sub>p b)"
    by (metis Skip.skip_prop_6 Skip.skip_prop_9 Un_subset_iff choice_state complete_state_subset equiv_is_transitive fail_choice_l local.l3 o1)
  have l6: "atomic_conc [a \<union>\<^sub>p b, c] \<equiv>\<^sub>p (a \<union>\<^sub>p b) ; c \<union>\<^sub>p c ; (a \<union>\<^sub>p b)"
    apply (auto simp: atomic_conc_def conc_elems_def)
    by (simp add: equiv_is_reflexive)
  have l7: "atomic_conc [a,c] \<union>\<^sub>p atomic_conc [b,c] \<equiv>\<^sub>p (a ; c \<union>\<^sub>p c ; a) \<union>\<^sub>p (b ; c \<union>\<^sub>p c ; b)"
    using atomic_prop3 choice_equiv by blast
  have l8: "(a \<union>\<^sub>p b) ; c \<equiv>\<^sub>p (a;c) \<union>\<^sub>p (b;c)" using compose_distrib1_3
    by (simp add: compose_distrib2_3) 
  have l9: "c ; (a \<union>\<^sub>p b) \<equiv>\<^sub>p (c;a) \<union>\<^sub>p (c;b)" using compose_distrib2_3
    by (simp add: compose_distrib1_3)
  have l10: "(a \<union>\<^sub>p b) ; c \<union>\<^sub>p c ; (a \<union>\<^sub>p b) \<equiv>\<^sub>p ((a;c) \<union>\<^sub>p (b;c)) \<union>\<^sub>p ((c;a) \<union>\<^sub>p (c;b))"
    using choice_equiv local.l8 local.l9 by blast
  show ?thesis
    by (smt (verit, ccfv_SIG) choice_assoc_1 choice_commute equiv_is_symetric equiv_is_transitive local.l10 local.l6 local.l7)
qed

theorem commute_compose: "commute_programs3 a b \<Longrightarrow> atomic_conc [a,b] \<equiv>\<^sub>p a ; b"
proof -
  assume a1: "commute_programs3 a b"
  have l1: "atomic_conc [a,b] \<equiv>\<^sub>p a ; b \<union>\<^sub>p b ; a"
    by (simp add: atomic_prop3)
  moreover have "... \<equiv>\<^sub>p a ; b \<union>\<^sub>p a ; b" using a1 apply (simp add: commute_programs3_def)
    by (metis equals_equiv_relation_3 equiv_is_symetric choice_equiv)
  moreover have "... \<equiv>\<^sub>p a ; b"
    by simp
  ultimately show ?thesis
    using equiv_is_transitive by blast
qed


end