theory Prime
  imports 
HOL.Finite_Set
"../T_01_Core"
"Choice"
begin

theorem finite_Field_implies_finite_relation:
  assumes "finite (Field r)"
  shows "finite r"
proof -
  have "r \<subseteq> Field r \<times> Field r"
    by (auto simp add: Field_def subset_iff)
  moreover have "finite (Field r \<times> Field r)"
    using assms by (simp add: finite_cartesian_product)
  ultimately show "finite r"
    by (rule finite_subset)
qed

theorem "finite (S p) \<Longrightarrow> finite (Pre p)"
  apply (induction "S p" rule: finite_induct)
   apply (auto simp: S_def)
  by (metis finite_Un finite_insert)

theorem finite_S_implies_finite_post:
  assumes "finite (S p)"
  shows "finite (post p)"
proof -
  have "S p = State p \<union> Pre p \<union> Field (post p)"
    by (simp add: S_def)
  
  then have "finite (State p \<union> Pre p \<union> Field (post p))"
    using assms by simp
  
  then have "finite (Field (post p))"
    by (simp add: finite_UnionD)
  
  then show "finite (post p)"
    by (simp add: finite_Field_implies_finite_relation)
qed

theorem post_cardinality_equals_P_cardinality:
  assumes "P = {\<lparr>State={a,b}, Pre={a}, post={(a,b)}\<rparr> | a b. (a,b) \<in> (post p)}"
  shows "card (post p) = card P"
proof -
  have bijection: "\<exists>f. bij_betw f (post p) P"
  proof (rule exI, rule bij_betwI')
    let ?f = "\<lambda>(a,b). \<lparr>State={a,b}, Pre={a}, post={(a,b)}\<rparr>"
    show "\<And>x y. x \<in> post p \<Longrightarrow> y \<in> post p \<Longrightarrow> (?f x = ?f y) = (x = y)"
      by fastforce
    show "\<And>x. x \<in> post p \<Longrightarrow> ?f x \<in> P"
      apply auto
      by (simp add: assms)
    show "\<And>y. y \<in> P \<Longrightarrow> \<exists>x\<in>post p. y = ?f x"
      by (smt (verit) assms case_prod_conv mem_Collect_eq)
  qed

  from bijection have "bij_betw (\<lambda>(a,b). \<lparr>State={a,b}, Pre={a}, post={(a,b)}\<rparr>) (post p) P"
    apply auto apply (rule bij_betwI')
    using Program.select_convs(3) case_prod_conv empty_iff insert_iff mem_case_prodE mem_case_prodI2 apply auto[1]
    using assms apply force
    by (smt (verit) assms case_prod_conv mem_Collect_eq)

  thus "card (post p) = card P"
    by (rule bij_betw_same_card)
qed

theorem same_card_and_finite_impl_finite:
  assumes "card a = card b"
    and "finite a"
    and "card a > 0"
  shows "finite b"
  using assms(1) assms(3) card_ge_0_finite by auto

theorem fst_in_state: "is_feasible p \<Longrightarrow> is_minimal p \<Longrightarrow> P = {\<lparr>State={a,b}, Pre={a}, post={(a,b)}\<rparr> | a b. (a,b) \<in> post p} \<Longrightarrow> r \<in> post p \<Longrightarrow> fst r \<in> State p"
  apply (auto simp: is_feasible_def is_minimal_def is_valid_def S_def Field_def Un_def Range_iff Domain_iff subset_iff)
  by (metis (no_types, lifting) mem_Collect_eq prod.collapse)

theorem snd_is_state: "is_feasible p \<Longrightarrow> is_minimal p \<Longrightarrow> P = {\<lparr>State={a,b}, Pre={a}, post={(a,b)}\<rparr> | a b. (a,b) \<in> post p} \<Longrightarrow> r \<in> post p \<Longrightarrow> snd r \<in> State p"
  apply (auto simp: is_feasible_def is_minimal_def is_valid_def S_def Field_def Un_def Range_iff Domain_iff subset_iff)
  by (metis (no_types, lifting) mem_Collect_eq prod.collapse)

theorem "is_feasible p \<Longrightarrow> is_minimal p \<Longrightarrow> P = {\<lparr>State={a,b}, Pre={a}, post={(a,b)}\<rparr> | a b. (a,b) \<in> post p} \<Longrightarrow> s \<in> State p \<Longrightarrow> \<exists>r \<in> post p. fst r = s \<or> snd r = s"
  using mem_Collect_eq prod.collapse apply (auto simp: is_feasible_def is_minimal_def is_valid_def S_def Field_def Un_def Range_iff Domain_iff subset_iff)
  by (meson split_pairs)

lemma fold_insert [simp]:
  assumes "finite A" and "x \<notin> A"
  shows "fold f z (insert x A) = f x (fold f z A)"

theorem choice_set_decomp_1: "finite F \<Longrightarrow> \<Union>\<^sub>P (insert x F) = \<Union>\<^sub>P F \<union>\<^sub>p x"
proof -
  assume a1: "finite F"
  have "\<Union>\<^sub>P (insert x F) = Finite_Set.fold (\<union>\<^sub>p) (Fail {}) (insert x F)"
    by (simp add: Choice_set_def)

  also have "... = (\<union>\<^sub>p) x (Finite_Set.fold (\<union>\<^sub>p) (Fail {}) F)" using a1
  proof (cases "x \<in> F")
    case True
    have l1: "insert x F = F"
      by (simp add: True insert_absorb)
    have l2: "Finite_Set.fold (\<union>\<^sub>p) (Fail {}) (insert x F) = Finite_Set.fold (\<union>\<^sub>p) (Fail {}) (F)"
      by (simp add: local.l1)
    have l3: "... = x \<union>\<^sub>p Finite_Set.fold (\<union>\<^sub>p) (Fail {}) F" using choice_idem_4
    then show ?thesis sorry
  next
    case False
    then show ?thesis using Finite_Set.fold_insert sorry
  qed

  also have "... = (\<union>\<^sub>p) x (\<Union>\<^sub>P F)"
    by (simp add: Choice_set_def)

  also have "... = \<Union>\<^sub>P F \<union>\<^sub>p x"
    by (simp add: choice_commute)

  finally show ?thesis .
qed

theorem choice_set_decomp_1: "\<Union>\<^sub>P (insert x F) = \<Union>\<^sub>P F \<union>\<^sub>p x"
proof -
  have state: "State (\<Union>\<^sub>P (insert x F)) = State (\<Union>\<^sub>P F \<union>\<^sub>p x)" sorry
  have pre: "Pre (\<Union>\<^sub>P (insert x F)) = Pre (\<Union>\<^sub>P F \<union>\<^sub>p x)" using choice_commute apply (auto simp: Choice_set_def) sorry
  have post: "post (\<Union>\<^sub>P (insert x F)) = post (\<Union>\<^sub>P F \<union>\<^sub>p x)" sorry
  show ?thesis using state pre post by simp
qed
  apply (auto simp: Choice_set_def choice_def Fail_def restr_post_def restrict_r_def S_def)

theorem choice_set_equality:
  assumes "finite (S p)"
    and "is_feasible p"
    and "is_minimal p"
    and "P = {\<lparr>State={a,b}, Pre={a}, post={(a,b)}\<rparr> | a b. (a,b) \<in> post p}"
    and "p\<^sub>i \<in> P"
  shows "\<Union>\<^sub>P P = p"
proof -
  have l1: "finite (post p)"
    by (simp add: assms(1) finite_S_implies_finite_post)
  have l2: "post p = {} \<Longrightarrow> P = {}"
    by (simp add: assms(4))
  have l3: "post p \<noteq> {} \<Longrightarrow> P \<noteq> {}"
    using assms(5) by auto
  have l4: "(card P) = 0 \<Longrightarrow> p = Fail {}" apply (auto simp: Fail_def assms(4))
    by (metis assms(5) card_0_eq empty_iff local.l1 local.l2 post_cardinality_equals_P_cardinality)
  have l5: "p = Fail {} \<Longrightarrow> finite P" by (auto simp: Fail_def assms(4))
  have l6: "finite P \<or> card P = 0"
    by (metis card.infinite)
  have finite_P: "finite P"
    using l4 l5 l6 by linarith

  have l7: "\<forall>s \<in> State p. \<exists>r \<in> post p. fst r = s \<or> snd r = s" using assms(2,3,4) 
    apply (simp add: is_feasible_def is_minimal_def is_valid_def Domain_iff subset_iff S_def Field_def Un_def Range_iff)
    by (meson split_pairs)
  have l8: "\<forall>s \<in> State p. \<exists>p\<^sub>i \<in>P. s \<in> State p\<^sub>i" using assms(2,3,4) apply (auto simp: is_feasible_def is_minimal_def)
    by (metis (no_types, opaque_lifting) Field_iff Program.select_convs(1) insert_iff)

  have "\<And>s. p\<^sub>i \<in> P \<Longrightarrow> s \<in> State p\<^sub>i \<Longrightarrow> s \<in> State (\<Union>\<^sub>P P)"
    using finite_P proof (induction P rule: finite_induct)
    case empty
    then show ?case apply (auto simp: Choice_set_def Fail_def) done
  next
    case (insert x F)
    assume ass: "finite F" and 
      "x \<notin> F" and 
      "\<And>s. p\<^sub>i \<in> F \<Longrightarrow> s \<in> State p\<^sub>i \<Longrightarrow> s \<in> State (\<Union>\<^sub>P F)" and
      "p\<^sub>i \<in> insert x F" and
      "s \<in> State p\<^sub>i"
    have decomp: "\<Union>\<^sub>P (insert x F) = \<Union>\<^sub>P F \<union>\<^sub>p x" apply (auto simp: Choice_set_def)
    then show "s \<in> State (\<Union>\<^sub>P (insert x F))"
    proof (cases "p\<^sub>i = x")
      case True
      then show ?thesis sorry
    next
      case False
      then show ?thesis sorry
    qed
  qed
     [1]
    apply (auto simp: Choice_set_def Fail_def) [1]

  have state_eq: "State (\<Union>\<^sub>P P) = State p"
    unfolding Choice_set_def choice_def S_def
    using assms(2,3,4) apply (auto simp: is_feasible_def is_minimal_def) sorry

  have pre_eq: "Pre (\<Union>\<^sub>P P) = Pre p"
    unfolding Choice_set_def choice_def
    using assms(4) by auto

  have post_eq: "post (\<Union>\<^sub>P P) = post p"
  proof (rule set_eqI)
    fix x
    show "(x \<in> post (\<Union>\<^sub>P P)) = (x \<in> post p)"
    proof
      assume "x \<in> post (\<Union>\<^sub>P P)"
      then obtain a b where "x = (a,b)" and "(a,b) \<in> post p"
        unfolding Choice_set_def choice_def restr_post_def restrict_r_def
        using assms(4) by auto
      thus "x \<in> post p" by simp
    next
      assume "x \<in> post p"
      then obtain a b where "x = (a,b)" by auto
      hence "\<lparr>State={a,b}, Pre={a}, post={(a,b)}\<rparr> \<in> P"
        using assms(4) by auto
      thus "x \<in> post (\<Union>\<^sub>P P)"
        unfolding Choice_set_def choice_def restr_post_def restrict_r_def
        by (simp add: finite_P)
    qed
  qed

  from state_eq pre_eq post_eq show ?thesis
    by (simp add: program_equality)
qed

theorem
  assumes "finite (S p)" and 
    "is_feasible p" and 
    "is_minimal p" and 
    "P = {\<lparr>State={a,b},Pre={a},post={(a,b)}\<rparr> |a b . (a,b) \<in> (post p)}" and
    "p\<^sub>i \<in> P"
  shows "is_prime p\<^sub>i \<and> p\<^sub>i \<preceq>\<^sub>p p \<and> \<Union>\<^sub>P P = p"
proof -
  have l1: "is_prime p\<^sub>i" using assms by (auto simp: is_prime_def)
  have l2: "p\<^sub>i \<preceq>\<^sub>p p" using assms
    apply (auto simp: subprogram_def)
    apply (auto simp: extends_def S_def Field_def) [1]
    apply (auto simp: weakens_def is_feasible_def subset_iff Domain_iff is_minimal_def) [1]
    apply (auto simp: strengthens_def is_feasible_def subset_iff Domain_iff is_minimal_def restrict_r_def) [1]
    done
  have l3: "finite (post p)" using assms(1)
    by (simp add: finite_S_implies_finite_post)
  have l4: "card (post p) = card P" using l3 assms(1) assms(4)
    using post_cardinality_equals_P_cardinality by force
  have l5: "finite P" using assms(1) assms (4) l4
    using card.infinite l3 by force
  have l6: "State (\<Union>\<^sub>P P) = State p"
    using l5 assms(4) apply (induction P rule: finite_induct)
    using assms(4) assms(5) apply auto[1]
  

theorem "finite (S p) \<Longrightarrow> is_feasible p \<Longrightarrow> is_minimal p \<Longrightarrow> \<exists> P. p\<^sub>i \<in> P \<longrightarrow> is_prime p\<^sub>i \<and> p\<^sub>i \<preceq>\<^sub>p p \<and> \<Union>\<^sub>P P = p"
proof -
  assume a1: "finite (S p)"
  assume a2: "is_feasible p"
  assume a3: "is_minimal p"
  obtain P where o1: "P = {\<lparr>State={a,b},Pre={a},post={(a,b)}\<rparr> |a b . (a,b) \<in> (post p)}" by auto
  have l1: "p\<^sub>i \<in> P \<Longrightarrow> is_prime p\<^sub>i" using o1 by (auto simp: is_prime_def)
  have l2: "p\<^sub>i \<in> P \<Longrightarrow> p\<^sub>i \<preceq>\<^sub>p p" using o1
    apply (auto simp: subprogram_def)
    apply (auto simp: extends_def S_def Field_def) [1]
    using a2 a3 apply (auto simp: weakens_def is_feasible_def subset_iff Domain_iff is_minimal_def) [1]
    using a2 a3 apply (auto simp: strengthens_def is_feasible_def subset_iff Domain_iff is_minimal_def restrict_r_def) [1]
    done
  have l3: "\<Union>\<^sub>P P = p"
qed

end