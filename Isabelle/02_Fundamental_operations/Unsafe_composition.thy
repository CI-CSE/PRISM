theory Unsafe_composition
  imports "../T_01_Core"
begin
section \<open>Unsafe composition for top\<close>

theorem unsafe_composition_state [simp]: "S (p\<^sub>1 ;\<^sub>p p\<^sub>2) = S p\<^sub>1 \<union> S p\<^sub>2"
  by (auto simp: unsafe_composition_def S_def restr_post_def restrict_r_def Field_def)

theorem unsafe_compose_assoc [simp]: "(p\<^sub>1 ;\<^sub>p p\<^sub>2) ;\<^sub>p p\<^sub>3 = p\<^sub>1 ;\<^sub>p (p\<^sub>2 ;\<^sub>p p\<^sub>3)" \<comment> \<open>T8\<close>
proof -
  have compose_assoc_S: "S (p\<^sub>1 ;\<^sub>p (p\<^sub>2 ;\<^sub>p p\<^sub>3)) = S ((p\<^sub>1 ;\<^sub>p p\<^sub>2) ;\<^sub>p p\<^sub>3)"
    by (simp add: sup_assoc)

  have compose_assoc_pre: "Pre (p\<^sub>1 ;\<^sub>p (p\<^sub>2 ;\<^sub>p p\<^sub>3)) = Pre ((p\<^sub>1 ;\<^sub>p p\<^sub>2) ;\<^sub>p p\<^sub>3)"
    by (simp add: unsafe_composition_def)

  have compose_assoc_post: "post (p\<^sub>1 ;\<^sub>p (p\<^sub>2 ;\<^sub>p p\<^sub>3)) = post ((p\<^sub>1 ;\<^sub>p p\<^sub>2) ;\<^sub>p p\<^sub>3)"
    proof -
      have compose_assoc_post_1: "post (p\<^sub>1 ;\<^sub>p (p\<^sub>2 ;\<^sub>p p\<^sub>3)) = {(a,d). \<exists>b c. (a,b) \<in> post p\<^sub>1 \<and> b \<in> Pre p\<^sub>2 \<and> (b,c) \<in> post p\<^sub>2 \<and> c \<in> Pre p\<^sub>3 \<and> (c,d) \<in> post p\<^sub>3}"
        apply (auto simp: unsafe_composition_def corestrict_r_def restr_post_def restrict_r_def)
        apply (auto)
        by fastforce
      have compose_assoc_post_2: "post ((p\<^sub>1 ;\<^sub>p p\<^sub>2) ;\<^sub>p p\<^sub>3) = {(a,d). \<exists>b c. (a,b) \<in> post p\<^sub>1 \<and> b \<in> Pre p\<^sub>2 \<and> (b,c) \<in> post p\<^sub>2 \<and> c \<in> Pre p\<^sub>3 \<and> (c,d) \<in> post p\<^sub>3}"
        apply (auto simp: unsafe_composition_def corestrict_r_def restr_post_def restrict_r_def)
        apply (auto)
        by fastforce
      show ?thesis
        by (auto simp: compose_assoc_post_1 compose_assoc_post_2)
    qed

  show ?thesis
    by (metis compose_assoc_S compose_assoc_post select_convs(2) select_convs(3) unsafe_composition_def unsafe_composition_state)
qed

theorem unsafe_compose_assoc_2 [simp]: "(p\<^sub>1 ;\<^sub>p p\<^sub>2) ;\<^sub>p p\<^sub>3 \<triangleq> p\<^sub>1 ;\<^sub>p (p\<^sub>2 ;\<^sub>p p\<^sub>3)" \<comment> \<open>T8\<close>
  by (simp add: equals_equiv_relation_1)

theorem unsafe_compose_assoc_3 [simp]: "(p\<^sub>1 ;\<^sub>p p\<^sub>2) ;\<^sub>p p\<^sub>3 \<equiv>\<^sub>p p\<^sub>1 ;\<^sub>p (p\<^sub>2 ;\<^sub>p p\<^sub>3)" \<comment> \<open>T8\<close>
  by (simp add: equals_equiv_relation_3)

theorem equivalence_is_maintained_by_unsafe_composition: "f⇩1 ≡⇩p p⇩1 ⟹ f⇩2 ≡⇩p p⇩2 ⟹ f⇩1 ;⇩p f⇩2 ≡⇩p p⇩1 ;⇩p p⇩2" ― ‹NEW›
  apply (auto simp: equiv_def restr_post_def restrict_r_def unsafe_composition_def corestrict_r_def)
  using mem_Collect_eq relcomp.relcompI snd_conv apply fastforce
  using mem_Collect_eq relcomp.relcompI snd_conv by fastforce

theorem equality_is_maintained_by_unsafe_composition: "f⇩1 ≜ p⇩1 ⟹ f⇩2 ≜ p⇩2 ⟹ f⇩1 ;⇩p f⇩2 ≜ p⇩1 ;⇩p p⇩2" ― ‹NEW›
  by (auto simp: equal_def restr_post_def unsafe_composition_def)

theorem unsafe_compose_feasible_1: "is_feasible (p⇩1 ;⇩p p⇩2) ⟹ is_feasible p⇩1"
  by (auto simp: unsafe_composition_def is_feasible_def corestrict_r_def)

theorem unsafe_compose_feasible_2: "all_feasible [p⇩1, p⇩2] ⟹ Range_p p⇩1 ⊆ Pre p⇩2 ⟹ is_feasible (p⇩1 ;⇩p p⇩2)"
proof -
  assume a1: "all_feasible [p⇩1, p⇩2]"
  assume a2: "Range_p p⇩1 ⊆ Pre p⇩2"
  have l1: "Pre (p⇩1 ;⇩p p⇩2) = {a. ∃c. (a,c) ∈ post p⇩1 ∧ a ∈ Pre p⇩1 ∧ c ∈ Pre p⇩2}"
    using a1 a2 apply (auto simp: unsafe_composition_def is_feasible_def Range_p_def restrict_r_def)
    proof -
      fix x :: 'a
      assume a1_1: "Range {r ∈ post p⇩1. fst r ∈ Pre p⇩1} ⊆ Pre p⇩2"
      assume a1_2: "Pre p⇩1 ⊆ Domain (post p⇩1)"
      assume a1_3: "x ∈ Pre p⇩1"
      then have "x ∈ Domain (post p⇩1)"
        using a1_2 by force
      then have l1_1: "x ∈ Domain {p ∈ post p⇩1. fst p ∈ Pre p⇩1}"
        using a1_3 by fastforce
      have "Range {p ∈ post p⇩1. fst p ∈ Pre p⇩1} ⊆ Pre p⇩2"
        using a1_1 by (smt (z3))
      then show "∃a. (x, a) ∈ post p⇩1 ∧ a ∈ Pre p⇩2"
        using l1_1 by blast
    qed
  have l2: "Domain (post (p⇩1 ;⇩p p⇩2)) = {a. ∃c. (a,c) ∈ post p⇩1 ∧ c ∈ Pre p⇩2}"
    proof -
      have l2_1: "post (p⇩1 ;⇩p p⇩2) = {(a,b). ∃c. (a,c) ∈ post p⇩1 ∧ (c,b) ∈ post p⇩2 ∧ c ∈ Pre p⇩2}"
        using a1 a2 by (auto simp: Range_p_def is_feasible_def unsafe_composition_def restr_post_def restrict_r_def)
      then have l2_2: "Domain (post (p⇩1 ;⇩p p⇩2)) = {a. ∃b c. (a,c) ∈ post p⇩1 ∧ (c,b) ∈ post p⇩2 ∧ c ∈ Pre p⇩2}"
        using a1 a2 by (auto simp: l2_1)
      then show "Domain (post (p⇩1 ;⇩p p⇩2)) = {a. ∃c. (a,c) ∈ post p⇩1 ∧ c ∈ Pre p⇩2}"
        apply (auto simp: l2_2)
        using a1 a2 l2_1 apply auto[1]
        using a1 a2 apply (auto simp: is_feasible_def)
        by (smt (verit, del_insts) Domain.cases a1 l2_2 mem_Collect_eq subsetD)
    qed
  have l3: "{a. ∃c. (a,c) ∈ post p⇩1 ∧ a ∈ Pre p⇩1 ∧ c ∈ Pre p⇩2} ⊆ {a. ∃c. (a,c) ∈ post p⇩1 ∧ c ∈ Pre p⇩2}"
    by auto
  have l4: "Pre (p⇩1 ;⇩p p⇩2) ⊆  Domain (post (p⇩1 ;⇩p p⇩2))"
    using a1 a2 l1 l2 by auto
  show "is_feasible (p⇩1 ;⇩p p⇩2)"
    by (simp add: is_feasible_def l4)
qed

end