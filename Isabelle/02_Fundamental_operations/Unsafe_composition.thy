theory Unsafe_composition
  imports "../T_01_Core"
begin
section \<open>Unsafe composition for top\<close>

theorem unsafe_composition_state [simp]: "S (p\<^sub>1 ;\<^sub>p p\<^sub>2) = S p\<^sub>1 \<union> S p\<^sub>2"
  by (auto simp: unsafe_composition_def S_def restr_post_def restrict_r_def Field_def)

theorem unsafe_compose_assoc [simp]: "(p\<^sub>1 ;\<^sub>p p\<^sub>2) ;\<^sub>p p\<^sub>3 = p\<^sub>1 ;\<^sub>p (p\<^sub>2 ;\<^sub>p p\<^sub>3)" \<comment> \<open>T8\<close>
proof -
  have compose_assoc_S: "State (p\<^sub>1 ;\<^sub>p (p\<^sub>2 ;\<^sub>p p\<^sub>3)) = State ((p\<^sub>1 ;\<^sub>p p\<^sub>2) ;\<^sub>p p\<^sub>3)"
    by (metis Program.select_convs(1) sup_assoc unsafe_composition_def unsafe_composition_state)

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

  from compose_assoc_S compose_assoc_pre compose_assoc_post show ?thesis
    by fastforce
qed

theorem unsafe_compose_assoc_2 [simp]: "(p\<^sub>1 ;\<^sub>p p\<^sub>2) ;\<^sub>p p\<^sub>3 \<triangleq> p\<^sub>1 ;\<^sub>p (p\<^sub>2 ;\<^sub>p p\<^sub>3)" \<comment> \<open>T8\<close>
  by (simp add: equals_equiv_relation_1)

theorem unsafe_compose_assoc_3 [simp]: "(p\<^sub>1 ;\<^sub>p p\<^sub>2) ;\<^sub>p p\<^sub>3 \<equiv>\<^sub>p p\<^sub>1 ;\<^sub>p (p\<^sub>2 ;\<^sub>p p\<^sub>3)" \<comment> \<open>T8\<close>
  by (simp add: equals_equiv_relation_3)

theorem equivalence_is_maintained_by_unsafe_composition: "f\<^sub>1 \<equiv>\<^sub>p p\<^sub>1 \<Longrightarrow> f\<^sub>2 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> f\<^sub>1 ;\<^sub>p f\<^sub>2 \<equiv>\<^sub>p p\<^sub>1 ;\<^sub>p p\<^sub>2" \<comment> \<open>NEW\<close>
  apply (auto simp: equiv_def restr_post_def restrict_r_def unsafe_composition_def corestrict_r_def)
  using mem_Collect_eq relcomp.relcompI snd_conv apply fastforce
  using mem_Collect_eq relcomp.relcompI snd_conv by fastforce

theorem equality_is_maintained_by_unsafe_composition: "f\<^sub>1 \<triangleq> p\<^sub>1 \<Longrightarrow> f\<^sub>2 \<triangleq> p\<^sub>2 \<Longrightarrow> f\<^sub>1 ;\<^sub>p f\<^sub>2 \<triangleq> p\<^sub>1 ;\<^sub>p p\<^sub>2" \<comment> \<open>NEW\<close>
  by (auto simp: equal_def restr_post_def unsafe_composition_def)

theorem unsafe_compose_feasible_1: "is_feasible (p\<^sub>1 ;\<^sub>p p\<^sub>2) \<Longrightarrow> is_feasible p\<^sub>1"
  by (auto simp: unsafe_composition_def is_feasible_def corestrict_r_def)

theorem unsafe_compose_feasible_2: "all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> Range_p p\<^sub>1 \<subseteq> Pre p\<^sub>2 \<Longrightarrow> is_feasible (p\<^sub>1 ;\<^sub>p p\<^sub>2)"
proof -
  assume a1: "all_feasible [p\<^sub>1, p\<^sub>2]"
  assume a2: "Range_p p\<^sub>1 \<subseteq> Pre p\<^sub>2"
  have l1: "Pre (p\<^sub>1 ;\<^sub>p p\<^sub>2) = {a. \<exists>c. (a,c) \<in> post p\<^sub>1 \<and> a \<in> Pre p\<^sub>1 \<and> c \<in> Pre p\<^sub>2}"
    using a1 a2 apply (auto simp: unsafe_composition_def is_feasible_def Range_p_def restrict_r_def)
    proof -
      fix x :: 'a
      assume a1_1: "Range {r \<in> post p\<^sub>1. fst r \<in> Pre p\<^sub>1} \<subseteq> Pre p\<^sub>2"
      assume a1_2: "Pre p\<^sub>1 \<subseteq> Domain (post p\<^sub>1)"
      assume a1_3: "x \<in> Pre p\<^sub>1"
      then have "x \<in> Domain (post p\<^sub>1)"
        using a1_2 by force
      then have l1_1: "x \<in> Domain {p \<in> post p\<^sub>1. fst p \<in> Pre p\<^sub>1}"
        using a1_3 by fastforce
      have "Range {p \<in> post p\<^sub>1. fst p \<in> Pre p\<^sub>1} \<subseteq> Pre p\<^sub>2"
        using a1_1 by auto
      then show "\<exists>a. (x, a) \<in> post p\<^sub>1 \<and> a \<in> Pre p\<^sub>2"
        using l1_1 by blast
    qed
  have l2: "Domain (post (p\<^sub>1 ;\<^sub>p p\<^sub>2)) = {a. \<exists>c. (a,c) \<in> post p\<^sub>1 \<and> c \<in> Pre p\<^sub>2}"
    proof -
      have l2_1: "post (p\<^sub>1 ;\<^sub>p p\<^sub>2) = {(a,b). \<exists>c. (a,c) \<in> post p\<^sub>1 \<and> (c,b) \<in> post p\<^sub>2 \<and> c \<in> Pre p\<^sub>2}"
        using a1 a2 by (auto simp: Range_p_def is_feasible_def unsafe_composition_def restr_post_def restrict_r_def)
      then have l2_2: "Domain (post (p\<^sub>1 ;\<^sub>p p\<^sub>2)) = {a. \<exists>b c. (a,c) \<in> post p\<^sub>1 \<and> (c,b) \<in> post p\<^sub>2 \<and> c \<in> Pre p\<^sub>2}"
        using a1 a2 by (auto simp: l2_1)
      then show "Domain (post (p\<^sub>1 ;\<^sub>p p\<^sub>2)) = {a. \<exists>c. (a,c) \<in> post p\<^sub>1 \<and> c \<in> Pre p\<^sub>2}"
        apply (auto simp: l2_2)
        using a1 a2 l2_1 apply auto[1]
        using a1 a2 apply (auto simp: is_feasible_def)
        by (meson Domain_iff subsetD)
    qed
  have l3: "{a. \<exists>c. (a,c) \<in> post p\<^sub>1 \<and> a \<in> Pre p\<^sub>1 \<and> c \<in> Pre p\<^sub>2} \<subseteq> {a. \<exists>c. (a,c) \<in> post p\<^sub>1 \<and> c \<in> Pre p\<^sub>2}"
    by auto
  have l4: "Pre (p\<^sub>1 ;\<^sub>p p\<^sub>2) \<subseteq>  Domain (post (p\<^sub>1 ;\<^sub>p p\<^sub>2))"
    using a1 a2 l1 l2 by auto
  show "is_feasible (p\<^sub>1 ;\<^sub>p p\<^sub>2)"
    by (simp add: is_feasible_def l4)
qed

end