theory Unsafe_composition2
  imports "../T_01_Core"
begin
section \<open>Unsafe composition2 for top\<close>

theorem unsafe_composition_state [simp]: "S (p\<^sub>1 ;\<^sup>p p\<^sub>2) = S p\<^sub>1 \<union> S p\<^sub>2"
  by (auto simp: unsafe_composition2_def S_def restr_post_def restrict_r_def Field_def)

lemma "Pre (p\<^sub>1 ;\<^sup>p (p\<^sub>2 ;\<^sup>p p\<^sub>3)) \<subseteq> Pre ((p\<^sub>1 ;\<^sup>p p\<^sub>2) ;\<^sup>p p\<^sub>3)"
  apply (simp add: unsafe_composition2_def corestrict_r_def relcomp_unfold Domain_iff Int_def)
  by auto

definition P1 :: "nat Program" where "P1 =\<lparr>State={1,2}, Pre={1,2}, post={(1,1), (1,2), (2,1), (2,2)}\<rparr>"
definition P2 :: "nat Program" where "P2 =\<lparr>State={1,2}, Pre={1}, post={(1,2), (2,1)}\<rparr>"
definition P3 :: "nat Program" where "P3 =\<lparr>State={1,2}, Pre={1}, post={(1,1)}\<rparr>"

value "P1 ;\<^sup>p P2"
value "P2 ;\<^sup>p P3"
value "P1 ;\<^sup>p (P2 ;\<^sup>p P3)"
value "(P1 ;\<^sup>p P2) ;\<^sup>p P3"

lemma "Pre ((p ;\<^sup>p q) ;\<^sup>p r) = Pre (p ;\<^sup>p (q ;\<^sup>p r))"
  nitpick
  oops

theorem unsafe_compose_assoc_3 [simp]: "(p\<^sub>1 ;\<^sup>p p\<^sub>2) ;\<^sup>p p\<^sub>3 \<equiv>\<^sub>p p\<^sub>1 ;\<^sup>p (p\<^sub>2 ;\<^sup>p p\<^sub>3)" \<comment> \<open>T8\<close>
  nitpick
  oops

theorem equivalence_is_maintained_by_unsafe_composition: "f\<^sub>1 \<equiv>\<^sub>p p\<^sub>1 \<Longrightarrow> f\<^sub>2 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> f\<^sub>1 ;\<^sup>p f\<^sub>2 \<equiv>\<^sub>p p\<^sub>1 ;\<^sup>p p\<^sub>2" \<comment> \<open>NEW\<close>
  nitpick
  oops

theorem unsafe_compose_feasible_1: "is_feasible (p\<^sub>1 ;\<^sup>p p\<^sub>2) \<Longrightarrow> is_feasible p\<^sub>1"
  nitpick
  oops

theorem unsafe_compose_feasible_2: "all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> Range_p p\<^sub>1 \<subseteq> Pre p\<^sub>2 \<Longrightarrow> is_feasible (p\<^sub>1 ;\<^sup>p p\<^sub>2)"
proof -
  assume a1: "all_feasible [p\<^sub>1, p\<^sub>2]"
  assume a2: "Range_p p\<^sub>1 \<subseteq> Pre p\<^sub>2"
  have l1: "Pre (p\<^sub>1 ;\<^sup>p p\<^sub>2) = {a. \<exists>c. (a,c) \<in> post p\<^sub>1 \<and> a \<in> Pre p\<^sub>1 \<and> c \<in> Pre p\<^sub>2}"
    using a1 a2 apply (auto simp: unsafe_composition2_def is_feasible_def Range_p_def restrict_r_def)
    apply (meson Domain_iff a2 range_p_explicit_2 subsetD)
    by (auto simp: corestrict_r_def)
  have l2: "Domain (post (p\<^sub>1 ;\<^sup>p p\<^sub>2)) = {a. \<exists>c d. (a,c) \<in> post p\<^sub>1 \<and> (c,d) \<in> post p\<^sub>2}" by (auto simp: unsafe_composition2_def)
  have l3: "{a. \<exists>c. (a,c) \<in> post p\<^sub>1 \<and> a \<in> Pre p\<^sub>1 \<and> c \<in> Pre p\<^sub>2} \<subseteq> {a. \<exists>c d. (a,c) \<in> post p\<^sub>1 \<and> (c,d) \<in> post p\<^sub>2}" by (smt (verit, best) Collect_mono_iff Domain_iff a1 all_feasible.simps(2) is_feasible_def subsetD)
  have l4: "Pre (p\<^sub>1 ;\<^sup>p p\<^sub>2) \<subseteq>  Domain (post (p\<^sub>1 ;\<^sup>p p\<^sub>2))" using a1 a2 l1 l2 l3 by auto
  show "is_feasible (p\<^sub>1 ;\<^sup>p p\<^sub>2)" by (simp add: is_feasible_def l4)
qed

end