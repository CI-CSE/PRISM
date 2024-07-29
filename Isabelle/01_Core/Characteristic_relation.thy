theory Characteristic_relation
  imports Definitions Equalities
begin
section \<open>Characteristic relation for top\<close>

theorem char_rel_is_unique_in_equality_1: "p\<^sub>1 = p\<^sub>2 \<Longrightarrow> char_rel p\<^sub>1 = char_rel p\<^sub>2"
  by (simp add: char_rel_def)

theorem char_rel_is_unique_in_equal_1: "p\<^sub>1 \<triangleq> p\<^sub>2 \<Longrightarrow> char_rel p\<^sub>1 = char_rel p\<^sub>2"
  by (simp add: char_rel_def equal_def)

theorem char_rel_is_unique_in_equiv_1: "p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> char_rel p\<^sub>1 = char_rel p\<^sub>2"
  by (auto simp: char_rel_def equiv_def restr_post_def)

theorem char_rel_is_unique_in_equality_2: "all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> (char_rel p\<^sub>1 = char_rel p\<^sub>2) \<Longrightarrow> (p\<^sub>1 = p\<^sub>2)"
  oops

theorem char_rel_is_unique_in_equal_2: "all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> (char_rel p\<^sub>1 = char_rel p\<^sub>2) \<Longrightarrow> (p\<^sub>1 \<triangleq> p\<^sub>2)"
  oops

theorem char_rel_is_unique_in_equiv_2: "all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> (char_rel p\<^sub>1 = char_rel p\<^sub>2) = (p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2)"
  apply (auto)
  apply (auto simp: char_rel_def equiv_def restr_post_def is_feasible_def restrict_r_def) [1]
  using fstI mem_Collect_eq apply force
  using fstI mem_Collect_eq apply force
  using char_rel_is_unique_in_equiv_1 by auto

theorem char_rel_choice: "char_rel (p\<^sub>1 \<union>\<^sub>p p\<^sub>2) = char_rel p\<^sub>1 \<union> char_rel p\<^sub>2"
  by (auto simp: char_rel_def choice_def restrict_r_def restr_post_def)

theorem char_rel_composition: "char_rel (p\<^sub>1 ; p\<^sub>2) = char_rel p\<^sub>1 O char_rel p\<^sub>2"
  by (auto simp: char_rel_def composition_def corestrict_r_def restrict_r_def restr_post_def)

theorem char_rel_restriction: "char_rel (p \<sslash>\<^sub>p C) = char_rel p \<sslash>\<^sub>r C"
  by (auto simp: char_rel_def restrict_p_def restrict_r_def)

theorem char_rel_corestriction: "char_rel (p \<setminus>\<^sub>p C) = char_rel p \<setminus>\<^sub>r C"
  by (auto simp: char_rel_def corestrict_p_def corestrict_r_def restrict_r_def)

theorem char_rel_strengthens: "strengthens p\<^sub>1 p\<^sub>2 \<Longrightarrow> char_rel p\<^sub>1 \<sslash>\<^sub>r Pre p\<^sub>2 \<subseteq> char_rel p\<^sub>2"
  by (auto simp: strengthens_def char_rel_def restrict_r_def)

theorem char_rel_weakens: "all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> weakens p\<^sub>1 p\<^sub>2 \<Longrightarrow> Domain (char_rel p\<^sub>2) \<subseteq> Domain (char_rel p\<^sub>1)"
  apply (auto simp: weakens_def char_rel_def restrict_r_def is_feasible_def subset_iff)
  by (simp add: Domain.simps)


theorem "p \<subseteq>\<^sub>p q \<Longrightarrow> char_rel p \<sslash>\<^sub>r (Domain (char_rel q)) \<subseteq> char_rel q"
  by (auto simp: char_rel_def refines_def strengthens_def restrict_r_def)

theorem "all_feasible [p, q] \<Longrightarrow> char_rel p \<sslash>\<^sub>r (Domain (char_rel q)) \<subseteq> char_rel q = strengthens p q"
  by (auto simp: char_rel_def strengthens_def restrict_r_def is_feasible_def Domain_iff subset_iff)

theorem "all_feasible [p, q] \<Longrightarrow> Domain (char_rel q) \<subseteq> Domain (char_rel p) = weakens p q"
  by (auto simp: char_rel_def weakens_def restrict_r_def is_feasible_def Domain_iff subset_iff)

end