theory Validity
  imports Definitions
begin
section \<open>Validity top\<close>

theorem valid_generalization: "is_valid p \<Longrightarrow> prop (S p) = prop (State p)"
  by (simp add: is_valid_def)

theorem pre_in_s: "is_valid p \<Longrightarrow> Pre p \<subseteq> State p"
  by (auto simp: S_def is_valid_def)

theorem post_in_s: "is_valid p \<Longrightarrow> (Field (post p) \<subseteq> State p)"
  by (auto simp: S_def is_valid_def)

subsection \<open>Validity is maintained by operations\<close>

theorem validity_inverse: "is_valid p \<Longrightarrow> is_valid (p\<^sup>-\<^sup>1)"
  by (auto simp: is_valid_def is_feasible_def inverse_def Range_p_def restr_post_def restrict_r_def S_def Field_def)

theorem validity_composition: "all_valid [p\<^sub>1, p\<^sub>2] \<Longrightarrow> is_valid (p\<^sub>1 ; p\<^sub>2)"
  apply (auto simp: is_valid_def is_feasible_def)
  by (auto simp: composition_def restr_post_def restrict_r_def corestrict_r_def S_def Field_def)
  
theorem validity_choice: "all_valid [p\<^sub>1, p\<^sub>2] \<Longrightarrow> is_valid (p\<^sub>1 \<union>\<^sub>p p\<^sub>2)"
  apply (auto simp: is_valid_def)
  by (auto simp: choice_def restr_post_def restrict_r_def corestrict_r_def S_def Field_def)

theorem validity_restriction: "is_valid p \<Longrightarrow> is_valid (p \<sslash>\<^sub>p C)"
  apply (auto simp: is_valid_def)
  by (auto simp: restrict_p_def restr_post_def restrict_r_def corestrict_r_def S_def Field_def)

theorem validity_corestriction: "is_valid p \<Longrightarrow> is_valid (p \<setminus>\<^sub>p C)"
  apply (auto simp: is_valid_def)
  by (auto simp: corestrict_p_def restr_post_def restrict_r_def corestrict_r_def S_def Field_def)

theorem validity_equality: "is_valid p \<Longrightarrow> is_valid q \<Longrightarrow> p \<triangleq> q \<Longrightarrow> p = q"
  by (auto simp: is_valid_def equal_def)

end