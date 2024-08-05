theory Range_p
  imports Definitions Equalities
begin
section \<open>Range_p properties for top\<close>

lemma same_range_p_3: "p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> Range_p p\<^sub>1 = Range_p p\<^sub>2"
  by (auto simp: Range_p_def equiv_def restr_post_def)

theorem same_range_p_2: "a \<triangleq> b \<Longrightarrow> Range_p a = Range_p b"
  using inverse_equality_1 same_range_p_3 by blast

theorem range_p_explicit_1: "y \<in> Range_p a \<Longrightarrow> \<exists>x. (x,y) \<in> post a \<and> x \<in> Pre a"
  by (auto simp: Range_p_def restrict_r_def)

theorem range_p_explicit_2: "(x,y) \<in> post a \<and> x \<in> Pre a \<Longrightarrow> y \<in> Range_p a"
  by (auto simp: Range_p_def restrict_r_def)

end