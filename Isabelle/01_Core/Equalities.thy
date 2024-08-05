theory Equalities
  imports Definitions
begin
section \<open>Equalities\<close>


section \<open>Equalities properties\<close>

theorem equals_equiv_relation_1: "p\<^sub>1 = p\<^sub>2 \<Longrightarrow> p\<^sub>1 \<triangleq> p\<^sub>2" \<comment> \<open>NEW\<close>
  by (simp add: equal_def)

theorem equals_equiv_relation_2: "p\<^sub>1 \<triangleq> p\<^sub>2 \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2" \<comment> \<open>NEW\<close>
  by (simp add: equiv_def equal_def restr_post_def)

theorem equals_equiv_relation_3: "p\<^sub>1 = p\<^sub>2 \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2" \<comment> \<open>NEW\<close>
  by (simp add: equiv_def)

theorem equal_is_reflexive: "p\<^sub>1 \<triangleq> p\<^sub>1"
  by (simp add: equal_def)

theorem equiv_is_reflexive: "p\<^sub>1 \<equiv>\<^sub>p p\<^sub>1"
  by (simp add: equiv_def)

theorem equal_is_symetric: "p\<^sub>1 \<triangleq> p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<triangleq> p\<^sub>1"
  by (simp add: equal_def)

theorem equiv_is_symetric: "p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<equiv>\<^sub>p p\<^sub>1"
  by (simp add: equiv_def)

theorem equal_is_transitive: "p\<^sub>1 \<triangleq> p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<triangleq> p\<^sub>3 \<Longrightarrow> p\<^sub>1 \<triangleq> p\<^sub>3"
  by (simp add: equal_def)

theorem equiv_is_transitive: "p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<equiv>\<^sub>p p\<^sub>3 \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>3"
  by (simp add: equiv_def)

subsection \<open>Property implication\<close>
theorem inverse_equality_1: "\<not> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> \<not> p\<^sub>1 \<triangleq> p\<^sub>2"
  using equals_equiv_relation_2 by auto
theorem inverse_equality_2: "\<not> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> \<not> p\<^sub>1 = p\<^sub>2"
  using equiv_is_reflexive by auto
theorem inverse_equality_3: "\<not> p\<^sub>1 \<triangleq> p\<^sub>2 \<Longrightarrow> \<not> p\<^sub>1 = p\<^sub>2"
  using equal_is_reflexive by auto

end