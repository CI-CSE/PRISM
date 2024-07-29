theory Subprogram
  imports Definitions
begin
section \<open>Subprogram for top.\<close>

lemma subprogram_is_reflexive: "p\<^sub>1 \<preceq>\<^sub>p p\<^sub>1"
  by (simp add: subprogram_def extends_def weakens_def strengthens_def restrict_r_def)

lemma subprogram_is_transitive: "p\<^sub>1 \<preceq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<preceq>\<^sub>p p\<^sub>3 \<Longrightarrow> p\<^sub>1 \<preceq>\<^sub>p p\<^sub>3"
  by (auto simp: subprogram_def extends_def weakens_def strengthens_def restrict_r_def subset_iff)

lemma subprogram_is_antisymetric: "p\<^sub>1 \<preceq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<preceq>\<^sub>p p\<^sub>1 \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2"
  by (auto simp: subprogram_def equiv_def extends_def weakens_def strengthens_def restrict_r_def restr_post_def)

theorem subprogram_is_preorder: "p\<^sub>1 \<preceq>\<^sub>p p\<^sub>1 \<and> (p\<^sub>2 \<preceq>\<^sub>p p\<^sub>3 \<and> p\<^sub>3 \<preceq>\<^sub>p p\<^sub>4 \<longrightarrow> p\<^sub>2 \<preceq>\<^sub>p p\<^sub>4)" \<comment> \<open>T1\<close>
  apply (rule conjI)
  apply (rule subprogram_is_reflexive)
  using subprogram_is_transitive by auto

theorem subprogram_is_order: "(p\<^sub>1 \<preceq>\<^sub>p p\<^sub>1) \<and> (p\<^sub>2 \<preceq>\<^sub>p p\<^sub>3 \<and> p\<^sub>3 \<preceq>\<^sub>p p\<^sub>4 \<longrightarrow> p\<^sub>2 \<preceq>\<^sub>p p\<^sub>4) \<and> (p\<^sub>5 \<preceq>\<^sub>p p\<^sub>6 \<and> p\<^sub>6 \<preceq>\<^sub>p p\<^sub>5 \<longrightarrow> p\<^sub>5 \<equiv>\<^sub>p p\<^sub>6)" \<comment> \<open>NEW\<close>
  using subprogram_is_antisymetric subprogram_is_preorder by blast



end