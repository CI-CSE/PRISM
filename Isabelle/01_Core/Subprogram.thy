theory Subprogram
  imports Definitions
begin
section \<open>Subprogram for top.\<close>

lemma subprogram_is_reflexive: "p\<^sub>1 \<preceq>\<^sub>p p\<^sub>1" \<comment> \<open>Subprogram_reflexive\<close>
  by (simp add: subprogram_def extends_def weakens_def strengthens_def restrict_r_def)

lemma subprogram_is_transitive: "p\<^sub>1 \<preceq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<preceq>\<^sub>p p\<^sub>3 \<Longrightarrow> p\<^sub>1 \<preceq>\<^sub>p p\<^sub>3" \<comment> \<open>Subprogram_transitive\<close>
  by (auto simp: subprogram_def extends_def weakens_def strengthens_def restrict_r_def subset_iff)

lemma subprogram_is_antisymetric: "p\<^sub>1 \<preceq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<preceq>\<^sub>p p\<^sub>1 \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2" \<comment> \<open>Subprogram_antisym\<close>
  by (auto simp: subprogram_def equiv_def extends_def weakens_def strengthens_def restrict_r_def restr_post_def)

theorem subprogram_is_preorder: "p\<^sub>1 \<preceq>\<^sub>p p\<^sub>1 \<and> (p\<^sub>2 \<preceq>\<^sub>p p\<^sub>3 \<and> p\<^sub>3 \<preceq>\<^sub>p p\<^sub>4 \<longrightarrow> p\<^sub>2 \<preceq>\<^sub>p p\<^sub>4)" \<comment> \<open>Subprogram_preorder\<close>
  apply (rule conjI)
  apply (rule subprogram_is_reflexive)
  using subprogram_is_transitive by auto

theorem subprogram_is_order: "(p\<^sub>1 \<preceq>\<^sub>p p\<^sub>1) \<and> (p\<^sub>2 \<preceq>\<^sub>p p\<^sub>3 \<and> p\<^sub>3 \<preceq>\<^sub>p p\<^sub>4 \<longrightarrow> p\<^sub>2 \<preceq>\<^sub>p p\<^sub>4) \<and> (p\<^sub>5 \<preceq>\<^sub>p p\<^sub>6 \<and> p\<^sub>6 \<preceq>\<^sub>p p\<^sub>5 \<longrightarrow> p\<^sub>5 \<equiv>\<^sub>p p\<^sub>6)" \<comment> \<open>Subprogram_order\<close>
  using subprogram_is_antisymetric subprogram_is_preorder by blast

theorem choice_decomp_1: "a \<preceq>\<^sub>p c \<and> b \<preceq>\<^sub>p c \<Longrightarrow> a \<union>\<^sub>p b \<preceq>\<^sub>p c"
  apply (auto simp: subprogram_def)
  apply (auto simp: extends_def choice_def restr_post_def restrict_r_def S_def Field_def) [1]
  apply (auto simp: weakens_def choice_def restr_post_def restrict_r_def S_def Field_def) [1]
  by (auto simp: strengthens_def choice_def restr_post_def restrict_r_def S_def Field_def) [1]

theorem choice_decomp_2: "a \<union>\<^sub>p b \<preceq>\<^sub>p c \<Longrightarrow> a \<preceq>\<^sub>p c \<and> b \<preceq>\<^sub>p c"
  apply (auto simp: subprogram_def)
  apply (auto simp: extends_def choice_def restr_post_def restrict_r_def S_def Field_def) [1]
  apply (auto simp: weakens_def choice_def restr_post_def restrict_r_def S_def Field_def) [1]
  apply (auto simp: strengthens_def choice_def restr_post_def restrict_r_def S_def Field_def) [1]
  apply (auto simp: extends_def choice_def restr_post_def restrict_r_def S_def Field_def) [1]
  apply (auto simp: weakens_def choice_def restr_post_def restrict_r_def S_def Field_def) [1]
  by (auto simp: strengthens_def choice_def restr_post_def restrict_r_def S_def Field_def) [1]

theorem choice_decomp: "a \<preceq>\<^sub>p c \<and> b \<preceq>\<^sub>p c \<equiv> a \<union>\<^sub>p b \<preceq>\<^sub>p c"
  by (smt (verit) choice_decomp_1 choice_decomp_2)

theorem subprogram_equiv: "a \<preceq>\<^sub>p b \<Longrightarrow> a \<equiv>\<^sub>p c \<Longrightarrow> b \<equiv>\<^sub>p d \<Longrightarrow> c \<preceq>\<^sub>p d"
  oops

theorem equiv_subprogram_transitivity: "S a \<subseteq> S b \<Longrightarrow> S c \<subseteq> S d \<Longrightarrow> a \<equiv>\<^sub>p b \<Longrightarrow> b \<preceq>\<^sub>p c \<Longrightarrow> c \<equiv>\<^sub>p d \<Longrightarrow> a \<preceq>\<^sub>p d"
  apply (auto simp: equiv_def subprogram_def)
  apply (auto simp: extends_def) [1]
  apply (auto simp: weakens_def) [1]
  by (auto simp: strengthens_def restrict_r_def restr_post_def) [1]
end