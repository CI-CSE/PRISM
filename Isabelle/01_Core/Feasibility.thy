theory Feasibility
  imports Definitions
begin
section \<open>Feasibility for top\<close>

section \<open>Feasibility of equality is maintained\<close>

theorem equal_maintains_feasiblity: "is_feasible p\<^sub>1 \<Longrightarrow> p\<^sub>1 \<triangleq> p\<^sub>2 \<Longrightarrow> is_feasible p\<^sub>2"
  by (simp add: equal_def is_feasible_def)

theorem equiv_maintains_feasiblity: "is_feasible p\<^sub>1 \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> is_feasible p\<^sub>2"
  apply (auto simp: equiv_def is_feasible_def restr_post_def restrict_r_def Domain_iff subset_iff)
  by fastforce


end