theory Refinement
  imports Definitions Independence
begin
section \<open>Refines is preorder and order in regard to equivalence.\<close>


lemma refines_is_reflexive: "p\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1"
  by (simp add: refines_def extends_def weakens_def strengthens_def restrict_r_def)

lemma refines_is_transitive_e: "p\<^sub>1 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>3 \<Longrightarrow> extends p\<^sub>1 p\<^sub>3"
  by (auto simp: extends_def refines_def)

lemma refines_is_transitive_w: "p\<^sub>1 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>3 \<Longrightarrow> weakens p\<^sub>1 p\<^sub>3"
  by (auto simp: weakens_def refines_def)

lemma refines_is_transitive_s: "p\<^sub>1 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>3 \<Longrightarrow> strengthens p\<^sub>1 p\<^sub>3"
  by (auto simp: strengthens_def weakens_def restrict_r_def refines_def)

lemma refines_is_transitive: "p\<^sub>1 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>3 \<Longrightarrow> p\<^sub>1 \<subseteq>\<^sub>p p\<^sub>3"
  by (metis refines_def refines_is_transitive_e refines_is_transitive_w refines_is_transitive_s)

lemma refines_is_antisymetric: "p\<^sub>1 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2" \<comment> \<open>NEW\<close>
  by (auto simp: refines_def extends_def weakens_def strengthens_def restrict_r_def equiv_def restr_post_def)

theorem refines_is_preorder: "p\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<and> (p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>3 \<and> p\<^sub>3 \<subseteq>\<^sub>p p\<^sub>4 \<longrightarrow> p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>4)" \<comment> \<open>T1\<close>
  apply (rule conjI)
  apply (rule refines_is_reflexive)
  using refines_is_transitive by auto

theorem refines_is_order: "(p\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1) \<and> (p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>3 \<and> p\<^sub>3 \<subseteq>\<^sub>p p\<^sub>4 \<longrightarrow> p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>4) \<and> (p\<^sub>5 \<subseteq>\<^sub>p p\<^sub>6 \<and> p\<^sub>6 \<subseteq>\<^sub>p p\<^sub>5 \<longrightarrow> p\<^sub>5 \<equiv>\<^sub>p p\<^sub>6)" \<comment> \<open>NEW\<close>
  using refines_is_antisymetric refines_is_preorder by blast

subsection \<open>Refinement safety\<close>
subsubsection \<open>Corestriction\<close>




subsubsection \<open>Choice\<close>

subsection \<open>Composition\<close>

subsection \<open>Restriction\<close>


subsection \<open>Atomic concurrecy\<close>


  subsection \<open>Non-Atomic concurrency\<close>


subsection \<open>Guarded conditional\<close>



end