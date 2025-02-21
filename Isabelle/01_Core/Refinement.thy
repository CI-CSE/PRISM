theory Refinement
  imports Definitions Independence
begin
section \<open>Refines is preorder and order in regard to equivalence.\<close>


lemma refines_is_reflexive: "p\<^sub>1 \<sqsubseteq>\<^sub>p p\<^sub>1" \<comment> \<open>Refine_reflexive\<close>
  by (simp add: refines_def extends_def weakens_def strengthens_def restrict_r_def)

lemma refines_is_transitive_e: "p\<^sub>1 \<sqsubseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<sqsubseteq>\<^sub>p p\<^sub>3 \<Longrightarrow> extends p\<^sub>1 p\<^sub>3"
  by (auto simp: extends_def refines_def)

lemma refines_is_transitive_w: "p\<^sub>1 \<sqsubseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<sqsubseteq>\<^sub>p p\<^sub>3 \<Longrightarrow> weakens p\<^sub>1 p\<^sub>3"
  by (auto simp: weakens_def refines_def)

lemma refines_is_transitive_s: "p\<^sub>1 \<sqsubseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<sqsubseteq>\<^sub>p p\<^sub>3 \<Longrightarrow> strengthens p\<^sub>1 p\<^sub>3"
  by (auto simp: strengthens_def weakens_def restrict_r_def refines_def)

lemma refines_is_transitive: "p\<^sub>1 \<sqsubseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<sqsubseteq>\<^sub>p p\<^sub>3 \<Longrightarrow> p\<^sub>1 \<sqsubseteq>\<^sub>p p\<^sub>3" \<comment> \<open>Refine_transitive\<close>
  by (metis refines_def refines_is_transitive_e refines_is_transitive_w refines_is_transitive_s)

lemma refines_is_antisymetric: "p\<^sub>1 \<sqsubseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<sqsubseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2" \<comment> \<open>Refine_antisym\<close>
  by (auto simp: refines_def extends_def weakens_def strengthens_def restrict_r_def equiv_def restr_post_def)

theorem refines_is_preorder: "p\<^sub>1 \<sqsubseteq>\<^sub>p p\<^sub>1 \<and> (p\<^sub>2 \<sqsubseteq>\<^sub>p p\<^sub>3 \<and> p\<^sub>3 \<sqsubseteq>\<^sub>p p\<^sub>4 \<longrightarrow> p\<^sub>2 \<sqsubseteq>\<^sub>p p\<^sub>4)" \<comment> \<open>Refine_preorder\<close>
  apply (rule conjI)
  apply (rule refines_is_reflexive)
  using refines_is_transitive by auto

theorem refines_is_order: "(p\<^sub>1 \<sqsubseteq>\<^sub>p p\<^sub>1) \<and> (p\<^sub>2 \<sqsubseteq>\<^sub>p p\<^sub>3 \<and> p\<^sub>3 \<sqsubseteq>\<^sub>p p\<^sub>4 \<longrightarrow> p\<^sub>2 \<sqsubseteq>\<^sub>p p\<^sub>4) \<and> (p\<^sub>5 \<sqsubseteq>\<^sub>p p\<^sub>6 \<and> p\<^sub>6 \<sqsubseteq>\<^sub>p p\<^sub>5 \<longrightarrow> p\<^sub>5 \<equiv>\<^sub>p p\<^sub>6)" \<comment> \<open>Refine_order\<close>
  using refines_is_antisymetric refines_is_preorder by blast

theorem extends_is_reflexive: "extends p p"
  by (auto simp: extends_def)

theorem extends_is_transitive: "extends p q \<Longrightarrow> extends q r \<Longrightarrow> extends p r"
  by (auto simp: extends_def)

theorem weakens_is_reflexive: "weakens p p"
  by (auto simp: weakens_def)

theorem weakens_is_transitive: "weakens p q \<Longrightarrow> weakens q r \<Longrightarrow> weakens p r"
  by (auto simp: weakens_def)

theorem strengthens_is_reflexive: "strengthens p p"
  by (auto simp: strengthens_def restrict_r_def)

theorem strengthens_is_transitive_1: "weakens p q \<Longrightarrow> weakens q r \<Longrightarrow> strengthens p q \<Longrightarrow> strengthens q r \<Longrightarrow> strengthens p r"
  by (auto simp: strengthens_def restrict_r_def weakens_def)

theorem strengthens_is_transitive_2: "weakens q p \<Longrightarrow> weakens r q \<Longrightarrow> strengthens p q \<Longrightarrow> strengthens q r \<Longrightarrow> strengthens p r"
  by (auto simp: strengthens_def restrict_r_def weakens_def)

end