theory Contract
  imports "../T_04_Composed_operations"
begin
section \<open>Contract for top\<close>

theorem consequence_rule:
  assumes "post\<^sub>1 \<subseteq> post\<^sub>2"
    and "Pre\<^sub>2 \<subseteq> Pre\<^sub>1"
    and "is_correct \<lparr>a_specification=\<lparr>State=Pre\<^sub>1 \<union> Field post\<^sub>2, Pre=Pre\<^sub>1, post=post\<^sub>1\<rparr>, a_implementation=b\<rparr>" 
  shows "is_correct \<lparr>a_specification=\<lparr>State=Pre\<^sub>1 \<union> Field post\<^sub>2, Pre=Pre\<^sub>2, post=post\<^sub>2\<rparr>, a_implementation=b\<rparr>"
proof -
  from assms show "is_correct \<lparr>a_specification=\<lparr>State=Pre\<^sub>1 \<union> Field post\<^sub>2, Pre=Pre\<^sub>2, post=post\<^sub>2\<rparr>, a_implementation=b\<rparr>"
    apply (auto simp: is_correct_def implements_def)
    apply (auto simp: refines_def)
    apply (auto simp: extends_def S_def) [1]
    apply (auto simp: weakens_def) [1]
    by (auto simp: strengthens_def restrict_r_def)
qed \<comment> \<open>Consequence_rule\<close>

theorem post_charac: "is_correct \<lparr>a_specification=s, a_implementation=b\<rparr> \<Longrightarrow> b sp (Pre s) \<subseteq> post s" \<comment> \<open>/Post_charac/\<close>
  by (auto simp: strongest_postcondition_def is_correct_def implements_def restrict_r_def refines_def weakens_def strengthens_def)

theorem pre_charac: "is_correct \<lparr>a_specification=s, a_implementation=b\<rparr> \<Longrightarrow> Pre s \<subseteq> b wp (post s)" \<comment> \<open>Pre_charac\<close>
  by (auto simp: weakest_precondition_def new_behavior_def is_correct_def implements_def restrict_r_def refines_def weakens_def strengthens_def  subset_iff)

value "implements \<lparr>State = {}, Pre = {a\<^sub>1}, post = {}\<rparr> \<lparr>State = {}, Pre = {}, post = {(a\<^sub>1, a\<^sub>1)}\<rparr>"

lemma correct_program_1: "is_correct \<lparr>a_specification=s, a_implementation=b\<rparr> \<Longrightarrow> Pre s \<subseteq> Pre b - Domain (post b - post s)"
  by (auto simp: is_correct_def implements_def refines_def weakens_def strengthens_def restrict_r_def subset_iff)

lemma correct_program_2: "S s = S b \<Longrightarrow> is_feasible b \<Longrightarrow> Pre s \<subseteq> Pre b - Domain (post b - post s) \<Longrightarrow> is_correct \<lparr>a_specification=s, a_implementation=b\<rparr>"
  by (auto simp: is_correct_def implements_def is_feasible_def refines_def weakens_def strengthens_def restrict_r_def S_def extends_def Field_def subset_iff)

theorem correct_program: "S s = S b \<Longrightarrow> is_feasible b \<Longrightarrow> is_correct \<lparr>a_specification=s, a_implementation=b\<rparr> = (Pre s \<subseteq> Pre b - Domain (post b - post s))" \<comment> \<open>Correct_program\<close>
  by (meson correct_program_1 correct_program_2)

theorem fail_false: "b sp FALSE = {}" \<comment> \<open>Fail_false\<close>
  by (auto simp: strongest_postcondition_def restrict_r_def FALSE_def)

theorem false_fail: "is_feasible b \<Longrightarrow> b wp {} = FALSE" \<comment> \<open>False_fail\<close>
  by (auto simp: weakest_precondition_def is_feasible_def new_behavior_def FALSE_def)

theorem fail_pre: "Fail S' sp Pre' = {}" \<comment> \<open>Fail_pre\<close>
  by (auto simp: Fail_def strongest_postcondition_def restrict_r_def)

theorem fail_post: "Fail S' wp post' = FALSE" \<comment> \<open>Fail_post\<close>
  by (auto simp: Fail_def weakest_precondition_def FALSE_def)

theorem sp_distrib: "b sp (p \<union> q) = b sp p \<union> b sp q" \<comment> \<open>sp_distrib\<close>
  by (auto simp: strongest_postcondition_def restrict_r_def)

theorem wp_distrib2: "(b wp p) \<union> (b wp q) \<subseteq> b wp (p \<union> q)" \<comment> \<open>wp_distrib2\<close>
  by (auto simp: weakest_precondition_def new_behavior_def)

theorem sanity: "q \<subseteq>\<^sub>p p \<Longrightarrow>  \<lparr>a_specification=s, a_implementation=q\<rparr> \<subseteq>\<^sub>c  \<lparr>a_specification=s, a_implementation=p\<rparr>"
  by (simp add: refines_c_def)

theorem mai_theorem_1: "is_feasible p \<Longrightarrow> is_correct (MAI p)" \<comment> \<open>MAI_theorem\<close>
  by (auto simp: is_feasible_def is_correct_def most_abstract_implementation_def implements_def refines_is_order)

theorem state_feasible_1: "(\<forall>s \<in> Pre p . is_trivial (post p) s \<or> is_relevant (post p) s) = is_feasible p" \<comment> \<open>State_feasible\<close>
  by (auto simp: is_feasible_def is_trivial_def is_relevant_def is_irrelevant_def S_def)

end
