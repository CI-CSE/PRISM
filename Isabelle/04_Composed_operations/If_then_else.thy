theory If_then_else
  imports "../T_03_Basic_programs"
begin
section \<open>If then else for top.\<close>

lemma ite_S: "S (ITE C q\<^sub>1 q\<^sub>2) = S q\<^sub>1 \<union> S q\<^sub>2"
  by (auto simp: if_then_else_def S_def restrict_p_def restrict_r_def Field_def choice_def restr_post_def)

theorem cond_swap: "ITE C p\<^sub>1 p\<^sub>2 = ITE (-C) p\<^sub>2 p\<^sub>1" \<comment> \<open>Cond_swap\<close>
  by (auto simp: if_then_else_def choice_def)

value "ITE {1::nat} 
           \<lparr>State={}, Pre = {1::nat, 2}, post = {(1,2), (2,1)}\<rparr> 
           \<lparr>State={}, Pre = {1::nat, 2}, post = {(1,1), (2,2)}\<rparr>"

value "\<lparr>State={}, Pre = {1::nat, 2}, post = {(1,2), (2,1)}\<rparr> \<sslash>\<^sub>p {1::nat}"

theorem property_on_ite_2: "Pre (p \<sslash>\<^sub>p C) = Pre (ITE C p (Skip (S p)))" \<comment> \<open>T53\<close>
  oops

theorem cond_refine3: "q\<^sub>1 \<sqsubseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<sqsubseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> ITE C q\<^sub>1 q\<^sub>2 \<sqsubseteq>\<^sub>p ITE C p\<^sub>1 p\<^sub>2" \<comment> \<open>Cond_refine3\<close>
  apply (auto simp: refines_def)
  apply (auto simp: extends_def ite_S) [1]
  apply (auto simp: weakens_def if_then_else_def restrict_p_def restrict_r_def choice_def S_def) [1]
  by (auto simp: strengthens_def if_then_else_def restrict_p_def restrict_r_def choice_def restr_post_def)

theorem cond_refine4: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> ITE C q\<^sub>1 q\<^sub>2 \<subseteq>\<^sub>p ITE C p\<^sub>1 p\<^sub>2" 
  apply (auto simp: specialize_def)
  apply (auto simp: extends_def if_then_else_def) [1]
  apply (auto simp: weakens_def if_then_else_def restrict_p_def) [1]
  by (auto simp: strengthens_def if_then_else_def restrict_p_def restr_post_def restrict_r_def)



end