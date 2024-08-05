theory Boolean
  imports "../T_02_Fundamental_operations"
begin
section \<open>Boolean for top\<close>
theorem restrict_true: "p \<sslash>\<^sub>p (TRUE (S p)) \<triangleq> p" \<comment> \<open>/Restrict_true/\<close>
  by (auto simp: equal_def TRUE_def restrict_p_def restrict_r_def S_def Field_def)

theorem cond_false_1: "p \<sslash>\<^sub>p FALSE \<equiv>\<^sub>p Fail (S p)" \<comment> \<open>/Cond_false/\<close>
  by (auto simp: equal_def restr_post_def FALSE_def restrict_p_def restrict_r_def S_def Field_def Fail_def equiv_def)

theorem corestrict_true: "is_feasible p \<Longrightarrow> p \<setminus>\<^sub>p (TRUE (S p)) \<equiv>\<^sub>p p" \<comment> \<open>/Corestrict_true/\<close>
  apply (auto simp: equiv_def is_feasible_def TRUE_def corestrict_p_def corestrict_r_def S_def Field_def restr_post_def restrict_r_def)
  proof -
    fix x :: 'a
    assume a1: "Pre p \<subseteq> Domain (post p)"
    assume "x \<in> Pre p"
    then have "x \<in> Domain (post p)"
      using a1 by blast
    then show "x \<in> Domain {pa \<in> post p. snd pa \<in> State p \<or> snd pa \<in> Pre p \<or> snd pa \<in> Domain (post p) \<or> snd pa \<in> Range (post p)}"
      by fastforce
  next
    show "\<And>a b. Pre p \<subseteq> Domain (post p) \<Longrightarrow>
           (a, b) \<in> post p \<Longrightarrow>
           a \<in> Pre p \<Longrightarrow>
           a \<in> Domain {r \<in> post p. snd r \<in> State p \<or> snd r \<in> Pre p \<or> snd r \<in> Domain (post p) \<or> snd r \<in> Range (post p)}"
      by fastforce
  qed

theorem corestrict_false: "p \<setminus>\<^sub>p FALSE \<equiv>\<^sub>p Fail (S p)" \<comment> \<open>/Corestrict_false/\<close>
  by (auto simp: FALSE_def equiv_def Fail_def S_def corestrict_p_def corestrict_r_def)

theorem cond_true: "ITE (TRUE (S p\<^sub>1 \<union> S p\<^sub>2)) p\<^sub>1 p\<^sub>2 \<equiv>\<^sub>p p\<^sub>1" \<comment> \<open>/Cond_true/\<close>
  by (auto simp: if_then_else_def TRUE_def restrict_p_def S_def restrict_r_def choice_def restr_post_def equiv_def)

theorem cond_false_2: "ITE (FALSE) p\<^sub>1 p\<^sub>2 \<equiv>\<^sub>p p\<^sub>2" \<comment> \<open>Cond_false_2\<close>
  by (auto simp: if_then_else_def FALSE_def restrict_p_def restrict_r_def choice_def restr_post_def equiv_def)

theorem true_selects_first_program_2: "GC (TRUE (S p\<^sub>1 \<union> S p\<^sub>2)) p\<^sub>1 FALSE p\<^sub>2 \<equiv>\<^sub>p p\<^sub>1" \<comment> \<open>NEW\<close>
  by (auto simp: guarded_conditional_def FALSE_def TRUE_def restrict_p_def S_def restrict_r_def choice_def restr_post_def equiv_def)

theorem false_selects_second_program_2: "GC (FALSE) p\<^sub>1 (TRUE (S p\<^sub>1 \<union> S p\<^sub>2)) p\<^sub>2 \<equiv>\<^sub>p p\<^sub>2" \<comment> \<open>NEW\<close>
  by (auto simp: guarded_conditional_def TRUE_def S_def FALSE_def restrict_p_def restrict_r_def choice_def restr_post_def equiv_def)

end