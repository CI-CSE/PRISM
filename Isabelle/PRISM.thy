theory PRISM
  imports T_05_Properties
begin
section \<open>PRISM\<close>


theorem cond_for_commutative_1: "Range_p p\<^sub>1 \<inter> Pre p\<^sub>2 = {} \<Longrightarrow> Range_p p\<^sub>2 \<inter> Pre p\<^sub>1 = {} \<Longrightarrow> commute_programs3 p\<^sub>1 p\<^sub>2"
  by (auto simp: used_states_def commute_programs3_def composition_def equiv_def corestrict_r_def Field_def restr_post_def restrict_r_def Range_p_def Range_iff Int_def)

lemma distinct_state_range_dist_from_pre: "used_states p\<^sub>1 \<inter> used_states p\<^sub>2 = {} \<Longrightarrow> Range_p p\<^sub>1 \<inter> Pre p\<^sub>2 = {} \<and> Range_p p\<^sub>2 \<inter> Pre p\<^sub>1 = {}"
  by (auto simp: used_states_def Range_p_def restrict_r_def Field_def)

theorem "used_states p\<^sub>1 \<inter> used_states p\<^sub>2 = {} \<Longrightarrow> commute_programs1 p\<^sub>1 p\<^sub>2"
  by (auto simp: used_states_def commute_programs1_def composition_def corestrict_r_def restr_post_def restrict_r_def Field_def)

theorem "x; until_loop a C b n \<equiv>\<^sub>p until_loop (x;a) C b n"
  by (metis compose_assoc_3 equiv_is_symetric until_loop_def)

theorem "p;q \<equiv>\<^sub>p p; (q \<sslash>\<^sub>p (Range_p p))"
  apply (auto simp: composition_def equiv_def restrict_p_def restrict_r_def Range_p_def corestrict_p_def corestrict_r_def restr_post_def Domain_iff Range_iff relcomp_unfold) 
  apply fastforce 
  by fastforce

end