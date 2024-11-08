theory Skip
  imports "../T_02_Fundamental_operations"
begin
section \<open>Skip for top\<close>

theorem skip_is_valid: "is_valid (Skip s)"
  by (auto simp: is_valid_def Skip_def S_def Field_def)

theorem skip_is_feasible: "is_feasible (Skip s)"
  by (auto simp: is_feasible_def Skip_def)

theorem skip_is_total: "is_total (Skip s)"
  by (auto simp: is_total_def S_def Field_def Skip_def)

theorem skip_is_idempondent_composition: "Skip C ; Skip C = Skip C" \<comment> \<open>NEW\<close>
  by (auto simp: composition_def Skip_def S_def restr_post_def Field_def corestrict_r_def restrict_r_def)

theorem skip_is_idempondent_unsafe_composition: "Skip C ;\<^sub>p Skip C = Skip C" \<comment> \<open>NEW\<close>
  by (auto simp: unsafe_composition_def Skip_def S_def restr_post_def Field_def corestrict_r_def restrict_r_def)

theorem skip_unsafe_compose_r_1: "p ;\<^sub>p Skip (S p) \<triangleq> p"
  by (auto simp: unsafe_composition_def restr_post_def restrict_r_def Skip_def S_def Field_def relcomp_unfold equal_def)

lemma skip_compose_r_post: "post (p ; Skip (S p)) = post p" 
  by (auto simp: S_def Skip_def Field_def composition_def corestrict_r_def relcomp_def restr_post_def restrict_r_def)

lemma skip_compose_r_Pre_1: "Pre (p ; Skip (S p)) = (Pre p \<inter> Domain (post p))"
  by (auto simp: Skip_def S_def Field_def composition_def corestrict_r_def Range_def Domain_def)

lemma skip_compose_r_S: "S (p ; Skip (S p)) = S p"
  by (auto simp: S_def Skip_def Field_def composition_def corestrict_r_def restr_post_def restrict_r_def)

theorem skip_compose1: "is_feasible p \<Longrightarrow> p ; Skip (S p) \<triangleq> p" \<comment> \<open>/Skip_compose1/\<close>
  apply (auto simp: is_feasible_def equal_def S_def composition_def Skip_def restr_post_def corestrict_r_def Field_def Range_iff subset_iff Domain_iff Un_def relcomp_unfold restrict_r_def)
  by blast

theorem "is_feasible p \<Longrightarrow> Skip (S p) ; p \<triangleq> p"
  oops

lemma skip_compose2: "is_feasible p \<Longrightarrow> p ; Skip (S p) \<equiv>\<^sub>p p" \<comment> \<open>/Skip_compose/\<close>
  by (simp add: equals_equiv_relation_2 skip_compose1)


lemma skip_compose_r_range2: "is_feasible p \<Longrightarrow> p ; Skip (Range (post p)) \<triangleq>  p"
  apply (auto simp: equal_def S_def Skip_def composition_def Range_p_def restrict_r_def Field_def restr_post_def is_feasible_def corestrict_r_def Range_iff Domain_iff subset_iff relcomp_unfold)
  by blast

lemma skip_compose_r_range: "is_feasible p \<Longrightarrow> p ; Skip (Range_p p) \<equiv>\<^sub>p  p"
  apply (auto simp: equiv_def S_def Skip_def composition_def Range_p_def restrict_r_def Field_def restr_post_def is_feasible_def corestrict_r_def Range_iff Domain_iff subset_iff relcomp_unfold)
   apply blast
  by blast
lemma skip_compose4: "is_feasible p \<Longrightarrow> Skip (Pre p) ; p \<equiv>\<^sub>p  p" \<comment> \<open>Skip_compose4\<close>
  by (auto simp: equiv_def S_def Skip_def composition_def Range_p_def restrict_r_def Field_def restr_post_def is_feasible_def corestrict_r_def Range_iff Domain_iff subset_iff relcomp_unfold)

theorem skip_compose_r_3: "p ; Skip (S p) \<equiv>\<^sub>p p \<sslash>\<^sub>p Domain (post p)"
  by (auto simp: Skip_def composition_def restrict_p_def restr_post_def S_def equiv_def corestrict_r_def Field_def restrict_r_def Domain_iff Range_iff)

theorem skip_makes_feasible: "is_feasible (p ; Skip (S p))" \<comment> \<open>NEW\<close>
  by (simp add: is_feasible_def skip_compose_r_Pre_1 skip_compose_r_post)

lemma skip_compose_l_S: "S (Skip (S p) ; p) = S p"
  by (auto simp: S_def Skip_def Field_def composition_def corestrict_r_def restr_post_def restrict_r_def)

lemma skip_compose_l_Pre: "Pre (Skip (S p) ; p) = Pre p"
  by (auto simp: S_def Skip_def Field_def composition_def corestrict_r_def relcomp_def)

lemma skip_compose_l_post: "post (Skip (S p) ; p) = post p \<sslash>\<^sub>r Pre p"
  by (auto simp: Skip_def restrict_r_def S_def composition_def corestrict_r_def restr_post_def)

lemma skip_compose_l_1: "Skip (S p) ; p \<triangleq> \<lparr> State = S p, Pre = Pre p, post = post p \<sslash>\<^sub>r Pre p\<rparr>" \<comment> \<open>NEW\<close>
  by (metis (no_types, lifting) Program.select_convs(2) Program.select_convs(3) composition_def composition_state equal_def skip_compose_l_Pre skip_compose_l_S skip_compose_l_post)

theorem skip_compose3: "Skip (S p) ; p \<equiv>\<^sub>p p" \<comment> \<open>/Skip_compose/\<close>
  by (auto simp: equiv_def restr_post_def restrict_r_def skip_compose_l_Pre skip_compose_l_post)

theorem skip_unsafe_compose_r_2: "Skip (S p) ;\<^sub>p p \<triangleq> \<lparr>State=S p, Pre=S p, post = restr_post p \<rparr>"
  by (auto simp: unsafe_composition_def equal_def Skip_def S_def restr_post_def restrict_r_def Field_def)
  
theorem corestriction_prop: "p \<setminus>\<^sub>p C \<equiv>\<^sub>p p ; (Skip (S p) \<sslash>\<^sub>p C)" \<comment> \<open>T28\<close>
  apply (auto simp: Skip_def restrict_p_def equiv_def corestrict_p_def corestrict_r_def composition_def restr_post_def restrict_r_def)
  by (auto simp: Domain_iff S_def Field_def Range_iff)

lemma skip_prop: "Skip C \<union>\<^sub>p Skip D \<equiv>\<^sub>p Skip (C \<union> D)"
  apply (auto simp: equiv_def)
  apply (auto simp: Skip_def)[3]
  by (auto simp: restr_post_def restrict_r_def Skip_def)

theorem skip_prop_2: "Skip (S p) \<sslash>\<^sub>p C ; p \<equiv>\<^sub>p p \<sslash>\<^sub>p C"
  by (auto simp: Skip_def S_def restrict_p_def equiv_def Field_def Range_iff Domain_iff Un_def composition_def corestrict_r_def restr_post_def restrict_r_def)

theorem "Skip (C) ; p \<triangleq> p \<sslash>\<^sub>p C"
  oops

theorem skip_restrict: "Skip (C) ; p \<equiv>\<^sub>p p \<sslash>\<^sub>p C" \<comment> \<open>/Skip_restrict/\<close>
proof -
  have l1: "\<forall>C'. C' \<subseteq> S p \<longrightarrow> Skip (C') ; p \<equiv>\<^sub>p p \<sslash>\<^sub>p C'"
   by (auto simp: S_def composition_def equiv_def corestrict_r_def restrict_p_def Skip_def restr_post_def restrict_r_def)
  have l3: "Skip C ; p \<equiv>\<^sub>p Skip (C \<inter> (S p)) ; p"
    by (auto simp: S_def composition_def equiv_def corestrict_r_def restrict_p_def Skip_def restr_post_def restrict_r_def)
  have l4: "p \<sslash>\<^sub>p C \<equiv>\<^sub>p p \<sslash>\<^sub>p (C \<inter> (S p))"
    by (auto simp: S_def composition_def equiv_def corestrict_r_def restrict_p_def restr_post_def restrict_r_def)
  from l1 have l5: "Skip (C \<inter> (S p)) ; p \<equiv>\<^sub>p p \<sslash>\<^sub>p (C \<inter> (S p))"
    by simp
  show "Skip C ; p \<equiv>\<^sub>p p \<sslash>\<^sub>p C"
    by (metis Definitions.equiv_def l3 l4 l5)
qed

theorem skip_prop_4: "Skip D \<sslash>\<^sub>p C \<equiv>\<^sub>p Skip (D \<inter> C)"
  by (auto simp: equiv_def Skip_def restrict_p_def restr_post_def restrict_r_def)

theorem skip_prop_5: "C \<subseteq> D \<Longrightarrow> Skip D \<sslash>\<^sub>p C \<equiv>\<^sub>p Skip C"
  by (metis inf.absorb_iff2 skip_prop_4)

theorem skip_prop_6: "S p \<subseteq> C \<Longrightarrow> Skip C ; p \<equiv>\<^sub>p p"
  by (auto simp: Skip_def composition_def S_def Field_def restr_post_def restrict_r_def corestrict_r_def equiv_def)

theorem corestrict_skip: "p ; Skip (C) \<equiv>\<^sub>p p \<setminus>\<^sub>p C" \<comment> \<open>/Corestrict_skip/\<close>
  by (auto simp: composition_def Skip_def equiv_def corestrict_r_def corestrict_p_def restr_post_def restrict_r_def)

theorem skip_prop_8: "Skip D \<setminus>\<^sub>p C \<equiv>\<^sub>p Skip (D \<inter> C)"
  by (auto simp: equiv_def Skip_def corestrict_p_def restr_post_def corestrict_r_def restrict_r_def)

theorem skip_prop_9: "S (Skip (C)) = C"
  by (auto simp: Skip_def S_def Field_def)

theorem skip_prop_10: "Skip x \<union>\<^sub>p Skip y = Skip (x \<union> y)"
  by (auto simp: Skip_def choice_def restr_post_def S_def Field_def restrict_r_def)

theorem skip_prop_11: "Skip {} \<union>\<^sub>p p \<equiv>\<^sub>p p"
  by (auto simp: choice_def Skip_def restr_post_def restrict_r_def equiv_def)

theorem skip_prop_12: "Skip {} \<union>\<^sub>p (p \<union>\<^sub>p q) = p \<union>\<^sub>p q" \<comment> \<open>Skip is left neutral if choice was already applied\<close>
  by (auto simp: choice_def S_def Skip_def restr_post_def restrict_r_def Field_def)

theorem skip_prop_13: "(a ; Skip (S a \<union> S b) ); b = a ; b" \<comment> \<open>Skips in the middle are truely neutral\<close>
  by (auto simp: Skip_def composition_def relcomp_unfold restr_post_def S_def restrict_r_def Field_def corestrict_r_def)

theorem skip_prop_14: "(a ; Skip (S a) ); b = a ; b" \<comment> \<open>Skips in the middle are truly neutral\<close>
  by (auto simp: Skip_def composition_def relcomp_unfold restr_post_def S_def restrict_r_def Field_def corestrict_r_def Range_iff)

theorem skip_prop_15: "(a ; Skip (S b) ); b = a ; b" \<comment> \<open>Skips in the middle are truly neutral\<close>
  by (auto simp: Skip_def composition_def relcomp_unfold restr_post_def S_def restrict_r_def Field_def corestrict_r_def Range_iff)

theorem skip_prop_16: "S a \<subseteq> C \<Longrightarrow> post ((a ; Skip C); b) = post (a ; b)"
  by (auto simp: Skip_def composition_def relcomp_unfold restr_post_def S_def restrict_r_def Field_def corestrict_r_def Range_iff)
theorem skip_prop_17: "S b \<subseteq> C \<Longrightarrow> post ((a ; Skip C); b) = post (a ; b)"
  by (auto simp: Skip_def composition_def relcomp_unfold restr_post_def S_def restrict_r_def Field_def corestrict_r_def Range_iff)
theorem skip_prop_18: "S a \<subseteq> C \<Longrightarrow>  Skip C ; (a ; Skip C) = (Skip (S a); a) ; Skip C"
  apply (auto simp: composition_def Skip_def restr_post_def corestrict_r_def restrict_r_def relcomp_unfold)
  by (auto simp: S_def Field_def Domain_iff)


end