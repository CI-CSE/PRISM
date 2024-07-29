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

theorem skip_unsafe_compose_r: "p ;\<^sub>p Skip (S p) \<triangleq> p"
  apply (auto simp: unsafe_composition_def restr_post_def restrict_r_def Skip_def S_def Field_def relcomp_unfold equal_def)

lemma skip_compose_r_post: "post (p ; Skip (S p)) = post p" 
  by (auto simp: S_def Skip_def Field_def composition_def corestrict_r_def relcomp_def restr_post_def restrict_r_def)

lemma skip_compose_r_Pre_1: "Pre (p ; Skip (S p)) = (Pre p \<inter> Domain (post p))"
  by (auto simp: Skip_def S_def Field_def composition_def corestrict_r_def Range_def Domain_def)

lemma skip_compose_r_S: "S (p ; Skip (S p)) = S p"
  by (auto simp: S_def Skip_def Field_def composition_def corestrict_r_def restr_post_def restrict_r_def)

theorem skip_compose_r_1: "is_feasible p \<Longrightarrow> p ; Skip (S p) \<triangleq> p" \<comment> \<open>/Skip_compose/\<close>
proof -
  assume a1: "is_feasible p"
  have l2: "is_feasible p \<Longrightarrow> Pre p = Pre p \<inter> Domain (post p)"
    by (meson inf.orderE is_feasible_def)
  have l3: "is_feasible p \<Longrightarrow> Pre (p ; Skip (S p)) = Pre p"
    by (metis l2 skip_compose_r_Pre_1)
  show ?thesis
    apply (auto simp: equal_def)
  proof -
    show "\<And>x. x \<in> Pre (p ; Skip (S p)) \<Longrightarrow> x \<in> Pre p"
      by (simp add: skip_compose_r_Pre_1)
  next from a1 skip_compose_r_Pre_1 l2 l3 show "\<And>x. x \<in> Pre p \<Longrightarrow> x \<in> Pre (p ; Skip (S p))"
      by (auto simp: is_feasible_def)
  next show "\<And>a b. (a, b) \<in> post (p ; Skip (S p)) \<Longrightarrow> (a, b) \<in> post p"
      by (simp add: skip_compose_r_post)
  next show "\<And>a b. (a, b) \<in> post p \<Longrightarrow> (a, b) \<in> post (p ; Skip (S p))"
      by (simp add: skip_compose_r_post)
  next show "\<And>x. x \<in> S (Skip (S p)) \<Longrightarrow> x \<in> S p"
      using skip_compose_r_S by fastforce
  qed
qed

theorem skip_compose_r_2: "is_feasible p \<Longrightarrow> p ; Skip (S p) \<equiv>\<^sub>p p" \<comment> \<open>\<comment> \<open>/Skip_compose/\<close>\<close>
  by (simp add: equals_equiv_relation_2 skip_compose_r_1)

theorem skip_makes_feasible: "is_feasible (p ; Skip (S p))" \<comment> \<open>NEW\<close>
  by (simp add: is_feasible_def skip_compose_r_Pre_1 skip_compose_r_post)

lemma skip_compose_l_S: "S (Skip (S p) ; p) = S p"
  by (auto simp: S_def Skip_def Field_def composition_def corestrict_r_def restr_post_def restrict_r_def)

lemma skip_compose_l_Pre: "Pre (Skip (S p) ; p) = Pre p"
  by (auto simp: S_def Skip_def Field_def composition_def corestrict_r_def relcomp_def)

lemma skip_compose_l_post: "post (Skip (S p) ; p) = post p \<sslash>\<^sub>r Pre p"
  by (auto simp: Skip_def restrict_r_def S_def composition_def corestrict_r_def restr_post_def)

lemma skip_compose_l_1: "Skip (S p) ; p \<triangleq> \<lparr> State = S p, Pre = Pre p, post = post p \<sslash>\<^sub>r Pre p\<rparr>" \<comment> \<open>NEW\<close>
  apply (auto simp: equal_def skip_compose_l_Pre skip_compose_l_post skip_compose_l_S)
  apply (metis S_def UnCI composition_state select_convs(1) skip_compose_r_S)
  by (auto simp: composition_def corestrict_r_def S_def Field_def restrict_r_def)

theorem skip_compose_l: "Skip (S p) ; p \<equiv>\<^sub>p p" \<comment> \<open>/Skip_compose/\<close>
  by (auto simp: equiv_def restr_post_def restrict_r_def skip_compose_l_Pre skip_compose_l_post)

theorem skip_unsafe_compose_r: "Skip (S p) ;\<^sub>p p \<triangleq> \<lparr>State=S p, Pre=S p, post = restr_post p \<rparr>"
  by (auto simp: unsafe_composition_def restr_post_def restrict_r_def Skip_def S_def Field_def equal_def)

theorem corestriction_prop: "p \<setminus>\<^sub>p C \<equiv>\<^sub>p p ; (Skip (S p) \<sslash>\<^sub>p C)" \<comment> \<open>T28\<close>
  apply (auto simp: Skip_def restrict_p_def equiv_def corestrict_p_def corestrict_r_def composition_def restr_post_def restrict_r_def)
  by (auto simp: Domain_iff S_def Field_def Range_iff)

lemma skip_prop: "Skip C \<union>\<^sub>p Skip D \<equiv>\<^sub>p Skip (C \<union> D)"
  apply (auto simp: equiv_def)
  apply (auto simp: Skip_def)[3]
  by (auto simp: restr_post_def restrict_r_def Skip_def)

theorem skip_prop_2: "Skip (S p) \<sslash>\<^sub>p C ; p \<equiv>\<^sub>p p \<sslash>\<^sub>p C"
  by (auto simp: Skip_def S_def restrict_p_def equiv_def Field_def Range_iff Domain_iff Un_def composition_def corestrict_r_def restr_post_def restrict_r_def)

theorem skip_prop_3: "Skip (C) ; p \<equiv>\<^sub>p p \<sslash>\<^sub>p C"
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

theorem skip_prop_7: "p ; Skip (C) \<equiv>\<^sub>p p \<setminus>\<^sub>p C"
  by (auto simp: composition_def Skip_def equiv_def corestrict_r_def corestrict_p_def restr_post_def restrict_r_def)

theorem skip_prop_8: "Skip D \<setminus>\<^sub>p C \<equiv>\<^sub>p Skip (D \<inter> C)"
  by (auto simp: equiv_def Skip_def corestrict_p_def restr_post_def corestrict_r_def restrict_r_def)
end