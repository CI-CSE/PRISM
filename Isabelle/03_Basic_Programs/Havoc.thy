theory Havoc
  imports "../T_02_Fundamental_operations" Skip
begin
section \<open>Havoc for top\<close>

theorem havoc_is_valid: "is_valid (Havoc s)"
  by (auto simp: is_valid_def Havoc_def S_def)

theorem havoc_is_feasible: "is_feasible (Havoc s)"
  by (auto simp: is_feasible_def Havoc_def)

theorem havoc_is_total: "is_total (Havoc s)"
  by (auto simp: is_total_def Havoc_def S_def)

theorem havoc_is_idempondent_composition: "Havoc C ; Havoc C = Havoc C" \<comment> \<open>NEW\<close>
  by (auto simp: composition_def Havoc_def S_def corestrict_r_def restr_post_def restrict_r_def)

theorem havoc_is_idempondent_unsafe_composition: "Havoc C ;\<^sub>p Havoc C = Havoc C" \<comment> \<open>NEW\<close>
  by (auto simp: unsafe_composition_def Havoc_def S_def corestrict_r_def restr_post_def restrict_r_def)

theorem havoc_union_l: "S p \<subseteq> C \<Longrightarrow> Havoc C \<union>\<^sub>p p = Havoc C" \<comment> \<open>/Havoc_union/\<close>
  by (auto simp: Havoc_def choice_def restr_post_def restrict_r_def S_def Field_def)

theorem havoc_union_r: "S p \<subseteq> C \<Longrightarrow> p \<union>\<^sub>p Havoc C = Havoc C" \<comment> \<open>/Havoc_union/\<close>
  by (auto simp: Havoc_def choice_def restr_post_def restrict_r_def S_def Field_def)

lemma havoc_pre_State: "State (p ; Havoc (S p)) = State (Havoc (S p) \<sslash>\<^sub>p Pre p)"
  by (simp add: composition_def Havoc_def restrict_p_def S_def Field_def)

lemma havoc_pre_S: "S p \<subseteq> C \<Longrightarrow> S (p ; Havoc C) = S (Havoc C \<sslash>\<^sub>p Pre p)"
  apply (simp add: composition_def Havoc_def restrict_p_def S_def corestrict_r_def)
  by (auto simp: Field_def restrict_r_def  restr_post_def)

lemma NOT_havoc_pre_Pre: "Pre (p ; Havoc (S p)) = Pre (Havoc (S p) \<sslash>\<^sub>p Pre p)"
  oops

lemma havoc_pre_Pre: "S p \<subseteq> C \<Longrightarrow>is_feasible p \<Longrightarrow> Pre (p ; Havoc C) = Pre (Havoc C \<sslash>\<^sub>p Pre p)"
  apply (simp add: is_feasible_def composition_def Havoc_def restrict_p_def corestrict_r_def S_def Field_def)
  using mem_Collect_eq prod.collapse 
  by force

lemma NOT_havoc_pre_post_1: "post (p ; Havoc (S p)) = post (Havoc (S p) \<sslash>\<^sub>p Pre p)" \<comment> \<open>NEW\<close>
  oops

lemma NOT_havoc_pre_post_1: "is_feasible p \<Longrightarrow> post (p ; Havoc (S p)) = post (Havoc (S p) \<sslash>\<^sub>p Pre p)" \<comment> \<open>NEW\<close>
  oops

lemma havoc_pre_post: "S p \<subseteq> C \<Longrightarrow>is_feasible p \<Longrightarrow> restr_post (p ; Havoc C)\<sslash>\<^sub>r Pre p = restr_post (Havoc C \<sslash>\<^sub>p Pre p)"
  apply (auto simp: is_feasible_def composition_def corestrict_r_def restrict_r_def Havoc_def restrict_p_def relcomp_def restr_post_def)
  apply (simp add: S_def)
  apply (simp add: S_def Field_def Domain_def Range_def)
  apply (auto simp: relcompp_apply subset_iff S_def Field_def)
  apply (meson Domain.cases Range.intros)
  by (metis (mono_tags, lifting) Domain_iff Relation_operations.corestrict_prop_1 mem_Collect_eq)

theorem NOT_havoc_pre: "p ; Havoc (S p) \<equiv>\<^sub>p Havoc (S p) \<sslash>\<^sub>p Pre p" \<comment> \<open>/Havoc_pre/\<close>
  oops


theorem havoc_pre: "S p \<subseteq> C \<Longrightarrow>is_feasible p \<Longrightarrow> (p ; Havoc C) \<equiv>\<^sub>p Havoc C \<sslash>\<^sub>p Pre p" \<comment> \<open>/Havoc_pre/\<close>
  apply (auto simp: equiv_def havoc_pre_Pre)
  apply (metis char_rel_composition char_rel_def char_rel_is_unique_in_equiv_1 char_rel_restriction compose_absorb_1 havoc_pre_post restr_post_def skip_compose_l skip_compose_l_Pre skip_compose_l_post)
  by (metis char_rel_composition char_rel_def char_rel_is_unique_in_equiv_1 char_rel_restriction compose_absorb_1 havoc_pre_post restr_post_def skip_compose_l skip_compose_l_Pre skip_compose_l_post)

theorem havoc_pre_unsafe: "S p \<subseteq> C \<Longrightarrow> (p ;\<^sub>p Havoc C) \<equiv>\<^sub>p Havoc C \<sslash>\<^sub>p Pre p"
  oops

theorem havoc_co_restricted: "(Havoc C \<sslash>\<^sub>p D) \<setminus>\<^sub>p D \<equiv>\<^sub>p Havoc (C \<inter> D)"
  by (auto simp: Havoc_def restrict_p_def corestrict_p_def equiv_def restrict_r_def corestrict_r_def S_def restr_post_def)


(* lemma havoc_absorbs_post_from_left_Pre: "is_feasible p \<Longrightarrow> Pre (Havoc (S p) ; p) = Pre (Havoc (S p) \<setminus>\<^sub>p Pre p)" *)
  (* by (simp add: is_feasible_def composition_def Havoc_def corestrict_p_def) *)

lemma havoc_from_left_S: "S p \<subseteq> C \<Longrightarrow> is_feasible p \<Longrightarrow> S (Havoc C ; p) = S(Havoc C \<setminus>\<^sub>p Range_p (p))"
  by (metis choice_state composition_state corestriction_state havoc_union_l)

lemma havoc_from_left_Pre: "S p \<subseteq> C \<Longrightarrow> is_feasible p \<Longrightarrow> \<not>p \<equiv>\<^sub>p Fail C \<Longrightarrow> Pre (Havoc C ; p) = C"
  by (auto simp: is_feasible_def composition_def corestrict_p_def corestrict_r_def Field_def Range_p_def restrict_r_def Havoc_def Fail_def equiv_def restr_post_def S_def)

lemma havoc_from_left_post: "S p \<subseteq> C \<Longrightarrow> is_feasible p \<Longrightarrow> post (Havoc C ; p) = post (Havoc C \<setminus>\<^sub>p Range_p (p))"
  by (auto simp: is_feasible_def corestrict_p_def corestrict_r_def Range_p_def restrict_r_def S_def composition_def Havoc_def Field_def  restr_post_def)


theorem havoc_from_left: "S p \<subseteq> C \<Longrightarrow> is_feasible p \<Longrightarrow> \<not>p \<equiv>\<^sub>p Fail C \<Longrightarrow> Havoc C ; p \<equiv>\<^sub>p Havoc C \<setminus>\<^sub>p Range_p p"
proof -
  assume a0: "S p \<subseteq> C"
  assume a1: "is_feasible p"
  assume a2: "\<not>p \<equiv>\<^sub>p Fail C"
  let ?left = "Havoc C ; p"
  let ?right = "Havoc C \<setminus>\<^sub>p Range_p p"

  have ld: "S p \<noteq> {}"
    using a1 a2 by (auto simp: Fail_def is_feasible_def equiv_def restr_post_def restrict_r_def S_def)

  have lc: "Range {r \<in> post p. fst r \<in> Pre p} \<noteq> {}"
  proof -
    have le: "Pre p \<noteq> {}"
      using a1 a2 by (auto simp: Fail_def is_feasible_def equiv_def restr_post_def restrict_r_def)
    show ?thesis
      using a1 le by (auto simp: is_feasible_def equiv_def Fail_def S_def Range_def)
  qed

  have la: "Range_p p \<noteq> {}"
    using a1 a2 lc by (auto simp: is_feasible_def Fail_def equiv_def restr_post_def restrict_r_def Range_p_def)

  from a0 a1 have l1: "S ?left = S ?right"
    using havoc_from_left_S by auto

  from a0 have lg: "Range_p p \<noteq> {} \<Longrightarrow> Pre ?right = C"
    apply (auto simp: Range_p_def restrict_r_def Havoc_def corestrict_p_def corestrict_r_def S_def Field_def Range_def Domain_def)
    by blast

  have l2: "Pre ?left = Pre ?right"
  proof -
    from a0 have l2_1: "Pre ?left = C"
      by (simp add: a1 a2 havoc_from_left_Pre)
    from a0 have l2_2: "Pre ?right = C"
      by (simp add: la lg)
    show ?thesis
      using l2_1 l2_2 by blast
  qed

  from a0 a1 a2 have l4: "s \<in> C \<Longrightarrow> t \<in> Range_p p \<Longrightarrow> (s,t) \<in> restr_post ?left"
    by (auto simp: restr_post_def Range_p_def Fail_def Havoc_def restrict_r_def composition_def S_def corestrict_r_def)

  from a0 have l5: "s \<in> C \<Longrightarrow> t \<in> Range_p p \<Longrightarrow> (s,t) \<in> restr_post ?right"
    apply (auto simp: equiv_def is_feasible_def Havoc_def Fail_def composition_def corestrict_r_def restr_post_def S_def corestrict_p_def restrict_r_def Range_p_def Field_def relcomp_def)
  proof -
    fix a :: 'a
    assume a1: "s \<in> C"
    assume a2: "(a, t) \<in> post p"
    assume a3: "a \<in> Pre p"
    assume "Range (post p) \<subseteq> C"
    then have f4: "t \<in> C"
      using a2 by auto
    have f5: "\<forall>a aa p. \<not> p (aa::'a, a::'a) \<or> aa \<in> Domain (Collect p)"
      by (metis (lifting) Relation_operations.restrict_prop_1 mem_Collect_eq split_pairs)
    have "t \<in> Range {pa \<in> post p. fst pa \<in> Pre p}"
      using a3 a2 by auto
    then show "s \<in> Domain {pa \<in> C \<times> C. snd pa \<in> Range {pa \<in> post p. fst pa \<in> Pre p}}"
      using f5 f4 a1 by simp
  qed
    
  from a0 have l3: "restr_post ?left = restr_post ?right"
    by (simp add: a1 havoc_from_left_post l2 restr_post_def)

  have l6: "?left \<equiv>\<^sub>p ?right"
    by (simp add: equiv_def l2 l3)

  from a0 show "Havoc C ; p \<equiv>\<^sub>p Havoc C \<setminus>\<^sub>p Range_p p"
    using l6 a0 by simp
qed

theorem refine_havoc: "p \<subseteq>\<^sub>p Havoc (S p) \<sslash>\<^sub>p Pre p" \<comment> \<open>/Refine_havoc/\<close>
  apply (auto simp: refines_def)
proof -
  show "extends p (Havoc (S p) \<sslash>\<^sub>p Pre p)"
    by (auto simp: extends_def S_def restrict_p_def Havoc_def restrict_r_def Field_def)
  show "weakens p (Havoc (S p) \<sslash>\<^sub>p Pre p)"
    by (auto simp: weakens_def restrict_p_def)
  show "strengthens p (Havoc (S p) \<sslash>\<^sub>p Pre p)"
    by (auto simp: strengthens_def restrict_p_def restrict_r_def S_def Havoc_def Field_def)
qed

theorem total_refine_havoc: "is_total p \<Longrightarrow> p \<subseteq>\<^sub>p Havoc (S p)" \<comment> \<open>/Total_refine_havoc/\<close>
  apply (auto simp: refines_def is_total_def)
proof -
  show "Pre p = S p \<Longrightarrow> extends p (Havoc (S p))"
    by (simp add: S_def extends_def Havoc_def)
  show "Pre p = S p \<Longrightarrow> weakens p (Havoc (S p))"
    by (simp add: S_def weakens_def Havoc_def)
  show "Pre p = S p \<Longrightarrow> strengthens p (Havoc (S p))"
    by (auto simp: S_def strengthens_def Havoc_def restrict_p_def restrict_r_def Field_def)
qed
end