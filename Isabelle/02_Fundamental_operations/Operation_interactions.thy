theory Operation_interactions
  imports 
"../T_01_Core"
"Choice"
"Composition"
"Inverse"
"Restriction"
"Unsafe_composition"
begin
section \<open>Operation interactions for top\<close>

subsection \<open>Basic operations\<close>
subsubsection \<open>Restriction unsafe composition\<close>
theorem unsafe_compose_absorb : "(p\<^sub>1;\<^sub>pp\<^sub>2)\<sslash>\<^sub>pC = p\<^sub>1\<sslash>\<^sub>pC;\<^sub>pp\<^sub>2"
  by (auto simp: equal_def S_def Field_def unsafe_composition_def restrict_p_def restrict_r_def corestrict_r_def restr_post_def)
theorem unsafe_compose_absorb_2 : "(p\<^sub>1;\<^sub>pp\<^sub>2)\<sslash>\<^sub>pC \<triangleq> p\<^sub>1\<sslash>\<^sub>pC;\<^sub>pp\<^sub>2"
  by (simp add: equal_is_reflexive unsafe_compose_absorb)
theorem unsafe_compose_absorb_3 : "(p\<^sub>1;\<^sub>pp\<^sub>2)\<sslash>\<^sub>pC \<equiv>\<^sub>p p\<^sub>1\<sslash>\<^sub>pC;\<^sub>pp\<^sub>2"
  by (simp add: equiv_is_reflexive unsafe_compose_absorb)

subsubsection \<open>Restriction composition\<close>
theorem compose_absorb_1 : "(p\<^sub>1;p\<^sub>2)\<sslash>\<^sub>pC = p\<^sub>1\<sslash>\<^sub>pC;p\<^sub>2" \<comment> \<open>/Compose_absorb/\<close>
  by (auto simp: equal_def S_def Field_def composition_def restrict_p_def restrict_r_def corestrict_r_def restr_post_def)
theorem compose_absorb_2 : "(p\<^sub>1;p\<^sub>2)\<sslash>\<^sub>pC \<triangleq> p\<^sub>1\<sslash>\<^sub>pC;p\<^sub>2" \<comment> \<open>/Compose_absorb/\<close>                
  by (simp add: compose_absorb_1 equal_is_reflexive)
theorem compose_absorb_3 : "(p\<^sub>1;p\<^sub>2)\<sslash>\<^sub>pC \<equiv>\<^sub>p p\<^sub>1\<sslash>\<^sub>pC;p\<^sub>2" \<comment> \<open>/Compose_absorb/\<close>
  by (simp add: compose_absorb_1 equiv_is_reflexive)

theorem range_p_composition: "Range_p(a) \<inter> C = {} \<Longrightarrow> a;b\<sslash>\<^sub>p(-C) \<equiv>\<^sub>p a;b"
  apply (auto simp: Range_p_def composition_def restrict_p_def equiv_def corestrict_r_def restrict_r_def Int_def Range_iff Domain_iff restr_post_def relcomp_unfold)
  by fastforce

subsubsection \<open>Restriction choice\<close>
theorem restrict_distrib_1 : "(p\<^sub>1 \<union>\<^sub>p p\<^sub>2)\<sslash>\<^sub>pC = (p\<^sub>1\<sslash>\<^sub>pC \<union>\<^sub>p p\<^sub>2\<sslash>\<^sub>pC)" \<comment> \<open>/Restrict_distrib/ restriction distributes over choice\<close>
  oops
theorem restrict_distrib_2 : "(p\<^sub>1 \<union>\<^sub>p p\<^sub>2)\<sslash>\<^sub>pC \<triangleq> (p\<^sub>1\<sslash>\<^sub>pC \<union>\<^sub>p p\<^sub>2\<sslash>\<^sub>pC)" \<comment> \<open>/Restrict_distrib/ restriction distributes over choice\<close>
  oops
theorem restrict_distrib_3 : "(p\<^sub>1 \<union>\<^sub>p p\<^sub>2)\<sslash>\<^sub>pC \<equiv>\<^sub>p (p\<^sub>1\<sslash>\<^sub>pC \<union>\<^sub>p p\<^sub>2\<sslash>\<^sub>pC)" \<comment> \<open>/Restrict_distrib/ restriction distributes over choice\<close>
  by (auto simp: equiv_def S_def Field_def restrict_p_def restrict_r_def choice_def restr_post_def)

subsubsection \<open>Restriction corestriction\<close>

subsubsection \<open>Restriction inverse\<close>
theorem restriction_absorbed_by_inverse_1: "(p\<^sup>-\<^sup>1)\<sslash>\<^sub>pC = ((p\<setminus>\<^sub>pC)\<^sup>-\<^sup>1)"
  oops
theorem restriction_absorbed_by_inverse_2: "(p\<^sup>-\<^sup>1)\<sslash>\<^sub>pC \<triangleq> (p\<setminus>\<^sub>pC)\<^sup>-\<^sup>1"
  oops
theorem restriction_absorbed_by_inverse_3: "(p\<^sup>-\<^sup>1)\<sslash>\<^sub>pC \<equiv>\<^sub>p (p\<setminus>\<^sub>pC)\<^sup>-\<^sup>1"
  apply (auto simp: equiv_def)
  apply (auto simp: restrict_p_def Range_p_def corestrict_p_def restrict_r_def corestrict_r_def Range_iff Domain_iff) [2]
  by (auto simp: restrict_p_def Range_p_def corestrict_p_def restrict_r_def corestrict_r_def restr_post_def Range_iff Domain_iff)


subsubsection \<open>Composition choice\<close>
value "\<lparr>State = {}, Pre = {}, post = {(1::nat, 1)}\<rparr>"
value "\<lparr>State = {}, Pre = {1::nat}, post = {(1, 1)}\<rparr>"
value "\<lparr>State = {}, Pre = {}, post = {}\<rparr>::nat Program"
value "\<lparr>State = {}, Pre = {}, post = {(1::nat, 1)}\<rparr> ; (\<lparr>State = {}, Pre = {1::nat}, post = {(1, 1)}\<rparr> \<union>\<^sub>p \<lparr>State = {}, Pre = {}, post = {}\<rparr>::nat Program)"
value "(\<lparr>State = {}, Pre = {}, post = {(1::nat, 1)}\<rparr> ; \<lparr>State = {}, Pre = {1::nat}, post = {(1, 1)}\<rparr>) \<union>\<^sub>p (\<lparr>State = {}, Pre = {}, post = {(1::nat, 1)}\<rparr> ; \<lparr>State = {}, Pre = {}, post = {}\<rparr>::nat Program)"

lemma compose_distrib1_1: "q;(p\<^sub>1\<union>\<^sub>pp\<^sub>2) = (q;p\<^sub>1) \<union>\<^sub>p (q;p\<^sub>2)" \<comment> \<open>/Compose_distrib1/\<close>
  oops
theorem compose_distrib1_2 : "q;(p\<^sub>1\<union>\<^sub>pp\<^sub>2) \<triangleq> (q;p\<^sub>1) \<union>\<^sub>p (q;p\<^sub>2)" \<comment> \<open>/Compose_distrib1/\<close>
  oops
theorem compose_distrib1_3 : "q;(p\<^sub>1\<union>\<^sub>pp\<^sub>2) \<equiv>\<^sub>p (q;p\<^sub>1) \<union>\<^sub>p (q;p\<^sub>2)" \<comment> \<open>/Compose_distrib1/\<close>
  by (auto simp: choice_def equiv_def restr_post_def restrict_r_def composition_def corestrict_r_def)

lemma compose_distrib2_1: "(p\<^sub>1\<union>\<^sub>pp\<^sub>2);q = (p\<^sub>1;q) \<union>\<^sub>p (p\<^sub>2;q)" \<comment> \<open>/Compose_distrib2/\<close>
  by (auto simp: choice_def composition_def restr_post_def restrict_r_def corestrict_r_def S_def Field_def)
theorem compose_distrib2_2 : "(p\<^sub>1\<union>\<^sub>pp\<^sub>2);q \<triangleq> (p\<^sub>1;q) \<union>\<^sub>p (p\<^sub>2;q)" \<comment> \<open>/Compose_distrib2/\<close>
  by (simp add: compose_distrib2_1 equal_is_reflexive)
theorem compose_distrib2_3 : "(p\<^sub>1\<union>\<^sub>pp\<^sub>2);q \<equiv>\<^sub>p (p\<^sub>1;q) \<union>\<^sub>p (p\<^sub>2;q)" \<comment> \<open>/Compose_distrib2/\<close>
  by (simp add: compose_distrib2_1 equiv_is_reflexive)

theorem choice_distributes_over_composition : "q\<union>\<^sub>p(p\<^sub>1;p\<^sub>2) \<equiv>\<^sub>p (q\<union>\<^sub>pp\<^sub>1) ; (q\<union>\<^sub>pp\<^sub>2)" \<comment> \<open>Does not hold. Line: 143\<close>
  oops
subsubsection \<open>Composition corestriction\<close>
theorem corestriction_on_composition : "p\<^sub>1 \<setminus>\<^sub>p s\<^sub>1 ; p\<^sub>2 = p\<^sub>1 ; p\<^sub>2 \<sslash>\<^sub>p s\<^sub>1" \<comment> \<open>NEW\<close>
  by (auto simp: restrict_p_def corestrict_p_def composition_def corestrict_r_def restrict_r_def S_def Field_def restr_post_def)

theorem corestrict_compose: "(p\<^sub>1 ; p\<^sub>2) \<setminus>\<^sub>p C \<equiv>\<^sub>p p\<^sub>1 ; (p\<^sub>2 \<setminus>\<^sub>p C)" \<comment> \<open>/Corestrict_compose/\<close>
  apply (auto simp: equiv_def restr_post_def)
  by (auto simp: corestrict_p_def corestrict_r_def composition_def relcomp_unfold restrict_r_def restr_post_def Domain_iff) 

subsubsection \<open>Composition unsafe composition\<close>
theorem unsafe_gets_safe_1: "(p\<^sub>1;\<^sub>pp\<^sub>2);p\<^sub>3 = (p\<^sub>1;p\<^sub>2);p\<^sub>3"
  by (auto simp: composition_def unsafe_composition_def restr_post_def corestrict_r_def restrict_r_def S_def)
theorem unsafe_gets_safe_2: "(p\<^sub>1;\<^sub>pp\<^sub>2);p\<^sub>3 \<triangleq> (p\<^sub>1;p\<^sub>2);p\<^sub>3"
  by (simp add: equal_is_reflexive unsafe_gets_safe_1)
theorem unsafe_gets_safe_3: "(p\<^sub>1;\<^sub>pp\<^sub>2);p\<^sub>3 \<equiv>\<^sub>p (p\<^sub>1;p\<^sub>2);p\<^sub>3"
  by (simp add: equiv_is_reflexive unsafe_gets_safe_1)
theorem unsafe_gets_safe_extended: "((p\<^sub>1;\<^sub>pp\<^sub>2);\<^sub>pp\<^sub>3);p\<^sub>4 \<equiv>\<^sub>p ((p\<^sub>1;p\<^sub>2);p\<^sub>3);p\<^sub>4"
  by (simp add: Definitions.equiv_def unsafe_gets_safe_1)

theorem equivalency_of_compositions_1: "(p\<^sub>1\<setminus>\<^sub>pPre p\<^sub>2);\<^sub>pp\<^sub>2 = p\<^sub>1;p\<^sub>2"
  by (auto simp: corestrict_p_def unsafe_composition_def composition_def corestrict_r_def restr_post_def restrict_r_def S_def Field_def)
theorem equivalency_of_compositions_2: "(p\<^sub>1\<setminus>\<^sub>pPre p\<^sub>2);\<^sub>pp\<^sub>2 \<triangleq> p\<^sub>1;p\<^sub>2"
  by (simp add: equal_is_reflexive equivalency_of_compositions_1)
theorem equivalency_of_compositions_3: "(p\<^sub>1\<setminus>\<^sub>pPre p\<^sub>2);\<^sub>pp\<^sub>2 \<equiv>\<^sub>p p\<^sub>1;p\<^sub>2"
  by (simp add: equiv_is_reflexive equivalency_of_compositions_1)

subsubsection \<open>Composition inverse\<close>
theorem composition_inverse_1: "(p;q)\<^sup>-\<^sup>1 = (q\<^sup>-\<^sup>1);(p\<^sup>-\<^sup>1)"
  apply (auto simp: composition_def  Range_p_def restr_post_def restrict_r_def corestrict_r_def inverse_def converse_def Domain_iff Range_iff relcomp_unfold S_def Field_def)
  by (auto)
theorem composition_inverse_2: "(p;q)\<^sup>-\<^sup>1 \<triangleq> (q\<^sup>-\<^sup>1);(p\<^sup>-\<^sup>1)"
  by (simp add: composition_inverse_1 equal_is_reflexive)
theorem composition_inverse_3: "(p;q)\<^sup>-\<^sup>1 \<equiv>\<^sub>p (q\<^sup>-\<^sup>1);(p\<^sup>-\<^sup>1)"
  by (simp add: composition_inverse_1 equiv_is_reflexive)
subsubsection \<open>Choice inverse\<close>
theorem choice_inverse_1: "(p \<union>\<^sub>p q)\<^sup>-\<^sup>1 = (p\<^sup>-\<^sup>1) \<union>\<^sub>p (q\<^sup>-\<^sup>1)"
  by (auto simp: choice_def inverse_def converse_def Range_p_def S_def restr_post_def restrict_r_def Field_def)
theorem choice_inverse_2: "(p \<union>\<^sub>p q)\<^sup>-\<^sup>1 \<triangleq> (p\<^sup>-\<^sup>1) \<union>\<^sub>p (q\<^sup>-\<^sup>1)"
  by (simp add: choice_inverse_1 equal_is_reflexive)
theorem choice_inverse_3: "(p \<union>\<^sub>p q)\<^sup>-\<^sup>1 \<equiv>\<^sub>p (p\<^sup>-\<^sup>1) \<union>\<^sub>p (q\<^sup>-\<^sup>1)"
  by (simp add: choice_inverse_1 equiv_is_reflexive)

subsubsection \<open>Corestriction unsafe composition\<close>
theorem corestriction_restriction_on_unsafe_composition_1 : "p\<^sub>1 \<setminus>\<^sub>p s\<^sub>1 ;\<^sub>p p\<^sub>2 \<equiv>\<^sub>p p\<^sub>1 ;\<^sub>p p\<^sub>2 \<sslash>\<^sub>p s\<^sub>1" \<comment> \<open>NEW\<close>
  oops
theorem corestrict_gets_absorbed_by_unsafe_composition_1: "(p\<^sub>1 ;\<^sub>p p\<^sub>2) \<setminus>\<^sub>p C \<equiv>\<^sub>p (p\<^sub>1 \<setminus>\<^sub>p C) ;\<^sub>p p\<^sub>2" \<comment> \<open>T30\<close>
  oops
theorem corestrict_gets_absorbed_by_unsafe_composition_2: "(p\<^sub>1 ;\<^sub>p p\<^sub>2) \<setminus>\<^sub>p C \<equiv>\<^sub>p p\<^sub>1 ;\<^sub>p (p\<^sub>2 \<setminus>\<^sub>p C)" \<comment> \<open>T30\<close>
  oops
subsubsection \<open>Corestriction inverse\<close>
theorem corestriction_absorbed_by_inverse_1: "(p\<^sup>-\<^sup>1)\<setminus>\<^sub>pC = ((p\<sslash>\<^sub>pC)\<^sup>-\<^sup>1)"
  by (auto simp: inverse_def Range_p_def restrict_r_def corestrict_p_def corestrict_r_def restr_post_def restrict_p_def S_def Field_def)
theorem corestriction_absorbed_by_inverse_2: "(p\<^sup>-\<^sup>1)\<setminus>\<^sub>pC \<triangleq> ((p\<sslash>\<^sub>pC)\<^sup>-\<^sup>1)"
  by (simp add: corestriction_absorbed_by_inverse_1 equal_is_reflexive)
theorem corestriction_absorbed_by_inverse_3: "(p\<^sup>-\<^sup>1)\<setminus>\<^sub>pC \<equiv>\<^sub>p (p\<sslash>\<^sub>pC)\<^sup>-\<^sup>1"
  by (simp add: corestriction_absorbed_by_inverse_1 equiv_is_reflexive)

subsubsection \<open>Unsafe composition inverse\<close>
theorem unsafe_composition_inverse_1: "(p;\<^sub>pq)\<^sup>-\<^sup>1 \<equiv>\<^sub>p (q\<^sup>-\<^sup>1);\<^sub>p(p\<^sup>-\<^sup>1)"
  oops
subsubsection \<open>Choice corestriction\<close>
theorem corestrict_union: "(p\<^sub>1 \<union>\<^sub>p p\<^sub>2) \<setminus>\<^sub>p C \<equiv>\<^sub>p (p\<^sub>1 \<setminus>\<^sub>p C) \<union>\<^sub>p (p\<^sub>2 \<setminus>\<^sub>p C)" \<comment> \<open>/Corestrict_union/\<close>
  apply (auto simp: equiv_def restr_post_def)
  by (auto simp: choice_def restr_post_def corestrict_p_def restrict_r_def corestrict_r_def)

subsubsection \<open>Choice unsafe composition\<close>

theorem unsafe_compose_distrib1_3_1 : "q;\<^sub>p(p\<^sub>1\<union>\<^sub>pp\<^sub>2) = (q;\<^sub>pp\<^sub>1) \<union>\<^sub>p (q;\<^sub>pp\<^sub>2)"
  oops
theorem unsafe_compose_distrib1_3_2 : "q;\<^sub>p(p\<^sub>1\<union>\<^sub>pp\<^sub>2) \<triangleq> (q;\<^sub>pp\<^sub>1) \<union>\<^sub>p (q;\<^sub>pp\<^sub>2)"
  oops
theorem unsafe_compose_distrib1_3_3 : "q;\<^sub>p(p\<^sub>1\<union>\<^sub>pp\<^sub>2) \<equiv>\<^sub>p (q;\<^sub>pp\<^sub>1) \<union>\<^sub>p (q;\<^sub>pp\<^sub>2)"
  by (auto simp: choice_def equiv_def restr_post_def restrict_r_def unsafe_composition_def corestrict_r_def)

theorem unsafe_compose_distrib2_1 : "(p\<^sub>1\<union>\<^sub>pp\<^sub>2);\<^sub>pq = (p\<^sub>1;\<^sub>pq) \<union>\<^sub>p (p\<^sub>2;\<^sub>pq)"
  by (auto simp: unsafe_composition_def choice_def restr_post_def restrict_r_def S_def Field_def)
theorem unsafe_compose_distrib2_2 : "(p\<^sub>1\<union>\<^sub>pp\<^sub>2);\<^sub>pq \<triangleq> (p\<^sub>1;\<^sub>pq) \<union>\<^sub>p (p\<^sub>2;\<^sub>pq)"
  by (simp add: equal_is_reflexive unsafe_compose_distrib2_1)
theorem unsafe_compose_distrib2_3 : "(p\<^sub>1\<union>\<^sub>pp\<^sub>2);\<^sub>pq \<equiv>\<^sub>p (p\<^sub>1;\<^sub>pq) \<union>\<^sub>p (p\<^sub>2;\<^sub>pq)"
  by (simp add: equiv_is_reflexive unsafe_compose_distrib2_1)



value "restr_post (\<lparr>State={0::nat}, Pre={0,1}, post={(0,1),(1,0)}\<rparr> \<union>\<^sub>p Fail {0::nat} ;\<^sub>p Fail {0::nat})"
value "restr_post ((\<lparr>State={0::nat}, Pre={0,1}, post={(0,1),(1,0)}\<rparr> \<union>\<^sub>p Fail {0::nat}) ;\<^sub>p 
      (\<lparr>State={0::nat}, Pre={0,1}, post={(0,1),(1,0)}\<rparr> \<union>\<^sub>p Fail {0::nat}))"

theorem choice_distributes_over_composition_4 : "q\<union>\<^sub>p(p\<^sub>1;\<^sub>pp\<^sub>2) \<equiv>\<^sub>p (q\<union>\<^sub>pp\<^sub>1) ;\<^sub>p (q\<union>\<^sub>pp\<^sub>2)"
  oops

subsubsection \<open>Relation between more than two operations\<close>
lemma until_simplification_1: "a;n\<setminus>\<^sub>pC \<union>\<^sub>p a;m\<setminus>\<^sub>pC \<equiv>\<^sub>p a;(n \<union>\<^sub>p m)\<setminus>\<^sub>pC"
  by (meson compose_distrib1_3 corestrict_union equiv_is_reflexive equiv_is_symetric equiv_is_transitive equivalence_is_maintained_by_composition)

(* locale two_elements = *)
  (* fixes a b :: 'a *)
  (* assumes "a \<noteq> b" *)

(* theorem (in two_elements) choice_distributes_over_composition_3 : "\<exists>q p\<^sub>1 p\<^sub>2. \<not> q\<union>\<^sub>p(p\<^sub>1;\<^sub>pp\<^sub>2) \<equiv>\<^sub>p (q\<union>\<^sub>pp\<^sub>1) ;\<^sub>p (q\<union>\<^sub>pp\<^sub>2)" *)
  (* sorry *)
(* theorem (in two_elements) choice_distributes_over_composition_2 : "\<exists>q p\<^sub>1 p\<^sub>2. \<not>q\<union>\<^sub>p(p\<^sub>1;\<^sub>pp\<^sub>2) \<triangleq> (q\<union>\<^sub>pp\<^sub>1) ;\<^sub>p (q\<union>\<^sub>pp\<^sub>2)" *)
  (* using choice_distributes_over_composition_3 equals_equiv_relation_2 by blast *)
(* theorem (in two_elements) choice_distributes_over_composition_1 : "\<exists>q p\<^sub>1 p\<^sub>2. \<not>q\<union>\<^sub>p(p\<^sub>1;\<^sub>pp\<^sub>2) = (q\<union>\<^sub>pp\<^sub>1) ;\<^sub>p (q\<union>\<^sub>pp\<^sub>2)" *)
  (* by (metis choice_distributes_over_composition_2 equal_is_reflexive) *)

end