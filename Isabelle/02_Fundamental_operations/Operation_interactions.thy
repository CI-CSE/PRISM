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

theorem range_p_unsafe_composition: "Range_p(a) \<inter> C = {} \<Longrightarrow> a;\<^sub>pb\<sslash>\<^sub>p(-C) \<equiv>\<^sub>p a;\<^sub>pb"
  apply (auto simp: Range_p_def unsafe_composition_def restrict_p_def equiv_def corestrict_r_def restrict_r_def Int_def Range_iff Domain_iff restr_post_def relcomp_unfold)
  by fastforce

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

value "(\<lparr>State = {a\<^sub>1}, Pre = {a\<^sub>1}, post = {(a\<^sub>1, a\<^sub>1)}\<rparr> \<union>\<^sub>p \<lparr>State = {a\<^sub>1}, Pre = {a\<^sub>1}, post = {(a\<^sub>1, a\<^sub>1)}\<rparr>)\<sslash>\<^sub>p{}"
value "(\<lparr>State = {a\<^sub>1}, Pre = {a\<^sub>1}, post = {(a\<^sub>1, a\<^sub>1)}\<rparr>\<sslash>\<^sub>p{} \<union>\<^sub>p \<lparr>State = {a\<^sub>1}, Pre = {a\<^sub>1}, post = {(a\<^sub>1, a\<^sub>1)}\<rparr>\<sslash>\<^sub>p{})"

subsubsection \<open>Restriction choice\<close>
theorem restrict_distrib_1 : "(p\<^sub>1 \<union>\<^sub>p p\<^sub>2)\<sslash>\<^sub>pC = (p\<^sub>1\<sslash>\<^sub>pC \<union>\<^sub>p p\<^sub>2\<sslash>\<^sub>pC)" \<comment> \<open>/Restrict_distrib/ restriction distributes over choice\<close>
  \<comment> \<open>nitpick\<close>
  oops
theorem restrict_distrib_2 : "(p\<^sub>1 \<union>\<^sub>p p\<^sub>2)\<sslash>\<^sub>pC \<triangleq> (p\<^sub>1\<sslash>\<^sub>pC \<union>\<^sub>p p\<^sub>2\<sslash>\<^sub>pC)" \<comment> \<open>/Restrict_distrib/ restriction distributes over choice\<close>
  oops
theorem restrict_distrib_3 : "(p\<^sub>1 \<union>\<^sub>p p\<^sub>2)\<sslash>\<^sub>pC \<equiv>\<^sub>p (p\<^sub>1\<sslash>\<^sub>pC \<union>\<^sub>p p\<^sub>2\<sslash>\<^sub>pC)" \<comment> \<open>/Restrict_distrib/ restriction distributes over choice\<close>
  apply (simp add: equiv_def S_def Field_def restrict_p_def restrict_r_def choice_def restr_post_def)
  by blast

theorem restrict_distrib_4 : "a \<union>\<^sub>p (p\<^sub>1 \<union>\<^sub>p p\<^sub>2)\<sslash>\<^sub>pC = a \<union>\<^sub>p (p\<^sub>1\<sslash>\<^sub>pC \<union>\<^sub>p p\<^sub>2\<sslash>\<^sub>pC)"
  apply (auto simp add: choice_def restrict_p_def restr_post_def restrict_r_def)
  apply (simp add: S_def Field_def Domain_iff Range_iff)
  by (simp add: S_def Field_def Domain_iff Range_iff)

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
  \<comment> \<open>nitpick\<close>
  oops

\<comment> \<open>
definition p1 :: "nat Program" where "p1 = \<lparr>State = {1}, Pre = {1}, post = {(1, 1)}\<rparr>"
definition p2 :: "nat Program" where "p2= \<lparr>State = {1}, Pre = {}, post = {}\<rparr>"
definition q :: "nat Program" where "q = \<lparr>State = {}, Pre = {}, post = {(1, 1)}\<rparr>"
value "(q;p1) \<union>p (q;p2)"
value "q;(p1\<union>pp2)"
value "(p1\<union>pp2)"\<close>

theorem compose_distrib1_2 : "q;(p\<^sub>1\<union>\<^sub>pp\<^sub>2) \<triangleq> (q;p\<^sub>1) \<union>\<^sub>p (q;p\<^sub>2)" \<comment> \<open>/Compose_distrib1/\<close>
  \<comment> \<open>nitpick\<close>
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

theorem corestrict_compose: "(p\<^sub>1 ; p\<^sub>2) \<setminus>\<^sub>p C = p\<^sub>1 ; (p\<^sub>2 \<setminus>\<^sub>p C)" \<comment> \<open>/Corestrict_compose/\<close>
  apply (auto simp: composition_def corestrict_p_def corestrict_r_def restr_post_def restrict_r_def S_def Field_def Domain_iff relcomp_unfold) 
    apply blast 
   apply blast 
  by blast

subsubsection \<open>Composition unsafCompose_distrib1e composition\<close>
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
  by (metis choice_inverse_1 equal_is_reflexive)
theorem choice_inverse_3: "(p \<union>\<^sub>p q)\<^sup>-\<^sup>1 \<equiv>\<^sub>p (p\<^sup>-\<^sup>1) \<union>\<^sub>p (q\<^sup>-\<^sup>1)"
  using choice_inverse_1 equals_equiv_relation_3 by blast

subsubsection \<open>Corestriction unsafe composition\<close>
theorem corestriction_restriction_on_unsafe_composition_1 : "p\<^sub>1 \<setminus>\<^sub>p s\<^sub>1 ;\<^sub>p p\<^sub>2 \<equiv>\<^sub>p p\<^sub>1 ;\<^sub>p p\<^sub>2 \<sslash>\<^sub>p s\<^sub>1" \<comment> \<open>NEW\<close>
  oops
theorem corestrict_gets_absorbed_by_unsafe_composition_1: "(p\<^sub>1 ;\<^sub>p p\<^sub>2) \<setminus>\<^sub>p C \<equiv>\<^sub>p (p\<^sub>1 \<setminus>\<^sub>p C) ;\<^sub>p p\<^sub>2" \<comment> \<open>T30\<close>
  oops
theorem corestrict_gets_absorbed_by_unsafe_composition_2: "(p\<^sub>1 ;\<^sub>p p\<^sub>2) \<setminus>\<^sub>p C \<equiv>\<^sub>p p\<^sub>1 ;\<^sub>p (p\<^sub>2 \<setminus>\<^sub>p C)" \<comment> \<open>T30\<close>
  oops


theorem corestriction_on_unsafe_composition : "p\<^sub>1 \<setminus>\<^sub>p s ;\<^sub>p p\<^sub>2 = p\<^sub>1 ;\<^sub>p p\<^sub>2 \<sslash>\<^sub>p s" \<comment> \<open>NEW\<close>
  oops \<comment> \<open>making p1 feasible does not help\<close>

theorem corestrict_unsafe_compose: "is_feasible p\<^sub>1 \<Longrightarrow> (p\<^sub>1 ;\<^sub>p p\<^sub>2) \<setminus>\<^sub>p C \<equiv>\<^sub>p p\<^sub>1 ;\<^sub>p (p\<^sub>2 \<setminus>\<^sub>p C)" \<comment> \<open>/Corestrict_unsafe_compose/\<close>
  oops \<comment> \<open>making p1 feasible does not help\<close>


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
theorem corestrict_choice_1: "(p\<^sub>1 \<union>\<^sub>p p\<^sub>2) \<setminus>\<^sub>p C = (p\<^sub>1 \<setminus>\<^sub>p C) \<union>\<^sub>p (p\<^sub>2 \<setminus>\<^sub>p C)"
  by (auto simp: choice_def restr_post_def corestrict_p_def restrict_r_def S_def Field_def corestrict_r_def)
theorem corestrict_choice_2: "(p\<^sub>1 \<union>\<^sub>p p\<^sub>2) \<setminus>\<^sub>p C \<triangleq> (p\<^sub>1 \<setminus>\<^sub>p C) \<union>\<^sub>p (p\<^sub>2 \<setminus>\<^sub>p C)"
  by (simp add: corestrict_choice_1 equal_is_reflexive)
theorem corestrict_choice_3: "(p\<^sub>1 \<union>\<^sub>p p\<^sub>2) \<setminus>\<^sub>p C \<equiv>\<^sub>p (p\<^sub>1 \<setminus>\<^sub>p C) \<union>\<^sub>p (p\<^sub>2 \<setminus>\<^sub>p C)" \<comment> \<open>/Corestrict_choice/\<close>
  by (simp add: corestrict_choice_1 equiv_is_reflexive)

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
  apply (auto simp: equiv_def)
  apply (auto simp: composition_def corestrict_p_def corestrict_r_def restr_post_def restrict_r_def Domain_iff) [2]
  apply (auto simp: composition_def corestrict_p_def corestrict_r_def restr_post_def restrict_r_def Domain_iff) [2]
  apply (simp add: restr_post_def composition_def corestrict_p_def corestrict_r_def restrict_r_def Domain_iff relcomp_unfold)
  by metis


lemma until_simplification_2: "a;\<^sub>pn\<setminus>\<^sub>pC \<union>\<^sub>p a;\<^sub>pm\<setminus>\<^sub>pC \<equiv>\<^sub>p a;\<^sub>p(n \<union>\<^sub>p m)\<setminus>\<^sub>pC"
  apply (auto simp: equiv_def)
  apply (auto simp: unsafe_composition_def corestrict_p_def corestrict_r_def restr_post_def restrict_r_def Domain_iff) [2]
  apply (auto simp: unsafe_composition_def corestrict_p_def corestrict_r_def restr_post_def restrict_r_def Domain_iff) [2]
  apply (simp add: restr_post_def unsafe_composition_def corestrict_p_def corestrict_r_def restrict_r_def Domain_iff relcomp_unfold)
  by metis
end