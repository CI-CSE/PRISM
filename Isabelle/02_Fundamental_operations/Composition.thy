theory Composition
  imports "../T_01_Core"
begin
section \<open>Composition for top\<close>

theorem composition_state [simp]: "S (f ; g) = S f \<union> S g"
  by (auto simp: composition_def S_def restr_post_def restrict_r_def Field_def)

theorem composition_pre [simp]: "Pre (f ; g) \<subseteq> Pre f"
  by (auto simp: composition_def)

theorem composition_post_1 [simp]: "Domain (post (f ; g)) \<subseteq> Domain (post f)"
  by (auto simp: composition_def)

theorem composition_post_2 [simp]: "Range (post (f ; g)) \<subseteq> Range (post g)"
  by (auto simp: composition_def restr_post_def restrict_r_def)

theorem compose_assoc [simp]: "(p\<^sub>1 ; p\<^sub>2) ; p\<^sub>3 = p\<^sub>1 ; (p\<^sub>2 ; p\<^sub>3)"  \<comment> \<open>/Compose_assoc/\<close>
proof -
  have compose_assoc_S: "S (p\<^sub>1 ; (p\<^sub>2 ; p\<^sub>3)) = S ((p\<^sub>1 ; p\<^sub>2) ; p\<^sub>3)"
    proof -
      have compose_assoc_S_1: "\<forall> f\<^sub>1 f\<^sub>2. S f\<^sub>1 \<subseteq> S (f\<^sub>1 ; f\<^sub>2)"
        by (auto simp: composition_def corestrict_r_def S_def)
    
      have compose_assoc_S_2: "\<forall> f\<^sub>1 f\<^sub>2. S f\<^sub>2 \<subseteq> S (f\<^sub>1 ; f\<^sub>2)"
        by (auto simp: composition_def corestrict_r_def S_def)
    
      have compose_assoc_S_3: "\<forall> f\<^sub>1 f\<^sub>2. S (f\<^sub>1 ; f\<^sub>2) = S f\<^sub>1 \<union> S f\<^sub>2"
        by (auto)
    
      have compose_assoc_S_4: "\<forall> f\<^sub>1 f\<^sub>2 f\<^sub>3. S (f\<^sub>1 ; (f\<^sub>2 ; f\<^sub>3)) = S f\<^sub>1 \<union> S f\<^sub>2 \<union> S f\<^sub>3"
        by (auto simp: compose_assoc_S_3)
      
      show ?thesis
        by (metis compose_assoc_S_3 compose_assoc_S_4)
    qed

  have compose_assoc_pre: "Pre (p\<^sub>1 ; (p\<^sub>2 ; p\<^sub>3)) = Pre ((p\<^sub>1 ; p\<^sub>2) ; p\<^sub>3)"
    proof -
      have compose_assoc_pre_1: "Pre ((p\<^sub>1 ; p\<^sub>2) ; p\<^sub>3) = {x.\<exists>y z. x \<in> Pre p\<^sub>1 \<and> (x,y) \<in> post p\<^sub>1 \<and> y \<in> Pre p\<^sub>2 \<and> (y,z) \<in> post p\<^sub>2 \<and> z \<in> Pre p\<^sub>3}"
        apply (auto simp: composition_def corestrict_r_def restr_post_def restrict_r_def)
        apply auto
        by fastforce
      have compose_assoc_pre_2: "Pre (p\<^sub>1 ; (p\<^sub>2 ; p\<^sub>3)) = {x.\<exists>y z.  x \<in> Pre p\<^sub>1 \<and> (x,y) \<in> post p\<^sub>1 \<and> y \<in> Pre p\<^sub>2 \<and> (y,z) \<in> post p\<^sub>2 \<and> z \<in> Pre p\<^sub>3}"
        apply (auto simp: composition_def corestrict_r_def)
        apply auto
        by fastforce
      show ?thesis
        by (auto simp: compose_assoc_pre_1 compose_assoc_pre_2)
    qed

  have compose_assoc_post: "post (p\<^sub>1 ; (p\<^sub>2 ; p\<^sub>3)) = post ((p\<^sub>1 ; p\<^sub>2) ; p\<^sub>3)"
    proof -
      have compose_assoc_post_1: "post (p\<^sub>1 ; (p\<^sub>2 ; p\<^sub>3)) = {(a,d). \<exists>b c. (a,b) \<in> post p\<^sub>1 \<and> b \<in> Pre p\<^sub>2 \<and> (b,c) \<in> post p\<^sub>2 \<and> c \<in> Pre p\<^sub>3 \<and> (c,d) \<in> post p\<^sub>3}"
        apply (auto simp: composition_def corestrict_r_def restr_post_def restrict_r_def)
        apply (auto)
        by fastforce
      have compose_assoc_post_2: "post ((p\<^sub>1 ; p\<^sub>2) ; p\<^sub>3) = {(a,d). \<exists>b c. (a,b) \<in> post p\<^sub>1 \<and> b \<in> Pre p\<^sub>2 \<and> (b,c) \<in> post p\<^sub>2 \<and> c \<in> Pre p\<^sub>3 \<and> (c,d) \<in> post p\<^sub>3}"
        apply (auto simp: composition_def corestrict_r_def restr_post_def restrict_r_def)
        apply (auto)
        by fastforce
      show ?thesis
        by (auto simp: compose_assoc_post_1 compose_assoc_post_2)
    qed

  show ?thesis
    by (metis Program.select_convs(2) Program.select_convs(3) compose_assoc_S compose_assoc_post compose_assoc_pre composition_def composition_state)
qed

theorem compose_assoc_2 [simp]: "(p\<^sub>1 ; p\<^sub>2) ; p\<^sub>3 \<triangleq> p\<^sub>1 ; (p\<^sub>2 ; p\<^sub>3)" \<comment> \<open>/Compose_assoc/\<close>
  by (simp add: equals_equiv_relation_1)

theorem compose_assoc_3 [simp]: "(p\<^sub>1 ; p\<^sub>2) ; p\<^sub>3 \<equiv>\<^sub>p p\<^sub>1 ; (p\<^sub>2 ; p\<^sub>3)" \<comment> \<open>/Compose_assoc/\<close>
  by (simp add: equals_equiv_relation_3)

theorem composition_simplification_1 : "p\<^sub>1 ; p\<^sub>2 = p\<^sub>1 \<setminus>\<^sub>p Pre p\<^sub>2 ; p\<^sub>2"
  by (auto simp: corestrict_p_def composition_def corestrict_r_def S_def restr_post_def restrict_r_def Field_def)

theorem composition_simplification_2 : "p\<^sub>1 ; p\<^sub>2 = p\<^sub>1 ; p\<^sub>2 \<sslash>\<^sub>p Pre p\<^sub>2"
  by (auto simp: restrict_p_def composition_def corestrict_r_def restrict_r_def S_def Field_def restr_post_def)

theorem composition_equiv: "f\<^sub>1 \<equiv>\<^sub>p p\<^sub>1 \<Longrightarrow> f\<^sub>2 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> f\<^sub>1 ; f\<^sub>2 \<equiv>\<^sub>p p\<^sub>1 ; p\<^sub>2" \<comment> \<open>Composition_equiv\<close>
  apply (auto simp: equiv_def restr_post_def restrict_r_def composition_def corestrict_r_def)
  using mem_Collect_eq relcomp.relcompI snd_conv apply fastforce
  using mem_Collect_eq relcomp.relcompI snd_conv by fastforce

theorem equality_is_maintained_by_composition: "f\<^sub>1 \<triangleq> p\<^sub>1 \<Longrightarrow> f\<^sub>2 \<triangleq> p\<^sub>2 \<Longrightarrow> f\<^sub>1 ; f\<^sub>2 \<triangleq> p\<^sub>1 ; p\<^sub>2" \<comment> \<open>NEW\<close>
  by (auto simp: equal_def restr_post_def composition_def)

lemma compose_feasible_lemma: "all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> Domain ((post p\<^sub>1) \<setminus>\<^sub>r (Pre p\<^sub>2)) = Domain ((post p\<^sub>1) \<setminus>\<^sub>r (Pre p\<^sub>2) O post p\<^sub>2)"
proof -
  assume a1: "all_feasible [p\<^sub>1, p\<^sub>2]"
  have compose_feasible_1: "is_feasible p\<^sub>1 \<Longrightarrow> is_feasible p\<^sub>2 \<Longrightarrow> Domain ((post p\<^sub>1) \<setminus>\<^sub>r (Pre p\<^sub>2)) = {x. \<exists>y z. (x,y) \<in> post p\<^sub>1 \<and> y \<in> Pre p\<^sub>2 \<and> (y, z) \<in> post p\<^sub>2}"
    using a1 apply (auto simp: corestrict_r_def is_feasible_def)
    by (meson Domain.cases subset_iff)
  have compose_feasible_2:  "Domain ((post p\<^sub>1) \<setminus>\<^sub>r (Pre p\<^sub>2) O post p\<^sub>2) = {x. \<exists>y z. (x,y) \<in> post p\<^sub>1 \<and> y \<in> Pre p\<^sub>2 \<and> (y, z) \<in> post p\<^sub>2}"
    using a1 by (auto simp: corestrict_r_def is_feasible_def relcomp_def)
  show ?thesis using a1 by (auto simp: is_feasible_def compose_feasible_2 compose_feasible_1)
qed

theorem compose_feasible2: "all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> is_feasible (p\<^sub>1 ; p\<^sub>2)" \<comment> \<open>/Compose_feasible2/\<close>
proof -
  assume a1: "all_feasible [p\<^sub>1, p\<^sub>2]"
  show "is_feasible (p\<^sub>1 ; p\<^sub>2)"
    using a1 apply (auto simp: composition_def compose_feasible_lemma is_feasible_def restr_post_def restrict_r_def corestrict_r_def Domain_iff relcomp_unfold subset_iff)
    by blast
qed

theorem composition_removes_dead_code_1: "p \<sslash>\<^sub>p (Pre p) ; q \<equiv>\<^sub>p p ; q"
  by (auto simp: composition_def equiv_def restrict_p_def restr_post_def restrict_r_def corestrict_r_def)

theorem composition_removes_dead_code_2: "p ; q \<sslash>\<^sub>p (Pre q) \<equiv>\<^sub>p p ; q"
  by (auto simp: composition_def equiv_def restrict_p_def restr_post_def restrict_r_def)

theorem compose_feasible: "is_feasible p\<^sub>2 \<Longrightarrow> is_feasible (p\<^sub>1 ; p\<^sub>2)" \<comment> \<open>Compose_feasible\<close>
  apply (auto simp: is_feasible_def composition_def restr_post_def restrict_r_def relcomp_unfold corestrict_r_def subset_iff Domain_iff)
  by blast

theorem "p\<^sub>1 ; p\<^sub>2 \<equiv>\<^sub>p \<lparr>State ={}, Pre=Pre p\<^sub>1 \<inter> Domain (post p\<^sub>1 \<setminus>\<^sub>r Pre p\<^sub>2), post=post p\<^sub>1\<rparr> ; p\<^sub>2"
  by (simp add: Definitions.equiv_def composition_def restr_post_def)

lemma range_decreases_composition: "Range_p (y;x) \<subseteq> Range_p x"
  by (auto simp: Range_p_def composition_def corestrict_r_def restrict_r_def restr_post_def)

text \<open>Composition is not refinement-safe due to the example below. All involved programs are feasible and q1 is independant from p2 and q2 from p1\<close>
theorem "p \<sqsubseteq>\<^sub>p q \<Longrightarrow> p;a \<sqsubseteq>\<^sub>p q;a"
  oops

theorem composition_subsafety: "a \<subseteq>\<^sub>p b \<Longrightarrow> a;c \<subseteq>\<^sub>p b;c" \<comment> \<open>Composition_subsafety\<close>
  apply (auto simp: specialize_def extends_def weakens_def strengthens_def restrict_r_def composition_def restr_post_def corestrict_r_def S_def Field_def Range_iff Domain_iff Un_def)
  by fastforce

theorem composition_subsafety2: "a \<subseteq>\<^sub>p b \<Longrightarrow> c;a \<subseteq>\<^sub>p c;b" \<comment> \<open>Composition_subsafety\<close>
  by (auto simp: specialize_def extends_def weakens_def strengthens_def restrict_r_def composition_def restr_post_def corestrict_r_def S_def Field_def Range_iff Domain_iff Un_def)

value "\<lparr>State={1::nat}, Pre={1}, post={(1,2),(1,3)}\<rparr>" \<comment> \<open>q1\<close>
value "\<lparr>State={1::nat}, Pre={2,3}, post={(2,4),(3,5)}\<rparr>" \<comment> \<open>q2\<close>

value "\<lparr>State={1::nat}, Pre={1}, post={(1,2),(1,3)}\<rparr>" \<comment> \<open>p1\<close>
value "\<lparr>State={1::nat}, Pre={2}, post={(2,4)}\<rparr>" \<comment> \<open>p2\<close>


value "\<lparr>State={1::nat}, Pre={1}, post={(1,2),(1,3)}\<rparr> \<sqsubseteq>\<^sub>p \<lparr>State={1::nat}, Pre={1}, post={(1,2),(1,3)}\<rparr>"
value "\<lparr>State={1::nat}, Pre={2,3}, post={(2,4),(3,5)}\<rparr> \<sqsubseteq>\<^sub>p \<lparr>State={1::nat}, Pre={2}, post={(2,4)}\<rparr>"

value "\<lparr>State={1::nat}, Pre={1}, post={(1,2),(1,3)}\<rparr> ; \<lparr>State={1::nat}, Pre={2,3}, post={(2,4),(3,5)}\<rparr>"
value "\<lparr>State={1::nat}, Pre={1}, post={(1,2),(1,3)}\<rparr> ; \<lparr>State={1::nat}, Pre={2}, post={(2,4)}\<rparr>"

value "\<lparr>State={1::nat}, Pre={1}, post={(1,2),(1,3)}\<rparr> ; \<lparr>State={1::nat}, Pre={2,3}, post={(2,4),(3,5)}\<rparr> \<sqsubseteq>\<^sub>p  \<lparr>State={1::nat}, Pre={1}, post={(1,2),(1,3)}\<rparr> ; \<lparr>State={1::nat}, Pre={2}, post={(2,4)}\<rparr>"

theorem comp_range_p_prop: "Range_p (q) \<subseteq> C \<Longrightarrow> Range_p (p;q) \<subseteq> C"
  by (auto simp: Range_p_def composition_def restrict_r_def corestrict_r_def restr_post_def)

theorem comp_range_p_prop_2: "x \<notin> Range_p q \<Longrightarrow> x \<notin> Range_p (p;q)"
  using range_decreases_composition by fastforce

theorem connecting_element: "(x,y) \<in> post (a;b) \<Longrightarrow> \<exists>z. (x,z) \<in> post a \<and> (z,y) \<in> post b \<and> z \<in> Pre b"
  by (auto simp: composition_def restr_post_def restrict_r_def)

theorem knowing_pre_composition: "x \<in> Pre (a) \<Longrightarrow> (x, y) \<in> post (a; b) \<Longrightarrow> x \<in> Pre (a ; b)"
  by (auto simp: composition_def restr_post_def corestrict_r_def restrict_r_def)


end