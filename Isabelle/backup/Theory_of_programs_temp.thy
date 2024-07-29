section \<open>Theory of programs temp\<close>


theory Theory_of_programs_temp
  imports Main
begin

section \<open>Helper\<close>


definition restrict_r :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" (infix "\<sslash>\<^sub>r" 150)
  where
    "restrict_r R S = {r \<in> R. fst r \<in> S}"

definition inv_restrict_r :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" (infix "\<sslash>\<^sub>-\<^sub>r" 150)
  where
    "inv_restrict_r R S = {r \<in> R. fst r \<notin> S}"

definition corestrict_r :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" (infix "\<setminus>\<^sub>r" 150)
  where
    "corestrict_r R S = {r \<in> R. snd r \<in> S}"

definition inv_corestrict_r :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" (infix "\<setminus>\<^sub>-\<^sub>r" 150)
  where
    "inv_corestrict_r R S = {r \<in> R. snd r \<notin> S}"

definition is_function :: "'a rel \<Rightarrow> bool"
  where
    "is_function R = (\<forall>r\<^sub>1 \<in> R.\<forall>r\<^sub>2\<in>R. fst r\<^sub>1 = fst r\<^sub>2 \<longrightarrow> snd r\<^sub>1 = snd r\<^sub>2)"

theorem corestriction_restriction_on_relcomp: "r\<^sub>1 \<setminus>\<^sub>r s\<^sub>1 O r\<^sub>2 = r\<^sub>1 O r\<^sub>2 \<sslash>\<^sub>r s\<^sub>1" \<comment> \<open>NEW\<close>
  by (auto simp: corestrict_r_def restrict_r_def)

theorem restrict_prop_1 [simp]: "r\<^sub>1 \<in> r \<Longrightarrow> fst r\<^sub>1 \<in> Domain r"
  by (simp add: Domain_fst)

theorem restrict_prop_2 [simp]: "r\<^sub>1 \<in> r \<Longrightarrow> fst r\<^sub>1 \<in> s \<Longrightarrow> fst r\<^sub>1 \<in> Domain (r \<sslash>\<^sub>r s)"
  by (simp add: restrict_r_def)

theorem restrict_prop_3 [simp]: "Domain r = Domain (r \<sslash>\<^sub>r s) \<union> Domain (r \<sslash>\<^sub>r (Field r - s))"
  apply (auto simp: restrict_r_def Field_def)
  using Domain.simps by fastforce

theorem restrict_prop_4 [simp]: "a \<sslash>\<^sub>r b \<union> a \<sslash>\<^sub>-\<^sub>r b = a"
  by (auto simp: restrict_r_def inv_restrict_r_def)

theorem corestrict_prop_1 [simp]: "r\<^sub>1 \<in> r \<Longrightarrow> snd r\<^sub>1 \<in> Range r"
  by (simp add: Range_snd)

theorem corestrict_prop_2 [simp]: "r\<^sub>1 \<in> r \<Longrightarrow> snd r\<^sub>1 \<in> s \<Longrightarrow> snd r\<^sub>1 \<in> Range (r \<setminus>\<^sub>r s)"
  by (simp add: corestrict_r_def)

theorem corestrict_prop_3 [simp]: "Domain r = Domain (r \<setminus>\<^sub>r s) \<union> Domain (r \<setminus>\<^sub>r (Field r - s))"
  apply (auto simp: corestrict_r_def Field_def)
  using Domain.simps by fastforce

theorem corestrict_prop_4 [simp]: "a \<setminus>\<^sub>r b \<union> a \<setminus>\<^sub>-\<^sub>r b = a"
  by (auto simp: corestrict_r_def inv_corestrict_r_def)


section \<open>2 Programs \<close>

datatype crash = Crash

datatype 'a elem = Elem 'a | Crashed

definition unpack :: "('a elem) set \<Rightarrow> 'a set" where
  "unpack es = {x. Elem x \<in> es}"

definition to_elems :: "'a set \<Rightarrow> 'a elem set" where
  "to_elems s = {Elem x | x. x \<in> s}"

definition to_elemr :: "'a rel \<Rightarrow> 'a elem rel" where
  "to_elemr r = {(Elem x, Elem y) | x y. (x,y) \<in> r}"

definition subsetoforequal :: "'a set \<Rightarrow> 'a elem set \<Rightarrow> bool" (infix "\<subseteq>\<^sub>e" 50) where
  "subsetoforequal s\<^sub>1 s\<^sub>2 = (to_elems s\<^sub>1 \<subseteq> s\<^sub>2)"

record 'a Program =
  State :: "'a elem set"
  Pre :: "'a elem set"
  post :: "'a elem rel"

(* locale ProgramLocale = *)
  (* fixes Program *)
  (* assumes consistant_space: "Pre p \<union> Field (post p) \<subseteq> S Program" *)

(* definition S :: "'a Program \<Rightarrow> 'a elem set" *)
  (* where *)
    (* "S p = State p \<union> Pre p \<union> Field (post p) \<union> {Crashed}" *)

definition is_valid :: "'a Program \<Rightarrow> bool"
  where
    "is_valid p \<equiv> Pre p \<subseteq> State p \<and> Field (post p) \<subseteq> State p \<and> Crashed \<in> State p \<and> Crashed \<notin> Pre p \<and> Crashed \<notin> Domain (post p) \<and> (\<forall> p\<^sub>1 \<in> Pre p - Domain (post p). (p\<^sub>1, Crashed) \<in> post p)"

definition ValidPrograms :: "('a Program) set"
  where
    "ValidPrograms = {p. is_valid p}"

abbreviation VP :: "('a Program) set"
  where
    "VP == ValidPrograms"

theorem pre_in_s: "p \<in> ValidPrograms \<Longrightarrow> Pre p \<subseteq> State p"
  by (auto simp: ValidPrograms_def is_valid_def)

theorem post_in_s: "p \<in> ValidPrograms \<Longrightarrow> (Field (post p) \<subseteq> State p)"
  by (auto simp: ValidPrograms_def is_valid_def)

value "Program \<lparr>
  State = to_elems {1,2,3,4},
  Pre = to_elems {0, 2, 4},
  post = to_elemr {(0, 1), (1, 2), (2, 3), (3, 4)}
\<rparr>"

theorem "p \<in> VP \<Longrightarrow> Pre p \<subseteq> State p"
  by (auto simp: ValidPrograms_def is_valid_def)
  

theorem "p \<in> VP \<Longrightarrow> Field (post p) \<subseteq> State p"
  by (auto simp: ValidPrograms_def is_valid_def)
  

theorem "Domain p \<subseteq> Field p"
  by (auto simp: Field_def)
  

theorem "Range p \<subseteq> Field p"
  by (auto simp: Field_def)
  

theorem "Field p = Domain p \<union> Range p"
  by (auto simp: Field_def)
  

definition is_deterministic :: "'a Program \<Rightarrow> bool" \<comment> \<open>D2\<close>
  where
    "is_deterministic p = is_function (post p)"

definition not_crashing ::"'a Program \<Rightarrow> bool" \<comment> \<open>New\<close>
  where
    "not_crashing p \<equiv> Crashed \<notin> Pre p \<and> Crashed \<notin> Field (post p \<sslash>\<^sub>r Pre p)"

definition is_feasible :: "'a Program \<Rightarrow> bool" \<comment> \<open>D5\<close>
  where
    "is_feasible p \<equiv> Pre p \<subseteq> Domain (post p) \<and> not_crashing p"

primrec all_feasible :: "('a Program) list \<Rightarrow> bool"
  where
    "all_feasible [] = True" |
    "all_feasible (x # xs) = (all_feasible xs \<and> is_feasible x)"

definition restr_post :: "'a Program \<Rightarrow> 'a elem rel"
  where
    "restr_post p = post p \<sslash>\<^sub>r Pre p"

(* definition equal :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" (infix "\<triangleq>" 48) \<comment> \<open>Make equals look at S and not State\<close> *)
  (* where *)
    (* "equal p\<^sub>1 p\<^sub>2 = (Pre p\<^sub>1 = Pre p\<^sub>2 \<and> post p\<^sub>1 = post p\<^sub>2 \<and> S p\<^sub>1 = S p\<^sub>2)" *)

definition equiv :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" (infix "\<equiv>\<^sub>p" 49) \<comment> \<open>D6\<close>
  where
    "equiv p\<^sub>1 p\<^sub>2 = (Pre p\<^sub>1 = Pre p\<^sub>2 \<and> restr_post p\<^sub>1 = restr_post p\<^sub>2)"

definition Range_p :: "'a Program \<Rightarrow> 'a elem set" \<comment> \<open>All states that could be reached\<close>
  where
    "Range_p p = Range (post p \<sslash>\<^sub>r Pre p)"

theorem range_p_prop : "p \<in> VP \<Longrightarrow> is_feasible p \<Longrightarrow> x \<in> Pre p \<Longrightarrow> x \<in> Domain (post p \<sslash>\<^sub>r Pre p)" \<comment> \<open>NEW\<close>
proof -
  assume a1: "p \<in> VP"
  assume a2: "is_feasible p"
  assume a3: "x \<in> Pre p"
  from a1 a2 a3 have t1: "x \<in> Domain (post p)" by (auto simp: is_feasible_def)
  from a1 a2 a3 t1 show "x \<in> Domain (post p \<sslash>\<^sub>r Pre p)"
    by (auto simp: ValidPrograms_def is_valid_def Range_p_def restrict_r_def Field_def is_feasible_def not_crashing_def)
qed

theorem range_p_prop_2 [simp]: " is_feasible p\<^sub>1 \<Longrightarrow> Range_p p\<^sub>1 \<subseteq> Pre p\<^sub>2 \<Longrightarrow> x \<in> Pre p\<^sub>1 \<Longrightarrow> x \<in> Domain {r \<in> post p\<^sub>1. snd r \<in> Pre p\<^sub>2}"
  (* apply (auto simp: ValidPrograms_def Range_p_def is_valid_def restrict_r_def Field_def is_feasible_def) *)
proof -
  assume a2: "is_feasible p\<^sub>1"
  assume a3: "Range_p p\<^sub>1 \<subseteq> Pre p\<^sub>2"
  assume a4: "x \<in> Pre p\<^sub>1"
  from a2 a4 have t1: "x \<in> Domain {r \<in> post p\<^sub>1. True}" by (auto simp: is_feasible_def)
  from a3 have t2: "Range (post p\<^sub>1 \<sslash>\<^sub>r Pre p\<^sub>1) \<subseteq> Pre p\<^sub>2" by (auto simp: Range_p_def)
  from a2 a3 a4 t1 t2 show "x \<in> Domain {r \<in> post p\<^sub>1. snd r \<in> Pre p\<^sub>2}" 
    apply (auto simp: Range_p_def restrict_r_def)
    by fastforce
qed

(* theorem equals_equiv_relation_1: "p\<^sub>1 = p\<^sub>2 \<Longrightarrow> p\<^sub>1 \<triangleq> p\<^sub>2" \<comment> \<open>NEW\<close> *)
  (* by (simp add: equal_def) *)

(* theorem equals_equiv_relation_2: "p\<^sub>1 \<triangleq> p\<^sub>2 \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2" \<comment> \<open>NEW\<close> *)
  (* by (simp add: equiv_def equal_def restr_post_def) *)

theorem equals_equiv_relation_3: "p\<^sub>1 = p\<^sub>2 \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2" \<comment> \<open>NEW\<close>
  by (simp add: equiv_def)

definition extends :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool"
  where
    "extends p\<^sub>2 p\<^sub>1 \<equiv> State p\<^sub>1 \<subseteq> State p\<^sub>2"

definition weakens :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool"
  where
    "weakens p\<^sub>2 p\<^sub>1 = (Pre p\<^sub>1 \<subseteq> Pre p\<^sub>2)"

definition strengthens :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" \<comment> \<open>Changed NEW\<close>
  where
    (* "strengthens p\<^sub>2 p\<^sub>1 \<equiv> \<forall> (a,b) \<in> post p\<^sub>2. (a \<in> Pre p\<^sub>1 \<and> a \<in> Pre p\<^sub>2) \<longrightarrow> ((a, b) \<in> post p\<^sub>1 \<or> (a, Crashed) \<in> post p\<^sub>1)" *)
    "strengthens p\<^sub>2 p\<^sub>1 \<equiv> (post p\<^sub>2 \<sslash>\<^sub>r Pre p\<^sub>2) \<sslash>\<^sub>r Pre p\<^sub>1 \<subseteq> post p\<^sub>1"  \<comment> \<open>Can be simplyfied if p2 weakens p1\<close>
  
definition refines :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" (infix "\<subseteq>\<^sub>p" 50) \<comment> \<open>D7\<close>
  where
    "refines p\<^sub>2 p\<^sub>1 \<equiv> extends p\<^sub>2 p\<^sub>1 \<and> weakens p\<^sub>2 p\<^sub>1 \<and> strengthens p\<^sub>2 p\<^sub>1 \<and> not_crashing p\<^sub>1 \<and> not_crashing p\<^sub>2"


subsection \<open>Refines is preorder and order in regard to equivalence.\<close>

lemma refines_is_reflexive: "not_crashing p \<Longrightarrow> p \<subseteq>\<^sub>p p"
  by (auto simp: refines_def extends_def weakens_def strengthens_def restrict_r_def)

lemma refines_is_transitive_e: "p\<^sub>1 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>3 \<Longrightarrow> extends p\<^sub>1 p\<^sub>3"
  by (auto simp: extends_def refines_def)

lemma refines_is_transitive_w: "p\<^sub>1 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>3 \<Longrightarrow> weakens p\<^sub>1 p\<^sub>3"
  by (auto simp: weakens_def refines_def)

lemma refines_is_transitive_s: "p\<^sub>1 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>3 \<Longrightarrow> strengthens p\<^sub>1 p\<^sub>3"
  by (auto simp: strengthens_def weakens_def restrict_r_def refines_def to_elems_def)

lemma refines_is_transitive: "p\<^sub>1 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>3 \<Longrightarrow> p\<^sub>1 \<subseteq>\<^sub>p p\<^sub>3"
  by (metis refines_def refines_is_transitive_e refines_is_transitive_w refines_is_transitive_s)

lemma refines_is_antisymetric: "{p\<^sub>1, p\<^sub>2} \<subseteq> VP \<Longrightarrow> p\<^sub>1 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2" \<comment> \<open>NEW\<close>
  by (auto simp: ValidPrograms_def is_valid_def refines_def extends_def weakens_def strengthens_def restrict_r_def equiv_def restr_post_def)

theorem refines_is_preorder: "{p\<^sub>1, p\<^sub>2, p\<^sub>3, p\<^sub>4} \<subseteq> VP \<Longrightarrow> not_crashing p\<^sub>1 \<Longrightarrow> p\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<and> (p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>3 \<and> p\<^sub>3 \<subseteq>\<^sub>p p\<^sub>4 \<longrightarrow> p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>4)" \<comment> \<open>T1\<close>
  apply (rule conjI)
  apply (rule refines_is_reflexive)
  using refines_is_transitive by auto

theorem refines_is_order: "{p\<^sub>1, p\<^sub>2, p\<^sub>3, p\<^sub>4, p\<^sub>5, p\<^sub>6} \<subseteq> VP \<Longrightarrow> not_crashing p\<^sub>1 \<Longrightarrow>(p\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1) \<and> (p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>3 \<and> p\<^sub>3 \<subseteq>\<^sub>p p\<^sub>4 \<longrightarrow> p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>4) \<and> (p\<^sub>5 \<subseteq>\<^sub>p p\<^sub>6 \<and> p\<^sub>6 \<subseteq>\<^sub>p p\<^sub>5 \<longrightarrow> p\<^sub>5 \<equiv>\<^sub>p p\<^sub>6)" \<comment> \<open>NEW\<close>
  by (meson dual_order.trans refines_is_antisymetric refines_is_reflexive refines_is_transitive subset_insertI)

(* subsubsection \<open>Strict refinement\<close> *)

(* definition strict_refines:: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" (infix "\<le>\<^sub>p" 50) *)
  (* where *)
    (* "strict_refines p\<^sub>2 p\<^sub>1 = (p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>1 \<and> Pre p\<^sub>2 = Pre p\<^sub>1)" *)

(* theorem strict_refines_is_order: "(p\<^sub>1 \<le>\<^sub>p p\<^sub>1) \<and> (p\<^sub>2 \<le>\<^sub>p p\<^sub>3 \<and> p\<^sub>3 \<le>\<^sub>p p\<^sub>4 \<longrightarrow> p\<^sub>2 \<le>\<^sub>p p\<^sub>4) \<and> (p\<^sub>5 \<le>\<^sub>p p\<^sub>6 \<and> p\<^sub>6 \<le>\<^sub>p p\<^sub>5 \<longrightarrow> p\<^sub>5 \<equiv>\<^sub>p p\<^sub>6)" *)
  (* apply (simp add: strict_refines_def) *)
  (* using refines_is_antisymetric refines_is_preorder by blast *)


subsubsection \<open>Independant properties\<close>

definition independant :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool"
  where
    "independant p\<^sub>1 p\<^sub>2 = (Pre p\<^sub>1 \<inter> Pre p\<^sub>2 = {})"

theorem independant_symetric: "independant p\<^sub>1 p\<^sub>2 = independant p\<^sub>2 p\<^sub>1"
  by (auto simp: independant_def)

theorem independant_weakens: "independant p\<^sub>1 p\<^sub>2 \<Longrightarrow> \<not>Pre p\<^sub>2 = {} \<Longrightarrow> \<not>weakens p\<^sub>1 p\<^sub>2"
  by (auto simp: independant_def weakens_def)

theorem independant_strengthens: "independant p\<^sub>1 p\<^sub>2 \<Longrightarrow> strengthens p\<^sub>1 p\<^sub>2"
  by (auto simp: independant_def strengthens_def restrict_r_def to_elems_def)

subsection \<open>Implementation.\<close>

definition implements :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" \<comment> \<open>D8\<close>
  where
    "implements p\<^sub>2 p\<^sub>1 = (p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>1 \<and> is_feasible p\<^sub>2)" \<comment> \<open>There seems to be a amiguous input\<close>

lemma implementation_1: "x \<in> X \<Longrightarrow> x \<in> Domain (R) \<Longrightarrow> x \<in> Domain (R \<sslash>\<^sub>r X)"
  by (auto simp: restrict_r_def)

theorem implementation_theorem: "{p\<^sub>2, p\<^sub>1} \<subseteq> VP \<Longrightarrow> implements p\<^sub>2 p\<^sub>1 \<Longrightarrow> is_feasible p\<^sub>1" \<comment> \<open>T2\<close>
proof -
  assume a1: "implements p\<^sub>2 p\<^sub>1"
  assume a2: "{p\<^sub>2, p\<^sub>1} \<subseteq> VP"
  have l1: "Pre p\<^sub>1 \<subseteq> Domain (post p\<^sub>2)"
    using a1 by (auto simp: implements_def is_feasible_def refines_def weakens_def)
  from a1 have l4: "\<forall>x \<in> Pre p\<^sub>1. x \<in> Domain (post p\<^sub>1)"
    by (meson Domain_mono l1 implementation_1 implements_def refines_def strengthens_def subsetD weakens_def)
  have l5: "Pre p\<^sub>1 \<subseteq> Domain (post p\<^sub>1)"
    by (simp add: l4 subsetI)
  from a1 a2 have l6: "not_crashing p\<^sub>1"
    by (auto simp: implements_def is_feasible_def refines_def weakens_def strengthens_def restrict_r_def not_crashing_def)
  then show "is_feasible p\<^sub>1"
    using l6 l5 by (simp add: is_feasible_def not_crashing_def)
qed
  

section \<open>3 Operations on specifications and programs\<close>
subsection \<open>3.2 Basic constructs \<close>

definition choice :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix "\<union>\<^sub>p" 151) \<comment> \<open>D9\<close>
  where
    "choice p\<^sub>1 p\<^sub>2 = \<lparr>State= State p\<^sub>1 \<union> State p\<^sub>2, Pre = Pre p\<^sub>1 \<union> Pre p\<^sub>2, post = restr_post p\<^sub>1 \<union> restr_post p\<^sub>2\<rparr>"

definition composition :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix ";" 152) \<comment> \<open>D10\<close>
  where
    "composition p\<^sub>1 p\<^sub>2 = \<lparr>
      State = State p\<^sub>1 \<union> State p\<^sub>2,
      Pre = Pre p\<^sub>1 \<inter> Domain (post p\<^sub>1 \<setminus>\<^sub>r Pre p\<^sub>2),
      post = (post p\<^sub>1) \<setminus>\<^sub>r (Pre p\<^sub>2) O (post p\<^sub>2)\<rparr>"

definition unsafe_composition ::"'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix ";\<^sub>p" 152)
  where
    "unsafe_composition p\<^sub>1 p\<^sub>2 = \<lparr>
      State = State p\<^sub>1 \<union> State p\<^sub>2,
      Pre = Pre p\<^sub>1,
      post = {(x,y).\<exists>z. (x,z)\<in>post p\<^sub>1 \<and> (z \<in> Pre p\<^sub>2 \<and> (z,y)\<in>post p\<^sub>2)} \<union> {(x, Crashed).\<exists>z. (x,z)\<in>post p\<^sub>1 \<and> \<not>(z \<in> Pre p\<^sub>2 \<or> (\<forall>y.(z,y) \<notin> post p\<^sub>2))}\<rparr>"
      (* post = (post p\<^sub>1) \<setminus>\<^sub>r (Pre p\<^sub>2) O (post p\<^sub>2) \<union> {(fst r, Crashed) | r. r \<in> ((post p\<^sub>1) \<setminus>\<^sub>-\<^sub>r (Pre p\<^sub>2))}\<rparr>" *)

value "(\<lparr>State={elem 1}, Pre={elem 1}, post={(elem 1,elem 2),(elem 1,elem 3)}\<rparr> :: nat Program) ; (\<lparr>State={elem 1}, Pre={elem 2,elem 3}, post={(elem 2,elem 4),(elem 3,elem 5)}\<rparr> :: nat Program)"


lemma domain_is_unchanged_1: 
  "{p\<^sub>1, p\<^sub>2} \<subseteq> VP \<Longrightarrow> Domain (post (p\<^sub>1 ;\<^sub>p p\<^sub>2)) \<subseteq> Domain (post p\<^sub>1)"
  by (auto simp: unsafe_composition_def)

lemma domain_is_unchanged_2: 
  "{p\<^sub>1, p\<^sub>2} \<subseteq> VP \<Longrightarrow> Domain (post (p\<^sub>1)) \<subseteq> Domain (post (p\<^sub>1 ;\<^sub>p p\<^sub>2))"
proof -
  assume a1: "{p\<^sub>1, p\<^sub>2} \<subseteq> VP"
  then have t1: "\<forall> (x,y) \<in> post p\<^sub>1. (\<exists>z. (x,z) \<in> post (p\<^sub>1 ;\<^sub>p p\<^sub>2))" sorry
  (* proof - *)
    (* (* fix x y  *) *)
    (* assume a2: "(x, y)\<in> post p\<^sub>1" *)
    (* from a1 a2 show t2: "\<exists>z. (x,z) \<in> post (p\<^sub>1 ;\<^sub>p p\<^sub>2)" *)
      (* sorry *)
  (* qed *)
  from a1 show ?thesis
    using t1 by (auto simp: Domain_iff)
qed

theorem domain_is_unchanged: 
  "{p\<^sub>1, p\<^sub>2} \<subseteq> VP \<Longrightarrow> Domain (post (p\<^sub>1 ;\<^sub>p p\<^sub>2)) = Domain (post p\<^sub>1)"
proof -
  assume a1: "{p\<^sub>1, p\<^sub>2} \<subseteq> VP"
  then have "\<forall>(x,y)\<in> post (p\<^sub>1 ;\<^sub>p p\<^sub>2). \<exists>z. (x,z) \<in> post p\<^sub>1"
    sorry
  then show ?thesis

qed



theorem domain_is_unchanged: "{p\<^sub>1, p\<^sub>2} \<subseteq> VP \<Longrightarrow> Domain (post (p\<^sub>1 ;\<^sub>p p\<^sub>2)) = Domain (post p\<^sub>1)"
proof
  assume a1: "{p\<^sub>1, p\<^sub>2} \<subseteq> VP"
  fix x assume "x \<in> Domain (post p\<^sub>1)"
  from a1 have "x \<in> Domain (post (p\<^sub>1 ;\<^sub>p p\<^sub>2))"
    apply (auto simp: unsafe_composition_def is_feasible_def ValidPrograms_def is_valid_def Field_def)

value "({(1,2)}::nat rel) O ({(2,3)} ::nat rel)"

definition restrict_p :: "'a Program \<Rightarrow> 'a elem set \<Rightarrow> 'a Program" (infix "\<sslash>\<^sub>p" 153) \<comment> \<open>D11\<close>
  where
    "restrict_p p C = \<lparr>State= State p, Pre=Pre p \<inter> C, post=post p \<sslash>\<^sub>r C\<rparr>"

definition corestrict_p :: "'a Program \<Rightarrow> 'a elem set \<Rightarrow> 'a Program" (infix "\<setminus>\<^sub>p" 154) \<comment> \<open>Definition number missing\<close>
  where
    "corestrict_p p C = \<lparr>State= State p, Pre=Pre p \<inter> Domain (post p \<setminus>\<^sub>r C), post=post p \<setminus>\<^sub>r C\<rparr>"

subsection \<open>Equivalence is maintained by operations\<close>

theorem equivalence_is_maintained_by_composition : "f\<^sub>1 \<equiv>\<^sub>p p\<^sub>1 \<Longrightarrow> f\<^sub>2 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> f\<^sub>1 ; f\<^sub>2 \<equiv>\<^sub>p p\<^sub>1 ; p\<^sub>2" \<comment> \<open>NEW\<close>
  apply (auto simp: equiv_def restr_post_def restrict_r_def composition_def corestrict_r_def)
  using mem_Collect_eq relcomp.relcompI snd_conv apply fastforce
  using mem_Collect_eq relcomp.relcompI snd_conv by fastforce

theorem equivalence_is_maintained_by_choice : "f\<^sub>1 \<equiv>\<^sub>p p\<^sub>1 \<Longrightarrow> f\<^sub>2 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> f\<^sub>1 \<union>\<^sub>p f\<^sub>2 \<equiv>\<^sub>p p\<^sub>1 \<union>\<^sub>p p\<^sub>2" \<comment> \<open>NEW\<close>
  by (auto simp: equiv_def restr_post_def restrict_r_def choice_def corestrict_r_def)

theorem equivalence_is_maintained_by_restriction : "f\<^sub>1 \<equiv>\<^sub>p p\<^sub>1 \<Longrightarrow> (f\<^sub>1 \<sslash>\<^sub>p C) \<equiv>\<^sub>p p\<^sub>1 \<sslash>\<^sub>p C" \<comment> \<open>NEW\<close>
  by (auto simp: equiv_def restr_post_def restrict_r_def restrict_p_def corestrict_r_def)

theorem equivalence_is_maintained_by_corestriction : "f\<^sub>1 \<equiv>\<^sub>p p\<^sub>1 \<Longrightarrow> (f\<^sub>1 \<setminus>\<^sub>p C) \<equiv>\<^sub>p p\<^sub>1 \<setminus>\<^sub>p C" \<comment> \<open>NEW\<close>
  by (auto simp: equiv_def restr_post_def restrict_r_def corestrict_p_def corestrict_r_def)

subsection \<open>Operations on feasibles stay feasible \<close>

theorem restrict_feasible : "is_feasible p \<Longrightarrow> is_feasible (p \<sslash>\<^sub>p C)" \<comment> \<open>T5\<close>
  by (auto simp: is_feasible_def restrict_p_def restrict_r_def Domain_def Field_def not_crashing_def)

theorem union_feasible : "is_feasible p\<^sub>1 \<and> is_feasible p\<^sub>2 \<Longrightarrow> is_feasible (p\<^sub>1 \<union>\<^sub>p p\<^sub>2)" \<comment> \<open>T3\<close>
  by (auto simp: is_feasible_def choice_def restr_post_def restrict_r_def Domain_def Field_def not_crashing_def)

theorem corestrict_feasible : "is_feasible p \<Longrightarrow> is_feasible (p \<setminus>\<^sub>p C)"
  by (auto simp: is_feasible_def corestrict_p_def Field_def corestrict_r_def not_crashing_def restrict_r_def)

theorem unsafe_compose_feasible_1: "{p\<^sub>1, p\<^sub>2} \<subseteq> VP \<Longrightarrow> is_feasible (p\<^sub>1 ;\<^sub>p p\<^sub>2) \<Longrightarrow> is_feasible p\<^sub>1"
proof -
  assume a1: "{p\<^sub>1, p\<^sub>2} \<subseteq> VP"
  assume a2: "is_feasible (p\<^sub>1 ;\<^sub>p p\<^sub>2)"
  have valid_p1: "is_valid p\<^sub>1" and valid_p2: "is_valid p\<^sub>2"
    using a1 by (auto simp: ValidPrograms_def)
  show "is_feasible p\<^sub>1"
  proof (auto simp: is_feasible_def not_crashing_def)
    have pre_p1: "Pre p\<^sub>1 \<subseteq> State p\<^sub>1"
      using valid_p1 by (simp add: is_valid_def)
    have pre_post_p1: "Pre p\<^sub>1 \<subseteq> Domain (post p\<^sub>1)"
    proof
      fix x assume "x \<in> Pre p\<^sub>1"
      hence "x \<in> Pre (p\<^sub>1 ;\<^sub>p p\<^sub>2)"
        using a2 by (auto simp: unsafe_composition_def is_feasible_def not_crashing_def)
      then show "x \<in> Domain (post p\<^sub>1)"
        using a2 by (auto simp: unsafe_composition_def restrict_r_def corestrict_r_def is_feasible_def)
    qed
    thus subgoal_1: "\<And>x. x \<in> Pre p\<^sub>1 \<Longrightarrow> x \<in> Domain (post p\<^sub>1)" by auto
    have crashed_p1: "Crashed \<notin> Pre p\<^sub>1"
      using valid_p1 by (simp add: is_valid_def)
    thus subgoal_2: "Crashed \<in> Pre p\<^sub>1 \<Longrightarrow> False" by auto
    have crashed_post_p1: "Crashed \<notin> Field (post p\<^sub>1 \<sslash>\<^sub>r Pre p\<^sub>1)"
      using a1 a2 by (auto simp: is_valid_def Field_def restrict_r_def is_feasible_def unsafe_composition_def corestrict_r_def not_crashing_def not_Pre_def ValidPrograms_def Range_def)
    from a1 a2 crashed_post_p1 crashed_p1 have "Crashed \<notin> Field (post p\<^sub>1 \<sslash>\<^sub>r Pre p\<^sub>1)"
      by (simp add: Field_def restrict_r_def)
    thus subgoal_3: "Crashed \<in> Field (post p\<^sub>1 \<sslash>\<^sub>r Pre p\<^sub>1) \<Longrightarrow> False" by auto
  qed
qed


theorem unsafe_compose_feasible_2: 
  "{p\<^sub>1, p\<^sub>2} \<subseteq> VP \<Longrightarrow> all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> Range_p p\<^sub>1 \<subseteq> Pre p\<^sub>2 \<Longrightarrow> is_feasible (p\<^sub>1 ;\<^sub>p p\<^sub>2)"
proof -
  assume a1: "{p\<^sub>1, p\<^sub>2} \<subseteq> VP"
  assume a2: "all_feasible [p\<^sub>1, p\<^sub>2]"
  assume a3: "Range_p p\<^sub>1 \<subseteq> Pre p\<^sub>2"
  have valid_p1: "is_valid p\<^sub>1" and valid_p2: "is_valid p\<^sub>2"
    using a1 by (auto simp: ValidPrograms_def)
  have feasible_p1: "is_feasible p\<^sub>1" and feasible_p2: "is_feasible p\<^sub>2"
    using a2 by auto
  show "is_feasible (p\<^sub>1 ;\<^sub>p p\<^sub>2)"
  proof (auto simp: is_feasible_def not_crashing_def)
    have pre_p1: "Pre p\<^sub>1 \<subseteq> State p\<^sub>1"
      using valid_p1 by (simp add: is_valid_def)
    have pre_p2: "Pre p\<^sub>2 \<subseteq> State p\<^sub>2"
      using valid_p2 by (simp add: is_valid_def)
    have pre_post_p1: "Pre p\<^sub>1 \<subseteq> Domain (post p\<^sub>1)"
      using feasible_p1 by (simp add: is_feasible_def)
    have pre_post_p2: "Pre p\<^sub>2 \<subseteq> Domain (post p\<^sub>2)"
      using feasible_p2 by (simp add: is_feasible_def)
    have pre_composed: "Pre (p\<^sub>1 ;\<^sub>p p\<^sub>2) = Pre p\<^sub>1"
      using pre_post_p2 pre_post_p1 pre_p1 pre_p2 valid_p1 valid_p2 a3 by (simp add: unsafe_composition_def restrict_r_def corestrict_r_def)
    from a2 a3 have "x \<in> Pre p\<^sub>1 \<Longrightarrow> x \<in> Domain {r \<in> post p\<^sub>1. snd r \<in> Pre p\<^sub>2}"
      by (auto simp: ValidPrograms_def is_valid_def is_feasible_def Range_p_def restrict_r_def not_crashing_def Field_def)
    hence "Pre (p\<^sub>1 ;\<^sub>p p\<^sub>2) \<subseteq> Domain (post p\<^sub>1 \<setminus>\<^sub>r Pre p\<^sub>2)"
      using a1 a2 a3 pre_post_p1 pre_post_p2 a3 by (auto simp: unsafe_composition_def corestrict_r_def Range_p_def restrict_r_def ValidPrograms_def is_valid_def is_feasible_def not_crashing_def Field_def)
    from a1 a2 a3 have "Pre (p\<^sub>1 ;\<^sub>p p\<^sub>2) \<subseteq> Domain (post (p\<^sub>1 ;\<^sub>p p\<^sub>2))"
    proof
      have "Pre (p\<^sub>1 ;\<^sub>p p\<^sub>2) = Pre p\<^sub>1" by (auto simp: unsafe_composition_def corestrict_r_def not_Pre_def ValidPrograms_def is_valid_def is_feasible_def Field_def not_crashing_def)
      apply (auto simp: unsafe_composition_def restrict_r_def corestrict_r_def ValidPrograms_def is_valid_def is_feasible_def not_crashing_def Field_def Range_p_def)
    thus "\<And>x. x \<in> Pre (p\<^sub>1 ;\<^sub>p p\<^sub>2) \<Longrightarrow> x \<in> Domain (post (p\<^sub>1 ;\<^sub>p p\<^sub>2))" by auto
    have crashed_pre: "Crashed \<notin> Pre (p\<^sub>1 ;\<^sub>p p\<^sub>2)"
      using valid_p1 valid_p2 by (simp add: pre_composed is_valid_def)
    hence "Crashed \<notin> Pre p\<^sub>1"
      using pre_composed by auto
    thus "Crashed \<notin> Pre (p\<^sub>1 ;\<^sub>p p\<^sub>2)"
      by (simp add: pre_composed)
    have crashed_post_p1: "Crashed \<notin> Field (post p\<^sub>1 \<sslash>\<^sub>r Pre p\<^sub>1)"
      using feasible_p1 by (simp add: is_feasible_def not_crashing_def)
    have crashed_post_p2: "Crashed \<notin> Field (post p\<^sub>2 \<sslash>\<^sub>r Pre p\<^sub>2)"
      using feasible_p2 by (simp add: is_feasible_def not_crashing_def)
    have "Crashed \<notin> Field ((post p\<^sub>1) \<sslash>\<^sub>r Pre p\<^sub>1)"
      using crashed_post_p1 by auto
    moreover have "Crashed \<notin> Field ((post p\<^sub>2) \<sslash>\<^sub>r Pre p\<^sub>2)"
      using crashed_post_p2 by auto
    ultimately have "Crashed \<notin> Field (post (p\<^sub>1 ;\<^sub>p p\<^sub>2) \<sslash>\<^sub>r Pre (p\<^sub>1 ;\<^sub>p p\<^sub>2))"
      using a1 a2 a3 crashed_post_p1 crashed_post_p2 apply (auto simp: unsafe_composition_def restrict_r_def corestrict_r_def Field_def not_Pre_def ValidPrograms_def is_feasible_def is_valid_def not_crashing_def Range_p_def)
      by (metis (no_types, lifting) Range_iff fst_conv mem_Collect_eq subset_iff)
    thus "Crashed \<notin> Field (post (p\<^sub>1 ;\<^sub>p p\<^sub>2) \<sslash>\<^sub>r Pre (p\<^sub>1 ;\<^sub>p p\<^sub>2))"
      by auto
  qed
qed




theorem unsafe_compose_feasible_2: "{p\<^sub>1, p\<^sub>2} \<subseteq> VP \<Longrightarrow> all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> Range_p p\<^sub>1 \<subseteq> Pre p\<^sub>2 \<Longrightarrow> is_feasible (p\<^sub>1 ;\<^sub>p p\<^sub>2)"
proof -
  assume a1: "all_feasible [p\<^sub>1, p\<^sub>2]"
  assume a2: "Range_p p\<^sub>1 \<subseteq> Pre p\<^sub>2"
  assume a3: "{p\<^sub>1, p\<^sub>2} \<subseteq> VP"
  have l1: "Pre (p\<^sub>1 ;\<^sub>p p\<^sub>2) = {a. \<exists>c. (a,c) \<in> post p\<^sub>1 \<and> a \<in> Pre p\<^sub>1 \<and> c \<in> Pre p\<^sub>2}"
    using a1 a2 apply (auto simp: unsafe_composition_def is_feasible_def Range_p_def restrict_r_def not_crashing_def Field_def)
    proof -
      fix x :: "'a elem"
      assume a1: "Range {r \<in> post p\<^sub>1. fst r \<in> Pre p\<^sub>1} \<subseteq> Pre p\<^sub>2"
      assume a2: "Pre p\<^sub>1 \<subseteq> Domain (post p\<^sub>1)"
      assume a3: "x \<in> Pre p\<^sub>1"
      then have "x \<in> Domain (post p\<^sub>1)"
        using a2 by blast
      then have f4: "x \<in> Domain {p \<in> post p\<^sub>1. fst p \<in> Pre p\<^sub>1}"
        using a3 by fastforce
      have "Range {p \<in> post p\<^sub>1. fst p \<in> Pre p\<^sub>1} \<subseteq> Pre p\<^sub>2"
        using a1 by (metis (lifting))
      then show "\<exists>e. (x, e) \<in> post p\<^sub>1 \<and> e \<in> Pre p\<^sub>2"
        using f4 by blast
    qed
  from a1 a2 a3 have l2: "Domain (post (p\<^sub>1 ;\<^sub>p p\<^sub>2)) = {a. \<exists>c. (a,c) \<in> post p\<^sub>1 \<and> c \<in> Pre p\<^sub>2}"
    apply (auto simp: unsafe_composition_def corestrict_r_def ValidPrograms_def is_valid_def is_feasible_def not_crashing_def Field_def restrict_r_def not_Pre_def)
    proof -
      from a1 a2 have l2_0: "Crashed \<notin> Range_p p\<^sub>1"
        by (auto simp: is_feasible_def not_crashing_def Range_p_def)
      from a1 a2 a3 have l2_a: "Crashed \<notin> Pre p\<^sub>2"
        by (simp add: is_feasible_def not_crashing_def)
      from a2 have l2_b: "(a, b) \<in> post p\<^sub>1 \<Longrightarrow> a \<in> Pre p\<^sub>1 \<Longrightarrow> b \<in> Pre p\<^sub>2"
        apply (auto simp: Range_p_def restrict_r_def)
        by (simp add: Range.intros subset_iff)
      from a1 a2 a3 l2_0 l2_a have l2_c: "{a. \<exists>b. (a, b) \<in> post p\<^sub>1 \<and> a \<in> Pre p\<^sub>1 \<and> b \<notin> Pre p\<^sub>2} = {}"
        apply (auto simp: ValidPrograms_def is_valid_def is_feasible_def not_crashing_def Range_p_def restrict_r_def Field_def)
        by fastforce
      from a1 a2 a3 l2_0 l2_a l2_b l2_c have l2_1: "post (p\<^sub>1 ;\<^sub>p p\<^sub>2) \<equiv> {(a,b). \<exists>c. (a,c) \<in> post p\<^sub>1 \<and> (c,b) \<in> post p\<^sub>2 \<and> c \<in> Pre p\<^sub>2}"
        apply (auto simp: Range_p_def restr_post_def is_feasible_def unsafe_composition_def not_crashing_def ValidPrograms_def restrict_r_def corestrict_r_def is_valid_def Field_def relcompp_apply not_Pre_def)
        sorry
      then have l2_2: "Domain (post (p\<^sub>1 ;\<^sub>p p\<^sub>2)) = {a. \<exists>b c. (a,c) \<in> post p\<^sub>1 \<and> (c,b) \<in> post p\<^sub>2 \<and> c \<in> Pre p\<^sub>2}"
        using a1 a2 by (auto simp: l2_1)
      then show "Domain (post (p\<^sub>1 ;\<^sub>p p\<^sub>2)) = {a. \<exists>c. (a,c) \<in> post p\<^sub>1 \<and> c \<in> Pre p\<^sub>2}"
        apply (auto simp: l2_2)
        using a1 a2 l2_1 apply auto[1]
        using a1 a2 apply (auto simp: is_feasible_def)
        by (smt (verit, del_insts) Domain.cases a1 l2_2 mem_Collect_eq subsetD)
    qed
  have l3: "{a. \<exists>c. (a,c) \<in> post p\<^sub>1 \<and> a \<in> Pre p\<^sub>1 \<and> c \<in> Pre p\<^sub>2} \<subseteq> {a. \<exists>c. (a,c) \<in> post p\<^sub>1 \<and> c \<in> Pre p\<^sub>2}"
    by auto
  have l4: "Pre (p\<^sub>1 ;\<^sub>p p\<^sub>2) \<subseteq>  Domain (post (p\<^sub>1 ;\<^sub>p p\<^sub>2))"
    using a1 a2 l1 l2 by auto
  from a1 have l5: "not_crashing (p\<^sub>1 ;\<^sub>p p\<^sub>2)"
    apply (auto simp: unsafe_composition_def Field_def is_feasible_def not_crashing_def restrict_r_def corestrict_r_def)
    (* apply (smt (verit) Domain.DomainI corestriction_restriction_on_relcomp relcomp.cases relcomp.relcompI) *)
    sorry
  show "is_feasible (p\<^sub>1 ;\<^sub>p p\<^sub>2)"
    by (simp add: is_feasible_def l4 l5)
qed

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

theorem compose_feasible: "all_feasible [p\<^sub>1, p\<^sub>2] \<Longrightarrow> is_feasible (p\<^sub>1 ; p\<^sub>2)" \<comment> \<open>T4\<close>
proof -
  assume a1: "all_feasible [p\<^sub>1, p\<^sub>2]"
  have state_prop: "S (p\<^sub>1 ; p\<^sub>2) = S p\<^sub>1 \<union> S p\<^sub>2"
    by (auto simp: composition_def S_def Field_def corestrict_r_def)
  from a1 state_prop have no_crash: "Crashed \<notin> S (p\<^sub>1 ; p\<^sub>2)"
    by (auto simp: is_feasible_def)
  have pre_feas: "Pre (p\<^sub>1 ; p\<^sub>2) \<subseteq> Domain (post (p\<^sub>1 ; p\<^sub>2))"
    by (metis Int_iff a1 composition_def compose_feasible_lemma select_convs(2) select_convs(3) subsetI)
  from pre_feas no_crash show "is_feasible (p\<^sub>1 ; p\<^sub>2)"
    by (auto simp: is_feasible_def)
qed
  

subsection \<open>Operation properties \<close>

theorem choice_commute: "p\<^sub>1 \<union>\<^sub>p p\<^sub>2 = p\<^sub>2 \<union>\<^sub>p p\<^sub>1" \<comment> \<open>T6\<close>
  by (auto simp: choice_def)

theorem choice_assoc : "(p\<^sub>1 \<union>\<^sub>p p\<^sub>2) \<union>\<^sub>p p\<^sub>3 \<triangleq> p\<^sub>1 \<union>\<^sub>p (p\<^sub>2 \<union>\<^sub>p p\<^sub>3)" \<comment> \<open>T7\<close>
  by (auto simp: equal_def S_def choice_def restr_post_def restrict_r_def Field_def)
 

theorem compose_assoc : "(p\<^sub>1 ; p\<^sub>2) ; p\<^sub>3 \<triangleq> p\<^sub>1 ; (p\<^sub>2 ; p\<^sub>3)" \<comment> \<open>T8\<close>
proof -
  have compose_assoc_S: "S (p\<^sub>1 ; (p\<^sub>2 ; p\<^sub>3)) = S ((p\<^sub>1 ; p\<^sub>2) ; p\<^sub>3)"
    proof -
      have compose_assoc_S_1: "\<forall> f\<^sub>1 f\<^sub>2. S f\<^sub>1 \<subseteq> S (f\<^sub>1 ; f\<^sub>2)"
        by (auto simp: composition_def corestrict_r_def S_def)
    
      have compose_assoc_S_2: "\<forall> f\<^sub>1 f\<^sub>2. S f\<^sub>2 \<subseteq> S (f\<^sub>1 ; f\<^sub>2)"
        by (auto simp: composition_def corestrict_r_def S_def)
    
      have compose_assoc_S_3: "\<forall> f\<^sub>1 f\<^sub>2. S (f\<^sub>1 ; f\<^sub>2) = S f\<^sub>1 \<union> S f\<^sub>2"
        apply (auto)
        by (auto simp: S_def Field_def composition_def corestrict_r_def)
    
      have compose_assoc_S_4: "\<forall> f\<^sub>1 f\<^sub>2 f\<^sub>3. S (f\<^sub>1 ; (f\<^sub>2 ; f\<^sub>3)) = S f\<^sub>1 \<union> S f\<^sub>2 \<union> S f\<^sub>3"
        by (auto simp: compose_assoc_S_3)
      
      show ?thesis
        by (metis compose_assoc_S_3 compose_assoc_S_4)
    qed

  have compose_assoc_pre: "Pre (p\<^sub>1 ; (p\<^sub>2 ; p\<^sub>3)) = Pre ((p\<^sub>1 ; p\<^sub>2) ; p\<^sub>3)"
    proof -
      have compose_assoc_pre_1: "Pre ((p\<^sub>1 ; p\<^sub>2) ; p\<^sub>3) = {x.\<exists>y z. x \<in> Pre p\<^sub>1 \<and> (x,y) \<in> post p\<^sub>1 \<and> y \<in> Pre p\<^sub>2 \<and> (y,z) \<in> post p\<^sub>2 \<and> z \<in> Pre p\<^sub>3}"
        apply (auto simp: composition_def corestrict_r_def)
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
        apply (auto simp: composition_def corestrict_r_def)
        apply (auto)
        by fastforce
      have compose_assoc_post_2: "post ((p\<^sub>1 ; p\<^sub>2) ; p\<^sub>3) = {(a,d). \<exists>b c. (a,b) \<in> post p\<^sub>1 \<and> b \<in> Pre p\<^sub>2 \<and> (b,c) \<in> post p\<^sub>2 \<and> c \<in> Pre p\<^sub>3 \<and> (c,d) \<in> post p\<^sub>3}"
        apply (auto simp: composition_def corestrict_r_def)
        apply (auto)
        by fastforce
      show ?thesis
        by (auto simp: compose_assoc_post_1 compose_assoc_post_2)
    qed

  show ?thesis
    by (auto simp: equal_def compose_assoc_pre compose_assoc_post compose_assoc_S)
qed


theorem unsafe_compose_assoc: "(p\<^sub>1 ;\<^sub>p p\<^sub>2) ;\<^sub>p p\<^sub>3 \<triangleq> p\<^sub>1 ;\<^sub>p (p\<^sub>2 ;\<^sub>p p\<^sub>3)"
proof -
  have compose_assoc_S_3: "\<forall> f\<^sub>1 f\<^sub>2. S (f\<^sub>1 ; f\<^sub>2) = S f\<^sub>1 \<union> S f\<^sub>2"
    apply (auto)
    by (auto simp: S_def Field_def composition_def corestrict_r_def)
  show ?thesis
    apply (simp add: unsafe_composition_def equal_def)
    by (smt (z3) O_assoc S_def compose_assoc_S_3 composition_def corestriction_restriction_on_relcomp select_convs(1) select_convs(2) select_convs(3) sup.right_idem sup_assoc sup_commute)
qed

theorem restrict_inter: "(p\<sslash>\<^sub>pC\<^sub>1)\<sslash>\<^sub>pC\<^sub>2 = p\<sslash>\<^sub>p(C\<^sub>1 \<inter> C\<^sub>2)" \<comment> \<open>T9\<close>
  by (auto simp: equal_def S_def Field_def restrict_p_def restrict_r_def)

theorem restrict_commute : "(p\<sslash>\<^sub>pC\<^sub>1)\<sslash>\<^sub>pC\<^sub>2 = (p\<sslash>\<^sub>pC\<^sub>2)\<sslash>\<^sub>pC\<^sub>1" \<comment> \<open>T10\<close>
  by (auto simp: equal_def S_def Field_def restrict_p_def restrict_r_def)

theorem restrict_distrib : "(p\<^sub>1 \<union>\<^sub>p p\<^sub>2)\<sslash>\<^sub>pC = (p\<^sub>1\<sslash>\<^sub>pC \<union>\<^sub>p p\<^sub>2\<sslash>\<^sub>pC)" \<comment> \<open>T11\<close>
  by (auto simp: equal_def S_def Field_def restrict_p_def restrict_r_def choice_def restr_post_def)

theorem compose_absorb : "(p\<^sub>1;p\<^sub>2)\<sslash>\<^sub>pC = p\<^sub>1\<sslash>\<^sub>pC;p\<^sub>2" \<comment> \<open>T12\<close>
  by (auto simp: equal_def S_def Field_def composition_def restrict_p_def restrict_r_def corestrict_r_def)

theorem unsafe_compose_absorb : "(p\<^sub>1;\<^sub>pp\<^sub>2)\<sslash>\<^sub>pC = p\<^sub>1\<sslash>\<^sub>pC;\<^sub>pp\<^sub>2"
  by (auto simp: equal_def S_def Field_def unsafe_composition_def restrict_p_def restrict_r_def corestrict_r_def)

lemma NOT_compose_distrib1_3: "q;(p\<^sub>1\<union>\<^sub>pp\<^sub>2) = (q;p\<^sub>1) \<union>\<^sub>p (q;p\<^sub>2)" \<comment> \<open>Does not hold\<close>
  oops

theorem compose_distrib1_3 : "q;(p\<^sub>1\<union>\<^sub>pp\<^sub>2) \<equiv>\<^sub>p (q;p\<^sub>1) \<union>\<^sub>p (q;p\<^sub>2)" \<comment> \<open>T13\<close>
  by (auto simp: choice_def equiv_def restr_post_def restrict_r_def composition_def corestrict_r_def)

theorem unsafe_compose_distrib1_3 : "q;\<^sub>p(p\<^sub>1\<union>\<^sub>pp\<^sub>2) \<equiv>\<^sub>p (q;\<^sub>pp\<^sub>1) \<union>\<^sub>p (q;\<^sub>pp\<^sub>2)"
  by (auto simp: choice_def equiv_def restr_post_def restrict_r_def unsafe_composition_def corestrict_r_def)

theorem compose_distrib2 : "(p\<^sub>1\<union>\<^sub>pp\<^sub>2);q \<equiv>\<^sub>p (p\<^sub>1;q) \<union>\<^sub>p (p\<^sub>2;q)" \<comment> \<open>T14\<close>
  by (auto simp: choice_def equiv_def restr_post_def restrict_r_def composition_def corestrict_r_def)

theorem unsafe_compose_distrib2 : "(p\<^sub>1\<union>\<^sub>pp\<^sub>2);\<^sub>pq \<equiv>\<^sub>p (p\<^sub>1;\<^sub>pq) \<union>\<^sub>p (p\<^sub>2;\<^sub>pq)"
  by (auto simp: choice_def equiv_def restr_post_def restrict_r_def unsafe_composition_def corestrict_r_def)

theorem choice_distributes_over_composition : "q\<union>\<^sub>p(p\<^sub>1;p\<^sub>2) \<equiv>\<^sub>p (q\<union>\<^sub>pp\<^sub>1) ; (q\<union>\<^sub>pp\<^sub>2)" \<comment> \<open>Does not hold. Line: 143\<close>
  oops

theorem corestriction_restriction_on_composition : "p\<^sub>1 \<setminus>\<^sub>p s\<^sub>1 ; p\<^sub>2 = p\<^sub>1 ; p\<^sub>2 \<sslash>\<^sub>p s\<^sub>1" \<comment> \<open>NEW\<close>
  by (auto simp: restrict_p_def corestrict_p_def composition_def corestrict_r_def restrict_r_def S_def Field_def)

theorem composition_simplification : "p\<^sub>1 ; p\<^sub>2 = p\<^sub>1 ; p\<^sub>2 \<sslash>\<^sub>p Pre p\<^sub>2"
  by (auto simp: restrict_p_def composition_def corestrict_r_def restrict_r_def S_def Field_def)

subsubsection \<open>Characteristic relation NEW\<close>

definition char_rel :: "'a Program \<Rightarrow> 'a elem rel"
  where
    "char_rel p = post p \<sslash>\<^sub>r Pre p"

theorem char_rel_is_unique_in_equiv: "p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<Longrightarrow> char_rel p\<^sub>1 = char_rel p\<^sub>2"
  by (auto simp: char_rel_def equiv_def restr_post_def)

theorem char_rel_choice: "char_rel (p\<^sub>1 \<union>\<^sub>p p\<^sub>2) = char_rel p\<^sub>1 \<union> char_rel p\<^sub>2"
  by (auto simp: char_rel_def choice_def restrict_r_def restr_post_def)

theorem char_rel_composition: "char_rel (p\<^sub>1 ; p\<^sub>2) = char_rel p\<^sub>1 O char_rel p\<^sub>2"
  by (auto simp: char_rel_def composition_def restrict_r_def corestrict_r_def)

theorem char_rel_restriction: "char_rel (p \<sslash>\<^sub>p C) = char_rel p \<sslash>\<^sub>r C"
  by (auto simp: char_rel_def restrict_p_def restrict_r_def)

theorem char_rel_corestriction: "char_rel (p \<setminus>\<^sub>p C) = char_rel p \<setminus>\<^sub>r C"
  by (auto simp: char_rel_def corestrict_p_def corestrict_r_def restrict_r_def)

theorem char_rel_strengthens: "strengthens p\<^sub>1 p\<^sub>2 \<Longrightarrow> char_rel p\<^sub>1 \<sslash>\<^sub>r Pre p\<^sub>2 \<subseteq> char_rel p\<^sub>2"
  by (auto simp: strengthens_def char_rel_def restrict_r_def)

subsection \<open>Basic programs\<close>

definition Fail :: "'a elem set \<Rightarrow> 'a Program"
  where
    "Fail s = \<lparr> State = s, Pre = {}, post = {}\<rparr>"

definition Havoc :: "'a elem set \<Rightarrow> 'a Program"
  where
    "Havoc s = \<lparr> State = s, Pre = {x. x \<in> s \<and> x \<noteq> Crashed}, post = {(x,y). x \<in> s \<and> y \<in> s \<and> x \<noteq> Crashed \<and> y \<noteq> Crashed}\<rparr>"

definition Skip :: "'a elem set \<Rightarrow> 'a Program"
  where
    "Skip s = \<lparr> State = s, Pre = {x. x \<in> s \<and> x \<noteq> Crashed}, post = {(x,y). x \<in> s \<and> x = y \<and> x \<noteq> Crashed} \<rparr>"

subsection \<open>Basic programs properties\<close>

theorem fail_is_feasible: "is_feasible (Fail s)"
  by (auto simp: is_feasible_def Fail_def)

theorem havoc_is_feasible: "is_feasible (Havoc s)"
  by (auto simp: is_feasible_def Havoc_def)

theorem skip_is_feasible: "is_feasible (Skip s)"
  by (auto simp: is_feasible_def Skip_def)

definition is_total :: "'a Program \<Rightarrow> bool"
  where
    "is_total p \<equiv> unpack (Pre p) = unpack (S p)"

theorem skip_is_total: "is_total (Skip s)"
  by (auto simp: is_total_def S_def Field_def Skip_def unpack_def)

theorem havoc_is_total: "is_total (Havoc s)"
  by (auto simp: is_total_def Havoc_def S_def unpack_def Field_def)

theorem no_pre_is_fail: "Pre p = {} \<Longrightarrow> Fail s \<equiv>\<^sub>p p" \<comment> \<open>NEW\<close>
  by (auto simp: Fail_def equiv_def restr_post_def restrict_r_def)

subsection \<open>Basic program interactions\<close>

subsubsection \<open>Skip is neutral element of composition.\<close>
lemma skip_compose_r_S: "S (p ; Skip (S p)) = S p"
  by (auto simp: S_def Skip_def Field_def composition_def corestrict_r_def)

lemma skip_compose_r_post: "is_feasible p \<Longrightarrow> post (p ; Skip (S p)) = post p"
  by (auto simp: S_def Skip_def Field_def composition_def corestrict_r_def relcomp_def is_feasible_def)

lemma skip_compose_r_Pre_1: "Pre (p ; Skip (S p)) = (Pre p \<inter> Domain (post p))"
  by (auto simp: Skip_def S_def Field_def composition_def corestrict_r_def Range_def Domain_def)

lemma skip_compose_r_Pre_2: "is_feasible p \<Longrightarrow> Pre p = Pre p \<inter> Domain (post p)"
  by (meson inf.orderE is_feasible_def)

lemma skip_compose_r_Pre_3: "is_feasible p \<Longrightarrow> Pre (p ; Skip (S p)) = Pre p"
  by (metis skip_compose_r_Pre_1 skip_compose_r_Pre_2)

theorem skip_makes_feasible: "is_feasible (p ; Skip (S p))" \<comment> \<open>NEW\<close>
  by (simp add: is_feasible_def skip_compose_r_Pre_1 skip_compose_r_post)

theorem skip_compose_r: "is_feasible p \<Longrightarrow> p ; Skip (S p) \<triangleq> p" \<comment> \<open>T15 NEW\<close>
  by (simp add: equal_def skip_compose_r_Pre_3 skip_compose_r_S skip_compose_r_post)

lemma skip_compose_l_S: "S (Skip (S p) ; p) = S p"
  by (auto simp: S_def Skip_def Field_def composition_def corestrict_r_def)

lemma skip_compose_l_Pre: "Pre (Skip (S p) ; p) = Pre p"
  by (auto simp: S_def Skip_def Field_def composition_def corestrict_r_def relcomp_def)

lemma skip_compose_l_post: "post (Skip (S p) ; p) = post p \<sslash>\<^sub>r Pre p"
  by (auto simp: Skip_def restrict_r_def S_def composition_def corestrict_r_def)

lemma skip_compose_l_1: "Skip (S p) ; p \<triangleq> \<lparr> State = S p, Pre = Pre p, post = post p \<sslash>\<^sub>r Pre p\<rparr>" \<comment> \<open>NEW\<close>
  apply (auto simp: equal_def skip_compose_l_Pre skip_compose_l_post skip_compose_l_S)
  by (auto simp: composition_def corestrict_r_def S_def Field_def restrict_r_def)

theorem skip_compose_l: "Skip (S p) ; p \<equiv>\<^sub>p p" \<comment> \<open>T15 NEW\<close>
  by (auto simp: equiv_def restr_post_def restrict_r_def skip_compose_l_Pre skip_compose_l_post)

subsubsection \<open>Fail is neutral element of choice.\<close>

theorem NOT_fail_union_r: "p \<union>\<^sub>p Fail (S p) \<triangleq> p"
  oops

theorem fail_union_r: "p \<union>\<^sub>p Fail (S p) \<equiv>\<^sub>p p" \<comment> \<open>T16 NEW\<close>
  by (auto simp: equiv_def choice_def Fail_def restr_post_def restrict_r_def) 

theorem NOT_fail_union_l: "Fail (S p) \<union>\<^sub>p p \<triangleq> p"
  oops

theorem fail_union_l: "Fail (S p) \<union>\<^sub>p p \<equiv>\<^sub>p p" \<comment> \<open>T16 NEW\<close>
  by (auto simp: equiv_def choice_def Fail_def restr_post_def restrict_r_def)

subsubsection \<open>Fail is fix-point of composition.\<close>

theorem fail_compose_l: "Fail (S p) ; p = Fail (S p)" \<comment> \<open>T17\<close>
  by (auto simp: Fail_def composition_def S_def corestrict_r_def)

theorem fail_compose_r: "p ; Fail (S p) = Fail (S p)" \<comment> \<open>T17\<close>
  by (auto simp: Fail_def composition_def S_def corestrict_r_def)

subsubsection \<open>Havoc is fix-point of choice.\<close>

theorem havoc_union_l: "Havoc (S p) \<union>\<^sub>p p = Havoc (S p)" \<comment> \<open>T17\<close>
  by (auto simp: Havoc_def choice_def restr_post_def restrict_r_def S_def Field_def)

theorem havoc_union_r: "p \<union>\<^sub>p Havoc (S p) = Havoc (S p)" \<comment> \<open>T17\<close>
  by (auto simp: Havoc_def choice_def restr_post_def restrict_r_def S_def Field_def)

subsubsection \<open>Havoc absorrebs postcondition from right on composition.\<close>

lemma havoc_pre_State: "State (p ; Havoc (S p)) = State (Havoc (S p) \<sslash>\<^sub>p Pre p)"
  by (simp add: composition_def Havoc_def restrict_p_def S_def)

lemma havoc_pre_S: "S (p ; Havoc (S p)) = S (Havoc (S p) \<sslash>\<^sub>p Pre p)"
  apply (simp add: composition_def Havoc_def restrict_p_def S_def corestrict_r_def)
  by (auto simp: Field_def restrict_r_def)

lemma NOT_havoc_pre_Pre: "Pre (p ; Havoc (S p)) = Pre (Havoc (S p) \<sslash>\<^sub>p Pre p)"
  oops

lemma havoc_pre_Pre: "is_feasible p \<Longrightarrow> Pre (p ; Havoc (S p)) = Pre (Havoc (S p) \<sslash>\<^sub>p Pre p)"
  apply (simp add: is_feasible_def composition_def Havoc_def restrict_p_def corestrict_r_def S_def Field_def)
  using mem_Collect_eq prod.collapse 
  by force

lemma NOT_havoc_pre_post_1: "post (p ; Havoc (S p)) = post (Havoc (S p) \<sslash>\<^sub>p Pre p)" \<comment> \<open>NEW\<close>
  oops

lemma NOT_havoc_pre_post_1: "is_feasible p \<Longrightarrow> post (p ; Havoc (S p)) = post (Havoc (S p) \<sslash>\<^sub>p Pre p)" \<comment> \<open>NEW\<close>
  oops

lemma havoc_pre_post: "is_feasible p \<Longrightarrow> post (p ; Havoc (S p))\<sslash>\<^sub>r Pre p = post (Havoc (S p) \<sslash>\<^sub>p Pre p)"
  apply (auto simp: is_feasible_def composition_def corestrict_r_def restrict_r_def Havoc_def restrict_p_def relcomp_def)
  apply (simp add: S_def)
  apply (simp add: S_def Field_def Domain_def Range_def)
  apply (auto simp: relcompp_apply subset_iff)
  apply force
  apply force
  apply force
  by force

theorem NOT_havoc_pre: "p ; Havoc (S p) \<equiv>\<^sub>p Havoc (S p) \<sslash>\<^sub>p Pre p" \<comment> \<open>T19\<close>
  oops


theorem havoc_from_right: "is_feasible p \<Longrightarrow> (p ; Havoc (S p)) \<equiv>\<^sub>p Havoc (S p) \<sslash>\<^sub>p Pre p" \<comment> \<open>T19 NEW\<close>
  apply (auto simp: equiv_def havoc_pre_Pre)
  apply (metis Int_Un_eq(3) Un_Int_eq(1) choice_def havoc_pre_Pre havoc_pre_post havoc_union_r restr_post_def restrict_p_def restrict_inter select_convs(2) select_convs(3))
  by (metis Int_Un_eq(3) Un_Int_eq(1) choice_def havoc_pre_Pre havoc_pre_post havoc_union_r restr_post_def restrict_p_def restrict_inter select_convs(2) select_convs(3))

(* lemma havoc_absorbs_post_from_left_Pre: "is_feasible p \<Longrightarrow> Pre (Havoc (S p) ; p) = Pre (Havoc (S p) \<setminus>\<^sub>p Pre p)" *)
  (* by (simp add: is_feasible_def composition_def Havoc_def corestrict_p_def) *)

lemma havoc_from_left_S: "is_feasible p \<Longrightarrow> S (Havoc (S p) ; p) = S(Havoc (S p) \<setminus>\<^sub>p Range_p (p))"
  by (auto simp: is_feasible_def S_def composition_def corestrict_p_def corestrict_r_def Havoc_def Field_def)

lemma havoc_from_left_Pre: "is_feasible p \<Longrightarrow> \<not>p \<equiv>\<^sub>p Fail (S p) \<Longrightarrow> Pre (Havoc (S p) ; p) = S p"
  by (auto simp: is_feasible_def composition_def corestrict_p_def corestrict_r_def Field_def Range_p_def restrict_r_def Havoc_def Fail_def equiv_def restr_post_def S_def)

lemma havoc_from_left_post: "is_feasible p \<Longrightarrow> post (Havoc (S p) ; p) = post (Havoc (S p) \<setminus>\<^sub>p Range_p (p))"
  by (auto simp: is_feasible_def corestrict_p_def corestrict_r_def Range_p_def restrict_r_def S_def composition_def Havoc_def Field_def)



theorem havoc_from_left: "is_feasible p \<Longrightarrow> \<not>p \<equiv>\<^sub>p Fail (S p) \<Longrightarrow> Havoc (S p) ; p \<equiv>\<^sub>p Havoc (S p) \<setminus>\<^sub>p Range_p p"
proof -
  assume a1: "is_feasible p"
  assume a2: "\<not>p \<equiv>\<^sub>p Fail (S p)"
  let ?left = "Havoc (S p) ; p"
  let ?right = "Havoc (S p) \<setminus>\<^sub>p Range_p p"

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

  have l1: "S ?left = S ?right"
    by (simp add: a1 havoc_from_left_S)

  have lg: "Range_p p \<noteq> {} \<Longrightarrow> Pre ?right = S p"
    by (auto simp: Range_p_def restrict_r_def Havoc_def corestrict_p_def corestrict_r_def S_def Field_def Range_def Domain_def)

  have l2: "Pre ?left = Pre ?right"
  proof -
    have l2_1: "Pre ?left = S p"
      by (simp add: a1 a2 havoc_from_left_Pre)
    have l2_2: "Pre ?right = S p"
      by (simp add: la lg)
    show ?thesis
      using l2_1 l2_2 by blast
  qed

  have l4: "s \<in> S p \<Longrightarrow> t \<in> Range_p p \<Longrightarrow> (s,t) \<in> restr_post ?left"
    using a1 a2 by (auto simp: corestrict_p_def restr_post_def restrict_r_def corestrict_r_def Havoc_def Fail_def is_feasible_def S_def Range_p_def composition_def)

  have l5: "s \<in> S p \<Longrightarrow> t \<in> Range_p p \<Longrightarrow> (s,t) \<in> restr_post ?right"
    apply (auto simp: equiv_def is_feasible_def Havoc_def Fail_def composition_def corestrict_r_def restr_post_def S_def corestrict_p_def restrict_r_def Range_p_def Field_def relcomp_def)
    apply (smt (z3) Domain.DomainI Range.intros mem_Collect_eq mem_Sigma_iff snd_conv split_pairs)
      apply (smt (z3) Domain.DomainI Range.intros mem_Collect_eq mem_Sigma_iff snd_conv split_pairs)
    by (auto simp: Range_def Domain_def)
    
  have l3: "restr_post ?left = restr_post ?right"
    by (metis a1 havoc_from_left_post l2 restr_post_def)

  have l6: "?left \<equiv>\<^sub>p ?right"
    by (simp add: equiv_def l2 l3)

  show "Havoc (S p) ; p \<equiv>\<^sub>p Havoc (S p) \<setminus>\<^sub>p Range_p p"
    using l6 by simp
qed



theorem restrict_refine: "p \<subseteq>\<^sub>p p \<sslash>\<^sub>p C" \<comment> \<open>T20\<close>
  by (auto simp: refines_def extends_def weakens_def strengthens_def restrict_p_def restrict_r_def S_def Field_def)

theorem NOT_corestricted_p_refines_p: "p \<setminus>\<^sub>p C \<subseteq>\<^sub>p p"
  oops \<comment> \<open>Not true as corestriction might remove a post relation completely\<close>

theorem NOT_p_refines_corestricted_p: "p \<subseteq>\<^sub>p p \<setminus>\<^sub>p C"
  oops \<comment> \<open>Not true as corestriction might remove a post ambiguity\<close>

theorem order_reversal: "D \<subseteq> C \<Longrightarrow> p \<sslash>\<^sub>p C \<subseteq>\<^sub>p p \<sslash>\<^sub>p D" \<comment> \<open>T21\<close>
  by (auto simp: refines_def extends_def weakens_def strengthens_def restrict_p_def restrict_r_def S_def Field_def)

theorem refinement_safety_restriction: "q \<subseteq>\<^sub>p p \<Longrightarrow> q \<sslash>\<^sub>p C \<subseteq>\<^sub>p p \<sslash>\<^sub>p C" \<comment> \<open>T22\<close>
  by (auto simp: refines_def extends_def weakens_def strengthens_def restrict_p_def restrict_r_def S_def Field_def)

theorem refinement_safety_restriction2: "q \<subseteq>\<^sub>p p \<Longrightarrow> D \<subseteq> C \<Longrightarrow> q \<sslash>\<^sub>p C \<subseteq>\<^sub>p p \<sslash>\<^sub>p D"
proof -
  assume a1: "q \<subseteq>\<^sub>p p"
  assume a2: "D \<subseteq> C"
  have "q \<sslash>\<^sub>p C \<subseteq>\<^sub>p p \<sslash>\<^sub>p C"
    using a1 refinement_safety_restriction by auto
  then show ?thesis
    using a2 by (metis (no_types) order_reversal refines_is_order)
qed

(* lemma refinement_safety_choice_Pre: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> Pre (p\<^sub>1 \<union>\<^sub>p p\<^sub>2) \<subseteq> Pre (q\<^sub>1 \<union>\<^sub>p q\<^sub>2)" *)
  (* by (auto simp: refines_def extends_def weakens_def strengthens_def restrict_r_def choice_def) *)

(* lemma refinement_safety_choice_S: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> S (p\<^sub>1 \<union>\<^sub>p p\<^sub>2) \<subseteq> S (q\<^sub>1 \<union>\<^sub>p q\<^sub>2)" *)
  (* apply (auto simp: refines_def extends_def weakens_def strengthens_def restrict_r_def choice_def) *)
  (* by (auto simp: S_def restr_post_def restrict_r_def Field_def) *)

lemma refinement_safety_choice_e: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> extends (q\<^sub>1 \<union>\<^sub>p q\<^sub>2) (p\<^sub>1 \<union>\<^sub>p p\<^sub>2)"
  by (auto simp: refines_def extends_def choice_def restr_post_def restrict_r_def S_def Field_def)

lemma refinement_safety_choice_w: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> weakens (q\<^sub>1 \<union>\<^sub>p q\<^sub>2) (p\<^sub>1 \<union>\<^sub>p p\<^sub>2)"
  by (auto simp: refines_def weakens_def choice_def restr_post_def restrict_r_def)

lemma refinement_safety_choice_s: "strengthens q\<^sub>1 p\<^sub>2 \<Longrightarrow> strengthens q\<^sub>2 p\<^sub>1 \<Longrightarrow> q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> strengthens (q\<^sub>1 \<union>\<^sub>p q\<^sub>2) (p\<^sub>1 \<union>\<^sub>p p\<^sub>2)"
  by (auto simp: refines_def strengthens_def choice_def restr_post_def restrict_r_def)
  
lemma refinement_safety_choice: "strengthens q\<^sub>1 p\<^sub>2 \<Longrightarrow> strengthens q\<^sub>2 p\<^sub>1 \<Longrightarrow> q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> (q\<^sub>1 \<union>\<^sub>p q\<^sub>2) \<subseteq>\<^sub>p (p\<^sub>1 \<union>\<^sub>p p\<^sub>2)" \<comment> \<open>NEW T23 weak\<close>
  by (simp add: refinement_safety_choice_e refinement_safety_choice_s refinement_safety_choice_w refines_def)


text \<open>Refinement seems to not be refinement-safe without serious assumptions. As I was not able to prove it even with the following commented out assumptions\<close>
(* lemma refinement_safety_composition_e: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> extends (q\<^sub>1 ; q\<^sub>2) (p\<^sub>1 ; p\<^sub>2)" *)
  (* by (auto simp: composition_def refines_def extends_def corestrict_r_def S_def Field_def) *)

(* lemma refinement_safety_composition_w_1: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> Pre (q\<^sub>1 ; q\<^sub>2) = {a. a \<in> Pre q\<^sub>1 \<and> (\<exists> b. b \<in> Pre q\<^sub>2 \<and> (a,b) \<in> post q\<^sub>1 \<and> (a \<in> Pre p\<^sub>1 \<longrightarrow> (a,b) \<in> post p\<^sub>1) \<and> ((a,b) \<in> post q\<^sub>2 \<longrightarrow> (a,b) \<in> post q\<^sub>2))}"  *)
  (* apply (auto simp: refines_def weakens_def composition_def corestrict_r_def strengthens_def restrict_r_def) *)
  (* by force *)

(* lemma refinement_safety_composition_w_2: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> Pre (p\<^sub>1 ; p\<^sub>2) = {a. a \<in> Pre q\<^sub>1 \<and> a \<in> Pre p\<^sub>1 \<and> (\<exists> b. b \<in> Pre p\<^sub>2 \<and> (a,b) \<in> post p\<^sub>1)}" *)
  (* by (auto simp: refines_def composition_def corestrict_r_def weakens_def strengthens_def restrict_r_def) *)

(* lemma refinement_safety_composition_w_3: "all_feasible [q\<^sub>1, p\<^sub>1, q\<^sub>2, p\<^sub>2] \<Longrightarrow> q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> Pre (p\<^sub>1 ; p\<^sub>2) \<subseteq> Pre (q\<^sub>1 ; q\<^sub>2)" *)
  (* apply (auto simp: is_feasible_def refinement_safety_composition_w_1 refinement_safety_composition_w_2) *)
  (* oops *)

(* lemma refinement_safety_composition_w: "all_feasible [q\<^sub>1, p\<^sub>1, q\<^sub>2, p\<^sub>2] \<Longrightarrow> q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> weakens (q\<^sub>1 ; q\<^sub>2) (p\<^sub>1 ; p\<^sub>2)" *)
  (* apply (auto simp: refines_def weakens_def composition_def corestrict_r_def strengthens_def restrict_r_def independant_def relcomp_def relcompp_apply is_feasible_def) *)
  (* oops *)

(* lemma refinement_safety_composition_s: "all_feasible [q\<^sub>1,  q\<^sub>2,  p\<^sub>1, p\<^sub>2] \<Longrightarrow> q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> strengthens (q\<^sub>1 ; q\<^sub>2) (p\<^sub>1 ; p\<^sub>2)" *)
  (* apply (auto simp: refines_def weakens_def strengthens_def composition_def restrict_r_def corestrict_r_def is_feasible_def relcomp_def relcompp_apply) *)
  (* oops *)

(* lemma refinement_safety_composition_s1: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> Pre q\<^sub>1 = Pre p\<^sub>1 \<Longrightarrow> Pre q\<^sub>2 = Pre p\<^sub>2  \<Longrightarrow> strengthens (q\<^sub>1 ; q\<^sub>2) (p\<^sub>1 ; p\<^sub>2)" *)
  (* apply (auto simp: refines_def strengthens_def composition_def restrict_r_def corestrict_r_def weakens_def relcomp_def relcompp_apply) *)
  (* using subset_iff by fastforce *)

(* lemma refinement_safety_composition_s2: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> independant q\<^sub>1 p\<^sub>2 \<Longrightarrow> independant q\<^sub>2 p\<^sub>1 \<Longrightarrow> strengthens (q\<^sub>1 ; q\<^sub>2) (p\<^sub>1 ; p\<^sub>2)" *)
  (* apply (auto simp: refines_def strengthens_def independant_def composition_def restrict_r_def corestrict_r_def weakens_def relcomp_def relcompp_apply) *)
  (* apply (auto simp: subset_iff) *)
  (* oops *)




(* lemma refinement_safety_composition_e2: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> extends (q\<^sub>1 ;\<^sub>p q\<^sub>2) (p\<^sub>1 ;\<^sub>p p\<^sub>2)" *)
  (* by (auto simp: unsafe_composition_def refines_def extends_def corestrict_r_def S_def Field_def) *)

(* lemma refinement_safety_composition_w2: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> weakens (q\<^sub>1 ;\<^sub>p q\<^sub>2) (p\<^sub>1 ;\<^sub>p p\<^sub>2)" *)
  (* by (auto simp: refines_def weakens_def unsafe_composition_def) *)

(* lemma refinement_safety_composition_s3: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> Pre q\<^sub>1 = Pre p\<^sub>1 \<Longrightarrow> Pre q\<^sub>2 = Pre p\<^sub>2 \<Longrightarrow> strengthens (q\<^sub>1 ;\<^sub>p q\<^sub>2) (p\<^sub>1 ;\<^sub>p p\<^sub>2)" *)
  (* apply (auto simp: refines_def strengthens_def unsafe_composition_def restrict_r_def corestrict_r_def weakens_def relcomp_def relcompp_apply) *)
  (* using fstI by force *)


(* lemma refinement_safety_composition_s4: "q\<^sub>1 \<subseteq>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<subseteq>\<^sub>p p\<^sub>2 \<Longrightarrow> is_feasible (q\<^sub>1 ;\<^sub>p q\<^sub>2) \<Longrightarrow> is_feasible (p\<^sub>1 ;\<^sub>p p\<^sub>2) \<Longrightarrow> strengthens (q\<^sub>1 ;\<^sub>p q\<^sub>2) (p\<^sub>1 ;\<^sub>p p\<^sub>2)" *)
  (* apply (auto simp: refines_def strengthens_def unsafe_composition_def restrict_r_def corestrict_r_def weakens_def relcomp_def relcompp_apply) *)
  (* using fstI by force *)


(* lemma refinement_safety_composition_w3: "all_feasible [q\<^sub>1,  q\<^sub>2,  p\<^sub>1, p\<^sub>2] \<Longrightarrow> q\<^sub>1 \<le>\<^sub>p p\<^sub>1 \<Longrightarrow> q\<^sub>2 \<le>\<^sub>p p\<^sub>2 \<Longrightarrow> Pre (q\<^sub>1 ; q\<^sub>2) = Pre (p\<^sub>1 ; p\<^sub>2)" *)
  (* apply (auto simp: strict_refines_def refines_def weakens_def composition_def is_feasible_def corestrict_r_def strengthens_def restrict_r_def) *)





end