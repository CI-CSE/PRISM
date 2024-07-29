theory Definitions
  imports Relation_operations "HOL-Library.Mapping"
begin
section \<open>Definitions for top\<close>

record 'a Program = \<comment> \<open>/Basic_def/\<close>
  State :: "'a set"
  Pre :: "'a set"
  post :: "'a rel" 

definition S :: "'a Program \<Rightarrow> 'a set"
  where
    "S p = State p \<union> Pre p \<union> Field (post p)"

definition is_feasible :: "'a Program \<Rightarrow> bool" \<comment> \<open>/Feasible/\<close>
  where
    "is_feasible p = (Pre p \<subseteq> Domain (post p))"

primrec all_feasible :: "('a Program) list \<Rightarrow> bool"
  where
    "all_feasible [] = True" |
    "all_feasible (x # xs) = (all_feasible xs \<and> is_feasible x)"

definition is_valid :: "'a Program \<Rightarrow> bool"
  where
    "is_valid p \<equiv> S p = State p"

primrec all_valid :: "('a Program) list \<Rightarrow> bool"
  where
    "all_valid [] = True" |
    "all_valid (x#xs) = (all_valid xs \<and> is_valid x)"

definition is_deterministic :: "'a Program \<Rightarrow> bool" \<comment> \<open>/Program_kind/\<close>
  where
    "is_deterministic p = is_function (post p)"

definition is_functional :: "'a Program \<Rightarrow> bool" \<comment> \<open>/Program_kind/\<close>
  where
    "is_functional p \<equiv> \<forall>C\<subseteq>(S p). Image (post p) C \<inter> C = {}"

(* type_synonym ('O) state_space = "nat \<Rightarrow> 'b" *)
(* Object oriented program is "'O Program"*)

(* value "\<lparr>State=(\<lambda>x. x), Pre=(\<lambda>x. x), post={((\<lambda>x. x), (\<lambda>x. x))} \<rparr>::(nat \<Rightarrow> nat) Program" *)

definition is_total :: "'a Program \<Rightarrow> bool"
  where
    "is_total p = (Pre p = S p)"

definition restr_post :: "'a Program \<Rightarrow> 'a  rel"
  where
    "restr_post p = post p \<sslash>\<^sub>r Pre p"

definition equal :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" (infix "\<triangleq>" 48) \<comment> \<open>Make equals look at S and not State\<close>
  where
    "p\<^sub>1 \<triangleq> p\<^sub>2 \<equiv> (Pre p\<^sub>1 = Pre p\<^sub>2 \<and> post p\<^sub>1 = post p\<^sub>2 \<and> S p\<^sub>1 = S p\<^sub>2)"

definition equiv :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" (infix "\<equiv>\<^sub>p" 49) \<comment> \<open>/Equiv/\<close>
  where
    "p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<equiv> (Pre p\<^sub>1 = Pre p\<^sub>2 \<and> restr_post p\<^sub>1 = restr_post p\<^sub>2)"

definition Range_p :: "'a Program \<Rightarrow> 'a set" \<comment> \<open>All states that could be reached\<close>
  where
    "Range_p p = Range (post p \<sslash>\<^sub>r Pre p)"

definition inverse :: "'a Program \<Rightarrow> 'a Program" \<comment> \<open>NEW\<close>
  where
    "inverse p \<equiv> \<lparr>State=S p, Pre=Range_p p, post=(restr_post p)\<inverse>\<rparr>"

notation inverse ("_\<^sup>-\<^sup>1" [50] 50)


definition extends :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool"
  where
    "extends p\<^sub>2 p\<^sub>1 = (S p\<^sub>1 \<subseteq> S p\<^sub>2)"

definition weakens :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool"
  where
    "weakens p\<^sub>2 p\<^sub>1 = (Pre p\<^sub>1 \<subseteq> Pre p\<^sub>2)"

definition strengthens :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" \<comment> \<open>NEW DEFINITION\<close>
  where
    "strengthens p\<^sub>2 p\<^sub>1 \<equiv> ((post p\<^sub>2) \<sslash>\<^sub>r Pre p\<^sub>2) \<sslash>\<^sub>r (Pre p\<^sub>1) \<subseteq> post p\<^sub>1"  \<comment> \<open>Can be simplified if p2 weakens p1\<close>  
  
definition refines :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" (infix "\<subseteq>\<^sub>p" 50) \<comment> \<open>D7\<close>
  where
    "p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>1 = (extends p\<^sub>2 p\<^sub>1 \<and> weakens p\<^sub>2 p\<^sub>1 \<and> strengthens p\<^sub>2 p\<^sub>1)"

definition subprogram :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" (infix "\<preceq>\<^sub>p" 50)
  where
    "p\<^sub>1 \<preceq>\<^sub>p p\<^sub>2 \<equiv> extends p\<^sub>2 p\<^sub>1 \<and> weakens p\<^sub>2 p\<^sub>1 \<and> strengthens p\<^sub>1 p\<^sub>2"

definition independent :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" \<comment> \<open>NEW DEFINITION\<close>
  where
    "independent p\<^sub>1 p\<^sub>2 = (Pre p\<^sub>1 \<inter> Pre p\<^sub>2 = {})"

definition implements :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" \<comment> \<open>D8\<close>
  where
    "implements p\<^sub>2 p\<^sub>1 = (p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>1 \<and> is_feasible p\<^sub>2)"

definition choice :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix "\<union>\<^sub>p" 151) \<comment> \<open>D9 NEW DEFINITION\<close>
  where
    "choice p\<^sub>1 p\<^sub>2 = \<lparr>State= S p\<^sub>1 \<union> S p\<^sub>2, Pre = Pre p\<^sub>1 \<union> Pre p\<^sub>2, post = restr_post p\<^sub>1 \<union> restr_post p\<^sub>2\<rparr>"

definition composition :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix ";" 152) \<comment> \<open>D10\<close>
  where
    "composition p\<^sub>1 p\<^sub>2 = \<lparr>
      State = S p\<^sub>1 \<union> S p\<^sub>2,
      Pre = Pre p\<^sub>1 \<inter> Domain (post p\<^sub>1 \<setminus>\<^sub>r Pre p\<^sub>2),
      post = (post p\<^sub>1) O (restr_post p\<^sub>2)\<rparr>" \<comment> \<open>IS THE SAME BECAUSE: r1\s O r2 = r1 O r2/s\<close>

definition commute :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool"
  where
    "commute p\<^sub>1 p\<^sub>2 \<equiv> (p\<^sub>1 ; p\<^sub>2) \<equiv>\<^sub>p (p\<^sub>2 ; p\<^sub>1)"

definition unsafe_composition ::"'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix ";\<^sub>p" 152)
  where
    "unsafe_composition p\<^sub>1 p\<^sub>2 = \<lparr>
      State = S p\<^sub>1 \<union> S p\<^sub>2,
      Pre = Pre p\<^sub>1,
      post = (post p\<^sub>1) O (restr_post p\<^sub>2)\<rparr>"

value "({(1,2)}::nat rel) O ({(2,3)} ::nat rel)"

definition restrict_p :: "'a Program \<Rightarrow> 'a set \<Rightarrow> 'a Program" (infix "\<sslash>\<^sub>p" 153) \<comment> \<open>D11 NEW DEFINITION\<close>
  where
    "restrict_p p C = \<lparr>State= S p, Pre=Pre p \<inter> C, post=post p\<rparr>"

definition corestrict_p :: "'a Program \<Rightarrow> 'a set \<Rightarrow> 'a Program" (infix "\<setminus>\<^sub>p" 154) \<comment> \<open>Definition number missing\<close>
  where
    "corestrict_p p C = \<lparr>State= S p, 
        Pre=Pre p \<inter> Domain (post p \<setminus>\<^sub>r C), \<comment> \<open>NEWLY EXPRESSED LIKE THIS\<close>
        post=post p \<setminus>\<^sub>r C\<rparr>"

definition char_rel :: "'a Program \<Rightarrow> 'a rel" \<comment> \<open>NEW DEFINITION\<close>
  where
    "char_rel p = post p \<sslash>\<^sub>r Pre p"

definition Fail :: "'a set \<Rightarrow> 'a Program"
  where
    "Fail s = \<lparr> State = s, Pre = {}, post = {}\<rparr>"

definition Havoc :: "'a set \<Rightarrow> 'a Program"
  where
    "Havoc s = \<lparr> State = s, Pre = s, post = {(x,y). x \<in> s \<and> y \<in> s}\<rparr>"

definition Skip :: "'a set \<Rightarrow> 'a Program"
  where
    "Skip s = \<lparr> State = s, Pre = s, post = {(x,y). x \<in> s \<and> x = y} \<rparr>"

definition Infeas :: "'a set \<Rightarrow> 'a Program"
  where
    "Infeas s = \<lparr> State = s, Pre = s, post = {} \<rparr>"

definition atomic_conc  :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix "||" 150)
  where
    "p\<^sub>1 || p\<^sub>2 \<equiv> (p\<^sub>1 ; p\<^sub>2) \<union>\<^sub>p (p\<^sub>2 ; p\<^sub>1)"

definition non_atomic_conc:: "('a Program \<times> 'a Program) \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix "\<parallel>" 50)
  where
    "p \<parallel> q \<equiv> ((fst p || q) ; snd p) \<union>\<^sub>p (fst p ; (snd p || q))"

definition guarded_conditional :: "'a set \<Rightarrow> 'a Program \<Rightarrow> 'a set \<Rightarrow> 'a Program \<Rightarrow> 'a Program"
  where
    "guarded_conditional C\<^sub>1 p\<^sub>1 C\<^sub>2 p\<^sub>2 \<equiv> (p\<^sub>1 \<sslash>\<^sub>p C\<^sub>1) \<union>\<^sub>p (p\<^sub>2 \<sslash>\<^sub>p C\<^sub>2)"

abbreviation GC :: "'a set \<Rightarrow> 'a Program \<Rightarrow> 'a set \<Rightarrow> 'a Program \<Rightarrow> 'a Program"
  where
    "GC == guarded_conditional"

definition if_then_else :: "'a set \<Rightarrow> 'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program"
  where
    "if_then_else C p\<^sub>1 p\<^sub>2 \<equiv> (p\<^sub>1 \<sslash>\<^sub>p C) \<union>\<^sub>p (p\<^sub>2 \<sslash>\<^sub>p (-C))"

abbreviation ITE :: "'a set \<Rightarrow> 'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program"
  where
    "ITE == if_then_else" 

definition if_then :: "'a set \<Rightarrow> 'a Program \<Rightarrow> 'a Program"
  where
    "if_then C p \<equiv> ITE C p (Skip (S p))"

definition TRUE:: "'a set \<Rightarrow> 'a set"
  where
    "TRUE s = s"

definition FALSE:: "'a set"
  where
    "FALSE = {}"

definition AND\<^sub>s:: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infix "\<and>\<^sub>s" 50)
  where
    "AND\<^sub>s s\<^sub>1 s\<^sub>2 = s\<^sub>1 \<inter> s\<^sub>2"

definition OR\<^sub>s:: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infix "\<or>\<^sub>s" 50)
  where
    "OR\<^sub>s s\<^sub>1 s\<^sub>2 = s\<^sub>1 \<union> s\<^sub>2"

definition NOT\<^sub>s:: "'a set \<Rightarrow> 'a set"
  where
    "NOT\<^sub>s s = -s"

notation NOT\<^sub>s ("\<not>\<^sub>s _" [50] 50)

definition IMPLIES\<^sub>s:: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infix "\<rightarrow>\<^sub>s" 50) \<comment> \<open>NEW DEFINITION\<close>
  where
    "IMPLIES\<^sub>s s\<^sub>1 s\<^sub>2 \<equiv> (\<not>\<^sub>s s\<^sub>1) \<or>\<^sub>s  s\<^sub>2"

primrec fixed_repetition_helper:: "'a Program \<Rightarrow> nat \<Rightarrow> 'a Program" (infix "^\<^sup>p" 153)
  where
    "fixed_repetition_helper p 0       = Skip (S p)" |
    "fixed_repetition_helper p (Suc i) = fixed_repetition_helper p i ; p"


primrec fixed_repetition:: "'a Program \<Rightarrow> nat \<Rightarrow> 'a Program" (infix "\<^bold>^" 153)
  where
    "p\<^bold>^0       = Skip (Pre p)" |
    "p\<^bold>^(Suc i) = p\<^bold>^i;p"

primrec Choice:: "('a Program) list \<Rightarrow> 'a Program"
  where
    "Choice [] = (Fail {})" |
    "Choice (x#xs) = x \<union>\<^sub>p (Choice xs)"

notation
  Choice ("\<Union>\<^sub>p")

primrec Union:: "('a set) list \<Rightarrow> 'a set"
  where
    "Union [] = {}" |
    "Union (x#xs) = x \<union> Union xs"

notation
  Union ("\<Union>\<^sub>s")

fun arbitrary_repetition:: "'a Program \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a Program"
  where
    "arbitrary_repetition p s 0 = (if s>0 then Fail (S p) else p\<^bold>^0)" |
    "arbitrary_repetition p s (Suc f) = (if s>(Suc f) then Fail (S p) else p\<^bold>^(Suc f) \<union>\<^sub>p arbitrary_repetition p s f)"

abbreviation loop :: "'a Program \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a Program" where
  "loop \<equiv> arbitrary_repetition"


definition while_support:: "'a Program \<Rightarrow> 'a set \<Rightarrow> 'a Program \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a Program"
  where
    "while_support a C b s f = a ; (loop (b\<sslash>\<^sub>p(-C)) s f)\<setminus>\<^sub>p C"

definition while_loop:: "'a Program \<Rightarrow> 'a set \<Rightarrow> 'a Program \<Rightarrow> nat \<Rightarrow> 'a Program"
  where
    "while_loop a C b n = a ; (loop (b\<sslash>\<^sub>p(-C)) 0 n)\<setminus>\<^sub>p C"

definition is_invariant:: "'a set \<Rightarrow> 'a Program \<Rightarrow> bool"
  where
    (* "is_invariant I p \<equiv> Range_p (p \<sslash>\<^sub>p I) \<subseteq> I" *)
    "is_invariant I p \<equiv> Pre p \<subseteq> I \<and> Range_p p \<subseteq> I" \<comment> \<open>Isn't this definition better?\<close>

lemma "Pre p \<subseteq> I \<and> Range_p p \<subseteq> I \<Longrightarrow> Range_p (p \<sslash>\<^sub>p I) \<subseteq> I"
  by (auto simp: Range_p_def restrict_p_def restrict_r_def)

definition is_loop_invariant:: "'a set \<Rightarrow> 'a Program \<Rightarrow> 'a set \<Rightarrow> 'a Program \<Rightarrow> bool"
  where
    (* "is_loop_invariant I a C b \<equiv> I \<subseteq> (Range_p a) \<and> is_invariant I (b\<sslash>\<^sub>p(-C))" *)
    "is_loop_invariant I a C b \<equiv> Range_p a \<subseteq> I \<and> is_invariant I (b\<sslash>\<^sub>p(-C))" \<comment> \<open>Isn't this definition better?\<close>


end