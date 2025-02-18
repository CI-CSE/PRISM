theory Definitions
  imports Relation_operations HOL.Finite_Set
begin
section \<open>Definitions for top\<close>

record 'a Program = \<comment> \<open>/Basic_def/\<close>
  State :: "'a set"
  Pre :: "'a set"
  post :: "'a rel"

record 'a Contracted_Program =
  a_specification :: "'a Program"
  a_implementation :: "'a Program"

type_synonym 'a CNF = "'a Program list list"

definition basic :: "'a CNF \<Rightarrow> 'a Program set"
  where
    "basic p \<equiv> foldl (\<union>) ({}::'a Program set) (map (set) p)"

definition normal_of :: "'a CNF \<Rightarrow> 'a Program set \<Rightarrow> bool"
  where
    "normal_of p xs \<equiv> (basic p \<subseteq> (xs \<union> {\<lparr>State={},Pre={},post={}\<rparr>})) \<and> finite xs"

definition S :: "'a Program \<Rightarrow> 'a set"
  where
    "S p = State p \<union> Pre p \<union> Field (post p)"

definition used_states :: "'a Program \<Rightarrow> 'a set" \<comment> \<open>NEW\<close>
  where
    "used_states p \<equiv> Pre p \<union> Field (post p)"

definition is_feasible :: "'a Program \<Rightarrow> bool" \<comment> \<open>/Feasible_program/\<close>
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

definition equiv :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" (infix "\<equiv>\<^sub>p" 49) \<comment> \<open>/Equiv_programs/\<close>
  where
    "p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<equiv> (Pre p\<^sub>1 = Pre p\<^sub>2 \<and> restr_post p\<^sub>1 = restr_post p\<^sub>2)"

definition Range_p :: "'a Program \<Rightarrow> 'a set" \<comment> \<open>All states that could be reached\<close>
  where
    "Range_p p = Range (post p \<sslash>\<^sub>r Pre p)"

definition inverse :: "'a Program \<Rightarrow> 'a Program" \<comment> \<open>NEW\<close>
  where
    "inverse p \<equiv> \<lparr>State=S p, Pre=Range_p p, post=(restr_post p)\<inverse>\<rparr>"

notation inverse ("_\<^sup>-\<^sup>1" [50] 50)

definition extends :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" \<comment> \<open>Extend_states\<close>
  where
    "extends p\<^sub>2 p\<^sub>1 = (S p\<^sub>1 \<subseteq> S p\<^sub>2)"

definition weakens :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" \<comment> \<open>Weaken_pre\<close>
  where
    "weakens p\<^sub>2 p\<^sub>1 = (Pre p\<^sub>1 \<subseteq> Pre p\<^sub>2)"

definition strengthens :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" \<comment> \<open>NEW DEFINITION\<close> \<comment> \<open>Weaken_pre\<close>
  where
    "strengthens p\<^sub>2 p\<^sub>1 \<equiv> ((post p\<^sub>2) \<sslash>\<^sub>r Pre p\<^sub>2) \<sslash>\<^sub>r (Pre p\<^sub>1) \<subseteq> post p\<^sub>1"  \<comment> \<open>Can be simplified if p2 weakens p1\<close>  
  
definition refines :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" (infix "\<subseteq>\<^sub>p" 50) \<comment> \<open>D7\<close>
  where
    "p\<^sub>1 \<subseteq>\<^sub>p p\<^sub>2 = (extends p\<^sub>1 p\<^sub>2 \<and> weakens p\<^sub>1 p\<^sub>2 \<and> strengthens p\<^sub>1 p\<^sub>2)"

definition refines_c :: "'a Contracted_Program \<Rightarrow> 'a Contracted_Program \<Rightarrow> bool" (infix "\<subseteq>\<^sub>c" 50)
  where
    "cp\<^sub>2 \<subseteq>\<^sub>c cp\<^sub>1 \<equiv> a_specification cp\<^sub>2 = a_specification cp\<^sub>1 \<and> a_implementation cp\<^sub>2 \<subseteq>\<^sub>p a_implementation cp\<^sub>1"

definition subprogram :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" (infix "\<preceq>\<^sub>p" 50)
  where
    "p\<^sub>1 \<preceq>\<^sub>p p\<^sub>2 \<equiv> extends p\<^sub>2 p\<^sub>1 \<and> weakens p\<^sub>2 p\<^sub>1 \<and> strengthens p\<^sub>1 p\<^sub>2"

definition independent :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" \<comment> \<open>NEW DEFINITION\<close>
  where
    "independent p\<^sub>1 p\<^sub>2 = (Pre p\<^sub>1 \<inter> Pre p\<^sub>2 = {})"

definition implements :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" \<comment> \<open>Implement_def\<close>
  where
    "implements p\<^sub>2 p\<^sub>1 = (p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>1 \<and> is_feasible p\<^sub>2)"

definition most_abstract_implementation :: "'a Program \<Rightarrow> 'a Contracted_Program" \<comment> \<open>MAI_definition\<close>
  where
    "most_abstract_implementation p \<equiv> \<lparr>a_specification=p, a_implementation=p\<rparr>"

abbreviation MAI :: "'a Program \<Rightarrow> 'a Contracted_Program"
  where
    "MAI \<equiv> most_abstract_implementation"

definition is_correct :: "'a Contracted_Program \<Rightarrow> bool"
  where
    "is_correct cp = implements (a_implementation cp) (a_specification cp)"

definition strongest_postcondition :: "'a Program \<Rightarrow> 'a set \<Rightarrow> 'a rel" (infix "sp" 150)
  where
    "p sp Pre' \<equiv> post (p) \<sslash>\<^sub>r Pre'"

definition new_behavior :: "'a Program \<Rightarrow> 'a rel \<Rightarrow> 'a rel"
  where
    "new_behavior p post' \<equiv> post p - post'" \<comment> \<open>Behavior to exclude\<close>

definition weakest_precondition :: "'a Program \<Rightarrow> 'a rel \<Rightarrow> 'a set" (infix "wp" 150)
  where
    "p wp post' \<equiv> Pre p - Domain (new_behavior p post')"

definition choice :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix "\<union>\<^sub>p" 151) \<comment> \<open>D9 NEW DEFINITION\<close>
  where
    "p\<^sub>1 \<union>\<^sub>p p\<^sub>2 = \<lparr>State= S p\<^sub>1 \<union> S p\<^sub>2, Pre = Pre p\<^sub>1 \<union> Pre p\<^sub>2, post = restr_post p\<^sub>1 \<union> restr_post p\<^sub>2\<rparr>"

definition non_empty :: "'a CNF \<Rightarrow> 'a CNF"
  where
    "non_empty xs \<equiv> [t . t \<leftarrow> xs, t \<noteq> []]"

definition non_empty2 :: "'a CNF list \<Rightarrow> 'a CNF list"
  where
    "non_empty2 xs \<equiv> [prog2. prog2 \<leftarrow> [non_empty prog. prog \<leftarrow> xs], prog2 \<noteq> []]"

definition choice_cnf :: "'a CNF \<Rightarrow> 'a CNF \<Rightarrow> 'a CNF" (infix "\<union>\<^sub>c" 150)
  where
    "choice_cnf a b \<equiv> a @ b"

definition composition_cnf :: "'a CNF \<Rightarrow> 'a CNF \<Rightarrow> 'a CNF" (infix ";\<^sub>c" 150)
  where
    "composition_cnf a b \<equiv> [xs @ ys. xs \<leftarrow> a, ys \<leftarrow> b]"


definition is_prime :: "'a Program \<Rightarrow> bool" 
  where
    "is_prime p \<equiv> card (Pre p) = 1 \<and> card (post p) = 1 \<and> Pre p \<union> Field (post p) = State p"

value "is_prime (\<lparr>State={1,2}, Pre={1}, post={(1,2)}\<rparr>::nat Program)"

theorem "\<lparr>State={}, Pre={1::nat}, post={(1,2)}\<rparr> \<preceq>\<^sub>p \<lparr>State={}, Pre={1::nat}, post={(1,2)}\<rparr>"
  by (auto simp: subprogram_def extends_def weakens_def strengthens_def restrict_r_def)

definition composition :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix ";" 152) \<comment> \<open>D10\<close>
  where
    "p\<^sub>1 ; p\<^sub>2 = \<lparr>
      State = S p\<^sub>1 \<union> S p\<^sub>2,
      Pre = Pre p\<^sub>1 \<inter> Domain (post p\<^sub>1 \<setminus>\<^sub>r Pre p\<^sub>2),
      post = (post p\<^sub>1) O (restr_post p\<^sub>2)\<rparr>" \<comment> \<open>IS THE SAME BECAUSE: r1\s O r2 = r1 O r2/s\<close>

definition commute_programs1 :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool"
  where
    "commute_programs1 p\<^sub>1 p\<^sub>2 \<equiv> (p\<^sub>1 ; p\<^sub>2) = (p\<^sub>2 ; p\<^sub>1)"

definition commute_programs2 :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool"
  where
    "commute_programs2 p\<^sub>1 p\<^sub>2 \<equiv> (p\<^sub>1 ; p\<^sub>2) \<triangleq> (p\<^sub>2 ; p\<^sub>1)"

definition commute_programs3 :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool"
  where
    "commute_programs3 p\<^sub>1 p\<^sub>2 \<equiv> (p\<^sub>1 ; p\<^sub>2) \<equiv>\<^sub>p (p\<^sub>2 ; p\<^sub>1)"

definition unsafe_composition :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix ";\<^sub>p" 152)
  where
    "p\<^sub>1 ;\<^sub>p p\<^sub>2 = \<lparr>
      State = S p\<^sub>1 \<union> S p\<^sub>2,
      Pre = Pre p\<^sub>1,
      post = (post p\<^sub>1) O (restr_post p\<^sub>2)\<rparr>"

definition unsafe_composition2 :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix ";\<^sup>p" 152)
  where
    "p\<^sub>1 ;\<^sup>p p\<^sub>2 = \<lparr>
      State = S p\<^sub>1 \<union> S p\<^sub>2,
      Pre = Pre p\<^sub>1 \<inter> Domain (post p\<^sub>1 \<setminus>\<^sub>r Pre p\<^sub>2),
      post = (post p\<^sub>1) O (post p\<^sub>2)\<rparr>"


definition unsafe_composition3 :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix ";\<^sub>P" 152)
  where
    "p\<^sub>1 ;\<^sub>P p\<^sub>2 = \<lparr>
      State = S p\<^sub>1 \<union> S p\<^sub>2,
      Pre = Pre p\<^sub>1,
      post = (post p\<^sub>1) O (post p\<^sub>2)\<rparr>"


value "({(1,2)}::nat rel) O ({(2,3)} ::nat rel)"

definition restrict_p :: "'a Program \<Rightarrow> 'a set \<Rightarrow> 'a Program" (infix "\<sslash>\<^sub>p" 153) \<comment> \<open>D11 NEW DEFINITION\<close>
  where
    "restrict_p p C = \<lparr>State= S p, Pre=Pre p \<inter> C, post=post p \<sslash>\<^sub>r C\<rparr>"

definition corestrict_p :: "'a Program \<Rightarrow> 'a set \<Rightarrow> 'a Program" (infix "\<setminus>\<^sub>p" 154) \<comment> \<open>Definition number missing\<close>
  where
    "corestrict_p p C = \<lparr>State= S p, 
        Pre=Pre p, \<comment> \<open>NEWLY EXPRESSED LIKE THIS\<close>
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

primrec generalized_non_atomic_conc:: "('a Program) list \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix "\<parallel>\<^sub>G" 50)
  where
    "[]     \<parallel>\<^sub>G q = q" |
    "(x#xs) \<parallel>\<^sub>G q = ((xs \<parallel>\<^sub>G q) ; x) \<union>\<^sub>p (x ; (xs \<parallel>\<^sub>G q))"

definition if_then_else :: "'a set \<Rightarrow> 'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program"
  where
    "if_then_else C p\<^sub>1 p\<^sub>2 \<equiv> (p\<^sub>1 \<sslash>\<^sub>p C) \<union>\<^sub>p (p\<^sub>2 \<sslash>\<^sub>p (-C))"

abbreviation ITE :: "'a set \<Rightarrow> 'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program"
  where
    "ITE \<equiv> if_then_else" 

definition if_then :: "'a set \<Rightarrow> 'a Program \<Rightarrow> 'a Program"
  where
    "if_then C p \<equiv> ITE C p (Skip (S p))"

definition TRUE:: "'a set \<Rightarrow> 'a set"
  where
    "TRUE s = s"

definition FALSE:: "'a set"
  where
    "FALSE = {}"

definition TRUE\<^sub>r:: "'a set \<Rightarrow> 'a rel"
  where
    "TRUE\<^sub>r s \<equiv> {(a,b) . a \<in> s \<and> b \<in> s}"

definition ID :: "'a set \<Rightarrow> 'a rel"
  where
    "ID s \<equiv> {(a,b) . a \<in> s \<and> b \<in> s \<and> a = b}"

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
    "p\<^bold>^0       = Skip (S p) \<sslash>\<^sub>p (Pre p)" |
    "p\<^bold>^(Suc i) = p\<^bold>^i;p"

fun Choice:: "('a Program) list \<Rightarrow> 'a Program"
  where
    "Choice [] = Fail {}" |
    "Choice [x] = x" |
    "Choice (x#xs) = foldl (\<union>\<^sub>p) x xs"

notation
  Choice ("\<Union>\<^sub>p")

fun Concat:: "('a Program) list \<Rightarrow> 'a set \<Rightarrow> 'a Program"
  where
    "Concat [] s = (Skip s)" |
    "Concat [x] s = x" |
    "Concat (x#xs) s = foldl (;) x xs"

definition Choice_set:: "('a Program) set \<Rightarrow> 'a Program"
  where
    "Choice_set P \<equiv> Finite_Set.fold (\<union>\<^sub>p) (Fail {}) P"
                                       
notation
  Choice_set ("\<Union>\<^sub>P")

definition is_minimal:: "'a Program \<Rightarrow> bool"
  where
    "is_minimal p \<equiv> (\<forall>a b. (a,b) \<in> post p \<longrightarrow> a \<in> Pre p) \<and> is_valid p \<and> (\<forall> s \<in> State p. s \<in> Field (post p))" \<comment> \<open>No dead code\<close>



definition guarded_conditional :: "('a set \<times> 'a Program) list \<Rightarrow>  'a Program"
  where
    "guarded_conditional xs = \<Union>\<^sub>p [snd t \<sslash>\<^sub>p fst t. t \<leftarrow> xs]"

(*
primrec guarded_conditional :: "('a set \<times> 'a Program) list \<Rightarrow>  'a Program"
  where
    "guarded_conditional [] = Fail {}" |
    "guarded_conditional (x#xs) = snd x \<sslash>\<^sub>p fst x \<union>\<^sub>p guarded_conditional xs"
*)

abbreviation GC :: "('a set \<times> 'a Program) list \<Rightarrow> 'a Program"
  where
    "GC \<equiv> guarded_conditional"

(*
primrec insert_all_positions :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  base: "insert_all_positions x [] = [[x]]" |
  step: "insert_all_positions x (y#ys) = (x#y#ys) # [(y#t). t <- (insert_all_positions x ys)]"
*)
(*
definition permutations :: "'a list \<Rightarrow> 'a list set" where
  "permutations xs = {t. \<forall>x. List.count_list t x = List.count_list xs x}"
*)

primrec  insert_all :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "insert_all x [] = [[x]]" |
  "insert_all x (y#ys) = (x#y#ys) # (map (\<lambda>zs. y#zs) (insert_all x ys))"

fun permutations :: "'a list \<Rightarrow> 'a list list" where
  "permutations [] = [[]]" |
  "permutations (x#xs) = concat (map (insert_all x) (permutations xs))"

value "permutations [a\<^sub>1, a\<^sub>2, a\<^sub>3]"
value "permutations ([]::nat list)"

definition complete_state :: "'a Program list \<Rightarrow> 'a set"
  where
    "complete_state xs \<equiv> fold (\<lambda> p s. S p \<union> s) xs {}"


primrec n_comp :: "'a Program list \<Rightarrow> 'a Program"
  where
    "n_comp [] = Fail {}" |
    "n_comp (x#xs) = x ; (n_comp xs)"

definition conc_elems :: "'a Program list \<Rightarrow> 'a Program list"
  where
    "conc_elems xs \<equiv> [Concat t (complete_state t). t <- permutations xs]"

definition atomic_conc :: "'a Program list \<Rightarrow> 'a Program"
  where
    "atomic_conc xs \<equiv> \<Union>\<^sub>p (conc_elems xs)"

(*
definition non_atomic_conc:: "('a Program \<times> 'a Program) \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix "\<parallel>" 50)
  where
    "p \<parallel> q \<equiv> (atomic_conc [fst p, q] ; snd p) \<union>\<^sub>p (fst p ; atomic_conc [snd p, q])"
*)

definition non_atomic_conc:: "'a Program list \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix "\<parallel>\<^sub>n" 50)
  where
    "xs \<parallel>\<^sub>n x \<equiv> \<Union>\<^sub>p [Concat t (complete_state t). t \<leftarrow> insert_all x xs]"

definition arbitrary_repetition_set :: "'a Program \<Rightarrow> 'a Program set"
  where
    "arbitrary_repetition_set p \<equiv> {p\<^bold>^i | i . 0\<le>i}"

fun arbitrary_repetition :: "'a Program \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a Program"
  where
    "arbitrary_repetition p s 0 = (if s>0 then Fail (S p) else p\<^bold>^0)" |
    "arbitrary_repetition p s (Suc f) = (if s>(Suc f) then Fail (S p) else p\<^bold>^(Suc f) \<union>\<^sub>p arbitrary_repetition p s f)"

(* definition arbitrary_repetition :: "'a Program \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a Program" *)
  (* where *)
    (* "arbitrary_repetition p s 0 \<equiv> " *)

abbreviation loop :: "'a Program \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a Program" where
  "loop \<equiv> arbitrary_repetition"

definition until_support:: "'a Program \<Rightarrow> 'a set \<Rightarrow> 'a Program \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a Program"
  where
    "until_support a C b s f = a ; (loop (b\<sslash>\<^sub>p(-C)) s f)\<setminus>\<^sub>p C"

definition until_loop:: "'a Program \<Rightarrow> 'a set \<Rightarrow> 'a Program \<Rightarrow> nat \<Rightarrow> 'a Program"
  where
    "until_loop a C b n = a ; (loop (b\<sslash>\<^sub>p(-C)) 0 n)\<setminus>\<^sub>p C"

definition is_invariant:: "'a set \<Rightarrow> 'a Program \<Rightarrow> bool"
  where
    "is_invariant I p \<equiv> Range_p (p \<sslash>\<^sub>p I) \<subseteq> I"
    (*"is_invariant I p \<equiv> Pre p \<subseteq> I \<and> Range_p p \<subseteq> I" \<comment> \<open>Isn't this definition better?\<close>*)

lemma "Pre p \<subseteq> I \<and> Range_p p \<subseteq> I \<Longrightarrow> Range_p (p \<sslash>\<^sub>p I) \<subseteq> I"
  by (auto simp: Range_p_def restrict_p_def restrict_r_def)


definition is_loop_invariant:: "'a set \<Rightarrow> 'a Program \<Rightarrow> 'a set \<Rightarrow> 'a Program \<Rightarrow> bool" \<comment> \<open>Loop_invariant\<close>
  where
    (* "is_loop_invariant I a C b \<equiv> I \<subseteq> (Range_p a) \<and> is_invariant I (b\<sslash>\<^sub>p(-C))" *)
    "is_loop_invariant I a C b \<equiv> Range_p a \<subseteq> I \<and> is_invariant I (b\<sslash>\<^sub>p(-C))" \<comment> \<open>Isn't this definition better?\<close>

definition markovian :: "'a rel \<Rightarrow> bool"
  where
    "markovian r \<equiv> \<forall>s s\<^sub>1 s\<^sub>2. ((s\<^sub>1, s) \<in> r) = ((s\<^sub>2, s) \<in> r)"

definition is_trivial :: "'a rel \<Rightarrow> 'a \<Rightarrow> bool"
  where
    "is_trivial r s \<equiv> \<forall>s\<^sub>1. (s, s\<^sub>1) \<in> r"

definition is_irrelevant :: "'a rel \<Rightarrow> 'a \<Rightarrow> bool"
  where
    "is_irrelevant r s \<equiv> \<forall>s\<^sub>1 s\<^sub>2. ((s, s\<^sub>1) \<in> r) = ((s, s\<^sub>2) \<in> r)"

definition is_relevant :: "'a rel \<Rightarrow> 'a \<Rightarrow> bool"
  where
    "is_relevant r s \<equiv> \<not> is_irrelevant r s"

definition is_programming_language :: "'a set \<Rightarrow> ('a Program) set \<Rightarrow> bool"
  where
    "is_programming_language s P \<equiv> \<forall>p \<in> P. is_feasible p \<and> S p \<subseteq> s"

fun occurs :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "occurs _ [] = 0" |
  "occurs x (y # ys) = (if x = y then 1 else 0) + occurs x ys"

definition inter :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix "\<inter>\<^sub>p" 50)
  where
    "p \<inter>\<^sub>p q \<equiv> \<lparr>State=S p \<inter> S q,Pre=Pre p \<inter> Pre q,post=post p \<inter> post q\<rparr>"

theorem "a \<union>\<^sub>p (a \<inter>\<^sub>p b) \<equiv>\<^sub>p a"
  by (auto simp: equiv_def choice_def inter_def restr_post_def restrict_r_def)

theorem "a \<inter>\<^sub>p (a \<union>\<^sub>p b) \<equiv>\<^sub>p a"
  by (auto simp: equiv_def choice_def inter_def restr_post_def restrict_r_def)

definition set_to_list :: "'a set \<Rightarrow> 'a list"
  where "set_to_list s = (if finite s then SOME l. set l = s \<and> distinct l else [])"

(*
definition is_atomic :: "'a Program \<Rightarrow> bool"
where
  "is_atomic p \<equiv> S p = State p \<and> card (post p) \<le> 1 \<and> card (Pre p) \<le> 1 \<and> card (State p) > 0 \<and>
   (card (post p) = 1 \<and> card (Pre p) = 1 \<longrightarrow>
    fst (THE x. x \<in> post p) = (THE x. x \<in> Pre p))"
*)
definition is_atomic :: "'a Program \<Rightarrow> bool"
where
  "is_atomic p \<equiv> S p = State p \<and> card (post p) = 1 \<and> card (Pre p) = 1 \<and> State p = (Pre p) \<union> (Field (post p)) \<and>
   (card (post p) = 1 \<and> card (Pre p) = 1 \<longrightarrow>
    fst (THE x. x \<in> post p) = (THE x. x \<in> Pre p))"

(*definition get_atomic :: "'a Program \<Rightarrow> ('a Program) set"
  where
    "get_atomic p = {\<lparr>State={a,b}, Pre={a}, post={(a, b)}\<rparr> | a b .     (a,b) \<in> post p \<and> a \<in> Pre p} \<union> 
                    {\<lparr>State={a,b}, Pre={},  post={(a, b)}\<rparr> | a b .     (a,b) \<in> post p \<and> a \<notin> Pre p} \<union> 
                    {\<lparr>State={a  }, Pre={a}, post={}      \<rparr> | a   . a \<notin> Domain (post p) \<and> a \<in> Pre p} \<union>
                    {\<lparr>State={a  }, Pre={},  post={}      \<rparr> | a   . a \<notin> Field (post p) \<and> a \<notin> Pre p \<and> a \<in> State p}"*)

definition get_atomic :: "'a Program \<Rightarrow> ('a Program) set"
  where
    "get_atomic p = {\<lparr>State={a,b}, Pre={a}, post={(a, b)}\<rparr> | a b .     (a,b) \<in> post p \<and> a \<in> Pre p}"

definition evaluate :: "'a CNF \<Rightarrow> 'a set \<Rightarrow> 'a Program"
  where
    "evaluate p s \<equiv> \<Union>\<^sub>p (map (\<lambda>xs. Concat xs s) p)"

function interleave :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" (infix "\<interleave>" 150) where
  "[] \<interleave> ys = [ys]"
| "(xs) \<interleave> [] = [xs]"
| "(x#xs) \<interleave> (y#ys) = map ((#) x) (xs \<interleave> (y#ys)) @  map ((#) y) ((x#xs) \<interleave> ys)"
by pat_completeness auto
termination
  by (relation "measure (\<lambda>(xs, ys). length xs + length ys)") auto

definition cnf_concurrency :: "'a CNF \<Rightarrow> 'a CNF \<Rightarrow> 'a CNF" (infix "\<parallel>" 151) where
  "cnf_concurrency xs ys = concat [path_m \<interleave> path_n. path_m \<leftarrow> xs, path_n \<leftarrow> ys]"

value "interleave [a,b] [c,d]"

value "cnf_concurrency ([a,b]#[[c,d]]) [[e,f],[g,h]]"
value "cnf_concurrency [[e,f],[g,h]] [[a,b],[c,d]]"
value "cnf_concurrency [[a,b],[]] [[d],[e,f], []]"
value "cnf_concurrency [[a,b],[]] [[]]"

(*
definition cnf_concurrency :: "'a CNF list \<Rightarrow> 'a CNF" where
  "cnf_concurrency progs = (if size (non_empty2 progs) \<noteq> 1 then concat (concat [[interleave path_m path_n. path_m \<leftarrow> prog_i, path_n \<leftarrow> prog_j]. (i, prog_i) \<leftarrow> zip [0..<length (non_empty2 progs)] (non_empty2 progs), (j, prog_j) \<leftarrow> zip [0..<length (non_empty2 progs)] (non_empty2 progs), i \<noteq> j]) else hd (non_empty2 progs))"

notation cnf_concurrency ("\<interleave> _" [51] 51)
*)
definition is_rounded :: "'a Program \<Rightarrow> bool"
  where
    "is_rounded p \<equiv> Domain (post p) \<subseteq> Pre p"

definition is_exact :: "'a Program \<Rightarrow> bool"
  where
    "is_exact p \<equiv> is_rounded p \<and> is_feasible p"

definition feasible_version :: "'a Program \<Rightarrow> 'a Program"
  where
    "feasible_version p \<equiv> \<lparr>State = S p, Pre = Pre p \<inter> Domain (post p), post = post p\<rparr>"

definition rounded_version :: "'a Program \<Rightarrow> 'a Program"
  where
    "rounded_version p \<equiv> \<lparr>State = S p, Pre = Pre p , post = post p \<sslash>\<^sub>r Pre p\<rparr>"

definition exact_version :: "'a Program \<Rightarrow> 'a Program"
  where
    "exact_version p \<equiv> \<lparr>State = S p, Pre = Pre p \<inter> Domain (post p) , post = post p \<sslash>\<^sub>r Pre p\<rparr>"

function civilized_n :: "'a Program \<Rightarrow> 'a Program set \<Rightarrow> nat \<Rightarrow> bool"
  where
    "civilized_n x B 0 = (((x \<in> B) \<or> x = Fail {} \<or> x = Skip (complete_state (set_to_list B))) \<and> finite B)" |
    "civilized_n x B (Suc n) = (((\<exists>a b. civilized_n a B n \<and> civilized_n b B n \<and> (a ; b = x \<or> a \<union>\<^sub>p b = x)) \<and> finite B) \<or> civilized_n x B n)"
    \<comment> \<open>"civilized_n x B (Suc n) = ((\<exists>a b m m'. m<(Suc n) \<and> m'<(Suc n) \<and> civilized_n a B m \<and> civilized_n b B m' \<and> (a ; b = x \<or> a \<union>p b = x)) \<and> finite B)"\<close>
  by pat_completeness auto
termination civilized_n
  apply (relation "measure (\<lambda>(_, _, n). n)")
  by auto

theorem civ_n_finite: "civilized_n p B n \<Longrightarrow> finite B"
  by (metis civilized_n.simps(1) civilized_n.simps(2) zero_induct)

definition civilized :: "'a Program \<Rightarrow> 'a Program set \<Rightarrow> bool"
  where
    "civilized x B \<equiv> (\<exists>n. civilized_n x B n)"

definition equal_cnf :: "'a CNF \<Rightarrow> 'a CNF \<Rightarrow> bool"
  where
    "equal_cnf a b \<equiv> (set a = set b) \<and> (size a = 1) = (size b = 1)"

primrec restrict_path :: "'a Program list \<Rightarrow> 'a set \<Rightarrow> 'a Program list"
  where
    "restrict_path [] C = []" |
    "restrict_path (x#xs) C = (x \<sslash>\<^sub>p C)#xs"

definition restriction_cnf :: "'a CNF \<Rightarrow> 'a set \<Rightarrow> 'a CNF" (infix "\<sslash>\<^sub>c" 150)
  where
    "restriction_cnf p C \<equiv> [restrict_path path_p C. path_p \<leftarrow> p]"

function corestrict_path :: "'a Program list \<Rightarrow> 'a set \<Rightarrow> 'a Program list"
  where
    "corestrict_path [] C = []" |
    "corestrict_path (xs@[x]) C = xs@[x \<setminus>\<^sub>p C]"
  apply auto
  using rev_exhaust by blast
termination corestrict_path
  using "termination" by blast


definition corestriction_cnf :: "'a CNF \<Rightarrow> 'a set \<Rightarrow> 'a CNF" (infix "\<setminus>\<^sub>c" 150)
  where
    "corestriction_cnf p C \<equiv> [corestrict_path path_p C. path_p \<leftarrow> p]"

definition complete_cnf_state :: "'a CNF \<Rightarrow> 'a set"
  where
    "complete_cnf_state p \<equiv> \<Union> {complete_state tr| tr. tr \<in> set p }"

definition normal_of :: "'a CNF \<Rightarrow> 'a Program set \<Rightarrow> bool"
  where
    "normal_of p xs \<equiv> (basic p \<subseteq> (xs \<union> {Fail {}, Skip (complete_state (set_to_list xs))})) \<and> finite xs"
(*
    C = {}
    D = {a\<^sub>1, a\<^sub>2}
    p = [[]]
lemma "(evaluate [[]] {1, 2}) \<sslash>\<^sub>p {} = g" apply (auto simp: evaluate_def restrict_p_def restrict_r_def) oops
lemma "evaluate ([[]] \<sslash>\<^sub>c {}) {1, 2} = g" apply (auto simp: evaluate_def restrict_p_def restrict_r_def restriction_cnf_def) oops
theorem "C \<subseteq> D \<Longrightarrow> (evaluate p D) \<sslash>\<^sub>p C \<equiv>\<^sub>p evaluate (p \<sslash>\<^sub>c C) D" nitpick
*)

end