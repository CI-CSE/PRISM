---
layout: page
---
# Introduction
This content is automatically generated from the Isabelle theory files.

All the definitions and theorems in the paper have a corresponding theorem or definition here.

# Definitions

## Definitions.thy

**record** :: *'a Program* =
  State :: "'a set"
  Pre :: "'a set"
  post :: "'a rel"

<a id=basic>**basic \[\]** :: *'a CNF ⇒ 'a Program set*</a>

&nbsp;&nbsp;&nbsp;&nbsp;basic p ≡ foldl (∪) ({}::'a Program set) (map (set) p)

---
<a id=S>**S \[\]** :: *'a Program ⇒ 'a set*</a>

&nbsp;&nbsp;&nbsp;&nbsp;S p = State p ∪ Pre p ∪ Field (post p)

---
<a id=used_states>**used_states \[\]** :: *'a Program ⇒ 'a set*</a>

&nbsp;&nbsp;&nbsp;&nbsp;used_states p ≡ Pre p ∪ Field (post p)

---
<a id=is_feasible>**is_feasible \[\]** :: *'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p = (Pre p ⊆ Domain (post p))

---
<a id=all_feasible>**all_feasible \[\]** :: *('a Program) list ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [ ] = True

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible (x # xs) = (all_feasible xs ∧ is_feasible x)

---
<a id=cnf_feasible>**cnf_feasible \[\]** :: *'a CNF ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;cnf_feasible [ ] = True

&nbsp;&nbsp;&nbsp;&nbsp;cnf_feasible (x # xs) = (all_feasible x ∧ cnf_feasible xs)

---
<a id=is_valid>**is_valid \[\]** :: *'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;is_valid p ≡ S p = State p

---
<a id=all_valid>**all_valid \[\]** :: *('a Program) list ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;all_valid [ ] = True

&nbsp;&nbsp;&nbsp;&nbsp;all_valid (x#xs) = (all_valid xs ∧ is_valid x)

---
<a id=is_deterministic>**is_deterministic \[\]** :: *'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;is_deterministic p = is_function (post p)

---
<a id=is_functional>**is_functional \[\]** :: *'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;is_functional p ≡ ∀C⊆(S p). Image (post p) C ∩ C = {}

---
<a id=is_total>**is_total \[\]** :: *'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;is_total p = (Pre p = S p)

---
<a id=restr_post>**restr_post \[\]** :: *'a Program ⇒ 'a  rel*</a>

&nbsp;&nbsp;&nbsp;&nbsp;restr_post p = post p / Pre p

---
<a id=equal>**equal \[=\]** :: *'a Program ⇒ 'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> = p<sub>2</sub> ≡ (Pre p<sub>1</sub> = Pre p<sub>2</sub> ∧ post p<sub>1</sub> = post p<sub>2</sub> ∧ S p<sub>1</sub> = S p<sub>2</sub>)

---
<a id=equiv>**equiv \[≡\]** :: *'a Program ⇒ 'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ≡ p<sub>2</sub> ≡ (Pre p<sub>1</sub> = Pre p<sub>2</sub> ∧ restr_post p<sub>1</sub> = restr_post p<sub>2</sub>)

---
<a id=Range_p>**Range_p \[\]** :: *'a Program ⇒ 'a set*</a>

&nbsp;&nbsp;&nbsp;&nbsp;Range_p p = Range (post p / Pre p)

---
<a id=inverse>**inverse \[<sup>-</sup><sup>1</sup>\]** :: *'a Program ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;inverse p ≡ 〈State=S p, Pre=Range_p p, post=(restr_post p)⁻¹〉

---
<a id=extends>**extends \[\]** :: *'a Program ⇒ 'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;extends p<sub>2</sub> p<sub>1</sub> = (S p<sub>1</sub> ⊆ S p<sub>2</sub>)

---
<a id=weakens>**weakens \[\]** :: *'a Program ⇒ 'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;weakens p<sub>2</sub> p<sub>1</sub> = (Pre p<sub>1</sub> ⊆ Pre p<sub>2</sub>)

---
<a id=strengthens>**strengthens \[\]** :: *'a Program ⇒ 'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;strengthens p<sub>2</sub> p<sub>1</sub> ≡ ((post p<sub>2</sub>) / Pre p<sub>2</sub>) / (Pre p<sub>1</sub>) ⊆ post p<sub>1</sub>

---
<a id=refines>**refines \[⊑\]** :: *'a Program ⇒ 'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ⊑ p<sub>2</sub> = (extends p<sub>1</sub> p<sub>2</sub> ∧ weakens p<sub>1</sub> p<sub>2</sub> ∧ strengthens p<sub>1</sub> p<sub>2</sub>)

---
<a id=refines_c>**refines_c \[⊑\]** :: *'a Contracted_Program ⇒ 'a Contracted_Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;cp<sub>2</sub> ⊑ cp<sub>1</sub> ≡ a_specification cp<sub>2</sub> = a_specification cp<sub>1</sub> ∧ a_implementation cp<sub>2</sub> ⊑ a_implementation cp<sub>1</sub>

---
<a id=specialize>**specialize \[⊆\]** :: *'a Program ⇒ 'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ⊆ p<sub>2</sub> ≡ extends p<sub>2</sub> p<sub>1</sub> ∧ weakens p<sub>2</sub> p<sub>1</sub> ∧ strengthens p<sub>1</sub> p<sub>2</sub>

---
<a id=independent>**independent \[\]** :: *'a Program ⇒ 'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;independent p<sub>1</sub> p<sub>2</sub> = (Pre p<sub>1</sub> ∩ Pre p<sub>2</sub> = {})

---
<a id=implements>**implements \[\]** :: *'a Program ⇒ 'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;implements p<sub>2</sub> p<sub>1</sub> = (p<sub>2</sub> ⊑ p<sub>1</sub> ∧ is_feasible p<sub>2</sub>)

---
<a id=most_abstract_implementation>**most_abstract_implementation \[\]** :: *'a Program ⇒ 'a Contracted_Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;most_abstract_implementation p ≡ 〈a_specification=p, a_implementation=p〉

---
<a id=MAI>**MAI \[\]** :: *'a Program ⇒ 'a Contracted_Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;MAI ≡ most_abstract_implementation

---
<a id=is_correct>**is_correct \[\]** :: *'a Contracted_Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;is_correct cp = implements (a_implementation cp) (a_specification cp)

---
<a id=strongest_postcondition>**strongest_postcondition \[sp\]** :: *'a Program ⇒ 'a set ⇒ 'a rel*</a>

&nbsp;&nbsp;&nbsp;&nbsp;p sp Pre' ≡ post (p) / Pre'

---
<a id=new_behavior>**new_behavior \[\]** :: *'a Program ⇒ 'a rel ⇒ 'a rel*</a>

&nbsp;&nbsp;&nbsp;&nbsp;new_behavior p post' ≡ post p - post'

---
<a id=weakest_precondition>**weakest_precondition \[wp\]** :: *'a Program ⇒ 'a rel ⇒ 'a set*</a>

&nbsp;&nbsp;&nbsp;&nbsp;p wp post' ≡ Pre p - Domain (new_behavior p post')

---
<a id=choice>**choice \[∪\]** :: *'a Program ⇒ 'a Program ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ∪ p<sub>2</sub> = 〈State= S p<sub>1</sub> ∪ S p<sub>2</sub>, Pre = Pre p<sub>1</sub> ∪ Pre p<sub>2</sub>, post = restr_post p<sub>1</sub> ∪ restr_post p<sub>2</sub>〉

---
<a id=non_empty>**non_empty \[\]** :: *'a CNF ⇒ 'a CNF*</a>

&nbsp;&nbsp;&nbsp;&nbsp;non_empty xs ≡ [t . t ← xs, t ≠ [ ]]

---
<a id=non_empty2>**non_empty2 \[\]** :: *'a CNF list ⇒ 'a CNF list*</a>

&nbsp;&nbsp;&nbsp;&nbsp;non_empty2 xs ≡ [prog2. prog2 ← [non_empty prog. prog ← xs], prog2 ≠ [ ]]

---
<a id=choice_cnf>**choice_cnf \[∪\]** :: *'a CNF ⇒ 'a CNF ⇒ 'a CNF*</a>

&nbsp;&nbsp;&nbsp;&nbsp;choice_cnf a b ≡ a @ b

---
<a id=composition_cnf>**composition_cnf \[;\]** :: *'a CNF ⇒ 'a CNF ⇒ 'a CNF*</a>

&nbsp;&nbsp;&nbsp;&nbsp;composition_cnf a b ≡ [xs @ ys. xs ← a, ys ← b]

---
<a id=is_prime>**is_prime \[\]** :: *'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;is_prime p ≡ card (Pre p) = 1 ∧ card (post p) = 1 ∧ Pre p ∪ Field (post p) = State p

---
<a id=composition>**composition \[;\]** :: *'a Program ⇒ 'a Program ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ; p<sub>2</sub> = 〈
      State = S p<sub>1</sub> ∪ S p<sub>2</sub>,
      Pre = Pre p<sub>1</sub> ∩ Domain (post p<sub>1</sub> ∖ Pre p<sub>2</sub>),
      post = (post p<sub>1</sub>) O (restr_post p<sub>2</sub>)〉

---
<a id=commute_programs1>**commute_programs1 \[\]** :: *'a Program ⇒ 'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;commute_programs1 p<sub>1</sub> p<sub>2</sub> ≡ (p<sub>1</sub> ; p<sub>2</sub>) = (p<sub>2</sub> ; p<sub>1</sub>)

---
<a id=commute_programs2>**commute_programs2 \[\]** :: *'a Program ⇒ 'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;commute_programs2 p<sub>1</sub> p<sub>2</sub> ≡ (p<sub>1</sub> ; p<sub>2</sub>) = (p<sub>2</sub> ; p<sub>1</sub>)

---
<a id=commute_programs3>**commute_programs3 \[\]** :: *'a Program ⇒ 'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;commute_programs3 p<sub>1</sub> p<sub>2</sub> ≡ (p<sub>1</sub> ; p<sub>2</sub>) ≡ (p<sub>2</sub> ; p<sub>1</sub>)

---
<a id=unsafe_composition>**unsafe_composition \[;\]** :: *'a Program ⇒ 'a Program ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ; p<sub>2</sub> = 〈
      State = S p<sub>1</sub> ∪ S p<sub>2</sub>,
      Pre = Pre p<sub>1</sub>,
      post = (post p<sub>1</sub>) O (restr_post p<sub>2</sub>)〉

---
<a id=unsafe_composition2>**unsafe_composition2 \[;<sup>p</sup>\]** :: *'a Program ⇒ 'a Program ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ;<sup>p</sup> p<sub>2</sub> = 〈
      State = S p<sub>1</sub> ∪ S p<sub>2</sub>,
      Pre = Pre p<sub>1</sub> ∩ Domain (post p<sub>1</sub> ∖ Pre p<sub>2</sub>),
      post = (post p<sub>1</sub>) O (post p<sub>2</sub>)〉

---
<a id=unsafe_composition3>**unsafe_composition3 \[;<sub>P</sub>\]** :: *'a Program ⇒ 'a Program ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ;<sub>P</sub> p<sub>2</sub> = 〈
      State = S p<sub>1</sub> ∪ S p<sub>2</sub>,
      Pre = Pre p<sub>1</sub>,
      post = (post p<sub>1</sub>) O (post p<sub>2</sub>)〉

---
<a id=restrict_p>**restrict_p \[/\]** :: *'a Program ⇒ 'a set ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;restrict_p p C = 〈State= S p, Pre=Pre p ∩ C, post=post p / C〉

---
<a id=corestrict_p>**corestrict_p \[∖\]** :: *'a Program ⇒ 'a set ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;corestrict_p p C = 〈State= S p, 
        Pre=Pre p, \
        post=post p ∖ C〉

---
<a id=char_rel>**char_rel \[\]** :: *'a Program ⇒ 'a rel*</a>

&nbsp;&nbsp;&nbsp;&nbsp;char_rel p = post p / Pre p

---
<a id=Fail>**Fail \[\]** :: *'a set ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;Fail s = 〈 State = s, Pre = {}, post = {}〉

---
<a id=Havoc>**Havoc \[\]** :: *'a set ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;Havoc s = 〈 State = s, Pre = s, post = {(x,y). x ∈ s ∧ y ∈ s}〉

---
<a id=Skip>**Skip \[\]** :: *'a set ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;Skip s = 〈 State = s, Pre = s, post = {(x,y). x ∈ s ∧ x = y} 〉

---
<a id=Infeas>**Infeas \[\]** :: *'a set ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;Infeas s = 〈 State = s, Pre = s, post = {} 〉

---
<a id=generalized_non_atomic_conc>**generalized_non_atomic_conc \[∥<sub>G</sub>\]** :: *('a Program) list ⇒ 'a Program ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;[ ]     ∥<sub>G</sub> q = q

&nbsp;&nbsp;&nbsp;&nbsp;(x#xs) ∥<sub>G</sub> q = ((xs ∥<sub>G</sub> q) ; x) ∪ (x ; (xs ∥<sub>G</sub> q))

---
<a id=if_then_else>**if_then_else \[\]** :: *'a set ⇒ 'a Program ⇒ 'a Program ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;if_then_else C p<sub>1</sub> p<sub>2</sub> ≡ (p<sub>1</sub> / C) ∪ (p<sub>2</sub> / (-C))

---
<a id=ITE>**ITE \[\]** :: *'a set ⇒ 'a Program ⇒ 'a Program ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;ITE ≡ if_then_else

---
<a id=if_then>**if_then \[\]** :: *'a set ⇒ 'a Program ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;if_then C p ≡ ITE C p (Skip (S p))

---
<a id=TRUE>**TRUE \[\]** :: *'a set ⇒ 'a set*</a>

&nbsp;&nbsp;&nbsp;&nbsp;TRUE s = s

---
<a id=FALSE>**FALSE \[\]** :: *'a set*</a>

&nbsp;&nbsp;&nbsp;&nbsp;FALSE = {}

---
<a id=ID>**ID \[\]** :: *'a set ⇒ 'a rel*</a>

&nbsp;&nbsp;&nbsp;&nbsp;ID s ≡ {(a,b) . a ∈ s ∧ b ∈ s ∧ a = b}

---
<a id=fixed_repetition_helper>**fixed_repetition_helper \[^<sup>p</sup>\]** :: *'a Program ⇒ nat ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;fixed_repetition_helper p 0       = Skip (S p)

&nbsp;&nbsp;&nbsp;&nbsp;fixed_repetition_helper p (i + 1) = fixed_repetition_helper p i ; p

---
<a id=fixed_repetition>**fixed_repetition \[<sup>^</sup>\]** :: *'a Program ⇒ nat ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;p<sup>0</sup>       = Skip (S p) / (Pre p)

&nbsp;&nbsp;&nbsp;&nbsp;p<sup>i + 1</sup> = p<sup>i</sup>;p

---
<a id=Choice>**Choice \[⋃\]** :: *('a Program) list ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;Choice [ ] = Fail {}

&nbsp;&nbsp;&nbsp;&nbsp;Choice [x] = x

&nbsp;&nbsp;&nbsp;&nbsp;Choice (x#xs) = foldl (∪) x xs

---
<a id=Concat>**Concat \[\]** :: *('a Program) list ⇒ 'a set ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;Concat [ ] s = (Skip s)

&nbsp;&nbsp;&nbsp;&nbsp;Concat [x] s = x

&nbsp;&nbsp;&nbsp;&nbsp;Concat (x#xs) s = foldl (;) x xs

---
<a id=Choice_set>**Choice_set \[⋃<sub>P</sub>\]** :: *('a Program) set ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;Choice_set P ≡ Finite_Set.fold (∪) (Fail {}) P

---
<a id=is_minimal>**is_minimal \[\]** :: *'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;is_minimal p ≡ (∀a b. (a,b) ∈ post p → a ∈ Pre p) ∧ is_valid p ∧ (∀ s ∈ State p. s ∈ Field (post p))

---
<a id=guarded_conditional>**guarded_conditional \[\]** :: *('a set × 'a Program) list ⇒  'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;guarded_conditional xs = ⋃ [snd t / fst t. t ← xs]

---
<a id=GC>**GC \[\]** :: *('a set × 'a Program) list ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;GC ≡ guarded_conditional

---
<a id=insert_all>**insert_all \[\]** :: *'a ⇒ 'a list ⇒ 'a list list*</a>

&nbsp;&nbsp;&nbsp;&nbsp;insert_all x [ ] = [[x]]

&nbsp;&nbsp;&nbsp;&nbsp;insert_all x (y#ys) = (x#y#ys) # (map (λzs. y#zs) (insert_all x ys))

---
<a id=permutations>**permutations \[\]** :: *'a list ⇒ 'a list list*</a>

&nbsp;&nbsp;&nbsp;&nbsp;permutations [ ] = [[ ]]

&nbsp;&nbsp;&nbsp;&nbsp;permutations (x#xs) = concat (map (insert_all x) (permutations xs))

---
<a id=complete_state>**complete_state \[\]** :: *'a Program list ⇒ 'a set*</a>

&nbsp;&nbsp;&nbsp;&nbsp;complete_state xs ≡ fold (λ p s. S p ∪ s) xs {}

---
<a id=n_comp>**n_comp \[\]** :: *'a Program list ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;n_comp [ ] = Fail {}

&nbsp;&nbsp;&nbsp;&nbsp;n_comp (x#xs) = x ; (n_comp xs)

---
<a id=conc_elems>**conc_elems \[\]** :: *'a Program list ⇒ 'a Program list*</a>

&nbsp;&nbsp;&nbsp;&nbsp;conc_elems xs ≡ [Concat t (complete_state t). t ← permutations xs]

---
<a id=atomic_conc>**atomic_conc \[\]** :: *'a Program list ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;atomic_conc xs ≡ ⋃ (conc_elems xs)

---
<a id=non_atomic_conc>**non_atomic_conc \[∥<sub>n</sub>\]** :: *'a Program list ⇒ 'a Program ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;xs ∥<sub>n</sub> x ≡ ⋃ [Concat t (complete_state t). t ← insert_all x xs]

---
<a id=arbitrary_repetition_set>**arbitrary_repetition_set \[\]** :: *'a Program ⇒ 'a Program set*</a>

&nbsp;&nbsp;&nbsp;&nbsp;arbitrary_repetition_set p ≡ {p<sup>i</sup> | i . 0&lt;i}

---
<a id=arbitrary_repetition>**arbitrary_repetition \[\]** :: *'a Program ⇒ nat ⇒ nat ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;arbitrary_repetition p s 0 = (if s>0 then Fail (S p) else p<sup>0</sup>)

&nbsp;&nbsp;&nbsp;&nbsp;arbitrary_repetition p s (f + 1) = (if s>(f + 1) then Fail (S p) else p<sup>f + 1</sup> ∪ arbitrary_repetition p s f)

---
<a id=loop>**loop \[\]** :: *'a Program ⇒ nat ⇒ nat ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;loop ≡ arbitrary_repetition

---
<a id=until_support>**until_support \[\]** :: *'a Program ⇒ 'a set ⇒ 'a Program ⇒ nat ⇒ nat ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;until_support a C b s f = a ; (loop (b/(-C)) s f)∖ C

---
<a id=until_loop>**until_loop \[\]** :: *'a Program ⇒ 'a set ⇒ 'a Program ⇒ nat ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;until_loop a C b n = a ; (loop (b/(-C)) 0 n)∖ C

---
<a id=is_invariant>**is_invariant \[\]** :: *'a set ⇒ 'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I p ≡ Range_p (p / I) ⊆ I

---
<a id=is_loop_invariant>**is_loop_invariant \[\]** :: *'a set ⇒ 'a Program ⇒ 'a set ⇒ 'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;is_loop_invariant I a C b ≡ Range_p a ⊆ I ∧ is_invariant I (b/(-C))

---
<a id=markovian>**markovian \[\]** :: *'a rel ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;markovian r ≡ ∀s s<sub>1</sub> s<sub>2</sub>. ((s<sub>1</sub>, s) ∈ r) = ((s<sub>2</sub>, s) ∈ r)

---
<a id=is_trivial>**is_trivial \[\]** :: *'a rel ⇒ 'a ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;is_trivial r s ≡ ∀s<sub>1</sub>. (s, s<sub>1</sub>) ∈ r

---
<a id=is_irrelevant>**is_irrelevant \[\]** :: *'a rel ⇒ 'a ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;is_irrelevant r s ≡ ∀s<sub>1</sub> s<sub>2</sub>. ((s, s<sub>1</sub>) ∈ r) = ((s, s<sub>2</sub>) ∈ r)

---
<a id=is_relevant>**is_relevant \[\]** :: *'a rel ⇒ 'a ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;is_relevant r s ≡ ¬ is_irrelevant r s

---
<a id=is_programming_language>**is_programming_language \[\]** :: *'a set ⇒ ('a Program) set ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;is_programming_language s P ≡ ∀p ∈ P. is_feasible p ∧ S p ⊆ s

---
<a id=occurs>**occurs \[\]** :: *'a ⇒ 'a list ⇒ nat*</a>

&nbsp;&nbsp;&nbsp;&nbsp;occurs _ [ ] = 0

&nbsp;&nbsp;&nbsp;&nbsp;occurs x (y # ys) = (if x = y then 1 else 0) + occurs x ys

---
<a id=inter>**inter \[∩\]** :: *'a Program ⇒ 'a Program ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;p ∩ q ≡ 〈State=S p ∩ S q,Pre=Pre p ∩ Pre q,post=post p ∩ post q〉

---
<a id=set_to_list>**set_to_list \[\]** :: *'a set ⇒ 'a list*</a>

&nbsp;&nbsp;&nbsp;&nbsp;set_to_list s = (if finite s then SOME l. set l = s ∧ distinct l else [ ])

---
<a id=is_atomic>**is_atomic \[\]** :: *'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;is_atomic p ≡ S p = State p ∧ card (post p) = 1 ∧ card (Pre p) = 1 ∧ State p = (Pre p) ∪ (Field (post p)) ∧
   (card (post p) = 1 ∧ card (Pre p) = 1 →
    fst (THE x. x ∈ post p) = (THE x. x ∈ Pre p))

---
<a id=get_atomic>**get_atomic \[\]** :: *'a Program ⇒ ('a Program) set*</a>

&nbsp;&nbsp;&nbsp;&nbsp;get_atomic p = {〈State={a,b}, Pre={a}, post={(a, b)} 〉 | a b .     (a,b) ∈ post p ∧ a ∈ Pre p}

---
<a id=evaluate>**evaluate \[\]** :: *'a CNF ⇒ 'a set ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;evaluate p s ≡ ⋃ (map (λxs. Concat xs s) p)

---
<a id=interleave>**interleave \[⫴\]** :: *'a list ⇒ 'a list ⇒ 'a list list*</a>

&nbsp;&nbsp;&nbsp;&nbsp;[ ] ⫴ ys = [ys]

&nbsp;&nbsp;&nbsp;&nbsp;(xs) ⫴ [ ] = [xs]

&nbsp;&nbsp;&nbsp;&nbsp;(x#xs) ⫴ (y#ys) = map ((#) x) (xs ⫴ (y#ys)) @  map ((#) y) ((x#xs) ⫴ ys)

---
<a id=cnf_concurrency>**cnf_concurrency \[∥\]** :: *'a CNF ⇒ 'a CNF ⇒ 'a CNF*</a>

&nbsp;&nbsp;&nbsp;&nbsp;cnf_concurrency xs ys = concat [path_m ⫴ path_n. path_m ← xs, path_n ← ys]

---
<a id=is_rounded>**is_rounded \[\]** :: *'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;is_rounded p ≡ Domain (post p) ⊆ Pre p

---
<a id=is_exact>**is_exact \[\]** :: *'a Program ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;is_exact p ≡ is_rounded p ∧ is_feasible p

---
<a id=feasible_version>**feasible_version \[\]** :: *'a Program ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;feasible_version p ≡ 〈State = S p, Pre = Pre p ∩ Domain (post p), post = post p〉

---
<a id=rounded_version>**rounded_version \[\]** :: *'a Program ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;rounded_version p ≡ 〈State = S p, Pre = Pre p , post = post p / Pre p〉

---
<a id=exact_version>**exact_version \[\]** :: *'a Program ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;exact_version p ≡ 〈State = S p, Pre = Pre p ∩ Domain (post p) , post = post p / Pre p〉

---
<a id=civilized_n>**civilized_n \[\]** :: *'a Program ⇒ 'a Program set ⇒ nat ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;civilized_n x B 0 = (((x ∈ B) ∨ x = Fail {} ∨ x = Skip (complete_state (set_to_list B))) ∧ finite B)

&nbsp;&nbsp;&nbsp;&nbsp;civilized_n x B (n + 1) = (((∃a b. civilized_n a B n ∧ civilized_n b B n ∧ (a ; b = x ∨ a ∪ b = x)) ∧ finite B) ∨ civilized_n x B n)

---
<a id=civilized>**civilized \[\]** :: *'a Program ⇒ 'a Program set ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;civilized x B ≡ (∃n. civilized_n x B n)

---
<a id=equal_cnf>**equal_cnf \[\]** :: *'a CNF ⇒ 'a CNF ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;equal_cnf a b ≡ (set a = set b) ∧ (size a = 1) = (size b = 1)

---
<a id=restrict_path>**restrict_path \[\]** :: *'a Program list ⇒ 'a set ⇒ 'a Program list*</a>

&nbsp;&nbsp;&nbsp;&nbsp;restrict_path [ ] C = [ ]

&nbsp;&nbsp;&nbsp;&nbsp;restrict_path (x#xs) C = (x / C)#xs

---
<a id=restriction_cnf>**restriction_cnf \[/\]** :: *'a CNF ⇒ 'a set ⇒ 'a CNF*</a>

&nbsp;&nbsp;&nbsp;&nbsp;restriction_cnf p C ≡ [restrict_path path_p C. path_p ← p]

---
<a id=corestrict_path>**corestrict_path \[\]** :: *'a Program list ⇒ 'a set ⇒ 'a Program list*</a>

&nbsp;&nbsp;&nbsp;&nbsp;corestrict_path [ ] C = [ ]

&nbsp;&nbsp;&nbsp;&nbsp;corestrict_path (xs@[x]) C = xs@[x ∖ C]

---
<a id=corestriction_cnf>**corestriction_cnf \[∖\]** :: *'a CNF ⇒ 'a set ⇒ 'a CNF*</a>

&nbsp;&nbsp;&nbsp;&nbsp;corestriction_cnf p C ≡ [corestrict_path path_p C. path_p ← p]

---
<a id=complete_cnf_state>**complete_cnf_state \[\]** :: *'a CNF ⇒ 'a set*</a>

&nbsp;&nbsp;&nbsp;&nbsp;complete_cnf_state p ≡ ⋃ {complete_state tr| tr. tr ∈ set p }

---
<a id=normal_of>**normal_of \[\]** :: *'a CNF ⇒ 'a Program set ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;normal_of p xs ≡ (basic p ⊆ (xs ∪ {Fail {}, Skip (complete_state (set_to_list xs))})) ∧ finite xs

---
<a id=feas_of>**feas_of \[\]** :: *'a Program ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;feas_of p ≡ 〈State=S p, Pre=Pre p ∩ Domain (post p), post=post p〉

---
<a id=set_to_list_r>**set_to_list_r \[\]** :: *'a set ⇒ 'a list*</a>

&nbsp;&nbsp;&nbsp;&nbsp;set_to_list_r s = (SOME l. set l = s)

---
<a id=factorial>**factorial \[\]** :: *nat ⇒ nat*</a>

&nbsp;&nbsp;&nbsp;&nbsp;factorial 0 = 1

&nbsp;&nbsp;&nbsp;&nbsp;factorial (n + 1) = (n + 1) * factorial n

---
<a id=sum>**sum \[\]** :: *nat list ⇒ nat*</a>

&nbsp;&nbsp;&nbsp;&nbsp;sum [ ] = 0

&nbsp;&nbsp;&nbsp;&nbsp;sum (x#xs) = x + sum xs

---
<a id=nmb_interleavings_pre>**nmb_interleavings_pre \[\]** :: *nat ⇒ nat ⇒ nat*</a>

&nbsp;&nbsp;&nbsp;&nbsp;nmb_interleavings_pre x y ≡ factorial (x + y) div (factorial x * factorial y)

---
<a id=nmb_interleavings>**nmb_interleavings \[\]** :: *'a list ⇒ 'a list ⇒ nat*</a>

&nbsp;&nbsp;&nbsp;&nbsp;nmb_interleavings xs ys ≡ nmb_interleavings_pre (size xs) (size ys)

---
<a id=list_equiv>**list_equiv \[\]** :: *'a Program list ⇒ 'a Program list ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;list_equiv [ ] [ ] = True

&nbsp;&nbsp;&nbsp;&nbsp;list_equiv (x#xs) (y#ys) = ((x ≡ y) ∧ list_equiv xs ys)

&nbsp;&nbsp;&nbsp;&nbsp;list_equiv _ _ = False

---
<a id=cnf_size>**cnf_size \[\]** :: *'a CNF ⇒ nat*</a>

&nbsp;&nbsp;&nbsp;&nbsp;cnf_size [ ] = 0

&nbsp;&nbsp;&nbsp;&nbsp;cnf_size (x#xs) = length x + cnf_size xs + 1

---
<a id=equiv_list>**equiv_list \[\]** :: *'a Program list ⇒ 'a Program list ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;equiv_list [ ] [ ] = True

&nbsp;&nbsp;&nbsp;&nbsp;equiv_list (x#xs) [ ] = False

&nbsp;&nbsp;&nbsp;&nbsp;equiv_list [ ] (y#ys) = False

&nbsp;&nbsp;&nbsp;&nbsp;equiv_list (x#xs) (y#ys) = (x ≡ y ∧ equiv_list xs ys)

---
<a id=cnf_concurrency2>**cnf_concurrency2 \[\]** :: *'a CNF ⇒ 'a CNF ⇒ 'a set ⇒ 'a Program*</a>

&nbsp;&nbsp;&nbsp;&nbsp;cnf_concurrency2 [ ] ys C = Fail {}

&nbsp;&nbsp;&nbsp;&nbsp;cnf_concurrency2 xs [ ] C = Fail {}

&nbsp;&nbsp;&nbsp;&nbsp;cnf_concurrency2 (x#xs) (y#ys) C = 
     (case (xs , ys) of
        ([ ], [ ]) ⇒ (case (x, y) of 
          ([ ], [ ]) ⇒ Skip C |
          ([a], [b]) ⇒ a;b ∪ b;a |
          ([ ], bs) ⇒ evaluate [bs] C |
          (as, [ ]) ⇒ evaluate [as] C |
          (a#as, b#bs) ⇒ a; (cnf_concurrency2 [as] [b#bs] C) ∪ b; (cnf_concurrency2 [a#as] [bs] C)) |
        (f#fs, [ ]) ⇒ cnf_concurrency2 [x] [y] C ∪ cnf_concurrency2 (f#fs) [y] C |
        ([ ], g#gs) ⇒ cnf_concurrency2 [x] [y] C ∪ cnf_concurrency2 [x] (g#gs) C |
        (f#fs, g#gs) ⇒ cnf_concurrency2 [x] (y#g#gs) C ∪ cnf_concurrency2 (f#fs) (y#g#gs) C
  )

---
## Relation_operations.thy

<a id=restrict_r>**restrict_r \[/\]** :: *'a rel ⇒ 'a set ⇒ 'a rel*</a>

&nbsp;&nbsp;&nbsp;&nbsp;restrict_r R S = {r ∈ R. fst r ∈ S}

---
<a id=inv_restrict_r>**inv_restrict_r \[/<sub>-</sub>\]** :: *'a rel ⇒ 'a set ⇒ 'a rel*</a>

&nbsp;&nbsp;&nbsp;&nbsp;inv_restrict_r R S = {r ∈ R. fst r ∉ S}

---
<a id=corestrict_r>**corestrict_r \[∖\]** :: *'a rel ⇒ 'a set ⇒ 'a rel*</a>

&nbsp;&nbsp;&nbsp;&nbsp;corestrict_r R S = {r ∈ R. snd r ∈ S}

---
<a id=inv_corestrict_r>**inv_corestrict_r \[∖<sub>-</sub>\]** :: *'a rel ⇒ 'a set ⇒ 'a rel*</a>

&nbsp;&nbsp;&nbsp;&nbsp;inv_corestrict_r R S = {r ∈ R. snd r ∉ S}

---
<a id=is_function>**is_function \[\]** :: *'a rel ⇒ bool*</a>

&nbsp;&nbsp;&nbsp;&nbsp;is_function R = (∀r<sub>1</sub> ∈ R.∀r<sub>2</sub>∈R. fst r<sub>1</sub> = fst r<sub>2</sub> → snd r<sub>1</sub> = snd r<sub>2</sub>)

---
# Theorems and Lemmas

## PRISM.thy

**cond_for_commutative_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Range_p" title=Range_p>Range_p</a> p<sub>1</sub> ∩ Pre p<sub>2</sub> = {} ⟹ <a href="#Range_p" title=Range_p>Range_p</a> p<sub>2</sub> ∩ Pre p<sub>1</sub> = {} ⟹ <a href="#commute_programs3" title=commute_programs3>commute_programs3</a> p<sub>1</sub> p<sub>2</sub>

---
**distinct_state_range_dist_from_pre**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#used_states" title=used_states>used_states</a> p<sub>1</sub> ∩ <a href="#used_states" title=used_states>used_states</a> p<sub>2</sub> = {} ⟹ <a href="#Range_p" title=Range_p>Range_p</a> p<sub>1</sub> ∩ Pre p<sub>2</sub> = {} ∧ <a href="#Range_p" title=Range_p>Range_p</a> p<sub>2</sub> ∩ Pre p<sub>1</sub> = {}

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#used_states" title=used_states>used_states</a> p<sub>1</sub> ∩ <a href="#used_states" title=used_states>used_states</a> p<sub>2</sub> = {} ⟹ <a href="#commute_programs1" title=commute_programs1>commute_programs1</a> p<sub>1</sub> p<sub>2</sub>

---
&nbsp;&nbsp;&nbsp;&nbsp;x <a href="#composition" title=composition>;</a> <a href="#until_loop" title=until_loop>until_loop</a> a C b n <a href="#equiv" title=equiv>≡</a> <a href="#until_loop" title=until_loop>until_loop</a> (x <a href="#composition" title=composition>;</a> a) C b n

---
&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#composition" title=composition>;</a> q <a href="#equiv" title=equiv>≡</a> p <a href="#composition" title=composition>;</a> (q <a href="#restrict_p" title=restrict_p>/</a> (<a href="#Range_p" title=Range_p>Range_p</a> p))

---
## T_03_Basic_programs.thy

**special_empty1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> {} = <a href="#Fail" title=Fail>Fail</a> {}

---
**special_empty2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Havoc" title=Havoc>Havoc</a> {} = <a href="#Fail" title=Fail>Fail</a> {}

---
**special_empty3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Havoc" title=Havoc>Havoc</a> {} = <a href="#Infeas" title=Infeas>Infeas</a> {}

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Havoc" title=Havoc>Havoc</a> C = 〈State=C, Pre=TRUE C, post=TRUE C 〉

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> C = 〈State=C, Pre=TRUE C, post=ID C〉

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Fail" title=Fail>Fail</a> C = 〈State=C, Pre=FALSE, post=FALSE〉

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Infeas" title=Infeas>Infeas</a> C = 〈State=C, Pre=TRUE C, post=FALSE〉

---
**special_refine1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Infeas" title=Infeas>Infeas</a> C <a href="#refines" title=refines>⊑</a> <a href="#Skip" title=Skip>Skip</a> C

---
**special_refine2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> C <a href="#refines" title=refines>⊑</a> <a href="#Havoc" title=Havoc>Havoc</a> C

---
**special_refine3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Havoc" title=Havoc>Havoc</a> C <a href="#refines" title=refines>⊑</a> <a href="#Fail" title=Fail>Fail</a> C

---
**special_refine4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Infeas" title=Infeas>Infeas</a> C <a href="#refines" title=refines>⊑</a> <a href="#Fail" title=Fail>Fail</a> C

---
**special_specialize1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Fail" title=Fail>Fail</a> C <a href="#specialize" title=specialize>⊆</a> <a href="#Infeas" title=Infeas>Infeas</a> C

---
**special_specialize2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Infeas" title=Infeas>Infeas</a> C <a href="#specialize" title=specialize>⊆</a> <a href="#Skip" title=Skip>Skip</a> C

---
**special_specialize3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> C <a href="#specialize" title=specialize>⊆</a> <a href="#Havoc" title=Havoc>Havoc</a> C

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ <a href="#Fail" title=Fail>Fail</a> D <a href="#refines" title=refines>⊑</a> <a href="#Fail" title=Fail>Fail</a> C

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ <a href="#Fail" title=Fail>Fail</a> C <a href="#specialize" title=specialize>⊆</a> <a href="#Fail" title=Fail>Fail</a> D

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ <a href="#Infeas" title=Infeas>Infeas</a> D <a href="#refines" title=refines>⊑</a> <a href="#Infeas" title=Infeas>Infeas</a> C

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ <a href="#Infeas" title=Infeas>Infeas</a> C <a href="#specialize" title=specialize>⊆</a> <a href="#Infeas" title=Infeas>Infeas</a> D

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ <a href="#Skip" title=Skip>Skip</a> D <a href="#refines" title=refines>⊑</a> <a href="#Skip" title=Skip>Skip</a> C

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ <a href="#Skip" title=Skip>Skip</a> C <a href="#specialize" title=specialize>⊆</a> <a href="#Skip" title=Skip>Skip</a> D

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ <a href="#Havoc" title=Havoc>Havoc</a> C <a href="#refines" title=refines>⊑</a> <a href="#Havoc" title=Havoc>Havoc</a> D

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ <a href="#Havoc" title=Havoc>Havoc</a> D <a href="#refines" title=refines>⊑</a> <a href="#Havoc" title=Havoc>Havoc</a> C

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ <a href="#Havoc" title=Havoc>Havoc</a> C <a href="#specialize" title=specialize>⊆</a> <a href="#Havoc" title=Havoc>Havoc</a> D

---
## Characteristic_relation.thy

**char_rel_is_unique_in_equality_1**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> = p<sub>2</sub> ⟹ <a href="#char_rel" title=char_rel>char_rel</a> p<sub>1</sub> = <a href="#char_rel" title=char_rel>char_rel</a> p<sub>2</sub>

---
**equal_charrel1**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#equal" title=equal>=</a> p<sub>2</sub> ⟹ <a href="#char_rel" title=char_rel>char_rel</a> p<sub>1</sub> = <a href="#char_rel" title=char_rel>char_rel</a> p<sub>2</sub>

---
**equiv_charrel1**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub> ⟹ <a href="#char_rel" title=char_rel>char_rel</a> p<sub>1</sub> = <a href="#char_rel" title=char_rel>char_rel</a> p<sub>2</sub>

---
**char_rel_is_unique_in_equality_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p<sub>1</sub>, p<sub>2</sub>] ⟹ (<a href="#char_rel" title=char_rel>char_rel</a> p<sub>1</sub> = <a href="#char_rel" title=char_rel>char_rel</a> p<sub>2</sub>) ⟹ (p<sub>1</sub> = p<sub>2</sub>)

---
**char_rel_is_unique_in_equal_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p<sub>1</sub>, p<sub>2</sub>] ⟹ (<a href="#char_rel" title=char_rel>char_rel</a> p<sub>1</sub> = <a href="#char_rel" title=char_rel>char_rel</a> p<sub>2</sub>) ⟹ (p<sub>1</sub> <a href="#equal" title=equal>=</a> p<sub>2</sub>)

---
**equiv_charrel2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p<sub>1</sub>, p<sub>2</sub>] ⟹ (<a href="#char_rel" title=char_rel>char_rel</a> p<sub>1</sub> = <a href="#char_rel" title=char_rel>char_rel</a> p<sub>2</sub>) = (p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub>)

---
**char_rel_choice**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#char_rel" title=char_rel>char_rel</a> (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>) = <a href="#char_rel" title=char_rel>char_rel</a> p<sub>1</sub> ∪ <a href="#char_rel" title=char_rel>char_rel</a> p<sub>2</sub>

---
**char_rel_composition**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#char_rel" title=char_rel>char_rel</a> (p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>) = <a href="#char_rel" title=char_rel>char_rel</a> p<sub>1</sub> O <a href="#char_rel" title=char_rel>char_rel</a> p<sub>2</sub>

---
**char_rel_restriction**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#char_rel" title=char_rel>char_rel</a> (p <a href="#restrict_p" title=restrict_p>/</a> C) = <a href="#char_rel" title=char_rel>char_rel</a> p <a href="#restrict_r" title=restrict_r>/</a> C

---
**char_rel_corestriction**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#char_rel" title=char_rel>char_rel</a> (p <a href="#corestrict_p" title=corestrict_p>∖</a> C) = <a href="#char_rel" title=char_rel>char_rel</a> p <a href="#corestrict_r" title=corestrict_r>∖</a> C

---
**char_rel_strengthens**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#strengthens" title=strengthens>strengthens</a> p<sub>1</sub> p<sub>2</sub> ⟹ <a href="#char_rel" title=char_rel>char_rel</a> p<sub>1</sub> <a href="#restrict_r" title=restrict_r>/</a> Domain (<a href="#char_rel" title=char_rel>char_rel</a> p<sub>2</sub>) ⊆ <a href="#char_rel" title=char_rel>char_rel</a> p<sub>2</sub>

---
**char_rel_weakens**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p<sub>1</sub> ⟹ <a href="#weakens" title=weakens>weakens</a> p<sub>1</sub> p<sub>2</sub> ⟹ Domain (<a href="#char_rel" title=char_rel>char_rel</a> p<sub>2</sub>) ⊆ Domain (<a href="#char_rel" title=char_rel>char_rel</a> p<sub>1</sub>)

---
**char_rel_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#refines" title=refines>⊑</a> q ⟹ <a href="#char_rel" title=char_rel>char_rel</a> p <a href="#restrict_r" title=restrict_r>/</a> (Domain (<a href="#char_rel" title=char_rel>char_rel</a> q)) ⊆ <a href="#char_rel" title=char_rel>char_rel</a> q

---
**charrel_strengthen**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p, q] ⟹ <a href="#char_rel" title=char_rel>char_rel</a> p <a href="#restrict_r" title=restrict_r>/</a> (Domain (<a href="#char_rel" title=char_rel>char_rel</a> q)) ⊆ <a href="#char_rel" title=char_rel>char_rel</a> q = <a href="#strengthens" title=strengthens>strengthens</a> p q

---
**charrel_weaken**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p, q] ⟹ Domain (<a href="#char_rel" title=char_rel>char_rel</a> q) ⊆ Domain (<a href="#char_rel" title=char_rel>char_rel</a> p) = <a href="#weakens" title=weakens>weakens</a> p q

---
**charrel_specialize**

&nbsp;&nbsp;&nbsp;&nbsp;q <a href="#specialize" title=specialize>⊆</a> p ⟹ <a href="#char_rel" title=char_rel>char_rel</a> q &lt; <a href="#char_rel" title=char_rel>char_rel</a> p

---
**charrel_refine**

&nbsp;&nbsp;&nbsp;&nbsp;q <a href="#refines" title=refines>⊑</a> p ⟹ <a href="#char_rel" title=char_rel>char_rel</a> q <a href="#restrict_r" title=restrict_r>/</a> (Pre p) &lt; <a href="#char_rel" title=char_rel>char_rel</a> p

---
**char_rel_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;Field (<a href="#char_rel" title=char_rel>char_rel</a> a) ⊆ <a href="#S" title=S>S</a> a

---
## Definitions.thy

&nbsp;&nbsp;&nbsp;&nbsp;〈State={}, Pre={1::nat}, post={(1,2)}〉 <a href="#specialize" title=specialize>⊆</a> 〈State={}, Pre={1::nat}, post={(1,2)}〉

---
&nbsp;&nbsp;&nbsp;&nbsp;Pre p ⊆ I ∧ <a href="#Range_p" title=Range_p>Range_p</a> p ⊆ I ⟹ <a href="#Range_p" title=Range_p>Range_p</a> (p <a href="#restrict_p" title=restrict_p>/</a> I) ⊆ I

---
&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#choice" title=choice>∪</a> (a <a href="#inter" title=inter>∩</a> b) <a href="#equiv" title=equiv>≡</a> a

---
&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#inter" title=inter>∩</a> (a <a href="#choice" title=choice>∪</a> b) <a href="#equiv" title=equiv>≡</a> a

---
**civ_n_finite**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#civilized_n" title=civilized_n>civilized_n</a> p B n ⟹ finite B

---
## Equalities.thy

**equals_equiv_relation_1**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> = p<sub>2</sub> ⟹ p<sub>1</sub> <a href="#equal" title=equal>=</a> p<sub>2</sub>

---
**equals_equiv_relation_2**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#equal" title=equal>=</a> p<sub>2</sub> ⟹ p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub>

---
**equals_equiv_relation_3**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> = p<sub>2</sub> ⟹ p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub>

---
**equal_is_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#equal" title=equal>=</a> p<sub>1</sub>

---
**equiv_is_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>1</sub>

---
**equal_is_symetric**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#equal" title=equal>=</a> p<sub>2</sub> ⟹ p<sub>2</sub> <a href="#equal" title=equal>=</a> p<sub>1</sub>

---
**equiv_is_symetric**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub> ⟹ p<sub>2</sub> <a href="#equiv" title=equiv>≡</a> p<sub>1</sub>

---
**equal_is_transitive**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#equal" title=equal>=</a> p<sub>2</sub> ⟹ p<sub>2</sub> <a href="#equal" title=equal>=</a> p<sub>3</sub> ⟹ p<sub>1</sub> <a href="#equal" title=equal>=</a> p<sub>3</sub>

---
**equiv_is_transitive**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub> ⟹ p<sub>2</sub> <a href="#equiv" title=equiv>≡</a> p<sub>3</sub> ⟹ p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>3</sub>

---
**inverse_equality_1**

&nbsp;&nbsp;&nbsp;&nbsp;¬ p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub> ⟹ ¬ p<sub>1</sub> <a href="#equal" title=equal>=</a> p<sub>2</sub>

---
**inverse_equality_2**

&nbsp;&nbsp;&nbsp;&nbsp;¬ p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub> ⟹ ¬ p<sub>1</sub> = p<sub>2</sub>

---
**inverse_equality_3**

&nbsp;&nbsp;&nbsp;&nbsp;¬ p<sub>1</sub> <a href="#equal" title=equal>=</a> p<sub>2</sub> ⟹ ¬ p<sub>1</sub> = p<sub>2</sub>

---
**empty_state_space_equal**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> a = {} ⟹ <a href="#S" title=S>S</a> b = {} ⟹ a = b

---
## Feasibility.thy

**equal_maintains_feasiblity**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p<sub>1</sub> ⟹ p<sub>1</sub> <a href="#equal" title=equal>=</a> p<sub>2</sub> ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> p<sub>2</sub>

---
**equiv_maintains_feasiblity**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p<sub>1</sub> ⟹ p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub> ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> p<sub>2</sub>

---
## Helper.thy

**rel_id_prop**

&nbsp;&nbsp;&nbsp;&nbsp;Field a ⊆ C ⟹ a O Id_on C = a

---
**list_comp_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;∀p. [p i. i ← [0..((int (n + 1)))]] = [p i. i ← [0..(int n)]] @ [p ((int (n + 1)))]

---
**orig_is_permutation_1**

&nbsp;&nbsp;&nbsp;&nbsp;List.member (<a href="#insert_all" title=insert_all>insert_all</a> x xs) (x#xs)

---
**permutation_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;List.member (<a href="#permutations" title=permutations>permutations</a> xs) xs

---
**l1**

&nbsp;&nbsp;&nbsp;&nbsp;set (<a href="#insert_all" title=insert_all>insert_all</a> x (ps)) ≠ {}

---
**l2**

&nbsp;&nbsp;&nbsp;&nbsp;x#xs ∈ set (<a href="#insert_all" title=insert_all>insert_all</a> x xs)

---
**l3**

&nbsp;&nbsp;&nbsp;&nbsp;xs@[x] ∈ set (<a href="#insert_all" title=insert_all>insert_all</a> x xs)

---
**l4**

&nbsp;&nbsp;&nbsp;&nbsp;a@x#b ∈ set (<a href="#insert_all" title=insert_all>insert_all</a> x (a@b))

---
**l5**

&nbsp;&nbsp;&nbsp;&nbsp;p ∈ set (<a href="#insert_all" title=insert_all>insert_all</a> x (a # xs)) ⟹ (hd p = x) ∨ (hd p = a)

---
**l5_2**

&nbsp;&nbsp;&nbsp;&nbsp;p ∈ set (<a href="#insert_all" title=insert_all>insert_all</a> x (a # xs)) ⟹ (h_hd p = [x]) ∨ (h_hd p = [a])

---
**l6**

&nbsp;&nbsp;&nbsp;&nbsp;h_hd p = [x] ⟹ hd p = x

---
**l7**

&nbsp;&nbsp;&nbsp;&nbsp;h_tl p = x ≡ tl p = x

---
**l8**

&nbsp;&nbsp;&nbsp;&nbsp;(h_hd p)@(h_tl p) = p

---
**l9**

&nbsp;&nbsp;&nbsp;&nbsp;a#p ∈ set (<a href="#insert_all" title=insert_all>insert_all</a> x (a # xs)) ⟹ p ∈ set (<a href="#insert_all" title=insert_all>insert_all</a> x xs)

---
**l10**

&nbsp;&nbsp;&nbsp;&nbsp;p ∈ set (<a href="#insert_all" title=insert_all>insert_all</a> x xs) ⟹ ∃a b. a@x#b=p

---
**l11**

&nbsp;&nbsp;&nbsp;&nbsp;p ∈ set (<a href="#insert_all" title=insert_all>insert_all</a> x ps) ⟹ x ∈ set p

---
**l12**

&nbsp;&nbsp;&nbsp;&nbsp;y ∈ set p ⟹ p ∈ set (<a href="#insert_all" title=insert_all>insert_all</a> x (a # ps)) ⟹ y ≠ a ⟹ p' ∈ set (<a href="#insert_all" title=insert_all>insert_all</a> x ps) ⟹ y ∈ set p'

---
**l13**

&nbsp;&nbsp;&nbsp;&nbsp;y ∈ set p ⟹ p ∈ set (<a href="#insert_all" title=insert_all>insert_all</a> x ps) ⟹ y ∉ set ps ⟹ y = x

---
**permutation_symmetric_1**

&nbsp;&nbsp;&nbsp;&nbsp;List.member (<a href="#permutations" title=permutations>permutations</a> xs) p ⟹ List.member p y ⟹ List.member xs y

---
**l14**

&nbsp;&nbsp;&nbsp;&nbsp;p ∈ set (<a href="#insert_all" title=insert_all>insert_all</a> x ps) ⟹ ∃a b. p = a @ x # b ∧ ps = a @ b

---
**count_invariant**

&nbsp;&nbsp;&nbsp;&nbsp;List.member (<a href="#permutations" title=permutations>permutations</a> xs) p ⟹ count_list p y = count_list xs y

---
**permutation_split**

&nbsp;&nbsp;&nbsp;&nbsp;List.member (<a href="#permutations" title=permutations>permutations</a> (x#xs)) xs' ⟹ ∃a b. a@x#b = xs'

---
**permutation_size**

&nbsp;&nbsp;&nbsp;&nbsp;List.member (<a href="#permutations" title=permutations>permutations</a> x1) x2 ⟹ size x2 = size x1

---
**insert_perm_rel**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (<a href="#insert_all" title=insert_all>insert_all</a> a xs) ⟹ x ∈ set (<a href="#permutations" title=permutations>permutations</a> (a#xs))

---
**insert_all_set_equality**

&nbsp;&nbsp;&nbsp;&nbsp;p1 ∈ set (<a href="#insert_all" title=insert_all>insert_all</a> x ps) ⟹ set p1 = insert x (set ps)

---
**permutation_set_equality**

&nbsp;&nbsp;&nbsp;&nbsp;p1 ∈ set (<a href="#permutations" title=permutations>permutations</a> xs) ⟹ set xs = set p1

---
**permutation_set_equality_2**

&nbsp;&nbsp;&nbsp;&nbsp;p1 ∈ set (<a href="#permutations" title=permutations>permutations</a> xs) ⟹ p2 ∈ set (<a href="#permutations" title=permutations>permutations</a> xs) ⟹ set p1 = set p2

---
**permutation_split_set**

&nbsp;&nbsp;&nbsp;&nbsp;x2 ∈ set (<a href="#permutations" title=permutations>permutations</a> (a # x1)) ⟹ ∃y z. x2 = y @ a # z ∧ y @ z ∈ set (<a href="#permutations" title=permutations>permutations</a> x1)

---
**insert_4**

&nbsp;&nbsp;&nbsp;&nbsp;(xs @ ([x] @ ys)) ∈ set (<a href="#insert_all" title=insert_all>insert_all</a> x (xs @ ys))

---
**count_eq_member**

&nbsp;&nbsp;&nbsp;&nbsp;List.count_list p y > 0 = List.member p y

---
**member_invariant**

&nbsp;&nbsp;&nbsp;&nbsp;p ∈ set (<a href="#permutations" title=permutations>permutations</a> xs) ⟹ List.member p y ⟹ List.member xs y

---
**length_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;List.member xs x ⟹ ∃a b. a@[x]@b = xs

---
**length_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;count_list (a @ [x] @ b) x = Suc (count_list (a @ b) x)

---
**length_prop_3**

&nbsp;&nbsp;&nbsp;&nbsp;x<sub>1</sub>≠x<sub>2</sub> ⟹ xs = a@[x<sub>2</sub>]@b ⟹ count_list (xs) x<sub>1</sub> = count_list (a@b) x<sub>1</sub>

---
**length_prop_4**

&nbsp;&nbsp;&nbsp;&nbsp;x<sub>1</sub>=x<sub>2</sub> ⟹ xs = a@[x<sub>2</sub>]@b ⟹ count_list (xs) x<sub>1</sub> = Suc (count_list (a@b) x<sub>1</sub>)

---
**length_prop_5**

&nbsp;&nbsp;&nbsp;&nbsp;∀x<sub>1</sub>. count_list (a # xs) x<sub>1</sub> = count_list (a # xs') x<sub>1</sub> ⟹ ∀x<sub>1</sub>. count_list (xs) x<sub>1</sub> = count_list (xs') x<sub>1</sub>

---
**length_prop_6**

&nbsp;&nbsp;&nbsp;&nbsp;∀x<sub>1</sub>. count_list xs x<sub>1</sub> = count_list xs' x<sub>1</sub> ⟹ length xs = length xs'

---
**length_inv**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (<a href="#permutations" title=permutations>permutations</a> xs) ⟹ length x = length xs

---
**perm_inv_2**

&nbsp;&nbsp;&nbsp;&nbsp;xb@xe ∈ set (<a href="#permutations" title=permutations>permutations</a> x1) ⟹ xb@a#xe ∈ set (<a href="#permutations" title=permutations>permutations</a> (a # x1))

---
**singleton_permutation**

&nbsp;&nbsp;&nbsp;&nbsp;[x] ∈ set (<a href="#permutations" title=permutations>permutations</a> xs) ⟹ xs = [x]

---
**count_invariant_2**

&nbsp;&nbsp;&nbsp;&nbsp;∀y. count_list p y = count_list xs y ⟹ List.member (<a href="#permutations" title=permutations>permutations</a> xs) p

---
**count_invariant_3**

&nbsp;&nbsp;&nbsp;&nbsp;x1 ∉ set (<a href="#permutations" title=permutations>permutations</a> x2) ⟹ ∃t. count_list x1 t ≠ count_list x2 t

---
**permutations_set_equality**

&nbsp;&nbsp;&nbsp;&nbsp;x1 ∈ set (<a href="#permutations" title=permutations>permutations</a> x2) ⟹ set (<a href="#permutations" title=permutations>permutations</a> x1) = set (<a href="#permutations" title=permutations>permutations</a> x2)

---
**perm_lemma_1**

&nbsp;&nbsp;&nbsp;&nbsp;x1 ∉ set (<a href="#permutations" title=permutations>permutations</a> x2) ⟹ a # x1 ∉ set (<a href="#permutations" title=permutations>permutations</a> (a # x2))

---
**perm_split**

&nbsp;&nbsp;&nbsp;&nbsp;a # x1 ∈ set (<a href="#permutations" title=permutations>permutations</a> (y @ a # z)) ⟹ x1 ∈ set (<a href="#permutations" title=permutations>permutations</a> (y @ z))

---
**perm_inv_3**

&nbsp;&nbsp;&nbsp;&nbsp;x1 ∈ set (<a href="#permutations" title=permutations>permutations</a> x2) ⟹ x2 ∈ set (<a href="#permutations" title=permutations>permutations</a> x1)

---
**orig_is_permutation_3**

&nbsp;&nbsp;&nbsp;&nbsp;List.member (<a href="#permutations" title=permutations>permutations</a> x1) x2 ⟹ List.member (<a href="#permutations" title=permutations>permutations</a> x2) x1

---
**complete_state_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;fold (λ p s. <a href="#S" title=S>S</a> p ∪ s) xs C = foldl (λ s p. <a href="#S" title=S>S</a> p ∪ s) C xs

---
**complete_state_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_state" title=complete_state>complete_state</a> xs = fold (∪) (map (λp. <a href="#S" title=S>S</a> p) xs) {}

---
**complete_state_prop_3**

&nbsp;&nbsp;&nbsp;&nbsp;fold (λ p s. <a href="#S" title=S>S</a> p ∪ s) xs C = fold (∪) (map (λp. <a href="#S" title=S>S</a> p) xs) C

---
**complete_state_prop_4**

&nbsp;&nbsp;&nbsp;&nbsp;fold (∪) xs C = fold (∪) xs {} ∪ C

---
**complete_state_prop_5**

&nbsp;&nbsp;&nbsp;&nbsp;fold (∪) (map (λp. <a href="#S" title=S>S</a> p) xs) C = fold (∪) (map (λp. <a href="#S" title=S>S</a> p) xs) {} ∪ C

---
**complete_state_prop**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_state" title=complete_state>complete_state</a> (x # xs) = <a href="#complete_state" title=complete_state>complete_state</a> xs ∪ <a href="#S" title=S>S</a> x

---
**permutation_complete_state_equality**

&nbsp;&nbsp;&nbsp;&nbsp;x1 ∈ set (<a href="#permutations" title=permutations>permutations</a> x2) ⟹ <a href="#complete_state" title=complete_state>complete_state</a> x2 = <a href="#complete_state" title=complete_state>complete_state</a> x1

---
**permutation_S_equiv**

&nbsp;&nbsp;&nbsp;&nbsp;x1 ∈ set (<a href="#permutations" title=permutations>permutations</a> x2) ⟹ fold (∪) (map (λp. <a href="#S" title=S>S</a> p) x1) {} ≡ fold (∪) (map (λp. <a href="#S" title=S>S</a> p) x2) {}

---
**complete_state_union_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_state" title=complete_state>complete_state</a> (a # xs) = <a href="#complete_state" title=complete_state>complete_state</a> (xs) ∪ <a href="#complete_state" title=complete_state>complete_state</a> ([a])

---
**complete_state_union_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_state" title=complete_state>complete_state</a> (xs) = <a href="#complete_state" title=complete_state>complete_state</a> (xs) ∪ <a href="#complete_state" title=complete_state>complete_state</a> ([ ])

---
**complete_state_union_3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_state" title=complete_state>complete_state</a> (a @ b) = <a href="#complete_state" title=complete_state>complete_state</a> a ∪ <a href="#complete_state" title=complete_state>complete_state</a> b

---
**perm_1**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (<a href="#permutations" title=permutations>permutations</a> xs) ⟹ a#x ∈ set (<a href="#permutations" title=permutations>permutations</a> (a#xs))

---
**perm_2**

&nbsp;&nbsp;&nbsp;&nbsp;set (<a href="#permutations" title=permutations>permutations</a> (a#xs)) = set (<a href="#permutations" title=permutations>permutations</a> (xs@[a]))

---
**perm_3**

&nbsp;&nbsp;&nbsp;&nbsp;set (<a href="#permutations" title=permutations>permutations</a> ([a]@st@ed)) = set (<a href="#permutations" title=permutations>permutations</a> (st@[a]@ed))

---
&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (<a href="#permutations" title=permutations>permutations</a> xs) ⟹ y ∈ set (<a href="#permutations" title=permutations>permutations</a> ys) ⟹ x@y ∈ set (<a href="#permutations" title=permutations>permutations</a> (xs@ys))

---
**elements_atomic**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ <a href="#get_atomic" title=get_atomic>get_atomic</a> p ⟹ <a href="#is_atomic" title=is_atomic>is_atomic</a> x

---
**empty_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;finite s ⟹ <a href="#set_to_list" title=set_to_list>set_to_list</a> s = [ ] ≡ s = {}

---
**empty_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#get_atomic" title=get_atomic>get_atomic</a> p = {} ⟹ Pre p = {}

---
**finite_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;finite xs ⟹ finite ys ⟹ finite {f a b | a b . a ∈ xs ∧ b ∈ ys}

---
**finite_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;finite xs ⟹ finite ys ⟹ finite {f a b | a b . (a, b) ∈ xs ∧ a ∉ ys}

---
**finite_relation**

&nbsp;&nbsp;&nbsp;&nbsp;finite r ≡ finite (Field r)

---
**decomp_program**

&nbsp;&nbsp;&nbsp;&nbsp;finite (<a href="#S" title=S>S</a> p) ⟹ x ∉ F ⟹ <a href="#S" title=S>S</a> p = insert x F ⟹ q = 〈State={s|s. s ∈ State p ∧ s ∈ F}, Pre={s|s. s ∈ Pre p ∧ s ∈ F}, post={(a,b)|a b. a ∈ F ∧ b ∈ F ∧ (a,b) ∈ post p}〉 ⟹ r = 〈State={s|s. s ∈ State p}, Pre={s|s. s ∈ Pre p}, post={(a,b)|a b. (a = x ∨ b = x) ∧ (a,b) ∈ post p}〉 ⟹ p <a href="#equiv" title=equiv>≡</a> q <a href="#choice" title=choice>∪</a> r

---
**decomp_program2**

&nbsp;&nbsp;&nbsp;&nbsp;finite (<a href="#S" title=S>S</a> p) ⟹ x ∉ F ⟹ <a href="#S" title=S>S</a> p = insert x F  ⟹ finite (<a href="#S" title=S>S</a> 〈State={s|s. s ∈ State p ∧ s ∈ F}, Pre={s|s. s ∈ Pre p ∧ s ∈ F}, post={(a,b)|a b. a ∈ F ∧ b ∈ F ∧ (a,b) ∈ post p}〉)

---
**decomp_program3**

&nbsp;&nbsp;&nbsp;&nbsp;finite (<a href="#S" title=S>S</a> p) ⟹ x ∉ F ⟹ <a href="#S" title=S>S</a> p = insert x F  ⟹ finite (<a href="#S" title=S>S</a> 〈State={s|s. s ∈ State p}, Pre={s|s. s ∈ Pre p}, post={(a,b)|a b. (a = x ∨ b = x) ∧ (a,b) ∈ post p}〉)

---
**card_prop**

&nbsp;&nbsp;&nbsp;&nbsp;finite a  ⟹ b ∩ c = {} ⟹ a = b ∪ c ⟹ card a = card b + card c

---
**card_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;finite b  ⟹ finite c  ⟹ b ∩ c = {} ⟹ a = b ∪ c ⟹ card a = card b + card c

---
**finite_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;finite x ⟹ finite {f a |a . a ∈ x}

---
**finite_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;finite x ⟹ finite {f a b |a b. (a, b) ∈ x}

---
**finite_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;finite (<a href="#S" title=S>S</a> p) ⟹ finite (<a href="#get_atomic" title=get_atomic>get_atomic</a> p)

---
**atomic_idem**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_atomic" title=is_atomic>is_atomic</a> p ⟹ (<a href="#get_atomic" title=get_atomic>get_atomic</a> p) ∪ {p} = <a href="#get_atomic" title=get_atomic>get_atomic</a> (p <a href="#choice" title=choice>∪</a> p)

---
**atomic_state**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_atomic" title=is_atomic>is_atomic</a> x ⟹ <a href="#S" title=S>S</a> x = State x

---
**atomic_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_atomic" title=is_atomic>is_atomic</a> x ⟹ ∃a b. 〈State={a,b}, Pre={a}, post={(a,b)}〉 = x

---
**atomic_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;∃a b. 〈State={a,b}, Pre={a}, post={(a,b)}〉 = x ⟹ <a href="#is_atomic" title=is_atomic>is_atomic</a> x

---
**atomic_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;∃a b. 〈State={a,b}, Pre={a}, post={(a,b)}〉 = x ≡ <a href="#is_atomic" title=is_atomic>is_atomic</a> x

---
**atomic_post**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_atomic" title=is_atomic>is_atomic</a> x ⟹ <a href="#restr_post" title=restr_post>restr_post</a> x = post x

---
**atomic_monotone**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#get_atomic" title=get_atomic>get_atomic</a> p ⊆ <a href="#get_atomic" title=get_atomic>get_atomic</a> (p <a href="#choice" title=choice>∪</a> q)

---
**atomic_split**

&nbsp;&nbsp;&nbsp;&nbsp;finite (<a href="#get_atomic" title=get_atomic>get_atomic</a> p) ⟹ finite (<a href="#get_atomic" title=get_atomic>get_atomic</a> q) ⟹ (<a href="#get_atomic" title=get_atomic>get_atomic</a> p) ∪ (<a href="#get_atomic" title=get_atomic>get_atomic</a> q) = <a href="#get_atomic" title=get_atomic>get_atomic</a> (p <a href="#choice" title=choice>∪</a> q)

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_atomic" title=is_atomic>is_atomic</a> x  ⟹ (<a href="#get_atomic" title=get_atomic>get_atomic</a> p) ∪ {x} = <a href="#get_atomic" title=get_atomic>get_atomic</a> (p <a href="#choice" title=choice>∪</a> x)

---
**fail_atomic**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#get_atomic" title=get_atomic>get_atomic</a> (<a href="#Fail" title=Fail>Fail</a> {}) = {}

---
**set_list_set**

&nbsp;&nbsp;&nbsp;&nbsp;finite xs ⟹ set (<a href="#set_to_list" title=set_to_list>set_to_list</a> xs) = xs

---
**set_list_prop**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ xs = <a href="#set_to_list" title=set_to_list>set_to_list</a> (insert x F) ⟹ ∃a b. a@x#b = xs

---
**set_to_list_distinct**

&nbsp;&nbsp;&nbsp;&nbsp;xs = <a href="#set_to_list" title=set_to_list>set_to_list</a> F ⟹ distinct xs

---
**set_to_list_size**

&nbsp;&nbsp;&nbsp;&nbsp;size (<a href="#set_to_list" title=set_to_list>set_to_list</a> F) = card F

---
**set_to_list_one**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#set_to_list" title=set_to_list>set_to_list</a> {x} = [x]

---
**atomic_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_atomic" title=is_atomic>is_atomic</a> x ⟹ <a href="#get_atomic" title=get_atomic>get_atomic</a> x = {x}

---
**Consistent_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#feasible_version" title=feasible_version>feasible_version</a> p)

---
**Consistent_round**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_rounded" title=is_rounded>is_rounded</a> (<a href="#rounded_version" title=rounded_version>rounded_version</a> p)

---
**Consistent_exact**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_exact" title=is_exact>is_exact</a> (<a href="#exact_version" title=exact_version>exact_version</a> p)

---
**Feasible_round**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#rounded_version" title=rounded_version>rounded_version</a> p)

---
**Round_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_rounded" title=is_rounded>is_rounded</a> p ⟹ <a href="#is_rounded" title=is_rounded>is_rounded</a> (<a href="#feasible_version" title=feasible_version>feasible_version</a> p)

---
**Equiv_prog**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#equiv" title=equiv>≡</a> b ≡ (Pre (<a href="#rounded_version" title=rounded_version>rounded_version</a> a) = Pre (<a href="#rounded_version" title=rounded_version>rounded_version</a> b) ∧ post (<a href="#rounded_version" title=rounded_version>rounded_version</a> a) = post (<a href="#rounded_version" title=rounded_version>rounded_version</a> b))

---
**Charrel_restriction**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#rounded_version" title=rounded_version>rounded_version</a> (p <a href="#restrict_p" title=restrict_p>/</a> C) = <a href="#rounded_version" title=rounded_version>rounded_version</a> p <a href="#restrict_p" title=restrict_p>/</a> C

---
**Charrel_choice**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#rounded_version" title=rounded_version>rounded_version</a> (p <a href="#choice" title=choice>∪</a> q) = <a href="#rounded_version" title=rounded_version>rounded_version</a> p <a href="#choice" title=choice>∪</a> <a href="#rounded_version" title=rounded_version>rounded_version</a> q

---
**Charrel_composition**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#rounded_version" title=rounded_version>rounded_version</a> (p <a href="#composition" title=composition>;</a> q) = <a href="#rounded_version" title=rounded_version>rounded_version</a> p <a href="#composition" title=composition>;</a> <a href="#rounded_version" title=rounded_version>rounded_version</a> q

---
**Charrel_corestriction**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#rounded_version" title=rounded_version>rounded_version</a> (p <a href="#corestrict_p" title=corestrict_p>∖</a> C) = <a href="#rounded_version" title=rounded_version>rounded_version</a> p <a href="#corestrict_p" title=corestrict_p>∖</a> C

---
**Restrict_rounded**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_rounded" title=is_rounded>is_rounded</a> p ⟹ <a href="#is_rounded" title=is_rounded>is_rounded</a> (p <a href="#restrict_p" title=restrict_p>/</a> C)

---
**Choice_rounded**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_rounded" title=is_rounded>is_rounded</a> (p <a href="#choice" title=choice>∪</a> q)

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_rounded" title=is_rounded>is_rounded</a> q ⟹ <a href="#is_rounded" title=is_rounded>is_rounded</a> p ⟹ <a href="#is_rounded" title=is_rounded>is_rounded</a> (p <a href="#composition" title=composition>;</a> q)

---
**Corestrict_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> ((p <a href="#restrict_p" title=restrict_p>/</a> (Pre p ∩ Domain (post p <a href="#corestrict_r" title=corestrict_r>∖</a> C))) <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
## Implementation.thy

**implementation_1**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ X ⟹ x ∈ Domain (R) ⟹ x ∈ Domain (R <a href="#restrict_r" title=restrict_r>/</a> X)

---
**implementation_theorem**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#implements" title=implements>implements</a> p<sub>2</sub> p<sub>1</sub> ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> p<sub>1</sub>

---
**implementation_is_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p<sub>1</sub> ⟹ <a href="#implements" title=implements>implements</a> p<sub>1</sub> p<sub>1</sub>

---
**implementation_is_transitive**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#implements" title=implements>implements</a> p<sub>1</sub> p<sub>2</sub> ⟹ <a href="#implements" title=implements>implements</a> p<sub>2</sub> p<sub>3</sub> ⟹ <a href="#implements" title=implements>implements</a> p<sub>1</sub> p<sub>3</sub>

---
**implementation_is_antisymetric**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#implements" title=implements>implements</a> p<sub>1</sub> p<sub>2</sub> ⟹ <a href="#implements" title=implements>implements</a> p<sub>2</sub> p<sub>1</sub> ⟹ p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub>

---
## Independence.thy

**independent_symetric**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#independent" title=independent>independent</a> p<sub>1</sub> p<sub>2</sub> = <a href="#independent" title=independent>independent</a> p<sub>2</sub> p<sub>1</sub>

---
**independent_weakens**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#independent" title=independent>independent</a> p<sub>1</sub> p<sub>2</sub> ⟹ Pre p<sub>2</sub> ≠ {} ⟹ ¬ <a href="#weakens" title=weakens>weakens</a> p<sub>1</sub> p<sub>2</sub>

---
**independent_strengthens**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#independent" title=independent>independent</a> p<sub>1</sub> p<sub>2</sub> ⟹ <a href="#strengthens" title=strengthens>strengthens</a> p<sub>1</sub> p<sub>2</sub>

---
## Range_p.thy

**same_range_p_3**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub> ⟹ <a href="#Range_p" title=Range_p>Range_p</a> p<sub>1</sub> = <a href="#Range_p" title=Range_p>Range_p</a> p<sub>2</sub>

---
**same_range_p_2**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#equal" title=equal>=</a> b ⟹ <a href="#Range_p" title=Range_p>Range_p</a> a = <a href="#Range_p" title=Range_p>Range_p</a> b

---
**range_p_explicit_1**

&nbsp;&nbsp;&nbsp;&nbsp;y ∈ <a href="#Range_p" title=Range_p>Range_p</a> a ⟹ ∃x. (x,y) ∈ post a ∧ x ∈ Pre a

---
**range_p_explicit_2**

&nbsp;&nbsp;&nbsp;&nbsp;(x,y) ∈ post a ∧ x ∈ Pre a ⟹ y ∈ <a href="#Range_p" title=Range_p>Range_p</a> a

---
**no_range_fail**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#Range_p" title=Range_p>Range_p</a> p = {} ⟹ p <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}

---
## Refinement.thy

**refines_is_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>1</sub>

---
**refines_is_transitive_e**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>2</sub> ⟹ p<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>3</sub> ⟹ <a href="#extends" title=extends>extends</a> p<sub>1</sub> p<sub>3</sub>

---
**refines_is_transitive_w**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>2</sub> ⟹ p<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>3</sub> ⟹ <a href="#weakens" title=weakens>weakens</a> p<sub>1</sub> p<sub>3</sub>

---
**refines_is_transitive_s**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>2</sub> ⟹ p<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>3</sub> ⟹ <a href="#strengthens" title=strengthens>strengthens</a> p<sub>1</sub> p<sub>3</sub>

---
**refines_is_transitive**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>2</sub> ⟹ p<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>3</sub> ⟹ p<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>3</sub>

---
**refines_is_antisymetric**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>2</sub> ⟹ p<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>1</sub> ⟹ p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub>

---
**refines_is_preorder**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>1</sub> ∧ (p<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>3</sub> ∧ p<sub>3</sub> <a href="#refines" title=refines>⊑</a> p<sub>4</sub> → p<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>4</sub>)

---
**refines_is_order**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>1</sub>) ∧ (p<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>3</sub> ∧ p<sub>3</sub> <a href="#refines" title=refines>⊑</a> p<sub>4</sub> → p<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>4</sub>) ∧ (p<sub>5</sub> <a href="#refines" title=refines>⊑</a> p<sub>6</sub> ∧ p<sub>6</sub> <a href="#refines" title=refines>⊑</a> p<sub>5</sub> → p<sub>5</sub> <a href="#equiv" title=equiv>≡</a> p<sub>6</sub>)

---
**extends_is_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#extends" title=extends>extends</a> p p

---
**extends_is_transitive**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#extends" title=extends>extends</a> p q ⟹ <a href="#extends" title=extends>extends</a> q r ⟹ <a href="#extends" title=extends>extends</a> p r

---
**weakens_is_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#weakens" title=weakens>weakens</a> p p

---
**weakens_is_transitive**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#weakens" title=weakens>weakens</a> p q ⟹ <a href="#weakens" title=weakens>weakens</a> q r ⟹ <a href="#weakens" title=weakens>weakens</a> p r

---
**strengthens_is_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#strengthens" title=strengthens>strengthens</a> p p

---
**strengthens_is_transitive_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#weakens" title=weakens>weakens</a> p q ⟹ <a href="#weakens" title=weakens>weakens</a> q r ⟹ <a href="#strengthens" title=strengthens>strengthens</a> p q ⟹ <a href="#strengthens" title=strengthens>strengthens</a> q r ⟹ <a href="#strengthens" title=strengthens>strengthens</a> p r

---
**strengthens_is_transitive_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#weakens" title=weakens>weakens</a> q p ⟹ <a href="#weakens" title=weakens>weakens</a> r q ⟹ <a href="#strengthens" title=strengthens>strengthens</a> p q ⟹ <a href="#strengthens" title=strengthens>strengthens</a> q r ⟹ <a href="#strengthens" title=strengthens>strengthens</a> p r

---
## Relation_operations.thy

**corestriction_restriction_on_relcomp**

&nbsp;&nbsp;&nbsp;&nbsp;r<sub>1</sub> <a href="#corestrict_r" title=corestrict_r>∖</a> s<sub>1</sub> O r<sub>2</sub> = r<sub>1</sub> O r<sub>2</sub> <a href="#restrict_r" title=restrict_r>/</a> s<sub>1</sub>

---
## Subprogram.thy

**specialize_is_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>1</sub>

---
**specialize_is_transitive**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>2</sub> ⟹ p<sub>2</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>3</sub> ⟹ p<sub>1</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>3</sub>

---
**specialize_is_antisymetric**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>2</sub> ⟹ p<sub>2</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>1</sub> ⟹ p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub>

---
**specialize_is_preorder**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>1</sub> ∧ (p<sub>2</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>3</sub> ∧ p<sub>3</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>4</sub> → p<sub>2</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>4</sub>)

---
**specialize_is_order**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>1</sub>) ∧ (p<sub>2</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>3</sub> ∧ p<sub>3</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>4</sub> → p<sub>2</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>4</sub>) ∧ (p<sub>5</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>6</sub> ∧ p<sub>6</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>5</sub> → p<sub>5</sub> <a href="#equiv" title=equiv>≡</a> p<sub>6</sub>)

---
**choice_decomp_1**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#specialize" title=specialize>⊆</a> c ∧ b <a href="#specialize" title=specialize>⊆</a> c ⟹ a <a href="#choice" title=choice>∪</a> b <a href="#specialize" title=specialize>⊆</a> c

---
**choice_decomp_2**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#choice" title=choice>∪</a> b <a href="#specialize" title=specialize>⊆</a> c ⟹ a <a href="#specialize" title=specialize>⊆</a> c ∧ b <a href="#specialize" title=specialize>⊆</a> c

---
**choice_decomp**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#specialize" title=specialize>⊆</a> c ∧ b <a href="#specialize" title=specialize>⊆</a> c ≡ a <a href="#choice" title=choice>∪</a> b <a href="#specialize" title=specialize>⊆</a> c

---
**specialize_equiv**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#specialize" title=specialize>⊆</a> b ⟹ a <a href="#equiv" title=equiv>≡</a> c ⟹ b <a href="#equiv" title=equiv>≡</a> d ⟹ c <a href="#specialize" title=specialize>⊆</a> d

---
**equiv_specialize_transitivity**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> a ⊆ <a href="#S" title=S>S</a> b ⟹ <a href="#S" title=S>S</a> c ⊆ <a href="#S" title=S>S</a> d ⟹ a <a href="#equiv" title=equiv>≡</a> b ⟹ b <a href="#specialize" title=specialize>⊆</a> c ⟹ c <a href="#equiv" title=equiv>≡</a> d ⟹ a <a href="#specialize" title=specialize>⊆</a> d

---
## Validity.thy

**valid_generalization**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_valid" title=is_valid>is_valid</a> p ⟹ prop (<a href="#S" title=S>S</a> p) = prop (State p)

---
**pre_in_s**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_valid" title=is_valid>is_valid</a> p ⟹ Pre p ⊆ State p

---
**post_in_s**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_valid" title=is_valid>is_valid</a> p ⟹ (Field (post p) ⊆ State p)

---
**validity_inverse**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_valid" title=is_valid>is_valid</a> p ⟹ <a href="#is_valid" title=is_valid>is_valid</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)

---
**validity_composition**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_valid" title=all_valid>all_valid</a> [p<sub>1</sub>, p<sub>2</sub>] ⟹ <a href="#is_valid" title=is_valid>is_valid</a> (p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>)

---
**validity_choice**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_valid" title=all_valid>all_valid</a> [p<sub>1</sub>, p<sub>2</sub>] ⟹ <a href="#is_valid" title=is_valid>is_valid</a> (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>)

---
**validity_restriction**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_valid" title=is_valid>is_valid</a> p ⟹ <a href="#is_valid" title=is_valid>is_valid</a> (p <a href="#restrict_p" title=restrict_p>/</a> C)

---
**validity_corestriction**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_valid" title=is_valid>is_valid</a> p ⟹ <a href="#is_valid" title=is_valid>is_valid</a> (p <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
**validity_equality**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_valid" title=is_valid>is_valid</a> p ⟹ <a href="#is_valid" title=is_valid>is_valid</a> q ⟹ p <a href="#equal" title=equal>=</a> q ⟹ p = q

---
## Choice.thy

**choice_idem_4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Fail" title=Fail>Fail</a> {} <a href="#choice" title=choice>∪</a> (p <a href="#choice" title=choice>∪</a> p) = <a href="#Fail" title=Fail>Fail</a> {} <a href="#choice" title=choice>∪</a> p

---
**choice_idem_5**

&nbsp;&nbsp;&nbsp;&nbsp;q <a href="#choice" title=choice>∪</a> (p <a href="#choice" title=choice>∪</a> p) = q <a href="#choice" title=choice>∪</a> p

---
**choice_idem_6**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#choice" title=choice>∪</a> p) <a href="#choice" title=choice>∪</a> q = p <a href="#choice" title=choice>∪</a> q

---
**choice_equiv**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>1</sub> ⟹ f<sub>2</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub> ⟹ f<sub>1</sub> <a href="#choice" title=choice>∪</a> f<sub>2</sub> <a href="#equiv" title=equiv>≡</a> p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>

---
**equality_is_maintained_by_choice**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> <a href="#equal" title=equal>=</a> p<sub>1</sub> ⟹ f<sub>2</sub> <a href="#equal" title=equal>=</a> p<sub>2</sub> ⟹ f<sub>1</sub> <a href="#choice" title=choice>∪</a> f<sub>2</sub> <a href="#equal" title=equal>=</a> p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>

---
**choice_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p<sub>1</sub>, p<sub>2</sub>] ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>)

---
**condition_for_choice_simplification**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Range_p" title=Range_p>Range_p</a> a ∩ Pre y = {} ⟹ <a href="#Range_p" title=Range_p>Range_p</a> x ∩ Pre b = {} ⟹ a <a href="#composition" title=composition>;</a> b <a href="#choice" title=choice>∪</a> x <a href="#composition" title=composition>;</a> y <a href="#equiv" title=equiv>≡</a> (a <a href="#choice" title=choice>∪</a> x) <a href="#composition" title=composition>;</a> (b <a href="#choice" title=choice>∪</a> y)

---
**choice_range**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Range_p" title=Range_p>Range_p</a> (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>) = <a href="#Range_p" title=Range_p>Range_p</a> p<sub>1</sub> ∪ <a href="#Range_p" title=Range_p>Range_p</a> p<sub>2</sub>

---
**refinement_safety_choice_e**

&nbsp;&nbsp;&nbsp;&nbsp;q<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>1</sub> ⟹ q<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>2</sub> ⟹ <a href="#extends" title=extends>extends</a> (q<sub>1</sub> <a href="#choice" title=choice>∪</a> q<sub>2</sub>) (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>)

---
**refinement_safety_choice_w**

&nbsp;&nbsp;&nbsp;&nbsp;q<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>1</sub> ⟹ q<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>2</sub> ⟹ <a href="#weakens" title=weakens>weakens</a> (q<sub>1</sub> <a href="#choice" title=choice>∪</a> q<sub>2</sub>) (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>)

---
**refinement_safety_choice_s_1**

&nbsp;&nbsp;&nbsp;&nbsp;q<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>1</sub> ⟹ q<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>2</sub> ⟹ <a href="#strengthens" title=strengthens>strengthens</a> (q<sub>1</sub> <a href="#choice" title=choice>∪</a> q<sub>2</sub>) (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>)

---
**refinement_safety_choice_s_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#strengthens" title=strengthens>strengthens</a> q<sub>1</sub> p<sub>2</sub> ⟹ <a href="#strengthens" title=strengthens>strengthens</a> q<sub>2</sub> p<sub>1</sub> ⟹ q<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>1</sub> ⟹ q<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>2</sub> ⟹ <a href="#strengthens" title=strengthens>strengthens</a> (q<sub>1</sub> <a href="#choice" title=choice>∪</a> q<sub>2</sub>) (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>)

---
**refinement_safety_choice**

&nbsp;&nbsp;&nbsp;&nbsp;q<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>1</sub> ⟹ q<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>2</sub> ⟹ (q<sub>1</sub> <a href="#choice" title=choice>∪</a> q<sub>2</sub>) <a href="#refines" title=refines>⊑</a> (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>)

---
**refinement_safety_choice**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#strengthens" title=strengthens>strengthens</a> a c ⟹ a <a href="#refines" title=refines>⊑</a> b ⟹ (a <a href="#choice" title=choice>∪</a> c) <a href="#refines" title=refines>⊑</a> (b <a href="#choice" title=choice>∪</a> c)

---
**refinement_safety_choice_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#strengthens" title=strengthens>strengthens</a> q<sub>1</sub> p<sub>2</sub> ⟹ <a href="#strengthens" title=strengthens>strengthens</a> q<sub>2</sub> p<sub>1</sub> ⟹ q<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>1</sub> ⟹ q<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>2</sub> ⟹ (q<sub>1</sub> <a href="#choice" title=choice>∪</a> q<sub>2</sub>) <a href="#refines" title=refines>⊑</a> (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>)

---
**refinement_safety_choice_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#independent" title=independent>independent</a> q<sub>1</sub> p<sub>2</sub> ⟹ <a href="#independent" title=independent>independent</a> q<sub>2</sub> p<sub>1</sub> ⟹ q<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>1</sub> ⟹ q<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>2</sub> ⟹ (q<sub>1</sub> <a href="#choice" title=choice>∪</a> q<sub>2</sub>) <a href="#refines" title=refines>⊑</a> (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>)

---
**choice_safety1**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#specialize" title=specialize>⊆</a> b ⟹ a <a href="#choice" title=choice>∪</a> c <a href="#specialize" title=specialize>⊆</a> b <a href="#choice" title=choice>∪</a> c

---
**implements_safety_choice**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> c ⟹ <a href="#implements" title=implements>implements</a> a b ⟹ <a href="#implements" title=implements>implements</a> (a <a href="#choice" title=choice>∪</a> c) (b <a href="#choice" title=choice>∪</a> c)

---
**implements_safety_choice**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#strengthens" title=strengthens>strengthens</a> a c ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> c ⟹ <a href="#implements" title=implements>implements</a> a b ⟹ <a href="#implements" title=implements>implements</a> (a <a href="#choice" title=choice>∪</a> c) (b <a href="#choice" title=choice>∪</a> c)

---
**program_is_specialize_of_choice**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#specialize" title=specialize>⊆</a> (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>)

---
**choice_choice_range**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Range_p" title=Range_p>Range_p</a> p ⊆ <a href="#Range_p" title=Range_p>Range_p</a> (p <a href="#choice" title=choice>∪</a> q)

---
**choice_range_p_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ <a href="#Range_p" title=Range_p>Range_p</a> (p <a href="#choice" title=choice>∪</a> q) ⟹ x ∉ <a href="#Range_p" title=Range_p>Range_p</a> p ⟹ x ∈ <a href="#Range_p" title=Range_p>Range_p</a> q

---
**choice_range_p_prop_3**

&nbsp;&nbsp;&nbsp;&nbsp;x ∉ <a href="#Range_p" title=Range_p>Range_p</a> (p <a href="#choice" title=choice>∪</a> q) ⟹ x ∉ <a href="#Range_p" title=Range_p>Range_p</a> p

---
**empty_is_neutral**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> a = {} ⟹ a <a href="#choice" title=choice>∪</a> (b <a href="#choice" title=choice>∪</a> c) = b <a href="#choice" title=choice>∪</a> c

---
**choice_idem_2**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#choice" title=choice>∪</a> (a <a href="#choice" title=choice>∪</a> b) = a <a href="#choice" title=choice>∪</a> b

---
**choice_suprogram_prop**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#specialize" title=specialize>⊆</a> c ⟹ b <a href="#specialize" title=specialize>⊆</a> c ⟹ a <a href="#choice" title=choice>∪</a> b <a href="#specialize" title=specialize>⊆</a> c

---
## Composition.thy

**composition_simplification_1**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub> = p<sub>1</sub> <a href="#corestrict_p" title=corestrict_p>∖</a> Pre p<sub>2</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>

---
**composition_simplification_2**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub> = p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub> <a href="#restrict_p" title=restrict_p>/</a> Pre p<sub>2</sub>

---
**composition_equiv**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>1</sub> ⟹ f<sub>2</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub> ⟹ f<sub>1</sub> <a href="#composition" title=composition>;</a> f<sub>2</sub> <a href="#equiv" title=equiv>≡</a> p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>

---
**equality_is_maintained_by_composition**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> <a href="#equal" title=equal>=</a> p<sub>1</sub> ⟹ f<sub>2</sub> <a href="#equal" title=equal>=</a> p<sub>2</sub> ⟹ f<sub>1</sub> <a href="#composition" title=composition>;</a> f<sub>2</sub> <a href="#equal" title=equal>=</a> p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>

---
**compose_feasible_lemma**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p<sub>1</sub>, p<sub>2</sub>] ⟹ Domain ((post p<sub>1</sub>) <a href="#corestrict_r" title=corestrict_r>∖</a> (Pre p<sub>2</sub>)) = Domain ((post p<sub>1</sub>) <a href="#corestrict_r" title=corestrict_r>∖</a> (Pre p<sub>2</sub>) O post p<sub>2</sub>)

---
**compose_feasible2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p<sub>1</sub>, p<sub>2</sub>] ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>)

---
**composition_removes_dead_code_1**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#restrict_p" title=restrict_p>/</a> (Pre p) <a href="#composition" title=composition>;</a> q <a href="#equiv" title=equiv>≡</a> p <a href="#composition" title=composition>;</a> q

---
**composition_removes_dead_code_2**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#composition" title=composition>;</a> q <a href="#restrict_p" title=restrict_p>/</a> (Pre q) <a href="#equiv" title=equiv>≡</a> p <a href="#composition" title=composition>;</a> q

---
**compose_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p<sub>2</sub> ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>)

---
&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub> <a href="#equiv" title=equiv>≡</a> 〈State ={}, Pre=Pre p<sub>1</sub> ∩ Domain (post p<sub>1</sub> <a href="#corestrict_r" title=corestrict_r>∖</a> Pre p<sub>2</sub>), post=post p<sub>1</sub>〉 <a href="#composition" title=composition>;</a> p<sub>2</sub>

---
**range_decreases_composition**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Range_p" title=Range_p>Range_p</a> (y <a href="#composition" title=composition>;</a> x) ⊆ <a href="#Range_p" title=Range_p>Range_p</a> x

---
&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#refines" title=refines>⊑</a> q ⟹ p <a href="#composition" title=composition>;</a> a <a href="#refines" title=refines>⊑</a> q <a href="#composition" title=composition>;</a> a

---
**composition_subsafety**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#specialize" title=specialize>⊆</a> b ⟹ a <a href="#composition" title=composition>;</a> c <a href="#specialize" title=specialize>⊆</a> b <a href="#composition" title=composition>;</a> c

---
**composition_subsafety2**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#specialize" title=specialize>⊆</a> b ⟹ c <a href="#composition" title=composition>;</a> a <a href="#specialize" title=specialize>⊆</a> c <a href="#composition" title=composition>;</a> b

---
**comp_range_p_prop**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Range_p" title=Range_p>Range_p</a> (q) ⊆ C ⟹ <a href="#Range_p" title=Range_p>Range_p</a> (p <a href="#composition" title=composition>;</a> q) ⊆ C

---
**comp_range_p_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;x ∉ <a href="#Range_p" title=Range_p>Range_p</a> q ⟹ x ∉ <a href="#Range_p" title=Range_p>Range_p</a> (p <a href="#composition" title=composition>;</a> q)

---
**connecting_element**

&nbsp;&nbsp;&nbsp;&nbsp;(x,y) ∈ post (a <a href="#composition" title=composition>;</a> b) ⟹ ∃z. (x,z) ∈ post a ∧ (z,y) ∈ post b ∧ z ∈ Pre b

---
**knowing_pre_composition**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ Pre (a) ⟹ (x, y) ∈ post (a <a href="#composition" title=composition>;</a> b) ⟹ x ∈ Pre (a <a href="#composition" title=composition>;</a> b)

---
## Corestriction.thy

**corestrict_idem**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#corestrict_p" title=corestrict_p>∖</a> C) <a href="#corestrict_p" title=corestrict_p>∖</a> C = p <a href="#corestrict_p" title=corestrict_p>∖</a> C

---
**corestrict_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Range_p" title=Range_p>Range_p</a> (p <a href="#corestrict_p" title=corestrict_p>∖</a> D) ⊆ D

---
**corestrict_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Range_p" title=Range_p>Range_p</a> (p <a href="#corestrict_p" title=corestrict_p>∖</a> D) ⊆ <a href="#Range_p" title=Range_p>Range_p</a> p

---
**corestrict_prop_**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Range_p" title=Range_p>Range_p</a> (p <a href="#corestrict_p" title=corestrict_p>∖</a> D) ⊆ <a href="#Range_p" title=Range_p>Range_p</a> p ∩ D

---
**NOT_corestricted_p_refines_p**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#refines" title=refines>⊑</a> p

---
**NOT_p_refines_corestricted_p**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#refines" title=refines>⊑</a> p <a href="#corestrict_p" title=corestrict_p>∖</a> C

---
**corestricted_refines_unrestricted_1**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#refines" title=refines>⊑</a> p

---
**unrestricted_refines_corestricted_1**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#refines" title=refines>⊑</a> p <a href="#corestrict_p" title=corestrict_p>∖</a> C

---
**corestricted_refines_unrestricted_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ p <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#refines" title=refines>⊑</a> p

---
**unrestricted_refines_corestricted_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ p <a href="#refines" title=refines>⊑</a> p <a href="#corestrict_p" title=corestrict_p>∖</a> C

---
**corestrict_subprog**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#specialize" title=specialize>⊆</a> p

---
**unrestricted_weakens_corestricted**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#weakens" title=weakens>weakens</a> p (p <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
**corestricted_strengthens_unrestricted**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#strengthens" title=strengthens>strengthens</a> (p <a href="#corestrict_p" title=corestrict_p>∖</a> C) p

---
**corestriction_prop**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ p <a href="#corestrict_p" title=corestrict_p>∖</a> D <a href="#refines" title=refines>⊑</a> p <a href="#corestrict_p" title=corestrict_p>∖</a> C

---
**corestriction_prop**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ p <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#refines" title=refines>⊑</a> p <a href="#corestrict_p" title=corestrict_p>∖</a> D

---
**corestriction_weakens_prop**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ <a href="#weakens" title=weakens>weakens</a> (p <a href="#corestrict_p" title=corestrict_p>∖</a> C) (p <a href="#corestrict_p" title=corestrict_p>∖</a> D)

---
**corestriction_strengthens_prop**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ <a href="#strengthens" title=strengthens>strengthens</a> (p <a href="#corestrict_p" title=corestrict_p>∖</a> D) (p <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
**corestrict_subprogorder1**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ (p <a href="#corestrict_p" title=corestrict_p>∖</a> D) <a href="#specialize" title=specialize>⊆</a> (p <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
**equivalence_is_maintained_by_corestriction**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>1</sub> ⟹ (f<sub>1</sub> <a href="#corestrict_p" title=corestrict_p>∖</a> C) <a href="#equiv" title=equiv>≡</a> p<sub>1</sub> <a href="#corestrict_p" title=corestrict_p>∖</a> C

---
**equality_is_maintained_by_corestriction**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> <a href="#equal" title=equal>=</a> p<sub>1</sub> ⟹ (f<sub>1</sub> <a href="#corestrict_p" title=corestrict_p>∖</a> C) <a href="#equal" title=equal>=</a> p<sub>1</sub> <a href="#corestrict_p" title=corestrict_p>∖</a> C

---
**corestrict_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (p <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
**corestriction_subsafety**

&nbsp;&nbsp;&nbsp;&nbsp;q <a href="#specialize" title=specialize>⊆</a> p ⟹ q <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#specialize" title=specialize>⊆</a> p <a href="#corestrict_p" title=corestrict_p>∖</a> C

---
**refinement_safety_corestriction**

&nbsp;&nbsp;&nbsp;&nbsp;q <a href="#refines" title=refines>⊑</a> p ⟹ q <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#refines" title=refines>⊑</a> p <a href="#corestrict_p" title=corestrict_p>∖</a> C

---
**implements_safety_corestriction**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#implements" title=implements>implements</a> a b ⟹ <a href="#implements" title=implements>implements</a> (a <a href="#corestrict_p" title=corestrict_p>∖</a> C) (b <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
**weakens_corestriction_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p, q] ⟹ q <a href="#refines" title=refines>⊑</a> p ⟹ <a href="#weakens" title=weakens>weakens</a> (q <a href="#corestrict_p" title=corestrict_p>∖</a> C) (p <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
**weakens_corestriction_2**

&nbsp;&nbsp;&nbsp;&nbsp;q <a href="#refines" title=refines>⊑</a> p ⟹ <a href="#weakens" title=weakens>weakens</a> (p <a href="#corestrict_p" title=corestrict_p>∖</a> C) (q <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
**strengthens_corestriction_1**

&nbsp;&nbsp;&nbsp;&nbsp;q <a href="#refines" title=refines>⊑</a> p ⟹ <a href="#strengthens" title=strengthens>strengthens</a> (p <a href="#corestrict_p" title=corestrict_p>∖</a> C) (q <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
**strengthens_corestriction_2**

&nbsp;&nbsp;&nbsp;&nbsp;q <a href="#refines" title=refines>⊑</a> p ⟹ <a href="#strengthens" title=strengthens>strengthens</a> (q <a href="#corestrict_p" title=corestrict_p>∖</a> C) (p <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
**corestrict_range_prop**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ C ⟹ x ∉ <a href="#Range_p" title=Range_p>Range_p</a> (p <a href="#corestrict_p" title=corestrict_p>∖</a> C) ⟹ x ∉ <a href="#Range_p" title=Range_p>Range_p</a> (p)

---
**corestrict_range_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> a ⟹ <a href="#Range_p" title=Range_p>Range_p</a> a ⊆ C ⟹ a <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#equiv" title=equiv>≡</a> a

---
**corestrict_range_prop_3**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p(a) ∩ C = {} ⟹ a∖C <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**corestrict_range_porp_4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ p <a href="#corestrict_p" title=corestrict_p>∖</a> <a href="#Range_p" title=Range_p>Range_p</a> p <a href="#equiv" title=equiv>≡</a> p

---
**corestrict_inter**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#corestrict_p" title=corestrict_p>∖</a> C) <a href="#corestrict_p" title=corestrict_p>∖</a> D = p∖ (C ∩ D)

---
**corestrict_commute**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#corestrict_p" title=corestrict_p>∖</a> C) <a href="#corestrict_p" title=corestrict_p>∖</a> D = (p <a href="#corestrict_p" title=corestrict_p>∖</a> D) <a href="#corestrict_p" title=corestrict_p>∖</a> C

---
## Inverse.thy

**inverse_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)

---
**inverse_of_inverse_is_self**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ p <sup>-</sup><sup>1</sup><sup>-</sup><sup>1</sup> <a href="#equiv" title=equiv>≡</a> p

---
**pre_of_inverse**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_deterministic" title=is_deterministic>is_deterministic</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>) ⟹ Pre p = Pre (p <a href="#composition" title=composition>;</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>))

---
**pre_is_unchanged**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ Pre (p <a href="#composition" title=composition>;</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)) = Pre p

---
**post_is_identity**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_deterministic" title=is_deterministic>is_deterministic</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>) ⟹ (x,y)∈ <a href="#restr_post" title=restr_post>restr_post</a> (p <a href="#composition" title=composition>;</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)) ⟹ x = y

---
**post_is_identity_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_deterministic" title=is_deterministic>is_deterministic</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>) ⟹ (x,y)∈ <a href="#restr_post" title=restr_post>restr_post</a> (p <a href="#unsafe_composition" title=unsafe_composition>;</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)) ⟹ x = y

---
**post_of_inverse**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#is_deterministic" title=is_deterministic>is_deterministic</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>) ⟹ <a href="#restr_post" title=restr_post>restr_post</a> (<a href="#Skip" title=Skip>Skip</a> (Pre p)) = <a href="#restr_post" title=restr_post>restr_post</a> (p <a href="#composition" title=composition>;</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>))

---
**inverse_reverses_composition_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#is_deterministic" title=is_deterministic>is_deterministic</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>) ⟹ <a href="#Skip" title=Skip>Skip</a> (Pre p) <a href="#equiv" title=equiv>≡</a> (p <a href="#composition" title=composition>;</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>))

---
**inverse_reverses_composition_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#refines" title=refines>⊑</a> (p <a href="#composition" title=composition>;</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>))

---
**equivalence_is_maintained_by_inverse**

&nbsp;&nbsp;&nbsp;&nbsp;f <a href="#equiv" title=equiv>≡</a> p ⟹ f <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a> <a href="#equiv" title=equiv>≡</a> p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>

---
**equality_is_maintained_by_inverse**

&nbsp;&nbsp;&nbsp;&nbsp;f <a href="#equal" title=equal>=</a> p ⟹ f <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a> <a href="#equal" title=equal>=</a> p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>

---
**refinement_safety_inverse**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> f = <a href="#S" title=S>S</a> g ⟹ <a href="#all_feasible" title=all_feasible>all_feasible</a> [f, g] ⟹ f <a href="#refines" title=refines>⊑</a> g ⟹ (g <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>) <a href="#refines" title=refines>⊑</a> (f <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)

---
**inverse_makes_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)

---
## Operation_interactions.thy

**unsafe_compose_absorb**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> ;p<sub>2</sub>)/C = p<sub>1</sub>/C ;p<sub>2</sub>

---
**unsafe_compose_absorb_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> ;p<sub>2</sub>)/C <a href="#equal" title=equal>=</a> p<sub>1</sub>/C ;p<sub>2</sub>

---
**unsafe_compose_absorb_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> ;p<sub>2</sub>)/C <a href="#equiv" title=equiv>≡</a> p<sub>1</sub>/C ;p<sub>2</sub>

---
**range_p_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p(a) ∩ C = {} ⟹ a ;b/(-C) <a href="#equiv" title=equiv>≡</a> a ;b

---
**compose_absorb_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>)/C = p<sub>1</sub>/C <a href="#composition" title=composition>;</a> p<sub>2</sub>

---
**compose_absorb_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>)/C <a href="#equal" title=equal>=</a> p<sub>1</sub>/C <a href="#composition" title=composition>;</a> p<sub>2</sub>

---
**compose_absorb_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>)/C <a href="#equiv" title=equiv>≡</a> p<sub>1</sub>/C <a href="#composition" title=composition>;</a> p<sub>2</sub>

---
**range_p_composition**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p(a) ∩ C = {} ⟹ a <a href="#composition" title=composition>;</a> b/(-C) <a href="#equiv" title=equiv>≡</a> a <a href="#composition" title=composition>;</a> b

---
**restrict_distrib_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>)/C = (p<sub>1</sub>/C <a href="#choice" title=choice>∪</a> p<sub>2</sub>/C)

---
**restrict_distrib_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>)/C <a href="#equal" title=equal>=</a> (p<sub>1</sub>/C <a href="#choice" title=choice>∪</a> p<sub>2</sub>/C)

---
**restrict_distrib_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>)/C <a href="#equiv" title=equiv>≡</a> (p<sub>1</sub>/C <a href="#choice" title=choice>∪</a> p<sub>2</sub>/C)

---
**restrict_distrib_4**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#choice" title=choice>∪</a> (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>)/C = a <a href="#choice" title=choice>∪</a> (p<sub>1</sub>/C <a href="#choice" title=choice>∪</a> p<sub>2</sub>/C)

---
**restriction_absorbed_by_inverse_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)/C = ((p∖C) <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)

---
**restriction_absorbed_by_inverse_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)/C <a href="#equal" title=equal>=</a> (p∖C) <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>

---
**restriction_absorbed_by_inverse_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)/C <a href="#equiv" title=equiv>≡</a> (p∖C) <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>

---
**compose_distrib1_1**

&nbsp;&nbsp;&nbsp;&nbsp;q <a href="#composition" title=composition>;</a> (p<sub>1</sub>∪p<sub>2</sub>) = (q <a href="#composition" title=composition>;</a> p<sub>1</sub>) <a href="#choice" title=choice>∪</a> (q <a href="#composition" title=composition>;</a> p<sub>2</sub>)

---
**compose_distrib1_2**

&nbsp;&nbsp;&nbsp;&nbsp;q <a href="#composition" title=composition>;</a> (p<sub>1</sub>∪p<sub>2</sub>) <a href="#equal" title=equal>=</a> (q <a href="#composition" title=composition>;</a> p<sub>1</sub>) <a href="#choice" title=choice>∪</a> (q <a href="#composition" title=composition>;</a> p<sub>2</sub>)

---
**compose_distrib1_3**

&nbsp;&nbsp;&nbsp;&nbsp;q <a href="#composition" title=composition>;</a> (p<sub>1</sub>∪p<sub>2</sub>) <a href="#equiv" title=equiv>≡</a> (q <a href="#composition" title=composition>;</a> p<sub>1</sub>) <a href="#choice" title=choice>∪</a> (q <a href="#composition" title=composition>;</a> p<sub>2</sub>)

---
**compose_distrib2_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>∪p<sub>2</sub>) <a href="#composition" title=composition>;</a> q = (p<sub>1</sub> <a href="#composition" title=composition>;</a> q) <a href="#choice" title=choice>∪</a> (p<sub>2</sub> <a href="#composition" title=composition>;</a> q)

---
**compose_distrib2_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>∪p<sub>2</sub>) <a href="#composition" title=composition>;</a> q <a href="#equal" title=equal>=</a> (p<sub>1</sub> <a href="#composition" title=composition>;</a> q) <a href="#choice" title=choice>∪</a> (p<sub>2</sub> <a href="#composition" title=composition>;</a> q)

---
**compose_distrib2_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>∪p<sub>2</sub>) <a href="#composition" title=composition>;</a> q <a href="#equiv" title=equiv>≡</a> (p<sub>1</sub> <a href="#composition" title=composition>;</a> q) <a href="#choice" title=choice>∪</a> (p<sub>2</sub> <a href="#composition" title=composition>;</a> q)

---
**choice_distributes_over_composition**

&nbsp;&nbsp;&nbsp;&nbsp;q∪(p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>) <a href="#equiv" title=equiv>≡</a> (q∪p<sub>1</sub>) <a href="#composition" title=composition>;</a> (q∪p<sub>2</sub>)

---
**corestriction_on_composition**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#corestrict_p" title=corestrict_p>∖</a> s<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub> = p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub> <a href="#restrict_p" title=restrict_p>/</a> s<sub>1</sub>

---
**corestrict_compose**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>) <a href="#corestrict_p" title=corestrict_p>∖</a> C = p<sub>1</sub> <a href="#composition" title=composition>;</a> (p<sub>2</sub> <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
**unsafe_gets_safe_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> ;p<sub>2</sub>) <a href="#composition" title=composition>;</a> p<sub>3</sub> = (p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>) <a href="#composition" title=composition>;</a> p<sub>3</sub>

---
**unsafe_gets_safe_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> ;p<sub>2</sub>) <a href="#composition" title=composition>;</a> p<sub>3</sub> <a href="#equal" title=equal>=</a> (p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>) <a href="#composition" title=composition>;</a> p<sub>3</sub>

---
**unsafe_gets_safe_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> ;p<sub>2</sub>) <a href="#composition" title=composition>;</a> p<sub>3</sub> <a href="#equiv" title=equiv>≡</a> (p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>) <a href="#composition" title=composition>;</a> p<sub>3</sub>

---
**unsafe_gets_safe_extended**

&nbsp;&nbsp;&nbsp;&nbsp;((p<sub>1</sub> ;p<sub>2</sub>) ;p<sub>3</sub>) <a href="#composition" title=composition>;</a> p<sub>4</sub> <a href="#equiv" title=equiv>≡</a> ((p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>) <a href="#composition" title=composition>;</a> p<sub>3</sub>) <a href="#composition" title=composition>;</a> p<sub>4</sub>

---
**equivalency_of_compositions_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>∖Pre p<sub>2</sub>) ;p<sub>2</sub> = p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>

---
**equivalency_of_compositions_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>∖Pre p<sub>2</sub>) ;p<sub>2</sub> <a href="#equal" title=equal>=</a> p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>

---
**equivalency_of_compositions_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>∖Pre p<sub>2</sub>) ;p<sub>2</sub> <a href="#equiv" title=equiv>≡</a> p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>

---
**composition_inverse_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#composition" title=composition>;</a> q) <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a> = (q <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>) <a href="#composition" title=composition>;</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)

---
**composition_inverse_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#composition" title=composition>;</a> q) <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a> <a href="#equal" title=equal>=</a> (q <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>) <a href="#composition" title=composition>;</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)

---
**composition_inverse_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#composition" title=composition>;</a> q) <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a> <a href="#equiv" title=equiv>≡</a> (q <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>) <a href="#composition" title=composition>;</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)

---
**choice_inverse_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#choice" title=choice>∪</a> q) <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a> = (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>) <a href="#choice" title=choice>∪</a> (q <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)

---
**choice_inverse_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#choice" title=choice>∪</a> q) <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a> <a href="#equal" title=equal>=</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>) <a href="#choice" title=choice>∪</a> (q <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)

---
**choice_inverse_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#choice" title=choice>∪</a> q) <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a> <a href="#equiv" title=equiv>≡</a> (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>) <a href="#choice" title=choice>∪</a> (q <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)

---
**corestriction_restriction_on_unsafe_composition_1**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#corestrict_p" title=corestrict_p>∖</a> s<sub>1</sub> <a href="#unsafe_composition" title=unsafe_composition>;</a> p<sub>2</sub> <a href="#equiv" title=equiv>≡</a> p<sub>1</sub> <a href="#unsafe_composition" title=unsafe_composition>;</a> p<sub>2</sub> <a href="#restrict_p" title=restrict_p>/</a> s<sub>1</sub>

---
**corestrict_gets_absorbed_by_unsafe_composition_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> <a href="#unsafe_composition" title=unsafe_composition>;</a> p<sub>2</sub>) <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#equiv" title=equiv>≡</a> (p<sub>1</sub> <a href="#corestrict_p" title=corestrict_p>∖</a> C) <a href="#unsafe_composition" title=unsafe_composition>;</a> p<sub>2</sub>

---
**corestrict_gets_absorbed_by_unsafe_composition_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> <a href="#unsafe_composition" title=unsafe_composition>;</a> p<sub>2</sub>) <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#equiv" title=equiv>≡</a> p<sub>1</sub> <a href="#unsafe_composition" title=unsafe_composition>;</a> (p<sub>2</sub> <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
**corestriction_on_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#corestrict_p" title=corestrict_p>∖</a> s <a href="#unsafe_composition" title=unsafe_composition>;</a> p<sub>2</sub> = p<sub>1</sub> <a href="#unsafe_composition" title=unsafe_composition>;</a> p<sub>2</sub> <a href="#restrict_p" title=restrict_p>/</a> s

---
**corestrict_unsafe_compose**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p<sub>1</sub> ⟹ (p<sub>1</sub> <a href="#unsafe_composition" title=unsafe_composition>;</a> p<sub>2</sub>) <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#equiv" title=equiv>≡</a> p<sub>1</sub> <a href="#unsafe_composition" title=unsafe_composition>;</a> (p<sub>2</sub> <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
**corestriction_absorbed_by_inverse_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)∖C = ((p/C) <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)

---
**corestriction_absorbed_by_inverse_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)∖C <a href="#equal" title=equal>=</a> ((p/C) <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)

---
**corestriction_absorbed_by_inverse_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)∖C <a href="#equiv" title=equiv>≡</a> (p/C) <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>

---
**unsafe_composition_inverse_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p ;q) <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a> <a href="#equiv" title=equiv>≡</a> (q <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>) ;(p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)

---
**corestrict_choice_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>) <a href="#corestrict_p" title=corestrict_p>∖</a> C = (p<sub>1</sub> <a href="#corestrict_p" title=corestrict_p>∖</a> C) <a href="#choice" title=choice>∪</a> (p<sub>2</sub> <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
**corestrict_choice_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>) <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#equal" title=equal>=</a> (p<sub>1</sub> <a href="#corestrict_p" title=corestrict_p>∖</a> C) <a href="#choice" title=choice>∪</a> (p<sub>2</sub> <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
**corestrict_choice_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>) <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#equiv" title=equiv>≡</a> (p<sub>1</sub> <a href="#corestrict_p" title=corestrict_p>∖</a> C) <a href="#choice" title=choice>∪</a> (p<sub>2</sub> <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
**unsafe_compose_distrib1_3_1**

&nbsp;&nbsp;&nbsp;&nbsp;q ;(p<sub>1</sub>∪p<sub>2</sub>) = (q ;p<sub>1</sub>) <a href="#choice" title=choice>∪</a> (q ;p<sub>2</sub>)

---
**unsafe_compose_distrib1_3_2**

&nbsp;&nbsp;&nbsp;&nbsp;q ;(p<sub>1</sub>∪p<sub>2</sub>) <a href="#equal" title=equal>=</a> (q ;p<sub>1</sub>) <a href="#choice" title=choice>∪</a> (q ;p<sub>2</sub>)

---
**unsafe_compose_distrib1_3_3**

&nbsp;&nbsp;&nbsp;&nbsp;q ;(p<sub>1</sub>∪p<sub>2</sub>) <a href="#equiv" title=equiv>≡</a> (q ;p<sub>1</sub>) <a href="#choice" title=choice>∪</a> (q ;p<sub>2</sub>)

---
**unsafe_compose_distrib2_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>∪p<sub>2</sub>) ;q = (p<sub>1</sub> ;q) <a href="#choice" title=choice>∪</a> (p<sub>2</sub> ;q)

---
**unsafe_compose_distrib2_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>∪p<sub>2</sub>) ;q <a href="#equal" title=equal>=</a> (p<sub>1</sub> ;q) <a href="#choice" title=choice>∪</a> (p<sub>2</sub> ;q)

---
**unsafe_compose_distrib2_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>∪p<sub>2</sub>) ;q <a href="#equiv" title=equiv>≡</a> (p<sub>1</sub> ;q) <a href="#choice" title=choice>∪</a> (p<sub>2</sub> ;q)

---
**choice_distributes_over_composition_4**

&nbsp;&nbsp;&nbsp;&nbsp;q∪(p<sub>1</sub> ;p<sub>2</sub>) <a href="#equiv" title=equiv>≡</a> (q∪p<sub>1</sub>) <a href="#unsafe_composition" title=unsafe_composition>;</a> (q∪p<sub>2</sub>)

---
**until_simplification_1**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#composition" title=composition>;</a> n∖C <a href="#choice" title=choice>∪</a> a <a href="#composition" title=composition>;</a> m∖C <a href="#equiv" title=equiv>≡</a> a <a href="#composition" title=composition>;</a> (n <a href="#choice" title=choice>∪</a> m)∖C

---
**until_simplification_2**

&nbsp;&nbsp;&nbsp;&nbsp;a ;n∖C <a href="#choice" title=choice>∪</a> a ;m∖C <a href="#equiv" title=equiv>≡</a> a ;(n <a href="#choice" title=choice>∪</a> m)∖C

---
## Prime.thy

**finite_Field_implies_finite_relation**

&nbsp;&nbsp;&nbsp;&nbsp;finite (Field r)  ⟹ finite r

---
&nbsp;&nbsp;&nbsp;&nbsp;finite (<a href="#S" title=S>S</a> p) ⟹ finite (Pre p)

---
**finite_S_implies_finite_post**

&nbsp;&nbsp;&nbsp;&nbsp;finite (<a href="#S" title=S>S</a> p)  ⟹ finite (post p)

---
**post_cardinality_equals_P_cardinality**

&nbsp;&nbsp;&nbsp;&nbsp;P = {〈State={a,b}, Pre={a}, post={(a,b)}〉 | a b. (a,b) ∈ (post p)}  ⟹ card (post p) = card P

---
**same_card_and_finite_impl_finite**

&nbsp;&nbsp;&nbsp;&nbsp;card a = card b  ⟹ finite a  ⟹ card a > 0  ⟹ finite b

---
**fst_in_state**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#is_minimal" title=is_minimal>is_minimal</a> p ⟹ P = {〈State={a,b}, Pre={a}, post={(a,b)}〉 | a b. (a,b) ∈ post p} ⟹ r ∈ post p ⟹ fst r ∈ State p

---
**snd_is_state**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#is_minimal" title=is_minimal>is_minimal</a> p ⟹ P = {〈State={a,b}, Pre={a}, post={(a,b)}〉 | a b. (a,b) ∈ post p} ⟹ r ∈ post p ⟹ snd r ∈ State p

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#is_minimal" title=is_minimal>is_minimal</a> p ⟹ P = {〈State={a,b}, Pre={a}, post={(a,b)}〉 | a b. (a,b) ∈ post p} ⟹ s ∈ State p ⟹ ∃r ∈ post p. fst r = s ∨ snd r = s

---
**choice_set_decomp_1**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ <a href="#Choice_set" title=Choice_set>⋃<sub>P</sub></a> (insert x F) = <a href="#Choice_set" title=Choice_set>⋃<sub>P</sub></a> F <a href="#choice" title=choice>∪</a> x

---
**choice_set_decomp_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Choice_set" title=Choice_set>⋃<sub>P</sub></a> (insert x F) = <a href="#Choice_set" title=Choice_set>⋃<sub>P</sub></a> F <a href="#choice" title=choice>∪</a> x

---
**choice_set_equality**

&nbsp;&nbsp;&nbsp;&nbsp;finite (<a href="#S" title=S>S</a> p) ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#is_minimal" title=is_minimal>is_minimal</a> p ⟹ P = {〈State={a,b}, Pre={a}, post={(a,b)}〉 | a b. (a,b) ∈ post p} ⟹ p<sub>i</sub> ∈ P ⟹ <a href="#Choice_set" title=Choice_set>⋃<sub>P</sub></a> P = p

---
&nbsp;&nbsp;&nbsp;&nbsp;finite (<a href="#S" title=S>S</a> p) ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#is_minimal" title=is_minimal>is_minimal</a> p ⟹ P = {〈State={a,b},Pre={a},post={(a,b)}〉 |a b . (a,b) ∈ (post p)} ⟹ p<sub>i</sub> ∈ P ⟹ <a href="#is_prime" title=is_prime>is_prime</a> p<sub>i</sub> ∧ p<sub>i</sub> <a href="#specialize" title=specialize>⊆</a> p ∧ <a href="#Choice_set" title=Choice_set>⋃<sub>P</sub></a> P = p

---
&nbsp;&nbsp;&nbsp;&nbsp;finite (<a href="#S" title=S>S</a> p) ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#is_minimal" title=is_minimal>is_minimal</a> p ⟹ ∃ P. p<sub>i</sub> ∈ P → <a href="#is_prime" title=is_prime>is_prime</a> p<sub>i</sub> ∧ p<sub>i</sub> <a href="#specialize" title=specialize>⊆</a> p ∧ <a href="#Choice_set" title=Choice_set>⋃<sub>P</sub></a> P = p

---
## Restriction.thy

**restrict_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (p <a href="#restrict_p" title=restrict_p>/</a> D) ⊆ D

---
**restrict_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (p <a href="#restrict_p" title=restrict_p>/</a> D) ⊆ Pre p

---
**restrict_prop**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (p <a href="#restrict_p" title=restrict_p>/</a> D) ⊆ Pre p ∩ D

---
**restrict_idem**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#restrict_p" title=restrict_p>/</a> C) <a href="#restrict_p" title=restrict_p>/</a> C = p <a href="#restrict_p" title=restrict_p>/</a> C

---
**restrict_inter**

&nbsp;&nbsp;&nbsp;&nbsp;(p/C<sub>1</sub>)/C<sub>2</sub> = p/(C<sub>1</sub> ∩ C<sub>2</sub>)

---
**restriction_equiv**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>1</sub> ⟹ (f<sub>1</sub> <a href="#restrict_p" title=restrict_p>/</a> C) <a href="#equiv" title=equiv>≡</a> p<sub>1</sub> <a href="#restrict_p" title=restrict_p>/</a> C

---
**equality_is_maintained_by_restriction**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> <a href="#equal" title=equal>=</a> p<sub>1</sub> ⟹ (f<sub>1</sub> <a href="#restrict_p" title=restrict_p>/</a> C) <a href="#equal" title=equal>=</a> p<sub>1</sub> <a href="#restrict_p" title=restrict_p>/</a> C

---
**restrict_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (p <a href="#restrict_p" title=restrict_p>/</a> C)

---
**restrict_might_make_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ Domain (post p) ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (p <a href="#restrict_p" title=restrict_p>/</a> C)

---
**restrict_refine_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#strengthens" title=strengthens>strengthens</a> p  (p <a href="#restrict_p" title=restrict_p>/</a> C)

---
**restrict_refine_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#strengthens" title=strengthens>strengthens</a> (p <a href="#restrict_p" title=restrict_p>/</a> C) p

---
**restrict_refine_3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#strengthens" title=strengthens>strengthens</a> p  q ⟹ <a href="#strengthens" title=strengthens>strengthens</a> (p <a href="#restrict_p" title=restrict_p>/</a> C) (q <a href="#restrict_p" title=restrict_p>/</a> C)

---
**restrict_refine_4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#weakens" title=weakens>weakens</a> p  (p <a href="#restrict_p" title=restrict_p>/</a> C)

---
**restrict_refine_5**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#weakens" title=weakens>weakens</a> p  q ⟹ <a href="#weakens" title=weakens>weakens</a> (p <a href="#restrict_p" title=restrict_p>/</a> C) (q <a href="#restrict_p" title=restrict_p>/</a> C)

---
**restrict_refine**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#refines" title=refines>⊑</a> p <a href="#restrict_p" title=restrict_p>/</a> C

---
**restrict_refineorder1**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ p <a href="#restrict_p" title=restrict_p>/</a> C <a href="#refines" title=refines>⊑</a> p <a href="#restrict_p" title=restrict_p>/</a> D

---
**restriction_refsafety**

&nbsp;&nbsp;&nbsp;&nbsp;q <a href="#refines" title=refines>⊑</a> p ⟹ q <a href="#restrict_p" title=restrict_p>/</a> C <a href="#refines" title=refines>⊑</a> p <a href="#restrict_p" title=restrict_p>/</a> C

---
**restriction_subsafety**

&nbsp;&nbsp;&nbsp;&nbsp;q <a href="#specialize" title=specialize>⊆</a> p ⟹ q <a href="#restrict_p" title=restrict_p>/</a> C <a href="#specialize" title=specialize>⊆</a> p <a href="#restrict_p" title=restrict_p>/</a> C

---
**restriction_refsafety2**

&nbsp;&nbsp;&nbsp;&nbsp;q <a href="#refines" title=refines>⊑</a> p ⟹ D ⊆ C ⟹ q <a href="#restrict_p" title=restrict_p>/</a> C <a href="#refines" title=refines>⊑</a> p <a href="#restrict_p" title=restrict_p>/</a> D

---
**implements_safety_restriction**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#implements" title=implements>implements</a> a b ⟹ <a href="#implements" title=implements>implements</a> (a <a href="#restrict_p" title=restrict_p>/</a> C) (b <a href="#restrict_p" title=restrict_p>/</a> C)

---
**restrict_subprogorder1**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ p <a href="#restrict_p" title=restrict_p>/</a> D <a href="#specialize" title=specialize>⊆</a> p <a href="#restrict_p" title=restrict_p>/</a> C

---
**restrict_subprog**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#restrict_p" title=restrict_p>/</a> C <a href="#specialize" title=specialize>⊆</a> p

---
## Unsafe_composition.thy

**equivalence_is_maintained_by_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>1</sub> ⟹ f<sub>2</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub> ⟹ f<sub>1</sub> <a href="#unsafe_composition" title=unsafe_composition>;</a> f<sub>2</sub> <a href="#equiv" title=equiv>≡</a> p<sub>1</sub> <a href="#unsafe_composition" title=unsafe_composition>;</a> p<sub>2</sub>

---
**equality_is_maintained_by_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> <a href="#equal" title=equal>=</a> p<sub>1</sub> ⟹ f<sub>2</sub> <a href="#equal" title=equal>=</a> p<sub>2</sub> ⟹ f<sub>1</sub> <a href="#unsafe_composition" title=unsafe_composition>;</a> f<sub>2</sub> <a href="#equal" title=equal>=</a> p<sub>1</sub> <a href="#unsafe_composition" title=unsafe_composition>;</a> p<sub>2</sub>

---
**unsafe_compose_feasible_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> (p<sub>1</sub> <a href="#unsafe_composition" title=unsafe_composition>;</a> p<sub>2</sub>) ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> p<sub>1</sub>

---
**unsafe_compose_feasible_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p<sub>1</sub>, p<sub>2</sub>] ⟹ <a href="#Range_p" title=Range_p>Range_p</a> p<sub>1</sub> ⊆ Pre p<sub>2</sub> ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (p<sub>1</sub> <a href="#unsafe_composition" title=unsafe_composition>;</a> p<sub>2</sub>)

---
## Unsafe_composition2.thy

&nbsp;&nbsp;&nbsp;&nbsp;Pre (p<sub>1</sub> <a href="#unsafe_composition2" title=unsafe_composition2>;<sup>p</sup></a> (p<sub>2</sub> <a href="#unsafe_composition2" title=unsafe_composition2>;<sup>p</sup></a> p<sub>3</sub>)) ⊆ Pre ((p<sub>1</sub> <a href="#unsafe_composition2" title=unsafe_composition2>;<sup>p</sup></a> p<sub>2</sub>) <a href="#unsafe_composition2" title=unsafe_composition2>;<sup>p</sup></a> p<sub>3</sub>)

---
&nbsp;&nbsp;&nbsp;&nbsp;Pre ((p <a href="#unsafe_composition2" title=unsafe_composition2>;<sup>p</sup></a> q) <a href="#unsafe_composition2" title=unsafe_composition2>;<sup>p</sup></a> r) = Pre (p <a href="#unsafe_composition2" title=unsafe_composition2>;<sup>p</sup></a> (q <a href="#unsafe_composition2" title=unsafe_composition2>;<sup>p</sup></a> r))

---
**equivalence_is_maintained_by_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>1</sub> ⟹ f<sub>2</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub> ⟹ f<sub>1</sub> <a href="#unsafe_composition2" title=unsafe_composition2>;<sup>p</sup></a> f<sub>2</sub> <a href="#equiv" title=equiv>≡</a> p<sub>1</sub> <a href="#unsafe_composition2" title=unsafe_composition2>;<sup>p</sup></a> p<sub>2</sub>

---
**unsafe_compose_feasible_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> (p<sub>1</sub> <a href="#unsafe_composition2" title=unsafe_composition2>;<sup>p</sup></a> p<sub>2</sub>) ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> p<sub>1</sub>

---
**unsafe_compose_feasible_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p<sub>1</sub>, p<sub>2</sub>] ⟹ <a href="#Range_p" title=Range_p>Range_p</a> p<sub>1</sub> ⊆ Pre p<sub>2</sub> ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (p<sub>1</sub> <a href="#unsafe_composition2" title=unsafe_composition2>;<sup>p</sup></a> p<sub>2</sub>)

---
## Unsafe_composition3.thy

**equivalence_is_maintained_by_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>1</sub> ⟹ f<sub>2</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub> ⟹ f<sub>1</sub> <a href="#unsafe_composition3" title=unsafe_composition3>;<sub>P</sub></a> f<sub>2</sub> <a href="#equiv" title=equiv>≡</a> p<sub>1</sub> <a href="#unsafe_composition3" title=unsafe_composition3>;<sub>P</sub></a> p<sub>2</sub>

---
**equality_is_maintained_by_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> <a href="#equal" title=equal>=</a> p<sub>1</sub> ⟹ f<sub>2</sub> <a href="#equal" title=equal>=</a> p<sub>2</sub> ⟹ f<sub>1</sub> <a href="#unsafe_composition3" title=unsafe_composition3>;<sub>P</sub></a> f<sub>2</sub> <a href="#equal" title=equal>=</a> p<sub>1</sub> <a href="#unsafe_composition3" title=unsafe_composition3>;<sub>P</sub></a> p<sub>2</sub>

---
**unsafe_compose_feasible_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> (p<sub>1</sub> <a href="#unsafe_composition3" title=unsafe_composition3>;<sub>P</sub></a> p<sub>2</sub>) ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> p<sub>1</sub>

---
**unsafe_compose_feasible_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p<sub>1</sub>, p<sub>2</sub>] ⟹ <a href="#Range_p" title=Range_p>Range_p</a> p<sub>1</sub> ⊆ Pre p<sub>2</sub> ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (p<sub>1</sub> <a href="#unsafe_composition3" title=unsafe_composition3>;<sub>P</sub></a> p<sub>2</sub>)

---
## Boolean.thy

**restrict_true**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#restrict_p" title=restrict_p>/</a> (<a href="#TRUE" title=TRUE>TRUE</a> (<a href="#S" title=S>S</a> p)) <a href="#equal" title=equal>=</a> p

---
**restrict_false**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#restrict_p" title=restrict_p>/</a> (<a href="#FALSE" title=FALSE>FALSE</a>) <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p)

---
**cond_false_1**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#restrict_p" title=restrict_p>/</a> <a href="#FALSE" title=FALSE>FALSE</a> <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p)

---
**corestrict_true**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ p <a href="#corestrict_p" title=corestrict_p>∖</a> (<a href="#TRUE" title=TRUE>TRUE</a> (<a href="#S" title=S>S</a> p)) <a href="#equiv" title=equiv>≡</a> p

---
**corestrict_false**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#corestrict_p" title=corestrict_p>∖</a> <a href="#FALSE" title=FALSE>FALSE</a> = <a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p)

---
**corestrict_false**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#corestrict_p" title=corestrict_p>∖</a> <a href="#FALSE" title=FALSE>FALSE</a> <a href="#equiv" title=equiv>≡</a> <a href="#Infeas" title=Infeas>Infeas</a> (Pre p)

---
**if_true**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#ITE" title=ITE>ITE</a> (<a href="#TRUE" title=TRUE>TRUE</a> (<a href="#S" title=S>S</a> p<sub>1</sub> ∪ <a href="#S" title=S>S</a> p<sub>2</sub>)) p<sub>1</sub> p<sub>2</sub> <a href="#equiv" title=equiv>≡</a> p<sub>1</sub>

---
**if_false1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#ITE" title=ITE>ITE</a> (<a href="#FALSE" title=FALSE>FALSE</a>) p<sub>1</sub> p<sub>2</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub>

---
**true_selects_first_program_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#GC" title=GC>GC</a> [(<a href="#TRUE" title=TRUE>TRUE</a> (<a href="#S" title=S>S</a> p<sub>1</sub> ∪ <a href="#S" title=S>S</a> p<sub>2</sub>), p<sub>1</sub>), (FALSE, p<sub>2</sub>)] <a href="#equiv" title=equiv>≡</a> p<sub>1</sub>

---
**false_selects_second_program_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#GC" title=GC>GC</a> [(FALSE, p<sub>1</sub>), ((<a href="#TRUE" title=TRUE>TRUE</a> (<a href="#S" title=S>S</a> p<sub>1</sub> ∪ <a href="#S" title=S>S</a> p<sub>2</sub>)), p<sub>2</sub>)] <a href="#equiv" title=equiv>≡</a> p<sub>2</sub>

---
**restrict_false2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> p ⊆ <a href="#S" title=S>S</a> q ⟹ p <a href="#restrict_p" title=restrict_p>/</a> <a href="#FALSE" title=FALSE>FALSE</a> <a href="#choice" title=choice>∪</a> q = <a href="#Fail" title=Fail>Fail</a> {} <a href="#choice" title=choice>∪</a> q

---
**implies_prop**

&nbsp;&nbsp;&nbsp;&nbsp;(C →<sub>s</sub> D) = UNIV ≡ (C ⊆ D)

---
**and_prop**

&nbsp;&nbsp;&nbsp;&nbsp;A ⊆ X ⟹ B ⊆ X ⟹ A ∧<sub>s</sub> B = <a href="#TRUE" title=TRUE>TRUE</a> X ≡ A = X ∧ B = X

---
**or_prop**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#TRUE" title=TRUE>TRUE</a> X ⊆ (A ∨<sub>s</sub> B) ≡ ∀x∈X. x ∈ A ∨ x ∈ B

---
## Fail.thy

**fail_is_valid**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_valid" title=is_valid>is_valid</a> (<a href="#Fail" title=Fail>Fail</a> s)

---
**fail_is_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#Fail" title=Fail>Fail</a> s)

---
**fail_is_total**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_total" title=is_total>is_total</a> (<a href="#Fail" title=Fail>Fail</a> s)

---
**fail_is_idempondent_composition**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Fail" title=Fail>Fail</a> C <a href="#composition" title=composition>;</a> <a href="#Fail" title=Fail>Fail</a> C = <a href="#Fail" title=Fail>Fail</a> C

---
**fail_is_idempondent_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Fail" title=Fail>Fail</a> C <a href="#unsafe_composition" title=unsafe_composition>;</a> <a href="#Fail" title=Fail>Fail</a> C = <a href="#Fail" title=Fail>Fail</a> C

---
**fail_equiv**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Fail" title=Fail>Fail</a> C <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> D

---
**no_pre_is_fail**

&nbsp;&nbsp;&nbsp;&nbsp;Pre p = {} ⟹ <a href="#Fail" title=Fail>Fail</a> s <a href="#equiv" title=equiv>≡</a> p

---
**NOT_fail_choice_r**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#choice" title=choice>∪</a> <a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p) <a href="#equal" title=equal>=</a> p

---
**fail_choice_r**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#choice" title=choice>∪</a> <a href="#Fail" title=Fail>Fail</a> C <a href="#equiv" title=equiv>≡</a> p

---
**NOT_fail_choice_l**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p) <a href="#choice" title=choice>∪</a> p <a href="#equal" title=equal>=</a> p

---
**fail_choice_l**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Fail" title=Fail>Fail</a> C <a href="#choice" title=choice>∪</a> p <a href="#equiv" title=equiv>≡</a> p

---
**fail_compose_l_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p) <a href="#composition" title=composition>;</a> p <a href="#equal" title=equal>=</a> <a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p)

---
**fail_compose_l**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Fail" title=Fail>Fail</a> C <a href="#composition" title=composition>;</a> p <a href="#equal" title=equal>=</a> <a href="#Fail" title=Fail>Fail</a> (C ∪ <a href="#S" title=S>S</a> p)

---
**fail_compose_r_2**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#composition" title=composition>;</a> <a href="#Fail" title=Fail>Fail</a> C <a href="#equal" title=equal>=</a> <a href="#Fail" title=Fail>Fail</a> (C ∪ <a href="#S" title=S>S</a> p)

---
**fail_compose_r**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#composition" title=composition>;</a> <a href="#Fail" title=Fail>Fail</a> C <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> C

---
**only_fail_refines_fail**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#refines" title=refines>⊑</a> <a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p)) = (p <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p))

---
**refine_fail**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#refines" title=refines>⊑</a> <a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p)

---
**fail_refine_self**

&nbsp;&nbsp;&nbsp;&nbsp;(<a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p) <a href="#refines" title=refines>⊑</a> p) = (p <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p))

---
**fail_specialize_self**

&nbsp;&nbsp;&nbsp;&nbsp;(p <a href="#specialize" title=specialize>⊆</a> <a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p)) = (p <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p))

---
**range_of_fail**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Range_p" title=Range_p>Range_p</a> (<a href="#Fail" title=Fail>Fail</a> C) = {}

---
**choice_fail_implication**

&nbsp;&nbsp;&nbsp;&nbsp;(a <a href="#choice" title=choice>∪</a> b <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}) = (a <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {} ∧ b <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {})

---
**fail_refine**

&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ <a href="#S" title=S>S</a> p ⟹ p <a href="#refines" title=refines>⊑</a> <a href="#Fail" title=Fail>Fail</a> C

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ <a href="#S" title=S>S</a> p ⟹ <a href="#Fail" title=Fail>Fail</a> C <a href="#specialize" title=specialize>⊆</a> p

---
**fail_specialize2**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#specialize" title=specialize>⊆</a> <a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p) ≡ p <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**fail_refine2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p) <a href="#refines" title=refines>⊑</a> p ≡ p <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**compose_empty_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> a = {} ⟹ b <a href="#composition" title=composition>;</a> a = <a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> b)

---
**compose_empty_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> a = {} ⟹ a <a href="#composition" title=composition>;</a> b = <a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> b)

---
**fail_union_1**

&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ <a href="#S" title=S>S</a> p ⟹ <a href="#Fail" title=Fail>Fail</a> C <a href="#choice" title=choice>∪</a> (p <a href="#choice" title=choice>∪</a> q) = (p <a href="#choice" title=choice>∪</a> q)

---
**fail_compose**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p) <a href="#composition" title=composition>;</a> p = <a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p)

---
**fail_union_2**

&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ <a href="#S" title=S>S</a> a ⟹ a <a href="#choice" title=choice>∪</a> <a href="#Fail" title=Fail>Fail</a> C = a <a href="#choice" title=choice>∪</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**fail_choice_decomp**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#choice" title=choice>∪</a> q <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {} ≡ p <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {} ∧ q <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**fail_specialize**

&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ <a href="#S" title=S>S</a> p ⟹ <a href="#Fail" title=Fail>Fail</a> C <a href="#specialize" title=specialize>⊆</a> p

---
**fail_specialize3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Fail" title=Fail>Fail</a> {} <a href="#specialize" title=specialize>⊆</a> p

---
## Havoc.thy

**havoc_is_valid**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_valid" title=is_valid>is_valid</a> (<a href="#Havoc" title=Havoc>Havoc</a> s)

---
**havoc_is_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#Havoc" title=Havoc>Havoc</a> s)

---
**havoc_is_total**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_total" title=is_total>is_total</a> (<a href="#Havoc" title=Havoc>Havoc</a> s)

---
**havoc_is_idempondent_composition**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Havoc" title=Havoc>Havoc</a> C <a href="#composition" title=composition>;</a> <a href="#Havoc" title=Havoc>Havoc</a> C = <a href="#Havoc" title=Havoc>Havoc</a> C

---
**havoc_is_idempondent_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Havoc" title=Havoc>Havoc</a> C <a href="#unsafe_composition" title=unsafe_composition>;</a> <a href="#Havoc" title=Havoc>Havoc</a> C = <a href="#Havoc" title=Havoc>Havoc</a> C

---
**havoc_choice_l**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> p ⊆ C ⟹ <a href="#Havoc" title=Havoc>Havoc</a> C <a href="#choice" title=choice>∪</a> p = <a href="#Havoc" title=Havoc>Havoc</a> C

---
**havoc_choice_r**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> p ⊆ C ⟹ p <a href="#choice" title=choice>∪</a> <a href="#Havoc" title=Havoc>Havoc</a> C = <a href="#Havoc" title=Havoc>Havoc</a> C

---
**havoc_pre_State**

&nbsp;&nbsp;&nbsp;&nbsp;State (p <a href="#composition" title=composition>;</a> <a href="#Havoc" title=Havoc>Havoc</a> (<a href="#S" title=S>S</a> p)) = State (<a href="#Havoc" title=Havoc>Havoc</a> (<a href="#S" title=S>S</a> p) <a href="#restrict_p" title=restrict_p>/</a> Pre p)

---
**havoc_pre_S**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> p ⊆ C ⟹ <a href="#S" title=S>S</a> (p <a href="#composition" title=composition>;</a> <a href="#Havoc" title=Havoc>Havoc</a> C) = <a href="#S" title=S>S</a> (<a href="#Havoc" title=Havoc>Havoc</a> C <a href="#restrict_p" title=restrict_p>/</a> Pre p)

---
**NOT_havoc_pre_Pre**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (p <a href="#composition" title=composition>;</a> <a href="#Havoc" title=Havoc>Havoc</a> (<a href="#S" title=S>S</a> p)) = Pre (<a href="#Havoc" title=Havoc>Havoc</a> (<a href="#S" title=S>S</a> p) <a href="#restrict_p" title=restrict_p>/</a> Pre p)

---
**havoc_pre_Pre**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> p ⊆ C ⟹is_feasible p ⟹ Pre (p <a href="#composition" title=composition>;</a> <a href="#Havoc" title=Havoc>Havoc</a> C) = Pre (<a href="#Havoc" title=Havoc>Havoc</a> C <a href="#restrict_p" title=restrict_p>/</a> Pre p)

---
**NOT_havoc_pre_post_1**

&nbsp;&nbsp;&nbsp;&nbsp;post (p <a href="#composition" title=composition>;</a> <a href="#Havoc" title=Havoc>Havoc</a> (<a href="#S" title=S>S</a> p)) = post (<a href="#Havoc" title=Havoc>Havoc</a> (<a href="#S" title=S>S</a> p) <a href="#restrict_p" title=restrict_p>/</a> Pre p)

---
**NOT_havoc_pre_post_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ post (p <a href="#composition" title=composition>;</a> <a href="#Havoc" title=Havoc>Havoc</a> (<a href="#S" title=S>S</a> p)) = post (<a href="#Havoc" title=Havoc>Havoc</a> (<a href="#S" title=S>S</a> p) <a href="#restrict_p" title=restrict_p>/</a> Pre p)

---
**havoc_pre_post**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> p ⊆ C ⟹is_feasible p ⟹ <a href="#restr_post" title=restr_post>restr_post</a> (p <a href="#composition" title=composition>;</a> <a href="#Havoc" title=Havoc>Havoc</a> C)/ Pre p = <a href="#restr_post" title=restr_post>restr_post</a> (<a href="#Havoc" title=Havoc>Havoc</a> C <a href="#restrict_p" title=restrict_p>/</a> Pre p)

---
**NOT_havoc_pre**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#composition" title=composition>;</a> <a href="#Havoc" title=Havoc>Havoc</a> (<a href="#S" title=S>S</a> p) <a href="#equiv" title=equiv>≡</a> <a href="#Havoc" title=Havoc>Havoc</a> (<a href="#S" title=S>S</a> p) <a href="#restrict_p" title=restrict_p>/</a> Pre p

---
**havoc_pre**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> p ⊆ C ⟹is_feasible p ⟹ (p <a href="#composition" title=composition>;</a> <a href="#Havoc" title=Havoc>Havoc</a> C) <a href="#equiv" title=equiv>≡</a> <a href="#Havoc" title=Havoc>Havoc</a> C <a href="#restrict_p" title=restrict_p>/</a> Pre p

---
**havoc_pre_unsafe**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> p ⊆ C ⟹ (p <a href="#unsafe_composition" title=unsafe_composition>;</a> <a href="#Havoc" title=Havoc>Havoc</a> C) <a href="#equiv" title=equiv>≡</a> <a href="#Havoc" title=Havoc>Havoc</a> C <a href="#restrict_p" title=restrict_p>/</a> Pre p

---
**havoc_co_restricted**

&nbsp;&nbsp;&nbsp;&nbsp;(<a href="#Havoc" title=Havoc>Havoc</a> C <a href="#restrict_p" title=restrict_p>/</a> D) <a href="#corestrict_p" title=corestrict_p>∖</a> D <a href="#equiv" title=equiv>≡</a> <a href="#Havoc" title=Havoc>Havoc</a> (C ∩ D)

---
**havoc_from_left_S**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> p ⊆ C ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#S" title=S>S</a> (<a href="#Havoc" title=Havoc>Havoc</a> C <a href="#composition" title=composition>;</a> p) = S(<a href="#Havoc" title=Havoc>Havoc</a> C <a href="#corestrict_p" title=corestrict_p>∖</a> <a href="#Range_p" title=Range_p>Range_p</a> (p))

---
**havoc_from_left_Pre**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> p ⊆ C ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ ¬ p <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> C ⟹ Pre (<a href="#Havoc" title=Havoc>Havoc</a> C <a href="#composition" title=composition>;</a> p) = C

---
**havoc_from_left_post**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> p ⊆ C ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ post (<a href="#Havoc" title=Havoc>Havoc</a> C <a href="#composition" title=composition>;</a> p) = post (<a href="#Havoc" title=Havoc>Havoc</a> C <a href="#corestrict_p" title=corestrict_p>∖</a> <a href="#Range_p" title=Range_p>Range_p</a> (p))

---
**havoc_from_left**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> p ⊆ C ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ ¬ p <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> C ⟹ <a href="#Havoc" title=Havoc>Havoc</a> C <a href="#composition" title=composition>;</a> p <a href="#equiv" title=equiv>≡</a> <a href="#Havoc" title=Havoc>Havoc</a> C <a href="#corestrict_p" title=corestrict_p>∖</a> <a href="#Range_p" title=Range_p>Range_p</a> p

---
**refine_havoc**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#refines" title=refines>⊑</a> <a href="#Havoc" title=Havoc>Havoc</a> (<a href="#S" title=S>S</a> p) <a href="#restrict_p" title=restrict_p>/</a> Pre p

---
**specialize_havoc**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#specialize" title=specialize>⊆</a> <a href="#Havoc" title=Havoc>Havoc</a> (<a href="#S" title=S>S</a> p) <a href="#restrict_p" title=restrict_p>/</a> Pre p

---
**refine_havoc2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_total" title=is_total>is_total</a> p ⟹ p <a href="#refines" title=refines>⊑</a> <a href="#Havoc" title=Havoc>Havoc</a> (<a href="#S" title=S>S</a> p)

---
**specialize_havoc2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> p ⊆ C ⟹ p <a href="#specialize" title=specialize>⊆</a> <a href="#Havoc" title=Havoc>Havoc</a> (C)

---
## Infeas.thy

**infeas_is_valid**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_valid" title=is_valid>is_valid</a> (<a href="#Infeas" title=Infeas>Infeas</a> s)

---
**infeas_is_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#Infeas" title=Infeas>Infeas</a> s)

---
**infeas_is_total**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_total" title=is_total>is_total</a> (<a href="#Infeas" title=Infeas>Infeas</a> s)

---
**infeas_is_idempondent_composition**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Infeas" title=Infeas>Infeas</a> C <a href="#composition" title=composition>;</a> <a href="#Infeas" title=Infeas>Infeas</a> C = <a href="#Infeas" title=Infeas>Infeas</a> C

---
**infeas_is_idempondent_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Infeas" title=Infeas>Infeas</a> C <a href="#unsafe_composition" title=unsafe_composition>;</a> <a href="#Infeas" title=Infeas>Infeas</a> C = <a href="#Infeas" title=Infeas>Infeas</a> C

---
**fail_equiv**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Infeas" title=Infeas>Infeas</a> C <a href="#equiv" title=equiv>≡</a> <a href="#Infeas" title=Infeas>Infeas</a> D

---
**not_total_infeas_makes_infeasible**

&nbsp;&nbsp;&nbsp;&nbsp;¬ <a href="#is_total" title=is_total>is_total</a> p ⟹ ¬ <a href="#is_feasible" title=is_feasible>is_feasible</a> (p <a href="#choice" title=choice>∪</a> <a href="#Infeas" title=Infeas>Infeas</a> (<a href="#S" title=S>S</a> p))

---
**infeas_makes_total**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_total" title=is_total>is_total</a> (p <a href="#choice" title=choice>∪</a> <a href="#Infeas" title=Infeas>Infeas</a> (<a href="#S" title=S>S</a> p))

---
**infeas_to_smaller_self**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#composition" title=composition>;</a> <a href="#Infeas" title=Infeas>Infeas</a> (<a href="#S" title=S>S</a> p) <a href="#equiv" title=equiv>≡</a> <a href="#Infeas" title=Infeas>Infeas</a> (Pre p ∩ Domain (post p))

---
**infeas_composition**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Infeas" title=Infeas>Infeas</a> (<a href="#S" title=S>S</a> p) <a href="#composition" title=composition>;</a> p = <a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p)

---
**infeas_unsafe_composition_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Infeas" title=Infeas>Infeas</a> (<a href="#S" title=S>S</a> p) <a href="#unsafe_composition" title=unsafe_composition>;</a> p = <a href="#Infeas" title=Infeas>Infeas</a> (<a href="#S" title=S>S</a> p)

---
**infeas_unsafe_composition_2**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#unsafe_composition" title=unsafe_composition>;</a> <a href="#Infeas" title=Infeas>Infeas</a> (<a href="#S" title=S>S</a> p) <a href="#equiv" title=equiv>≡</a> <a href="#Infeas" title=Infeas>Infeas</a> (Pre p)

---
**infeas_restriction**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Infeas" title=Infeas>Infeas</a> (C) <a href="#restrict_p" title=restrict_p>/</a> D <a href="#equiv" title=equiv>≡</a> <a href="#Infeas" title=Infeas>Infeas</a> (C ∩ D)

---
**infeas_corestriction**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Infeas" title=Infeas>Infeas</a> (C) <a href="#corestrict_p" title=corestrict_p>∖</a> D = <a href="#Fail" title=Fail>Fail</a> (C)

---
**infeas_corestriction2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Infeas" title=Infeas>Infeas</a> (C) <a href="#corestrict_p" title=corestrict_p>∖</a> D = <a href="#Infeas" title=Infeas>Infeas</a> (C)

---
## Skip.thy

**skip_is_valid**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_valid" title=is_valid>is_valid</a> (<a href="#Skip" title=Skip>Skip</a> s)

---
**skip_is_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#Skip" title=Skip>Skip</a> s)

---
**skip_is_total**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_total" title=is_total>is_total</a> (<a href="#Skip" title=Skip>Skip</a> s)

---
**skip_is_idempondent_composition**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> C <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> C = <a href="#Skip" title=Skip>Skip</a> C

---
**skip_is_idempondent_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> C <a href="#unsafe_composition" title=unsafe_composition>;</a> <a href="#Skip" title=Skip>Skip</a> C = <a href="#Skip" title=Skip>Skip</a> C

---
**skip_unsafe_compose_r_1**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#unsafe_composition" title=unsafe_composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#equal" title=equal>=</a> p

---
**skip_compose_r_post**

&nbsp;&nbsp;&nbsp;&nbsp;post (p <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p)) = post p

---
**skip_compose_r_Pre_1**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (p <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p)) = (Pre p ∩ Domain (post p))

---
**skip_compose_r_S**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (p <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p)) = <a href="#S" title=S>S</a> p

---
**Skip_compleft**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ p <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#equal" title=equal>=</a> p

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#composition" title=composition>;</a> p <a href="#equal" title=equal>=</a> p

---
**skip_compose2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ p <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#equiv" title=equiv>≡</a> p

---
**skip_compose_r_range2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ p <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (Range (post p)) <a href="#equal" title=equal>=</a>  p

---
**skip_compose_r_range**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ p <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#Range_p" title=Range_p>Range_p</a> p) <a href="#equiv" title=equiv>≡</a>  p

---
**skip_compose4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#Skip" title=Skip>Skip</a> (Pre p) <a href="#composition" title=composition>;</a> p <a href="#equiv" title=equiv>≡</a>  p

---
**skip_compose_r_3**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#equiv" title=equiv>≡</a> p <a href="#restrict_p" title=restrict_p>/</a> Domain (post p)

---
**skip_makes_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> (p <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p))

---
**skip_compose_l_S**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (<a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#composition" title=composition>;</a> p) = <a href="#S" title=S>S</a> p

---
**skip_compose_l_Pre**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (<a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#composition" title=composition>;</a> p) = Pre p

---
**skip_compose_l_post**

&nbsp;&nbsp;&nbsp;&nbsp;post (<a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#composition" title=composition>;</a> p) = post p <a href="#restrict_r" title=restrict_r>/</a> Pre p

---
**skip_compose_l_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#composition" title=composition>;</a> p <a href="#equal" title=equal>=</a> 〈 State = <a href="#S" title=S>S</a> p, Pre = Pre p, post = post p <a href="#restrict_r" title=restrict_r>/</a> Pre p〉

---
**skip_compose3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#composition" title=composition>;</a> p <a href="#equiv" title=equiv>≡</a> p

---
**skip_unsafe_compose_r_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#unsafe_composition" title=unsafe_composition>;</a> p <a href="#equal" title=equal>=</a> 〈State=S p, Pre=S p, post = <a href="#restr_post" title=restr_post>restr_post</a> p 〉

---
**corestriction_prop**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#equiv" title=equiv>≡</a> p <a href="#composition" title=composition>;</a> (<a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#restrict_p" title=restrict_p>/</a> C)

---
**skip_prop**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> C <a href="#choice" title=choice>∪</a> <a href="#Skip" title=Skip>Skip</a> D <a href="#equiv" title=equiv>≡</a> <a href="#Skip" title=Skip>Skip</a> (C ∪ D)

---
**skip_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#restrict_p" title=restrict_p>/</a> C <a href="#composition" title=composition>;</a> p <a href="#equiv" title=equiv>≡</a> p <a href="#restrict_p" title=restrict_p>/</a> C

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> (C) <a href="#composition" title=composition>;</a> p <a href="#equal" title=equal>=</a> p <a href="#restrict_p" title=restrict_p>/</a> C

---
**Skip_comprestrict**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> (C) <a href="#composition" title=composition>;</a> p <a href="#equiv" title=equiv>≡</a> p <a href="#restrict_p" title=restrict_p>/</a> C

---
**skip_prop_4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> D <a href="#restrict_p" title=restrict_p>/</a> C <a href="#equiv" title=equiv>≡</a> <a href="#Skip" title=Skip>Skip</a> (D ∩ C)

---
**skip_prop_5**

&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ <a href="#Skip" title=Skip>Skip</a> D <a href="#restrict_p" title=restrict_p>/</a> C <a href="#equiv" title=equiv>≡</a> <a href="#Skip" title=Skip>Skip</a> C

---
**skip_prop_6**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> p ⊆ C ⟹ <a href="#Skip" title=Skip>Skip</a> C <a href="#composition" title=composition>;</a> p <a href="#equiv" title=equiv>≡</a> p

---
**corestrict_skip**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (C) <a href="#equiv" title=equiv>≡</a> p <a href="#corestrict_p" title=corestrict_p>∖</a> C

---
**skip_prop_8**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> D <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#equiv" title=equiv>≡</a> <a href="#Skip" title=Skip>Skip</a> (D ∩ C)

---
**skip_prop_9**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (<a href="#Skip" title=Skip>Skip</a> (C)) = C

---
**skip_prop_10**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> x <a href="#choice" title=choice>∪</a> <a href="#Skip" title=Skip>Skip</a> y = <a href="#Skip" title=Skip>Skip</a> (x ∪ y)

---
**skip_prop_11**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> {} <a href="#choice" title=choice>∪</a> p <a href="#equiv" title=equiv>≡</a> p

---
**skip_prop_12**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> {} <a href="#choice" title=choice>∪</a> (p <a href="#choice" title=choice>∪</a> q) = p <a href="#choice" title=choice>∪</a> q

---
**skip_prop_13**

&nbsp;&nbsp;&nbsp;&nbsp;(a <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> a ∪ <a href="#S" title=S>S</a> b) ) <a href="#composition" title=composition>;</a> b = a <a href="#composition" title=composition>;</a> b

---
**skip_prop_14**

&nbsp;&nbsp;&nbsp;&nbsp;(a <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> a) ) <a href="#composition" title=composition>;</a> b = a <a href="#composition" title=composition>;</a> b

---
**skip_prop_15**

&nbsp;&nbsp;&nbsp;&nbsp;(a <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> b) ) <a href="#composition" title=composition>;</a> b = a <a href="#composition" title=composition>;</a> b

---
**skip_prop_16**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> a ⊆ C ⟹ post ((a <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> C) <a href="#composition" title=composition>;</a> b) = post (a <a href="#composition" title=composition>;</a> b)

---
**skip_prop_17**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> b ⊆ C ⟹ post ((a <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> C) <a href="#composition" title=composition>;</a> b) = post (a <a href="#composition" title=composition>;</a> b)

---
**skip_prop_18**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> a ⊆ C ⟹  <a href="#Skip" title=Skip>Skip</a> C <a href="#composition" title=composition>;</a> (a <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> C) = (<a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> a) <a href="#composition" title=composition>;</a> a) <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> C

---
## Arbitrary_repetition.thy

**loop_l1**

&nbsp;&nbsp;&nbsp;&nbsp;s=0 ⟹ f=0 ⟹ <a href="#loop" title=loop>loop</a> p s f = <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#restrict_p" title=restrict_p>/</a> (Pre p) 

---
**loop_l2**

&nbsp;&nbsp;&nbsp;&nbsp;s=0 ⟹ f=1 ⟹ <a href="#loop" title=loop>loop</a> p s f = <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#restrict_p" title=restrict_p>/</a> (Pre p) <a href="#choice" title=choice>∪</a>  (<a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#restrict_p" title=restrict_p>/</a> (Pre p) <a href="#composition" title=composition>;</a> p)

---
**loop_l2_01**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#loop" title=loop>loop</a> p (f + 1) f = <a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> p)

---
**loop_l2_02**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#loop" title=loop>loop</a> p 0 f <a href="#composition" title=composition>;</a> p = <a href="#loop" title=loop>loop</a> p (0 + 1) (f + 1)

---
**loop_l2_03**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#loop" title=loop>loop</a> p s s <a href="#composition" title=composition>;</a> p = <a href="#loop" title=loop>loop</a> p (s + 1) (s + 1)

---
**loop_l2_04**

&nbsp;&nbsp;&nbsp;&nbsp;s&lt;f ⟹ <a href="#loop" title=loop>loop</a> p s f <a href="#composition" title=composition>;</a> p = <a href="#loop" title=loop>loop</a> p (s + 1) (f + 1)

---
**loop_l2_05**

&nbsp;&nbsp;&nbsp;&nbsp;0<s ⟹ <a href="#loop" title=loop>loop</a> p s s = p<sup>s</sup> <a href="#choice" title=choice>∪</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**loop_l2_1**

&nbsp;&nbsp;&nbsp;&nbsp;s=f ⟹ <a href="#loop" title=loop>loop</a> p s f <a href="#equiv" title=equiv>≡</a> p<sup>s</sup>

---
**loop_l2_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#loop" title=loop>loop</a> p s (s + 1) = p<sup>s</sup> <a href="#choice" title=choice>∪</a> p<sup>s + 1</sup>

---
**loop_l3**

&nbsp;&nbsp;&nbsp;&nbsp;s&lt;f ⟹ <a href="#loop" title=loop>loop</a> p s (f + 1) <a href="#equiv" title=equiv>≡</a> (p<sup>f + 1</sup>) <a href="#choice" title=choice>∪</a> (<a href="#loop" title=loop>loop</a> p s f)

---
**loop_l4**

&nbsp;&nbsp;&nbsp;&nbsp;s&lt;f ⟹ <a href="#loop" title=loop>loop</a> p s f <a href="#equiv" title=equiv>≡</a> (p<sup>s</sup>) <a href="#choice" title=choice>∪</a> (<a href="#loop" title=loop>loop</a> p (s + 1) f)

---
**loop_l6**

&nbsp;&nbsp;&nbsp;&nbsp;s=0 ⟹ s<f ⟹ <a href="#loop" title=loop>loop</a> p s f <a href="#equiv" title=equiv>≡</a> (<a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#restrict_p" title=restrict_p>/</a> (Pre p)) <a href="#choice" title=choice>∪</a> (<a href="#loop" title=loop>loop</a> p 1 f)

---
&nbsp;&nbsp;&nbsp;&nbsp;0<s ⟹ s<f ⟹ <a href="#loop" title=loop>loop</a> p s f <a href="#equiv" title=equiv>≡</a> p<sup>s</sup> <a href="#choice" title=choice>∪</a> <a href="#loop" title=loop>loop</a> p (s + 1) f

---
**loop_l5**

&nbsp;&nbsp;&nbsp;&nbsp;s&lt;f ⟹ s &lt; k ⟹ k &lt; f ⟹ <a href="#loop" title=loop>loop</a> p s f <a href="#equiv" title=equiv>≡</a> (<a href="#loop" title=loop>loop</a> p s k) <a href="#choice" title=choice>∪</a> (<a href="#loop" title=loop>loop</a> p (k + 1) f)

---
**loop_simplification**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [x,y] ⟹ <a href="#Range_p" title=Range_p>Range_p</a> x ∩ Pre y = {} ⟹ <a href="#Range_p" title=Range_p>Range_p</a> y ∩ Pre x = {} ⟹ (<a href="#loop" title=loop>loop</a> x s f) <a href="#choice" title=choice>∪</a> (<a href="#loop" title=loop>loop</a> y s f) <a href="#equiv" title=equiv>≡</a> <a href="#loop" title=loop>loop</a> (x <a href="#choice" title=choice>∪</a> y) s f

---
**equiv_is_maintained_by_arbitrary_repetition_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p<sub>1</sub>, p<sub>2</sub>] ⟹ p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub> ⟹ <a href="#S" title=S>S</a> p<sub>1</sub> = <a href="#S" title=S>S</a> p<sub>2</sub> ⟹ <a href="#loop" title=loop>loop</a> p<sub>1</sub> s f <a href="#equiv" title=equiv>≡</a> <a href="#loop" title=loop>loop</a> p<sub>2</sub> s f

---
**equiv_is_maintained_by_arbitrary_repetition_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p<sub>1</sub>, p<sub>2</sub>] ⟹ p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub> ⟹ 0<s ⟹ <a href="#loop" title=loop>loop</a> p<sub>1</sub> s f <a href="#equiv" title=equiv>≡</a> <a href="#loop" title=loop>loop</a> p<sub>2</sub> s f

---
**arbitrary_rep_feasibility_l1**

&nbsp;&nbsp;&nbsp;&nbsp;s > f ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#loop" title=loop>loop</a> p s f)

---
**arbitrary_rep_feasibility_l2**

&nbsp;&nbsp;&nbsp;&nbsp;s &lt; f ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#loop" title=loop>loop</a> p s f)

---
**arbitrary_rep_feasibility**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#loop" title=loop>loop</a> p s f)

---
**skip_compose_l_of_loop_1**

&nbsp;&nbsp;&nbsp;&nbsp;s &lt; f ⟹ s=0 ⟹ <a href="#loop" title=loop>loop</a> p s f <a href="#equiv" title=equiv>≡</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#restrict_p" title=restrict_p>/</a> (Pre p) <a href="#choice" title=choice>∪</a> <a href="#loop" title=loop>loop</a> p s f

---
**skip_compose_r_of_loop_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#loop" title=loop>loop</a> p s f <a href="#equiv" title=equiv>≡</a> <a href="#loop" title=loop>loop</a> p s f <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p)

---
**skip_compose_l_of_loop_3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#loop" title=loop>loop</a> p s f <a href="#equiv" title=equiv>≡</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#composition" title=composition>;</a> <a href="#loop" title=loop>loop</a> p s f

---
**range_fixed_rep**

&nbsp;&nbsp;&nbsp;&nbsp;s&lt;m ⟹ m&lt;f ⟹ x ∉ <a href="#Range_p" title=Range_p>Range_p</a> (<a href="#loop" title=loop>loop</a> p s f) ⟹ x ∉ <a href="#Range_p" title=Range_p>Range_p</a> (p<sup>m</sup>)

---
**pre_is_known_arbitrary_rep_1**

&nbsp;&nbsp;&nbsp;&nbsp;∀x y. x ∈ Pre a ∧ (x, y) ∈ post (a <a href="#composition" title=composition>;</a> (b <a href="#restrict_p" title=restrict_p>/</a> (- C))<sup>n</sup>) → x ∈ Pre (a <a href="#composition" title=composition>;</a> (b <a href="#restrict_p" title=restrict_p>/</a> (- C))<sup>n</sup>)

---
**pre_is_known_arbitrary_rep_2**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ Pre a ⟹ (x, y) ∈ post (a <a href="#composition" title=composition>;</a> (b <a href="#restrict_p" title=restrict_p>/</a> (- C))<sup>n</sup>) ⟹ x ∈ Pre (a <a href="#composition" title=composition>;</a> (b <a href="#restrict_p" title=restrict_p>/</a> (- C))<sup>n</sup>)

---
**bad_index_is_fail_arbitrary**

&nbsp;&nbsp;&nbsp;&nbsp;f<s ⟹ <a href="#loop" title=loop>loop</a> a s f <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**fail_stays_fail_arbitrary**

&nbsp;&nbsp;&nbsp;&nbsp;s&lt;f ⟹ <a href="#loop" title=loop>loop</a> p s f <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {} ⟹ <a href="#loop" title=loop>loop</a> p s (f + 1) <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**fail_stays_fail_arbitrary_2**

&nbsp;&nbsp;&nbsp;&nbsp;s&lt;f ⟹ <a href="#loop" title=loop>loop</a> p s (f + 1) <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {} ⟹ <a href="#loop" title=loop>loop</a> p s f <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**fail_stays_fail_arbitrary_3**

&nbsp;&nbsp;&nbsp;&nbsp;s&lt;f ⟹ <a href="#loop" title=loop>loop</a> p s (f + 1) <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {} ≡ <a href="#loop" title=loop>loop</a> p s f <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**fail_stays_fail_arbitrary_4**

&nbsp;&nbsp;&nbsp;&nbsp;s&lt;f ⟹ <a href="#loop" title=loop>loop</a> p s s <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {} ≡ <a href="#loop" title=loop>loop</a> p s f <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**fail_arbitrary_implies_fixed**

&nbsp;&nbsp;&nbsp;&nbsp;k &lt; n ⟹ <a href="#loop" title=loop>loop</a> (b <a href="#restrict_p" title=restrict_p>/</a> (- C)) 0 n <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {} ⟹ (b <a href="#restrict_p" title=restrict_p>/</a> (- C)) <a href="#fixed_repetition" title=fixed_repetition><sup><</sup>/a> k <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**extract_fixed_from_arbitrary**

&nbsp;&nbsp;&nbsp;&nbsp;k&lt;n ⟹ a <a href="#composition" title=composition>;</a> <a href="#loop" title=loop>loop</a> (b <a href="#restrict_p" title=restrict_p>/</a> (- C)) 0 n <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#equiv" title=equiv>≡</a> a <a href="#composition" title=composition>;</a> <a href="#loop" title=loop>loop</a> (b <a href="#restrict_p" title=restrict_p>/</a> (- C)) 0 n <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#choice" title=choice>∪</a> a <a href="#composition" title=composition>;</a> ((b <a href="#restrict_p" title=restrict_p>/</a> (- C)) <a href="#fixed_repetition" title=fixed_repetition><sup><</sup>/a> k) <a href="#corestrict_p" title=corestrict_p>∖</a> C

---
**fail_arbitrary_implies_fixed_2**

&nbsp;&nbsp;&nbsp;&nbsp;k &lt; n ⟹ a <a href="#composition" title=composition>;</a> <a href="#loop" title=loop>loop</a> (b <a href="#restrict_p" title=restrict_p>/</a> (- C)) 0 n <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {} ⟹ a <a href="#composition" title=composition>;</a> ((b <a href="#restrict_p" title=restrict_p>/</a> (- C)) <a href="#fixed_repetition" title=fixed_repetition><sup><</sup>/a> k) <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> x) <a href="#choice" title=choice>∪</a> x <a href="#fixed_repetition" title=fixed_repetition><sup><</sup>/a> 0 = x <a href="#fixed_repetition" title=fixed_repetition><sup><</sup>/a> 0

---
**fixed_prop**

&nbsp;&nbsp;&nbsp;&nbsp;0<f ⟹ <a href="#Fail" title=Fail>Fail</a> (<a href="#S" title=S>S</a> x) <a href="#choice" title=choice>∪</a> x <a href="#fixed_repetition" title=fixed_repetition><sup><</sup>/a> f = x <a href="#fixed_repetition" title=fixed_repetition><sup><</sup>/a> f

---
**loop_choice3**

&nbsp;&nbsp;&nbsp;&nbsp;0<s ⟹ 0<f ⟹ <a href="#all_feasible" title=all_feasible>all_feasible</a> [x,y] ⟹ <a href="#Range_p" title=Range_p>Range_p</a> x ∩ Pre y = {} ⟹ <a href="#Range_p" title=Range_p>Range_p</a> y ∩ Pre x = {} ⟹ (<a href="#loop" title=loop>loop</a> x s f) <a href="#choice" title=choice>∪</a> (<a href="#loop" title=loop>loop</a> y s f) = <a href="#loop" title=loop>loop</a> (x <a href="#choice" title=choice>∪</a> y) s f

---
**Loop_fail**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#loop" title=loop>loop</a> p 0 n <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {} ⟹ <a href="#loop" title=loop>loop</a> p 0 m <a href="#equiv" title=equiv>≡</a> Fail{}

---
## Atomic_concurrency.thy

&nbsp;&nbsp;&nbsp;&nbsp;foldl (f::'a Program ⇒ 'a Program ⇒ 'a Program) (f a x) xs = f a (foldl f x xs)

---
**complete_state_subset_fold_composition**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ <a href="#complete_state" title=complete_state>complete_state</a> xs ⟹ x ∈ <a href="#S" title=S>S</a> (foldl (<a href="#composition" title=composition>;</a>) (<a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> xs)) xs)

---
**fold_choice_inv_1**

&nbsp;&nbsp;&nbsp;&nbsp;foldl (<a href="#choice" title=choice>∪</a>) (<a href="#Fail" title=Fail>Fail</a> {}) (a # xs)  = a <a href="#choice" title=choice>∪</a> foldl (<a href="#choice" title=choice>∪</a>) (<a href="#Fail" title=Fail>Fail</a> {}) (xs) 

---
**fold_choice_inv_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (foldl (<a href="#choice" title=choice>∪</a>) (<a href="#Fail" title=Fail>Fail</a> {}) xs ) = ⋃ (set (map (<a href="#S" title=S>S</a>) xs))

---
**conc_elems_state**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (<a href="#conc_elems" title=conc_elems>conc_elems</a> xs) ⟹ <a href="#S" title=S>S</a> x = <a href="#complete_state" title=complete_state>complete_state</a> xs

---
**atomic_conc_complete_state**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (<a href="#atomic_conc" title=atomic_conc>atomic_conc</a> xs) = <a href="#complete_state" title=complete_state>complete_state</a> xs

---
**atomic_conc_equivalence**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ <a href="#S" title=S>S</a> (<a href="#Concat" title=Concat>Concat</a> xs C) = <a href="#S" title=S>S</a> (<a href="#atomic_conc" title=atomic_conc>atomic_conc</a> xs)

---
**pre_zero**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (<a href="#atomic_conc" title=atomic_conc>atomic_conc</a> [ ]) = {}

---
**pre_one**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> x ⟹ Pre (<a href="#atomic_conc" title=atomic_conc>atomic_conc</a> [x]) = Pre x

---
**lemma_pre_1**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (<a href="#atomic_conc" title=atomic_conc>atomic_conc</a> (a#[b])) ⊆ Pre a ∪ Pre b

---
**list_equiv_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#list_equiv" title=list_equiv>list_equiv</a> xs xs

---
**list_equiv_comp_equiv**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#list_equiv" title=list_equiv>list_equiv</a> xs ys ⟹ b <a href="#equiv" title=equiv>≡</a> b' ⟹ fold (<a href="#composition" title=composition>;</a>) xs b <a href="#equiv" title=equiv>≡</a> fold (<a href="#composition" title=composition>;</a>) ys b'

---
**skip_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> a ⟹ <a href="#S" title=S>S</a> a ⊆ C ⟹ a <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> C <a href="#equiv" title=equiv>≡</a> a

---
**skip_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> a ⟹a <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> (a # xs)) <a href="#equiv" title=equiv>≡</a> a

---
**skip_restrict**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> a ⟹ fold (<a href="#composition" title=composition>;</a>) xs (a <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> (a # xs))) <a href="#equiv" title=equiv>≡</a> fold (<a href="#composition" title=composition>;</a>) xs a

---
**feas_of_prop**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#feas_of" title=feas_of>feas_of</a> p)

---
**feas_of_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#feas_of" title=feas_of>feas_of</a> p <a href="#equal" title=equal>=</a> p

---
**skip_prop_4**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> a) <a href="#equiv" title=equiv>≡</a> <a href="#feas_of" title=feas_of>feas_of</a> a

---
**skip_prop_5**

&nbsp;&nbsp;&nbsp;&nbsp;fold (<a href="#composition" title=composition>;</a>) xs (<a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> (a # xs)) <a href="#composition" title=composition>;</a> a) <a href="#equiv" title=equiv>≡</a> fold (<a href="#composition" title=composition>;</a>) xs a

---
**get_trace**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ x ∈ set (<a href="#conc_elems" title=conc_elems>conc_elems</a> xs) ⟹ ∃tr. tr ∈ set (<a href="#permutations" title=permutations>permutations</a> xs) ∧ x = <a href="#Concat" title=Concat>Concat</a> tr C

---
**skip_prop_6**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p ∪ x) <a href="#composition" title=composition>;</a> p <a href="#equiv" title=equiv>≡</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#composition" title=composition>;</a> p

---
**no_right_neutral**

&nbsp;&nbsp;&nbsp;&nbsp;∃t. p <a href="#composition" title=composition>;</a> t <a href="#equiv" title=equiv>≡</a> p

---
**corestrict_skip**

&nbsp;&nbsp;&nbsp;&nbsp;(a <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> a ∪ <a href="#S" title=S>S</a> b)) <a href="#composition" title=composition>;</a> b <a href="#equiv" title=equiv>≡</a> a <a href="#composition" title=composition>;</a> b

---
**skip_prop_8**

&nbsp;&nbsp;&nbsp;&nbsp;(a <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> a)) <a href="#composition" title=composition>;</a> b <a href="#equiv" title=equiv>≡</a> a <a href="#composition" title=composition>;</a> b

---
**skip_prop_9**

&nbsp;&nbsp;&nbsp;&nbsp;(a <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> b)) <a href="#composition" title=composition>;</a> b <a href="#equiv" title=equiv>≡</a> a <a href="#composition" title=composition>;</a> b

---
**fold_decomp**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ (foldl (<a href="#composition" title=composition>;</a>) (a) (xs)) <a href="#equiv" title=equiv>≡</a> a <a href="#composition" title=composition>;</a> (foldl (<a href="#composition" title=composition>;</a>) (<a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> xs)) (xs))

---
**fold_decomp2**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ (foldl (<a href="#composition" title=composition>;</a>) (a) (xs)) <a href="#equiv" title=equiv>≡</a> a <a href="#composition" title=composition>;</a> (foldl (<a href="#composition" title=composition>;</a>) (<a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> a)) (xs))

---
**fold_equiv_maintained**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#equiv" title=equiv>≡</a> b ⟹ foldl (<a href="#composition" title=composition>;</a>) a xs <a href="#equiv" title=equiv>≡</a> foldl (<a href="#composition" title=composition>;</a>) b xs

---
**fold_compress_1**

&nbsp;&nbsp;&nbsp;&nbsp;ys ≠ [ ] ⟹ ∃e'. (a) <a href="#composition" title=composition>;</a> e' <a href="#equiv" title=equiv>≡</a> (foldl (<a href="#composition" title=composition>;</a>) (<a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> ([a]@ys))) ([a]@ys))

---
**fold_compress_2**

&nbsp;&nbsp;&nbsp;&nbsp;∃e'. e' <a href="#composition" title=composition>;</a> a <a href="#equiv" title=equiv>≡</a> (foldl (<a href="#composition" title=composition>;</a>) (<a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> (ys@[a]))) (ys@[a]))

---
**fold_compress_3**

&nbsp;&nbsp;&nbsp;&nbsp;∃s' e'. (s' <a href="#composition" title=composition>;</a> a) <a href="#composition" title=composition>;</a> e' <a href="#equiv" title=equiv>≡</a> (foldl (<a href="#composition" title=composition>;</a>) (<a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> (xs@[a]@ys))) (xs@[a]@ys)) ∨ s' <a href="#composition" title=composition>;</a> a=(foldl (<a href="#composition" title=composition>;</a>) (<a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> (xs@[a]@ys))) (xs@[a]@ys))

---
**conc_elems_dec**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (<a href="#conc_elems" title=conc_elems>conc_elems</a> (a # xs)) ⟹ ∃s' e'. (s' <a href="#composition" title=composition>;</a> a) <a href="#composition" title=composition>;</a> e' = x ∨ s' <a href="#composition" title=composition>;</a> a=x ∨ a = x∨ a <a href="#composition" title=composition>;</a> e' = x

---
**concat_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ tr ∈ set (<a href="#permutations" title=permutations>permutations</a> xs) ⟹ <a href="#Concat" title=Concat>Concat</a> tr (<a href="#complete_state" title=complete_state>complete_state</a> xs) ∈ set (<a href="#conc_elems" title=conc_elems>conc_elems</a> xs)

---
**fold_choice_inv**

&nbsp;&nbsp;&nbsp;&nbsp;t ∈ set (xs) ⟹ foldl (<a href="#choice" title=choice>∪</a>) (x) (xs) = t <a href="#choice" title=choice>∪</a> (foldl (<a href="#choice" title=choice>∪</a>) (x) (xs))

---
**atomic_conc_inv**

&nbsp;&nbsp;&nbsp;&nbsp;tr ∈ set (<a href="#conc_elems" title=conc_elems>conc_elems</a> xs) ⟹ tr <a href="#choice" title=choice>∪</a> <a href="#atomic_conc" title=atomic_conc>atomic_conc</a> xs <a href="#equiv" title=equiv>≡</a> <a href="#atomic_conc" title=atomic_conc>atomic_conc</a> xs

---
**atomic_conc_inv2**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (<a href="#conc_elems" title=conc_elems>conc_elems</a> xs) ⟹ x <a href="#specialize" title=specialize>⊆</a> <a href="#atomic_conc" title=atomic_conc>atomic_conc</a> xs

---
**atomic_conc_inv3**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ <a href="#Concat" title=Concat>Concat</a> xs (<a href="#complete_state" title=complete_state>complete_state</a> xs) <a href="#specialize" title=specialize>⊆</a> <a href="#atomic_conc" title=atomic_conc>atomic_conc</a> xs

---
**perm_prop**

&nbsp;&nbsp;&nbsp;&nbsp;set (<a href="#permutations" title=permutations>permutations</a> (a@b)) = set (<a href="#permutations" title=permutations>permutations</a> (b@a))

---
**perm_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (<a href="#permutations" title=permutations>permutations</a> y) ⟹ set (<a href="#conc_elems" title=conc_elems>conc_elems</a> (y)) = set (<a href="#conc_elems" title=conc_elems>conc_elems</a> (x))

---
**perm_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;set (<a href="#conc_elems" title=conc_elems>conc_elems</a> (a@b)) = set (<a href="#conc_elems" title=conc_elems>conc_elems</a> (b@a))

---
**perm_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;size (<a href="#insert_all" title=insert_all>insert_all</a> x xs) = size xs + 1

---
**perm_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;size (concat [ ]) = 0 

---
**perm_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;size (concat (x#xs)) = size x + size (concat (xs))

---
**perm_prop7**

&nbsp;&nbsp;&nbsp;&nbsp;size (concat xs) = foldl (λa b. a + (size b)) 0 xs

---
**perm_prop8**

&nbsp;&nbsp;&nbsp;&nbsp;a ∈ set (map (<a href="#insert_all" title=insert_all>insert_all</a> x) (<a href="#permutations" title=permutations>permutations</a> xs)) ⟹ b ∈ set a ⟹ size b = size xs + 1

---
**perm_prop9**

&nbsp;&nbsp;&nbsp;&nbsp;a ∈ set (map (<a href="#insert_all" title=insert_all>insert_all</a> x) (<a href="#permutations" title=permutations>permutations</a> xs)) ⟹ size a = size xs + 1

---
**size_concat**

&nbsp;&nbsp;&nbsp;&nbsp;size (concat xss) = sum_list (map size xss)

---
**insert_all_prop**

&nbsp;&nbsp;&nbsp;&nbsp;size (concat (map (<a href="#insert_all" title=insert_all>insert_all</a> x) xss)) = sum_list (map (λy. Suc (size y)) xss)

---
&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (<a href="#permutations" title=permutations>permutations</a> xs) ⟹ y ∈ set (<a href="#permutations" title=permutations>permutations</a> xs) ⟹ size x = size y

---
**sum_list_simp**

&nbsp;&nbsp;&nbsp;&nbsp;(∀x ∈ set xss. ∀ y ∈ set xss. size x = size y) ⟹ sum_list (map size xss) = size xss * size (hd xss)

---
**size_lemma**

&nbsp;&nbsp;&nbsp;&nbsp;∀x ∈ set xs. size x = n ⟹ size (concat xs) = size xs * n

---
**length_concat_insert_all**

&nbsp;&nbsp;&nbsp;&nbsp;length (concat (map (<a href="#insert_all" title=insert_all>insert_all</a> x) (<a href="#permutations" title=permutations>permutations</a> xs))) = (length xs + 1) * length (<a href="#permutations" title=permutations>permutations</a> xs)

---
**size_permutations_fact**

&nbsp;&nbsp;&nbsp;&nbsp;length (<a href="#permutations" title=permutations>permutations</a> xs) = fact (length xs)

---
**perm_size_eq**

&nbsp;&nbsp;&nbsp;&nbsp;size xs = size ys ⟹ size (<a href="#permutations" title=permutations>permutations</a> xs) = size (<a href="#permutations" title=permutations>permutations</a> ys)

---
**perm_prop10**

&nbsp;&nbsp;&nbsp;&nbsp;size (<a href="#permutations" title=permutations>permutations</a> (x#xs)) = size (<a href="#permutations" title=permutations>permutations</a> (xs)) * size (x#xs)

---
**fold_choice_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#permutations" title=permutations>permutations</a> a = <a href="#permutations" title=permutations>permutations</a> b ⟹ set (<a href="#conc_elems" title=conc_elems>conc_elems</a> a) = set (<a href="#conc_elems" title=conc_elems>conc_elems</a> b)

---
&nbsp;&nbsp;&nbsp;&nbsp;size xs > 0⟹ size (<a href="#conc_elems" title=conc_elems>conc_elems</a> xs) > 0

---
**fold_choice_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;a ∈ set xs ⟹ foldl (<a href="#choice" title=choice>∪</a>) a xs = foldl (<a href="#choice" title=choice>∪</a>) (<a href="#Skip" title=Skip>Skip</a> {}) xs

---
**fold_choice_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;a ∈ set (<a href="#conc_elems" title=conc_elems>conc_elems</a> (xs)) ⟹ foldl (<a href="#choice" title=choice>∪</a>) (a) (<a href="#conc_elems" title=conc_elems>conc_elems</a> (xs)) = foldl (<a href="#choice" title=choice>∪</a>) (<a href="#Skip" title=Skip>Skip</a> {}) (<a href="#conc_elems" title=conc_elems>conc_elems</a> (xs))

---
**fold_choice_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;foldl (<a href="#choice" title=choice>∪</a>) x (x'#xs) = foldl (<a href="#choice" title=choice>∪</a>) (<a href="#Fail" title=Fail>Fail</a> {}) (x#x'#xs)

---
**atomic_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ ys ∈ set (<a href="#permutations" title=permutations>permutations</a> xs) ⟹ <a href="#Concat" title=Concat>Concat</a> ys (<a href="#complete_state" title=complete_state>complete_state</a> xs) <a href="#specialize" title=specialize>⊆</a> <a href="#atomic_conc" title=atomic_conc>atomic_conc</a> xs

---
**atomic_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#atomic_conc" title=atomic_conc>atomic_conc</a> [a,b] <a href="#equiv" title=equiv>≡</a> a <a href="#composition" title=composition>;</a> b <a href="#choice" title=choice>∪</a> b <a href="#composition" title=composition>;</a> a

---
**equiv_to_equal**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> a = <a href="#S" title=S>S</a> b ⟹ post a = post b ⟹ a <a href="#equiv" title=equiv>≡</a> b ⟹ a <a href="#equal" title=equal>=</a> b

---
**atomic_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#atomic_conc" title=atomic_conc>atomic_conc</a> [a, b <a href="#choice" title=choice>∪</a> c] <a href="#equiv" title=equiv>≡</a> <a href="#atomic_conc" title=atomic_conc>atomic_conc</a> [a,b] <a href="#choice" title=choice>∪</a> <a href="#atomic_conc" title=atomic_conc>atomic_conc</a> [a,c]

---
**atomic_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#atomic_conc" title=atomic_conc>atomic_conc</a> [a <a href="#choice" title=choice>∪</a> b] = <a href="#atomic_conc" title=atomic_conc>atomic_conc</a> [a] <a href="#choice" title=choice>∪</a> <a href="#atomic_conc" title=atomic_conc>atomic_conc</a> [b]

---
**set_to_list_set**

&nbsp;&nbsp;&nbsp;&nbsp;finite xs ⟹ set (<a href="#set_to_list" title=set_to_list>set_to_list</a> xs) = xs

---
**specialize_prop**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#equal" title=equal>=</a> b ⟹ b <a href="#specialize" title=specialize>⊆</a> a ∧ a <a href="#specialize" title=specialize>⊆</a> b

---
**atomic_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#atomic_conc" title=atomic_conc>atomic_conc</a> [a <a href="#choice" title=choice>∪</a> b, c] <a href="#equiv" title=equiv>≡</a> <a href="#atomic_conc" title=atomic_conc>atomic_conc</a> [a,c] <a href="#choice" title=choice>∪</a> <a href="#atomic_conc" title=atomic_conc>atomic_conc</a> [b,c]

---
**commute_compose**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#commute_programs3" title=commute_programs3>commute_programs3</a> a b ⟹ <a href="#atomic_conc" title=atomic_conc>atomic_conc</a> [a,b] <a href="#equiv" title=equiv>≡</a> a <a href="#composition" title=composition>;</a> b

---
## Big_choice.thy

**fold_compose**

&nbsp;&nbsp;&nbsp;&nbsp;foldl (<a href="#composition" title=composition>;</a>) (a <a href="#composition" title=composition>;</a> b) xs = a <a href="#composition" title=composition>;</a> (foldl (<a href="#composition" title=composition>;</a>) b xs)

---
**fold_choice**

&nbsp;&nbsp;&nbsp;&nbsp;foldl (<a href="#choice" title=choice>∪</a>) (a <a href="#choice" title=choice>∪</a> b) xs = a <a href="#choice" title=choice>∪</a> (foldl (<a href="#choice" title=choice>∪</a>) b xs)

---
**Choice_prop_1_2**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ <a href="#Choice" title=Choice>⋃</a> (x#xs) = x <a href="#choice" title=choice>∪</a> <a href="#Choice" title=Choice>⋃</a> xs

---
**Choice_prop_1_3**

&nbsp;&nbsp;&nbsp;&nbsp;a@b ≠ [ ] ⟹ <a href="#Choice" title=Choice>⋃</a> (a@x#b) = x <a href="#choice" title=choice>∪</a> <a href="#Choice" title=Choice>⋃</a> (a@b)

---
**Choice_prop_1_1**

&nbsp;&nbsp;&nbsp;&nbsp;ys ∈ set (<a href="#permutations" title=permutations>permutations</a> xs) ⟹ <a href="#Choice" title=Choice>⋃</a> xs = <a href="#Choice" title=Choice>⋃</a> ys

---
**Choice_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ <a href="#Choice" title=Choice>⋃</a> (xs@[x]) = x <a href="#choice" title=choice>∪</a> <a href="#Choice" title=Choice>⋃</a> xs

---
**Choice_prop_1_4**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ foldl (<a href="#choice" title=choice>∪</a>) x xs = x <a href="#choice" title=choice>∪</a> <a href="#Choice" title=Choice>Choice</a> xs

---
**Choice_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Choice" title=Choice>⋃</a> [a <a href="#composition" title=composition>;</a> t. t ← xs] <a href="#equiv" title=equiv>≡</a> a ;⋃ [t. t ← xs]

---
**Choice_prop_3**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ <a href="#Choice" title=Choice>⋃</a> (xs@[x]) = <a href="#Choice" title=Choice>⋃</a> (xs) <a href="#choice" title=choice>∪</a> x

---
**Choice_prop_4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Choice" title=Choice>⋃</a> [t <a href="#composition" title=composition>;</a> a. t ← xs] <a href="#equiv" title=equiv>≡</a> <a href="#Choice" title=Choice>⋃</a> [t. t ← xs] <a href="#composition" title=composition>;</a> a

---
**Choice_state**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (<a href="#Choice" title=Choice>⋃</a> (xs)) = ⋃ {S x | x . x ∈ set xs}

---
**Union_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ {} ⟹ ⋃ {t | x . x ∈ xs} = t

---
**Choice_prop_5**

&nbsp;&nbsp;&nbsp;&nbsp;size xs = 1 ⟹ set (xs) = {x} ⟹ (<a href="#Choice" title=Choice>⋃</a> xs = x)

---
**Choice_prop_6**

&nbsp;&nbsp;&nbsp;&nbsp;size xs > 1 ⟹ set (xs) = {x} ⟹ (<a href="#Choice" title=Choice>⋃</a> xs = x <a href="#choice" title=choice>∪</a> x)

---
**Choice_prop_7**

&nbsp;&nbsp;&nbsp;&nbsp;a ≠ [ ] ⟹ b ≠ [ ] ⟹ <a href="#Choice" title=Choice>⋃</a> a <a href="#choice" title=choice>∪</a> <a href="#Choice" title=Choice>⋃</a> b = <a href="#Choice" title=Choice>⋃</a> (a@b)

---
**Choice_prop_8**

&nbsp;&nbsp;&nbsp;&nbsp;∃x ∈ set xs. p x ⟹ ∃x ∈ set xs. ¬ p x ⟹ <a href="#Choice" title=Choice>⋃</a> (filter (λx. p x) xs) <a href="#choice" title=choice>∪</a> <a href="#Choice" title=Choice>⋃</a> (filter (λx. ¬ p x) xs) = <a href="#Choice" title=Choice>⋃</a> xs

---
**Choice_prop_9**

&nbsp;&nbsp;&nbsp;&nbsp;size xs>1 ⟹ size ys>1 ⟹ set xs = set ys ⟹ <a href="#Choice" title=Choice>⋃</a> (xs) = <a href="#Choice" title=Choice>⋃</a> (ys)

---
**Choice_prop_10**

&nbsp;&nbsp;&nbsp;&nbsp;size xs=1 ⟹ size ys=1 ⟹ set xs = set ys ⟹ <a href="#Choice" title=Choice>⋃</a> (xs) = <a href="#Choice" title=Choice>⋃</a> (ys)

---
**Choice_prop11**

&nbsp;&nbsp;&nbsp;&nbsp;size xs > 1 ⟹ <a href="#Choice" title=Choice>⋃</a> (filter (λt. P t) xs) <a href="#choice" title=choice>∪</a> <a href="#Choice" title=Choice>⋃</a> (filter (λt. ¬ P t) xs) = <a href="#Choice" title=Choice>⋃</a> xs

---
**Choice_prop12**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set xs ⟹ <a href="#Choice" title=Choice>⋃</a> (filter ((=) x) (x#xs)) = x <a href="#choice" title=choice>∪</a> x

---
**Choice_state_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_state" title=complete_state>complete_state</a> xs = <a href="#S" title=S>S</a> (<a href="#Choice" title=Choice>Choice</a> xs)

---
**Concat_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ foldl (<a href="#composition" title=composition>;</a>) x xs = x <a href="#composition" title=composition>;</a> <a href="#Concat" title=Concat>Concat</a> xs s

---
**Concat_state**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ <a href="#complete_state" title=complete_state>complete_state</a> xs = <a href="#S" title=S>S</a> (<a href="#Concat" title=Concat>Concat</a> xs s)

---
**Choice_prop_13**

&nbsp;&nbsp;&nbsp;&nbsp;size xs > 0 ⟹ <a href="#Choice" title=Choice>⋃</a> [a <a href="#composition" title=composition>;</a> (<a href="#Concat" title=Concat>Concat</a> t s). t ← xs] <a href="#equiv" title=equiv>≡</a> a ;⋃ [(<a href="#Concat" title=Concat>Concat</a> t s). t ← xs]

---
**Choice_prop_14**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Choice" title=Choice>⋃</a> [t <a href="#restrict_p" title=restrict_p>/</a> C . t ← xs] <a href="#equiv" title=equiv>≡</a> <a href="#Choice" title=Choice>⋃</a> [t . t ← xs]/ C

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Choice" title=Choice>⋃</a> [t <a href="#restrict_p" title=restrict_p>/</a> C . t ← xs] = <a href="#Choice" title=Choice>⋃</a> [t . t ← xs]/ C

---
**Choice_prop_15**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Choice" title=Choice>⋃</a> [t <a href="#corestrict_p" title=corestrict_p>∖</a> C . t ← xs] = <a href="#Choice" title=Choice>⋃</a> [t . t ← xs]∖ C

---
**Concat_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ <a href="#Concat" title=Concat>Concat</a> (xs@[x]) s = <a href="#Concat" title=Concat>Concat</a> xs s <a href="#composition" title=composition>;</a> x

---
**Concat_prop_3**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ <a href="#Concat" title=Concat>Concat</a> xs s <a href="#restrict_p" title=restrict_p>/</a> C <a href="#equiv" title=equiv>≡</a> <a href="#Concat" title=Concat>Concat</a> (hd xs <a href="#restrict_p" title=restrict_p>/</a> C # tl xs) s

---
**Concat_prop_4**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ <a href="#Concat" title=Concat>Concat</a> xs s <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#equiv" title=equiv>≡</a> <a href="#Concat" title=Concat>Concat</a> (butlast xs @ [(last xs)∖ C]) s

---
**Choice_prop_16**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set xs ⟹ <a href="#Choice" title=Choice>⋃</a> xs <a href="#equiv" title=equiv>≡</a> <a href="#Choice" title=Choice>⋃</a> xs <a href="#choice" title=choice>∪</a> x

---
**Choice_prop_17**

&nbsp;&nbsp;&nbsp;&nbsp;size xs > 1 ⟹ x ∈ set xs ⟹ <a href="#Choice" title=Choice>⋃</a> xs = <a href="#Choice" title=Choice>⋃</a> xs <a href="#choice" title=choice>∪</a> x

---
**Concat_prop_5**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ ys ≠ [ ] ⟹ <a href="#Concat" title=Concat>Concat</a> (xs@ys) s = <a href="#Concat" title=Concat>Concat</a> xs s <a href="#composition" title=composition>;</a> <a href="#Concat" title=Concat>Concat</a> ys s

---
**Concat_prop_6**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Concat" title=Concat>Concat</a> (a <a href="#choice" title=choice>∪</a> b # xs) s = <a href="#Concat" title=Concat>Concat</a> (a # xs) s <a href="#choice" title=choice>∪</a> <a href="#Concat" title=Concat>Concat</a> (b # xs) s

---
**Concat_prop_7**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Concat" title=Concat>Concat</a> (xs@[a <a href="#choice" title=choice>∪</a> b]) s <a href="#equiv" title=equiv>≡</a> <a href="#Concat" title=Concat>Concat</a> (xs@[a]) s <a href="#choice" title=choice>∪</a> <a href="#Concat" title=Concat>Concat</a> (xs@[b]) s

---
**Concat_prop_8**

&nbsp;&nbsp;&nbsp;&nbsp;e ≠ [ ] ⟹ <a href="#Concat" title=Concat>Concat</a> (s@(a <a href="#choice" title=choice>∪</a> b)#e) s' <a href="#equiv" title=equiv>≡</a> <a href="#Concat" title=Concat>Concat</a> (s@a#e) s' <a href="#choice" title=choice>∪</a> <a href="#Concat" title=Concat>Concat</a> (s@b#e) s'

---
**Choice_prop_18**

&nbsp;&nbsp;&nbsp;&nbsp;size b > 1 ⟹ <a href="#Choice" title=Choice>⋃</a> b = <a href="#Choice" title=Choice>⋃</a> b <a href="#choice" title=choice>∪</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**Choice_prop_19**

&nbsp;&nbsp;&nbsp;&nbsp;size (a@b) > 1 ⟹ <a href="#Choice" title=Choice>⋃</a> a <a href="#choice" title=choice>∪</a> <a href="#Choice" title=Choice>⋃</a> b = <a href="#Choice" title=Choice>⋃</a> (a@b)

---
**Choice_prop_20**

&nbsp;&nbsp;&nbsp;&nbsp;size (a@b) > 0 ⟹ <a href="#Choice" title=Choice>⋃</a> a <a href="#choice" title=choice>∪</a> (x <a href="#choice" title=choice>∪</a> <a href="#Choice" title=Choice>⋃</a> b) = <a href="#Choice" title=Choice>⋃</a> (a@x#b)

---
**Choice_prop_21**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> x ⊆ <a href="#complete_state" title=complete_state>complete_state</a> (a@b) ⟹ <a href="#Choice" title=Choice>⋃</a> a <a href="#choice" title=choice>∪</a> (x <a href="#restrict_p" title=restrict_p>/</a> <a href="#FALSE" title=FALSE>FALSE</a> <a href="#choice" title=choice>∪</a> <a href="#Choice" title=Choice>⋃</a> b) = <a href="#Choice" title=Choice>⋃</a> a <a href="#choice" title=choice>∪</a> (<a href="#Fail" title=Fail>Fail</a> {} <a href="#choice" title=choice>∪</a> <a href="#Choice" title=Choice>⋃</a> b)

---
**list_prop**

&nbsp;&nbsp;&nbsp;&nbsp;1 &lt; i ⟹ i &lt; n ⟹ [p . t ← [1 .. int n]] = [p . t ← [1 .. int i]] @ [p . t ← [int (i + 1) .. int n]]

---
**list_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;[p . t ← [1 .. int (n + 1)]] = [p . t ← [1 .. int n]]@[p]

---
**list_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;size x = size y ⟹ [p. t ← x] = [p. t ← y]

---
**list_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;[p . t ← [1 .. int (n + 1)]] = p#[p . t ← [1 .. int n]]

---
**Concat_prop_9**

&nbsp;&nbsp;&nbsp;&nbsp;0<n ⟹ <a href="#Concat" title=Concat>Concat</a> [p . t ← [1 .. int n]] s <a href="#composition" title=composition>;</a> p = <a href="#Concat" title=Concat>Concat</a> [p . t ← [1 .. int (n + 1)]] s

---
**Concat_prop_10**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ <a href="#Concat" title=Concat>Concat</a> (x#xs) s = x <a href="#composition" title=composition>;</a> <a href="#Concat" title=Concat>Concat</a> xs s

---
**Concat_prop_11**

&nbsp;&nbsp;&nbsp;&nbsp;0<n ⟹ p <a href="#composition" title=composition>;</a> <a href="#Concat" title=Concat>Concat</a> [p . t ← [1 .. int n]] s = <a href="#Concat" title=Concat>Concat</a> [p . t ← [1 .. int (n + 1)]] s

---
**Choice_prop_22**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#choice" title=choice>∪</a> <a href="#Choice" title=Choice>⋃</a> (x#xs) = a <a href="#choice" title=choice>∪</a> (x <a href="#choice" title=choice>∪</a> <a href="#Choice" title=Choice>⋃</a> xs)

---
**Choice_prop_23**

&nbsp;&nbsp;&nbsp;&nbsp;∀x ∈ set xs. x = y ⟹ <a href="#Choice" title=Choice>⋃</a> xs = <a href="#Fail" title=Fail>Fail</a> {} ∨ <a href="#Choice" title=Choice>⋃</a> xs = y ∨ <a href="#Choice" title=Choice>⋃</a> xs = y <a href="#choice" title=choice>∪</a> y

---
**Choice_prop_24**

&nbsp;&nbsp;&nbsp;&nbsp;distinct xs ⟹ distinct ys ⟹ set xs = set ys ⟹ size xs = size ys ⟹ <a href="#Choice" title=Choice>⋃</a> xs = <a href="#Choice" title=Choice>⋃</a> ys

---
**atomic_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ ∀x ∈ F. <a href="#is_atomic" title=is_atomic>is_atomic</a> x ⟹ <a href="#get_atomic" title=get_atomic>get_atomic</a> (<a href="#Choice" title=Choice>⋃</a> (<a href="#set_to_list" title=set_to_list>set_to_list</a> F)) = F

---
**decomp_programs**

&nbsp;&nbsp;&nbsp;&nbsp;Pre a = Pre p - {y} ⟹ post b = {t. t ∈ post p ∧ (fst t=y ∨ snd t=y)} ⟹ Pre b = Pre p ∩ ({y} ∪ Domain (post p <a href="#corestrict_r" title=corestrict_r>∖</a> {y})) ⟹ post a = {t. t ∈ post p ∧ (fst t ≠ y ∧ snd t ≠ y)} ⟹ a <a href="#choice" title=choice>∪</a> b <a href="#equiv" title=equiv>≡</a> p

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ finite (<a href="#S" title=S>S</a> p) ⟹ ∃xs. <a href="#Choice" title=Choice>⋃</a> xs <a href="#equiv" title=equiv>≡</a> p ∧ (∀x ∈ set xs. <a href="#is_atomic" title=is_atomic>is_atomic</a> x)

---
**civilized_finite**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#civilized_n" title=civilized_n>civilized_n</a> x B n ⟹ finite B

---
**civilized_ind**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#civilized_n" title=civilized_n>civilized_n</a> x B n ⟹ <a href="#civilized_n" title=civilized_n>civilized_n</a> x B (n + 1)

---
**civilized_ind2**

&nbsp;&nbsp;&nbsp;&nbsp;⋀m. n&lt;m ⟹ <a href="#civilized_n" title=civilized_n>civilized_n</a> x B n ⟹ <a href="#civilized_n" title=civilized_n>civilized_n</a> x B m

---
**civilized_generic**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#civilized_n" title=civilized_n>civilized_n</a> x B n = ((∃a b m m'. m<n ∧ m'<n ∧ <a href="#civilized_n" title=civilized_n>civilized_n</a> a B m ∧ <a href="#civilized_n" title=civilized_n>civilized_n</a> b B m' ∧ (a <a href="#composition" title=composition>;</a> b = x ∨ a <a href="#choice" title=choice>∪</a> b = x)) ∧ finite B) ∨ <a href="#civilized_n" title=civilized_n>civilized_n</a> x B 0

---
**civ_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#civilized_n" title=civilized_n>civilized_n</a> p B n ⟹ <a href="#civilized" title=civilized>civilized</a> p B

---
**civ_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#civilized" title=civilized>civilized</a> p B ⟹ <a href="#civilized" title=civilized>civilized</a> q B ⟹ <a href="#civilized" title=civilized>civilized</a> (p <a href="#composition" title=composition>;</a> q) B

---
**civ_prop_3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#civilized" title=civilized>civilized</a> p B ⟹ <a href="#civilized" title=civilized>civilized</a> q B ⟹ <a href="#civilized" title=civilized>civilized</a> (p <a href="#choice" title=choice>∪</a> q) B

---
**fold_prop**

&nbsp;&nbsp;&nbsp;&nbsp;foldl (∪) {} xs = {} ⟹ t ∈ set xs ⟹ t = {}

---
**fold_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ tr ⟹ tr ∈ set xs ⟹ foldl (∪) {} xs ⊆ B ⟹ x ∈ B

---
**normal_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;set x ⊆ {p} ⟹ ∃n. x = replicate n p

---
**basic_normal**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#basic" title=basic>basic</a> a = <a href="#basic" title=basic>basic</a> b ⟹ <a href="#normal_of" title=normal_of>normal_of</a> a B = <a href="#normal_of" title=normal_of>normal_of</a> b B

---
**basic_normal2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#basic" title=basic>basic</a> a = insert (<a href="#Fail" title=Fail>Fail</a> {}) (<a href="#basic" title=basic>basic</a> b) ⟹ <a href="#normal_of" title=normal_of>normal_of</a> a B = <a href="#normal_of" title=normal_of>normal_of</a> b B

---
**normal_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;finite B ⟹ <a href="#normal_of" title=normal_of>normal_of</a> [[ ]] B

---
**normal_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;finite B ⟹ <a href="#normal_of" title=normal_of>normal_of</a> [[〈State = {}, Pre = {}, post = {}〉]] B

---
**normal_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;infinite B ⟹ ¬ <a href="#normal_of" title=normal_of>normal_of</a> xs B

---
**normal_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;finite B ⟹ <a href="#normal_of" title=normal_of>normal_of</a> xs B ⟹ <a href="#normal_of" title=normal_of>normal_of</a> ([ ]#xs) B

---
**normal_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;finite B ⟹ <a href="#normal_of" title=normal_of>normal_of</a> ([ ]#xs) B ⟹ <a href="#normal_of" title=normal_of>normal_of</a> xs B

---
**normal_prop7**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#normal_of" title=normal_of>normal_of</a> [x#xs] B = (<a href="#normal_of" title=normal_of>normal_of</a> [[x]] B ∧ <a href="#normal_of" title=normal_of>normal_of</a> [xs] B)

---
**basic_prop0**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#basic" title=basic>basic</a> [[x]] ∪ <a href="#basic" title=basic>basic</a> [xs] = <a href="#basic" title=basic>basic</a> [x#xs]

---
**basic_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#basic" title=basic>basic</a> [x] ∪ <a href="#basic" title=basic>basic</a> xs = <a href="#basic" title=basic>basic</a> (x#xs)

---
**basic_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#basic" title=basic>basic</a> xs ∪ <a href="#basic" title=basic>basic</a> ys = <a href="#basic" title=basic>basic</a> (xs@ys)

---
**normal_prop8**

&nbsp;&nbsp;&nbsp;&nbsp;trace ∈ set xs ⟹ <a href="#normal_of" title=normal_of>normal_of</a> xs B ⟹ <a href="#normal_of" title=normal_of>normal_of</a> [trace] B

---
**normal_prop9**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#normal_of" title=normal_of>normal_of</a> ((a # x) # xs) B ⟹ <a href="#normal_of" title=normal_of>normal_of</a> [[a]] B

---
**basic_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;trace ∈ set xs ⟹ <a href="#basic" title=basic>basic</a> [trace] ⊆ <a href="#basic" title=basic>basic</a> xs

---
**basic_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set trace ⟹ <a href="#basic" title=basic>basic</a> [[x]] ⊆ <a href="#basic" title=basic>basic</a> [trace]

---
**normal_prop10**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set trace ⟹ trace ∈ set xs ⟹ <a href="#normal_of" title=normal_of>normal_of</a> xs B ⟹ <a href="#normal_of" title=normal_of>normal_of</a> [[x]] B

---
**normal_prop11**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#normal_of" title=normal_of>normal_of</a> ((a#x)#xs) B = (<a href="#normal_of" title=normal_of>normal_of</a> [[a]] B ∧ <a href="#normal_of" title=normal_of>normal_of</a> (x#xs) B)

---
**normal_prop12**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#normal_of" title=normal_of>normal_of</a> (x#xs) B = (<a href="#normal_of" title=normal_of>normal_of</a> [x] B ∧ <a href="#normal_of" title=normal_of>normal_of</a> xs B)

---
**normal_prop13**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#normal_of" title=normal_of>normal_of</a> (a#p) B = <a href="#normal_of" title=normal_of>normal_of</a> ((〈State = {}, Pre = {}, post = {}〉#Skip (<a href="#complete_state" title=complete_state>complete_state</a> (<a href="#set_to_list" title=set_to_list>set_to_list</a> B))#a)#p) B

---
**fold_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;trace ∈ set p ⟹ x ∈ set trace ⟹ x ∈ foldl (∪) {} (map set p)

---
**normal_prop14**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#normal_of" title=normal_of>normal_of</a> p B ⟹ trace ∈ set p ⟹ x ∈ set trace ⟹ x ∈ {Fail {}, <a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> (<a href="#set_to_list" title=set_to_list>set_to_list</a> B))} ∪ B

---
**basic_monotone1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#basic" title=basic>basic</a> a ⊆ <a href="#basic" title=basic>basic</a> (x#a)

---
**basic_monotone2**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set p ⟹ <a href="#basic" title=basic>basic</a> [x] ⊆ <a href="#basic" title=basic>basic</a> p

---
**basic_decomp1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#basic" title=basic>basic</a> [x] ∪ <a href="#basic" title=basic>basic</a> xs = <a href="#basic" title=basic>basic</a> (x#xs)

---
**basic_decomp2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#basic" title=basic>basic</a> [x] ∪ <a href="#basic" title=basic>basic</a> xs = <a href="#basic" title=basic>basic</a> (xs@[x])

---
**fold_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;foldl (∪) (foldl (∪) {} xs) ys = foldl (∪) {} xs ∪ foldl (∪) {} ys

---
**basic_decomp**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#basic" title=basic>basic</a> a ∪ <a href="#basic" title=basic>basic</a> b = <a href="#basic" title=basic>basic</a> (a@b)

---
**basic_monotone**

&nbsp;&nbsp;&nbsp;&nbsp;set a ⊆ set b ⟹ <a href="#basic" title=basic>basic</a> a ⊆ <a href="#basic" title=basic>basic</a> b

---
**basic_prop**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#basic" title=basic>basic</a> (a@b) ⊆ B ⟹ <a href="#basic" title=basic>basic</a> b ⊆ B

---
**basic_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#basic" title=basic>basic</a> (a@b) ⊆ B ⟹ <a href="#basic" title=basic>basic</a> a ⊆ B

---
**basic_monotone3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#basic" title=basic>basic</a> [a] ⊆ <a href="#basic" title=basic>basic</a> [a@b]

---
**basic_monotone4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#basic" title=basic>basic</a> [b] ⊆ <a href="#basic" title=basic>basic</a> [a@b]

---
**basic_monotone5**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#basic" title=basic>basic</a> [b] ∪ <a href="#basic" title=basic>basic</a> [a] = <a href="#basic" title=basic>basic</a> [a@b]

---
**civilized_empty2**

&nbsp;&nbsp;&nbsp;&nbsp;finite B ⟹ <a href="#civilized_n" title=civilized_n>civilized_n</a> (<a href="#Choice" title=Choice>⋃</a> [ ]) B 0

---
**civilized_empty3**

&nbsp;&nbsp;&nbsp;&nbsp;finite B ⟹ <a href="#civilized_n" title=civilized_n>civilized_n</a> (<a href="#Fail" title=Fail>Fail</a> {}) B 0

---
**civilized_empty4**

&nbsp;&nbsp;&nbsp;&nbsp;finite B ⟹ <a href="#civilized_n" title=civilized_n>civilized_n</a> (<a href="#Skip" title=Skip>Skip</a> {}) B 0

---
**normal_civilized**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#normal_of" title=normal_of>normal_of</a> p B ⟹ <a href="#civilized" title=civilized>civilized</a> (<a href="#evaluate" title=evaluate>evaluate</a> p (<a href="#complete_state" title=complete_state>complete_state</a> (<a href="#set_to_list" title=set_to_list>set_to_list</a> B))) B

---
**concat_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> ([ ] <a href="#composition_cnf" title=composition_cnf>;</a> b) c = <a href="#Fail" title=Fail>Fail</a> {}

---
**concat_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> [ ] c = <a href="#Fail" title=Fail>Fail</a> {}

---
**concat_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ <a href="#evaluate" title=evaluate>evaluate</a> (x#xs) c = <a href="#evaluate" title=evaluate>evaluate</a> [x] c <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> xs c

---
**concat_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (x#xs) ⊆ c ⟹ xs ≠ [ ] ⟹ <a href="#evaluate" title=evaluate>evaluate</a> (x#xs) c <a href="#equal" title=equal>=</a> <a href="#evaluate" title=evaluate>evaluate</a> [x] c <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> xs c

---
**concat_prop4_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> (x#xs) c <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> [x] c <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> xs c

---
**fail_compose**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Fail" title=Fail>Fail</a> {} <a href="#composition" title=composition>;</a> p <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**concat_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> (a@b) c <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> a c <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> b c

---
**Skip_concat**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> a) <a href="#composition" title=composition>;</a> <a href="#Concat" title=Concat>Concat</a> a (<a href="#complete_state" title=complete_state>complete_state</a> a) <a href="#equiv" title=equiv>≡</a> <a href="#Concat" title=Concat>Concat</a> a (<a href="#complete_state" title=complete_state>complete_state</a> a)

---
**concat_prop**

&nbsp;&nbsp;&nbsp;&nbsp;a ≠ [ ] ⟹ <a href="#Concat" title=Concat>Concat</a> a (insert x (<a href="#complete_state" title=complete_state>complete_state</a> a)) <a href="#equiv" title=equiv>≡</a> <a href="#Concat" title=Concat>Concat</a> a (<a href="#complete_state" title=complete_state>complete_state</a> a)

---
**state_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (<a href="#evaluate" title=evaluate>evaluate</a> xs C) ∪ <a href="#S" title=S>S</a> (<a href="#evaluate" title=evaluate>evaluate</a> [x] C) = <a href="#S" title=S>S</a> (<a href="#evaluate" title=evaluate>evaluate</a> (x#xs) C)

---
**state_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (<a href="#evaluate" title=evaluate>evaluate</a> xs C) ∪ <a href="#S" title=S>S</a> (<a href="#evaluate" title=evaluate>evaluate</a> ys C) = <a href="#S" title=S>S</a> (<a href="#evaluate" title=evaluate>evaluate</a> (ys@xs) C)

---
**eval_prop**

&nbsp;&nbsp;&nbsp;&nbsp;[ ] ∉ set xs ⟹ <a href="#evaluate" title=evaluate>evaluate</a> xs C = <a href="#evaluate" title=evaluate>evaluate</a> xs D

---
**state_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;[ ] ∈ set xs ⟹ <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (xs) ⊆ <a href="#S" title=S>S</a> (<a href="#evaluate" title=evaluate>evaluate</a> (xs) (<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (xx#xs)))

---
**state_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;[ ] ∉ set xs ⟹ <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (xs) ⊆ <a href="#S" title=S>S</a> (<a href="#evaluate" title=evaluate>evaluate</a> (xs) (<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (xx#xs)))

---
**state_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (xs) ⊆ <a href="#S" title=S>S</a> (<a href="#evaluate" title=evaluate>evaluate</a> (xs) (<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (xx#xs)))

---
**state_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (<a href="#evaluate" title=evaluate>evaluate</a> xs (<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> xs)) = <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> xs

---
**skip_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> (<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> xs) <a href="#composition" title=composition>;</a> <a href="#evaluate" title=evaluate>evaluate</a> (xs) (<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> xs) <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> (xs) (<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> xs)

---
**concat_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> ([ ]#xs) (<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> xs) <a href="#equiv" title=equiv>≡</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> xs) <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> xs (<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> xs)

---
**non_empty0**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty" title=non_empty>non_empty</a> (<a href="#non_empty" title=non_empty>non_empty</a> xs) = <a href="#non_empty" title=non_empty>non_empty</a> xs

---
**non_empty1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty" title=non_empty>non_empty</a> [ ] = [ ]

---
**non_empty2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty" title=non_empty>non_empty</a> [[ ]] = [ ]

---
**cnf_choice1**

&nbsp;&nbsp;&nbsp;&nbsp;[ ] <a href="#choice_cnf" title=choice_cnf>∪</a> p = <a href="#non_empty" title=non_empty>non_empty</a> p

---
**cnf_choice1**

&nbsp;&nbsp;&nbsp;&nbsp;[ ] <a href="#choice_cnf" title=choice_cnf>∪</a> p = p

---
**non_empty3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty" title=non_empty>non_empty</a> ([ ]#xs) = <a href="#non_empty" title=non_empty>non_empty</a> xs

---
**non_empty4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty" title=non_empty>non_empty</a> (a@b) = <a href="#non_empty" title=non_empty>non_empty</a> a @ <a href="#non_empty" title=non_empty>non_empty</a> b

---
**cnf_choice2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty" title=non_empty>non_empty</a> (x#xs) = [x] <a href="#choice_cnf" title=choice_cnf>∪</a> xs

---
**cnf_choice2**

&nbsp;&nbsp;&nbsp;&nbsp;(x#xs) = [x] <a href="#choice_cnf" title=choice_cnf>∪</a> xs

---
**cnf_choice3**

&nbsp;&nbsp;&nbsp;&nbsp;ys <a href="#choice_cnf" title=choice_cnf>∪</a> (x#xs) = (ys@[x]) <a href="#choice_cnf" title=choice_cnf>∪</a> xs

---
**non_empty5**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty" title=non_empty>non_empty</a> ((xx # x) # b) = (xx#x) # (<a href="#non_empty" title=non_empty>non_empty</a> b)

---
**non_empty6**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty" title=non_empty>non_empty</a> ((xx # x) # b) = [xx#x] <a href="#choice_cnf" title=choice_cnf>∪</a> (<a href="#non_empty" title=non_empty>non_empty</a> b)

---
**non_empty6**

&nbsp;&nbsp;&nbsp;&nbsp;((xx # x) # b) = [xx#x] <a href="#choice_cnf" title=choice_cnf>∪</a> b

---
**non_empty7**

&nbsp;&nbsp;&nbsp;&nbsp;((x#xs)@(y#ys)) = (x#xs) <a href="#choice_cnf" title=choice_cnf>∪</a> (y#ys)

---
**non_empty7**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty" title=non_empty>non_empty</a> ((x#xs)@(y#ys)) = (x#xs) <a href="#choice_cnf" title=choice_cnf>∪</a> (y#ys)

---
**non_empty8**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#choice_cnf" title=choice_cnf>∪</a> b ≠ [[ ]] ⟹ a <a href="#choice_cnf" title=choice_cnf>∪</a> b = (<a href="#non_empty" title=non_empty>non_empty</a> a) <a href="#choice_cnf" title=choice_cnf>∪</a> (<a href="#non_empty" title=non_empty>non_empty</a> b)

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> (<a href="#non_empty" title=non_empty>non_empty</a> a) = <a href="#evaluate" title=evaluate>evaluate</a> a

---
**cnf_choice_4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> (a <a href="#choice_cnf" title=choice_cnf>∪</a> b) = <a href="#evaluate" title=evaluate>evaluate</a> (<a href="#non_empty" title=non_empty>non_empty</a> a <a href="#choice_cnf" title=choice_cnf>∪</a> <a href="#non_empty" title=non_empty>non_empty</a> b)

---
**state_prop7**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (<a href="#evaluate" title=evaluate>evaluate</a> [y] (<a href="#complete_state" title=complete_state>complete_state</a> y)) = <a href="#complete_state" title=complete_state>complete_state</a> y

---
**skip_prop**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> x ⊆ C ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> x ⟹x <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> C <a href="#equiv" title=equiv>≡</a> x

---
**concat_prop8**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_state" title=complete_state>complete_state</a> y ⊆ C ⟹ <a href="#evaluate" title=evaluate>evaluate</a> [[ ]] C <a href="#composition" title=composition>;</a> <a href="#evaluate" title=evaluate>evaluate</a> [y] C <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> ([[ ]] <a href="#composition_cnf" title=composition_cnf>;</a> [y]) C

---
**concat_prop9**

&nbsp;&nbsp;&nbsp;&nbsp;x ≠ [ ] ⟹ y ≠ [ ] ⟹ [x] <a href="#composition_cnf" title=composition_cnf>;</a> [y] = [x@y]

---
**concat_prop10**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_state" title=complete_state>complete_state</a> (x#xs) ⊆ C ⟹ <a href="#all_feasible" title=all_feasible>all_feasible</a> (x#xs) ⟹ <a href="#evaluate" title=evaluate>evaluate</a> [[x]] C <a href="#composition" title=composition>;</a> <a href="#evaluate" title=evaluate>evaluate</a> [xs] C <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> ([[x]] <a href="#composition_cnf" title=composition_cnf>;</a> [xs]) C

---
**feas_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> (x @ y) ⟹ <a href="#all_feasible" title=all_feasible>all_feasible</a> x

---
**feas_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> (x @ y) ⟹ <a href="#all_feasible" title=all_feasible>all_feasible</a> y

---
**concat_prop11**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> (x@y) ⟹ <a href="#complete_state" title=complete_state>complete_state</a> (x@y) ⊆ C ⟹ <a href="#evaluate" title=evaluate>evaluate</a> [x] C <a href="#composition" title=composition>;</a> <a href="#evaluate" title=evaluate>evaluate</a> [y] C <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> ([x] <a href="#composition_cnf" title=composition_cnf>;</a> [y]) C

---
**concat_prop11_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> (x@y) ⟹ <a href="#evaluate" title=evaluate>evaluate</a> [x] (<a href="#complete_state" title=complete_state>complete_state</a> (x@y)) <a href="#composition" title=composition>;</a> <a href="#evaluate" title=evaluate>evaluate</a> [y] (<a href="#complete_state" title=complete_state>complete_state</a> (x@y)) <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> ([x] <a href="#composition_cnf" title=composition_cnf>;</a> [y]) (<a href="#complete_state" title=complete_state>complete_state</a> (x@y))

---
**concat_prop12**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> (a#x@y) ⟹ (<a href="#complete_state" title=complete_state>complete_state</a> (a#x@y)) ⊆ C ⟹ <a href="#evaluate" title=evaluate>evaluate</a> [a # x] C <a href="#composition" title=composition>;</a> <a href="#evaluate" title=evaluate>evaluate</a> [y] C <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> ([a # x] <a href="#composition_cnf" title=composition_cnf>;</a> [y]) C

---
**concat_prop12_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> (a#x@y) ⟹ <a href="#evaluate" title=evaluate>evaluate</a> [a # x] (<a href="#complete_state" title=complete_state>complete_state</a> (a#x@y)) <a href="#composition" title=composition>;</a> <a href="#evaluate" title=evaluate>evaluate</a> [y] (<a href="#complete_state" title=complete_state>complete_state</a> (a#x@y)) <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> ([a # x] <a href="#composition_cnf" title=composition_cnf>;</a> [y]) (<a href="#complete_state" title=complete_state>complete_state</a> (a#x@y))

---
**choice_non_empty**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty" title=non_empty>non_empty</a> a <a href="#choice_cnf" title=choice_cnf>∪</a> b = a <a href="#choice_cnf" title=choice_cnf>∪</a> b

---
**choice_non_empty2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty" title=non_empty>non_empty</a> a <a href="#choice_cnf" title=choice_cnf>∪</a> <a href="#non_empty" title=non_empty>non_empty</a> b = a <a href="#choice_cnf" title=choice_cnf>∪</a> b

---
**non_empty9**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (<a href="#non_empty" title=non_empty>non_empty</a> xs) ⟹ x ∈ set xs

---
**non_empty10**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty" title=non_empty>non_empty</a> xs = [y] ⟹ ∃a b. a@y#b = xs

---
**non_empty11**

&nbsp;&nbsp;&nbsp;&nbsp;xs = [ ] ⟹ <a href="#evaluate" title=evaluate>evaluate</a> xs C = <a href="#Fail" title=Fail>Fail</a> {}

---
**non_empty12**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty" title=non_empty>non_empty</a> xs = [x] ⟹ <a href="#non_empty" title=non_empty>non_empty</a> xs = xs ⟹  <a href="#evaluate" title=evaluate>evaluate</a> xs = <a href="#evaluate" title=evaluate>evaluate</a> [x]

---
**nonempty_monotonic**

&nbsp;&nbsp;&nbsp;&nbsp;size (<a href="#non_empty" title=non_empty>non_empty</a> (x#xs)) &gt; size (<a href="#non_empty" title=non_empty>non_empty</a> xs)

---
**non_empty_reduces_size**

&nbsp;&nbsp;&nbsp;&nbsp;size (<a href="#non_empty" title=non_empty>non_empty</a> xs) &lt; size xs

---
**non_empty_13**

&nbsp;&nbsp;&nbsp;&nbsp;size (x#xs) = size (<a href="#non_empty" title=non_empty>non_empty</a> (x#xs)) ⟹ x ≠ [ ]

---
**non_empty_14**

&nbsp;&nbsp;&nbsp;&nbsp;size b = size (<a href="#non_empty" title=non_empty>non_empty</a> b) ⟹ b = (<a href="#non_empty" title=non_empty>non_empty</a> b)

---
**eval_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;size b = 1 ⟹ size (<a href="#non_empty" title=non_empty>non_empty</a> b) = 1 ⟹ <a href="#evaluate" title=evaluate>evaluate</a> b = <a href="#evaluate" title=evaluate>evaluate</a> (<a href="#non_empty" title=non_empty>non_empty</a> b)

---
**comp_cnf3**

&nbsp;&nbsp;&nbsp;&nbsp;x ≠ [ ] ⟹ y ≠ [ ] ⟹ <a href="#Concat" title=Concat>Concat</a> x (<a href="#complete_state" title=complete_state>complete_state</a> (x@y)) <a href="#composition" title=composition>;</a> <a href="#Concat" title=Concat>Concat</a> y (<a href="#complete_state" title=complete_state>complete_state</a> (x@y)) = <a href="#Concat" title=Concat>Concat</a> (x @ y) (<a href="#complete_state" title=complete_state>complete_state</a> (x@y))

---
**comp_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;x <a href="#composition" title=composition>;</a> (y <a href="#choice" title=choice>∪</a> <a href="#Skip" title=Skip>Skip</a> {}) <a href="#equiv" title=equiv>≡</a> x <a href="#composition" title=composition>;</a> y

---
**choice_cnf_thm**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> xs (<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (xs@ys)) <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> ys (<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (xs@ys)) <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> (xs <a href="#choice_cnf" title=choice_cnf>∪</a> ys) (<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (xs@ys))

---
**non_empty14**

&nbsp;&nbsp;&nbsp;&nbsp;∀t ∈ set xs. t ≠ [ ] ⟹ <a href="#non_empty" title=non_empty>non_empty</a> xs = xs

---
**choic_cnf1**

&nbsp;&nbsp;&nbsp;&nbsp;(x#xs) <a href="#composition_cnf" title=composition_cnf>;</a> ys = ([x] <a href="#composition_cnf" title=composition_cnf>;</a> ys) <a href="#choice_cnf" title=choice_cnf>∪</a> (xs <a href="#composition_cnf" title=composition_cnf>;</a> ys)

---
**comp_distrib_r**

&nbsp;&nbsp;&nbsp;&nbsp;(b <a href="#choice_cnf" title=choice_cnf>∪</a> c) <a href="#composition_cnf" title=composition_cnf>;</a> a = (b <a href="#composition_cnf" title=composition_cnf>;</a> a) <a href="#choice_cnf" title=choice_cnf>∪</a> (c <a href="#composition_cnf" title=composition_cnf>;</a> a)

---
**choice_cnf_commute**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#choice_cnf" title=choice_cnf>∪</a> (b <a href="#choice_cnf" title=choice_cnf>∪</a> c) = (a <a href="#choice_cnf" title=choice_cnf>∪</a> b) <a href="#choice_cnf" title=choice_cnf>∪</a> c

---
**equal_sym**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#equal_cnf" title=equal_cnf>equal_cnf</a> a b = <a href="#equal_cnf" title=equal_cnf>equal_cnf</a> b a

---
**equal_empty**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#equal_cnf" title=equal_cnf>equal_cnf</a> a [ ] ⟹ a = [ ]

---
**eval_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;ys≠[ ] ⟹ <a href="#evaluate" title=evaluate>evaluate</a> ys C <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> [y] C = <a href="#evaluate" title=evaluate>evaluate</a> (ys @ [y]) C

---
**evaluate_switch**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> (y#ys) C = <a href="#evaluate" title=evaluate>evaluate</a> (ys@[y]) C

---
**evaluate_split**

&nbsp;&nbsp;&nbsp;&nbsp;xs≠[ ] ⟹ ys ≠ [ ] ⟹ <a href="#evaluate" title=evaluate>evaluate</a> (xs@ys) C = <a href="#evaluate" title=evaluate>evaluate</a> xs C <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> ys C

---
**evaluate_switch2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> (yss@yse) C = <a href="#evaluate" title=evaluate>evaluate</a> (yse@yss) C

---
**eval_perm**

&nbsp;&nbsp;&nbsp;&nbsp;a#ys' ∈ set (<a href="#permutations" title=permutations>permutations</a> ys) ⟹ <a href="#evaluate" title=evaluate>evaluate</a> (a#ys') C = <a href="#evaluate" title=evaluate>evaluate</a> ys C

---
**perm_eval**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set (<a href="#permutations" title=permutations>permutations</a> ys) ⟹ <a href="#evaluate" title=evaluate>evaluate</a> xs C = <a href="#evaluate" title=evaluate>evaluate</a> ys C

---
**perm_prop**

&nbsp;&nbsp;&nbsp;&nbsp;[t. t ← xs, ¬ p t] @ [t. t ← xs, p t] ∈ set (<a href="#permutations" title=permutations>permutations</a> xs)

---
**size_prop**

&nbsp;&nbsp;&nbsp;&nbsp;size ([t. t ← xs, ¬ p t] @ [t. t ← xs, p t]) = size xs

---
**evaluate_split1**

&nbsp;&nbsp;&nbsp;&nbsp;size (xs@ys) ≠ 1 ⟹ <a href="#evaluate" title=evaluate>evaluate</a> xs C <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> ys C = <a href="#evaluate" title=evaluate>evaluate</a> (xs@ys) C

---
**evaluate_split2**

&nbsp;&nbsp;&nbsp;&nbsp;size xs ≠1 ⟹ <a href="#evaluate" title=evaluate>evaluate</a> xs C  = <a href="#evaluate" title=evaluate>evaluate</a> [t. t ← xs, t =x] C <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> [t. t ← xs, t≠x] C

---
**size_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;size [t. t←a, t=x] + size [t. t←a, t≠x] = size a

---
**evaluate_prop**

&nbsp;&nbsp;&nbsp;&nbsp;size xs = 1 ⟹ ∀t ∈ set xs. t=x ⟹ <a href="#evaluate" title=evaluate>evaluate</a> xs = <a href="#evaluate" title=evaluate>evaluate</a> [x]

---
**evaluate_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;size xs > 1 ⟹ ∀t ∈ set xs. t=x ⟹ <a href="#evaluate" title=evaluate>evaluate</a> xs C = <a href="#evaluate" title=evaluate>evaluate</a> [x] C <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> [x] C

---
**equal_eval**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#equal_cnf" title=equal_cnf>equal_cnf</a> a b ⟹ <a href="#evaluate" title=evaluate>evaluate</a> a C = <a href="#evaluate" title=evaluate>evaluate</a> b C

---
**eval_simp**

&nbsp;&nbsp;&nbsp;&nbsp;∀C. <a href="#evaluate" title=evaluate>evaluate</a> a C = <a href="#evaluate" title=evaluate>evaluate</a> b C ⟹ <a href="#evaluate" title=evaluate>evaluate</a> a = <a href="#evaluate" title=evaluate>evaluate</a> b

---
**equal_eval2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#equal_cnf" title=equal_cnf>equal_cnf</a> a b ⟹ <a href="#evaluate" title=evaluate>evaluate</a> a = <a href="#evaluate" title=evaluate>evaluate</a> b

---
**eq_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#equal" title=equal>equal</a> xs xs

---
**comp_prop**

&nbsp;&nbsp;&nbsp;&nbsp;tr ∈ set (xs <a href="#composition_cnf" title=composition_cnf>;</a> ys) ⟹ ∃x y. x ∈ set xs ∧ y ∈ set ys ∧ x@y = tr

---
**comp_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set xs ⟹ y ∈ set ys ⟹ x@y ∈ set (xs <a href="#composition_cnf" title=composition_cnf>;</a> ys)

---
**choice_prop**

&nbsp;&nbsp;&nbsp;&nbsp;tr ∈ set (xs <a href="#choice_cnf" title=choice_cnf>∪</a> ys) ⟹ (tr ∈ set xs ∨ tr ∈ set ys)

---
**same_traces_size_equal**

&nbsp;&nbsp;&nbsp;&nbsp;∀tr ∈ set xs. tr ∈ set ys ⟹ ∀tr ∈ set ys. tr ∈ set xs ⟹ size xs = size ys ⟹ <a href="#equal_cnf" title=equal_cnf>equal_cnf</a> xs ys

---
**same_traces_size_equal2**

&nbsp;&nbsp;&nbsp;&nbsp;size xs = size ys ⟹ <a href="#equal_cnf" title=equal_cnf>equal_cnf</a> xs ys ⟹ ∀tr ∈ set xs. tr ∈ set ys

---
**same_traces_size_equal3**

&nbsp;&nbsp;&nbsp;&nbsp;size xs = size ys ⟹ <a href="#equal_cnf" title=equal_cnf>equal_cnf</a> xs ys ⟹ ∀tr ∈ set ys. tr ∈ set xs

---
**comp_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;∃q w. q ∈ set a ∧ w ∈ set b ∧ tr = q @ w ∧ q ≠ [ ] ∧ w ≠ [ ] ⟹ tr ∈ set (a <a href="#composition_cnf" title=composition_cnf>;</a> b)

---
**choice_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;∃q. (q ∈ set a ∨ q ∈ set b) ∧ tr = q ∧ q ≠ [ ] ⟹ tr ∈ set (a <a href="#choice_cnf" title=choice_cnf>∪</a> b)

---
&nbsp;&nbsp;&nbsp;&nbsp;size (a <a href="#choice_cnf" title=choice_cnf>∪</a> b) = size (a) + size (b)

---
**comp_size**

&nbsp;&nbsp;&nbsp;&nbsp;x ≠ [ ] ⟹ length (((xx # x) # xs) <a href="#composition_cnf" title=composition_cnf>;</a> b) = length ((x # xs) <a href="#composition_cnf" title=composition_cnf>;</a> b)

---
**comp_size2**

&nbsp;&nbsp;&nbsp;&nbsp;size ([[a]] <a href="#composition_cnf" title=composition_cnf>;</a> b) = size b

---
**comp_size3**

&nbsp;&nbsp;&nbsp;&nbsp;size (a <a href="#composition_cnf" title=composition_cnf>;</a> b) = size a * size b

---
**feas_prop**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> xs ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#Concat" title=Concat>Concat</a> xs C)

---
**feas_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#evaluate" title=evaluate>evaluate</a> [ ] C)

---
**feas_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#evaluate" title=evaluate>evaluate</a> [[ ]] C)

---
**feas_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> x ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#evaluate" title=evaluate>evaluate</a> [[x]] C)

---
**eval_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ <a href="#evaluate" title=evaluate>evaluate</a> [x # xs] C = <a href="#evaluate" title=evaluate>evaluate</a> [[x]] C <a href="#composition" title=composition>;</a> <a href="#evaluate" title=evaluate>evaluate</a> [xs] C

---
**feas_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> xs ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#evaluate" title=evaluate>evaluate</a> [xs] C)

---
**feas_prop7**

&nbsp;&nbsp;&nbsp;&nbsp;∀bb ∈ set b. <a href="#all_feasible" title=all_feasible>all_feasible</a> bb ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#evaluate" title=evaluate>evaluate</a> b C)

---
**cnf_state_prop**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (x#b) ⊆ C ⟹ <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> b ⊆ C

---
**cnf_state_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_state" title=complete_state>complete_state</a> xs ⊆ C ⟹ <a href="#S" title=S>S</a> (<a href="#evaluate" title=evaluate>evaluate</a> [xs] C) ⊆ C

---
**cnf_state_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> xs ⊆ C ⟹ <a href="#S" title=S>S</a> (<a href="#evaluate" title=evaluate>evaluate</a> xs C) ⊆ C

---
**skip_left_neutral**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> b ⊆ C ⟹ <a href="#Skip" title=Skip>Skip</a> C <a href="#composition" title=composition>;</a> <a href="#evaluate" title=evaluate>evaluate</a> b C <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> b C

---
**skip_right_neutral**

&nbsp;&nbsp;&nbsp;&nbsp;∀bb ∈ set b. <a href="#all_feasible" title=all_feasible>all_feasible</a> bb ⟹ <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> b ⊆ C ⟹ <a href="#evaluate" title=evaluate>evaluate</a> b C <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> C <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> b C

---
**feas_prop8**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> x ⟹ <a href="#all_feasible" title=all_feasible>all_feasible</a> b1 ⟹ <a href="#all_feasible" title=all_feasible>all_feasible</a> (x @ b1)

---
**state_prop**

&nbsp;&nbsp;&nbsp;&nbsp;y ∈set ys ⟹ <a href="#complete_state" title=complete_state>complete_state</a> (ys) = <a href="#complete_state" title=complete_state>complete_state</a> (y#ys)

---
**state_prop8**

&nbsp;&nbsp;&nbsp;&nbsp;set xs ⊆ set ys ⟹ <a href="#complete_state" title=complete_state>complete_state</a> xs ⊆ <a href="#complete_state" title=complete_state>complete_state</a> ys

---
**state_prop9**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (xs # [ys]) = <a href="#complete_state" title=complete_state>complete_state</a> (xs @ ys)

---
**compose_equiv**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (x#b) ⊆ C ⟹ <a href="#all_feasible" title=all_feasible>all_feasible</a> x ⟹ ∀bb ∈ set b. <a href="#all_feasible" title=all_feasible>all_feasible</a> bb ⟹ <a href="#evaluate" title=evaluate>evaluate</a> [x] C <a href="#composition" title=composition>;</a> <a href="#evaluate" title=evaluate>evaluate</a> b C <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> ([x] <a href="#composition_cnf" title=composition_cnf>;</a> b) C

---
**state_prop10**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (a) ⊆ <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (a @ b)

---
**state_prop11**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (b) ⊆ <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (a @ b)

---
**state_prop12**

&nbsp;&nbsp;&nbsp;&nbsp;set xs ⊆ set ys ⟹ <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> xs ⊆ <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> ys

---
**eval_choice**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> xs C <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> ys C <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> (xs <a href="#choice_cnf" title=choice_cnf>∪</a> ys) C

---
**comp_choice**

&nbsp;&nbsp;&nbsp;&nbsp;([x] <a href="#composition_cnf" title=composition_cnf>;</a> b) <a href="#choice_cnf" title=choice_cnf>∪</a> (a' <a href="#composition_cnf" title=composition_cnf>;</a> b) = (x#a') <a href="#composition_cnf" title=composition_cnf>;</a> b

---
**normal_prop15**

&nbsp;&nbsp;&nbsp;&nbsp;set a = set b ⟹ <a href="#normal_of" title=normal_of>normal_of</a> a B = <a href="#normal_of" title=normal_of>normal_of</a> b B

---
**normal_prop16**

&nbsp;&nbsp;&nbsp;&nbsp;set a ⊆ set b ⟹ <a href="#normal_of" title=normal_of>normal_of</a> b B → <a href="#normal_of" title=normal_of>normal_of</a> a B

---
**non_empty_is_smaller**

&nbsp;&nbsp;&nbsp;&nbsp;set (<a href="#non_empty" title=non_empty>non_empty</a> xs) ⊆ set xs

---
**normal_prop17**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#normal_of" title=normal_of>normal_of</a> a B ⟹ <a href="#normal_of" title=normal_of>normal_of</a> (<a href="#non_empty" title=non_empty>non_empty</a> a) B

---
**normal_prop17_5**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#normal_of" title=normal_of>normal_of</a> xs B ⟹ <a href="#normal_of" title=normal_of>normal_of</a> [x] B ⟹ <a href="#normal_of" title=normal_of>normal_of</a> (x#xs) B

---
**normal_prop18**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#normal_of" title=normal_of>normal_of</a> a B ⟹ <a href="#normal_of" title=normal_of>normal_of</a> b B ⟹ <a href="#normal_of" title=normal_of>normal_of</a> (a <a href="#choice_cnf" title=choice_cnf>∪</a> b) B

---
**basic_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#basic" title=basic>basic</a> (map ((@) x) bs) ⊆ <a href="#basic" title=basic>basic</a> [x] ∪ <a href="#basic" title=basic>basic</a> bs

---
**normal_prop19**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#normal_of" title=normal_of>normal_of</a> [x] B ⟹ <a href="#normal_of" title=normal_of>normal_of</a> b B ⟹ <a href="#normal_of" title=normal_of>normal_of</a> [x@ys. ys ← b] B

---
**normal_prop20**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#normal_of" title=normal_of>normal_of</a> a B ⟹ <a href="#normal_of" title=normal_of>normal_of</a> b B ⟹ <a href="#normal_of" title=normal_of>normal_of</a> (a <a href="#composition_cnf" title=composition_cnf>;</a> b) B

---
**state_prop13**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#normal_of" title=normal_of>normal_of</a> [x] B ⟹ <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> [x] ⊆ <a href="#complete_state" title=complete_state>complete_state</a> (<a href="#set_to_list" title=set_to_list>set_to_list</a> B)

---
**state_prop14**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#normal_of" title=normal_of>normal_of</a> xs B ⟹ <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> xs ⊆ <a href="#complete_state" title=complete_state>complete_state</a> (<a href="#set_to_list" title=set_to_list>set_to_list</a> B)

---
**feas_prop9**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> (<a href="#set_to_list" title=set_to_list>set_to_list</a> B) ⟹ <a href="#normal_of" title=normal_of>normal_of</a> xs B ⟹ ∀tr ∈ set xs. <a href="#all_feasible" title=all_feasible>all_feasible</a> tr

---
**comp_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> x ⟹ <a href="#all_feasible" title=all_feasible>all_feasible</a> y ⟹ <a href="#complete_state" title=complete_state>complete_state</a> x ⊆ C ⟹ <a href="#complete_state" title=complete_state>complete_state</a> y ⊆ C ⟹ <a href="#evaluate" title=evaluate>evaluate</a> ([x] <a href="#composition_cnf" title=composition_cnf>;</a> [y]) C <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> [x] C <a href="#composition" title=composition>;</a> <a href="#evaluate" title=evaluate>evaluate</a> [y] C

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (x#ys) ⊆ C ⟹ ∀tr∈set (x#ys). <a href="#all_feasible" title=all_feasible>all_feasible</a> tr ⟹ <a href="#evaluate" title=evaluate>evaluate</a> ([x] <a href="#composition_cnf" title=composition_cnf>;</a> ys) C <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> ([x]) C <a href="#composition" title=composition>;</a> <a href="#evaluate" title=evaluate>evaluate</a> (ys) C

---
**civilized_thm1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> (<a href="#set_to_list" title=set_to_list>set_to_list</a> B) ⟹ <a href="#S" title=S>S</a> p ⊆ C ⟹ <a href="#civilized_n" title=civilized_n>civilized_n</a> p B n ⟹ ∃(y::'a CNF). <a href="#evaluate" title=evaluate>evaluate</a> y C <a href="#equiv" title=equiv>≡</a> p ∧ <a href="#normal_of" title=normal_of>normal_of</a> y B

---
**set_to_list_prop**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ y ∉ F ⟹ count_list (<a href="#set_to_list" title=set_to_list>set_to_list</a> F) y = 0

---
**set_to_list_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ count_list (<a href="#set_to_list" title=set_to_list>set_to_list</a> (F - {y})) y = 0

---
**set_to_list_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;count_list (<a href="#set_to_list" title=set_to_list>set_to_list</a> {y}) y = 1

---
**set_to_list_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;count_list (<a href="#set_to_list" title=set_to_list>set_to_list</a> {}) y = 0

---
**set_to_list_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ y ∉ F ⟹ <a href="#set_to_list" title=set_to_list>set_to_list</a> (insert y F) ∈ set (<a href="#permutations" title=permutations>permutations</a> (y # <a href="#set_to_list" title=set_to_list>set_to_list</a> F))

---
&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ count_list (<a href="#set_to_list" title=set_to_list>set_to_list</a> (insert x F)) x = 1

---
**set_to_list_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ x ∉ F ⟹ count_list (<a href="#set_to_list" title=set_to_list>set_to_list</a> (insert x F)) y = count_list (x#set_to_list F) y

---
**set_to_list_prop7**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ x ∉ F ⟹ x ≠ y ⟹ count_list (<a href="#set_to_list" title=set_to_list>set_to_list</a> (insert x F)) y = count_list (<a href="#set_to_list" title=set_to_list>set_to_list</a> F) y

---
**set_to_list_prop8**

&nbsp;&nbsp;&nbsp;&nbsp;x=y ⟹ count_list (yst@x#ynd) y = count_list (yst@ynd) y + 1

---
**set_to_list_prop9**

&nbsp;&nbsp;&nbsp;&nbsp;x≠y ⟹ count_list (yst@x#ynd) y = count_list (yst@ynd) y

---
**set_to_list_prop10**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set (<a href="#permutations" title=permutations>permutations</a> ys) ⟹ count_list xs = count_list ys

---
**set_to_list_prop11**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ count_list (<a href="#set_to_list" title=set_to_list>set_to_list</a> F) x &lt; 1

---
**set_to_list_prop12**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ x ∈ F ⟹ count_list (<a href="#set_to_list" title=set_to_list>set_to_list</a> F) x = 1

---
**set_to_list_prop13**

&nbsp;&nbsp;&nbsp;&nbsp;count_list xs x = 1 ⟹ count_list (<a href="#set_to_list" title=set_to_list>set_to_list</a> (set xs)) x = 1

---
**set_to_list_prop14**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ <a href="#complete_state" title=complete_state>complete_state</a> (<a href="#set_to_list" title=set_to_list>set_to_list</a> (insert y F)) = <a href="#complete_state" title=complete_state>complete_state</a> (<a href="#set_to_list" title=set_to_list>set_to_list</a> (F)) ∪ <a href="#S" title=S>S</a> y

---
**set_to_list_prop15**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#civilized" title=civilized>civilized</a> p B ⟹ <a href="#S" title=S>S</a> p ⊆ <a href="#complete_state" title=complete_state>complete_state</a> (<a href="#set_to_list" title=set_to_list>set_to_list</a> B)

---
**civilized_thm2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> (<a href="#set_to_list" title=set_to_list>set_to_list</a> B) ⟹ <a href="#civilized" title=civilized>civilized</a> p B ⟹ ∃(y::'a CNF). <a href="#evaluate" title=evaluate>evaluate</a> y (<a href="#complete_state" title=complete_state>complete_state</a> (<a href="#set_to_list" title=set_to_list>set_to_list</a> B)) <a href="#equiv" title=equiv>≡</a> p ∧ <a href="#normal_of" title=normal_of>normal_of</a> y B

---
**fail_is_civilized**

&nbsp;&nbsp;&nbsp;&nbsp;finite B ⟹ <a href="#civilized" title=civilized>civilized</a> (Fail{}) B

---
**skip_is_civilized**

&nbsp;&nbsp;&nbsp;&nbsp;finite B ⟹ <a href="#civilized" title=civilized>civilized</a> (<a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> (<a href="#set_to_list" title=set_to_list>set_to_list</a> B))) B

---
**civilized_thm3**

&nbsp;&nbsp;&nbsp;&nbsp;∃(y::'a CNF). <a href="#evaluate" title=evaluate>evaluate</a> y (<a href="#complete_state" title=complete_state>complete_state</a> (<a href="#set_to_list" title=set_to_list>set_to_list</a> B)) = p ∧ <a href="#normal_of" title=normal_of>normal_of</a> y B ⟹ <a href="#civilized" title=civilized>civilized</a> p B

---
**composition_cnf_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;[[x]] <a href="#composition_cnf" title=composition_cnf>;</a> xs = [x#ys. ys ← xs]

---
**composition_cnf_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;[y#ys] <a href="#composition_cnf" title=composition_cnf>;</a> xs = [( y#ys)@t. t ← xs]

---
**non2_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty" title=non_empty>non_empty</a> x = [ ] ⟹ <a href="#non_empty2" title=non_empty2>non_empty2</a> (x # xs) = <a href="#non_empty2" title=non_empty2>non_empty2</a> xs

---
**non2_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty" title=non_empty>non_empty</a> x ≠ [ ] ⟹ <a href="#non_empty2" title=non_empty2>non_empty2</a> (x # xs) = <a href="#non_empty" title=non_empty>non_empty</a> x # <a href="#non_empty2" title=non_empty2>non_empty2</a> xs

---
**non2_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty2" title=non_empty2>non_empty2</a> (xs @ ys) = <a href="#non_empty2" title=non_empty2>non_empty2</a> xs @ <a href="#non_empty2" title=non_empty2>non_empty2</a> ys

---
**non2_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;size (<a href="#non_empty2" title=non_empty2>non_empty2</a> xs) &lt; size xs

---
**non2_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty2" title=non_empty2>non_empty2</a> (x#xs) = x#xs ⟹ <a href="#non_empty2" title=non_empty2>non_empty2</a> xs = xs

---
**non2_prop5_5**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty2" title=non_empty2>non_empty2</a> [x] = [x] ⟹ ∀path∈set x. path ≠ [ ]

---
**non2_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty2" title=non_empty2>non_empty2</a> xs = xs ⟹ ∀prog ∈ set xs. prog ≠ [ ] ∧ (∀path ∈ set prog. path ≠ [ ])

---
**non_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty" title=non_empty>non_empty</a> xs = xs ⟹ ∀path ∈ set xs. path ≠ [ ]

---
**non2_prop7**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty2" title=non_empty2>non_empty2</a> xs = xs ⟹ x ∈ set xs ⟹ <a href="#non_empty" title=non_empty>non_empty</a> x = x

---
**non2_idem**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#non_empty2" title=non_empty2>non_empty2</a> xs = <a href="#non_empty2" title=non_empty2>non_empty2</a> (<a href="#non_empty2" title=non_empty2>non_empty2</a> xs)

---
**inter_head**

&nbsp;&nbsp;&nbsp;&nbsp;p ∈ set ((x#xs) <a href="#interleave" title=interleave>⫴</a> (y#ys)) ⟹ hd p = x ∨ hd p = y

---
**count_prop**

&nbsp;&nbsp;&nbsp;&nbsp;count_list (map ((#) x) xs) (x#p) = count_list xs p

---
**count_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;x≠y ⟹ count_list (map ((#) x) xs) (y#p) = 0

---
**interleave_non_empty**

&nbsp;&nbsp;&nbsp;&nbsp;p ∈ set ((x#xs) <a href="#interleave" title=interleave>⫴</a> (y#ys)) ⟹ p ≠ [ ]

---
**inter2**

&nbsp;&nbsp;&nbsp;&nbsp;count_list (ys <a href="#interleave" title=interleave>⫴</a> xs) p = count_list (xs <a href="#interleave" title=interleave>⫴</a> ys) p

---
**inter_perm**

&nbsp;&nbsp;&nbsp;&nbsp;ys <a href="#interleave" title=interleave>⫴</a> xs ∈ set (<a href="#permutations" title=permutations>permutations</a> (xs <a href="#interleave" title=interleave>⫴</a> ys))

---
**t1**

&nbsp;&nbsp;&nbsp;&nbsp;size xs = size ys ⟹ ∀t∈set (zip xs ys). fst t ∈ set (<a href="#permutations" title=permutations>permutations</a> (snd t)) ⟹ concat xs ∈ set (<a href="#permutations" title=permutations>permutations</a> (concat ys))

---
**t15**

&nbsp;&nbsp;&nbsp;&nbsp;size xs = size ys ⟹ ∃xs'. xs' ∈ set (<a href="#permutations" title=permutations>permutations</a> xs) ∧ (∀t∈set (zip xs' ys). fst t ∈ set (<a href="#permutations" title=permutations>permutations</a> (snd t))) ⟹ concat xs ∈ set (<a href="#permutations" title=permutations>permutations</a> (concat ys))

---
**t2**

&nbsp;&nbsp;&nbsp;&nbsp;size [f x y. x ← xs, y ← ys] = size xs * size ys

---
**t3**

&nbsp;&nbsp;&nbsp;&nbsp;size [path_m <a href="#interleave" title=interleave>⫴</a> path_n. path_m ← xs, path_n ← ys] = size [path_m <a href="#interleave" title=interleave>⫴</a> path_n. path_m ← ys, path_n ← xs]

---
**index_prop**

&nbsp;&nbsp;&nbsp;&nbsp;length xs = a ⟹ (xs@ys)!(a+b) = ys!b

---
**index_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;a < length xs ⟹ xs!a = (xs@ys)!a

---
**index_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;size (concat (map (λx. f x y # map (f x) ys) xs)) = size xs * size (y#ys)

---
**list_comp_index**

&nbsp;&nbsp;&nbsp;&nbsp;x_ind < size xs ⟹ y_ind < size ys ⟹ [f x y. x ← xs, y ← ys] ! (x_ind * size ys + y_ind) = f (xs ! x_ind) (ys ! y_ind)

---
**interleave_ind_comp**

&nbsp;&nbsp;&nbsp;&nbsp;x_ind<size xs ⟹ y_ind<size ys ⟹ [path_m <a href="#interleave" title=interleave>⫴</a> path_n. path_m ← xs, path_n ← ys] ! ((x_ind* (size ys))+y_ind) = (xs ! x_ind) <a href="#interleave" title=interleave>⫴</a> (ys ! y_ind)

---
&nbsp;&nbsp;&nbsp;&nbsp;x_ind < size xs ⟹ y_ind < size ys ⟹ [path_m <a href="#interleave" title=interleave>⫴</a> path_n. path_m ← xs, path_n ← ys] ! ((x_ind* (size ys))+y_ind) = [path_m <a href="#interleave" title=interleave>⫴</a> path_n. path_m ← ys, path_n ← xs] ! ((y_ind* (size xs))+x_ind)

---
**all_elements_have_permutation**

&nbsp;&nbsp;&nbsp;&nbsp;x_ind < size xs ⟹ y_ind < size ys ⟹ [path_m <a href="#interleave" title=interleave>⫴</a> path_n. path_m ← xs, path_n ← ys] ! ((x_ind* (size ys))+y_ind) ∈ set (<a href="#permutations" title=permutations>permutations</a> ([path_m <a href="#interleave" title=interleave>⫴</a> path_n. path_m ← ys, path_n ← xs] ! ((y_ind* (size xs))+x_ind)))

---
**perm_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set (<a href="#permutations" title=permutations>permutations</a> xs') ⟹ ys  ∈ set (<a href="#permutations" title=permutations>permutations</a> ys') ⟹ xs@ys ∈ set (<a href="#permutations" title=permutations>permutations</a> (xs'@ys'))

---
**is_perm**

&nbsp;&nbsp;&nbsp;&nbsp;size xy = sx * sy ⟹ [xy ! ((x_ind*sy)+y_ind). x_ind ← [0..<sx], y_ind ← [0..<sy]] ∈ set (<a href="#permutations" title=permutations>permutations</a> xy)

---
**is_perm2**

&nbsp;&nbsp;&nbsp;&nbsp;size xy = size xs * size ys ⟹ [xy ! ((x_ind*(size ys))+y_ind). x_ind ← [0..<size xs], y_ind ← [0..<size ys]] ∈ set (<a href="#permutations" title=permutations>permutations</a> xy)

---
**index_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;i < size xs * size ys ⟹ concat (map (λx. map (f x) ys) xs) ! i = f (xs ! (i div length ys)) (ys ! (i mod length ys))

---
**index_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;concat (map (λx. map (f x) ys) xs) = [f (xs ! (i div length ys)) (ys ! (i mod length ys)). i ← [0..<size xs * size ys]]

---
**perm_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;[ ] ∈ set (<a href="#permutations" title=permutations>permutations</a> xy) ⟹ xy = [ ]

---
**perm_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;concat (map (λy. map (λx. f x y) [x]) (ys)) @ concat (map (λy. map (λx. f x y) xs) (ys)) ∈ set (<a href="#permutations" title=permutations>permutations</a> (concat (map (λy. map (λx. f x y) (x # xs)) (ys))))

---
**perm_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;[f x y. x ← xs, y ← ys] ∈ set (<a href="#permutations" title=permutations>permutations</a> xy) ⟹ [f x y. y ← ys, x ← xs] ∈ set (<a href="#permutations" title=permutations>permutations</a> xy)

---
**is_perm4**

&nbsp;&nbsp;&nbsp;&nbsp;size xy = sx * sy ⟹ [xy ! ((x_ind*sy)+y_ind). y_ind ← [0..<sy], x_ind ← [0..<sx]] ∈ set (<a href="#permutations" title=permutations>permutations</a> xy)

---
**perm_exists**

&nbsp;&nbsp;&nbsp;&nbsp;xy = [path_m <a href="#interleave" title=interleave>⫴</a> path_n. path_m ← xs, path_n ← ys] ⟹ yx = [path_m <a href="#interleave" title=interleave>⫴</a> path_n. path_m ← ys, path_n ← xs] ⟹ ∃xy'. xy' ∈ set (<a href="#permutations" title=permutations>permutations</a> xy) ∧ (∀t∈set (zip xy' yx). fst t ∈ set (<a href="#permutations" title=permutations>permutations</a> (snd t)))

---
**is_permutation**

&nbsp;&nbsp;&nbsp;&nbsp;(xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) ∈ set (<a href="#permutations" title=permutations>permutations</a> (ys <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> xs))

---
**t4**

&nbsp;&nbsp;&nbsp;&nbsp;size (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) = size (ys <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> xs)

---
**inter_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ <a href="#interleave" title=interleave>interleave</a> xs ys ≠ [ ]

---
**perm_is_equal**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set (<a href="#permutations" title=permutations>permutations</a> ys) ⟹ <a href="#evaluate" title=evaluate>evaluate</a> xs = <a href="#evaluate" title=evaluate>evaluate</a> ys

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) = <a href="#evaluate" title=evaluate>evaluate</a> (ys <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> xs)

---
## CNF_concurrency.thy

&nbsp;&nbsp;&nbsp;&nbsp;(a@b)∥c =(a∥c)@(b∥c)

---
**fact_eq**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#factorial" title=factorial>factorial</a> n = fact n

---
**factorial_mod_product**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#factorial" title=factorial>factorial</a> (a + b) mod (<a href="#factorial" title=factorial>factorial</a> a * <a href="#factorial" title=factorial>factorial</a> b) = (0::nat)

---
**factorial_bound**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#factorial" title=factorial>factorial</a> n > 0

---
**simp_div**

&nbsp;&nbsp;&nbsp;&nbsp;a mod b = 0 ⟹ c mod b = 0 ⟹ (a::nat) div b + c div b = (a + c) div b

---
**exits_mulit**

&nbsp;&nbsp;&nbsp;&nbsp;∃t::nat. n*t=m ⟹ m mod n = 0

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#nmb_interleavings_pre" title=nmb_interleavings_pre>nmb_interleavings_pre</a> (<a href="#nmb_interleavings_pre" title=nmb_interleavings_pre>nmb_interleavings_pre</a> x y) z = <a href="#nmb_interleavings_pre" title=nmb_interleavings_pre>nmb_interleavings_pre</a> x (<a href="#nmb_interleavings_pre" title=nmb_interleavings_pre>nmb_interleavings_pre</a> y z)

---
**number_interleav**

&nbsp;&nbsp;&nbsp;&nbsp;length (xs <a href="#interleave" title=interleave>⫴</a> ys) = <a href="#nmb_interleavings" title=nmb_interleavings>nmb_interleavings</a> xs ys

---
**monoton_fact**

&nbsp;&nbsp;&nbsp;&nbsp;a &lt; b ⟹ <a href="#factorial" title=factorial>factorial</a> a &lt; <a href="#factorial" title=factorial>factorial</a> b

---
**interleave_size**

&nbsp;&nbsp;&nbsp;&nbsp;size xs * size ys &lt; size (xs <a href="#interleave" title=interleave>⫴</a> ys)

---
**list_comp_size**

&nbsp;&nbsp;&nbsp;&nbsp;size [f path_m path_n. path_m ← xs, path_n ← ys] &gt; size xs * size ys

---
**interleav_lower_bound**

&nbsp;&nbsp;&nbsp;&nbsp;size (xs <a href="#interleave" title=interleave>⫴</a> ys) &gt; 1

---
**concat_prop**

&nbsp;&nbsp;&nbsp;&nbsp;∀x ∈ set xs. size x &gt; 1 ⟹ size (concat xs) &gt; size xs

---
**conc_size**

&nbsp;&nbsp;&nbsp;&nbsp;size xs * size ys &lt; size (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys)

---
**size_one1**

&nbsp;&nbsp;&nbsp;&nbsp;size (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) = 1 ⟹ size xs = 1

---
**size_one2**

&nbsp;&nbsp;&nbsp;&nbsp;size (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) = 1 ⟹ size ys = 1

---
**sum_1**

&nbsp;&nbsp;&nbsp;&nbsp;size (concat xs) = <a href="#sum" title=sum>sum</a> [size x. x←xs]

---
**path_decomp**

&nbsp;&nbsp;&nbsp;&nbsp;path ∈ set (p <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> q) ⟹ ∃path_p path_q. path_p ∈ set p ∧ path_q ∈ set q ∧ path ∈ set (path_p <a href="#interleave" title=interleave>⫴</a> path_q)

---
**path_decomp2**

&nbsp;&nbsp;&nbsp;&nbsp;path_p ∈ set p ⟹ path_q ∈ set q ⟹ path ∈ set (path_p <a href="#interleave" title=interleave>⫴</a> path_q) ⟹ path ∈ set (p <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> q)

---
**inter_leav1**

&nbsp;&nbsp;&nbsp;&nbsp;(p#path) ∈ set ((x#xs) <a href="#interleave" title=interleave>⫴</a> (y#ys)) ⟹ ((p=x) ∧ path ∈ set (xs <a href="#interleave" title=interleave>⫴</a> (y#ys))) ∨ ((p=y) ∧ path ∈ set ((x#xs) <a href="#interleave" title=interleave>⫴</a> (ys)))

---
**inter_leav2**

&nbsp;&nbsp;&nbsp;&nbsp;((p=y) ∧ path ∈ set ((x#xs) <a href="#interleave" title=interleave>⫴</a> (ys))) ⟹ (p#path) ∈ set ((x#xs) <a href="#interleave" title=interleave>⫴</a> (y#ys))

---
**inter_leav3**

&nbsp;&nbsp;&nbsp;&nbsp;((p=x) ∧ path ∈ set (xs <a href="#interleave" title=interleave>⫴</a> (y#ys))) ⟹ (p#path) ∈ set ((x#xs) <a href="#interleave" title=interleave>⫴</a> (y#ys))

---
**conc_lem1**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) = ⋃ {set (path_x <a href="#interleave" title=interleave>⫴</a> path_y) |path_x path_y. path_x ∈ set xs ∧ path_y ∈ set ys}

---
&nbsp;&nbsp;&nbsp;&nbsp;set ((x#xs) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) = set ([x]∥ys) ∪ set (xs∥ys)

---
**assoc_1**

&nbsp;&nbsp;&nbsp;&nbsp;set (([x] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [y]) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [z]) ⊆ set ([x] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ([y] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [z]))

---
**assoc_2**

&nbsp;&nbsp;&nbsp;&nbsp;set ([x] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ([y] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [z])) ⊆ set (([x] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [y]) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [z])

---
**assoc_3**

&nbsp;&nbsp;&nbsp;&nbsp;set (([x] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [y]) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [z]) ⊆ set (((x#xs) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (y#ys)) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (z#zs))

---
**assoc_4**

&nbsp;&nbsp;&nbsp;&nbsp;set ([x] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ([y] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [z])) ⊆ set ((x#xs) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ((y#ys) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (z#zs)))

---
**assoc_5**

&nbsp;&nbsp;&nbsp;&nbsp;set xs = set xs' ⟹ set ys = set ys' ⟹ set (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) = set (xs' <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys')

---
**assoc_6**

&nbsp;&nbsp;&nbsp;&nbsp;y ∈ set ys ⟹ x ∈ set xs ⟹ set ((x#xs) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (y#ys)) =  set ((xs) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (ys))

---
**assoc_7**

&nbsp;&nbsp;&nbsp;&nbsp;set ((xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs) ⊆ set (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (ys <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs))

---
**assoc_8**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (ys <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs)) ⊆ set ((xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs)

---
**assoc_9**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (ys <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs)) = set ((xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs)

---
**inter_size**

&nbsp;&nbsp;&nbsp;&nbsp;size (x <a href="#interleave" title=interleave>⫴</a> y) > 0" apply (cases "x=[ ]

---
**inter_size2**

&nbsp;&nbsp;&nbsp;&nbsp;size (x <a href="#interleave" title=interleave>⫴</a> y) = 1 ⟹ size x = 0 ∨ size y = 0

---
**inter_size3**

&nbsp;&nbsp;&nbsp;&nbsp;size x = 0 ∨ size y = 0 ⟹ size (x <a href="#interleave" title=interleave>⫴</a> y) = 1

---
**interleaving_lemma**

&nbsp;&nbsp;&nbsp;&nbsp;size ([x] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [y]) =  <a href="#nmb_interleavings_pre" title=nmb_interleavings_pre>nmb_interleavings_pre</a> (size x) (size y)

---
**inter_size4**

&nbsp;&nbsp;&nbsp;&nbsp;size (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) = 1 ⟹ size xs = 1 ∨ size ys = 1

---
**conc_prop**

&nbsp;&nbsp;&nbsp;&nbsp;xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [[ ]] = xs

---
**conc_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;[[ ]] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> xs = xs

---
**assoc_10**

&nbsp;&nbsp;&nbsp;&nbsp;size (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (ys <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs)) = 1 ⟹ size ((xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs) = 1

---
**assoc_11**

&nbsp;&nbsp;&nbsp;&nbsp;size ((xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs) = 1 ⟹ size (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (ys <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs)) = 1

---
**assoc_12**

&nbsp;&nbsp;&nbsp;&nbsp;size (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (ys <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs)) = 1 ≡ size ((xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs) = 1

---
**assoc_cnf1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#equal_cnf" title=equal_cnf>equal_cnf</a> ((xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs)  (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (ys <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs))

---
**assoc_cnf**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> ((xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs) = <a href="#evaluate" title=evaluate>evaluate</a> (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (ys <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs))

---
**cnf_prop**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ <a href="#evaluate" title=evaluate>evaluate</a> [x#xs] C = x <a href="#composition" title=composition>;</a> (<a href="#evaluate" title=evaluate>evaluate</a> [xs] C)

---
**cnf_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ <a href="#evaluate" title=evaluate>evaluate</a> [xs@[x]] C = (<a href="#evaluate" title=evaluate>evaluate</a> [xs] C) <a href="#composition" title=composition>;</a> x

---
**restrict_cnf1**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ <a href="#evaluate" title=evaluate>evaluate</a> ([x] <a href="#restriction_cnf" title=restriction_cnf>/</a> C) D = (<a href="#evaluate" title=evaluate>evaluate</a> [x] D) <a href="#restrict_p" title=restrict_p>/</a> C

---
**restr_distrib**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#restrict_p" title=restrict_p>/</a> C <a href="#choice" title=choice>∪</a> b <a href="#restrict_p" title=restrict_p>/</a> C = (a <a href="#choice" title=choice>∪</a> b) <a href="#restrict_p" title=restrict_p>/</a> C

---
**restrict_cnf**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ <a href="#evaluate" title=evaluate>evaluate</a> (xs <a href="#restriction_cnf" title=restriction_cnf>/</a> C) D = (<a href="#evaluate" title=evaluate>evaluate</a> xs D) <a href="#restrict_p" title=restrict_p>/</a> C

---
**corestrict_cnf1**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ <a href="#evaluate" title=evaluate>evaluate</a> ([x] <a href="#corestriction_cnf" title=corestriction_cnf>∖</a> C) D = (<a href="#evaluate" title=evaluate>evaluate</a> [x] D) <a href="#corestrict_p" title=corestrict_p>∖</a> C

---
**corestrict_cnf**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ <a href="#evaluate" title=evaluate>evaluate</a> (xs <a href="#corestriction_cnf" title=corestriction_cnf>∖</a> C) D= (<a href="#evaluate" title=evaluate>evaluate</a> xs D) <a href="#corestrict_p" title=corestrict_p>∖</a> C

---
**conc_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) ⊆ set (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (y#ys))

---
**conc_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) ⊆ set (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (ys <a href="#choice_cnf" title=choice_cnf>∪</a> zs))

---
**conc_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (ys <a href="#choice_cnf" title=choice_cnf>∪</a> zs)) = set (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (zs <a href="#choice_cnf" title=choice_cnf>∪</a> ys))

---
**conc_choice1_1**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (ys <a href="#choice_cnf" title=choice_cnf>∪</a> zs)) = set ((xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) <a href="#choice_cnf" title=choice_cnf>∪</a> (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs))

---
**choice_size1**

&nbsp;&nbsp;&nbsp;&nbsp;size (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (ys <a href="#choice_cnf" title=choice_cnf>∪</a> zs)) = 1 ⟹ size ((xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) <a href="#choice_cnf" title=choice_cnf>∪</a> (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs)) = 1

---
**choice_size2**

&nbsp;&nbsp;&nbsp;&nbsp;size ((xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) <a href="#choice_cnf" title=choice_cnf>∪</a> (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs)) = 1 ⟹ size (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (ys <a href="#choice_cnf" title=choice_cnf>∪</a> zs)) = 1

---
**Conc_choice1_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#equal_cnf" title=equal_cnf>equal_cnf</a> ((xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) <a href="#choice_cnf" title=choice_cnf>∪</a> (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs)) (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (ys <a href="#choice_cnf" title=choice_cnf>∪</a> zs))

---
**Conc_choice1_**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> ((xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) <a href="#choice_cnf" title=choice_cnf>∪</a> (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs)) = <a href="#evaluate" title=evaluate>evaluate</a> (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (ys <a href="#choice_cnf" title=choice_cnf>∪</a> zs))

---
**conc_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) ⊆ set ((x#xs) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys)

---
**conc_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) ⊆ set ((xs <a href="#choice_cnf" title=choice_cnf>∪</a> zs) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys)

---
**conc_prop7**

&nbsp;&nbsp;&nbsp;&nbsp;set ((zs <a href="#choice_cnf" title=choice_cnf>∪</a> xs) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) = set ((xs <a href="#choice_cnf" title=choice_cnf>∪</a> zs) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys)

---
**conc_choice2_1**

&nbsp;&nbsp;&nbsp;&nbsp;set ((xs <a href="#choice_cnf" title=choice_cnf>∪</a> ys) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs) = set ((xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs) <a href="#choice_cnf" title=choice_cnf>∪</a> (ys <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs))

---
**choice_size3**

&nbsp;&nbsp;&nbsp;&nbsp;size ((xs <a href="#choice_cnf" title=choice_cnf>∪</a> ys) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs) = 1 ⟹ size ((xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs) <a href="#choice_cnf" title=choice_cnf>∪</a> (ys <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs)) = 1

---
**choice_size4**

&nbsp;&nbsp;&nbsp;&nbsp;size ((xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs) <a href="#choice_cnf" title=choice_cnf>∪</a> (ys <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs)) = 1 ⟹ size ((xs <a href="#choice_cnf" title=choice_cnf>∪</a> ys) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs) = 1

---
**Conc_choice2_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#equal_cnf" title=equal_cnf>equal_cnf</a> ((xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs) <a href="#choice_cnf" title=choice_cnf>∪</a> (ys <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs)) ((xs <a href="#choice_cnf" title=choice_cnf>∪</a> ys) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs)

---
**Conc_choice2_**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> ((xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs) <a href="#choice_cnf" title=choice_cnf>∪</a> (ys <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs)) = <a href="#evaluate" title=evaluate>evaluate</a> ((xs <a href="#choice_cnf" title=choice_cnf>∪</a> ys) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> zs)

---
**eval_specialize**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> ys C <a href="#specialize" title=specialize>⊆</a> <a href="#evaluate" title=evaluate>evaluate</a> (y # ys) C

---
**eval_specialize2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> [y] C <a href="#specialize" title=specialize>⊆</a> <a href="#evaluate" title=evaluate>evaluate</a> (y # ys) C

---
**eval_specialize3**

&nbsp;&nbsp;&nbsp;&nbsp;set xs ⊆ set [y] ⟹ <a href="#evaluate" title=evaluate>evaluate</a> xs C <a href="#specialize" title=specialize>⊆</a> <a href="#evaluate" title=evaluate>evaluate</a> [y] C

---
**eval_specialize4**

&nbsp;&nbsp;&nbsp;&nbsp;set [x] ⊆ set ys ⟹ <a href="#evaluate" title=evaluate>evaluate</a> [x] C <a href="#specialize" title=specialize>⊆</a> <a href="#evaluate" title=evaluate>evaluate</a> ys C

---
**eval_specialize5**

&nbsp;&nbsp;&nbsp;&nbsp;size xs > 1 ⟹ <a href="#equal_cnf" title=equal_cnf>equal_cnf</a> xs zs ⟹ <a href="#evaluate" title=evaluate>evaluate</a> xs C = <a href="#evaluate" title=evaluate>evaluate</a> [ ] C <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> zs C

---
**eval_specialize6**

&nbsp;&nbsp;&nbsp;&nbsp;size (ys @ zs) > 1 ⟹ <a href="#evaluate" title=evaluate>evaluate</a> ys C <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> zs C = <a href="#evaluate" title=evaluate>evaluate</a> (ys <a href="#choice_cnf" title=choice_cnf>∪</a> zs) C

---
**eval_specialize7**

&nbsp;&nbsp;&nbsp;&nbsp;size xs ≠ 1 ⟹ <a href="#equal_cnf" title=equal_cnf>equal_cnf</a> xs (ys <a href="#choice_cnf" title=choice_cnf>∪</a> zs) ⟹ <a href="#evaluate" title=evaluate>evaluate</a> xs C = <a href="#evaluate" title=evaluate>evaluate</a> ys C <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> zs C

---
**eval_specialize8**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> [x. x ← xs, f x] C <a href="#specialize" title=specialize>⊆</a> <a href="#evaluate" title=evaluate>evaluate</a> xs C

---
**eval_specialize9**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> [x. x ← (x#xx#xs), f x] C <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> [x. x ← x#xx#xs, ¬ f x] C = (<a href="#evaluate" title=evaluate>evaluate</a> [x] C <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> [xx] C) <a href="#choice" title=choice>∪</a> (<a href="#evaluate" title=evaluate>evaluate</a> [x. x ← (xs), f x] C <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> [x. x ← xs, ¬ f x] C)

---
**eval_specialize10**

&nbsp;&nbsp;&nbsp;&nbsp;(<a href="#evaluate" title=evaluate>evaluate</a> [x] C <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> [xx] C) <a href="#choice" title=choice>∪</a> (<a href="#evaluate" title=evaluate>evaluate</a> [x. x ← (xs), f x] C <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> [x. x ← xs, ¬ f x] C) = (<a href="#evaluate" title=evaluate>evaluate</a> [x] C <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> [xx] C) <a href="#choice" title=choice>∪</a> (<a href="#evaluate" title=evaluate>evaluate</a> xs C)

---
**eval_specialize11**

&nbsp;&nbsp;&nbsp;&nbsp;size xs > 1 ⟹ <a href="#evaluate" title=evaluate>evaluate</a> [x. x ← xs, f x] C <a href="#choice" title=choice>∪</a> <a href="#evaluate" title=evaluate>evaluate</a> [x. x ← xs, ¬ f x] C = <a href="#evaluate" title=evaluate>evaluate</a> xs C

---
**eval_specialize12**

&nbsp;&nbsp;&nbsp;&nbsp;set xs ⊆ set ys ⟹ <a href="#evaluate" title=evaluate>evaluate</a> xs C⊆ <a href="#evaluate" title=evaluate>evaluate</a> ys C

---
**subset1**

&nbsp;&nbsp;&nbsp;&nbsp;set (p <a href="#composition_cnf" title=composition_cnf>;</a> xs) ⊆ set (p <a href="#composition_cnf" title=composition_cnf>;</a> (x#xs))

---
**subset2**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs <a href="#composition_cnf" title=composition_cnf>;</a> p) ⊆ set ((x#xs) <a href="#composition_cnf" title=composition_cnf>;</a> p)

---
**subset3**

&nbsp;&nbsp;&nbsp;&nbsp;set (p <a href="#choice_cnf" title=choice_cnf>∪</a> xs) ⊆ set (p <a href="#choice_cnf" title=choice_cnf>∪</a> (x#xs))

---
**subset4**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs <a href="#choice_cnf" title=choice_cnf>∪</a> p) ⊆ set ((x#xs) <a href="#choice_cnf" title=choice_cnf>∪</a> p)

---
**subset5**

&nbsp;&nbsp;&nbsp;&nbsp;set q ⊆ set q' ⟹ set (p <a href="#composition_cnf" title=composition_cnf>;</a> q) ⊆ set (p <a href="#composition_cnf" title=composition_cnf>;</a> q')

---
**subset6**

&nbsp;&nbsp;&nbsp;&nbsp;set q ⊆ set q' ⟹ set (q <a href="#composition_cnf" title=composition_cnf>;</a> p) ⊆ set (q' <a href="#composition_cnf" title=composition_cnf>;</a> p)

---
**subset7**

&nbsp;&nbsp;&nbsp;&nbsp;set q ⊆ set q' ⟹ set (p <a href="#choice_cnf" title=choice_cnf>∪</a> q) ⊆ set (p <a href="#choice_cnf" title=choice_cnf>∪</a> q')

---
**subset8**

&nbsp;&nbsp;&nbsp;&nbsp;set q ⊆ set q' ⟹ set (q <a href="#choice_cnf" title=choice_cnf>∪</a> p) ⊆ set (q' <a href="#choice_cnf" title=choice_cnf>∪</a> p)

---
**subset9**

&nbsp;&nbsp;&nbsp;&nbsp;set q ⊆ set q' ⟹ set (p <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> q) ⊆ set (p <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> q')

---
**subset10**

&nbsp;&nbsp;&nbsp;&nbsp;set q ⊆ set q' ⟹ set (q <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> p) ⊆ set (q' <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> p)

---
**interleav_prop**

&nbsp;&nbsp;&nbsp;&nbsp;ps @ rs ∈ set (ps <a href="#interleave" title=interleave>⫴</a> rs)

---
**prop5**

&nbsp;&nbsp;&nbsp;&nbsp;set (map (λxs. xs @ [p]) (ps <a href="#interleave" title=interleave>⫴</a> (qs @ [q]))) = {tr @ [p] |tr. tr ∈ set (ps <a href="#interleave" title=interleave>⫴</a> (qs @ [q]))}

---
**prop6**

&nbsp;&nbsp;&nbsp;&nbsp;set (map (λxs. xs @ [q]) ((ps @ [p]) <a href="#interleave" title=interleave>⫴</a> qs )) = {tr @ [q] |tr. tr ∈ set ((ps @ [p]) <a href="#interleave" title=interleave>⫴</a> qs)}

---
**prop3_1**

&nbsp;&nbsp;&nbsp;&nbsp;[x] <a href="#interleave" title=interleave>⫴</a> ys = <a href="#insert_all" title=insert_all>insert_all</a> x ys

---
**prop3_2**

&nbsp;&nbsp;&nbsp;&nbsp;ys <a href="#interleave" title=interleave>⫴</a> [x] = rev (<a href="#insert_all" title=insert_all>insert_all</a> x ys)

---
**prop3_3**

&nbsp;&nbsp;&nbsp;&nbsp;set ([x] <a href="#interleave" title=interleave>⫴</a> (y#ys)) = {x#y#ys} ∪ {y#x#ys} ∪ ((#) y) ` set ([x] <a href="#interleave" title=interleave>⫴</a> ys)

---
**prop3_4**

&nbsp;&nbsp;&nbsp;&nbsp;set ([x] <a href="#interleave" title=interleave>⫴</a> (ys@[y])) = {ys@[x,y]} ∪ {ys@[y,x]} ∪ (λtr. tr@[y]) ` set ([x] <a href="#interleave" title=interleave>⫴</a> ys)

---
**prop3_5**

&nbsp;&nbsp;&nbsp;&nbsp;set ([x] <a href="#interleave" title=interleave>⫴</a> rev (y#ys)) = {(rev ys)@[x,y]} ∪ {(rev ys)@[y,x]} ∪ (λtr. tr@[y]) ` set ([x] <a href="#interleave" title=interleave>⫴</a> (rev ys))

---
**prop3_6**

&nbsp;&nbsp;&nbsp;&nbsp;{rev tr |tr. tr ∈ set ([x] <a href="#interleave" title=interleave>⫴</a> (ys))} = set ([x] <a href="#interleave" title=interleave>⫴</a> rev ys)

---
**prop3_7**

&nbsp;&nbsp;&nbsp;&nbsp;rev ` set ([x] <a href="#interleave" title=interleave>⫴</a> ys) = set ([x] <a href="#interleave" title=interleave>⫴</a> rev ys)

---
**prop3_8**

&nbsp;&nbsp;&nbsp;&nbsp;(λtr. tr @ [y]) ` set ([x] <a href="#interleave" title=interleave>⫴</a> ys) ⊆ set ([x] <a href="#interleave" title=interleave>⫴</a> (ys @ [y]))

---
**prop3_9**

&nbsp;&nbsp;&nbsp;&nbsp;tr ∈ set ([x] <a href="#interleave" title=interleave>⫴</a> rev ys) ⟹ tr @ [y] ∈ set ([x] <a href="#interleave" title=interleave>⫴</a> (rev ys @ [y]))

---
**prop3_10**

&nbsp;&nbsp;&nbsp;&nbsp;(map (λzs. zs@[y]) (<a href="#insert_all" title=insert_all>insert_all</a> x ys)) @ [ys@[y,x]] = <a href="#insert_all" title=insert_all>insert_all</a> x (ys@[y])

---
**prop3_10_1**

&nbsp;&nbsp;&nbsp;&nbsp;map (λtr. tr @ [y]) ([x] <a href="#interleave" title=interleave>⫴</a> ys) @ [ys@[y,x]] = <a href="#insert_all" title=insert_all>insert_all</a> x (ys@[y])

---
**prop3_11**

&nbsp;&nbsp;&nbsp;&nbsp;xa ∈ set ([x] <a href="#interleave" title=interleave>⫴</a> (rev ys @ [y])) ⟹ xa ∉ (λtr. tr @ [y]) ` set ([x] <a href="#interleave" title=interleave>⫴</a> rev ys) ⟹ xa = rev ys @ [y, x]

---
**prop3_12**

&nbsp;&nbsp;&nbsp;&nbsp;x≠y ⟹ set (map ((#) y) ((x#xs) <a href="#interleave" title=interleave>⫴</a> ys)) ∩ set (map ((#) x) (xs <a href="#interleave" title=interleave>⫴</a> (y#ys))) = {}

---
**prop3_13**

&nbsp;&nbsp;&nbsp;&nbsp;x≠y ⟹ set (map ((#) x) (xs <a href="#interleave" title=interleave>⫴</a> (y#ys))) = set ((x#xs) <a href="#interleave" title=interleave>⫴</a> (y#ys)) - set (map ((#) y) ((x#xs) <a href="#interleave" title=interleave>⫴</a> ys))

---
**prop3_14**

&nbsp;&nbsp;&nbsp;&nbsp;(x#xs) <a href="#interleave" title=interleave>⫴</a> (x#ys) = map ((#) x) ((xs <a href="#interleave" title=interleave>⫴</a> (x#ys)) @ ((x#xs) <a href="#interleave" title=interleave>⫴</a> ys))

---
**prop3_15**

&nbsp;&nbsp;&nbsp;&nbsp;set [(xs @ [x, y])] ∪ (λtr. tr @ [x]) ` set ((xs <a href="#interleave" title=interleave>⫴</a> [y])) = set (((xs @ [x]) <a href="#interleave" title=interleave>⫴</a> [y]))

---
**prop3_16**

&nbsp;&nbsp;&nbsp;&nbsp;set (map (λtr. tr@[y]) (rev (x#xs) <a href="#interleave" title=interleave>⫴</a> rev ys)) ∪ set (map (λtr. tr@[x]) (rev xs <a href="#interleave" title=interleave>⫴</a> rev (y#ys))) = set (rev (x # xs) <a href="#interleave" title=interleave>⫴</a> rev (y # ys))

---
**prop3**

&nbsp;&nbsp;&nbsp;&nbsp;set (map rev (xs <a href="#interleave" title=interleave>⫴</a> ys)) = set (rev xs <a href="#interleave" title=interleave>⫴</a> rev ys)

---
**prop4**

&nbsp;&nbsp;&nbsp;&nbsp;set ((ps @ [p]) <a href="#interleave" title=interleave>⫴</a> (qs @ [q])) = {tr @ [p] |tr. tr ∈ set (ps <a href="#interleave" title=interleave>⫴</a> (qs @ [q]))} ∪ {tr @ [q] |tr. tr ∈ set ((ps @ [p]) <a href="#interleave" title=interleave>⫴</a> qs)}

---
**prop7**

&nbsp;&nbsp;&nbsp;&nbsp;set ((ps@[p]) <a href="#interleave" title=interleave>⫴</a> (qs@[q])) = set (map (λxs. xs@[p]) (ps <a href="#interleave" title=interleave>⫴</a> (qs@[q])) @ map (λxs. xs@[q]) ((ps@[p]) <a href="#interleave" title=interleave>⫴</a> qs))

---
**prop8**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set ys ⟹ xs@[x] ∈ set (map (λt. t@[x]) ys)

---
**prop9**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set (p <a href="#interleave" title=interleave>⫴</a> q) ⟹ xs @ r ∈ set (p <a href="#interleave" title=interleave>⫴</a> (q @ r))

---
**prop9_1**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set ((p <a href="#interleave" title=interleave>⫴</a> r)) ⟹ q @ xs ∈  set (p <a href="#interleave" title=interleave>⫴</a> (q @ r))

---
**prop10**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [q] <a href="#composition_cnf" title=composition_cnf>;</a> [r]) ⊆ set ([p] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ([q] <a href="#composition_cnf" title=composition_cnf>;</a> [r]))

---
**prop10_1**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [r] <a href="#composition_cnf" title=composition_cnf>;</a> [q]) ⊆ set (([p] <a href="#composition_cnf" title=composition_cnf>;</a> [q]) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [r])

---
**prop10_2**

&nbsp;&nbsp;&nbsp;&nbsp;set ([q] <a href="#composition_cnf" title=composition_cnf>;</a> [p] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [r]) ⊆ set ([p] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ([q] <a href="#composition_cnf" title=composition_cnf>;</a> [r]))

---
**prop10_3**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] <a href="#composition_cnf" title=composition_cnf>;</a> [q] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [r]) ⊆ set (([p] <a href="#composition_cnf" title=composition_cnf>;</a> [q]) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [r])

---
**inter1**

&nbsp;&nbsp;&nbsp;&nbsp;set ((ps <a href="#interleave" title=interleave>⫴</a> qs) <a href="#composition_cnf" title=composition_cnf>;</a> (rs <a href="#interleave" title=interleave>⫴</a> vs)) ⊆ set ((ps @ rs) <a href="#interleave" title=interleave>⫴</a> (qs @ vs))

---
**prop10_3_1**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [q] <a href="#composition_cnf" title=composition_cnf>;</a> [r] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [v]) ⊆ set (([p] <a href="#composition_cnf" title=composition_cnf>;</a> [r]) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ([q] <a href="#composition_cnf" title=composition_cnf>;</a> [v]))

---
**prop10_4**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [q] <a href="#composition_cnf" title=composition_cnf>;</a> [r] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> vs) ⊆ set (([p] <a href="#composition_cnf" title=composition_cnf>;</a> [r]) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ([q] <a href="#composition_cnf" title=composition_cnf>;</a> vs))

---
**prop11**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> qs <a href="#composition_cnf" title=composition_cnf>;</a> [r]) ⊆ set ([p] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (qs <a href="#composition_cnf" title=composition_cnf>;</a> [r]))

---
**prop12**

&nbsp;&nbsp;&nbsp;&nbsp;set (([p] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> rs) <a href="#composition_cnf" title=composition_cnf>;</a> [q]) ⊆ set (([p] <a href="#composition_cnf" title=composition_cnf>;</a> [q]) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> rs)

---
**prop13**

&nbsp;&nbsp;&nbsp;&nbsp;set ([q] <a href="#composition_cnf" title=composition_cnf>;</a> [p] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> rs) ⊆ set ([p] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ([q] <a href="#composition_cnf" title=composition_cnf>;</a> rs))

---
**prop14**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] <a href="#composition_cnf" title=composition_cnf>;</a> qs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [r]) ⊆ set (([p] <a href="#composition_cnf" title=composition_cnf>;</a> qs) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [r])

---
**prop15**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ([q]) <a href="#composition_cnf" title=composition_cnf>;</a> rs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> s) ⊆ set (([p] <a href="#composition_cnf" title=composition_cnf>;</a> rs) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ([q] <a href="#composition_cnf" title=composition_cnf>;</a> s))

---
**subset12**

&nbsp;&nbsp;&nbsp;&nbsp;set (ps <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> q <a href="#composition_cnf" title=composition_cnf>;</a> [r]) ⊆ set (ps <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (q <a href="#composition_cnf" title=composition_cnf>;</a> [r]))

---
**subset13**

&nbsp;&nbsp;&nbsp;&nbsp;set ((ps <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> r) <a href="#composition_cnf" title=composition_cnf>;</a> [q]) ⊆ set ((ps <a href="#composition_cnf" title=composition_cnf>;</a> [q]) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> r)

---
**subset14**

&nbsp;&nbsp;&nbsp;&nbsp;set ([q] <a href="#composition_cnf" title=composition_cnf>;</a> ps <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> r) ⊆ set (ps <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ([q] <a href="#composition_cnf" title=composition_cnf>;</a> r))

---
**subset15**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] <a href="#composition_cnf" title=composition_cnf>;</a> q <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> rs) ⊆ set (([p] <a href="#composition_cnf" title=composition_cnf>;</a> q) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> rs)

---
**subset16**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> qs <a href="#composition_cnf" title=composition_cnf>;</a> r <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> s) ⊆ set (([p] <a href="#composition_cnf" title=composition_cnf>;</a> r) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (qs <a href="#composition_cnf" title=composition_cnf>;</a> s))

---
**Conc_composeright_1**

&nbsp;&nbsp;&nbsp;&nbsp;set ((p <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> q) <a href="#composition_cnf" title=composition_cnf>;</a> rs) ⊆ set (p <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (q <a href="#composition_cnf" title=composition_cnf>;</a> rs))

---
**Conc_composeright1_1**

&nbsp;&nbsp;&nbsp;&nbsp;set ((p <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> r) <a href="#composition_cnf" title=composition_cnf>;</a> qs) ⊆ set ((p <a href="#composition_cnf" title=composition_cnf>;</a> qs) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> r)

---
**Conc_composeleft1_1**

&nbsp;&nbsp;&nbsp;&nbsp;set (qs <a href="#composition_cnf" title=composition_cnf>;</a> (p <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> r)) ⊆ set (p <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (qs <a href="#composition_cnf" title=composition_cnf>;</a> r))

---
**Conc_composeright_2**

&nbsp;&nbsp;&nbsp;&nbsp;set (ps <a href="#composition_cnf" title=composition_cnf>;</a> (q <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> r)) ⊆ set ((ps <a href="#composition_cnf" title=composition_cnf>;</a> q) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> r)

---
**Conc_composeleft**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> ((p <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> q) <a href="#composition_cnf" title=composition_cnf>;</a> r) C <a href="#specialize" title=specialize>⊆</a> <a href="#evaluate" title=evaluate>evaluate</a> (p <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (q <a href="#composition_cnf" title=composition_cnf>;</a> r)) C

---
**Conc_composeleftright**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> (q <a href="#composition_cnf" title=composition_cnf>;</a> (p <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> r)) C <a href="#specialize" title=specialize>⊆</a> <a href="#evaluate" title=evaluate>evaluate</a> (p <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (q <a href="#composition_cnf" title=composition_cnf>;</a> r)) C

---
**Conc_composeright**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> (p <a href="#composition_cnf" title=composition_cnf>;</a> (q <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> r)) C <a href="#specialize" title=specialize>⊆</a> <a href="#evaluate" title=evaluate>evaluate</a> ((p <a href="#composition_cnf" title=composition_cnf>;</a> q) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> r) C

---
**Conc_composerightleft**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> ((p <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> r) <a href="#composition_cnf" title=composition_cnf>;</a> q) C <a href="#specialize" title=specialize>⊆</a> <a href="#evaluate" title=evaluate>evaluate</a> ((p <a href="#composition_cnf" title=composition_cnf>;</a> q) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> r) C

---
**Conc_composegeneral**

&nbsp;&nbsp;&nbsp;&nbsp;set (([p] <a href="#composition_cnf" title=composition_cnf>;</a> [q]) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ([u] <a href="#composition_cnf" title=composition_cnf>;</a> [v])) ⊆ set (([p] <a href="#composition_cnf" title=composition_cnf>;</a> [u]) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ([q] <a href="#composition_cnf" title=composition_cnf>;</a> [v]))

---
**Conc_composegeneral**

&nbsp;&nbsp;&nbsp;&nbsp;set (([p] <a href="#composition_cnf" title=composition_cnf>;</a> [u]) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ([q] <a href="#composition_cnf" title=composition_cnf>;</a> [v])) ⊆ set (([p] <a href="#composition_cnf" title=composition_cnf>;</a> [q]) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ([u] <a href="#composition_cnf" title=composition_cnf>;</a> [v]))

---
**Conc_composegeneral**

&nbsp;&nbsp;&nbsp;&nbsp;set ((p <a href="#composition_cnf" title=composition_cnf>;</a> q) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (u <a href="#composition_cnf" title=composition_cnf>;</a> v)) ⊆ set ((p <a href="#composition_cnf" title=composition_cnf>;</a> u) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (q <a href="#composition_cnf" title=composition_cnf>;</a> v))

---
**Conc_composegeneral_1**

&nbsp;&nbsp;&nbsp;&nbsp;set ((ps <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> q) <a href="#composition_cnf" title=composition_cnf>;</a> (r <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> s)) ⊆ set ((ps <a href="#composition_cnf" title=composition_cnf>;</a> r) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (q <a href="#composition_cnf" title=composition_cnf>;</a> s))

---
**Conc_composegeneral**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#evaluate" title=evaluate>evaluate</a> ((p <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> q) <a href="#composition_cnf" title=composition_cnf>;</a> (r <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> s)) C <a href="#specialize" title=specialize>⊆</a> <a href="#evaluate" title=evaluate>evaluate</a> ((p <a href="#composition_cnf" title=composition_cnf>;</a> r) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> (q <a href="#composition_cnf" title=composition_cnf>;</a> s)) C

---
&nbsp;&nbsp;&nbsp;&nbsp;foldl (+) (b::nat) xs = b + foldl (+) 0 xs

---
**cnf_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#cnf_concurrency2" title=cnf_concurrency2>cnf_concurrency2</a> [[x]] [[y]] C = <a href="#evaluate" title=evaluate>evaluate</a> ([x] <a href="#interleave" title=interleave>⫴</a> [y]) C

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_rounded" title=is_rounded>is_rounded</a> a ⟹ (a <a href="#composition" title=composition>;</a> b) <a href="#choice" title=choice>∪</a> (a <a href="#composition" title=composition>;</a> c) = a <a href="#composition" title=composition>;</a> (b <a href="#choice" title=choice>∪</a> c)

---
**cnf2_prop**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#cnf_feasible" title=cnf_feasible>cnf_feasible</a> ([y]#ys) ⟹ <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> ([y]#ys) ⊆ C ⟹ <a href="#Choice" title=Choice>⋃</a> (map ((λxs. <a href="#Concat" title=Concat>Concat</a> xs C) ∘ (#) y) (ys)) <a href="#equiv" title=equiv>≡</a> y <a href="#composition" title=composition>;</a> <a href="#Choice" title=Choice>⋃</a> (map (λxs. <a href="#Concat" title=Concat>Concat</a> xs C) (ys))

---
**cnf2_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#cnf_feasible" title=cnf_feasible>cnf_feasible</a> xs ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> x ⟹ <a href="#cnf_feasible" title=cnf_feasible>cnf_feasible</a> (map ((#) x) (xs))

---
**cnf2_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#cnf_feasible" title=cnf_feasible>cnf_feasible</a> xs ⟹ <a href="#cnf_feasible" title=cnf_feasible>cnf_feasible</a> ys ⟹ <a href="#cnf_feasible" title=cnf_feasible>cnf_feasible</a> (xs@ys)

---
**cnf2_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> (xs@ys) ⟹ <a href="#cnf_feasible" title=cnf_feasible>cnf_feasible</a> (xs <a href="#interleave" title=interleave>⫴</a> ys)

---
**cnf2_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (map ((#) x) xs) = <a href="#S" title=S>S</a> x ∪ <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> xs

---
**cnf2_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> xs ∪ <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> ys = <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (xs@ys)

---
**cnf2_prop7**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_state" title=complete_state>complete_state</a> xs ∪ <a href="#complete_state" title=complete_state>complete_state</a> ys = <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (xs <a href="#interleave" title=interleave>⫴</a> ys)

---
**cnf2_prop8**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> y ⊆ C ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> y ⟹ <a href="#Choice" title=Choice>⋃</a> (map ((λxs. <a href="#Concat" title=Concat>Concat</a> xs C) ∘ (#) y) ys) <a href="#equiv" title=equiv>≡</a> <a href="#Choice" title=Choice>⋃</a> (map (λxs. y <a href="#composition" title=composition>;</a> <a href="#Concat" title=Concat>Concat</a> xs C) ys)

---
**cnf2_prop9**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Choice" title=Choice>⋃</a> (map (λxs. y <a href="#composition" title=composition>;</a> <a href="#Concat" title=Concat>Concat</a> xs C) xs) <a href="#equiv" title=equiv>≡</a> y <a href="#composition" title=composition>;</a>  <a href="#Choice" title=Choice>⋃</a> (map (λxs. <a href="#Concat" title=Concat>Concat</a> xs C) xs)

---
**cnf2_prop10**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> y ⟹ <a href="#S" title=S>S</a> y ⊆ C ⟹ y <a href="#composition" title=composition>;</a> <a href="#Choice" title=Choice>⋃</a> (map (λxs. <a href="#Concat" title=Concat>Concat</a> xs C) ([x] <a href="#interleave" title=interleave>⫴</a> ys)) <a href="#equiv" title=equiv>≡</a> <a href="#Choice" title=Choice>⋃</a> (map ((λxs. <a href="#Concat" title=Concat>Concat</a> xs C) ∘ (#) y) ([x] <a href="#interleave" title=interleave>⫴</a> ys))

---
**cnf2_prop11**

&nbsp;&nbsp;&nbsp;&nbsp;size xs = size ys ⟹ ∀z ∈ set (zip xs ys). fst z <a href="#equiv" title=equiv>≡</a> snd z ⟹ <a href="#Choice" title=Choice>⋃</a> xs <a href="#equiv" title=equiv>≡</a> <a href="#Choice" title=Choice>⋃</a> ys

---
**cnf2_prop12**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> x ⟹ <a href="#S" title=S>S</a> x ⊆ C ⟹ <a href="#evaluate" title=evaluate>evaluate</a> (map ((#) x) xs) C <a href="#equiv" title=equiv>≡</a> x <a href="#composition" title=composition>;</a> <a href="#evaluate" title=evaluate>evaluate</a> xs C

---
**cnf_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> (xs@ys) ⟹ <a href="#complete_state" title=complete_state>complete_state</a> (xs@ys) ⊆ C ⟹ <a href="#cnf_concurrency2" title=cnf_concurrency2>cnf_concurrency2</a> [xs] [ys] C <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> (xs <a href="#interleave" title=interleave>⫴</a> ys) C

---
**cnf_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> (x#ys) ⟹ <a href="#complete_state" title=complete_state>complete_state</a> (x#ys) ⊆ C ⟹ <a href="#cnf_concurrency2" title=cnf_concurrency2>cnf_concurrency2</a> [[x]] [ys] C <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> ([x] <a href="#interleave" title=interleave>⫴</a> ys) C

---
**cnf2_prop13**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> (x#xs@[y]) ⟹ <a href="#complete_state" title=complete_state>complete_state</a> (x#xs@[y]) ⊆ C ⟹ x <a href="#composition" title=composition>;</a> <a href="#cnf_concurrency2" title=cnf_concurrency2>cnf_concurrency2</a> [xs] [[y]] C <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> (map ((#) x) (xs <a href="#interleave" title=interleave>⫴</a> [y])) C

---
**cnf2_prop14**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> (xs@ys) ⟹ <a href="#complete_state" title=complete_state>complete_state</a> (xs@ys) ⊆ C ⟹ <a href="#cnf_concurrency2" title=cnf_concurrency2>cnf_concurrency2</a> [xs] [ys] C <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> ([xs] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> [ys]) C

---
**cnf2_prop15**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#cnf_feasible" title=cnf_feasible>cnf_feasible</a> (x#ys) ⟹ <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (x#ys) ⊆ C ⟹ <a href="#cnf_concurrency2" title=cnf_concurrency2>cnf_concurrency2</a> [x] ys C <a href="#equiv" title=equiv>≡</a> evaluate(concat (map ((<a href="#interleave" title=interleave>⫴</a>) x) ys)) C

---
**cnf2_prop16**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#cnf_feasible" title=cnf_feasible>cnf_feasible</a> (xs @ ys) ⟹ <a href="#cnf_feasible" title=cnf_feasible>cnf_feasible</a> ys

---
**cnf2_prop17**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#cnf_feasible" title=cnf_feasible>cnf_feasible</a> (xs @ ys) ⟹ <a href="#cnf_feasible" title=cnf_feasible>cnf_feasible</a> xs

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#cnf_feasible" title=cnf_feasible>cnf_feasible</a> (xs @ ys) ⟹ <a href="#complete_cnf_state" title=complete_cnf_state>complete_cnf_state</a> (xs @ ys) ⊆ C ⟹ <a href="#cnf_concurrency2" title=cnf_concurrency2>cnf_concurrency2</a> xs ys C <a href="#equiv" title=equiv>≡</a> <a href="#evaluate" title=evaluate>evaluate</a> (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> ys) C

---
## Complex_operation_interactions.thy

**cond_distrib2_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p), (C<sub>2</sub>, q)] <a href="#restrict_p" title=restrict_p>/</a> D <a href="#equal" title=equal>=</a> <a href="#GC" title=GC>GC</a> [((D ∩ C<sub>1</sub>), p), ((D ∩ C<sub>2</sub>), q)]

---
**Cond_distrib2_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p), (C<sub>2</sub>, q)] <a href="#restrict_p" title=restrict_p>/</a> D <a href="#equiv" title=equiv>≡</a> <a href="#GC" title=GC>GC</a> [((D ∩ C<sub>1</sub>), p), ((D ∩ C<sub>2</sub>), q)]

---
**restriction_ite**

&nbsp;&nbsp;&nbsp;&nbsp;(<a href="#ITE" title=ITE>ITE</a> C a b) <a href="#restrict_p" title=restrict_p>/</a> D = (<a href="#ITE" title=ITE>ITE</a> C (a/D) (b/D))

---
**restriction_ite**

&nbsp;&nbsp;&nbsp;&nbsp;(<a href="#ITE" title=ITE>ITE</a> C a b) <a href="#restrict_p" title=restrict_p>/</a> D <a href="#equal" title=equal>=</a> (<a href="#ITE" title=ITE>ITE</a> C (a/D) (b/D))

---
**restriction_ite**

&nbsp;&nbsp;&nbsp;&nbsp;(<a href="#ITE" title=ITE>ITE</a> C a b) <a href="#restrict_p" title=restrict_p>/</a> D <a href="#equiv" title=equiv>≡</a> (<a href="#ITE" title=ITE>ITE</a> C (a/D) (b/D))

---
**restriction_fixed_repetition_1**

&nbsp;&nbsp;&nbsp;&nbsp;0<n ⟹ (p<sup>n + 1</sup>) <a href="#restrict_p" title=restrict_p>/</a> C <a href="#equiv" title=equiv>≡</a> (p <a href="#restrict_p" title=restrict_p>/</a> C) <a href="#composition" title=composition>;</a> (p<sup>n</sup>)

---
**restriction_fixed_repetition_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ (p<sup>n</sup>) <a href="#restrict_p" title=restrict_p>/</a> C <a href="#equiv" title=equiv>≡</a> (<a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#restrict_p" title=restrict_p>/</a> C) <a href="#composition" title=composition>;</a> (p<sup>n</sup>)

---
**restriction_fixed_repetition_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sup>n</sup>) <a href="#restrict_p" title=restrict_p>/</a> C <a href="#equiv" title=equiv>≡</a> (<a href="#Skip" title=Skip>Skip</a> C) <a href="#composition" title=composition>;</a> (p<sup>n</sup>)

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#loop" title=loop>loop</a> p s f <a href="#restrict_p" title=restrict_p>/</a> C <a href="#equiv" title=equiv>≡</a> <a href="#Skip" title=Skip>Skip</a> C <a href="#composition" title=composition>;</a> <a href="#loop" title=loop>loop</a> p s f

---
**cond_distrib1_gc_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, (p<sub>2</sub> <a href="#choice" title=choice>∪</a> p<sub>3</sub>))] <a href="#equal" title=equal>=</a> (<a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, p<sub>2</sub>)]) <a href="#choice" title=choice>∪</a> (<a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, p<sub>3</sub>)])

---
**cond_distrib1_gc_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, (p<sub>2</sub> <a href="#choice" title=choice>∪</a> p<sub>3</sub>))] <a href="#equiv" title=equiv>≡</a> (<a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, p<sub>2</sub>)]) <a href="#choice" title=choice>∪</a> (<a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, p<sub>3</sub>)])

---
**cond_distrib1_gc_3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>3</sub>)), (C<sub>2</sub>, p<sub>2</sub>)] <a href="#equal" title=equal>=</a> <a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p<sub>1</sub>), ( C<sub>2</sub>, p<sub>2</sub>)] <a href="#choice" title=choice>∪</a> <a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p<sub>3</sub>), ( C<sub>2</sub>, p<sub>2</sub>)]

---
**cond_distrib1_gc_4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>3</sub>)), ( C<sub>2</sub>, p<sub>2</sub>)] <a href="#equiv" title=equiv>≡</a> <a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p<sub>1</sub>), ( C<sub>2</sub>, p<sub>2</sub>)] <a href="#choice" title=choice>∪</a> <a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p<sub>3</sub>), ( C<sub>2</sub>, p<sub>2</sub>)]

---
**cond_distrib1_ite_1**

&nbsp;&nbsp;&nbsp;&nbsp;(<a href="#ITE" title=ITE>ITE</a> C p<sub>1</sub> (p<sub>2</sub> <a href="#choice" title=choice>∪</a> p<sub>3</sub>)) <a href="#equal" title=equal>=</a> (<a href="#ITE" title=ITE>ITE</a> C p<sub>1</sub> p<sub>2</sub>) <a href="#choice" title=choice>∪</a> (<a href="#ITE" title=ITE>ITE</a> C p<sub>1</sub> p<sub>3</sub>)

---
**cond_distrib1_ite_2**

&nbsp;&nbsp;&nbsp;&nbsp;(<a href="#ITE" title=ITE>ITE</a> C p<sub>1</sub> (p<sub>2</sub> <a href="#choice" title=choice>∪</a> p<sub>3</sub>)) <a href="#equiv" title=equiv>≡</a> (<a href="#ITE" title=ITE>ITE</a> C p<sub>1</sub> p<sub>2</sub>) <a href="#choice" title=choice>∪</a> (<a href="#ITE" title=ITE>ITE</a> C p<sub>1</sub> p<sub>3</sub>)

---
**cond_distrib1_ite_3**

&nbsp;&nbsp;&nbsp;&nbsp;(<a href="#ITE" title=ITE>ITE</a> C (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>) p<sub>3</sub>) <a href="#equal" title=equal>=</a> (<a href="#ITE" title=ITE>ITE</a> C p<sub>1</sub> p<sub>3</sub>) <a href="#choice" title=choice>∪</a> (<a href="#ITE" title=ITE>ITE</a> C p<sub>2</sub> p<sub>3</sub>)

---
**cond_distrib1_ite_4**

&nbsp;&nbsp;&nbsp;&nbsp;(<a href="#ITE" title=ITE>ITE</a> C (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>) p<sub>3</sub>) <a href="#equiv" title=equiv>≡</a> (<a href="#ITE" title=ITE>ITE</a> C p<sub>1</sub> p<sub>3</sub>) <a href="#choice" title=choice>∪</a> (<a href="#ITE" title=ITE>ITE</a> C p<sub>2</sub> p<sub>3</sub>)

---
**guard_ifthenelse**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#ITE" title=ITE>ITE</a> C p<sub>1</sub> p<sub>2</sub> = <a href="#GC" title=GC>GC</a> [(C, p<sub>1</sub>), ((-C), p<sub>2</sub>)]

---
**until_def_lemma**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#until_loop" title=until_loop>until_loop</a> a C b n <a href="#equiv" title=equiv>≡</a> a <a href="#composition" title=composition>;</a> (<a href="#loop" title=loop>loop</a> (b/(-C)) 0 n)∖C

---
## Fixed_repetition.thy

**state_space_is_same**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> p = <a href="#S" title=S>S</a> (p <a href="#fixed_repetition" title=fixed_repetition><sup><</sup>/a> n)

---
**state_space_is_same2**

&nbsp;&nbsp;&nbsp;&nbsp;State (p<sup>n</sup>) = <a href="#S" title=S>S</a> p

---
**fixed_pre_decreases**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (p<sup>n + 1</sup>) ⊆ Pre (p<sup>n</sup>)

---
**fixed_rep_one_1**

&nbsp;&nbsp;&nbsp;&nbsp;p<sup>1</sup> <a href="#equiv" title=equiv>≡</a> p <a href="#restrict_p" title=restrict_p>/</a> (Pre p)

---
**fixed_rep_one_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ p<sup>1</sup> <a href="#equiv" title=equiv>≡</a> p

---
**fixed_rep_one_3**

&nbsp;&nbsp;&nbsp;&nbsp;x <a href="#composition" title=composition>;</a> p<sup>1</sup> <a href="#equiv" title=equiv>≡</a> x <a href="#composition" title=composition>;</a> p

---
**fixed_rep_two_1**

&nbsp;&nbsp;&nbsp;&nbsp;p<sup>2</sup> <a href="#equiv" title=equiv>≡</a> p <a href="#composition" title=composition>;</a> p

---
**fixed_rep_decomp_front**

&nbsp;&nbsp;&nbsp;&nbsp;0<i ⟹ p<sup>i + 1</sup> <a href="#equiv" title=equiv>≡</a> p <a href="#composition" title=composition>;</a> p<sup>i</sup>

---
**fixed_rep_decomp_back**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ p<sup>i + 1</sup> <a href="#equiv" title=equiv>≡</a> p<sup>i</sup> <a href="#composition" title=composition>;</a> p

---
**fixed_rep_feasibility**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (p<sup>n</sup>)

---
**fixed_rep_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;p<sup>i + 1</sup> <a href="#equiv" title=equiv>≡</a> p<sup>i</sup> <a href="#composition" title=composition>;</a> p

---
**range_decreases_fixed_repetition**

&nbsp;&nbsp;&nbsp;&nbsp;0 < n ⟹ <a href="#Range_p" title=Range_p>Range_p</a> (x <a href="#fixed_repetition" title=fixed_repetition><sup><</sup>/a> n) ⊆ <a href="#Range_p" title=Range_p>Range_p</a> x

---
**range_decreases_fixed_repetition_2**

&nbsp;&nbsp;&nbsp;&nbsp;0 < n ⟹ <a href="#Range_p" title=Range_p>Range_p</a> (x <a href="#fixed_repetition" title=fixed_repetition><sup><</sup>/a> n + 1) ⊆ <a href="#Range_p" title=Range_p>Range_p</a> (x <a href="#fixed_repetition" title=fixed_repetition><sup><</sup>/a> n)

---
**fixed_prop**

&nbsp;&nbsp;&nbsp;&nbsp;x<sup>1</sup> = <a href="#Skip" title=Skip>Skip</a> (Pre x) <a href="#composition" title=composition>;</a> x

---
**skip_choice**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Skip" title=Skip>Skip</a> (Pre x) <a href="#composition" title=composition>;</a> x <a href="#choice" title=choice>∪</a> <a href="#Skip" title=Skip>Skip</a> (Pre y) <a href="#composition" title=composition>;</a> y = <a href="#Skip" title=Skip>Skip</a> (Pre x ∪ Pre y) <a href="#composition" title=composition>;</a> (x <a href="#choice" title=choice>∪</a> y)

---
**comp_prop**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Range_p" title=Range_p>Range_p</a> a ∩ Pre d = {} ⟹ <a href="#Range_p" title=Range_p>Range_p</a> c ∩ Pre b = {} ⟹ a <a href="#composition" title=composition>;</a> b <a href="#choice" title=choice>∪</a> c <a href="#composition" title=composition>;</a> d = (a <a href="#choice" title=choice>∪</a> c) <a href="#composition" title=composition>;</a> (b <a href="#choice" title=choice>∪</a> d)

---
**arbitrary_repetition_simplification**

&nbsp;&nbsp;&nbsp;&nbsp;0<n ⟹ <a href="#all_feasible" title=all_feasible>all_feasible</a> [x,y] ⟹ <a href="#Range_p" title=Range_p>Range_p</a> x ∩ Pre y = {} ⟹ <a href="#Range_p" title=Range_p>Range_p</a> y ∩ Pre x = {} ⟹ x<sup>n</sup> <a href="#choice" title=choice>∪</a> y<sup>n</sup> = (x <a href="#choice" title=choice>∪</a> y)<sup>n</sup>

---
**arbitrary_repetition_simplification2**

&nbsp;&nbsp;&nbsp;&nbsp;0<n ⟹ <a href="#all_feasible" title=all_feasible>all_feasible</a> [x,y] ⟹ <a href="#Range_p" title=Range_p>Range_p</a> x ∩ Pre y = {} ⟹ <a href="#Range_p" title=Range_p>Range_p</a> y ∩ Pre x = {} ⟹ x<sup>n</sup> <a href="#choice" title=choice>∪</a> y<sup>n</sup> <a href="#equiv" title=equiv>≡</a> (x <a href="#choice" title=choice>∪</a> y)<sup>n</sup>

---
**equality_is_maintained_by_fixed_repetition**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#equal" title=equal>=</a> p<sub>2</sub> ⟹ p<sub>1</sub><sup>n</sup> <a href="#equal" title=equal>=</a> p<sub>2</sub><sup>n</sup>

---
**equiv_is_maintained_by_fixed_repetition**

&nbsp;&nbsp;&nbsp;&nbsp;0<n ⟹ <a href="#all_feasible" title=all_feasible>all_feasible</a> [p<sub>1</sub>, p<sub>2</sub>] ⟹ p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub> ⟹ p<sub>1</sub><sup>n</sup> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub><sup>n</sup>

---
**skip_compose_r_of_fixed_rep_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ p<sup>n</sup> <a href="#equiv" title=equiv>≡</a> p<sup>n</sup> <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p)

---
**skip_compose_l_of_fixed_rep_1**

&nbsp;&nbsp;&nbsp;&nbsp;p<sup>n</sup> <a href="#equiv" title=equiv>≡</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#composition" title=composition>;</a> p<sup>n</sup>

---
**fail_stays_fail_fixed**

&nbsp;&nbsp;&nbsp;&nbsp;p<sup>n</sup> <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {} ⟹ p<sup>n</sup> + 1 <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**repetition_fail**

&nbsp;&nbsp;&nbsp;&nbsp;i<j ⟹ p<sup>i</sup> <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {} ⟹ p<sup>j</sup> <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**fix_rep_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;0<i ⟹ p<sup>i</sup> = <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#restrict_p" title=restrict_p>/</a> (Pre p) <a href="#composition" title=composition>;</a> <a href="#Concat" title=Concat>Concat</a> [p . t ← [1 .. int i]] (<a href="#S" title=S>S</a> p)

---
**fix_rep_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;p<sup>i</sup> = <a href="#Concat" title=Concat>Concat</a> ((<a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p) <a href="#restrict_p" title=restrict_p>/</a> (Pre p))#[p . t ← [1 .. int i]]) (<a href="#S" title=S>S</a> p)

---
## Guarded_conditional.thy

**gc_S**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (<a href="#GC" title=GC>GC</a> ((C,p)#xs)) = <a href="#S" title=S>S</a> p ∪ <a href="#S" title=S>S</a> (<a href="#GC" title=GC>GC</a> xs)

---
**gc_S_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (<a href="#GC" title=GC>GC</a> (xs)) = <a href="#complete_state" title=complete_state>complete_state</a> ([snd t. t ← (xs)])

---
**cond_helper_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#GC" title=GC>GC</a> (x#xs) = <a href="#GC" title=GC>GC</a> (xs @ [x])

---
**cond_helper_2**

&nbsp;&nbsp;&nbsp;&nbsp;xs≠[ ] ⟹ <a href="#GC" title=GC>GC</a> (x#xs) = <a href="#GC" title=GC>GC</a> [x] <a href="#choice" title=choice>∪</a> <a href="#GC" title=GC>GC</a> xs

---
**cond_helper_3**

&nbsp;&nbsp;&nbsp;&nbsp;a ≠[ ] ⟹ b≠ [ ] ⟹ <a href="#GC" title=GC>GC</a> (a@b) = <a href="#GC" title=GC>GC</a> a <a href="#choice" title=choice>∪</a> <a href="#GC" title=GC>GC</a> b

---
**cond_commute**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set (<a href="#permutations" title=permutations>permutations</a> ys) ⟹ <a href="#GC" title=GC>GC</a> xs = <a href="#GC" title=GC>GC</a> ys

---
**cond_sub1**

&nbsp;&nbsp;&nbsp;&nbsp;D<sub>1</sub> ⊆ C<sub>1</sub> ⟹ D<sub>2</sub> ⊆ C<sub>2</sub> ⟹ (<a href="#GC" title=GC>GC</a> [(D<sub>1</sub>, p), (D<sub>2</sub>, q)]) <a href="#specialize" title=specialize>⊆</a> (<a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p), (C<sub>2</sub>, q)])

---
**property_on_gc_3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p<sub>1</sub>, p<sub>2</sub>] ⟹ <a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, p<sub>2</sub>)] <a href="#refines" title=refines>⊑</a> p<sub>1</sub> <a href="#restrict_p" title=restrict_p>/</a> C<sub>1</sub>

---
**property_on_gc_3_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#weakens" title=weakens>weakens</a> (<a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, p<sub>2</sub>)]) (p<sub>1</sub> <a href="#restrict_p" title=restrict_p>/</a> C<sub>1</sub>)

---
**property_on_gc_3_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#strengthens" title=strengthens>strengthens</a> (p<sub>1</sub> <a href="#restrict_p" title=restrict_p>/</a> C<sub>1</sub>) (<a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, p<sub>2</sub>)])

---
**cond_sub4**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> <a href="#restrict_p" title=restrict_p>/</a> C<sub>1</sub>) <a href="#specialize" title=specialize>⊆</a> (<a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, p<sub>2</sub>)])

---
**refinement_safety_gc_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p, q] ⟹ D<sub>1</sub> ⊆ C<sub>1</sub> ⟹ D<sub>2</sub> ⊆ C<sub>2</sub> ⟹ <a href="#GC" title=GC>GC</a> [(D<sub>1</sub>, p), (D<sub>2</sub>, q)] <a href="#refines" title=refines>⊑</a> <a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p), (C<sub>2</sub>, q)]

---
**refinement_safety_gc_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p, q] ⟹ D<sub>1</sub> ⊆ C<sub>1</sub> ⟹ D<sub>2</sub> ⊆ C<sub>2</sub> ⟹ <a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p), (C<sub>2</sub>, q)] <a href="#refines" title=refines>⊑</a> <a href="#GC" title=GC>GC</a> [(D<sub>1</sub>, p), (D<sub>2</sub>, q)]

---
**refinement_safety_gc_weakens**

&nbsp;&nbsp;&nbsp;&nbsp;D<sub>1</sub> ⊆ C<sub>1</sub> ⟹ D<sub>2</sub> ⊆ C<sub>2</sub> ⟹ <a href="#weakens" title=weakens>weakens</a> (<a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p), (C<sub>2</sub>, q)]) (<a href="#GC" title=GC>GC</a> [(D<sub>1</sub>, p), (D<sub>2</sub>, q)])

---
**refinement_safety_gc_strengthens**

&nbsp;&nbsp;&nbsp;&nbsp;D<sub>1</sub> ⊆ C<sub>1</sub> ⟹ D<sub>2</sub> ⊆ C<sub>2</sub> ⟹ <a href="#strengthens" title=strengthens>strengthens</a> (<a href="#GC" title=GC>GC</a> [(D<sub>1</sub>, p), (D<sub>2</sub>, q)]) (<a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p), (C<sub>2</sub>, q)])

---
**cond_refine1**

&nbsp;&nbsp;&nbsp;&nbsp;D<sub>1</sub> ⊆ C<sub>1</sub> ⟹ D<sub>2</sub> ⊆ C<sub>2</sub> ⟹ (<a href="#GC" title=GC>GC</a> [(D<sub>1</sub>, p), (D<sub>2</sub>, q)]) <a href="#refines" title=refines>⊑</a> (<a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p), (C<sub>2</sub>, q)])

---
**cond_refine2**

&nbsp;&nbsp;&nbsp;&nbsp;q<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>1</sub> ⟹ q<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>2</sub> ⟹ <a href="#GC" title=GC>GC</a> [(C, q<sub>1</sub>), (C, q<sub>2</sub>)] <a href="#refines" title=refines>⊑</a> <a href="#GC" title=GC>GC</a> [(C, p<sub>1</sub>), (C, p<sub>2</sub>)]

---
**refinement_safety_gc_3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p<sub>1</sub>, p<sub>2</sub>, q<sub>1</sub>, q<sub>2</sub>] ⟹ <a href="#strengthens" title=strengthens>strengthens</a> q<sub>1</sub> p<sub>2</sub> ⟹ <a href="#strengthens" title=strengthens>strengthens</a> q<sub>2</sub> p<sub>1</sub> ⟹ q<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>1</sub> ⟹ q<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>2</sub> ⟹ <a href="#GC" title=GC>GC</a> [(C, q<sub>1</sub>), (C, q<sub>2</sub>)] <a href="#refines" title=refines>⊑</a> <a href="#GC" title=GC>GC</a> [(C, p<sub>1</sub>), (C, p<sub>2</sub>)]

---
**refinement_safety_gc_4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [p<sub>1</sub>, p<sub>2</sub>, q<sub>1</sub>, q<sub>2</sub>] ⟹ <a href="#independent" title=independent>independent</a> q<sub>1</sub> p<sub>2</sub> ⟹ <a href="#independent" title=independent>independent</a> q<sub>2</sub> p<sub>1</sub> ⟹ q<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>1</sub> ⟹ q<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>2</sub> ⟹ <a href="#GC" title=GC>GC</a> [(C, q<sub>1</sub>), (C, q<sub>2</sub>)] <a href="#refines" title=refines>⊑</a> <a href="#GC" title=GC>GC</a> [(C, p<sub>1</sub>), (C, p<sub>2</sub>)]

---
**cond_refine4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#GC" title=GC>GC</a> [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, p<sub>2</sub>)] <a href="#refines" title=refines>⊑</a> p<sub>1</sub> <a href="#restrict_p" title=restrict_p>/</a> C<sub>1</sub>

---
**cond_sub2**

&nbsp;&nbsp;&nbsp;&nbsp;q<sub>1</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>1</sub> ⟹ q<sub>2</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>2</sub> ⟹ <a href="#GC" title=GC>GC</a> [(C, q<sub>1</sub>), (C, q<sub>2</sub>)] <a href="#specialize" title=specialize>⊆</a> <a href="#GC" title=GC>GC</a> [(C, p<sub>1</sub>), (C, p<sub>2</sub>)]

---
**cond_distrib**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#GC" title=GC>GC</a> xs <a href="#restrict_p" title=restrict_p>/</a> C <a href="#equiv" title=equiv>≡</a> <a href="#GC" title=GC>GC</a> [(fst t ∩ C, snd t) . t ← xs]

---
**GC_prop_22**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#choice" title=choice>∪</a> <a href="#GC" title=GC>GC</a> (x#xs) = a <a href="#choice" title=choice>∪</a> (<a href="#GC" title=GC>GC</a> [x] <a href="#choice" title=choice>∪</a> <a href="#GC" title=GC>GC</a> xs)

---
**gc_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (snd x) ⊆ <a href="#complete_state" title=complete_state>complete_state</a> (map snd xs) ⟹ fst x = <a href="#FALSE" title=FALSE>FALSE</a> ⟹ 1 < length xs ⟹ <a href="#GC" title=GC>GC</a> (x # xs) = <a href="#GC" title=GC>GC</a> xs

---
**gc_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (snd x) ⊆ <a href="#complete_state" title=complete_state>complete_state</a> (map snd (a@b)) ⟹ fst x = <a href="#FALSE" title=FALSE>FALSE</a> ⟹ size (a@b) > 1 ⟹ <a href="#GC" title=GC>GC</a> (a@x#b) = GC(a@b)

---
**if_false2**

&nbsp;&nbsp;&nbsp;&nbsp;fst x = <a href="#FALSE" title=FALSE>FALSE</a> ⟹ <a href="#GC" title=GC>GC</a> (a@x#b) <a href="#equiv" title=equiv>≡</a> GC(a@b)

---
**gc_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (snd x) ⊆ <a href="#complete_state" title=complete_state>complete_state</a> (map snd (a@b)) ⟹ fst x = <a href="#FALSE" title=FALSE>FALSE</a> ⟹ size (a@b) = 0 ⟹ <a href="#GC" title=GC>GC</a> (a@x#b) = GC(a@b)

---
**fail_choice**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> q ⊆ <a href="#S" title=S>S</a> p ⟹ q <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {} ⟹ q <a href="#choice" title=choice>∪</a> p = <a href="#Fail" title=Fail>Fail</a> {} <a href="#choice" title=choice>∪</a> p

---
**gc_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (snd x) ⊆ <a href="#complete_state" title=complete_state>complete_state</a> (map snd (a@b)) ⟹ fst x = <a href="#FALSE" title=FALSE>FALSE</a> ⟹ size (a@b) = 1 ⟹ <a href="#GC" title=GC>GC</a> (a@x#b) = <a href="#Fail" title=Fail>Fail</a> {} <a href="#choice" title=choice>∪</a> GC(a@b)

---
**cond_one**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#GC" title=GC>GC</a> [(C,p)] = p/C

---
**gc_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;x <a href="#restrict_p" title=restrict_p>/</a> C <a href="#specialize" title=specialize>⊆</a> <a href="#GC" title=GC>GC</a> ((C,x) # xs)

---
**gc_prop7**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#GC" title=GC>GC</a> a <a href="#specialize" title=specialize>⊆</a> <a href="#GC" title=GC>GC</a> (a@b)

---
**cond_sub3**

&nbsp;&nbsp;&nbsp;&nbsp;(C, x) ∈ set (xs) ⟹ x/C <a href="#specialize" title=specialize>⊆</a> <a href="#GC" title=GC>GC</a> xs

---
## If_then_else.thy

**ite_S**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (<a href="#ITE" title=ITE>ITE</a> C q<sub>1</sub> q<sub>2</sub>) = <a href="#S" title=S>S</a> q<sub>1</sub> ∪ <a href="#S" title=S>S</a> q<sub>2</sub>

---
**cond_swap**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#ITE" title=ITE>ITE</a> C p<sub>1</sub> p<sub>2</sub> = <a href="#ITE" title=ITE>ITE</a> (-C) p<sub>2</sub> p<sub>1</sub>

---
**property_on_ite_2**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (p <a href="#restrict_p" title=restrict_p>/</a> C) = Pre (<a href="#ITE" title=ITE>ITE</a> C p (<a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> p)))

---
**cond_refine3**

&nbsp;&nbsp;&nbsp;&nbsp;q<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>1</sub> ⟹ q<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>2</sub> ⟹ <a href="#ITE" title=ITE>ITE</a> C q<sub>1</sub> q<sub>2</sub> <a href="#refines" title=refines>⊑</a> <a href="#ITE" title=ITE>ITE</a> C p<sub>1</sub> p<sub>2</sub>

---
**cond_refine4**

&nbsp;&nbsp;&nbsp;&nbsp;q<sub>1</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>1</sub> ⟹ q<sub>2</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>2</sub> ⟹ <a href="#ITE" title=ITE>ITE</a> C q<sub>1</sub> q<sub>2</sub> <a href="#specialize" title=specialize>⊆</a> <a href="#ITE" title=ITE>ITE</a> C p<sub>1</sub> p<sub>2</sub>

---
## Non_atomic_concurrency.thy

**non_atomic_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;[ ] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> x = x

---
**non_atomic_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;((a # xs) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> x) <a href="#equiv" title=equiv>≡</a> a <a href="#composition" title=composition>;</a> (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> x) <a href="#choice" title=choice>∪</a> <a href="#Concat" title=Concat>Concat</a> (x#a#xs)

---
**compose_distrib**

&nbsp;&nbsp;&nbsp;&nbsp;(b <a href="#choice" title=choice>∪</a> (a <a href="#composition" title=composition>;</a> c <a href="#choice" title=choice>∪</a> a <a href="#composition" title=composition>;</a> d)) = (b <a href="#choice" title=choice>∪</a> a <a href="#composition" title=composition>;</a> (c <a href="#choice" title=choice>∪</a> d))

---
**concur_two**

&nbsp;&nbsp;&nbsp;&nbsp;[a]∥b = a <a href="#composition" title=composition>;</a> b <a href="#choice" title=choice>∪</a> b <a href="#composition" title=composition>;</a> a

---
**concur_commute**

&nbsp;&nbsp;&nbsp;&nbsp;[a]∥b = ([b]∥a)

---
**compose_distrib2**

&nbsp;&nbsp;&nbsp;&nbsp;∀x ∈ set xs. x ≠ [ ] ⟹ xs ≠ [ ] ⟹ b <a href="#choice" title=choice>∪</a> <a href="#Choice" title=Choice>⋃</a> [a <a href="#composition" title=composition>;</a> (<a href="#Concat" title=Concat>Concat</a> t). t ← xs] = b <a href="#choice" title=choice>∪</a>  a ;⋃ [(<a href="#Concat" title=Concat>Concat</a> t). t ← xs]

---
**concur_recursive**

&nbsp;&nbsp;&nbsp;&nbsp;((a # xs) <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> x) = a <a href="#composition" title=composition>;</a> (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> x) <a href="#choice" title=choice>∪</a> <a href="#Concat" title=Concat>Concat</a> (x#a#xs)

---
**non_atomic_conc_S**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (xs∥x) = <a href="#complete_state" title=complete_state>complete_state</a> (x#xs)

---
**concor_three_1**

&nbsp;&nbsp;&nbsp;&nbsp;[p<sub>1</sub>, p<sub>2</sub>] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> q = ((q <a href="#composition" title=composition>;</a> p<sub>1</sub>) <a href="#composition" title=composition>;</a> p<sub>2</sub> <a href="#choice" title=choice>∪</a> ((p<sub>1</sub> <a href="#composition" title=composition>;</a> q) <a href="#composition" title=composition>;</a> p<sub>2</sub>)) <a href="#choice" title=choice>∪</a> ((p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>) <a href="#composition" title=composition>;</a> q)

---
**concor_three_2**

&nbsp;&nbsp;&nbsp;&nbsp;[p<sub>1</sub>, p<sub>2</sub>] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> q <a href="#equal" title=equal>=</a> ((q <a href="#composition" title=composition>;</a> p<sub>1</sub>) <a href="#composition" title=composition>;</a> p<sub>2</sub> <a href="#choice" title=choice>∪</a> ((p<sub>1</sub> <a href="#composition" title=composition>;</a> q) <a href="#composition" title=composition>;</a> p<sub>2</sub>)) <a href="#choice" title=choice>∪</a> ((p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>) <a href="#composition" title=composition>;</a> q)

---
**concor_three_3**

&nbsp;&nbsp;&nbsp;&nbsp;[p<sub>1</sub>, p<sub>2</sub>] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> q <a href="#equiv" title=equiv>≡</a> ((q <a href="#composition" title=composition>;</a> p<sub>1</sub>) <a href="#composition" title=composition>;</a> p<sub>2</sub> <a href="#choice" title=choice>∪</a> ((p<sub>1</sub> <a href="#composition" title=composition>;</a> q) <a href="#composition" title=composition>;</a> p<sub>2</sub>)) <a href="#choice" title=choice>∪</a> ((p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>) <a href="#composition" title=composition>;</a> q)

---
**Concat_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> xs ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#Concat" title=Concat>Concat</a> xs)

---
**Choice_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> xs ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#Choice" title=Choice>⋃</a> xs)

---
**all_feasible_prop**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> xs ⟹ x ∈ set xs ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> x

---
**all_feasible_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;∀x ∈ set xs. <a href="#is_feasible" title=is_feasible>is_feasible</a> x ≡ <a href="#all_feasible" title=all_feasible>all_feasible</a> xs

---
**all_feasible_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set (<a href="#permutations" title=permutations>permutations</a> ys) ⟹ <a href="#all_feasible" title=all_feasible>all_feasible</a> ys ⟹ <a href="#all_feasible" title=all_feasible>all_feasible</a> xs

---
**non_atomic_conc_feasible_preserving**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> (x#xs) ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> x)

---
**atomic_conc_refinement_safe**

&nbsp;&nbsp;&nbsp;&nbsp;q<sub>1</sub> <a href="#refines" title=refines>⊑</a> p<sub>1</sub> ⟹ q<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>2</sub> ⟹ q<sub>3</sub> <a href="#refines" title=refines>⊑</a> p<sub>3</sub> ⟹ ([q<sub>1</sub>, q<sub>2</sub>] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> q<sub>3</sub>) <a href="#refines" title=refines>⊑</a> ([p<sub>1</sub>, p<sub>2</sub>] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> p<sub>3</sub>)

---
&nbsp;&nbsp;&nbsp;&nbsp;((ys@[x])@xs) <a href="#generalized_non_atomic_conc" title=generalized_non_atomic_conc>∥<sub>G</sub></a> q <a href="#equiv" title=equiv>≡</a> (ys@([x]@xs)) <a href="#generalized_non_atomic_conc" title=generalized_non_atomic_conc>∥<sub>G</sub></a> q

---
**atomic_restrict_1**

&nbsp;&nbsp;&nbsp;&nbsp;(xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> x) <a href="#restrict_p" title=restrict_p>/</a> C <a href="#equiv" title=equiv>≡</a>  <a href="#Choice" title=Choice>⋃</a> [Concat t <a href="#restrict_p" title=restrict_p>/</a> C. t ← <a href="#insert_all" title=insert_all>insert_all</a> x xs]

---
**concur_restrict**

&nbsp;&nbsp;&nbsp;&nbsp;(xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> x) <a href="#restrict_p" title=restrict_p>/</a> C =  <a href="#Choice" title=Choice>⋃</a> [Concat t <a href="#restrict_p" title=restrict_p>/</a> C. t ← <a href="#insert_all" title=insert_all>insert_all</a> x xs]

---
**atomic_corestrict_1**

&nbsp;&nbsp;&nbsp;&nbsp;(xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> x) <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#equiv" title=equiv>≡</a>  <a href="#Choice" title=Choice>⋃</a> [Concat t <a href="#corestrict_p" title=corestrict_p>∖</a> C. t ← <a href="#insert_all" title=insert_all>insert_all</a> x xs]

---
**equiv_list_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#equiv_list" title=equiv_list>equiv_list</a> xs ys ⟹ <a href="#Choice" title=Choice>⋃</a> xs <a href="#equiv" title=equiv>≡</a> <a href="#Choice" title=Choice>⋃</a> ys

---
**equiv_list_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;∀a ∈ set xs. a ≠ [ ] ⟹ <a href="#equiv_list" title=equiv_list>equiv_list</a> [Concat t <a href="#restrict_p" title=restrict_p>/</a> C. t ← xs] [Concat (hd t <a href="#restrict_p" title=restrict_p>/</a> C # tl t). t ← xs]

---
**equiv_list_prop_3**

&nbsp;&nbsp;&nbsp;&nbsp;∀a ∈ set xs. a ≠ [ ] ⟹ <a href="#equiv_list" title=equiv_list>equiv_list</a> [Concat t <a href="#corestrict_p" title=corestrict_p>∖</a> C. t ← xs] [Concat (butlast t @ [(last t)∖ C]). t ← xs]

---
**concur_restrict**

&nbsp;&nbsp;&nbsp;&nbsp;(xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> x) <a href="#restrict_p" title=restrict_p>/</a> C <a href="#equiv" title=equiv>≡</a>  <a href="#Choice" title=Choice>⋃</a> [Concat (hd t/C#tl t). t ← <a href="#insert_all" title=insert_all>insert_all</a> x xs]

---
**concur_corestrict**

&nbsp;&nbsp;&nbsp;&nbsp;(xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> x) <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#equiv" title=equiv>≡</a>  <a href="#Choice" title=Choice>⋃</a> [Concat (butlast t @ [(last t)∖ C]). t ← <a href="#insert_all" title=insert_all>insert_all</a> x xs]

---
**concur_specialize1**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#composition" title=composition>;</a> q <a href="#specialize" title=specialize>⊆</a> ([p] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> q)

---
**non_atomic_specialize**

&nbsp;&nbsp;&nbsp;&nbsp;ys ∈ set (<a href="#insert_all" title=insert_all>insert_all</a> x xs) ⟹ (<a href="#Concat" title=Concat>Concat</a> ys) <a href="#specialize" title=specialize>⊆</a> (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> x)

---
**commute_compose**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#commute_programs3" title=commute_programs3>commute_programs3</a> a b ⟹ [a] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> b <a href="#equiv" title=equiv>≡</a> a <a href="#composition" title=composition>;</a> b

---
**concur_distrib1**

&nbsp;&nbsp;&nbsp;&nbsp;xs∥(b <a href="#choice" title=choice>∪</a> c) <a href="#equiv" title=equiv>≡</a> (xs∥b) <a href="#choice" title=choice>∪</a> (xs∥c)

---
**concur_choice1**

&nbsp;&nbsp;&nbsp;&nbsp;[a∪b]∥(c) = ([a]∥c) <a href="#choice" title=choice>∪</a> ([b]∥c)

---
**concur_choice2**

&nbsp;&nbsp;&nbsp;&nbsp;xs∥(b <a href="#choice" title=choice>∪</a> c) = (xs∥b) <a href="#choice" title=choice>∪</a> (xs∥c)

---
**concur_specialize2**

&nbsp;&nbsp;&nbsp;&nbsp;([Concat xs] <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> x) <a href="#specialize" title=specialize>⊆</a> (xs <a href="#cnf_concurrency" title=cnf_concurrency>∥</a> x)

---
## Permutations.thy

**simp_2**

&nbsp;&nbsp;&nbsp;&nbsp;∀x<sub>1</sub> x<sub>2</sub> x<sub>3</sub>. f (f x<sub>1</sub> x<sub>2</sub>) x<sub>3</sub> = f  x<sub>1</sub> (f x<sub>2</sub> x<sub>3</sub>) ⟹ foldl f (f a x) xs = f a (foldl f x xs)

---
**fold_composition_assoc**

&nbsp;&nbsp;&nbsp;&nbsp;foldl (<a href="#composition" title=composition>;</a>) x (as @ [a]) = (foldl (<a href="#composition" title=composition>;</a>) x as) <a href="#composition" title=composition>;</a> a

---
**S_foldl_composition**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (foldl (<a href="#composition" title=composition>;</a>) x as) = ⋃ (<a href="#S" title=S>S</a> ` (set (x # as)))

---
**main_theorem**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (foldl (<a href="#composition" title=composition>;</a>) x (a # as)) = <a href="#S" title=S>S</a> ((foldl (<a href="#composition" title=composition>;</a>) x as) <a href="#composition" title=composition>;</a> a)

---
**skip_fold_complete_state**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (<a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> (x # xs))) ∪ <a href="#S" title=S>S</a> x ∪ <a href="#S" title=S>S</a> (foldl (<a href="#composition" title=composition>;</a>) x xs) = <a href="#complete_state" title=complete_state>complete_state</a> (x # xs) ∪ <a href="#S" title=S>S</a> x ∪ <a href="#complete_state" title=complete_state>complete_state</a> xs

---
**simp_5**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (foldl (<a href="#composition" title=composition>;</a>) (<a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> xs)) xs) = <a href="#complete_state" title=complete_state>complete_state</a> xs

---
**simp_4_right**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (foldl (<a href="#composition" title=composition>;</a>) (<a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> xs)) xs) ⊆ <a href="#complete_state" title=complete_state>complete_state</a> xs

---
**fold_composition_state_inv**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (fold (<a href="#composition" title=composition>;</a>) t b) = <a href="#S" title=S>S</a> (foldl (<a href="#composition" title=composition>;</a>) b t)

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (fold (<a href="#composition" title=composition>;</a>) t (<a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> t))) = <a href="#S" title=S>S</a> (foldl (<a href="#composition" title=composition>;</a>) (<a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> t)) t)

---
**permutation_fold_subset_complete_state**

&nbsp;&nbsp;&nbsp;&nbsp;t ∈ set (<a href="#permutations" title=permutations>permutations</a> xs) ⟹ <a href="#S" title=S>S</a> (fold (<a href="#composition" title=composition>;</a>) t (<a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> t))) ⊆ <a href="#complete_state" title=complete_state>complete_state</a> xs

---
**state_composition**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ <a href="#S" title=S>S</a> a ⟹ x ∈ <a href="#S" title=S>S</a> (a <a href="#composition" title=composition>;</a> b)

---
**state_composition_1**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ <a href="#S" title=S>S</a> p ⟹ x ∈ <a href="#S" title=S>S</a> (foldl (<a href="#composition" title=composition>;</a>) p (xs))

---
**state_composition_2**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ <a href="#S" title=S>S</a> a ⟹ x ∈ <a href="#S" title=S>S</a> (foldl (<a href="#composition" title=composition>;</a>) p (a#xs))

---
**state_composition_3**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ <a href="#S" title=S>S</a> a ⟹ x ∈ <a href="#S" title=S>S</a> (foldl (<a href="#composition" title=composition>;</a>) p (ys@a#xs))

---
**complete_state_subset**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#complete_state" title=complete_state>complete_state</a> xs ⊆ <a href="#S" title=S>S</a> (<a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> xs))

---
**foldl_composition_preserves_state**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> p ⊆ <a href="#S" title=S>S</a> (foldl (<a href="#composition" title=composition>;</a>) p xs)

---
**Union_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;⋃ (set (xs@[x])) = x ∪ ⋃ (set xs)

---
**Union_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;⋃ (xs ∪ {x}) = x ∪ ⋃ xs

---
**fold_comp_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ foldl (<a href="#composition" title=composition>;</a>) x xs = foldl (<a href="#composition" title=composition>;</a>) (x <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> x)) xs

---
**fold_comp_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ foldl (<a href="#composition" title=composition>;</a>) x xs = foldl (<a href="#composition" title=composition>;</a>) (x <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> (x#xs))) xs

---
**fold_comp_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (foldl (<a href="#composition" title=composition>;</a>) x xs) = <a href="#complete_state" title=complete_state>complete_state</a> (x # xs)

---
**fold_comp_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ foldl (<a href="#composition" title=composition>;</a>) x xs = foldl (<a href="#composition" title=composition>;</a>) (x <a href="#composition" title=composition>;</a> <a href="#Skip" title=Skip>Skip</a> (<a href="#complete_state" title=complete_state>complete_state</a> (xs))) xs

---
**perm_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;(filter (p) xs) @ (filter (λx. ¬ p x) xs) ∈ set (<a href="#permutations" title=permutations>permutations</a> xs)

---
**perm_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set (<a href="#permutations" title=permutations>permutations</a> ys) ⟹ map p xs ∈ set (<a href="#permutations" title=permutations>permutations</a> (map p ys))

---
## Until_loop.thy

**until_conncetion**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#until_loop" title=until_loop>until_loop</a> a C b n = <a href="#until_support" title=until_support>until_support</a> a C b 0 n

---
**until_decomposition**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#until_loop" title=until_loop>until_loop</a> a C b (n + 1) <a href="#equiv" title=equiv>≡</a> a <a href="#composition" title=composition>;</a> ((b/(-C))<sup>n + 1</sup> <a href="#choice" title=choice>∪</a> (<a href="#loop" title=loop>loop</a> (b/(-C)) 0 n)) <a href="#corestrict_p" title=corestrict_p>∖</a> C

---
**until_decomposition_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#until_loop" title=until_loop>until_loop</a> a C b (n + 1) <a href="#equiv" title=equiv>≡</a> a <a href="#composition" title=composition>;</a> ((b/(-C))<sup>n + 1</sup>) <a href="#corestrict_p" title=corestrict_p>∖</a> C <a href="#choice" title=choice>∪</a> <a href="#until_loop" title=until_loop>until_loop</a> a C b n

---
**until_def_lemma_3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#until_loop" title=until_loop>until_loop</a> a C b n <a href="#equiv" title=equiv>≡</a> a <a href="#composition" title=composition>;</a> ((<a href="#Skip" title=Skip>Skip</a> (<a href="#S" title=S>S</a> (b/(-C))) <a href="#restrict_p" title=restrict_p>/</a> (Pre (b/(-C)))) <a href="#choice" title=choice>∪</a> (<a href="#loop" title=loop>loop</a> (b/(-C)) 1 n)) <a href="#corestrict_p" title=corestrict_p>∖</a> C

---
**loop_choice1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#until_loop" title=until_loop>until_loop</a> a C b n <a href="#equiv" title=equiv>≡</a> <a href="#Choice" title=Choice>⋃</a> [a <a href="#composition" title=composition>;</a> ((b <a href="#restrict_p" title=restrict_p>/</a> (- C))<sup>nat i</sup>)∖C. i ← [0..int n]]

---
**loop_choice2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Range_p" title=Range_p>Range_p</a> (<a href="#until_loop" title=until_loop>until_loop</a> a C b n) = ⋃ (set [Range_p (a <a href="#composition" title=composition>;</a> ((b <a href="#restrict_p" title=restrict_p>/</a> (- C))<sup>nat i</sup>)∖C). i ← [0..int n]])

---
**until_loop_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [a, b] ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#until_loop" title=until_loop>until_loop</a> a C b n)

---
**equiv_is_maintained_by_until_loop_2**

&nbsp;&nbsp;&nbsp;&nbsp;a<sub>1</sub> <a href="#equiv" title=equiv>≡</a> a<sub>2</sub> ⟹ b<sub>1</sub> <a href="#equiv" title=equiv>≡</a> b<sub>2</sub> ⟹ <a href="#S" title=S>S</a> b<sub>1</sub> = <a href="#S" title=S>S</a> b<sub>2</sub> ⟹ <a href="#all_feasible" title=all_feasible>all_feasible</a> [b<sub>1</sub>, b<sub>2</sub>] ⟹ <a href="#until_loop" title=until_loop>until_loop</a> a<sub>1</sub> C b<sub>1</sub> n <a href="#equiv" title=equiv>≡</a> <a href="#until_loop" title=until_loop>until_loop</a> a<sub>2</sub> C b<sub>2</sub> n

---
**until_decom**

&nbsp;&nbsp;&nbsp;&nbsp;k&lt;n ⟹ <a href="#until_loop" title=until_loop>until_loop</a> a C b n <a href="#equiv" title=equiv>≡</a> <a href="#until_loop" title=until_loop>until_loop</a> a C b n <a href="#choice" title=choice>∪</a> <a href="#until_loop" title=until_loop>until_loop</a> a C b k

---
**range_until_loop_1**

&nbsp;&nbsp;&nbsp;&nbsp;m&lt;n ⟹ x ∉ <a href="#Range_p" title=Range_p>Range_p</a> (<a href="#until_loop" title=until_loop>until_loop</a> a C b n) ⟹ x ∉ <a href="#Range_p" title=Range_p>Range_p</a> (<a href="#until_loop" title=until_loop>until_loop</a> a C b m)

---
**range_until_loop_2**

&nbsp;&nbsp;&nbsp;&nbsp;m&lt;n ⟹ x ∉ <a href="#Range_p" title=Range_p>Range_p</a> (<a href="#until_loop" title=until_loop>until_loop</a> a C b n) ⟹ x ∉ <a href="#Range_p" title=Range_p>Range_p</a> (<a href="#until_support" title=until_support>until_support</a> a C b s m)

---
**loop_range**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Range_p" title=Range_p>Range_p</a> (<a href="#until_loop" title=until_loop>until_loop</a> a C b n) ⊆ C

---
**split_front**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#until_loop" title=until_loop>until_loop</a> (x <a href="#composition" title=composition>;</a> a) C b n <a href="#equiv" title=equiv>≡</a> x <a href="#composition" title=composition>;</a> <a href="#until_loop" title=until_loop>until_loop</a> a C b n

---
**fail_until**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#until_loop" title=until_loop>until_loop</a> a C b (n + 1) <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {} ⟹ <a href="#until_loop" title=until_loop>until_loop</a> a C b n <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**fail_until_2**

&nbsp;&nbsp;&nbsp;&nbsp;k&lt;n ⟹ <a href="#until_loop" title=until_loop>until_loop</a> a C b n <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {} ⟹ <a href="#until_loop" title=until_loop>until_loop</a> a C b k <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**loop_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (<a href="#loop" title=loop>loop</a> (b/(-C)) 0 n) = <a href="#S" title=S>S</a> b

---
**loop_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;State (<a href="#loop" title=loop>loop</a> (b/(-C)) 0 n) = <a href="#S" title=S>S</a> b

---
**loop_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> (<a href="#until_loop" title=until_loop>until_loop</a> a C b n) = <a href="#S" title=S>S</a> a ∪ <a href="#S" title=S>S</a> b

---
**loop_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;State (<a href="#until_loop" title=until_loop>until_loop</a> a C b n) = <a href="#S" title=S>S</a> (<a href="#until_loop" title=until_loop>until_loop</a> a C b n)

---
**loop_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;State (<a href="#until_loop" title=until_loop>until_loop</a> a C b n) = <a href="#S" title=S>S</a> a ∪ <a href="#S" title=S>S</a> b

---
**loop_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#until_loop" title=until_loop>until_loop</a> (<a href="#Skip" title=Skip>Skip</a> D) <a href="#FALSE" title=FALSE>FALSE</a> (<a href="#Skip" title=Skip>Skip</a> D) n = <a href="#Fail" title=Fail>Fail</a> D

---
## Until_support.thy

**until_decomp_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#until_support" title=until_support>until_support</a> a C b 0 n <a href="#equiv" title=equiv>≡</a> <a href="#until_support" title=until_support>until_support</a> a C b 0 0 <a href="#choice" title=choice>∪</a> <a href="#until_support" title=until_support>until_support</a> a C b (0 + 1) n

---
**until_decomp_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#until_support" title=until_support>until_support</a> a C b 0 (n + 1) <a href="#equiv" title=equiv>≡</a> <a href="#until_support" title=until_support>until_support</a> a C b 0 n <a href="#choice" title=choice>∪</a> <a href="#until_support" title=until_support>until_support</a> a C b (n + 1) (n + 1)

---
**until_decomp_3**

&nbsp;&nbsp;&nbsp;&nbsp;s &lt; f ⟹ <a href="#until_support" title=until_support>until_support</a> a C b s f <a href="#equiv" title=equiv>≡</a> <a href="#until_support" title=until_support>until_support</a> a C b s s <a href="#choice" title=choice>∪</a> <a href="#until_support" title=until_support>until_support</a> a C b (s + 1) f

---
**until_decomp_4**

&nbsp;&nbsp;&nbsp;&nbsp;s &lt; f ⟹ <a href="#until_support" title=until_support>until_support</a> a C b s (f + 1) <a href="#equiv" title=equiv>≡</a> <a href="#until_support" title=until_support>until_support</a> a C b (f + 1) (f + 1) <a href="#choice" title=choice>∪</a> <a href="#until_support" title=until_support>until_support</a> a C b s f

---
**until_decomp_5**

&nbsp;&nbsp;&nbsp;&nbsp;0 &lt; k ⟹ k &lt; n ⟹ <a href="#until_support" title=until_support>until_support</a> a C b 0 n <a href="#equiv" title=equiv>≡</a> <a href="#until_support" title=until_support>until_support</a> a C b 0 k <a href="#choice" title=choice>∪</a> <a href="#until_support" title=until_support>until_support</a> a C b (k + 1) n

---
**until_decomp_6**

&nbsp;&nbsp;&nbsp;&nbsp;s &lt; k ⟹ k &lt; f ⟹ <a href="#until_support" title=until_support>until_support</a> a C b s f <a href="#equiv" title=equiv>≡</a> <a href="#until_support" title=until_support>until_support</a> a C b s k <a href="#choice" title=choice>∪</a> <a href="#until_support" title=until_support>until_support</a> a C b (k + 1) f

---
**until_decomp_7**

&nbsp;&nbsp;&nbsp;&nbsp;s = f ⟹ <a href="#until_support" title=until_support>until_support</a> a C b s f <a href="#equiv" title=equiv>≡</a> a <a href="#composition" title=composition>;</a> ((b <a href="#restrict_p" title=restrict_p>/</a> (- C))<sup>f</sup>) <a href="#corestrict_p" title=corestrict_p>∖</a> C

---
**until_support_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#all_feasible" title=all_feasible>all_feasible</a> [a, b] ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> (<a href="#until_support" title=until_support>until_support</a> a C b s f)

---
**equiv_is_maintained_by_until_support_1**

&nbsp;&nbsp;&nbsp;&nbsp;a<sub>1</sub> <a href="#equiv" title=equiv>≡</a> a<sub>2</sub> ⟹ b<sub>1</sub> <a href="#equiv" title=equiv>≡</a> b<sub>2</sub> ⟹ <a href="#S" title=S>S</a> b<sub>1</sub> = <a href="#S" title=S>S</a> b<sub>2</sub> ⟹ <a href="#all_feasible" title=all_feasible>all_feasible</a> [b<sub>1</sub>, b<sub>2</sub>] ⟹ <a href="#until_support" title=until_support>until_support</a> a<sub>1</sub> C b<sub>1</sub> s f <a href="#equiv" title=equiv>≡</a> <a href="#until_support" title=until_support>until_support</a> a<sub>2</sub> C b<sub>2</sub> s f

---
**equiv_is_maintained_by_until_support_2**

&nbsp;&nbsp;&nbsp;&nbsp;a<sub>1</sub> <a href="#equiv" title=equiv>≡</a> a<sub>2</sub> ⟹ b<sub>1</sub> <a href="#equiv" title=equiv>≡</a> b<sub>2</sub> ⟹ 0<s ⟹ <a href="#all_feasible" title=all_feasible>all_feasible</a> [b<sub>1</sub>, b<sub>2</sub>] ⟹ <a href="#until_support" title=until_support>until_support</a> a<sub>1</sub> C b<sub>1</sub> s f <a href="#equiv" title=equiv>≡</a> <a href="#until_support" title=until_support>until_support</a> a<sub>2</sub> C b<sub>2</sub> s f

---
**bad_index_is_fail_support**

&nbsp;&nbsp;&nbsp;&nbsp;f < s ⟹ <a href="#until_support" title=until_support>until_support</a> a C b s f <a href="#equiv" title=equiv>≡</a> <a href="#Fail" title=Fail>Fail</a> {}

---
**bad_index_range_support**

&nbsp;&nbsp;&nbsp;&nbsp;f < s ⟹ <a href="#Range_p" title=Range_p>Range_p</a> (<a href="#until_support" title=until_support>until_support</a> a C b s f) = {}

---
**until_support_decomp**

&nbsp;&nbsp;&nbsp;&nbsp;s&lt;s' ⟹ f'&lt;f ⟹ <a href="#until_support" title=until_support>until_support</a> a C b s f <a href="#equiv" title=equiv>≡</a> <a href="#until_support" title=until_support>until_support</a> a C b s f <a href="#choice" title=choice>∪</a> <a href="#until_support" title=until_support>until_support</a> a C b s' f'

---
## Contract.thy

**consequence_rule**

&nbsp;&nbsp;&nbsp;&nbsp;post<sub>1</sub> ⊆ post<sub>2</sub> ⟹ Pre<sub>2</sub> ⊆ Pre<sub>1</sub> ⟹ <a href="#is_correct" title=is_correct>is_correct</a> 〈a_specification=〈State=Pre<sub>1</sub> ∪ Field post<sub>2</sub>, Pre=Pre<sub>1</sub>, post=post<sub>1</sub>〉, a_implementation=b〉 ⟹ <a href="#is_correct" title=is_correct>is_correct</a> 〈a_specification=〈State=Pre<sub>1</sub> ∪ Field post<sub>2</sub>, Pre=Pre<sub>2</sub>, post=post<sub>2</sub>〉, a_implementation=b〉

---
**post_charac_old**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_correct" title=is_correct>is_correct</a> 〈a_specification=s, a_implementation=b〉 ⟹ b <a href="#strongest_postcondition" title=strongest_postcondition>sp</a> (Pre s) ⊆ post s

---
**pre_charac_old**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_correct" title=is_correct>is_correct</a> 〈a_specification=s, a_implementation=b〉 ⟹ Pre s ⊆ b <a href="#weakest_precondition" title=weakest_precondition>wp</a> (post s)

---
**correct_program_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_correct" title=is_correct>is_correct</a> 〈a_specification=s, a_implementation=b〉 ⟹ Pre s ⊆ Pre b - Domain (post b - post s)

---
**correct_program_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> s = <a href="#S" title=S>S</a> b ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> b ⟹ Pre s ⊆ Pre b - Domain (post b - post s) ⟹ <a href="#is_correct" title=is_correct>is_correct</a> 〈a_specification=s, a_implementation=b〉

---
**correct_program**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> s = <a href="#S" title=S>S</a> b ⟹ <a href="#is_feasible" title=is_feasible>is_feasible</a> b ⟹ <a href="#is_correct" title=is_correct>is_correct</a> 〈a_specification=s, a_implementation=b〉 = (Pre s ⊆ Pre b - Domain (post b - post s))

---
**fail_false**

&nbsp;&nbsp;&nbsp;&nbsp;b <a href="#strongest_postcondition" title=strongest_postcondition>sp</a> <a href="#FALSE" title=FALSE>FALSE</a> = <a href="#FALSE" title=FALSE>FALSE</a>

---
**false_fail**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> b ⟹ b <a href="#weakest_precondition" title=weakest_precondition>wp</a> <a href="#FALSE" title=FALSE>FALSE</a> = <a href="#FALSE" title=FALSE>FALSE</a>

---
&nbsp;&nbsp;&nbsp;&nbsp;b <a href="#weakest_precondition" title=weakest_precondition>wp</a> <a href="#FALSE" title=FALSE>FALSE</a> = Pre b - Domain (post b)

---
**fail_pre**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Fail" title=Fail>Fail</a> S' <a href="#strongest_postcondition" title=strongest_postcondition>sp</a> Pre' = {}

---
**sp_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#strongest_postcondition" title=strongest_postcondition>sp</a> <a href="#TRUE" title=TRUE>TRUE</a> (<a href="#S" title=S>S</a> p) = post p

---
**wp_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#weakest_precondition" title=weakest_precondition>wp</a> TRUE (<a href="#S" title=S>S</a> p) = Pre p

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Havoc" title=Havoc>Havoc</a> C <a href="#strongest_postcondition" title=strongest_postcondition>sp</a> pre = {(x,y). x ∈ pre ∧ x ∈ C ∧ y ∈ C}

---
&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Havoc" title=Havoc>Havoc</a> C <a href="#strongest_postcondition" title=strongest_postcondition>sp</a> pre = post (<a href="#Havoc" title=Havoc>Havoc</a> C) <a href="#restrict_r" title=restrict_r>/</a> pre

---
**fail_post**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#Fail" title=Fail>Fail</a> S' <a href="#weakest_precondition" title=weakest_precondition>wp</a> post' = <a href="#FALSE" title=FALSE>FALSE</a>

---
**sp_distrib**

&nbsp;&nbsp;&nbsp;&nbsp;b <a href="#strongest_postcondition" title=strongest_postcondition>sp</a> (p ∪ q) = b <a href="#strongest_postcondition" title=strongest_postcondition>sp</a> p ∪ b <a href="#strongest_postcondition" title=strongest_postcondition>sp</a> q

---
**wp_distrib2**

&nbsp;&nbsp;&nbsp;&nbsp;(b <a href="#weakest_precondition" title=weakest_precondition>wp</a> p) ∪ (b <a href="#weakest_precondition" title=weakest_precondition>wp</a> q) ⊆ b <a href="#weakest_precondition" title=weakest_precondition>wp</a> (p ∪ q)

---
**sanity**

&nbsp;&nbsp;&nbsp;&nbsp;q <a href="#refines" title=refines>⊑</a> p ⟹  〈a_specification=s, a_implementation=q〉 <a href="#refines_c" title=refines_c>⊑</a>  〈a_specification=s, a_implementation=p〉

---
**mai_theorem_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_feasible" title=is_feasible>is_feasible</a> p ⟹ <a href="#is_correct" title=is_correct>is_correct</a> (<a href="#MAI" title=MAI>MAI</a> p)

---
**state_feasible_1**

&nbsp;&nbsp;&nbsp;&nbsp;(∀s ∈ Pre p . <a href="#is_trivial" title=is_trivial>is_trivial</a> (post p) s ∨ <a href="#is_relevant" title=is_relevant>is_relevant</a> (post p) s) = <a href="#is_feasible" title=is_feasible>is_feasible</a> p

---
&nbsp;&nbsp;&nbsp;&nbsp;(<a href="#Infeas" title=Infeas>Infeas</a> D) <a href="#weakest_precondition" title=weakest_precondition>wp</a> C = <a href="#TRUE" title=TRUE>TRUE</a> D

---
&nbsp;&nbsp;&nbsp;&nbsp;(<a href="#Infeas" title=Infeas>Infeas</a> D) <a href="#strongest_postcondition" title=strongest_postcondition>sp</a> C = <a href="#FALSE" title=FALSE>FALSE</a>

---
&nbsp;&nbsp;&nbsp;&nbsp;(<a href="#Havoc" title=Havoc>Havoc</a> D) <a href="#strongest_postcondition" title=strongest_postcondition>sp</a> C = (TRUE D) <a href="#restrict_r" title=restrict_r>/</a> C

---
&nbsp;&nbsp;&nbsp;&nbsp;(<a href="#Infeas" title=Infeas>Infeas</a> D) <a href="#strongest_postcondition" title=strongest_postcondition>sp</a> C = <a href="#FALSE" title=FALSE>FALSE</a>

---
**post_charac**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#implements" title=implements>implements</a> a b ⟹ a <a href="#strongest_postcondition" title=strongest_postcondition>sp</a> (Pre b) ⊆ post b

---
**pre_charac**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#implements" title=implements>implements</a> i s ⟹ Pre s ⊆ i <a href="#weakest_precondition" title=weakest_precondition>wp</a> (post s)

---
## Invariant.thy

**invariant_disjoint_from_pre**

&nbsp;&nbsp;&nbsp;&nbsp;I ∩ (Pre p) = {} ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I p

---
**false_is_invariant**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> <a href="#FALSE" title=FALSE>FALSE</a> p

---
**equiv_inv**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> <a href="#equiv" title=equiv>≡</a> p<sub>2</sub> ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I p<sub>1</sub> = <a href="#is_invariant" title=is_invariant>is_invariant</a> I p<sub>2</sub>

---
**invariant_relation_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I p ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> J p ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> (I ∪ J) p

---
**invariant_relation_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I p ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> J p ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> (I ∩ J) p

---
**invariant_refinement**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I p<sub>1</sub> ⟹ p<sub>2</sub> <a href="#refines" title=refines>⊑</a> p<sub>1</sub> ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (p<sub>2</sub> <a href="#restrict_p" title=restrict_p>/</a> (Pre p<sub>1</sub>))

---
**invariant_prop_specialize**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I p<sub>1</sub> ⟹ p<sub>2</sub> <a href="#specialize" title=specialize>⊆</a> p<sub>1</sub> ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (p<sub>2</sub>)

---
**invariant_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I (<a href="#Fail" title=Fail>Fail</a> C)

---
**invariant_prop_3**

&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ I ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (<a href="#Havoc" title=Havoc>Havoc</a> C)

---
**invariant_prop_4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I (<a href="#Skip" title=Skip>Skip</a> C)

---
**composition_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I p<sub>1</sub> ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I p<sub>2</sub> ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (p<sub>1</sub> <a href="#composition" title=composition>;</a> p<sub>2</sub>)

---
**choice_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I p<sub>1</sub> ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I p<sub>2</sub> ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>)

---
**choice_invariant_preserve_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>) ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I p<sub>1</sub>

---
**choice_invariant_preserve_3**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>) ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I p<sub>2</sub>

---
**choice_invariant_preserve_4**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I (p<sub>1</sub> <a href="#choice" title=choice>∪</a> p<sub>2</sub>) = (<a href="#is_invariant" title=is_invariant>is_invariant</a> I p<sub>1</sub> ∧ <a href="#is_invariant" title=is_invariant>is_invariant</a> I p<sub>2</sub>)

---
**restriction_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I p ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (p <a href="#restrict_p" title=restrict_p>/</a> C)

---
**restriction_invariant_preserve_2**

&nbsp;&nbsp;&nbsp;&nbsp;I ⊆ C ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (p <a href="#restrict_p" title=restrict_p>/</a> C) ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I p

---
**corestriction_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I p ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (p <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
**c_is_invariant**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> C (p <a href="#corestrict_p" title=corestrict_p>∖</a> C)

---
**guarded_conditional_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I p ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I q ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (<a href="#GC" title=GC>GC</a> [(C, p), (D, q)])

---
**if_then_else_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I p ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I q ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (<a href="#ITE" title=ITE>ITE</a> C p q)

---
**fixed_repetition_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp; <a href="#is_invariant" title=is_invariant>is_invariant</a> I p ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (p<sup>n</sup>)

---
**arbitrary_repetition_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I p ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (<a href="#loop" title=loop>loop</a> p s f)

---
**until_support_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;0<s ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I a ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I b ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (<a href="#until_support" title=until_support>until_support</a> a C b s f)

---
**until_loop_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I a ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I b ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (<a href="#until_loop" title=until_loop>until_loop</a> a C b n)

---
**inverse_is_not_invariant_preseving**

&nbsp;&nbsp;&nbsp;&nbsp;Pre p ⊆ I ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I p ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (p <a href="#inverse" title=inverse><sup>-</sup><sup>1</sup></a>)

---
**true_is_invariant**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> p ⊆ C ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> (<a href="#TRUE" title=TRUE>TRUE</a> C) p

---
**invariant_exp**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I b ⟹ x ∈ Pre b ⟹ (x,y) ∈ post b  ⟹ x ∈ I ⟹ y ∈ I

---
**invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_invariant" title=is_invariant>is_invariant</a> I b ⟹ <a href="#Range_p" title=Range_p>Range_p</a> a ⊆ I ⟹ x ∈ Pre a ⟹ (x,y) ∈ post (a <a href="#composition" title=composition>;</a> b) ⟹ y ∈ I

---
## Loop_invariant.thy

**false_is_loop_invariant**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_loop_invariant" title=is_loop_invariant>is_loop_invariant</a> <a href="#FALSE" title=FALSE>FALSE</a> a C b

---
**true_is_loop_invariant**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#S" title=S>S</a> a ∪ <a href="#S" title=S>S</a> b ∪ C ⊆ D ⟹ <a href="#is_loop_invariant" title=is_loop_invariant>is_loop_invariant</a> (<a href="#TRUE" title=TRUE>TRUE</a> D) a C b

---
**loop_invariant_is_invariant_of_loop**

&nbsp;&nbsp;&nbsp;&nbsp;0<s ⟹ <a href="#is_loop_invariant" title=is_loop_invariant>is_loop_invariant</a> I a C b ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (<a href="#loop" title=loop>loop</a> (b/(-C)) s n)

---
**loop_correct_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_loop_invariant" title=is_loop_invariant>is_loop_invariant</a> I a C b ⟹ <a href="#Range_p" title=Range_p>Range_p</a> (a <a href="#composition" title=composition>;</a> <a href="#loop" title=loop>loop</a> (b <a href="#restrict_p" title=restrict_p>/</a> (- C)) n n) ⊆ I

---
**loop_correct_2**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_loop_invariant" title=is_loop_invariant>is_loop_invariant</a> I a C b ⟹ <a href="#Range_p" title=Range_p>Range_p</a> (<a href="#until_support" title=until_support>until_support</a> a C b n n) ⊆ I

---
**loop_correct_3**

&nbsp;&nbsp;&nbsp;&nbsp;s&lt;f ⟹ <a href="#is_loop_invariant" title=is_loop_invariant>is_loop_invariant</a> I a C b ⟹ <a href="#Range_p" title=Range_p>Range_p</a> (<a href="#until_support" title=until_support>until_support</a> a C b s f) ⊆ I

---
**loop_correct**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_loop_invariant" title=is_loop_invariant>is_loop_invariant</a> I a C b ⟹ <a href="#Range_p" title=Range_p>Range_p</a> (<a href="#until_loop" title=until_loop>until_loop</a> a C b n) ⊆ C ∩ I

---
**is_invariant_is_preserved**

&nbsp;&nbsp;&nbsp;&nbsp;p <a href="#equiv" title=equiv>≡</a> q ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I p ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I q

---
**is_loop_invariant_is_preserved**

&nbsp;&nbsp;&nbsp;&nbsp;a <a href="#equiv" title=equiv>≡</a> a' ⟹ b <a href="#equiv" title=equiv>≡</a> b' ⟹ <a href="#is_loop_invariant" title=is_loop_invariant>is_loop_invariant</a> I a C b ⟹ <a href="#is_loop_invariant" title=is_loop_invariant>is_loop_invariant</a> I a' C b'

---
**loop_inv_is_inv_for_a**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_loop_invariant" title=is_loop_invariant>is_loop_invariant</a> I a C b ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I a

---
**Loop_inv_1**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_loop_invariant" title=is_loop_invariant>is_loop_invariant</a> I a C b ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (b <a href="#restrict_p" title=restrict_p>/</a> (- C))

---
**loop_inv_is_inv_of_loop**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_loop_invariant" title=is_loop_invariant>is_loop_invariant</a> I a C b ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (<a href="#loop" title=loop>loop</a> (b/(-C)) 0 n)

---
**Loop_invinv**

&nbsp;&nbsp;&nbsp;&nbsp;<a href="#is_loop_invariant" title=is_loop_invariant>is_loop_invariant</a> I a C b ⟹ <a href="#is_invariant" title=is_invariant>is_invariant</a> I (<a href="#until_loop" title=until_loop>until_loop</a> a C b n)

---
