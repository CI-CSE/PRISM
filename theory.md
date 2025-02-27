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

**basic** :: *'a CNF ⇒ 'a Program set*

&nbsp;&nbsp;&nbsp;&nbsp;basic p ≡ foldl (∪) ({}::'a Program set) (map (set) p)

---
**S** :: *'a Program ⇒ 'a set*

&nbsp;&nbsp;&nbsp;&nbsp;S p = State p ∪ Pre p ∪ Field (post p)

---
**used_states** :: *'a Program ⇒ 'a set*

&nbsp;&nbsp;&nbsp;&nbsp;used_states p ≡ Pre p ∪ Field (post p)

---
**is_feasible** :: *'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p = (Pre p ⊆ Domain (post p))

---
**all_feasible** :: *('a Program) list ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [ ] = True

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible (x # xs) = (all_feasible xs ∧ is_feasible x)

---
**cnf_feasible** :: *'a CNF ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;cnf_feasible [ ] = True

&nbsp;&nbsp;&nbsp;&nbsp;cnf_feasible (x # xs) = (all_feasible x ∧ cnf_feasible xs)

---
**is_valid** :: *'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;is_valid p ≡ S p = State p

---
**all_valid** :: *('a Program) list ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;all_valid [ ] = True

&nbsp;&nbsp;&nbsp;&nbsp;all_valid (x#xs) = (all_valid xs ∧ is_valid x)

---
**is_deterministic** :: *'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;is_deterministic p = is_function (post p)

---
**is_functional** :: *'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;is_functional p ≡ ∀C⊆(S p). Image (post p) C ∩ C = {}

---
**is_total** :: *'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;is_total p = (Pre p = S p)

---
**restr_post** :: *'a Program ⇒ 'a  rel*

&nbsp;&nbsp;&nbsp;&nbsp;restr_post p = post p /<sub>r</sub> Pre p

---
**equal [=]** :: *'a Program ⇒ 'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> = p<sub>2</sub> ≡ (Pre p<sub>1</sub> = Pre p<sub>2</sub> ∧ post p<sub>1</sub> = post p<sub>2</sub> ∧ S p<sub>1</sub> = S p<sub>2</sub>)

---
**equiv [≡<sub>p</sub>]** :: *'a Program ⇒ 'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ≡<sub>p</sub> p<sub>2</sub> ≡ (Pre p<sub>1</sub> = Pre p<sub>2</sub> ∧ restr_post p<sub>1</sub> = restr_post p<sub>2</sub>)

---
**Range_p** :: *'a Program ⇒ 'a set*

&nbsp;&nbsp;&nbsp;&nbsp;Range_p p = Range (post p /<sub>r</sub> Pre p)

---
**inverse** :: *'a Program ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;inverse p ≡ 〈State=S p, Pre=Range_p p, post=(restr_post p)⁻¹〉

---
**extends** :: *'a Program ⇒ 'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;extends p<sub>2</sub> p<sub>1</sub> = (S p<sub>1</sub> ⊆ S p<sub>2</sub>)

---
**weakens** :: *'a Program ⇒ 'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;weakens p<sub>2</sub> p<sub>1</sub> = (Pre p<sub>1</sub> ⊆ Pre p<sub>2</sub>)

---
**strengthens** :: *'a Program ⇒ 'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;strengthens p<sub>2</sub> p<sub>1</sub> ≡ ((post p<sub>2</sub>) /<sub>r</sub> Pre p<sub>2</sub>) /<sub>r</sub> (Pre p<sub>1</sub>) ⊆ post p<sub>1</sub>

---
**refines [⊑<sub>p</sub>]** :: *'a Program ⇒ 'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ⊑<sub>p</sub> p<sub>2</sub> = (extends p<sub>1</sub> p<sub>2</sub> ∧ weakens p<sub>1</sub> p<sub>2</sub> ∧ strengthens p<sub>1</sub> p<sub>2</sub>)

---
**refines_c [⊑<sub>c</sub>]** :: *'a Contracted_Program ⇒ 'a Contracted_Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;cp<sub>2</sub> ⊑<sub>c</sub> cp<sub>1</sub> ≡ a_specification cp<sub>2</sub> = a_specification cp<sub>1</sub> ∧ a_implementation cp<sub>2</sub> ⊑<sub>p</sub> a_implementation cp<sub>1</sub>

---
**specialize [⊆<sub>p</sub>]** :: *'a Program ⇒ 'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ⊆<sub>p</sub> p<sub>2</sub> ≡ extends p<sub>2</sub> p<sub>1</sub> ∧ weakens p<sub>2</sub> p<sub>1</sub> ∧ strengthens p<sub>1</sub> p<sub>2</sub>

---
**independent** :: *'a Program ⇒ 'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;independent p<sub>1</sub> p<sub>2</sub> = (Pre p<sub>1</sub> ∩ Pre p<sub>2</sub> = {})

---
**implements** :: *'a Program ⇒ 'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;implements p<sub>2</sub> p<sub>1</sub> = (p<sub>2</sub> ⊑<sub>p</sub> p<sub>1</sub> ∧ is_feasible p<sub>2</sub>)

---
**most_abstract_implementation** :: *'a Program ⇒ 'a Contracted_Program*

&nbsp;&nbsp;&nbsp;&nbsp;most_abstract_implementation p ≡ 〈a_specification=p, a_implementation=p〉

---
**MAI** :: *'a Program ⇒ 'a Contracted_Program*

&nbsp;&nbsp;&nbsp;&nbsp;MAI ≡ most_abstract_implementation

---
**is_correct** :: *'a Contracted_Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;is_correct cp = implements (a_implementation cp) (a_specification cp)

---
**strongest_postcondition [sp]** :: *'a Program ⇒ 'a set ⇒ 'a rel*

&nbsp;&nbsp;&nbsp;&nbsp;p sp Pre' ≡ post (p) /<sub>r</sub> Pre'

---
**new_behavior** :: *'a Program ⇒ 'a rel ⇒ 'a rel*

&nbsp;&nbsp;&nbsp;&nbsp;new_behavior p post' ≡ post p - post'

---
**weakest_precondition [wp]** :: *'a Program ⇒ 'a rel ⇒ 'a set*

&nbsp;&nbsp;&nbsp;&nbsp;p wp post' ≡ Pre p - Domain (new_behavior p post')

---
**choice [∪<sub>p</sub>]** :: *'a Program ⇒ 'a Program ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub> = 〈State= S p<sub>1</sub> ∪ S p<sub>2</sub>, Pre = Pre p<sub>1</sub> ∪ Pre p<sub>2</sub>, post = restr_post p<sub>1</sub> ∪ restr_post p<sub>2</sub>〉

---
**non_empty** :: *'a CNF ⇒ 'a CNF*

&nbsp;&nbsp;&nbsp;&nbsp;non_empty xs ≡ [t . t ← xs, t ≠ [ ]]

---
**non_empty2** :: *'a CNF list ⇒ 'a CNF list*

&nbsp;&nbsp;&nbsp;&nbsp;non_empty2 xs ≡ [prog2. prog2 ← [non_empty prog. prog ← xs], prog2 ≠ [ ]]

---
**choice_cnf [∪<sub>c</sub>]** :: *'a CNF ⇒ 'a CNF ⇒ 'a CNF*

&nbsp;&nbsp;&nbsp;&nbsp;choice_cnf a b ≡ a @ b

---
**composition_cnf [;<sub>c</sub>]** :: *'a CNF ⇒ 'a CNF ⇒ 'a CNF*

&nbsp;&nbsp;&nbsp;&nbsp;composition_cnf a b ≡ [xs @ ys. xs ← a, ys ← b]

---
**is_prime** :: *'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;is_prime p ≡ card (Pre p) = 1 ∧ card (post p) = 1 ∧ Pre p ∪ Field (post p) = State p

---
**composition [;]** :: *'a Program ⇒ 'a Program ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ; p<sub>2</sub> = 〈
      State = S p<sub>1</sub> ∪ S p<sub>2</sub>,
      Pre = Pre p<sub>1</sub> ∩ Domain (post p<sub>1</sub> ∖<sub>r</sub> Pre p<sub>2</sub>),
      post = (post p<sub>1</sub>) O (restr_post p<sub>2</sub>)〉

---
**commute_programs1** :: *'a Program ⇒ 'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;commute_programs1 p<sub>1</sub> p<sub>2</sub> ≡ (p<sub>1</sub> ; p<sub>2</sub>) = (p<sub>2</sub> ; p<sub>1</sub>)

---
**commute_programs2** :: *'a Program ⇒ 'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;commute_programs2 p<sub>1</sub> p<sub>2</sub> ≡ (p<sub>1</sub> ; p<sub>2</sub>) = (p<sub>2</sub> ; p<sub>1</sub>)

---
**commute_programs3** :: *'a Program ⇒ 'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;commute_programs3 p<sub>1</sub> p<sub>2</sub> ≡ (p<sub>1</sub> ; p<sub>2</sub>) ≡<sub>p</sub> (p<sub>2</sub> ; p<sub>1</sub>)

---
**unsafe_composition [;<sub>p</sub>]** :: *'a Program ⇒ 'a Program ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ;<sub>p</sub> p<sub>2</sub> = 〈
      State = S p<sub>1</sub> ∪ S p<sub>2</sub>,
      Pre = Pre p<sub>1</sub>,
      post = (post p<sub>1</sub>) O (restr_post p<sub>2</sub>)〉

---
**unsafe_composition2 [;<sup>p</sup>]** :: *'a Program ⇒ 'a Program ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ;<sup>p</sup> p<sub>2</sub> = 〈
      State = S p<sub>1</sub> ∪ S p<sub>2</sub>,
      Pre = Pre p<sub>1</sub> ∩ Domain (post p<sub>1</sub> ∖<sub>r</sub> Pre p<sub>2</sub>),
      post = (post p<sub>1</sub>) O (post p<sub>2</sub>)〉

---
**unsafe_composition3 [;<sub>P</sub>]** :: *'a Program ⇒ 'a Program ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ;<sub>P</sub> p<sub>2</sub> = 〈
      State = S p<sub>1</sub> ∪ S p<sub>2</sub>,
      Pre = Pre p<sub>1</sub>,
      post = (post p<sub>1</sub>) O (post p<sub>2</sub>)〉

---
**restrict_p [/<sub>p</sub>]** :: *'a Program ⇒ 'a set ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;restrict_p p C = 〈State= S p, Pre=Pre p ∩ C, post=post p /<sub>r</sub> C〉

---
**corestrict_p [∖<sub>p</sub>]** :: *'a Program ⇒ 'a set ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;corestrict_p p C = 〈State= S p, 
        Pre=Pre p, \
        post=post p ∖<sub>r</sub> C〉

---
**char_rel** :: *'a Program ⇒ 'a rel*

&nbsp;&nbsp;&nbsp;&nbsp;char_rel p = post p /<sub>r</sub> Pre p

---
**Fail** :: *'a set ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;Fail s = 〈 State = s, Pre = {}, post = {}〉

---
**Havoc** :: *'a set ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;Havoc s = 〈 State = s, Pre = s, post = {(x,y). x ∈ s ∧ y ∈ s}〉

---
**Skip** :: *'a set ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;Skip s = 〈 State = s, Pre = s, post = {(x,y). x ∈ s ∧ x = y} 〉

---
**Infeas** :: *'a set ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;Infeas s = 〈 State = s, Pre = s, post = {} 〉

---
**generalized_non_atomic_conc [∥<sub>G</sub>]** :: *('a Program) list ⇒ 'a Program ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;[ ]     ∥<sub>G</sub> q = q

&nbsp;&nbsp;&nbsp;&nbsp;(x#xs) ∥<sub>G</sub> q = ((xs ∥<sub>G</sub> q) ; x) ∪<sub>p</sub> (x ; (xs ∥<sub>G</sub> q))

---
**if_then_else** :: *'a set ⇒ 'a Program ⇒ 'a Program ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;if_then_else C p<sub>1</sub> p<sub>2</sub> ≡ (p<sub>1</sub> /<sub>p</sub> C) ∪<sub>p</sub> (p<sub>2</sub> /<sub>p</sub> (-C))

---
**ITE** :: *'a set ⇒ 'a Program ⇒ 'a Program ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;ITE ≡ if_then_else

---
**if_then** :: *'a set ⇒ 'a Program ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;if_then C p ≡ ITE C p (Skip (S p))

---
**TRUE** :: *'a set ⇒ 'a set*

&nbsp;&nbsp;&nbsp;&nbsp;TRUE s = s

---
**FALSE** :: *'a set*

&nbsp;&nbsp;&nbsp;&nbsp;FALSE = {}

---
**ID** :: *'a set ⇒ 'a rel*

&nbsp;&nbsp;&nbsp;&nbsp;ID s ≡ {(a,b) . a ∈ s ∧ b ∈ s ∧ a = b}

---
**fixed_repetition_helper [^<sup>p</sup>]** :: *'a Program ⇒ nat ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;fixed_repetition_helper p 0       = Skip (S p)

&nbsp;&nbsp;&nbsp;&nbsp;fixed_repetition_helper p (i + 1) = fixed_repetition_helper p i ; p

---
**fixed_repetition [<sup>^</sup>]** :: *'a Program ⇒ nat ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;p<sup>0</sup>       = Skip (S p) /<sub>p</sub> (Pre p)

&nbsp;&nbsp;&nbsp;&nbsp;p<sup>i + 1</sup> = p<sup>i</sup>;p

---
**Choice** :: *('a Program) list ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;Choice [ ] = Fail {}

&nbsp;&nbsp;&nbsp;&nbsp;Choice [x] = x

&nbsp;&nbsp;&nbsp;&nbsp;Choice (x#xs) = foldl (∪<sub>p</sub>) x xs

---
**Concat** :: *('a Program) list ⇒ 'a set ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;Concat [ ] s = (Skip s)

&nbsp;&nbsp;&nbsp;&nbsp;Concat [x] s = x

&nbsp;&nbsp;&nbsp;&nbsp;Concat (x#xs) s = foldl (;) x xs

---
**Choice_set** :: *('a Program) set ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;Choice_set P ≡ Finite_Set.fold (∪<sub>p</sub>) (Fail {}) P

---
**is_minimal** :: *'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;is_minimal p ≡ (∀a b. (a,b) ∈ post p → a ∈ Pre p) ∧ is_valid p ∧ (∀ s ∈ State p. s ∈ Field (post p))

---
**guarded_conditional** :: *('a set × 'a Program) list ⇒  'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;guarded_conditional xs = ⋃<sub>p</sub> [snd t /<sub>p</sub> fst t. t ← xs]

---
**GC** :: *('a set × 'a Program) list ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;GC ≡ guarded_conditional

---
**insert_all** :: *'a ⇒ 'a list ⇒ 'a list list*

&nbsp;&nbsp;&nbsp;&nbsp;insert_all x [ ] = [[x]]

&nbsp;&nbsp;&nbsp;&nbsp;insert_all x (y#ys) = (x#y#ys) # (map (λzs. y#zs) (insert_all x ys))

---
**permutations** :: *'a list ⇒ 'a list list*

&nbsp;&nbsp;&nbsp;&nbsp;permutations [ ] = [[ ]]

&nbsp;&nbsp;&nbsp;&nbsp;permutations (x#xs) = concat (map (insert_all x) (permutations xs))

---
**complete_state** :: *'a Program list ⇒ 'a set*

&nbsp;&nbsp;&nbsp;&nbsp;complete_state xs ≡ fold (λ p s. S p ∪ s) xs {}

---
**n_comp** :: *'a Program list ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;n_comp [ ] = Fail {}

&nbsp;&nbsp;&nbsp;&nbsp;n_comp (x#xs) = x ; (n_comp xs)

---
**conc_elems** :: *'a Program list ⇒ 'a Program list*

&nbsp;&nbsp;&nbsp;&nbsp;conc_elems xs ≡ [Concat t (complete_state t). t ← permutations xs]

---
**atomic_conc** :: *'a Program list ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;atomic_conc xs ≡ ⋃<sub>p</sub> (conc_elems xs)

---
**non_atomic_conc [∥<sub>n</sub>]** :: *'a Program list ⇒ 'a Program ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;xs ∥<sub>n</sub> x ≡ ⋃<sub>p</sub> [Concat t (complete_state t). t ← insert_all x xs]

---
**arbitrary_repetition_set** :: *'a Program ⇒ 'a Program set*

&nbsp;&nbsp;&nbsp;&nbsp;arbitrary_repetition_set p ≡ {p<sup>i</sup> | i . 0<i}

---
**arbitrary_repetition** :: *'a Program ⇒ nat ⇒ nat ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;arbitrary_repetition p s 0 = (if s>0 then Fail (S p) else p<sup>0</sup>)

&nbsp;&nbsp;&nbsp;&nbsp;arbitrary_repetition p s (f + 1) = (if s>(f + 1) then Fail (S p) else p<sup>f + 1</sup> ∪<sub>p</sub> arbitrary_repetition p s f)

---
**loop** :: *'a Program ⇒ nat ⇒ nat ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;loop ≡ arbitrary_repetition

---
**until_support** :: *'a Program ⇒ 'a set ⇒ 'a Program ⇒ nat ⇒ nat ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;until_support a C b s f = a ; (loop (b/<sub>p</sub>(-C)) s f)∖<sub>p</sub> C

---
**until_loop** :: *'a Program ⇒ 'a set ⇒ 'a Program ⇒ nat ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;until_loop a C b n = a ; (loop (b/<sub>p</sub>(-C)) 0 n)∖<sub>p</sub> C

---
**is_invariant** :: *'a set ⇒ 'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I p ≡ Range_p (p /<sub>p</sub> I) ⊆ I

---
**is_loop_invariant** :: *'a set ⇒ 'a Program ⇒ 'a set ⇒ 'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;is_loop_invariant I a C b ≡ Range_p a ⊆ I ∧ is_invariant I (b/<sub>p</sub>(-C))

---
**markovian** :: *'a rel ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;markovian r ≡ ∀s s<sub>1</sub> s<sub>2</sub>. ((s<sub>1</sub>, s) ∈ r) = ((s<sub>2</sub>, s) ∈ r)

---
**is_trivial** :: *'a rel ⇒ 'a ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;is_trivial r s ≡ ∀s<sub>1</sub>. (s, s<sub>1</sub>) ∈ r

---
**is_irrelevant** :: *'a rel ⇒ 'a ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;is_irrelevant r s ≡ ∀s<sub>1</sub> s<sub>2</sub>. ((s, s<sub>1</sub>) ∈ r) = ((s, s<sub>2</sub>) ∈ r)

---
**is_relevant** :: *'a rel ⇒ 'a ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;is_relevant r s ≡ ¬ is_irrelevant r s

---
**is_programming_language** :: *'a set ⇒ ('a Program) set ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;is_programming_language s P ≡ ∀p ∈ P. is_feasible p ∧ S p ⊆ s

---
**occurs** :: *'a ⇒ 'a list ⇒ nat*

&nbsp;&nbsp;&nbsp;&nbsp;occurs _ [ ] = 0

&nbsp;&nbsp;&nbsp;&nbsp;occurs x (y # ys) = (if x = y then 1 else 0) + occurs x ys

---
**inter [∩<sub>p</sub>]** :: *'a Program ⇒ 'a Program ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;p ∩<sub>p</sub> q ≡ 〈State=S p ∩ S q,Pre=Pre p ∩ Pre q,post=post p ∩ post q〉

---
**set_to_list** :: *'a set ⇒ 'a list*

&nbsp;&nbsp;&nbsp;&nbsp;set_to_list s = (if finite s then SOME l. set l = s ∧ distinct l else [ ])

---
**is_atomic** :: *'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;is_atomic p ≡ S p = State p ∧ card (post p) = 1 ∧ card (Pre p) = 1 ∧ State p = (Pre p) ∪ (Field (post p)) ∧
   (card (post p) = 1 ∧ card (Pre p) = 1 →
    fst (THE x. x ∈ post p) = (THE x. x ∈ Pre p))

---
**get_atomic** :: *'a Program ⇒ ('a Program) set*

&nbsp;&nbsp;&nbsp;&nbsp;get_atomic p = {〈State={a,b}, Pre={a}, post={(a, b)} 〉 | a b .     (a,b) ∈ post p ∧ a ∈ Pre p}

---
**evaluate** :: *'a CNF ⇒ 'a set ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;evaluate p s ≡ ⋃<sub>p</sub> (map (λxs. Concat xs s) p)

---
**interleave [⫴]** :: *'a list ⇒ 'a list ⇒ 'a list list*

&nbsp;&nbsp;&nbsp;&nbsp;[ ] ⫴ ys = [ys]

&nbsp;&nbsp;&nbsp;&nbsp;(xs) ⫴ [ ] = [xs]

&nbsp;&nbsp;&nbsp;&nbsp;(x#xs) ⫴ (y#ys) = map ((#) x) (xs ⫴ (y#ys)) @  map ((#) y) ((x#xs) ⫴ ys)

---
**cnf_concurrency [∥]** :: *'a CNF ⇒ 'a CNF ⇒ 'a CNF*

&nbsp;&nbsp;&nbsp;&nbsp;cnf_concurrency xs ys = concat [path_m ⫴ path_n. path_m ← xs, path_n ← ys]

---
**is_rounded** :: *'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;is_rounded p ≡ Domain (post p) ⊆ Pre p

---
**is_exact** :: *'a Program ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;is_exact p ≡ is_rounded p ∧ is_feasible p

---
**feasible_version** :: *'a Program ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;feasible_version p ≡ 〈State = S p, Pre = Pre p ∩ Domain (post p), post = post p〉

---
**rounded_version** :: *'a Program ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;rounded_version p ≡ 〈State = S p, Pre = Pre p , post = post p /<sub>r</sub> Pre p〉

---
**exact_version** :: *'a Program ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;exact_version p ≡ 〈State = S p, Pre = Pre p ∩ Domain (post p) , post = post p /<sub>r</sub> Pre p〉

---
**civilized_n** :: *'a Program ⇒ 'a Program set ⇒ nat ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;civilized_n x B 0 = (((x ∈ B) ∨ x = Fail {} ∨ x = Skip (complete_state (set_to_list B))) ∧ finite B)

&nbsp;&nbsp;&nbsp;&nbsp;civilized_n x B (n + 1) = (((∃a b. civilized_n a B n ∧ civilized_n b B n ∧ (a ; b = x ∨ a ∪<sub>p</sub> b = x)) ∧ finite B) ∨ civilized_n x B n)

---
**civilized** :: *'a Program ⇒ 'a Program set ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;civilized x B ≡ (∃n. civilized_n x B n)

---
**equal_cnf** :: *'a CNF ⇒ 'a CNF ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;equal_cnf a b ≡ (set a = set b) ∧ (size a = 1) = (size b = 1)

---
**restrict_path** :: *'a Program list ⇒ 'a set ⇒ 'a Program list*

&nbsp;&nbsp;&nbsp;&nbsp;restrict_path [ ] C = [ ]

&nbsp;&nbsp;&nbsp;&nbsp;restrict_path (x#xs) C = (x /<sub>p</sub> C)#xs

---
**restriction_cnf [/<sub>c</sub>]** :: *'a CNF ⇒ 'a set ⇒ 'a CNF*

&nbsp;&nbsp;&nbsp;&nbsp;restriction_cnf p C ≡ [restrict_path path_p C. path_p ← p]

---
**corestrict_path** :: *'a Program list ⇒ 'a set ⇒ 'a Program list*

&nbsp;&nbsp;&nbsp;&nbsp;corestrict_path [ ] C = [ ]

&nbsp;&nbsp;&nbsp;&nbsp;corestrict_path (xs@[x]) C = xs@[x ∖<sub>p</sub> C]

---
**corestriction_cnf [∖<sub>c</sub>]** :: *'a CNF ⇒ 'a set ⇒ 'a CNF*

&nbsp;&nbsp;&nbsp;&nbsp;corestriction_cnf p C ≡ [corestrict_path path_p C. path_p ← p]

---
**complete_cnf_state** :: *'a CNF ⇒ 'a set*

&nbsp;&nbsp;&nbsp;&nbsp;complete_cnf_state p ≡ ⋃ {complete_state tr| tr. tr ∈ set p }

---
**normal_of** :: *'a CNF ⇒ 'a Program set ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;normal_of p xs ≡ (basic p ⊆ (xs ∪ {Fail {}, Skip (complete_state (set_to_list xs))})) ∧ finite xs

---
**feas_of** :: *'a Program ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;feas_of p ≡ 〈State=S p, Pre=Pre p ∩ Domain (post p), post=post p〉

---
**set_to_list** :: *'a set ⇒ 'a list*

&nbsp;&nbsp;&nbsp;&nbsp;set_to_list s = (SOME l. set l = s)

---
**nmb_interleavings_pre** :: *nat ⇒ nat ⇒ nat*

&nbsp;&nbsp;&nbsp;&nbsp;nmb_interleavings_pre x y ≡ factorial (x + y) div (factorial x * factorial y)

---
**nmb_interleavings** :: *'a list ⇒ 'a list ⇒ nat*

&nbsp;&nbsp;&nbsp;&nbsp;nmb_interleavings xs ys ≡ nmb_interleavings_pre (size xs) (size ys)

---
**list_equiv** :: *'a Program list ⇒ 'a Program list ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;list_equiv [ ] [ ] = True

&nbsp;&nbsp;&nbsp;&nbsp;list_equiv (x#xs) (y#ys) = ((x ≡<sub>p</sub> y) ∧ list_equiv xs ys)

&nbsp;&nbsp;&nbsp;&nbsp;list_equiv _ _ = False

---
**cnf_size** :: *'a CNF ⇒ nat*

&nbsp;&nbsp;&nbsp;&nbsp;cnf_size [ ] = 0

&nbsp;&nbsp;&nbsp;&nbsp;cnf_size (x#xs) = length x + cnf_size xs + 1

---
**equiv_list** :: *'a Program list ⇒ 'a Program list ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;equiv_list [ ] [ ] = True

&nbsp;&nbsp;&nbsp;&nbsp;equiv_list (x#xs) [ ] = False

&nbsp;&nbsp;&nbsp;&nbsp;equiv_list [ ] (y#ys) = False

&nbsp;&nbsp;&nbsp;&nbsp;equiv_list (x#xs) (y#ys) = (x ≡<sub>p</sub> y ∧ equiv_list xs ys)

---
**cnf_concurrency2** :: *'a CNF ⇒ 'a CNF ⇒ 'a set ⇒ 'a Program*

&nbsp;&nbsp;&nbsp;&nbsp;cnf_concurrency2 [ ] ys C = Fail {}

&nbsp;&nbsp;&nbsp;&nbsp;cnf_concurrency2 xs [ ] C = Fail {}

&nbsp;&nbsp;&nbsp;&nbsp;cnf_concurrency2 (x#xs) (y#ys) C = 
     (case (xs , ys) of
        ([ ], [ ]) ⇒ (case (x, y) of 
          ([ ], [ ]) ⇒ Skip C |
          ([a], [b]) ⇒ a;b ∪<sub>p</sub> b;a |
          ([ ], bs) ⇒ evaluate [bs] C |
          (as, [ ]) ⇒ evaluate [as] C |
          (a#as, b#bs) ⇒ a; (cnf_concurrency2 [as] [b#bs] C) ∪<sub>p</sub> b; (cnf_concurrency2 [a#as] [bs] C)) |
        (f#fs, [ ]) ⇒ cnf_concurrency2 [x] [y] C ∪<sub>p</sub> cnf_concurrency2 (f#fs) [y] C |
        ([ ], g#gs) ⇒ cnf_concurrency2 [x] [y] C ∪<sub>p</sub> cnf_concurrency2 [x] (g#gs) C |
        (f#fs, g#gs) ⇒ cnf_concurrency2 [x] (y#g#gs) C ∪<sub>p</sub> cnf_concurrency2 (f#fs) (y#g#gs) C
  )

---
**factorial** :: *nat ⇒ nat*

&nbsp;&nbsp;&nbsp;&nbsp;factorial 0 = 1

&nbsp;&nbsp;&nbsp;&nbsp;factorial (n + 1) = (n + 1) * factorial n

---
**sum** :: *nat list ⇒ nat*

&nbsp;&nbsp;&nbsp;&nbsp;sum [ ] = 0

&nbsp;&nbsp;&nbsp;&nbsp;sum (x#xs) = x + sum xs

---
## Relation_operations.thy

**restrict_r [/<sub>r</sub>]** :: *'a rel ⇒ 'a set ⇒ 'a rel*

&nbsp;&nbsp;&nbsp;&nbsp;restrict_r R S = {r ∈ R. fst r ∈ S}

---
**inv_restrict_r [/<sub>-</sub><sub>r</sub>]** :: *'a rel ⇒ 'a set ⇒ 'a rel*

&nbsp;&nbsp;&nbsp;&nbsp;inv_restrict_r R S = {r ∈ R. fst r ∉ S}

---
**corestrict_r [∖<sub>r</sub>]** :: *'a rel ⇒ 'a set ⇒ 'a rel*

&nbsp;&nbsp;&nbsp;&nbsp;corestrict_r R S = {r ∈ R. snd r ∈ S}

---
**inv_corestrict_r [∖<sub>-</sub><sub>r</sub>]** :: *'a rel ⇒ 'a set ⇒ 'a rel*

&nbsp;&nbsp;&nbsp;&nbsp;inv_corestrict_r R S = {r ∈ R. snd r ∉ S}

---
**is_function** :: *'a rel ⇒ bool*

&nbsp;&nbsp;&nbsp;&nbsp;is_function R = (∀r<sub>1</sub> ∈ R.∀r<sub>2</sub>∈R. fst r<sub>1</sub> = fst r<sub>2</sub> → snd r<sub>1</sub> = snd r<sub>2</sub>)

---
# Theorems and Lemmas

## MyTheory.thy

**this_lemma**

&nbsp;&nbsp;&nbsp;&nbsp;((m::nat) + n)*(m+n) = m*m + 2*m*n + n*n

---
## PRISM.thy

**cond_for_commutative_1**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p p<sub>1</sub> ∩ Pre p<sub>2</sub> = {} ⟹ Range_p p<sub>2</sub> ∩ Pre p<sub>1</sub> = {} ⟹ commute_programs3 p<sub>1</sub> p<sub>2</sub>

---
**distinct_state_range_dist_from_pre**

&nbsp;&nbsp;&nbsp;&nbsp;used_states p<sub>1</sub> ∩ used_states p<sub>2</sub> = {} ⟹ Range_p p<sub>1</sub> ∩ Pre p<sub>2</sub> = {} ∧ Range_p p<sub>2</sub> ∩ Pre p<sub>1</sub> = {}

---
&nbsp;&nbsp;&nbsp;&nbsp;used_states p<sub>1</sub> ∩ used_states p<sub>2</sub> = {} ⟹ commute_programs1 p<sub>1</sub> p<sub>2</sub>

---
&nbsp;&nbsp;&nbsp;&nbsp;x; until_loop a C b n ≡<sub>p</sub> until_loop (x;a) C b n

---
&nbsp;&nbsp;&nbsp;&nbsp;p;q ≡<sub>p</sub> p; (q /<sub>p</sub> (Range_p p))

---
## T_03_Basic_programs.thy

**special_empty1**

&nbsp;&nbsp;&nbsp;&nbsp;Skip {} = Fail {}

---
**special_empty2**

&nbsp;&nbsp;&nbsp;&nbsp;Havoc {} = Fail {}

---
**special_empty3**

&nbsp;&nbsp;&nbsp;&nbsp;Havoc {} = Infeas {}

---
&nbsp;&nbsp;&nbsp;&nbsp;Havoc C = 〈State=C, Pre=TRUE C, post=TRUE<sub>r</sub> C 〉

---
&nbsp;&nbsp;&nbsp;&nbsp;Skip C = 〈State=C, Pre=TRUE C, post=ID C〉

---
&nbsp;&nbsp;&nbsp;&nbsp;Fail C = 〈State=C, Pre=FALSE, post=FALSE〉

---
&nbsp;&nbsp;&nbsp;&nbsp;Infeas C = 〈State=C, Pre=TRUE C, post=FALSE〉

---
**special_refine1**

&nbsp;&nbsp;&nbsp;&nbsp;Infeas C ⊑<sub>p</sub> Skip C

---
**special_refine2**

&nbsp;&nbsp;&nbsp;&nbsp;Skip C ⊑<sub>p</sub> Havoc C

---
**special_refine3**

&nbsp;&nbsp;&nbsp;&nbsp;Havoc C ⊑<sub>p</sub> Fail C

---
**special_refine4**

&nbsp;&nbsp;&nbsp;&nbsp;Infeas C ⊑<sub>p</sub> Fail C

---
**special_specialize1**

&nbsp;&nbsp;&nbsp;&nbsp;Fail C ⊆<sub>p</sub> Infeas C

---
**special_specialize2**

&nbsp;&nbsp;&nbsp;&nbsp;Infeas C ⊆<sub>p</sub> Skip C

---
**special_specialize3**

&nbsp;&nbsp;&nbsp;&nbsp;Skip C ⊆<sub>p</sub> Havoc C

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ Fail D ⊑<sub>p</sub> Fail C

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ Fail C ⊆<sub>p</sub> Fail D

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ Infeas D ⊑<sub>p</sub> Infeas C

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ Infeas C ⊆<sub>p</sub> Infeas D

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ Skip D ⊑<sub>p</sub> Skip C

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ Skip C ⊆<sub>p</sub> Skip D

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ Havoc C ⊑<sub>p</sub> Havoc D

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ Havoc D ⊑<sub>p</sub> Havoc C

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ Havoc C ⊆<sub>p</sub> Havoc D

---
## Characteristic_relation.thy

**char_rel_is_unique_in_equality_1**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> = p<sub>2</sub> ⟹ char_rel p<sub>1</sub> = char_rel p<sub>2</sub>

---
**equal_charrel1**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> = p<sub>2</sub> ⟹ char_rel p<sub>1</sub> = char_rel p<sub>2</sub>

---
**equiv_charrel1**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ≡<sub>p</sub> p<sub>2</sub> ⟹ char_rel p<sub>1</sub> = char_rel p<sub>2</sub>

---
**char_rel_is_unique_in_equality_2**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p<sub>1</sub>, p<sub>2</sub>] ⟹ (char_rel p<sub>1</sub> = char_rel p<sub>2</sub>) ⟹ (p<sub>1</sub> = p<sub>2</sub>)

---
**char_rel_is_unique_in_equal_2**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p<sub>1</sub>, p<sub>2</sub>] ⟹ (char_rel p<sub>1</sub> = char_rel p<sub>2</sub>) ⟹ (p<sub>1</sub> = p<sub>2</sub>)

---
**equiv_charrel2**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p<sub>1</sub>, p<sub>2</sub>] ⟹ (char_rel p<sub>1</sub> = char_rel p<sub>2</sub>) = (p<sub>1</sub> ≡<sub>p</sub> p<sub>2</sub>)

---
**char_rel_choice**

&nbsp;&nbsp;&nbsp;&nbsp;char_rel (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>) = char_rel p<sub>1</sub> ∪ char_rel p<sub>2</sub>

---
**char_rel_composition**

&nbsp;&nbsp;&nbsp;&nbsp;char_rel (p<sub>1</sub> ; p<sub>2</sub>) = char_rel p<sub>1</sub> O char_rel p<sub>2</sub>

---
**char_rel_restriction**

&nbsp;&nbsp;&nbsp;&nbsp;char_rel (p /<sub>p</sub> C) = char_rel p /<sub>r</sub> C

---
**char_rel_corestriction**

&nbsp;&nbsp;&nbsp;&nbsp;char_rel (p ∖<sub>p</sub> C) = char_rel p ∖<sub>r</sub> C

---
**char_rel_strengthens**

&nbsp;&nbsp;&nbsp;&nbsp;strengthens p<sub>1</sub> p<sub>2</sub> ⟹ char_rel p<sub>1</sub> /<sub>r</sub> Domain (char_rel p<sub>2</sub>) ⊆ char_rel p<sub>2</sub>

---
**char_rel_weakens**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p<sub>1</sub> ⟹ weakens p<sub>1</sub> p<sub>2</sub> ⟹ Domain (char_rel p<sub>2</sub>) ⊆ Domain (char_rel p<sub>1</sub>)

---
**char_rel_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;p ⊑<sub>p</sub> q ⟹ char_rel p /<sub>r</sub> (Domain (char_rel q)) ⊆ char_rel q

---
**charrel_strengthen**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p, q] ⟹ char_rel p /<sub>r</sub> (Domain (char_rel q)) ⊆ char_rel q = strengthens p q

---
**charrel_weaken**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p, q] ⟹ Domain (char_rel q) ⊆ Domain (char_rel p) = weakens p q

---
**charrel_specialize**

&nbsp;&nbsp;&nbsp;&nbsp;q ⊆<sub>p</sub> p ⟹ char_rel q < char_rel p

---
**charrel_refine**

&nbsp;&nbsp;&nbsp;&nbsp;q ⊑<sub>p</sub> p ⟹ char_rel q /<sub>r</sub> (Pre p) < char_rel p

---
**char_rel_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;Field (char_rel a) ⊆ S a

---
## Definitions.thy

&nbsp;&nbsp;&nbsp;&nbsp;〈State={}, Pre={1::nat}, post={(1,2)}〉 ⊆<sub>p</sub> 〈State={}, Pre={1::nat}, post={(1,2)}〉

---
&nbsp;&nbsp;&nbsp;&nbsp;Pre p ⊆ I ∧ Range_p p ⊆ I ⟹ Range_p (p /<sub>p</sub> I) ⊆ I

---
&nbsp;&nbsp;&nbsp;&nbsp;a ∪<sub>p</sub> (a ∩<sub>p</sub> b) ≡<sub>p</sub> a

---
&nbsp;&nbsp;&nbsp;&nbsp;a ∩<sub>p</sub> (a ∪<sub>p</sub> b) ≡<sub>p</sub> a

---
**civ_n_finite**

&nbsp;&nbsp;&nbsp;&nbsp;civilized_n p B n ⟹ finite B

---
## Equalities.thy

**equals_equiv_relation_1**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> = p<sub>2</sub> ⟹ p<sub>1</sub> = p<sub>2</sub>

---
**equals_equiv_relation_2**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> = p<sub>2</sub> ⟹ p<sub>1</sub> ≡<sub>p</sub> p<sub>2</sub>

---
**equals_equiv_relation_3**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> = p<sub>2</sub> ⟹ p<sub>1</sub> ≡<sub>p</sub> p<sub>2</sub>

---
**equal_is_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> = p<sub>1</sub>

---
**equiv_is_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ≡<sub>p</sub> p<sub>1</sub>

---
**equal_is_symetric**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> = p<sub>2</sub> ⟹ p<sub>2</sub> = p<sub>1</sub>

---
**equiv_is_symetric**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ≡<sub>p</sub> p<sub>2</sub> ⟹ p<sub>2</sub> ≡<sub>p</sub> p<sub>1</sub>

---
**equal_is_transitive**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> = p<sub>2</sub> ⟹ p<sub>2</sub> = p<sub>3</sub> ⟹ p<sub>1</sub> = p<sub>3</sub>

---
**equiv_is_transitive**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ≡<sub>p</sub> p<sub>2</sub> ⟹ p<sub>2</sub> ≡<sub>p</sub> p<sub>3</sub> ⟹ p<sub>1</sub> ≡<sub>p</sub> p<sub>3</sub>

---
**inverse_equality_1**

&nbsp;&nbsp;&nbsp;&nbsp;¬ p<sub>1</sub> ≡<sub>p</sub> p<sub>2</sub> ⟹ ¬ p<sub>1</sub> = p<sub>2</sub>

---
**inverse_equality_2**

&nbsp;&nbsp;&nbsp;&nbsp;¬ p<sub>1</sub> ≡<sub>p</sub> p<sub>2</sub> ⟹ ¬ p<sub>1</sub> = p<sub>2</sub>

---
**inverse_equality_3**

&nbsp;&nbsp;&nbsp;&nbsp;¬ p<sub>1</sub> = p<sub>2</sub> ⟹ ¬ p<sub>1</sub> = p<sub>2</sub>

---
**empty_state_space_equal**

&nbsp;&nbsp;&nbsp;&nbsp;S a = {} ⟹ S b = {} ⟹ a = b

---
## Feasibility.thy

**equal_maintains_feasiblity**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p<sub>1</sub> ⟹ p<sub>1</sub> = p<sub>2</sub> ⟹ is_feasible p<sub>2</sub>

---
**equiv_maintains_feasiblity**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p<sub>1</sub> ⟹ p<sub>1</sub> ≡<sub>p</sub> p<sub>2</sub> ⟹ is_feasible p<sub>2</sub>

---
## Helper.thy

**rel_id_prop**

&nbsp;&nbsp;&nbsp;&nbsp;Field a ⊆ C ⟹ a O Id_on C = a

---
**list_comp_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;∀p. [p i. i ← [0..((int (n + 1)))]] = [p i. i ← [0..(int n)]] @ [p ((int (n + 1)))]

---
**orig_is_permutation_1**

&nbsp;&nbsp;&nbsp;&nbsp;List.member (insert_all x xs) (x#xs)

---
**permutation_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;List.member (permutations xs) xs

---
**l1**

&nbsp;&nbsp;&nbsp;&nbsp;set (insert_all x (ps)) ≠ {}

---
**l2**

&nbsp;&nbsp;&nbsp;&nbsp;x#xs ∈ set (insert_all x xs)

---
**l3**

&nbsp;&nbsp;&nbsp;&nbsp;xs@[x] ∈ set (insert_all x xs)

---
**l4**

&nbsp;&nbsp;&nbsp;&nbsp;a@x#b ∈ set (insert_all x (a@b))

---
**l5**

&nbsp;&nbsp;&nbsp;&nbsp;p ∈ set (insert_all x (a # xs)) ⟹ (hd p = x) ∨ (hd p = a)

---
**l5_2**

&nbsp;&nbsp;&nbsp;&nbsp;p ∈ set (insert_all x (a # xs)) ⟹ (h_hd p = [x]) ∨ (h_hd p = [a])

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

&nbsp;&nbsp;&nbsp;&nbsp;a#p ∈ set (insert_all x (a # xs)) ⟹ p ∈ set (insert_all x xs)

---
**l10**

&nbsp;&nbsp;&nbsp;&nbsp;p ∈ set (insert_all x xs) ⟹ ∃a b. a@x#b=p

---
**l11**

&nbsp;&nbsp;&nbsp;&nbsp;p ∈ set (insert_all x ps) ⟹ x ∈ set p

---
**l12**

&nbsp;&nbsp;&nbsp;&nbsp;y ∈ set p ⟹ p ∈ set (insert_all x (a # ps)) ⟹ y ≠ a ⟹ p' ∈ set (insert_all x ps) ⟹ y ∈ set p'

---
**l13**

&nbsp;&nbsp;&nbsp;&nbsp;y ∈ set p ⟹ p ∈ set (insert_all x ps) ⟹ y ∉ set ps ⟹ y = x

---
**permutation_symmetric_1**

&nbsp;&nbsp;&nbsp;&nbsp;List.member (permutations xs) p ⟹ List.member p y ⟹ List.member xs y

---
**l14**

&nbsp;&nbsp;&nbsp;&nbsp;p ∈ set (insert_all x ps) ⟹ ∃a b. p = a @ x # b ∧ ps = a @ b

---
**count_invariant**

&nbsp;&nbsp;&nbsp;&nbsp;List.member (permutations xs) p ⟹ count_list p y = count_list xs y

---
**permutation_split**

&nbsp;&nbsp;&nbsp;&nbsp;List.member (permutations (x#xs)) xs' ⟹ ∃a b. a@x#b = xs'

---
**permutation_size**

&nbsp;&nbsp;&nbsp;&nbsp;List.member (permutations x1) x2 ⟹ size x2 = size x1

---
**insert_perm_rel**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (insert_all a xs) ⟹ x ∈ set (permutations (a#xs))

---
**insert_all_set_equality**

&nbsp;&nbsp;&nbsp;&nbsp;p1 ∈ set (insert_all x ps) ⟹ set p1 = insert x (set ps)

---
**permutation_set_equality**

&nbsp;&nbsp;&nbsp;&nbsp;p1 ∈ set (permutations xs) ⟹ set xs = set p1

---
**permutation_set_equality_2**

&nbsp;&nbsp;&nbsp;&nbsp;p1 ∈ set (permutations xs) ⟹ p2 ∈ set (permutations xs) ⟹ set p1 = set p2

---
**permutation_split_set**

&nbsp;&nbsp;&nbsp;&nbsp;x2 ∈ set (permutations (a # x1)) ⟹ ∃y z. x2 = y @ a # z ∧ y @ z ∈ set (permutations x1)

---
**insert_4**

&nbsp;&nbsp;&nbsp;&nbsp;(xs @ ([x] @ ys)) ∈ set (insert_all x (xs @ ys))

---
**count_eq_member**

&nbsp;&nbsp;&nbsp;&nbsp;List.count_list p y > 0 = List.member p y

---
**member_invariant**

&nbsp;&nbsp;&nbsp;&nbsp;p ∈ set (permutations xs) ⟹ List.member p y ⟹ List.member xs y

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

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (permutations xs) ⟹ length x = length xs

---
**perm_inv_2**

&nbsp;&nbsp;&nbsp;&nbsp;xb@xe ∈ set (permutations x1) ⟹ xb@a#xe ∈ set (permutations (a # x1))

---
**singleton_permutation**

&nbsp;&nbsp;&nbsp;&nbsp;[x] ∈ set (permutations xs) ⟹ xs = [x]

---
**count_invariant_2**

&nbsp;&nbsp;&nbsp;&nbsp;∀y. count_list p y = count_list xs y ⟹ List.member (permutations xs) p

---
**count_invariant_3**

&nbsp;&nbsp;&nbsp;&nbsp;x1 ∉ set (permutations x2) ⟹ ∃t. count_list x1 t ≠ count_list x2 t

---
**permutations_set_equality**

&nbsp;&nbsp;&nbsp;&nbsp;x1 ∈ set (permutations x2) ⟹ set (permutations x1) = set (permutations x2)

---
**perm_lemma_1**

&nbsp;&nbsp;&nbsp;&nbsp;x1 ∉ set (permutations x2) ⟹ a # x1 ∉ set (permutations (a # x2))

---
**perm_split**

&nbsp;&nbsp;&nbsp;&nbsp;a # x1 ∈ set (permutations (y @ a # z)) ⟹ x1 ∈ set (permutations (y @ z))

---
**perm_inv_3**

&nbsp;&nbsp;&nbsp;&nbsp;x1 ∈ set (permutations x2) ⟹ x2 ∈ set (permutations x1)

---
**orig_is_permutation_3**

&nbsp;&nbsp;&nbsp;&nbsp;List.member (permutations x1) x2 ⟹ List.member (permutations x2) x1

---
**complete_state_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;fold (λ p s. S p ∪ s) xs C = foldl (λ s p. S p ∪ s) C xs

---
**complete_state_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;complete_state xs = fold (∪) (map (λp. S p) xs) {}

---
**complete_state_prop_3**

&nbsp;&nbsp;&nbsp;&nbsp;fold (λ p s. S p ∪ s) xs C = fold (∪) (map (λp. S p) xs) C

---
**complete_state_prop_4**

&nbsp;&nbsp;&nbsp;&nbsp;fold (∪) xs C = fold (∪) xs {} ∪ C

---
**complete_state_prop_5**

&nbsp;&nbsp;&nbsp;&nbsp;fold (∪) (map (λp. S p) xs) C = fold (∪) (map (λp. S p) xs) {} ∪ C

---
**complete_state_prop**

&nbsp;&nbsp;&nbsp;&nbsp;complete_state (x # xs) = complete_state xs ∪ S x

---
**permutation_complete_state_equality**

&nbsp;&nbsp;&nbsp;&nbsp;x1 ∈ set (permutations x2) ⟹ complete_state x2 = complete_state x1

---
**permutation_S_equiv**

&nbsp;&nbsp;&nbsp;&nbsp;x1 ∈ set (permutations x2) ⟹ fold (∪) (map (λp. S p) x1) {} ≡ fold (∪) (map (λp. S p) x2) {}

---
**complete_state_union_1**

&nbsp;&nbsp;&nbsp;&nbsp;complete_state (a # xs) = complete_state (xs) ∪ complete_state ([a])

---
**complete_state_union_2**

&nbsp;&nbsp;&nbsp;&nbsp;complete_state (xs) = complete_state (xs) ∪ complete_state ([ ])

---
**complete_state_union_3**

&nbsp;&nbsp;&nbsp;&nbsp;complete_state (a @ b) = complete_state a ∪ complete_state b

---
**perm_1**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (permutations xs) ⟹ a#x ∈ set (permutations (a#xs))

---
**perm_2**

&nbsp;&nbsp;&nbsp;&nbsp;set (permutations (a#xs)) = set (permutations (xs@[a]))

---
**perm_3**

&nbsp;&nbsp;&nbsp;&nbsp;set (permutations ([a]@st@ed)) = set (permutations (st@[a]@ed))

---
&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (permutations xs) ⟹ y ∈ set (permutations ys) ⟹ x@y ∈ set (permutations (xs@ys))

---
**elements_atomic**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ get_atomic p ⟹ is_atomic x

---
**empty_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;finite s ⟹ set_to_list s = [ ] ≡ s = {}

---
**empty_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ get_atomic p = {} ⟹ Pre p = {}

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

&nbsp;&nbsp;&nbsp;&nbsp;finite (S p) ⟹ x ∉ F ⟹ S p = insert x F ⟹ q = 〈State={s|s. s ∈ State p ∧ s ∈ F}, Pre={s|s. s ∈ Pre p ∧ s ∈ F}, post={(a,b)|a b. a ∈ F ∧ b ∈ F ∧ (a,b) ∈ post p}〉 ⟹ r = 〈State={s|s. s ∈ State p}, Pre={s|s. s ∈ Pre p}, post={(a,b)|a b. (a = x ∨ b = x) ∧ (a,b) ∈ post p}〉 ⟹ p ≡<sub>p</sub> q ∪<sub>p</sub> r

---
**decomp_program2**

&nbsp;&nbsp;&nbsp;&nbsp;finite (S p) ⟹ x ∉ F ⟹ S p = insert x F  ⟹ finite (S 〈State={s|s. s ∈ State p ∧ s ∈ F}, Pre={s|s. s ∈ Pre p ∧ s ∈ F}, post={(a,b)|a b. a ∈ F ∧ b ∈ F ∧ (a,b) ∈ post p}〉)

---
**decomp_program3**

&nbsp;&nbsp;&nbsp;&nbsp;finite (S p) ⟹ x ∉ F ⟹ S p = insert x F  ⟹ finite (S 〈State={s|s. s ∈ State p}, Pre={s|s. s ∈ Pre p}, post={(a,b)|a b. (a = x ∨ b = x) ∧ (a,b) ∈ post p}〉)

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

&nbsp;&nbsp;&nbsp;&nbsp;finite (S p) ⟹ finite (get_atomic p)

---
**atomic_idem**

&nbsp;&nbsp;&nbsp;&nbsp;is_atomic p ⟹ (get_atomic p) ∪ {p} = get_atomic (p ∪<sub>p</sub> p)

---
**atomic_state**

&nbsp;&nbsp;&nbsp;&nbsp;is_atomic x ⟹ S x = State x

---
**atomic_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;is_atomic x ⟹ ∃a b. 〈State={a,b}, Pre={a}, post={(a,b)}〉 = x

---
**atomic_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;∃a b. 〈State={a,b}, Pre={a}, post={(a,b)}〉 = x ⟹ is_atomic x

---
**atomic_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;∃a b. 〈State={a,b}, Pre={a}, post={(a,b)}〉 = x ≡ is_atomic x

---
**atomic_post**

&nbsp;&nbsp;&nbsp;&nbsp;is_atomic x ⟹ restr_post x = post x

---
**atomic_monotone**

&nbsp;&nbsp;&nbsp;&nbsp;get_atomic p ⊆ get_atomic (p ∪<sub>p</sub> q)

---
**atomic_split**

&nbsp;&nbsp;&nbsp;&nbsp;finite (get_atomic p) ⟹ finite (get_atomic q) ⟹ (get_atomic p) ∪ (get_atomic q) = get_atomic (p ∪<sub>p</sub> q)

---
&nbsp;&nbsp;&nbsp;&nbsp;is_atomic x  ⟹ (get_atomic p) ∪ {x} = get_atomic (p ∪<sub>p</sub> x)

---
**fail_atomic**

&nbsp;&nbsp;&nbsp;&nbsp;get_atomic (Fail {}) = {}

---
**set_list_set**

&nbsp;&nbsp;&nbsp;&nbsp;finite xs ⟹ set (set_to_list xs) = xs

---
**set_list_prop**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ xs = set_to_list (insert x F) ⟹ ∃a b. a@x#b = xs

---
**set_to_list_distinct**

&nbsp;&nbsp;&nbsp;&nbsp;xs = set_to_list F ⟹ distinct xs

---
**set_to_list_size**

&nbsp;&nbsp;&nbsp;&nbsp;size (set_to_list F) = card F

---
**set_to_list_one**

&nbsp;&nbsp;&nbsp;&nbsp;set_to_list {x} = [x]

---
**atomic_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;is_atomic x ⟹ get_atomic x = {x}

---
**Consistent_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible (feasible_version p)

---
**Consistent_round**

&nbsp;&nbsp;&nbsp;&nbsp;is_rounded (rounded_version p)

---
**Consistent_exact**

&nbsp;&nbsp;&nbsp;&nbsp;is_exact (exact_version p)

---
**Feasible_round**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ is_feasible (rounded_version p)

---
**Round_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;is_rounded p ⟹ is_rounded (feasible_version p)

---
**Equiv_prog**

&nbsp;&nbsp;&nbsp;&nbsp;a ≡<sub>p</sub> b ≡ (Pre (rounded_version a) = Pre (rounded_version b) ∧ post (rounded_version a) = post (rounded_version b))

---
**Charrel_restriction**

&nbsp;&nbsp;&nbsp;&nbsp;rounded_version (p /<sub>p</sub> C) = rounded_version p /<sub>p</sub> C

---
**Charrel_choice**

&nbsp;&nbsp;&nbsp;&nbsp;rounded_version (p ∪<sub>p</sub> q) = rounded_version p ∪<sub>p</sub> rounded_version q

---
**Charrel_composition**

&nbsp;&nbsp;&nbsp;&nbsp;rounded_version (p ; q) = rounded_version p ; rounded_version q

---
**Charrel_corestriction**

&nbsp;&nbsp;&nbsp;&nbsp;rounded_version (p ∖<sub>p</sub> C) = rounded_version p ∖<sub>p</sub> C

---
**Restrict_rounded**

&nbsp;&nbsp;&nbsp;&nbsp;is_rounded p ⟹ is_rounded (p /<sub>p</sub> C)

---
**Choice_rounded**

&nbsp;&nbsp;&nbsp;&nbsp;is_rounded (p ∪<sub>p</sub> q)

---
&nbsp;&nbsp;&nbsp;&nbsp;is_rounded q ⟹ is_rounded p ⟹ is_rounded (p;q)

---
**Corestrict_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ is_feasible ((p /<sub>p</sub> (Pre p ∩ Domain (post p ∖<sub>r</sub> C))) ∖<sub>p</sub> C)

---
## Implementation.thy

**implementation_1**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ X ⟹ x ∈ Domain (R) ⟹ x ∈ Domain (R /<sub>r</sub> X)

---
**implementation_theorem**

&nbsp;&nbsp;&nbsp;&nbsp;implements p<sub>2</sub> p<sub>1</sub> ⟹ is_feasible p<sub>1</sub>

---
**implementation_is_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p<sub>1</sub> ⟹ implements p<sub>1</sub> p<sub>1</sub>

---
**implementation_is_transitive**

&nbsp;&nbsp;&nbsp;&nbsp;implements p<sub>1</sub> p<sub>2</sub> ⟹ implements p<sub>2</sub> p<sub>3</sub> ⟹ implements p<sub>1</sub> p<sub>3</sub>

---
**implementation_is_antisymetric**

&nbsp;&nbsp;&nbsp;&nbsp;implements p<sub>1</sub> p<sub>2</sub> ⟹ implements p<sub>2</sub> p<sub>1</sub> ⟹ p<sub>1</sub> ≡<sub>p</sub> p<sub>2</sub>

---
## Independence.thy

**independent_symetric**

&nbsp;&nbsp;&nbsp;&nbsp;independent pâ‡©1 pâ‡©2 = independent pâ‡©2 pâ‡©1

---
**independent_weakens**

&nbsp;&nbsp;&nbsp;&nbsp;independent pâ‡©1 pâ‡©2 âŸ¹ Pre pâ‡©2 â‰  {} âŸ¹ Â¬weakens pâ‡©1 pâ‡©2

---
**independent_strengthens**

&nbsp;&nbsp;&nbsp;&nbsp;independent pâ‡©1 pâ‡©2 âŸ¹ strengthens pâ‡©1 pâ‡©2

---
## Range_p.thy

**same_range_p_3**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ≡<sub>p</sub> p<sub>2</sub> ⟹ Range_p p<sub>1</sub> = Range_p p<sub>2</sub>

---
**same_range_p_2**

&nbsp;&nbsp;&nbsp;&nbsp;a = b ⟹ Range_p a = Range_p b

---
**range_p_explicit_1**

&nbsp;&nbsp;&nbsp;&nbsp;y ∈ Range_p a ⟹ ∃x. (x,y) ∈ post a ∧ x ∈ Pre a

---
**range_p_explicit_2**

&nbsp;&nbsp;&nbsp;&nbsp;(x,y) ∈ post a ∧ x ∈ Pre a ⟹ y ∈ Range_p a

---
**no_range_fail**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ Range_p p = {} ⟹ p ≡<sub>p</sub> Fail {}

---
## Refinement.thy

**refines_is_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ⊑<sub>p</sub> p<sub>1</sub>

---
**refines_is_transitive_e**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ⊑<sub>p</sub> p<sub>2</sub> ⟹ p<sub>2</sub> ⊑<sub>p</sub> p<sub>3</sub> ⟹ extends p<sub>1</sub> p<sub>3</sub>

---
**refines_is_transitive_w**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ⊑<sub>p</sub> p<sub>2</sub> ⟹ p<sub>2</sub> ⊑<sub>p</sub> p<sub>3</sub> ⟹ weakens p<sub>1</sub> p<sub>3</sub>

---
**refines_is_transitive_s**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ⊑<sub>p</sub> p<sub>2</sub> ⟹ p<sub>2</sub> ⊑<sub>p</sub> p<sub>3</sub> ⟹ strengthens p<sub>1</sub> p<sub>3</sub>

---
**refines_is_transitive**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ⊑<sub>p</sub> p<sub>2</sub> ⟹ p<sub>2</sub> ⊑<sub>p</sub> p<sub>3</sub> ⟹ p<sub>1</sub> ⊑<sub>p</sub> p<sub>3</sub>

---
**refines_is_antisymetric**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ⊑<sub>p</sub> p<sub>2</sub> ⟹ p<sub>2</sub> ⊑<sub>p</sub> p<sub>1</sub> ⟹ p<sub>1</sub> ≡<sub>p</sub> p<sub>2</sub>

---
**refines_is_preorder**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ⊑<sub>p</sub> p<sub>1</sub> ∧ (p<sub>2</sub> ⊑<sub>p</sub> p<sub>3</sub> ∧ p<sub>3</sub> ⊑<sub>p</sub> p<sub>4</sub> → p<sub>2</sub> ⊑<sub>p</sub> p<sub>4</sub>)

---
**refines_is_order**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> ⊑<sub>p</sub> p<sub>1</sub>) ∧ (p<sub>2</sub> ⊑<sub>p</sub> p<sub>3</sub> ∧ p<sub>3</sub> ⊑<sub>p</sub> p<sub>4</sub> → p<sub>2</sub> ⊑<sub>p</sub> p<sub>4</sub>) ∧ (p<sub>5</sub> ⊑<sub>p</sub> p<sub>6</sub> ∧ p<sub>6</sub> ⊑<sub>p</sub> p<sub>5</sub> → p<sub>5</sub> ≡<sub>p</sub> p<sub>6</sub>)

---
**extends_is_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;extends p p

---
**extends_is_transitive**

&nbsp;&nbsp;&nbsp;&nbsp;extends p q ⟹ extends q r ⟹ extends p r

---
**weakens_is_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;weakens p p

---
**weakens_is_transitive**

&nbsp;&nbsp;&nbsp;&nbsp;weakens p q ⟹ weakens q r ⟹ weakens p r

---
**strengthens_is_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;strengthens p p

---
**strengthens_is_transitive_1**

&nbsp;&nbsp;&nbsp;&nbsp;weakens p q ⟹ weakens q r ⟹ strengthens p q ⟹ strengthens q r ⟹ strengthens p r

---
**strengthens_is_transitive_2**

&nbsp;&nbsp;&nbsp;&nbsp;weakens q p ⟹ weakens r q ⟹ strengthens p q ⟹ strengthens q r ⟹ strengthens p r

---
## Relation_operations.thy

**corestriction_restriction_on_relcomp**

&nbsp;&nbsp;&nbsp;&nbsp;r<sub>1</sub> ∖<sub>r</sub> s<sub>1</sub> O r<sub>2</sub> = r<sub>1</sub> O r<sub>2</sub> /<sub>r</sub> s<sub>1</sub>

---
## Subprogram.thy

**specialize_is_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ⊆<sub>p</sub> p<sub>1</sub>

---
**specialize_is_transitive**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ⊆<sub>p</sub> p<sub>2</sub> ⟹ p<sub>2</sub> ⊆<sub>p</sub> p<sub>3</sub> ⟹ p<sub>1</sub> ⊆<sub>p</sub> p<sub>3</sub>

---
**specialize_is_antisymetric**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ⊆<sub>p</sub> p<sub>2</sub> ⟹ p<sub>2</sub> ⊆<sub>p</sub> p<sub>1</sub> ⟹ p<sub>1</sub> ≡<sub>p</sub> p<sub>2</sub>

---
**specialize_is_preorder**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ⊆<sub>p</sub> p<sub>1</sub> ∧ (p<sub>2</sub> ⊆<sub>p</sub> p<sub>3</sub> ∧ p<sub>3</sub> ⊆<sub>p</sub> p<sub>4</sub> → p<sub>2</sub> ⊆<sub>p</sub> p<sub>4</sub>)

---
**specialize_is_order**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> ⊆<sub>p</sub> p<sub>1</sub>) ∧ (p<sub>2</sub> ⊆<sub>p</sub> p<sub>3</sub> ∧ p<sub>3</sub> ⊆<sub>p</sub> p<sub>4</sub> → p<sub>2</sub> ⊆<sub>p</sub> p<sub>4</sub>) ∧ (p<sub>5</sub> ⊆<sub>p</sub> p<sub>6</sub> ∧ p<sub>6</sub> ⊆<sub>p</sub> p<sub>5</sub> → p<sub>5</sub> ≡<sub>p</sub> p<sub>6</sub>)

---
**choice_decomp_1**

&nbsp;&nbsp;&nbsp;&nbsp;a ⊆<sub>p</sub> c ∧ b ⊆<sub>p</sub> c ⟹ a ∪<sub>p</sub> b ⊆<sub>p</sub> c

---
**choice_decomp_2**

&nbsp;&nbsp;&nbsp;&nbsp;a ∪<sub>p</sub> b ⊆<sub>p</sub> c ⟹ a ⊆<sub>p</sub> c ∧ b ⊆<sub>p</sub> c

---
**choice_decomp**

&nbsp;&nbsp;&nbsp;&nbsp;a ⊆<sub>p</sub> c ∧ b ⊆<sub>p</sub> c ≡ a ∪<sub>p</sub> b ⊆<sub>p</sub> c

---
**specialize_equiv**

&nbsp;&nbsp;&nbsp;&nbsp;a ⊆<sub>p</sub> b ⟹ a ≡<sub>p</sub> c ⟹ b ≡<sub>p</sub> d ⟹ c ⊆<sub>p</sub> d

---
**equiv_specialize_transitivity**

&nbsp;&nbsp;&nbsp;&nbsp;S a ⊆ S b ⟹ S c ⊆ S d ⟹ a ≡<sub>p</sub> b ⟹ b ⊆<sub>p</sub> c ⟹ c ≡<sub>p</sub> d ⟹ a ⊆<sub>p</sub> d

---
## Validity.thy

**valid_generalization**

&nbsp;&nbsp;&nbsp;&nbsp;is_valid p ⟹ prop (S p) = prop (State p)

---
**pre_in_s**

&nbsp;&nbsp;&nbsp;&nbsp;is_valid p ⟹ Pre p ⊆ State p

---
**post_in_s**

&nbsp;&nbsp;&nbsp;&nbsp;is_valid p ⟹ (Field (post p) ⊆ State p)

---
**validity_inverse**

&nbsp;&nbsp;&nbsp;&nbsp;is_valid p ⟹ is_valid (p<sup>-</sup><sup>1</sup>)

---
**validity_composition**

&nbsp;&nbsp;&nbsp;&nbsp;all_valid [p<sub>1</sub>, p<sub>2</sub>] ⟹ is_valid (p<sub>1</sub> ; p<sub>2</sub>)

---
**validity_choice**

&nbsp;&nbsp;&nbsp;&nbsp;all_valid [p<sub>1</sub>, p<sub>2</sub>] ⟹ is_valid (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>)

---
**validity_restriction**

&nbsp;&nbsp;&nbsp;&nbsp;is_valid p ⟹ is_valid (p /<sub>p</sub> C)

---
**validity_corestriction**

&nbsp;&nbsp;&nbsp;&nbsp;is_valid p ⟹ is_valid (p ∖<sub>p</sub> C)

---
**validity_equality**

&nbsp;&nbsp;&nbsp;&nbsp;is_valid p ⟹ is_valid q ⟹ p = q ⟹ p = q

---
## Choice.thy

**choice_idem_4**

&nbsp;&nbsp;&nbsp;&nbsp;Fail {} ∪<sub>p</sub> (p ∪<sub>p</sub> p) = Fail {} ∪<sub>p</sub> p

---
**choice_idem_5**

&nbsp;&nbsp;&nbsp;&nbsp;q ∪<sub>p</sub> (p ∪<sub>p</sub> p) = q ∪<sub>p</sub> p

---
**choice_idem_6**

&nbsp;&nbsp;&nbsp;&nbsp;(p ∪<sub>p</sub> p) ∪<sub>p</sub> q = p ∪<sub>p</sub> q

---
**choice_equiv**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> ≡<sub>p</sub> p<sub>1</sub> ⟹ f<sub>2</sub> ≡<sub>p</sub> p<sub>2</sub> ⟹ f<sub>1</sub> ∪<sub>p</sub> f<sub>2</sub> ≡<sub>p</sub> p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>

---
**equality_is_maintained_by_choice**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> = p<sub>1</sub> ⟹ f<sub>2</sub> = p<sub>2</sub> ⟹ f<sub>1</sub> ∪<sub>p</sub> f<sub>2</sub> = p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>

---
**choice_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p<sub>1</sub>, p<sub>2</sub>] ⟹ is_feasible (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>)

---
**condition_for_choice_simplification**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p a ∩ Pre y = {} ⟹ Range_p x ∩ Pre b = {} ⟹ a;b ∪<sub>p</sub> x;y ≡<sub>p</sub> (a ∪<sub>p</sub> x) ; (b ∪<sub>p</sub> y)

---
**choice_range**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>) = Range_p p<sub>1</sub> ∪ Range_p p<sub>2</sub>

---
**refinement_safety_choice_e**

&nbsp;&nbsp;&nbsp;&nbsp;q<sub>1</sub> ⊑<sub>p</sub> p<sub>1</sub> ⟹ q<sub>2</sub> ⊑<sub>p</sub> p<sub>2</sub> ⟹ extends (q<sub>1</sub> ∪<sub>p</sub> q<sub>2</sub>) (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>)

---
**refinement_safety_choice_w**

&nbsp;&nbsp;&nbsp;&nbsp;q<sub>1</sub> ⊑<sub>p</sub> p<sub>1</sub> ⟹ q<sub>2</sub> ⊑<sub>p</sub> p<sub>2</sub> ⟹ weakens (q<sub>1</sub> ∪<sub>p</sub> q<sub>2</sub>) (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>)

---
**refinement_safety_choice_s_1**

&nbsp;&nbsp;&nbsp;&nbsp;q<sub>1</sub> ⊑<sub>p</sub> p<sub>1</sub> ⟹ q<sub>2</sub> ⊑<sub>p</sub> p<sub>2</sub> ⟹ strengthens (q<sub>1</sub> ∪<sub>p</sub> q<sub>2</sub>) (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>)

---
**refinement_safety_choice_s_2**

&nbsp;&nbsp;&nbsp;&nbsp;strengthens q<sub>1</sub> p<sub>2</sub> ⟹ strengthens q<sub>2</sub> p<sub>1</sub> ⟹ q<sub>1</sub> ⊑<sub>p</sub> p<sub>1</sub> ⟹ q<sub>2</sub> ⊑<sub>p</sub> p<sub>2</sub> ⟹ strengthens (q<sub>1</sub> ∪<sub>p</sub> q<sub>2</sub>) (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>)

---
**refinement_safety_choice**

&nbsp;&nbsp;&nbsp;&nbsp;q<sub>1</sub> ⊑<sub>p</sub> p<sub>1</sub> ⟹ q<sub>2</sub> ⊑<sub>p</sub> p<sub>2</sub> ⟹ (q<sub>1</sub> ∪<sub>p</sub> q<sub>2</sub>) ⊑<sub>p</sub> (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>)

---
**refinement_safety_choice**

&nbsp;&nbsp;&nbsp;&nbsp;strengthens a c ⟹ a ⊑<sub>p</sub> b ⟹ (a ∪<sub>p</sub> c) ⊑<sub>p</sub> (b ∪<sub>p</sub> c)

---
**refinement_safety_choice_1**

&nbsp;&nbsp;&nbsp;&nbsp;strengthens q<sub>1</sub> p<sub>2</sub> ⟹ strengthens q<sub>2</sub> p<sub>1</sub> ⟹ q<sub>1</sub> ⊑<sub>p</sub> p<sub>1</sub> ⟹ q<sub>2</sub> ⊑<sub>p</sub> p<sub>2</sub> ⟹ (q<sub>1</sub> ∪<sub>p</sub> q<sub>2</sub>) ⊑<sub>p</sub> (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>)

---
**refinement_safety_choice_2**

&nbsp;&nbsp;&nbsp;&nbsp;independent q<sub>1</sub> p<sub>2</sub> ⟹ independent q<sub>2</sub> p<sub>1</sub> ⟹ q<sub>1</sub> ⊑<sub>p</sub> p<sub>1</sub> ⟹ q<sub>2</sub> ⊑<sub>p</sub> p<sub>2</sub> ⟹ (q<sub>1</sub> ∪<sub>p</sub> q<sub>2</sub>) ⊑<sub>p</sub> (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>)

---
**choice_safety1**

&nbsp;&nbsp;&nbsp;&nbsp;a ⊆<sub>p</sub> b ⟹ a ∪<sub>p</sub> c ⊆<sub>p</sub> b ∪<sub>p</sub> c

---
**implements_safety_choice**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible c ⟹ implements a b ⟹ implements (a ∪<sub>p</sub> c) (b ∪<sub>p</sub> c)

---
**implements_safety_choice**

&nbsp;&nbsp;&nbsp;&nbsp;strengthens a c ⟹ is_feasible c ⟹ implements a b ⟹ implements (a ∪<sub>p</sub> c) (b ∪<sub>p</sub> c)

---
**program_is_specialize_of_choice**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ⊆<sub>p</sub> (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>)

---
**choice_choice_range**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p p ⊆ Range_p (p ∪<sub>p</sub> q)

---
**choice_range_p_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ Range_p (p ∪<sub>p</sub> q) ⟹ x ∉ Range_p p ⟹ x ∈ Range_p q

---
**choice_range_p_prop_3**

&nbsp;&nbsp;&nbsp;&nbsp;x ∉ Range_p (p ∪<sub>p</sub> q) ⟹ x ∉ Range_p p

---
**empty_is_neutral**

&nbsp;&nbsp;&nbsp;&nbsp;S a = {} ⟹ a ∪<sub>p</sub> (b ∪<sub>p</sub> c) = b ∪<sub>p</sub> c

---
**choice_idem_2**

&nbsp;&nbsp;&nbsp;&nbsp;a ∪<sub>p</sub> (a ∪<sub>p</sub> b) = a ∪<sub>p</sub> b

---
**choice_suprogram_prop**

&nbsp;&nbsp;&nbsp;&nbsp;a ⊆<sub>p</sub> c ⟹ b ⊆<sub>p</sub> c ⟹ a ∪<sub>p</sub> b ⊆<sub>p</sub> c

---
## Composition.thy

**composition_simplification_1**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ; p<sub>2</sub> = p<sub>1</sub> ∖<sub>p</sub> Pre p<sub>2</sub> ; p<sub>2</sub>

---
**composition_simplification_2**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ; p<sub>2</sub> = p<sub>1</sub> ; p<sub>2</sub> /<sub>p</sub> Pre p<sub>2</sub>

---
**composition_equiv**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> ≡<sub>p</sub> p<sub>1</sub> ⟹ f<sub>2</sub> ≡<sub>p</sub> p<sub>2</sub> ⟹ f<sub>1</sub> ; f<sub>2</sub> ≡<sub>p</sub> p<sub>1</sub> ; p<sub>2</sub>

---
**equality_is_maintained_by_composition**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> = p<sub>1</sub> ⟹ f<sub>2</sub> = p<sub>2</sub> ⟹ f<sub>1</sub> ; f<sub>2</sub> = p<sub>1</sub> ; p<sub>2</sub>

---
**compose_feasible_lemma**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p<sub>1</sub>, p<sub>2</sub>] ⟹ Domain ((post p<sub>1</sub>) ∖<sub>r</sub> (Pre p<sub>2</sub>)) = Domain ((post p<sub>1</sub>) ∖<sub>r</sub> (Pre p<sub>2</sub>) O post p<sub>2</sub>)

---
**compose_feasible2**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p<sub>1</sub>, p<sub>2</sub>] ⟹ is_feasible (p<sub>1</sub> ; p<sub>2</sub>)

---
**composition_removes_dead_code_1**

&nbsp;&nbsp;&nbsp;&nbsp;p /<sub>p</sub> (Pre p) ; q ≡<sub>p</sub> p ; q

---
**composition_removes_dead_code_2**

&nbsp;&nbsp;&nbsp;&nbsp;p ; q /<sub>p</sub> (Pre q) ≡<sub>p</sub> p ; q

---
**compose_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p<sub>2</sub> ⟹ is_feasible (p<sub>1</sub> ; p<sub>2</sub>)

---
&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ; p<sub>2</sub> ≡<sub>p</sub> 〈State ={}, Pre=Pre p<sub>1</sub> ∩ Domain (post p<sub>1</sub> ∖<sub>r</sub> Pre p<sub>2</sub>), post=post p<sub>1</sub>〉 ; p<sub>2</sub>

---
**range_decreases_composition**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p (y;x) ⊆ Range_p x

---
&nbsp;&nbsp;&nbsp;&nbsp;p ⊑<sub>p</sub> q ⟹ p;a ⊑<sub>p</sub> q;a

---
**composition_subsafety**

&nbsp;&nbsp;&nbsp;&nbsp;a ⊆<sub>p</sub> b ⟹ a;c ⊆<sub>p</sub> b;c

---
**composition_subsafety2**

&nbsp;&nbsp;&nbsp;&nbsp;a ⊆<sub>p</sub> b ⟹ c;a ⊆<sub>p</sub> c;b

---
**comp_range_p_prop**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p (q) ⊆ C ⟹ Range_p (p;q) ⊆ C

---
**comp_range_p_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;x ∉ Range_p q ⟹ x ∉ Range_p (p;q)

---
**connecting_element**

&nbsp;&nbsp;&nbsp;&nbsp;(x,y) ∈ post (a;b) ⟹ ∃z. (x,z) ∈ post a ∧ (z,y) ∈ post b ∧ z ∈ Pre b

---
**knowing_pre_composition**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ Pre (a) ⟹ (x, y) ∈ post (a; b) ⟹ x ∈ Pre (a ; b)

---
## Corestriction.thy

**corestrict_idem**

&nbsp;&nbsp;&nbsp;&nbsp;(p ∖<sub>p</sub> C) ∖<sub>p</sub> C = p ∖<sub>p</sub> C

---
**corestrict_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p (p ∖<sub>p</sub> D) ⊆ D

---
**corestrict_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p (p ∖<sub>p</sub> D) ⊆ Range_p p

---
**corestrict_prop_**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p (p ∖<sub>p</sub> D) ⊆ Range_p p ∩ D

---
**NOT_corestricted_p_refines_p**

&nbsp;&nbsp;&nbsp;&nbsp;p ∖<sub>p</sub> C ⊑<sub>p</sub> p

---
**NOT_p_refines_corestricted_p**

&nbsp;&nbsp;&nbsp;&nbsp;p ⊑<sub>p</sub> p ∖<sub>p</sub> C

---
**corestricted_refines_unrestricted_1**

&nbsp;&nbsp;&nbsp;&nbsp;p ∖<sub>p</sub> C ⊑<sub>p</sub> p

---
**unrestricted_refines_corestricted_1**

&nbsp;&nbsp;&nbsp;&nbsp;p ⊑<sub>p</sub> p ∖<sub>p</sub> C

---
**corestricted_refines_unrestricted_2**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ p ∖<sub>p</sub> C ⊑<sub>p</sub> p

---
**unrestricted_refines_corestricted_2**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ p ⊑<sub>p</sub> p ∖<sub>p</sub> C

---
**corestrict_subprog**

&nbsp;&nbsp;&nbsp;&nbsp;p ∖<sub>p</sub> C ⊆<sub>p</sub> p

---
**unrestricted_weakens_corestricted**

&nbsp;&nbsp;&nbsp;&nbsp;weakens p (p ∖<sub>p</sub> C)

---
**corestricted_strengthens_unrestricted**

&nbsp;&nbsp;&nbsp;&nbsp;strengthens (p ∖<sub>p</sub> C) p

---
**corestriction_prop**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ p ∖<sub>p</sub> D ⊑<sub>p</sub> p ∖<sub>p</sub> C

---
**corestriction_prop**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ p ∖<sub>p</sub> C ⊑<sub>p</sub> p ∖<sub>p</sub> D

---
**corestriction_weakens_prop**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ weakens (p ∖<sub>p</sub> C) (p ∖<sub>p</sub> D)

---
**corestriction_strengthens_prop**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ strengthens (p ∖<sub>p</sub> D) (p ∖<sub>p</sub> C)

---
**corestrict_subprogorder1**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ (p ∖<sub>p</sub> D) ⊆<sub>p</sub> (p ∖<sub>p</sub> C)

---
**equivalence_is_maintained_by_corestriction**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> ≡<sub>p</sub> p<sub>1</sub> ⟹ (f<sub>1</sub> ∖<sub>p</sub> C) ≡<sub>p</sub> p<sub>1</sub> ∖<sub>p</sub> C

---
**equality_is_maintained_by_corestriction**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> = p<sub>1</sub> ⟹ (f<sub>1</sub> ∖<sub>p</sub> C) = p<sub>1</sub> ∖<sub>p</sub> C

---
**corestrict_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ is_feasible (p ∖<sub>p</sub> C)

---
**corestriction_subsafety**

&nbsp;&nbsp;&nbsp;&nbsp;q ⊆<sub>p</sub> p ⟹ q ∖<sub>p</sub> C ⊆<sub>p</sub> p ∖<sub>p</sub> C

---
**refinement_safety_corestriction**

&nbsp;&nbsp;&nbsp;&nbsp;q ⊑<sub>p</sub> p ⟹ q ∖<sub>p</sub> C ⊑<sub>p</sub> p ∖<sub>p</sub> C

---
**implements_safety_corestriction**

&nbsp;&nbsp;&nbsp;&nbsp;implements a b ⟹ implements (a ∖<sub>p</sub> C) (b ∖<sub>p</sub> C)

---
**weakens_corestriction_1**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p, q] ⟹ q ⊑<sub>p</sub> p ⟹ weakens (q ∖<sub>p</sub> C) (p ∖<sub>p</sub> C)

---
**weakens_corestriction_2**

&nbsp;&nbsp;&nbsp;&nbsp;q ⊑<sub>p</sub> p ⟹ weakens (p ∖<sub>p</sub> C) (q ∖<sub>p</sub> C)

---
**strengthens_corestriction_1**

&nbsp;&nbsp;&nbsp;&nbsp;q ⊑<sub>p</sub> p ⟹ strengthens (p ∖<sub>p</sub> C) (q ∖<sub>p</sub> C)

---
**strengthens_corestriction_2**

&nbsp;&nbsp;&nbsp;&nbsp;q ⊑<sub>p</sub> p ⟹ strengthens (q ∖<sub>p</sub> C) (p ∖<sub>p</sub> C)

---
**corestrict_range_prop**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ C ⟹ x ∉ Range_p (p ∖<sub>p</sub> C) ⟹ x ∉ Range_p (p)

---
**corestrict_range_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible a ⟹ Range_p a ⊆ C ⟹ a ∖<sub>p</sub> C ≡<sub>p</sub> a

---
**corestrict_range_prop_3**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p(a) ∩ C = {} ⟹ a∖<sub>p</sub>C ≡<sub>p</sub> Fail {}

---
**corestrict_range_porp_4**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ p ∖<sub>p</sub> Range_p p ≡<sub>p</sub> p

---
**corestrict_inter**

&nbsp;&nbsp;&nbsp;&nbsp;(p ∖<sub>p</sub> C) ∖<sub>p</sub> D = p∖<sub>p</sub> (C ∩ D)

---
**corestrict_commute**

&nbsp;&nbsp;&nbsp;&nbsp;(p ∖<sub>p</sub> C) ∖<sub>p</sub> D = (p ∖<sub>p</sub> D) ∖<sub>p</sub> C

---
## Inverse.thy

**inverse_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ is_feasible (p<sup>-</sup><sup>1</sup>)

---
**inverse_of_inverse_is_self**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ p<sup>-</sup><sup>1</sup><sup>-</sup><sup>1</sup> ≡<sub>p</sub> p

---
**pre_of_inverse**

&nbsp;&nbsp;&nbsp;&nbsp;is_deterministic (p<sup>-</sup><sup>1</sup>) ⟹ Pre p = Pre (p ; (p<sup>-</sup><sup>1</sup>))

---
**pre_is_unchanged**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ Pre (p ; (p<sup>-</sup><sup>1</sup>)) = Pre p

---
**post_is_identity**

&nbsp;&nbsp;&nbsp;&nbsp;is_deterministic (p<sup>-</sup><sup>1</sup>) ⟹ (x,y)∈ restr_post (p ; (p<sup>-</sup><sup>1</sup>)) ⟹ x = y

---
**post_is_identity_2**

&nbsp;&nbsp;&nbsp;&nbsp;is_deterministic (p<sup>-</sup><sup>1</sup>) ⟹ (x,y)∈ restr_post (p ;<sub>p</sub> (p<sup>-</sup><sup>1</sup>)) ⟹ x = y

---
**post_of_inverse**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ is_deterministic (p<sup>-</sup><sup>1</sup>) ⟹ restr_post (Skip (Pre p)) = restr_post (p ; (p<sup>-</sup><sup>1</sup>))

---
**inverse_reverses_composition_1**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ is_deterministic (p<sup>-</sup><sup>1</sup>) ⟹ Skip (Pre p) ≡<sub>p</sub> (p ; (p<sup>-</sup><sup>1</sup>))

---
**inverse_reverses_composition_2**

&nbsp;&nbsp;&nbsp;&nbsp;Skip (S p) ⊑<sub>p</sub> (p ; (p<sup>-</sup><sup>1</sup>))

---
**equivalence_is_maintained_by_inverse**

&nbsp;&nbsp;&nbsp;&nbsp;f ≡<sub>p</sub> p ⟹ f<sup>-</sup><sup>1</sup> ≡<sub>p</sub> p<sup>-</sup><sup>1</sup>

---
**equality_is_maintained_by_inverse**

&nbsp;&nbsp;&nbsp;&nbsp;f = p ⟹ f<sup>-</sup><sup>1</sup> = p<sup>-</sup><sup>1</sup>

---
**refinement_safety_inverse**

&nbsp;&nbsp;&nbsp;&nbsp;S f = S g ⟹ all_feasible [f, g] ⟹ f ⊑<sub>p</sub> g ⟹ (g<sup>-</sup><sup>1</sup>) ⊑<sub>p</sub> (f<sup>-</sup><sup>1</sup>)

---
**inverse_makes_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible (p<sup>-</sup><sup>1</sup>)

---
## Operation_interactions.thy

**unsafe_compose_absorb**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>;<sub>p</sub>p<sub>2</sub>)/<sub>p</sub>C = p<sub>1</sub>/<sub>p</sub>C;<sub>p</sub>p<sub>2</sub>

---
**unsafe_compose_absorb_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>;<sub>p</sub>p<sub>2</sub>)/<sub>p</sub>C = p<sub>1</sub>/<sub>p</sub>C;<sub>p</sub>p<sub>2</sub>

---
**unsafe_compose_absorb_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>;<sub>p</sub>p<sub>2</sub>)/<sub>p</sub>C ≡<sub>p</sub> p<sub>1</sub>/<sub>p</sub>C;<sub>p</sub>p<sub>2</sub>

---
**range_p_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p(a) ∩ C = {} ⟹ a;<sub>p</sub>b/<sub>p</sub>(-C) ≡<sub>p</sub> a;<sub>p</sub>b

---
**compose_absorb_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>;p<sub>2</sub>)/<sub>p</sub>C = p<sub>1</sub>/<sub>p</sub>C;p<sub>2</sub>

---
**compose_absorb_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>;p<sub>2</sub>)/<sub>p</sub>C = p<sub>1</sub>/<sub>p</sub>C;p<sub>2</sub>

---
**compose_absorb_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>;p<sub>2</sub>)/<sub>p</sub>C ≡<sub>p</sub> p<sub>1</sub>/<sub>p</sub>C;p<sub>2</sub>

---
**range_p_composition**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p(a) ∩ C = {} ⟹ a;b/<sub>p</sub>(-C) ≡<sub>p</sub> a;b

---
**restrict_distrib_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>)/<sub>p</sub>C = (p<sub>1</sub>/<sub>p</sub>C ∪<sub>p</sub> p<sub>2</sub>/<sub>p</sub>C)

---
**restrict_distrib_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>)/<sub>p</sub>C = (p<sub>1</sub>/<sub>p</sub>C ∪<sub>p</sub> p<sub>2</sub>/<sub>p</sub>C)

---
**restrict_distrib_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>)/<sub>p</sub>C ≡<sub>p</sub> (p<sub>1</sub>/<sub>p</sub>C ∪<sub>p</sub> p<sub>2</sub>/<sub>p</sub>C)

---
**restrict_distrib_4**

&nbsp;&nbsp;&nbsp;&nbsp;a ∪<sub>p</sub> (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>)/<sub>p</sub>C = a ∪<sub>p</sub> (p<sub>1</sub>/<sub>p</sub>C ∪<sub>p</sub> p<sub>2</sub>/<sub>p</sub>C)

---
**restriction_absorbed_by_inverse_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sup>-</sup><sup>1</sup>)/<sub>p</sub>C = ((p∖<sub>p</sub>C)<sup>-</sup><sup>1</sup>)

---
**restriction_absorbed_by_inverse_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sup>-</sup><sup>1</sup>)/<sub>p</sub>C = (p∖<sub>p</sub>C)<sup>-</sup><sup>1</sup>

---
**restriction_absorbed_by_inverse_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sup>-</sup><sup>1</sup>)/<sub>p</sub>C ≡<sub>p</sub> (p∖<sub>p</sub>C)<sup>-</sup><sup>1</sup>

---
**compose_distrib1_1**

&nbsp;&nbsp;&nbsp;&nbsp;q;(p<sub>1</sub>∪<sub>p</sub>p<sub>2</sub>) = (q;p<sub>1</sub>) ∪<sub>p</sub> (q;p<sub>2</sub>)

---
**compose_distrib1_2**

&nbsp;&nbsp;&nbsp;&nbsp;q;(p<sub>1</sub>∪<sub>p</sub>p<sub>2</sub>) = (q;p<sub>1</sub>) ∪<sub>p</sub> (q;p<sub>2</sub>)

---
**compose_distrib1_3**

&nbsp;&nbsp;&nbsp;&nbsp;q;(p<sub>1</sub>∪<sub>p</sub>p<sub>2</sub>) ≡<sub>p</sub> (q;p<sub>1</sub>) ∪<sub>p</sub> (q;p<sub>2</sub>)

---
**compose_distrib2_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>∪<sub>p</sub>p<sub>2</sub>);q = (p<sub>1</sub>;q) ∪<sub>p</sub> (p<sub>2</sub>;q)

---
**compose_distrib2_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>∪<sub>p</sub>p<sub>2</sub>);q = (p<sub>1</sub>;q) ∪<sub>p</sub> (p<sub>2</sub>;q)

---
**compose_distrib2_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>∪<sub>p</sub>p<sub>2</sub>);q ≡<sub>p</sub> (p<sub>1</sub>;q) ∪<sub>p</sub> (p<sub>2</sub>;q)

---
**choice_distributes_over_composition**

&nbsp;&nbsp;&nbsp;&nbsp;q∪<sub>p</sub>(p<sub>1</sub>;p<sub>2</sub>) ≡<sub>p</sub> (q∪<sub>p</sub>p<sub>1</sub>) ; (q∪<sub>p</sub>p<sub>2</sub>)

---
**corestriction_on_composition**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ∖<sub>p</sub> s<sub>1</sub> ; p<sub>2</sub> = p<sub>1</sub> ; p<sub>2</sub> /<sub>p</sub> s<sub>1</sub>

---
**corestrict_compose**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> ; p<sub>2</sub>) ∖<sub>p</sub> C = p<sub>1</sub> ; (p<sub>2</sub> ∖<sub>p</sub> C)

---
**unsafe_gets_safe_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>;<sub>p</sub>p<sub>2</sub>);p<sub>3</sub> = (p<sub>1</sub>;p<sub>2</sub>);p<sub>3</sub>

---
**unsafe_gets_safe_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>;<sub>p</sub>p<sub>2</sub>);p<sub>3</sub> = (p<sub>1</sub>;p<sub>2</sub>);p<sub>3</sub>

---
**unsafe_gets_safe_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>;<sub>p</sub>p<sub>2</sub>);p<sub>3</sub> ≡<sub>p</sub> (p<sub>1</sub>;p<sub>2</sub>);p<sub>3</sub>

---
**unsafe_gets_safe_extended**

&nbsp;&nbsp;&nbsp;&nbsp;((p<sub>1</sub>;<sub>p</sub>p<sub>2</sub>);<sub>p</sub>p<sub>3</sub>);p<sub>4</sub> ≡<sub>p</sub> ((p<sub>1</sub>;p<sub>2</sub>);p<sub>3</sub>);p<sub>4</sub>

---
**equivalency_of_compositions_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>∖<sub>p</sub>Pre p<sub>2</sub>);<sub>p</sub>p<sub>2</sub> = p<sub>1</sub>;p<sub>2</sub>

---
**equivalency_of_compositions_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>∖<sub>p</sub>Pre p<sub>2</sub>);<sub>p</sub>p<sub>2</sub> = p<sub>1</sub>;p<sub>2</sub>

---
**equivalency_of_compositions_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>∖<sub>p</sub>Pre p<sub>2</sub>);<sub>p</sub>p<sub>2</sub> ≡<sub>p</sub> p<sub>1</sub>;p<sub>2</sub>

---
**composition_inverse_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p;q)<sup>-</sup><sup>1</sup> = (q<sup>-</sup><sup>1</sup>);(p<sup>-</sup><sup>1</sup>)

---
**composition_inverse_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p;q)<sup>-</sup><sup>1</sup> = (q<sup>-</sup><sup>1</sup>);(p<sup>-</sup><sup>1</sup>)

---
**composition_inverse_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p;q)<sup>-</sup><sup>1</sup> ≡<sub>p</sub> (q<sup>-</sup><sup>1</sup>);(p<sup>-</sup><sup>1</sup>)

---
**choice_inverse_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p ∪<sub>p</sub> q)<sup>-</sup><sup>1</sup> = (p<sup>-</sup><sup>1</sup>) ∪<sub>p</sub> (q<sup>-</sup><sup>1</sup>)

---
**choice_inverse_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p ∪<sub>p</sub> q)<sup>-</sup><sup>1</sup> = (p<sup>-</sup><sup>1</sup>) ∪<sub>p</sub> (q<sup>-</sup><sup>1</sup>)

---
**choice_inverse_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p ∪<sub>p</sub> q)<sup>-</sup><sup>1</sup> ≡<sub>p</sub> (p<sup>-</sup><sup>1</sup>) ∪<sub>p</sub> (q<sup>-</sup><sup>1</sup>)

---
**corestriction_restriction_on_unsafe_composition_1**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ∖<sub>p</sub> s<sub>1</sub> ;<sub>p</sub> p<sub>2</sub> ≡<sub>p</sub> p<sub>1</sub> ;<sub>p</sub> p<sub>2</sub> /<sub>p</sub> s<sub>1</sub>

---
**corestrict_gets_absorbed_by_unsafe_composition_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> ;<sub>p</sub> p<sub>2</sub>) ∖<sub>p</sub> C ≡<sub>p</sub> (p<sub>1</sub> ∖<sub>p</sub> C) ;<sub>p</sub> p<sub>2</sub>

---
**corestrict_gets_absorbed_by_unsafe_composition_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> ;<sub>p</sub> p<sub>2</sub>) ∖<sub>p</sub> C ≡<sub>p</sub> p<sub>1</sub> ;<sub>p</sub> (p<sub>2</sub> ∖<sub>p</sub> C)

---
**corestriction_on_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ∖<sub>p</sub> s ;<sub>p</sub> p<sub>2</sub> = p<sub>1</sub> ;<sub>p</sub> p<sub>2</sub> /<sub>p</sub> s

---
**corestrict_unsafe_compose**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p<sub>1</sub> ⟹ (p<sub>1</sub> ;<sub>p</sub> p<sub>2</sub>) ∖<sub>p</sub> C ≡<sub>p</sub> p<sub>1</sub> ;<sub>p</sub> (p<sub>2</sub> ∖<sub>p</sub> C)

---
**corestriction_absorbed_by_inverse_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sup>-</sup><sup>1</sup>)∖<sub>p</sub>C = ((p/<sub>p</sub>C)<sup>-</sup><sup>1</sup>)

---
**corestriction_absorbed_by_inverse_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sup>-</sup><sup>1</sup>)∖<sub>p</sub>C = ((p/<sub>p</sub>C)<sup>-</sup><sup>1</sup>)

---
**corestriction_absorbed_by_inverse_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sup>-</sup><sup>1</sup>)∖<sub>p</sub>C ≡<sub>p</sub> (p/<sub>p</sub>C)<sup>-</sup><sup>1</sup>

---
**unsafe_composition_inverse_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p;<sub>p</sub>q)<sup>-</sup><sup>1</sup> ≡<sub>p</sub> (q<sup>-</sup><sup>1</sup>);<sub>p</sub>(p<sup>-</sup><sup>1</sup>)

---
**corestrict_choice_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>) ∖<sub>p</sub> C = (p<sub>1</sub> ∖<sub>p</sub> C) ∪<sub>p</sub> (p<sub>2</sub> ∖<sub>p</sub> C)

---
**corestrict_choice_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>) ∖<sub>p</sub> C = (p<sub>1</sub> ∖<sub>p</sub> C) ∪<sub>p</sub> (p<sub>2</sub> ∖<sub>p</sub> C)

---
**corestrict_choice_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>) ∖<sub>p</sub> C ≡<sub>p</sub> (p<sub>1</sub> ∖<sub>p</sub> C) ∪<sub>p</sub> (p<sub>2</sub> ∖<sub>p</sub> C)

---
**unsafe_compose_distrib1_3_1**

&nbsp;&nbsp;&nbsp;&nbsp;q;<sub>p</sub>(p<sub>1</sub>∪<sub>p</sub>p<sub>2</sub>) = (q;<sub>p</sub>p<sub>1</sub>) ∪<sub>p</sub> (q;<sub>p</sub>p<sub>2</sub>)

---
**unsafe_compose_distrib1_3_2**

&nbsp;&nbsp;&nbsp;&nbsp;q;<sub>p</sub>(p<sub>1</sub>∪<sub>p</sub>p<sub>2</sub>) = (q;<sub>p</sub>p<sub>1</sub>) ∪<sub>p</sub> (q;<sub>p</sub>p<sub>2</sub>)

---
**unsafe_compose_distrib1_3_3**

&nbsp;&nbsp;&nbsp;&nbsp;q;<sub>p</sub>(p<sub>1</sub>∪<sub>p</sub>p<sub>2</sub>) ≡<sub>p</sub> (q;<sub>p</sub>p<sub>1</sub>) ∪<sub>p</sub> (q;<sub>p</sub>p<sub>2</sub>)

---
**unsafe_compose_distrib2_1**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>∪<sub>p</sub>p<sub>2</sub>);<sub>p</sub>q = (p<sub>1</sub>;<sub>p</sub>q) ∪<sub>p</sub> (p<sub>2</sub>;<sub>p</sub>q)

---
**unsafe_compose_distrib2_2**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>∪<sub>p</sub>p<sub>2</sub>);<sub>p</sub>q = (p<sub>1</sub>;<sub>p</sub>q) ∪<sub>p</sub> (p<sub>2</sub>;<sub>p</sub>q)

---
**unsafe_compose_distrib2_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub>∪<sub>p</sub>p<sub>2</sub>);<sub>p</sub>q ≡<sub>p</sub> (p<sub>1</sub>;<sub>p</sub>q) ∪<sub>p</sub> (p<sub>2</sub>;<sub>p</sub>q)

---
**choice_distributes_over_composition_4**

&nbsp;&nbsp;&nbsp;&nbsp;q∪<sub>p</sub>(p<sub>1</sub>;<sub>p</sub>p<sub>2</sub>) ≡<sub>p</sub> (q∪<sub>p</sub>p<sub>1</sub>) ;<sub>p</sub> (q∪<sub>p</sub>p<sub>2</sub>)

---
**until_simplification_1**

&nbsp;&nbsp;&nbsp;&nbsp;a;n∖<sub>p</sub>C ∪<sub>p</sub> a;m∖<sub>p</sub>C ≡<sub>p</sub> a;(n ∪<sub>p</sub> m)∖<sub>p</sub>C

---
**until_simplification_2**

&nbsp;&nbsp;&nbsp;&nbsp;a;<sub>p</sub>n∖<sub>p</sub>C ∪<sub>p</sub> a;<sub>p</sub>m∖<sub>p</sub>C ≡<sub>p</sub> a;<sub>p</sub>(n ∪<sub>p</sub> m)∖<sub>p</sub>C

---
## Prime.thy

**finite_Field_implies_finite_relation**

&nbsp;&nbsp;&nbsp;&nbsp;finite (Field r)  ⟹ finite r

---
&nbsp;&nbsp;&nbsp;&nbsp;finite (S p) ⟹ finite (Pre p)

---
**finite_S_implies_finite_post**

&nbsp;&nbsp;&nbsp;&nbsp;finite (S p)  ⟹ finite (post p)

---
**post_cardinality_equals_P_cardinality**

&nbsp;&nbsp;&nbsp;&nbsp;P = {〈State={a,b}, Pre={a}, post={(a,b)}〉 | a b. (a,b) ∈ (post p)}  ⟹ card (post p) = card P

---
**same_card_and_finite_impl_finite**

&nbsp;&nbsp;&nbsp;&nbsp;card a = card b  ⟹ finite a  ⟹ card a > 0  ⟹ finite b

---
**fst_in_state**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ is_minimal p ⟹ P = {〈State={a,b}, Pre={a}, post={(a,b)}〉 | a b. (a,b) ∈ post p} ⟹ r ∈ post p ⟹ fst r ∈ State p

---
**snd_is_state**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ is_minimal p ⟹ P = {〈State={a,b}, Pre={a}, post={(a,b)}〉 | a b. (a,b) ∈ post p} ⟹ r ∈ post p ⟹ snd r ∈ State p

---
&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ is_minimal p ⟹ P = {〈State={a,b}, Pre={a}, post={(a,b)}〉 | a b. (a,b) ∈ post p} ⟹ s ∈ State p ⟹ ∃r ∈ post p. fst r = s ∨ snd r = s

---
**choice_set_decomp_1**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ ⋃<sub>P</sub> (insert x F) = ⋃<sub>P</sub> F ∪<sub>p</sub> x

---
**choice_set_decomp_1**

&nbsp;&nbsp;&nbsp;&nbsp;⋃<sub>P</sub> (insert x F) = ⋃<sub>P</sub> F ∪<sub>p</sub> x

---
**choice_set_equality**

&nbsp;&nbsp;&nbsp;&nbsp;finite (S p) ⟹ is_feasible p ⟹ is_minimal p ⟹ P = {〈State={a,b}, Pre={a}, post={(a,b)}〉 | a b. (a,b) ∈ post p} ⟹ p<sub>i</sub> ∈ P ⟹ ⋃<sub>P</sub> P = p

---
&nbsp;&nbsp;&nbsp;&nbsp;finite (S p) ⟹ is_feasible p ⟹ is_minimal p ⟹ P = {〈State={a,b},Pre={a},post={(a,b)}〉 |a b . (a,b) ∈ (post p)} ⟹ p<sub>i</sub> ∈ P ⟹ is_prime p<sub>i</sub> ∧ p<sub>i</sub> ⊆<sub>p</sub> p ∧ ⋃<sub>P</sub> P = p

---
&nbsp;&nbsp;&nbsp;&nbsp;finite (S p) ⟹ is_feasible p ⟹ is_minimal p ⟹ ∃ P. p<sub>i</sub> ∈ P → is_prime p<sub>i</sub> ∧ p<sub>i</sub> ⊆<sub>p</sub> p ∧ ⋃<sub>P</sub> P = p

---
## Restriction.thy

**restrict_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (p /<sub>p</sub> D) ⊆ D

---
**restrict_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (p /<sub>p</sub> D) ⊆ Pre p

---
**restrict_prop**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (p /<sub>p</sub> D) ⊆ Pre p ∩ D

---
**restrict_idem**

&nbsp;&nbsp;&nbsp;&nbsp;(p /<sub>p</sub> C) /<sub>p</sub> C = p /<sub>p</sub> C

---
**restrict_inter**

&nbsp;&nbsp;&nbsp;&nbsp;(p/<sub>p</sub>C<sub>1</sub>)/<sub>p</sub>C<sub>2</sub> = p/<sub>p</sub>(C<sub>1</sub> ∩ C<sub>2</sub>)

---
**restriction_equiv**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> ≡<sub>p</sub> p<sub>1</sub> ⟹ (f<sub>1</sub> /<sub>p</sub> C) ≡<sub>p</sub> p<sub>1</sub> /<sub>p</sub> C

---
**equality_is_maintained_by_restriction**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> = p<sub>1</sub> ⟹ (f<sub>1</sub> /<sub>p</sub> C) = p<sub>1</sub> /<sub>p</sub> C

---
**restrict_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ is_feasible (p /<sub>p</sub> C)

---
**restrict_might_make_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ Domain (post p) ⟹ is_feasible (p /<sub>p</sub> C)

---
**restrict_refine_1**

&nbsp;&nbsp;&nbsp;&nbsp;strengthens p  (p /<sub>p</sub> C)

---
**restrict_refine_2**

&nbsp;&nbsp;&nbsp;&nbsp;strengthens (p /<sub>p</sub> C) p

---
**restrict_refine_3**

&nbsp;&nbsp;&nbsp;&nbsp;strengthens p  q ⟹ strengthens (p /<sub>p</sub> C) (q /<sub>p</sub> C)

---
**restrict_refine_4**

&nbsp;&nbsp;&nbsp;&nbsp;weakens p  (p /<sub>p</sub> C)

---
**restrict_refine_5**

&nbsp;&nbsp;&nbsp;&nbsp;weakens p  q ⟹ weakens (p /<sub>p</sub> C) (q /<sub>p</sub> C)

---
**restrict_refine**

&nbsp;&nbsp;&nbsp;&nbsp;p ⊑<sub>p</sub> p /<sub>p</sub> C

---
**restrict_refineorder1**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ p /<sub>p</sub> C ⊑<sub>p</sub> p /<sub>p</sub> D

---
**restriction_refsafety**

&nbsp;&nbsp;&nbsp;&nbsp;q ⊑<sub>p</sub> p ⟹ q /<sub>p</sub> C ⊑<sub>p</sub> p /<sub>p</sub> C

---
**restriction_subsafety**

&nbsp;&nbsp;&nbsp;&nbsp;q ⊆<sub>p</sub> p ⟹ q /<sub>p</sub> C ⊆<sub>p</sub> p /<sub>p</sub> C

---
**restriction_refsafety2**

&nbsp;&nbsp;&nbsp;&nbsp;q ⊑<sub>p</sub> p ⟹ D ⊆ C ⟹ q /<sub>p</sub> C ⊑<sub>p</sub> p /<sub>p</sub> D

---
**implements_safety_restriction**

&nbsp;&nbsp;&nbsp;&nbsp;implements a b ⟹ implements (a /<sub>p</sub> C) (b /<sub>p</sub> C)

---
**restrict_subprogorder1**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ p /<sub>p</sub> D ⊆<sub>p</sub> p /<sub>p</sub> C

---
**restrict_subprog**

&nbsp;&nbsp;&nbsp;&nbsp;p /<sub>p</sub> C ⊆<sub>p</sub> p

---
## Unsafe_composition.thy

**equivalence_is_maintained_by_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> ≡<sub>p</sub> p<sub>1</sub> ⟹ f<sub>2</sub> ≡<sub>p</sub> p<sub>2</sub> ⟹ f<sub>1</sub> ;<sub>p</sub> f<sub>2</sub> ≡<sub>p</sub> p<sub>1</sub> ;<sub>p</sub> p<sub>2</sub>

---
**equality_is_maintained_by_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> = p<sub>1</sub> ⟹ f<sub>2</sub> = p<sub>2</sub> ⟹ f<sub>1</sub> ;<sub>p</sub> f<sub>2</sub> = p<sub>1</sub> ;<sub>p</sub> p<sub>2</sub>

---
**unsafe_compose_feasible_1**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible (p<sub>1</sub> ;<sub>p</sub> p<sub>2</sub>) ⟹ is_feasible p<sub>1</sub>

---
**unsafe_compose_feasible_2**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p<sub>1</sub>, p<sub>2</sub>] ⟹ Range_p p<sub>1</sub> ⊆ Pre p<sub>2</sub> ⟹ is_feasible (p<sub>1</sub> ;<sub>p</sub> p<sub>2</sub>)

---
## Unsafe_composition2.thy

&nbsp;&nbsp;&nbsp;&nbsp;Pre (p<sub>1</sub> ;<sup>p</sup> (p<sub>2</sub> ;<sup>p</sup> p<sub>3</sub>)) ⊆ Pre ((p<sub>1</sub> ;<sup>p</sup> p<sub>2</sub>) ;<sup>p</sup> p<sub>3</sub>)

---
&nbsp;&nbsp;&nbsp;&nbsp;Pre ((p ;<sup>p</sup> q) ;<sup>p</sup> r) = Pre (p ;<sup>p</sup> (q ;<sup>p</sup> r))

---
**equivalence_is_maintained_by_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> ≡<sub>p</sub> p<sub>1</sub> ⟹ f<sub>2</sub> ≡<sub>p</sub> p<sub>2</sub> ⟹ f<sub>1</sub> ;<sup>p</sup> f<sub>2</sub> ≡<sub>p</sub> p<sub>1</sub> ;<sup>p</sup> p<sub>2</sub>

---
**unsafe_compose_feasible_1**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible (p<sub>1</sub> ;<sup>p</sup> p<sub>2</sub>) ⟹ is_feasible p<sub>1</sub>

---
**unsafe_compose_feasible_2**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p<sub>1</sub>, p<sub>2</sub>] ⟹ Range_p p<sub>1</sub> ⊆ Pre p<sub>2</sub> ⟹ is_feasible (p<sub>1</sub> ;<sup>p</sup> p<sub>2</sub>)

---
## Unsafe_composition3.thy

**equivalence_is_maintained_by_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> ≡<sub>p</sub> p<sub>1</sub> ⟹ f<sub>2</sub> ≡<sub>p</sub> p<sub>2</sub> ⟹ f<sub>1</sub> ;<sub>P</sub> f<sub>2</sub> ≡<sub>p</sub> p<sub>1</sub> ;<sub>P</sub> p<sub>2</sub>

---
**equality_is_maintained_by_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;f<sub>1</sub> = p<sub>1</sub> ⟹ f<sub>2</sub> = p<sub>2</sub> ⟹ f<sub>1</sub> ;<sub>P</sub> f<sub>2</sub> = p<sub>1</sub> ;<sub>P</sub> p<sub>2</sub>

---
**unsafe_compose_feasible_1**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible (p<sub>1</sub> ;<sub>P</sub> p<sub>2</sub>) ⟹ is_feasible p<sub>1</sub>

---
**unsafe_compose_feasible_2**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p<sub>1</sub>, p<sub>2</sub>] ⟹ Range_p p<sub>1</sub> ⊆ Pre p<sub>2</sub> ⟹ is_feasible (p<sub>1</sub> ;<sub>P</sub> p<sub>2</sub>)

---
## Boolean.thy

**restrict_true**

&nbsp;&nbsp;&nbsp;&nbsp;p /<sub>p</sub> (TRUE (S p)) = p

---
**restrict_false**

&nbsp;&nbsp;&nbsp;&nbsp;p /<sub>p</sub> (FALSE) ≡<sub>p</sub> Fail (S p)

---
**cond_false_1**

&nbsp;&nbsp;&nbsp;&nbsp;p /<sub>p</sub> FALSE ≡<sub>p</sub> Fail (S p)

---
**corestrict_true**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ p ∖<sub>p</sub> (TRUE (S p)) ≡<sub>p</sub> p

---
**corestrict_false**

&nbsp;&nbsp;&nbsp;&nbsp;p ∖<sub>p</sub> FALSE = Fail (S p)

---
**corestrict_false**

&nbsp;&nbsp;&nbsp;&nbsp;p ∖<sub>p</sub> FALSE ≡<sub>p</sub> Infeas (Pre p)

---
**if_true**

&nbsp;&nbsp;&nbsp;&nbsp;ITE (TRUE (S p<sub>1</sub> ∪ S p<sub>2</sub>)) p<sub>1</sub> p<sub>2</sub> ≡<sub>p</sub> p<sub>1</sub>

---
**if_false1**

&nbsp;&nbsp;&nbsp;&nbsp;ITE (FALSE) p<sub>1</sub> p<sub>2</sub> ≡<sub>p</sub> p<sub>2</sub>

---
**true_selects_first_program_2**

&nbsp;&nbsp;&nbsp;&nbsp;GC [(TRUE (S p<sub>1</sub> ∪ S p<sub>2</sub>), p<sub>1</sub>), (FALSE, p<sub>2</sub>)] ≡<sub>p</sub> p<sub>1</sub>

---
**false_selects_second_program_2**

&nbsp;&nbsp;&nbsp;&nbsp;GC [(FALSE, p<sub>1</sub>), ((TRUE (S p<sub>1</sub> ∪ S p<sub>2</sub>)), p<sub>2</sub>)] ≡<sub>p</sub> p<sub>2</sub>

---
**restrict_false2**

&nbsp;&nbsp;&nbsp;&nbsp;S p ⊆ S q ⟹ p /<sub>p</sub> FALSE ∪<sub>p</sub> q = Fail {} ∪<sub>p</sub> q

---
**implies_prop**

&nbsp;&nbsp;&nbsp;&nbsp;(C →<sub>s</sub> D) = UNIV ≡ (C ⊆ D)

---
**and_prop**

&nbsp;&nbsp;&nbsp;&nbsp;A ⊆ X ⟹ B ⊆ X ⟹ A ∧<sub>s</sub> B = TRUE X ≡ A = X ∧ B = X

---
**or_prop**

&nbsp;&nbsp;&nbsp;&nbsp;TRUE X ⊆ (A ∨<sub>s</sub> B) ≡ ∀x∈X. x ∈ A ∨ x ∈ B

---
## Fail.thy

**fail_is_valid**

&nbsp;&nbsp;&nbsp;&nbsp;is_valid (Fail s)

---
**fail_is_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible (Fail s)

---
**fail_is_total**

&nbsp;&nbsp;&nbsp;&nbsp;is_total (Fail s)

---
**fail_is_idempondent_composition**

&nbsp;&nbsp;&nbsp;&nbsp;Fail C ; Fail C = Fail C

---
**fail_is_idempondent_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;Fail C ;<sub>p</sub> Fail C = Fail C

---
**fail_equiv**

&nbsp;&nbsp;&nbsp;&nbsp;Fail C ≡<sub>p</sub> Fail D

---
**no_pre_is_fail**

&nbsp;&nbsp;&nbsp;&nbsp;Pre p = {} ⟹ Fail s ≡<sub>p</sub> p

---
**NOT_fail_choice_r**

&nbsp;&nbsp;&nbsp;&nbsp;p ∪<sub>p</sub> Fail (S p) = p

---
**fail_choice_r**

&nbsp;&nbsp;&nbsp;&nbsp;p ∪<sub>p</sub> Fail C ≡<sub>p</sub> p

---
**NOT_fail_choice_l**

&nbsp;&nbsp;&nbsp;&nbsp;Fail (S p) ∪<sub>p</sub> p = p

---
**fail_choice_l**

&nbsp;&nbsp;&nbsp;&nbsp;Fail C ∪<sub>p</sub> p ≡<sub>p</sub> p

---
**fail_compose_l_2**

&nbsp;&nbsp;&nbsp;&nbsp;Fail (S p) ; p = Fail (S p)

---
**fail_compose_l**

&nbsp;&nbsp;&nbsp;&nbsp;Fail C ; p = Fail (C ∪ S p)

---
**fail_compose_r_2**

&nbsp;&nbsp;&nbsp;&nbsp;p ; Fail C = Fail (C ∪ S p)

---
**fail_compose_r**

&nbsp;&nbsp;&nbsp;&nbsp;p ; Fail C ≡<sub>p</sub> Fail C

---
**only_fail_refines_fail**

&nbsp;&nbsp;&nbsp;&nbsp;(p ⊑<sub>p</sub> Fail (S p)) = (p ≡<sub>p</sub> Fail (S p))

---
**refine_fail**

&nbsp;&nbsp;&nbsp;&nbsp;p ⊑<sub>p</sub> Fail (S p)

---
**fail_refine_self**

&nbsp;&nbsp;&nbsp;&nbsp;(Fail (S p) ⊑<sub>p</sub> p) = (p ≡<sub>p</sub> Fail (S p))

---
**fail_specialize_self**

&nbsp;&nbsp;&nbsp;&nbsp;(p ⊆<sub>p</sub> Fail (S p)) = (p ≡<sub>p</sub> Fail (S p))

---
**range_of_fail**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p (Fail C) = {}

---
**choice_fail_implication**

&nbsp;&nbsp;&nbsp;&nbsp;(a ∪<sub>p</sub> b ≡<sub>p</sub> Fail {}) = (a ≡<sub>p</sub> Fail {} ∧ b ≡<sub>p</sub> Fail {})

---
**fail_refine**

&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ S p ⟹ p ⊑<sub>p</sub> Fail C

---
&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ S p ⟹ Fail C ⊆<sub>p</sub> p

---
**fail_specialize2**

&nbsp;&nbsp;&nbsp;&nbsp;p ⊆<sub>p</sub> Fail (S p) ≡ p ≡<sub>p</sub> Fail {}

---
**fail_refine2**

&nbsp;&nbsp;&nbsp;&nbsp;Fail (S p) ⊑<sub>p</sub> p ≡ p ≡<sub>p</sub> Fail {}

---
**compose_empty_1**

&nbsp;&nbsp;&nbsp;&nbsp;S a = {} ⟹ b ; a = Fail (S b)

---
**compose_empty_2**

&nbsp;&nbsp;&nbsp;&nbsp;S a = {} ⟹ a; b = Fail (S b)

---
**fail_union_1**

&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ S p ⟹ Fail C ∪<sub>p</sub> (p ∪<sub>p</sub> q) = (p ∪<sub>p</sub> q)

---
**fail_compose**

&nbsp;&nbsp;&nbsp;&nbsp;Fail (S p);p = Fail (S p)

---
**fail_union_2**

&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ S a ⟹ a ∪<sub>p</sub> Fail C = a ∪<sub>p</sub> Fail {}

---
**fail_choice_decomp**

&nbsp;&nbsp;&nbsp;&nbsp;p ∪<sub>p</sub> q ≡<sub>p</sub> Fail {} ≡ p ≡<sub>p</sub> Fail {} ∧ q ≡<sub>p</sub> Fail {}

---
**fail_specialize**

&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ S p ⟹ Fail C ⊆<sub>p</sub> p

---
**fail_specialize3**

&nbsp;&nbsp;&nbsp;&nbsp;Fail {} ⊆<sub>p</sub> p

---
## Havoc.thy

**havoc_is_valid**

&nbsp;&nbsp;&nbsp;&nbsp;is_valid (Havoc s)

---
**havoc_is_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible (Havoc s)

---
**havoc_is_total**

&nbsp;&nbsp;&nbsp;&nbsp;is_total (Havoc s)

---
**havoc_is_idempondent_composition**

&nbsp;&nbsp;&nbsp;&nbsp;Havoc C ; Havoc C = Havoc C

---
**havoc_is_idempondent_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;Havoc C ;<sub>p</sub> Havoc C = Havoc C

---
**havoc_choice_l**

&nbsp;&nbsp;&nbsp;&nbsp;S p ⊆ C ⟹ Havoc C ∪<sub>p</sub> p = Havoc C

---
**havoc_choice_r**

&nbsp;&nbsp;&nbsp;&nbsp;S p ⊆ C ⟹ p ∪<sub>p</sub> Havoc C = Havoc C

---
**havoc_pre_State**

&nbsp;&nbsp;&nbsp;&nbsp;State (p ; Havoc (S p)) = State (Havoc (S p) /<sub>p</sub> Pre p)

---
**havoc_pre_S**

&nbsp;&nbsp;&nbsp;&nbsp;S p ⊆ C ⟹ S (p ; Havoc C) = S (Havoc C /<sub>p</sub> Pre p)

---
**NOT_havoc_pre_Pre**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (p ; Havoc (S p)) = Pre (Havoc (S p) /<sub>p</sub> Pre p)

---
**havoc_pre_Pre**

&nbsp;&nbsp;&nbsp;&nbsp;S p ⊆ C ⟹is_feasible p ⟹ Pre (p ; Havoc C) = Pre (Havoc C /<sub>p</sub> Pre p)

---
**NOT_havoc_pre_post_1**

&nbsp;&nbsp;&nbsp;&nbsp;post (p ; Havoc (S p)) = post (Havoc (S p) /<sub>p</sub> Pre p)

---
**NOT_havoc_pre_post_1**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ post (p ; Havoc (S p)) = post (Havoc (S p) /<sub>p</sub> Pre p)

---
**havoc_pre_post**

&nbsp;&nbsp;&nbsp;&nbsp;S p ⊆ C ⟹is_feasible p ⟹ restr_post (p ; Havoc C)/<sub>r</sub> Pre p = restr_post (Havoc C /<sub>p</sub> Pre p)

---
**NOT_havoc_pre**

&nbsp;&nbsp;&nbsp;&nbsp;p ; Havoc (S p) ≡<sub>p</sub> Havoc (S p) /<sub>p</sub> Pre p

---
**havoc_pre**

&nbsp;&nbsp;&nbsp;&nbsp;S p ⊆ C ⟹is_feasible p ⟹ (p ; Havoc C) ≡<sub>p</sub> Havoc C /<sub>p</sub> Pre p

---
**havoc_pre_unsafe**

&nbsp;&nbsp;&nbsp;&nbsp;S p ⊆ C ⟹ (p ;<sub>p</sub> Havoc C) ≡<sub>p</sub> Havoc C /<sub>p</sub> Pre p

---
**havoc_co_restricted**

&nbsp;&nbsp;&nbsp;&nbsp;(Havoc C /<sub>p</sub> D) ∖<sub>p</sub> D ≡<sub>p</sub> Havoc (C ∩ D)

---
**havoc_from_left_S**

&nbsp;&nbsp;&nbsp;&nbsp;S p ⊆ C ⟹ is_feasible p ⟹ S (Havoc C ; p) = S(Havoc C ∖<sub>p</sub> Range_p (p))

---
**havoc_from_left_Pre**

&nbsp;&nbsp;&nbsp;&nbsp;S p ⊆ C ⟹ is_feasible p ⟹ ¬p ≡<sub>p</sub> Fail C ⟹ Pre (Havoc C ; p) = C

---
**havoc_from_left_post**

&nbsp;&nbsp;&nbsp;&nbsp;S p ⊆ C ⟹ is_feasible p ⟹ post (Havoc C ; p) = post (Havoc C ∖<sub>p</sub> Range_p (p))

---
**havoc_from_left**

&nbsp;&nbsp;&nbsp;&nbsp;S p ⊆ C ⟹ is_feasible p ⟹ ¬p ≡<sub>p</sub> Fail C ⟹ Havoc C ; p ≡<sub>p</sub> Havoc C ∖<sub>p</sub> Range_p p

---
**refine_havoc**

&nbsp;&nbsp;&nbsp;&nbsp;p ⊑<sub>p</sub> Havoc (S p) /<sub>p</sub> Pre p

---
**specialize_havoc**

&nbsp;&nbsp;&nbsp;&nbsp;p ⊆<sub>p</sub> Havoc (S p) /<sub>p</sub> Pre p

---
**refine_havoc2**

&nbsp;&nbsp;&nbsp;&nbsp;is_total p ⟹ p ⊑<sub>p</sub> Havoc (S p)

---
**specialize_havoc2**

&nbsp;&nbsp;&nbsp;&nbsp;S p ⊆ C ⟹ p ⊆<sub>p</sub> Havoc (C)

---
## Infeas.thy

**infeas_is_valid**

&nbsp;&nbsp;&nbsp;&nbsp;is_valid (Infeas s)

---
**infeas_is_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible (Infeas s)

---
**infeas_is_total**

&nbsp;&nbsp;&nbsp;&nbsp;is_total (Infeas s)

---
**infeas_is_idempondent_composition**

&nbsp;&nbsp;&nbsp;&nbsp;Infeas C ; Infeas C = Infeas C

---
**infeas_is_idempondent_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;Infeas C ;<sub>p</sub> Infeas C = Infeas C

---
**fail_equiv**

&nbsp;&nbsp;&nbsp;&nbsp;Infeas C ≡<sub>p</sub> Infeas D

---
**not_total_infeas_makes_infeasible**

&nbsp;&nbsp;&nbsp;&nbsp;¬is_total p ⟹ ¬is_feasible (p ∪<sub>p</sub> Infeas (S p))

---
**infeas_makes_total**

&nbsp;&nbsp;&nbsp;&nbsp;is_total (p ∪<sub>p</sub> Infeas (S p))

---
**infeas_to_smaller_self**

&nbsp;&nbsp;&nbsp;&nbsp;p ; Infeas (S p) ≡<sub>p</sub> Infeas (Pre p ∩ Domain (post p))

---
**infeas_composition**

&nbsp;&nbsp;&nbsp;&nbsp;Infeas (S p) ; p = Fail (S p)

---
**infeas_unsafe_composition_1**

&nbsp;&nbsp;&nbsp;&nbsp;Infeas (S p) ;<sub>p</sub> p = Infeas (S p)

---
**infeas_unsafe_composition_2**

&nbsp;&nbsp;&nbsp;&nbsp;p ;<sub>p</sub> Infeas (S p) ≡<sub>p</sub> Infeas (Pre p)

---
**infeas_restriction**

&nbsp;&nbsp;&nbsp;&nbsp;Infeas (C) /<sub>p</sub> D ≡<sub>p</sub> Infeas (C ∩ D)

---
**infeas_corestriction**

&nbsp;&nbsp;&nbsp;&nbsp;Infeas (C) ∖<sub>p</sub> D = Fail (C)

---
**infeas_corestriction2**

&nbsp;&nbsp;&nbsp;&nbsp;Infeas (C) ∖<sub>p</sub> D = Infeas (C)

---
## Skip.thy

**skip_is_valid**

&nbsp;&nbsp;&nbsp;&nbsp;is_valid (Skip s)

---
**skip_is_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible (Skip s)

---
**skip_is_total**

&nbsp;&nbsp;&nbsp;&nbsp;is_total (Skip s)

---
**skip_is_idempondent_composition**

&nbsp;&nbsp;&nbsp;&nbsp;Skip C ; Skip C = Skip C

---
**skip_is_idempondent_unsafe_composition**

&nbsp;&nbsp;&nbsp;&nbsp;Skip C ;<sub>p</sub> Skip C = Skip C

---
**skip_unsafe_compose_r_1**

&nbsp;&nbsp;&nbsp;&nbsp;p ;<sub>p</sub> Skip (S p) = p

---
**skip_compose_r_post**

&nbsp;&nbsp;&nbsp;&nbsp;post (p ; Skip (S p)) = post p

---
**skip_compose_r_Pre_1**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (p ; Skip (S p)) = (Pre p ∩ Domain (post p))

---
**skip_compose_r_S**

&nbsp;&nbsp;&nbsp;&nbsp;S (p ; Skip (S p)) = S p

---
**Skip_compleft**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ p ; Skip (S p) = p

---
&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ Skip (S p) ; p = p

---
**skip_compose2**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ p ; Skip (S p) ≡<sub>p</sub> p

---
**skip_compose_r_range2**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ p ; Skip (Range (post p)) =  p

---
**skip_compose_r_range**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ p ; Skip (Range_p p) ≡<sub>p</sub>  p

---
**skip_compose4**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ Skip (Pre p) ; p ≡<sub>p</sub>  p

---
**skip_compose_r_3**

&nbsp;&nbsp;&nbsp;&nbsp;p ; Skip (S p) ≡<sub>p</sub> p /<sub>p</sub> Domain (post p)

---
**skip_makes_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible (p ; Skip (S p))

---
**skip_compose_l_S**

&nbsp;&nbsp;&nbsp;&nbsp;S (Skip (S p) ; p) = S p

---
**skip_compose_l_Pre**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (Skip (S p) ; p) = Pre p

---
**skip_compose_l_post**

&nbsp;&nbsp;&nbsp;&nbsp;post (Skip (S p) ; p) = post p /<sub>r</sub> Pre p

---
**skip_compose_l_1**

&nbsp;&nbsp;&nbsp;&nbsp;Skip (S p) ; p = 〈 State = S p, Pre = Pre p, post = post p /<sub>r</sub> Pre p〉

---
**skip_compose3**

&nbsp;&nbsp;&nbsp;&nbsp;Skip (S p) ; p ≡<sub>p</sub> p

---
**skip_unsafe_compose_r_2**

&nbsp;&nbsp;&nbsp;&nbsp;Skip (S p) ;<sub>p</sub> p = 〈State=S p, Pre=S p, post = restr_post p 〉

---
**corestriction_prop**

&nbsp;&nbsp;&nbsp;&nbsp;p ∖<sub>p</sub> C ≡<sub>p</sub> p ; (Skip (S p) /<sub>p</sub> C)

---
**skip_prop**

&nbsp;&nbsp;&nbsp;&nbsp;Skip C ∪<sub>p</sub> Skip D ≡<sub>p</sub> Skip (C ∪ D)

---
**skip_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;Skip (S p) /<sub>p</sub> C ; p ≡<sub>p</sub> p /<sub>p</sub> C

---
&nbsp;&nbsp;&nbsp;&nbsp;Skip (C) ; p = p /<sub>p</sub> C

---
**Skip_comprestrict**

&nbsp;&nbsp;&nbsp;&nbsp;Skip (C) ; p ≡<sub>p</sub> p /<sub>p</sub> C

---
**skip_prop_4**

&nbsp;&nbsp;&nbsp;&nbsp;Skip D /<sub>p</sub> C ≡<sub>p</sub> Skip (D ∩ C)

---
**skip_prop_5**

&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ D ⟹ Skip D /<sub>p</sub> C ≡<sub>p</sub> Skip C

---
**skip_prop_6**

&nbsp;&nbsp;&nbsp;&nbsp;S p ⊆ C ⟹ Skip C ; p ≡<sub>p</sub> p

---
**corestrict_skip**

&nbsp;&nbsp;&nbsp;&nbsp;p ; Skip (C) ≡<sub>p</sub> p ∖<sub>p</sub> C

---
**skip_prop_8**

&nbsp;&nbsp;&nbsp;&nbsp;Skip D ∖<sub>p</sub> C ≡<sub>p</sub> Skip (D ∩ C)

---
**skip_prop_9**

&nbsp;&nbsp;&nbsp;&nbsp;S (Skip (C)) = C

---
**skip_prop_10**

&nbsp;&nbsp;&nbsp;&nbsp;Skip x ∪<sub>p</sub> Skip y = Skip (x ∪ y)

---
**skip_prop_11**

&nbsp;&nbsp;&nbsp;&nbsp;Skip {} ∪<sub>p</sub> p ≡<sub>p</sub> p

---
**skip_prop_12**

&nbsp;&nbsp;&nbsp;&nbsp;Skip {} ∪<sub>p</sub> (p ∪<sub>p</sub> q) = p ∪<sub>p</sub> q

---
**skip_prop_13**

&nbsp;&nbsp;&nbsp;&nbsp;(a ; Skip (S a ∪ S b) ); b = a ; b

---
**skip_prop_14**

&nbsp;&nbsp;&nbsp;&nbsp;(a ; Skip (S a) ); b = a ; b

---
**skip_prop_15**

&nbsp;&nbsp;&nbsp;&nbsp;(a ; Skip (S b) ); b = a ; b

---
**skip_prop_16**

&nbsp;&nbsp;&nbsp;&nbsp;S a ⊆ C ⟹ post ((a ; Skip C); b) = post (a ; b)

---
**skip_prop_17**

&nbsp;&nbsp;&nbsp;&nbsp;S b ⊆ C ⟹ post ((a ; Skip C); b) = post (a ; b)

---
**skip_prop_18**

&nbsp;&nbsp;&nbsp;&nbsp;S a ⊆ C ⟹  Skip C ; (a ; Skip C) = (Skip (S a); a) ; Skip C

---
## Arbitrary_repetition.thy

**loop_l1**

&nbsp;&nbsp;&nbsp;&nbsp;s=0 ⟹ f=0 ⟹ loop p s f = Skip (S p) /<sub>p</sub> (Pre p) 

---
**loop_l2**

&nbsp;&nbsp;&nbsp;&nbsp;s=0 ⟹ f=1 ⟹ loop p s f = Skip (S p) /<sub>p</sub> (Pre p) ∪<sub>p</sub>  (Skip (S p) /<sub>p</sub> (Pre p);p)

---
**loop_l2_01**

&nbsp;&nbsp;&nbsp;&nbsp;loop p (f + 1) f = Fail (S p)

---
**loop_l2_02**

&nbsp;&nbsp;&nbsp;&nbsp;loop p 0 f ; p = loop p (0 + 1) (f + 1)

---
**loop_l2_03**

&nbsp;&nbsp;&nbsp;&nbsp;loop p s s ; p = loop p (s + 1) (s + 1)

---
**loop_l2_04**

&nbsp;&nbsp;&nbsp;&nbsp;s<f ⟹ loop p s f ; p = loop p (s + 1) (f + 1)

---
**loop_l2_05**

&nbsp;&nbsp;&nbsp;&nbsp;0<s ⟹ loop p s s = p<sup>s</sup> ∪<sub>p</sub> Fail {}

---
**loop_l2_1**

&nbsp;&nbsp;&nbsp;&nbsp;s=f ⟹ loop p s f ≡<sub>p</sub> p<sup>s</sup>

---
**loop_l2_2**

&nbsp;&nbsp;&nbsp;&nbsp;loop p s (s + 1) = p<sup>s</sup> ∪<sub>p</sub> p<sup>s + 1</sup>

---
**loop_l3**

&nbsp;&nbsp;&nbsp;&nbsp;s<f ⟹ loop p s (f + 1) ≡<sub>p</sub> (p<sup>f + 1</sup>) ∪<sub>p</sub> (loop p s f)

---
**loop_l4**

&nbsp;&nbsp;&nbsp;&nbsp;s<f ⟹ loop p s f ≡<sub>p</sub> (p<sup>s</sup>) ∪<sub>p</sub> (loop p (s + 1) f)

---
**loop_l6**

&nbsp;&nbsp;&nbsp;&nbsp;s=0 ⟹ s<f ⟹ loop p s f ≡<sub>p</sub> (Skip (S p) /<sub>p</sub> (Pre p)) ∪<sub>p</sub> (loop p 1 f)

---
&nbsp;&nbsp;&nbsp;&nbsp;0<s ⟹ s<f ⟹ loop p s f ≡<sub>p</sub> p<sup>s</sup> ∪<sub>p</sub> loop p (s + 1) f

---
**loop_l5**

&nbsp;&nbsp;&nbsp;&nbsp;s<f ⟹ s < k ⟹ k < f ⟹ loop p s f ≡<sub>p</sub> (loop p s k) ∪<sub>p</sub> (loop p (k + 1) f)

---
**loop_simplification**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [x,y] ⟹ Range_p x ∩ Pre y = {} ⟹ Range_p y ∩ Pre x = {} ⟹ (loop x s f) ∪<sub>p</sub> (loop y s f) ≡<sub>p</sub> loop (x ∪<sub>p</sub> y) s f

---
**equiv_is_maintained_by_arbitrary_repetition_1**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p<sub>1</sub>, p<sub>2</sub>] ⟹ p<sub>1</sub> ≡<sub>p</sub> p<sub>2</sub> ⟹ S p<sub>1</sub> = S p<sub>2</sub> ⟹ loop p<sub>1</sub> s f ≡<sub>p</sub> loop p<sub>2</sub> s f

---
**equiv_is_maintained_by_arbitrary_repetition_2**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p<sub>1</sub>, p<sub>2</sub>] ⟹ p<sub>1</sub> ≡<sub>p</sub> p<sub>2</sub> ⟹ 0<s ⟹ loop p<sub>1</sub> s f ≡<sub>p</sub> loop p<sub>2</sub> s f

---
**arbitrary_rep_feasibility_l1**

&nbsp;&nbsp;&nbsp;&nbsp;s > f ⟹ is_feasible p ⟹ is_feasible (loop p s f)

---
**arbitrary_rep_feasibility_l2**

&nbsp;&nbsp;&nbsp;&nbsp;s < f ⟹ is_feasible p ⟹ is_feasible (loop p s f)

---
**arbitrary_rep_feasibility**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ is_feasible (loop p s f)

---
**skip_compose_l_of_loop_1**

&nbsp;&nbsp;&nbsp;&nbsp;s < f ⟹ s=0 ⟹ loop p s f ≡<sub>p</sub> Skip (S p) /<sub>p</sub> (Pre p) ∪<sub>p</sub> loop p s f

---
**skip_compose_r_of_loop_2**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ loop p s f ≡<sub>p</sub> loop p s f ; Skip (S p)

---
**skip_compose_l_of_loop_3**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ loop p s f ≡<sub>p</sub> Skip (S p) ; loop p s f

---
**range_fixed_rep**

&nbsp;&nbsp;&nbsp;&nbsp;s<m ⟹ m<f ⟹ x ∉ Range_p (loop p s f) ⟹ x ∉ Range_p (p<sup>m</sup>)

---
**pre_is_known_arbitrary_rep_1**

&nbsp;&nbsp;&nbsp;&nbsp;∀x y. x ∈ Pre a ∧ (x, y) ∈ post (a ; (b /<sub>p</sub> (- C))<sup>n</sup>) → x ∈ Pre (a ; (b /<sub>p</sub> (- C))<sup>n</sup>)

---
**pre_is_known_arbitrary_rep_2**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ Pre a ⟹ (x, y) ∈ post (a ; (b /<sub>p</sub> (- C))<sup>n</sup>) ⟹ x ∈ Pre (a ; (b /<sub>p</sub> (- C))<sup>n</sup>)

---
**bad_index_is_fail_arbitrary**

&nbsp;&nbsp;&nbsp;&nbsp;f<s ⟹ loop a s f ≡<sub>p</sub> Fail {}

---
**fail_stays_fail_arbitrary**

&nbsp;&nbsp;&nbsp;&nbsp;s<f ⟹ loop p s f ≡<sub>p</sub> Fail {} ⟹ loop p s (f + 1) ≡<sub>p</sub> Fail {}

---
**fail_stays_fail_arbitrary_2**

&nbsp;&nbsp;&nbsp;&nbsp;s<f ⟹ loop p s (f + 1) ≡<sub>p</sub> Fail {} ⟹ loop p s f ≡<sub>p</sub> Fail {}

---
**fail_stays_fail_arbitrary_3**

&nbsp;&nbsp;&nbsp;&nbsp;s<f ⟹ loop p s (f + 1) ≡<sub>p</sub> Fail {} ≡ loop p s f ≡<sub>p</sub> Fail {}

---
**fail_stays_fail_arbitrary_4**

&nbsp;&nbsp;&nbsp;&nbsp;s<f ⟹ loop p s s ≡<sub>p</sub> Fail {} ≡ loop p s f ≡<sub>p</sub> Fail {}

---
**fail_arbitrary_implies_fixed**

&nbsp;&nbsp;&nbsp;&nbsp;k < n ⟹ loop (b /<sub>p</sub> (- C)) 0 n ≡<sub>p</sub> Fail {} ⟹ (b /<sub>p</sub> (- C)) <sup> </sup>k ≡<sub>p</sub> Fail {}

---
**extract_fixed_from_arbitrary**

&nbsp;&nbsp;&nbsp;&nbsp;k<n ⟹ a ; loop (b /<sub>p</sub> (- C)) 0 n ∖<sub>p</sub> C ≡<sub>p</sub> a ; loop (b /<sub>p</sub> (- C)) 0 n ∖<sub>p</sub> C ∪<sub>p</sub> a ; ((b /<sub>p</sub> (- C)) <sup> </sup>k) ∖<sub>p</sub> C

---
**fail_arbitrary_implies_fixed_2**

&nbsp;&nbsp;&nbsp;&nbsp;k < n ⟹ a ; loop (b /<sub>p</sub> (- C)) 0 n ∖<sub>p</sub> C ≡<sub>p</sub> Fail {} ⟹ a ; ((b /<sub>p</sub> (- C)) <sup> </sup>k) ∖<sub>p</sub> C ≡<sub>p</sub> Fail {}

---
&nbsp;&nbsp;&nbsp;&nbsp;Fail (S x) ∪<sub>p</sub> x <sup> </sup>0 = x <sup> </sup>0

---
**fixed_prop**

&nbsp;&nbsp;&nbsp;&nbsp;0<f ⟹ Fail (S x) ∪<sub>p</sub> x <sup> </sup>f = x <sup> </sup>f

---
**loop_choice3**

&nbsp;&nbsp;&nbsp;&nbsp;0<s ⟹ 0<f ⟹ all_feasible [x,y] ⟹ Range_p x ∩ Pre y = {} ⟹ Range_p y ∩ Pre x = {} ⟹ (loop x s f) ∪<sub>p</sub> (loop y s f) = loop (x ∪<sub>p</sub> y) s f

---
**Loop_fail**

&nbsp;&nbsp;&nbsp;&nbsp;loop p 0 n ≡<sub>p</sub> Fail {} ⟹ loop p 0 m ≡<sub>p</sub> Fail{}

---
## Atomic_concurrency.thy

&nbsp;&nbsp;&nbsp;&nbsp;foldl (f::'a Program ⇒ 'a Program ⇒ 'a Program) (f a x) xs = f a (foldl f x xs)

---
**complete_state_subset_fold_composition**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ complete_state xs ⟹ x ∈ S (foldl (;) (Skip (complete_state xs)) xs)

---
**fold_choice_inv_1**

&nbsp;&nbsp;&nbsp;&nbsp;foldl (∪<sub>p</sub>) (Fail {}) (a # xs)  = a ∪<sub>p</sub> foldl (∪<sub>p</sub>) (Fail {}) (xs) 

---
**fold_choice_inv_2**

&nbsp;&nbsp;&nbsp;&nbsp;S (foldl (∪<sub>p</sub>) (Fail {}) xs ) = ⋃ (set (map (S) xs))

---
**conc_elems_state**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (conc_elems xs) ⟹ S x = complete_state xs

---
**atomic_conc_complete_state**

&nbsp;&nbsp;&nbsp;&nbsp;S (atomic_conc xs) = complete_state xs

---
**atomic_conc_equivalence**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ S (Concat xs C) = S (atomic_conc xs)

---
**pre_zero**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (atomic_conc [ ]) = {}

---
**pre_one**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible x ⟹ Pre (atomic_conc [x]) = Pre x

---
**lemma_pre_1**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (atomic_conc (a#[b])) ⊆ Pre a ∪ Pre b

---
**list_equiv_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;list_equiv xs xs

---
**list_equiv_comp_equiv**

&nbsp;&nbsp;&nbsp;&nbsp;list_equiv xs ys ⟹ b ≡<sub>p</sub> b' ⟹ fold (;) xs b ≡<sub>p</sub> fold (;) ys b'

---
**skip_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible a ⟹ S a ⊆ C ⟹ a ; Skip C ≡<sub>p</sub> a

---
**skip_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible a ⟹a ; Skip (complete_state (a # xs)) ≡<sub>p</sub> a

---
**skip_restrict**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible a ⟹ fold (;) xs (a ; Skip (complete_state (a # xs))) ≡<sub>p</sub> fold (;) xs a

---
**feas_of_prop**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible (feas_of p)

---
**feas_of_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ feas_of p = p

---
**skip_prop_4**

&nbsp;&nbsp;&nbsp;&nbsp;a ; Skip (S a) ≡<sub>p</sub> feas_of a

---
**skip_prop_5**

&nbsp;&nbsp;&nbsp;&nbsp;fold (;) xs (Skip (complete_state (a # xs)) ; a) ≡<sub>p</sub> fold (;) xs a

---
**get_trace**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ x ∈ set (conc_elems xs) ⟹ ∃tr. tr ∈ set (permutations xs) ∧ x = Concat tr C

---
**skip_prop_6**

&nbsp;&nbsp;&nbsp;&nbsp;Skip (S p ∪ x) ; p ≡<sub>p</sub> Skip (S p) ; p

---
**no_right_neutral**

&nbsp;&nbsp;&nbsp;&nbsp;∃t. p;t ≡<sub>p</sub> p

---
**corestrict_skip**

&nbsp;&nbsp;&nbsp;&nbsp;(a; Skip (S a ∪ S b)) ; b ≡<sub>p</sub> a ; b

---
**skip_prop_8**

&nbsp;&nbsp;&nbsp;&nbsp;(a; Skip (S a)) ; b ≡<sub>p</sub> a ; b

---
**skip_prop_9**

&nbsp;&nbsp;&nbsp;&nbsp;(a; Skip (S b)) ; b ≡<sub>p</sub> a ; b

---
**fold_decomp**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ (foldl (;) (a) (xs)) ≡<sub>p</sub> a; (foldl (;) (Skip (complete_state xs)) (xs))

---
**fold_decomp2**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ (foldl (;) (a) (xs)) ≡<sub>p</sub> a; (foldl (;) (Skip (S a)) (xs))

---
**fold_equiv_maintained**

&nbsp;&nbsp;&nbsp;&nbsp;a ≡<sub>p</sub> b ⟹ foldl (;) a xs ≡<sub>p</sub> foldl (;) b xs

---
**fold_compress_1**

&nbsp;&nbsp;&nbsp;&nbsp;ys ≠ [ ] ⟹ ∃e'. (a);e' ≡<sub>p</sub> (foldl (;) (Skip (complete_state ([a]@ys))) ([a]@ys))

---
**fold_compress_2**

&nbsp;&nbsp;&nbsp;&nbsp;∃e'. e';a ≡<sub>p</sub> (foldl (;) (Skip (complete_state (ys@[a]))) (ys@[a]))

---
**fold_compress_3**

&nbsp;&nbsp;&nbsp;&nbsp;∃s' e'. (s';a);e' ≡<sub>p</sub> (foldl (;) (Skip (complete_state (xs@[a]@ys))) (xs@[a]@ys)) ∨ s';a=(foldl (;) (Skip (complete_state (xs@[a]@ys))) (xs@[a]@ys))

---
**conc_elems_dec**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (conc_elems (a # xs)) ⟹ ∃s' e'. (s';a);e' = x ∨ s';a=x ∨ a = x∨ a;e' = x

---
**concat_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ tr ∈ set (permutations xs) ⟹ Concat tr (complete_state xs) ∈ set (conc_elems xs)

---
**fold_choice_inv**

&nbsp;&nbsp;&nbsp;&nbsp;t ∈ set (xs) ⟹ foldl (∪<sub>p</sub>) (x) (xs) = t ∪<sub>p</sub> (foldl (∪<sub>p</sub>) (x) (xs))

---
**atomic_conc_inv**

&nbsp;&nbsp;&nbsp;&nbsp;tr ∈ set (conc_elems xs) ⟹ tr ∪<sub>p</sub> atomic_conc xs ≡<sub>p</sub> atomic_conc xs

---
**atomic_conc_inv2**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (conc_elems xs) ⟹ x ⊆<sub>p</sub> atomic_conc xs

---
**atomic_conc_inv3**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ Concat xs (complete_state xs) ⊆<sub>p</sub> atomic_conc xs

---
**perm_prop**

&nbsp;&nbsp;&nbsp;&nbsp;set (permutations (a@b)) = set (permutations (b@a))

---
**perm_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (permutations y) ⟹ set (conc_elems (y)) = set (conc_elems (x))

---
**perm_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;set (conc_elems (a@b)) = set (conc_elems (b@a))

---
**perm_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;size (insert_all x xs) = size xs + 1

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

&nbsp;&nbsp;&nbsp;&nbsp;a ∈ set (map (insert_all x) (permutations xs)) ⟹ b ∈ set a ⟹ size b = size xs + 1

---
**perm_prop9**

&nbsp;&nbsp;&nbsp;&nbsp;a ∈ set (map (insert_all x) (permutations xs)) ⟹ size a = size xs + 1

---
**size_concat**

&nbsp;&nbsp;&nbsp;&nbsp;size (concat xss) = sum_list (map size xss)

---
**insert_all_prop**

&nbsp;&nbsp;&nbsp;&nbsp;size (concat (map (insert_all x) xss)) = sum_list (map (λy. Suc (size y)) xss)

---
&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (permutations xs) ⟹ y ∈ set (permutations xs) ⟹ size x = size y

---
**sum_list_simp**

&nbsp;&nbsp;&nbsp;&nbsp;(∀x ∈ set xss. ∀ y ∈ set xss. size x = size y) ⟹ sum_list (map size xss) = size xss * size (hd xss)

---
**size_lemma**

&nbsp;&nbsp;&nbsp;&nbsp;∀x ∈ set xs. size x = n ⟹ size (concat xs) = size xs * n

---
**length_concat_insert_all**

&nbsp;&nbsp;&nbsp;&nbsp;length (concat (map (insert_all x) (permutations xs))) = (length xs + 1) * length (permutations xs)

---
**size_permutations_fact**

&nbsp;&nbsp;&nbsp;&nbsp;length (permutations xs) = fact (length xs)

---
**perm_size_eq**

&nbsp;&nbsp;&nbsp;&nbsp;size xs = size ys ⟹ size (permutations xs) = size (permutations ys)

---
**perm_prop10**

&nbsp;&nbsp;&nbsp;&nbsp;size (permutations (x#xs)) = size (permutations (xs)) * size (x#xs)

---
**fold_choice_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;permutations a = permutations b ⟹ set (conc_elems a) = set (conc_elems b)

---
&nbsp;&nbsp;&nbsp;&nbsp;size xs > 0⟹ size (conc_elems xs) > 0

---
**fold_choice_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;a ∈ set xs ⟹ foldl (∪<sub>p</sub>) a xs = foldl (∪<sub>p</sub>) (Skip {}) xs

---
**fold_choice_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;a ∈ set (conc_elems (xs)) ⟹ foldl (∪<sub>p</sub>) (a) (conc_elems (xs)) = foldl (∪<sub>p</sub>) (Skip {}) (conc_elems (xs))

---
**fold_choice_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;foldl (∪<sub>p</sub>) x (x'#xs) = foldl (∪<sub>p</sub>) (Fail {}) (x#x'#xs)

---
**atomic_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ ys ∈ set (permutations xs) ⟹ Concat ys (complete_state xs) ⊆<sub>p</sub> atomic_conc xs

---
**atomic_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;atomic_conc [a,b] ≡<sub>p</sub> a ; b ∪<sub>p</sub> b ; a

---
**equiv_to_equal**

&nbsp;&nbsp;&nbsp;&nbsp;S a = S b ⟹ post a = post b ⟹ a ≡<sub>p</sub> b ⟹ a = b

---
**atomic_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;atomic_conc [a, b ∪<sub>p</sub> c] ≡<sub>p</sub> atomic_conc [a,b] ∪<sub>p</sub> atomic_conc [a,c]

---
**atomic_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;atomic_conc [a ∪<sub>p</sub> b] = atomic_conc [a] ∪<sub>p</sub> atomic_conc [b]

---
**set_to_list_set**

&nbsp;&nbsp;&nbsp;&nbsp;finite xs ⟹ set (set_to_list xs) = xs

---
**specialize_prop**

&nbsp;&nbsp;&nbsp;&nbsp;a = b ⟹ b ⊆<sub>p</sub> a ∧ a ⊆<sub>p</sub> b

---
**atomic_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;atomic_conc [a ∪<sub>p</sub> b, c] ≡<sub>p</sub> atomic_conc [a,c] ∪<sub>p</sub> atomic_conc [b,c]

---
**commute_compose**

&nbsp;&nbsp;&nbsp;&nbsp;commute_programs3 a b ⟹ atomic_conc [a,b] ≡<sub>p</sub> a ; b

---
## Big_choice.thy

**fold_compose**

&nbsp;&nbsp;&nbsp;&nbsp;foldl (;) (a ; b) xs = a ; (foldl (;) b xs)

---
**fold_choice**

&nbsp;&nbsp;&nbsp;&nbsp;foldl (∪<sub>p</sub>) (a ∪<sub>p</sub> b) xs = a ∪<sub>p</sub> (foldl (∪<sub>p</sub>) b xs)

---
**Choice_prop_1_2**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ ⋃<sub>p</sub> (x#xs) = x ∪<sub>p</sub> ⋃<sub>p</sub> xs

---
**Choice_prop_1_3**

&nbsp;&nbsp;&nbsp;&nbsp;a@b ≠ [ ] ⟹ ⋃<sub>p</sub> (a@x#b) = x ∪<sub>p</sub> ⋃<sub>p</sub> (a@b)

---
**Choice_prop_1_1**

&nbsp;&nbsp;&nbsp;&nbsp;ys ∈ set (permutations xs) ⟹ ⋃<sub>p</sub> xs = ⋃<sub>p</sub> ys

---
**Choice_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ ⋃<sub>p</sub> (xs@[x]) = x ∪<sub>p</sub> ⋃<sub>p</sub> xs

---
**Choice_prop_1_4**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ foldl (∪<sub>p</sub>) x xs = x ∪<sub>p</sub> Choice xs

---
**Choice_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;⋃<sub>p</sub> [a;t. t ← xs] ≡<sub>p</sub> a;⋃<sub>p</sub> [t. t ← xs]

---
**Choice_prop_3**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ ⋃<sub>p</sub> (xs@[x]) = ⋃<sub>p</sub> (xs) ∪<sub>p</sub> x

---
**Choice_prop_4**

&nbsp;&nbsp;&nbsp;&nbsp;⋃<sub>p</sub> [t;a. t ← xs] ≡<sub>p</sub> ⋃<sub>p</sub> [t. t ← xs];a

---
**Choice_state**

&nbsp;&nbsp;&nbsp;&nbsp;S (⋃<sub>p</sub> (xs)) = ⋃ {S x | x . x ∈ set xs}

---
**Union_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ {} ⟹ ⋃ {t | x . x ∈ xs} = t

---
**Choice_prop_5**

&nbsp;&nbsp;&nbsp;&nbsp;size xs = 1 ⟹ set (xs) = {x} ⟹ (⋃<sub>p</sub> xs = x)

---
**Choice_prop_6**

&nbsp;&nbsp;&nbsp;&nbsp;size xs > 1 ⟹ set (xs) = {x} ⟹ (⋃<sub>p</sub> xs = x ∪<sub>p</sub> x)

---
**Choice_prop_7**

&nbsp;&nbsp;&nbsp;&nbsp;a ≠ [ ] ⟹ b ≠ [ ] ⟹ ⋃<sub>p</sub> a ∪<sub>p</sub> ⋃<sub>p</sub> b = ⋃<sub>p</sub> (a@b)

---
**Choice_prop_8**

&nbsp;&nbsp;&nbsp;&nbsp;∃x ∈ set xs. p x ⟹ ∃x ∈ set xs. ¬p x ⟹ ⋃<sub>p</sub> (filter (λx. p x) xs) ∪<sub>p</sub> ⋃<sub>p</sub> (filter (λx. ¬p x) xs) = ⋃<sub>p</sub> xs

---
**Choice_prop_9**

&nbsp;&nbsp;&nbsp;&nbsp;size xs>1 ⟹ size ys>1 ⟹ set xs = set ys ⟹ ⋃<sub>p</sub> (xs) = ⋃<sub>p</sub> (ys)

---
**Choice_prop_10**

&nbsp;&nbsp;&nbsp;&nbsp;size xs=1 ⟹ size ys=1 ⟹ set xs = set ys ⟹ ⋃<sub>p</sub> (xs) = ⋃<sub>p</sub> (ys)

---
**Choice_prop11**

&nbsp;&nbsp;&nbsp;&nbsp;size xs > 1 ⟹ ⋃<sub>p</sub> (filter (λt. P t) xs) ∪<sub>p</sub> ⋃<sub>p</sub> (filter (λt. ¬P t) xs) = ⋃<sub>p</sub> xs

---
**Choice_prop12**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set xs ⟹ ⋃<sub>p</sub> (filter ((=) x) (x#xs)) = x ∪<sub>p</sub> x

---
**Choice_state_1**

&nbsp;&nbsp;&nbsp;&nbsp;complete_state xs = S (Choice xs)

---
**Concat_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ foldl (;) x xs = x ; Concat xs s

---
**Concat_state**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ complete_state xs = S (Concat xs s)

---
**Choice_prop_13**

&nbsp;&nbsp;&nbsp;&nbsp;size xs > 0 ⟹ ⋃<sub>p</sub> [a;(Concat t s). t ← xs] ≡<sub>p</sub> a;⋃<sub>p</sub> [(Concat t s). t ← xs]

---
**Choice_prop_14**

&nbsp;&nbsp;&nbsp;&nbsp;⋃<sub>p</sub> [t /<sub>p</sub> C . t ← xs] ≡<sub>p</sub> ⋃<sub>p</sub> [t . t ← xs]/<sub>p</sub> C

---
&nbsp;&nbsp;&nbsp;&nbsp;⋃<sub>p</sub> [t /<sub>p</sub> C . t ← xs] = ⋃<sub>p</sub> [t . t ← xs]/<sub>p</sub> C

---
**Choice_prop_15**

&nbsp;&nbsp;&nbsp;&nbsp;⋃<sub>p</sub> [t ∖<sub>p</sub> C . t ← xs] = ⋃<sub>p</sub> [t . t ← xs]∖<sub>p</sub> C

---
**Concat_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ Concat (xs@[x]) s = Concat xs s ; x

---
**Concat_prop_3**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ Concat xs s /<sub>p</sub> C ≡<sub>p</sub> Concat (hd xs /<sub>p</sub> C # tl xs) s

---
**Concat_prop_4**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ Concat xs s ∖<sub>p</sub> C ≡<sub>p</sub> Concat (butlast xs @ [(last xs)∖<sub>p</sub> C]) s

---
**Choice_prop_16**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set xs ⟹ ⋃<sub>p</sub> xs ≡<sub>p</sub> ⋃<sub>p</sub> xs ∪<sub>p</sub> x

---
**Choice_prop_17**

&nbsp;&nbsp;&nbsp;&nbsp;size xs > 1 ⟹ x ∈ set xs ⟹ ⋃<sub>p</sub> xs = ⋃<sub>p</sub> xs ∪<sub>p</sub> x

---
**Concat_prop_5**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ ys ≠ [ ] ⟹ Concat (xs@ys) s = Concat xs s ; Concat ys s

---
**Concat_prop_6**

&nbsp;&nbsp;&nbsp;&nbsp;Concat (a ∪<sub>p</sub> b # xs) s = Concat (a # xs) s ∪<sub>p</sub> Concat (b # xs) s

---
**Concat_prop_7**

&nbsp;&nbsp;&nbsp;&nbsp;Concat (xs@[a ∪<sub>p</sub> b]) s ≡<sub>p</sub> Concat (xs@[a]) s ∪<sub>p</sub> Concat (xs@[b]) s

---
**Concat_prop_8**

&nbsp;&nbsp;&nbsp;&nbsp;e ≠ [ ] ⟹ Concat (s@(a ∪<sub>p</sub> b)#e) s' ≡<sub>p</sub> Concat (s@a#e) s' ∪<sub>p</sub> Concat (s@b#e) s'

---
**Choice_prop_18**

&nbsp;&nbsp;&nbsp;&nbsp;size b > 1 ⟹ ⋃<sub>p</sub> b = ⋃<sub>p</sub> b ∪<sub>p</sub> Fail {}

---
**Choice_prop_19**

&nbsp;&nbsp;&nbsp;&nbsp;size (a@b) > 1 ⟹ ⋃<sub>p</sub> a ∪<sub>p</sub> ⋃<sub>p</sub> b = ⋃<sub>p</sub> (a@b)

---
**Choice_prop_20**

&nbsp;&nbsp;&nbsp;&nbsp;size (a@b) > 0 ⟹ ⋃<sub>p</sub> a ∪<sub>p</sub> (x ∪<sub>p</sub> ⋃<sub>p</sub> b) = ⋃<sub>p</sub> (a@x#b)

---
**Choice_prop_21**

&nbsp;&nbsp;&nbsp;&nbsp;S x ⊆ complete_state (a@b) ⟹ ⋃<sub>p</sub> a ∪<sub>p</sub> (x /<sub>p</sub> FALSE ∪<sub>p</sub> ⋃<sub>p</sub> b) = ⋃<sub>p</sub> a ∪<sub>p</sub> (Fail {} ∪<sub>p</sub> ⋃<sub>p</sub> b)

---
**list_prop**

&nbsp;&nbsp;&nbsp;&nbsp;1 < i ⟹ i < n ⟹ [p . t ← [1 .. int n]] = [p . t ← [1 .. int i]] @ [p . t ← [int (i + 1) .. int n]]

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

&nbsp;&nbsp;&nbsp;&nbsp;0<n ⟹ Concat [p . t ← [1 .. int n]] s ; p = Concat [p . t ← [1 .. int (n + 1)]] s

---
**Concat_prop_10**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ Concat (x#xs) s = x ; Concat xs s

---
**Concat_prop_11**

&nbsp;&nbsp;&nbsp;&nbsp;0<n ⟹ p ; Concat [p . t ← [1 .. int n]] s = Concat [p . t ← [1 .. int (n + 1)]] s

---
**Choice_prop_22**

&nbsp;&nbsp;&nbsp;&nbsp;a ∪<sub>p</sub> ⋃<sub>p</sub> (x#xs) = a ∪<sub>p</sub> (x ∪<sub>p</sub> ⋃<sub>p</sub> xs)

---
**Choice_prop_23**

&nbsp;&nbsp;&nbsp;&nbsp;∀x ∈ set xs. x = y ⟹ ⋃<sub>p</sub> xs = Fail {} ∨ ⋃<sub>p</sub> xs = y ∨ ⋃<sub>p</sub> xs = y ∪<sub>p</sub> y

---
**Choice_prop_24**

&nbsp;&nbsp;&nbsp;&nbsp;distinct xs ⟹ distinct ys ⟹ set xs = set ys ⟹ size xs = size ys ⟹ ⋃<sub>p</sub> xs = ⋃<sub>p</sub> ys

---
**atomic_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ ∀x ∈ F. is_atomic x ⟹ get_atomic (⋃<sub>p</sub> (set_to_list F)) = F

---
**decomp_programs**

&nbsp;&nbsp;&nbsp;&nbsp;Pre a = Pre p - {y} ⟹ post b = {t. t ∈ post p ∧ (fst t=y ∨ snd t=y)} ⟹ Pre b = Pre p ∩ ({y} ∪ Domain (post p ∖<sub>r</sub> {y})) ⟹ post a = {t. t ∈ post p ∧ (fst t ≠ y ∧ snd t ≠ y)} ⟹ a ∪<sub>p</sub> b ≡<sub>p</sub> p

---
&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ finite (S p) ⟹ ∃xs. ⋃<sub>p</sub> xs ≡<sub>p</sub> p ∧ (∀x ∈ set xs. is_atomic x)

---
**civilized_finite**

&nbsp;&nbsp;&nbsp;&nbsp;civilized_n x B n ⟹ finite B

---
**civilized_ind**

&nbsp;&nbsp;&nbsp;&nbsp;civilized_n x B n ⟹ civilized_n x B (n + 1)

---
**civilized_ind2**

&nbsp;&nbsp;&nbsp;&nbsp;⋀m. n<m ⟹ civilized_n x B n ⟹ civilized_n x B m

---
**civilized_generic**

&nbsp;&nbsp;&nbsp;&nbsp;civilized_n x B n = ((∃a b m m'. m<n ∧ m'<n ∧ civilized_n a B m ∧ civilized_n b B m' ∧ (a ; b = x ∨ a ∪<sub>p</sub> b = x)) ∧ finite B) ∨ civilized_n x B 0

---
**civ_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;civilized_n p B n ⟹ civilized p B

---
**civ_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;civilized p B ⟹ civilized q B ⟹ civilized (p;q) B

---
**civ_prop_3**

&nbsp;&nbsp;&nbsp;&nbsp;civilized p B ⟹ civilized q B ⟹ civilized (p ∪<sub>p</sub> q) B

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

&nbsp;&nbsp;&nbsp;&nbsp;basic a = basic b ⟹ normal_of a B = normal_of b B

---
**basic_normal2**

&nbsp;&nbsp;&nbsp;&nbsp;basic a = insert (Fail {}) (basic b) ⟹ normal_of a B = normal_of b B

---
**normal_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;finite B ⟹ normal_of [[ ]] B

---
**normal_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;finite B ⟹ normal_of [[〈State = {}, Pre = {}, post = {}〉]] B

---
**normal_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;infinite B ⟹ ¬normal_of xs B

---
**normal_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;finite B ⟹ normal_of xs B ⟹ normal_of ([ ]#xs) B

---
**normal_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;finite B ⟹ normal_of ([ ]#xs) B ⟹ normal_of xs B

---
**normal_prop7**

&nbsp;&nbsp;&nbsp;&nbsp;normal_of [x#xs] B = (normal_of [[x]] B ∧ normal_of [xs] B)

---
**basic_prop0**

&nbsp;&nbsp;&nbsp;&nbsp;basic [[x]] ∪ basic [xs] = basic [x#xs]

---
**basic_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;basic [x] ∪ basic xs = basic (x#xs)

---
**basic_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;basic xs ∪ basic ys = basic (xs@ys)

---
**normal_prop8**

&nbsp;&nbsp;&nbsp;&nbsp;trace ∈ set xs ⟹ normal_of xs B ⟹ normal_of [trace] B

---
**normal_prop9**

&nbsp;&nbsp;&nbsp;&nbsp;normal_of ((a # x) # xs) B ⟹ normal_of [[a]] B

---
**basic_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;trace ∈ set xs ⟹ basic [trace] ⊆ basic xs

---
**basic_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set trace ⟹ basic [[x]] ⊆ basic [trace]

---
**normal_prop10**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set trace ⟹ trace ∈ set xs ⟹ normal_of xs B ⟹ normal_of [[x]] B

---
**normal_prop11**

&nbsp;&nbsp;&nbsp;&nbsp;normal_of ((a#x)#xs) B = (normal_of [[a]] B ∧ normal_of (x#xs) B)

---
**normal_prop12**

&nbsp;&nbsp;&nbsp;&nbsp;normal_of (x#xs) B = (normal_of [x] B ∧ normal_of xs B)

---
**normal_prop13**

&nbsp;&nbsp;&nbsp;&nbsp;normal_of (a#p) B = normal_of ((〈State = {}, Pre = {}, post = {}〉#Skip (complete_state (set_to_list B))#a)#p) B

---
**fold_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;trace ∈ set p ⟹ x ∈ set trace ⟹ x ∈ foldl (∪) {} (map set p)

---
**normal_prop14**

&nbsp;&nbsp;&nbsp;&nbsp;normal_of p B ⟹ trace ∈ set p ⟹ x ∈ set trace ⟹ x ∈ {Fail {}, Skip (complete_state (set_to_list B))} ∪ B

---
**basic_monotone1**

&nbsp;&nbsp;&nbsp;&nbsp;basic a ⊆ basic (x#a)

---
**basic_monotone2**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set p ⟹ basic [x] ⊆ basic p

---
**basic_decomp1**

&nbsp;&nbsp;&nbsp;&nbsp;basic [x] ∪ basic xs = basic (x#xs)

---
**basic_decomp2**

&nbsp;&nbsp;&nbsp;&nbsp;basic [x] ∪ basic xs = basic (xs@[x])

---
**fold_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;foldl (∪) (foldl (∪) {} xs) ys = foldl (∪) {} xs ∪ foldl (∪) {} ys

---
**basic_decomp**

&nbsp;&nbsp;&nbsp;&nbsp;basic a ∪ basic b = basic (a@b)

---
**basic_monotone**

&nbsp;&nbsp;&nbsp;&nbsp;set a ⊆ set b ⟹ basic a ⊆ basic b

---
**basic_prop**

&nbsp;&nbsp;&nbsp;&nbsp;basic (a@b) ⊆ B ⟹ basic b ⊆ B

---
**basic_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;basic (a@b) ⊆ B ⟹ basic a ⊆ B

---
**basic_monotone3**

&nbsp;&nbsp;&nbsp;&nbsp;basic [a] ⊆ basic [a@b]

---
**basic_monotone4**

&nbsp;&nbsp;&nbsp;&nbsp;basic [b] ⊆ basic [a@b]

---
**basic_monotone5**

&nbsp;&nbsp;&nbsp;&nbsp;basic [b] ∪ basic [a] = basic [a@b]

---
**civilized_empty2**

&nbsp;&nbsp;&nbsp;&nbsp;finite B ⟹ civilized_n (⋃<sub>p</sub> [ ]) B 0

---
**civilized_empty3**

&nbsp;&nbsp;&nbsp;&nbsp;finite B ⟹ civilized_n (Fail {}) B 0

---
**civilized_empty4**

&nbsp;&nbsp;&nbsp;&nbsp;finite B ⟹ civilized_n (Skip {}) B 0

---
**normal_civilized**

&nbsp;&nbsp;&nbsp;&nbsp;normal_of p B ⟹ civilized (evaluate p (complete_state (set_to_list B))) B

---
**concat_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate ([ ] ;<sub>c</sub> b) c = Fail {}

---
**concat_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate [ ] c = Fail {}

---
**concat_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ evaluate (x#xs) c = evaluate [x] c ∪<sub>p</sub> evaluate xs c

---
**concat_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;complete_cnf_state (x#xs) ⊆ c ⟹ xs ≠ [ ] ⟹ evaluate (x#xs) c = evaluate [x] c ∪<sub>p</sub> evaluate xs c

---
**concat_prop4_1**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate (x#xs) c ≡<sub>p</sub> evaluate [x] c ∪<sub>p</sub> evaluate xs c

---
**fail_compose**

&nbsp;&nbsp;&nbsp;&nbsp;Fail {} ; p ≡<sub>p</sub> Fail {}

---
**concat_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate (a@b) c ≡<sub>p</sub> evaluate a c ∪<sub>p</sub> evaluate b c

---
**Skip_concat**

&nbsp;&nbsp;&nbsp;&nbsp;Skip (complete_state a) ; Concat a (complete_state a) ≡<sub>p</sub> Concat a (complete_state a)

---
**concat_prop**

&nbsp;&nbsp;&nbsp;&nbsp;a ≠ [ ] ⟹ Concat a (insert x (complete_state a)) ≡<sub>p</sub> Concat a (complete_state a)

---
**state_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;S (evaluate xs C) ∪ S (evaluate [x] C) = S (evaluate (x#xs) C)

---
**state_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;S (evaluate xs C) ∪ S (evaluate ys C) = S (evaluate (ys@xs) C)

---
**eval_prop**

&nbsp;&nbsp;&nbsp;&nbsp;[ ] ∉ set xs ⟹ evaluate xs C = evaluate xs D

---
**state_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;[ ] ∈ set xs ⟹ complete_cnf_state (xs) ⊆ S (evaluate (xs) (complete_cnf_state (xx#xs)))

---
**state_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;[ ] ∉ set xs ⟹ complete_cnf_state (xs) ⊆ S (evaluate (xs) (complete_cnf_state (xx#xs)))

---
**state_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;complete_cnf_state (xs) ⊆ S (evaluate (xs) (complete_cnf_state (xx#xs)))

---
**state_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;S (evaluate xs (complete_cnf_state xs)) = complete_cnf_state xs

---
**skip_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;Skip (complete_cnf_state xs) ; evaluate (xs) (complete_cnf_state xs) ≡<sub>p</sub> evaluate (xs) (complete_cnf_state xs)

---
**concat_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate ([ ]#xs) (complete_cnf_state xs) ≡<sub>p</sub> Skip (complete_cnf_state xs) ∪<sub>p</sub> evaluate xs (complete_cnf_state xs)

---
**non_empty0**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty (non_empty xs) = non_empty xs

---
**non_empty1**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty [ ] = [ ]

---
**non_empty2**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty [[ ]] = [ ]

---
**cnf_choice1**

&nbsp;&nbsp;&nbsp;&nbsp;[ ] ∪<sub>c</sub> p = non_empty p

---
**cnf_choice1**

&nbsp;&nbsp;&nbsp;&nbsp;[ ] ∪<sub>c</sub> p = p

---
**non_empty3**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty ([ ]#xs) = non_empty xs

---
**non_empty4**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty (a@b) = non_empty a @ non_empty b

---
**cnf_choice2**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty (x#xs) = [x] ∪<sub>c</sub> xs

---
**cnf_choice2**

&nbsp;&nbsp;&nbsp;&nbsp;(x#xs) = [x] ∪<sub>c</sub> xs

---
**cnf_choice3**

&nbsp;&nbsp;&nbsp;&nbsp;ys ∪<sub>c</sub> (x#xs) = (ys@[x]) ∪<sub>c</sub> xs

---
**non_empty5**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty ((xx # x) # b) = (xx#x) # (non_empty b)

---
**non_empty6**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty ((xx # x) # b) = [xx#x] ∪<sub>c</sub> (non_empty b)

---
**non_empty6**

&nbsp;&nbsp;&nbsp;&nbsp;((xx # x) # b) = [xx#x] ∪<sub>c</sub> b

---
**non_empty7**

&nbsp;&nbsp;&nbsp;&nbsp;((x#xs)@(y#ys)) = (x#xs) ∪<sub>c</sub> (y#ys)

---
**non_empty7**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty ((x#xs)@(y#ys)) = (x#xs) ∪<sub>c</sub> (y#ys)

---
**non_empty8**

&nbsp;&nbsp;&nbsp;&nbsp;a ∪<sub>c</sub> b ≠ [[ ]] ⟹ a ∪<sub>c</sub> b = (non_empty a) ∪<sub>c</sub> (non_empty b)

---
&nbsp;&nbsp;&nbsp;&nbsp;evaluate (non_empty a) = evaluate a

---
**cnf_choice_4**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate (a ∪<sub>c</sub> b) = evaluate (non_empty a ∪<sub>c</sub> non_empty b)

---
**state_prop7**

&nbsp;&nbsp;&nbsp;&nbsp;S (evaluate [y] (complete_state y)) = complete_state y

---
**skip_prop**

&nbsp;&nbsp;&nbsp;&nbsp;S x ⊆ C ⟹ is_feasible x ⟹x ; Skip C ≡<sub>p</sub> x

---
**concat_prop8**

&nbsp;&nbsp;&nbsp;&nbsp;complete_state y ⊆ C ⟹ evaluate [[ ]] C ; evaluate [y] C ≡<sub>p</sub> evaluate ([[ ]] ;<sub>c</sub> [y]) C

---
**concat_prop9**

&nbsp;&nbsp;&nbsp;&nbsp;x ≠ [ ] ⟹ y ≠ [ ] ⟹ [x] ;<sub>c</sub> [y] = [x@y]

---
**concat_prop10**

&nbsp;&nbsp;&nbsp;&nbsp;complete_state (x#xs) ⊆ C ⟹ all_feasible (x#xs) ⟹ evaluate [[x]] C ; evaluate [xs] C ≡<sub>p</sub> evaluate ([[x]] ;<sub>c</sub> [xs]) C

---
**feas_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible (x @ y) ⟹ all_feasible x

---
**feas_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible (x @ y) ⟹ all_feasible y

---
**concat_prop11**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible (x@y) ⟹ complete_state (x@y) ⊆ C ⟹ evaluate [x] C ; evaluate [y] C ≡<sub>p</sub> evaluate ([x] ;<sub>c</sub> [y]) C

---
**concat_prop11_1**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible (x@y) ⟹ evaluate [x] (complete_state (x@y)) ; evaluate [y] (complete_state (x@y)) ≡<sub>p</sub> evaluate ([x] ;<sub>c</sub> [y]) (complete_state (x@y))

---
**concat_prop12**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible (a#x@y) ⟹ (complete_state (a#x@y)) ⊆ C ⟹ evaluate [a # x] C ; evaluate [y] C ≡<sub>p</sub> evaluate ([a # x] ;<sub>c</sub> [y]) C

---
**concat_prop12_1**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible (a#x@y) ⟹ evaluate [a # x] (complete_state (a#x@y)) ; evaluate [y] (complete_state (a#x@y)) ≡<sub>p</sub> evaluate ([a # x] ;<sub>c</sub> [y]) (complete_state (a#x@y))

---
**choice_non_empty**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty a ∪<sub>c</sub> b = a ∪<sub>c</sub> b

---
**choice_non_empty2**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty a ∪<sub>c</sub> non_empty b = a ∪<sub>c</sub> b

---
**non_empty9**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set (non_empty xs) ⟹ x ∈ set xs

---
**non_empty10**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty xs = [y] ⟹ ∃a b. a@y#b = xs

---
**non_empty11**

&nbsp;&nbsp;&nbsp;&nbsp;xs = [ ] ⟹ evaluate xs C = Fail {}

---
**non_empty12**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty xs = [x] ⟹ non_empty xs = xs ⟹  evaluate xs = evaluate [x]

---
**nonempty_monotonic**

&nbsp;&nbsp;&nbsp;&nbsp;size (non_empty (x#xs)) > size (non_empty xs)

---
**non_empty_reduces_size**

&nbsp;&nbsp;&nbsp;&nbsp;size (non_empty xs) < size xs

---
**non_empty_13**

&nbsp;&nbsp;&nbsp;&nbsp;size (x#xs) = size (non_empty (x#xs)) ⟹ x ≠ [ ]

---
**non_empty_14**

&nbsp;&nbsp;&nbsp;&nbsp;size b = size (non_empty b) ⟹ b = (non_empty b)

---
**eval_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;size b = 1 ⟹ size (non_empty b) = 1 ⟹ evaluate b = evaluate (non_empty b)

---
**comp_cnf3**

&nbsp;&nbsp;&nbsp;&nbsp;x ≠ [ ] ⟹ y ≠ [ ] ⟹ Concat x (complete_state (x@y)) ; Concat y (complete_state (x@y)) = Concat (x @ y) (complete_state (x@y))

---
**comp_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;x ; (y ∪<sub>p</sub> Skip {}) ≡<sub>p</sub> x ; y

---
**choice_cnf_thm**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate xs (complete_cnf_state (xs@ys)) ∪<sub>p</sub> evaluate ys (complete_cnf_state (xs@ys)) ≡<sub>p</sub> evaluate (xs ∪<sub>c</sub> ys) (complete_cnf_state (xs@ys))

---
**non_empty14**

&nbsp;&nbsp;&nbsp;&nbsp;∀t ∈ set xs. t ≠ [ ] ⟹ non_empty xs = xs

---
**choic_cnf1**

&nbsp;&nbsp;&nbsp;&nbsp;(x#xs) ;<sub>c</sub> ys = ([x] ;<sub>c</sub> ys) ∪<sub>c</sub> (xs ;<sub>c</sub> ys)

---
**comp_distrib_r**

&nbsp;&nbsp;&nbsp;&nbsp;(b ∪<sub>c</sub> c) ;<sub>c</sub> a = (b ;<sub>c</sub> a) ∪<sub>c</sub> (c ;<sub>c</sub> a)

---
**choice_cnf_commute**

&nbsp;&nbsp;&nbsp;&nbsp;a ∪<sub>c</sub> (b ∪<sub>c</sub> c) = (a ∪<sub>c</sub> b) ∪<sub>c</sub> c

---
**equal_sym**

&nbsp;&nbsp;&nbsp;&nbsp;equal_cnf a b = equal_cnf b a

---
**equal_empty**

&nbsp;&nbsp;&nbsp;&nbsp;equal_cnf a [ ] ⟹ a = [ ]

---
**eval_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;ys≠[ ] ⟹ evaluate ys C ∪<sub>p</sub> evaluate [y] C = evaluate (ys @ [y]) C

---
**evaluate_switch**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate (y#ys) C = evaluate (ys@[y]) C

---
**evaluate_split**

&nbsp;&nbsp;&nbsp;&nbsp;xs≠[ ] ⟹ ys ≠ [ ] ⟹ evaluate (xs@ys) C = evaluate xs C ∪<sub>p</sub> evaluate ys C

---
**evaluate_switch2**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate (yss@yse) C = evaluate (yse@yss) C

---
**eval_perm**

&nbsp;&nbsp;&nbsp;&nbsp;a#ys' ∈ set (permutations ys) ⟹ evaluate (a#ys') C = evaluate ys C

---
**perm_eval**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set (permutations ys) ⟹ evaluate xs C = evaluate ys C

---
**perm_prop**

&nbsp;&nbsp;&nbsp;&nbsp;[t. t ← xs, ¬p t] @ [t. t ← xs, p t] ∈ set (permutations xs)

---
**size_prop**

&nbsp;&nbsp;&nbsp;&nbsp;size ([t. t ← xs, ¬p t] @ [t. t ← xs, p t]) = size xs

---
**evaluate_split1**

&nbsp;&nbsp;&nbsp;&nbsp;size (xs@ys) ≠ 1 ⟹ evaluate xs C ∪<sub>p</sub> evaluate ys C = evaluate (xs@ys) C

---
**evaluate_split2**

&nbsp;&nbsp;&nbsp;&nbsp;size xs ≠1 ⟹ evaluate xs C  = evaluate [t. t ← xs, t =x] C ∪<sub>p</sub> evaluate [t. t ← xs, t≠x] C

---
**size_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;size [t. t←a, t=x] + size [t. t←a, t≠x] = size a

---
**evaluate_prop**

&nbsp;&nbsp;&nbsp;&nbsp;size xs = 1 ⟹ ∀t ∈ set xs. t=x ⟹ evaluate xs = evaluate [x]

---
**evaluate_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;size xs > 1 ⟹ ∀t ∈ set xs. t=x ⟹ evaluate xs C = evaluate [x] C ∪<sub>p</sub> evaluate [x] C

---
**equal_eval**

&nbsp;&nbsp;&nbsp;&nbsp;equal_cnf a b ⟹ evaluate a C = evaluate b C

---
**eval_simp**

&nbsp;&nbsp;&nbsp;&nbsp;∀C. evaluate a C = evaluate b C ⟹ evaluate a = evaluate b

---
**equal_eval2**

&nbsp;&nbsp;&nbsp;&nbsp;equal_cnf a b ⟹ evaluate a = evaluate b

---
**eq_reflexive**

&nbsp;&nbsp;&nbsp;&nbsp;equal xs xs

---
**comp_prop**

&nbsp;&nbsp;&nbsp;&nbsp;tr ∈ set (xs ;<sub>c</sub> ys) ⟹ ∃x y. x ∈ set xs ∧ y ∈ set ys ∧ x@y = tr

---
**comp_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ set xs ⟹ y ∈ set ys ⟹ x@y ∈ set (xs ;<sub>c</sub> ys)

---
**choice_prop**

&nbsp;&nbsp;&nbsp;&nbsp;tr ∈ set (xs ∪<sub>c</sub> ys) ⟹ (tr ∈ set xs ∨ tr ∈ set ys)

---
**same_traces_size_equal**

&nbsp;&nbsp;&nbsp;&nbsp;∀tr ∈ set xs. tr ∈ set ys ⟹ ∀tr ∈ set ys. tr ∈ set xs ⟹ size xs = size ys ⟹ equal_cnf xs ys

---
**same_traces_size_equal2**

&nbsp;&nbsp;&nbsp;&nbsp;size xs = size ys ⟹ equal_cnf xs ys ⟹ ∀tr ∈ set xs. tr ∈ set ys

---
**same_traces_size_equal3**

&nbsp;&nbsp;&nbsp;&nbsp;size xs = size ys ⟹ equal_cnf xs ys ⟹ ∀tr ∈ set ys. tr ∈ set xs

---
**comp_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;∃q w. q ∈ set a ∧ w ∈ set b ∧ tr = q @ w ∧ q ≠ [ ] ∧ w ≠ [ ] ⟹ tr ∈ set (a ;<sub>c</sub> b)

---
**choice_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;∃q. (q ∈ set a ∨ q ∈ set b) ∧ tr = q ∧ q ≠ [ ] ⟹ tr ∈ set (a ∪<sub>c</sub> b)

---
&nbsp;&nbsp;&nbsp;&nbsp;size (a ∪<sub>c</sub> b) = size (a) + size (b)

---
**comp_size**

&nbsp;&nbsp;&nbsp;&nbsp;x ≠ [ ] ⟹ length (((xx # x) # xs) ;<sub>c</sub> b) = length ((x # xs) ;<sub>c</sub> b)

---
**comp_size2**

&nbsp;&nbsp;&nbsp;&nbsp;size ([[a]] ;<sub>c</sub> b) = size b

---
**comp_size3**

&nbsp;&nbsp;&nbsp;&nbsp;size (a ;<sub>c</sub> b) = size a * size b

---
**feas_prop**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible xs ⟹ is_feasible (Concat xs C)

---
**feas_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible (evaluate [ ] C)

---
**feas_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible (evaluate [[ ]] C)

---
**feas_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible x ⟹ is_feasible (evaluate [[x]] C)

---
**eval_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ evaluate [x # xs] C = evaluate [[x]] C ; evaluate [xs] C

---
**feas_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible xs ⟹ is_feasible (evaluate [xs] C)

---
**feas_prop7**

&nbsp;&nbsp;&nbsp;&nbsp;∀bb ∈ set b. all_feasible bb ⟹ is_feasible (evaluate b C)

---
**cnf_state_prop**

&nbsp;&nbsp;&nbsp;&nbsp;complete_cnf_state (x#b) ⊆ C ⟹ complete_cnf_state b ⊆ C

---
**cnf_state_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;complete_state xs ⊆ C ⟹ S (evaluate [xs] C) ⊆ C

---
**cnf_state_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;complete_cnf_state xs ⊆ C ⟹ S (evaluate xs C) ⊆ C

---
**skip_left_neutral**

&nbsp;&nbsp;&nbsp;&nbsp;complete_cnf_state b ⊆ C ⟹ Skip C ; evaluate b C ≡<sub>p</sub> evaluate b C

---
**skip_right_neutral**

&nbsp;&nbsp;&nbsp;&nbsp;∀bb ∈ set b. all_feasible bb ⟹ complete_cnf_state b ⊆ C ⟹ evaluate b C ; Skip C ≡<sub>p</sub> evaluate b C

---
**feas_prop8**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible x ⟹ all_feasible b1 ⟹ all_feasible (x @ b1)

---
**state_prop**

&nbsp;&nbsp;&nbsp;&nbsp;y ∈set ys ⟹ complete_state (ys) = complete_state (y#ys)

---
**state_prop8**

&nbsp;&nbsp;&nbsp;&nbsp;set xs ⊆ set ys ⟹ complete_state xs ⊆ complete_state ys

---
**state_prop9**

&nbsp;&nbsp;&nbsp;&nbsp;complete_cnf_state (xs # [ys]) = complete_state (xs @ ys)

---
**compose_equiv**

&nbsp;&nbsp;&nbsp;&nbsp;complete_cnf_state (x#b) ⊆ C ⟹ all_feasible x ⟹ ∀bb ∈ set b. all_feasible bb ⟹ evaluate [x] C ; evaluate b C ≡<sub>p</sub> evaluate ([x] ;<sub>c</sub> b) C

---
**state_prop10**

&nbsp;&nbsp;&nbsp;&nbsp;complete_cnf_state (a) ⊆ complete_cnf_state (a @ b)

---
**state_prop11**

&nbsp;&nbsp;&nbsp;&nbsp;complete_cnf_state (b) ⊆ complete_cnf_state (a @ b)

---
**state_prop12**

&nbsp;&nbsp;&nbsp;&nbsp;set xs ⊆ set ys ⟹ complete_cnf_state xs ⊆ complete_cnf_state ys

---
**eval_choice**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate xs C ∪<sub>p</sub> evaluate ys C ≡<sub>p</sub> evaluate (xs ∪<sub>c</sub> ys) C

---
**comp_choice**

&nbsp;&nbsp;&nbsp;&nbsp;([x] ;<sub>c</sub> b) ∪<sub>c</sub> (a' ;<sub>c</sub> b) = (x#a') ;<sub>c</sub> b

---
**normal_prop15**

&nbsp;&nbsp;&nbsp;&nbsp;set a = set b ⟹ normal_of a B = normal_of b B

---
**normal_prop16**

&nbsp;&nbsp;&nbsp;&nbsp;set a ⊆ set b ⟹ normal_of b B → normal_of a B

---
**non_empty_is_smaller**

&nbsp;&nbsp;&nbsp;&nbsp;set (non_empty xs) ⊆ set xs

---
**normal_prop17**

&nbsp;&nbsp;&nbsp;&nbsp;normal_of a B ⟹ normal_of (non_empty a) B

---
**normal_prop17_5**

&nbsp;&nbsp;&nbsp;&nbsp;normal_of xs B ⟹ normal_of [x] B ⟹ normal_of (x#xs) B

---
**normal_prop18**

&nbsp;&nbsp;&nbsp;&nbsp;normal_of a B ⟹ normal_of b B ⟹ normal_of (a ∪<sub>c</sub> b) B

---
**basic_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;basic (map ((@) x) bs) ⊆ basic [x] ∪ basic bs

---
**normal_prop19**

&nbsp;&nbsp;&nbsp;&nbsp;normal_of [x] B ⟹ normal_of b B ⟹ normal_of [x@ys. ys ← b] B

---
**normal_prop20**

&nbsp;&nbsp;&nbsp;&nbsp;normal_of a B ⟹ normal_of b B ⟹ normal_of (a ;<sub>c</sub> b) B

---
**state_prop13**

&nbsp;&nbsp;&nbsp;&nbsp;normal_of [x] B ⟹ complete_cnf_state [x] ⊆ complete_state (set_to_list B)

---
**state_prop14**

&nbsp;&nbsp;&nbsp;&nbsp;normal_of xs B ⟹ complete_cnf_state xs ⊆ complete_state (set_to_list B)

---
**feas_prop9**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible (set_to_list B) ⟹ normal_of xs B ⟹ ∀tr ∈ set xs. all_feasible tr

---
**comp_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible x ⟹ all_feasible y ⟹ complete_state x ⊆ C ⟹ complete_state y ⊆ C ⟹ evaluate ([x] ;<sub>c</sub> [y]) C ≡<sub>p</sub> evaluate [x] C ; evaluate [y] C

---
&nbsp;&nbsp;&nbsp;&nbsp;complete_cnf_state (x#ys) ⊆ C ⟹ ∀tr∈set (x#ys). all_feasible tr ⟹ evaluate ([x] ;<sub>c</sub> ys) C ≡<sub>p</sub> evaluate ([x]) C ; evaluate (ys) C

---
**civilized_thm1**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible (set_to_list B) ⟹ S p ⊆ C ⟹ civilized_n p B n ⟹ ∃(y::'a CNF). evaluate y C ≡<sub>p</sub> p ∧ normal_of y B

---
**set_to_list_prop**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ y ∉ F ⟹ count_list (set_to_list F) y = 0

---
**set_to_list_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ count_list (set_to_list (F - {y})) y = 0

---
**set_to_list_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;count_list (set_to_list {y}) y = 1

---
**set_to_list_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;count_list (set_to_list {}) y = 0

---
**set_to_list_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ y ∉ F ⟹ set_to_list (insert y F) ∈ set (permutations (y # set_to_list F))

---
&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ count_list (set_to_list (insert x F)) x = 1

---
**set_to_list_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ x ∉ F ⟹ count_list (set_to_list (insert x F)) y = count_list (x#set_to_list F) y

---
**set_to_list_prop7**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ x ∉ F ⟹ x ≠ y ⟹ count_list (set_to_list (insert x F)) y = count_list (set_to_list F) y

---
**set_to_list_prop8**

&nbsp;&nbsp;&nbsp;&nbsp;x=y ⟹ count_list (yst@x#ynd) y = count_list (yst@ynd) y + 1

---
**set_to_list_prop9**

&nbsp;&nbsp;&nbsp;&nbsp;x≠y ⟹ count_list (yst@x#ynd) y = count_list (yst@ynd) y

---
**set_to_list_prop10**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set (permutations ys) ⟹ count_list xs = count_list ys

---
**set_to_list_prop11**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ count_list (set_to_list F) x < 1

---
**set_to_list_prop12**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ x ∈ F ⟹ count_list (set_to_list F) x = 1

---
**set_to_list_prop13**

&nbsp;&nbsp;&nbsp;&nbsp;count_list xs x = 1 ⟹ count_list (set_to_list (set xs)) x = 1

---
**set_to_list_prop14**

&nbsp;&nbsp;&nbsp;&nbsp;finite F ⟹ complete_state (set_to_list (insert y F)) = complete_state (set_to_list (F)) ∪ S y

---
**set_to_list_prop15**

&nbsp;&nbsp;&nbsp;&nbsp;civilized p B ⟹ S p ⊆ complete_state (set_to_list B)

---
**civilized_thm2**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible (set_to_list B) ⟹ civilized p B ⟹ ∃(y::'a CNF). evaluate y (complete_state (set_to_list B)) ≡<sub>p</sub> p ∧ normal_of y B

---
**fail_is_civilized**

&nbsp;&nbsp;&nbsp;&nbsp;finite B ⟹ civilized (Fail{}) B

---
**skip_is_civilized**

&nbsp;&nbsp;&nbsp;&nbsp;finite B ⟹ civilized (Skip (complete_state (set_to_list B))) B

---
**civilized_thm3**

&nbsp;&nbsp;&nbsp;&nbsp;∃(y::'a CNF). evaluate y (complete_state (set_to_list B)) = p ∧ normal_of y B ⟹ civilized p B

---
**composition_cnf_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;[[x]] ;<sub>c</sub> xs = [x#ys. ys ← xs]

---
**composition_cnf_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;[y#ys] ;<sub>c</sub> xs = [( y#ys)@t. t ← xs]

---
**non2_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty x = [ ] ⟹ non_empty2 (x # xs) = non_empty2 xs

---
**non2_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty x ≠ [ ] ⟹ non_empty2 (x # xs) = non_empty x # non_empty2 xs

---
**non2_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty2 (xs @ ys) = non_empty2 xs @ non_empty2 ys

---
**non2_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;size (non_empty2 xs) < size xs

---
**non2_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty2 (x#xs) = x#xs ⟹ non_empty2 xs = xs

---
**non2_prop5_5**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty2 [x] = [x] ⟹ ∀path∈set x. path ≠ [ ]

---
**non2_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty2 xs = xs ⟹ ∀prog ∈ set xs. prog ≠ [ ] ∧ (∀path ∈ set prog. path ≠ [ ])

---
**non_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty xs = xs ⟹ ∀path ∈ set xs. path ≠ [ ]

---
**non2_prop7**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty2 xs = xs ⟹ x ∈ set xs ⟹ non_empty x = x

---
**non2_idem**

&nbsp;&nbsp;&nbsp;&nbsp;non_empty2 xs = non_empty2 (non_empty2 xs)

---
**inter_head**

&nbsp;&nbsp;&nbsp;&nbsp;p ∈ set ((x#xs) ⫴ (y#ys)) ⟹ hd p = x ∨ hd p = y

---
**count_prop**

&nbsp;&nbsp;&nbsp;&nbsp;count_list (map ((#) x) xs) (x#p) = count_list xs p

---
**count_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;x≠y ⟹ count_list (map ((#) x) xs) (y#p) = 0

---
**interleave_non_empty**

&nbsp;&nbsp;&nbsp;&nbsp;p ∈ set ((x#xs) ⫴ (y#ys)) ⟹ p ≠ [ ]

---
**inter2**

&nbsp;&nbsp;&nbsp;&nbsp;count_list (ys ⫴ xs) p = count_list (xs ⫴ ys) p

---
**inter_perm**

&nbsp;&nbsp;&nbsp;&nbsp;ys ⫴ xs ∈ set (permutations (xs ⫴ ys))

---
**t1**

&nbsp;&nbsp;&nbsp;&nbsp;size xs = size ys ⟹ ∀t∈set (zip xs ys). fst t ∈ set (permutations (snd t)) ⟹ concat xs ∈ set (permutations (concat ys))

---
**t15**

&nbsp;&nbsp;&nbsp;&nbsp;size xs = size ys ⟹ ∃xs'. xs' ∈ set (permutations xs) ∧ (∀t∈set (zip xs' ys). fst t ∈ set (permutations (snd t))) ⟹ concat xs ∈ set (permutations (concat ys))

---
**t2**

&nbsp;&nbsp;&nbsp;&nbsp;size [f x y. x ← xs, y ← ys] = size xs * size ys

---
**t3**

&nbsp;&nbsp;&nbsp;&nbsp;size [path_m ⫴ path_n. path_m ← xs, path_n ← ys] = size [path_m ⫴ path_n. path_m ← ys, path_n ← xs]

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

&nbsp;&nbsp;&nbsp;&nbsp;x_ind<size xs ⟹ y_ind<size ys ⟹ [path_m ⫴ path_n. path_m ← xs, path_n ← ys] ! ((x_ind* (size ys))+y_ind) = (xs ! x_ind) ⫴ (ys ! y_ind)

---
&nbsp;&nbsp;&nbsp;&nbsp;x_ind < size xs ⟹ y_ind < size ys ⟹ [path_m ⫴ path_n. path_m ← xs, path_n ← ys] ! ((x_ind* (size ys))+y_ind) = [path_m ⫴ path_n. path_m ← ys, path_n ← xs] ! ((y_ind* (size xs))+x_ind)

---
**all_elements_have_permutation**

&nbsp;&nbsp;&nbsp;&nbsp;x_ind < size xs ⟹ y_ind < size ys ⟹ [path_m ⫴ path_n. path_m ← xs, path_n ← ys] ! ((x_ind* (size ys))+y_ind) ∈ set (permutations ([path_m ⫴ path_n. path_m ← ys, path_n ← xs] ! ((y_ind* (size xs))+x_ind)))

---
**perm_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set (permutations xs') ⟹ ys  ∈ set (permutations ys') ⟹ xs@ys ∈ set (permutations (xs'@ys'))

---
**is_perm**

&nbsp;&nbsp;&nbsp;&nbsp;size xy = sx * sy ⟹ [xy ! ((x_ind*sy)+y_ind). x_ind ← [0..<sx], y_ind ← [0..<sy]] ∈ set (permutations xy)

---
**is_perm2**

&nbsp;&nbsp;&nbsp;&nbsp;size xy = size xs * size ys ⟹ [xy ! ((x_ind*(size ys))+y_ind). x_ind ← [0..<size xs], y_ind ← [0..<size ys]] ∈ set (permutations xy)

---
**index_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;i < size xs * size ys ⟹ concat (map (λx. map (f x) ys) xs) ! i = f (xs ! (i div length ys)) (ys ! (i mod length ys))

---
**index_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;concat (map (λx. map (f x) ys) xs) = [f (xs ! (i div length ys)) (ys ! (i mod length ys)). i ← [0..<size xs * size ys]]

---
**perm_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;[ ] ∈ set (permutations xy) ⟹ xy = [ ]

---
**perm_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;concat (map (λy. map (λx. f x y) [x]) (ys)) @ concat (map (λy. map (λx. f x y) xs) (ys)) ∈ set (permutations (concat (map (λy. map (λx. f x y) (x # xs)) (ys))))

---
**perm_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;[f x y. x ← xs, y ← ys] ∈ set (permutations xy) ⟹ [f x y. y ← ys, x ← xs] ∈ set (permutations xy)

---
**is_perm4**

&nbsp;&nbsp;&nbsp;&nbsp;size xy = sx * sy ⟹ [xy ! ((x_ind*sy)+y_ind). y_ind ← [0..<sy], x_ind ← [0..<sx]] ∈ set (permutations xy)

---
**perm_exists**

&nbsp;&nbsp;&nbsp;&nbsp;xy = [path_m ⫴ path_n. path_m ← xs, path_n ← ys] ⟹ yx = [path_m ⫴ path_n. path_m ← ys, path_n ← xs] ⟹ ∃xy'. xy' ∈ set (permutations xy) ∧ (∀t∈set (zip xy' yx). fst t ∈ set (permutations (snd t)))

---
**is_permutation**

&nbsp;&nbsp;&nbsp;&nbsp;(xs ∥ ys) ∈ set (permutations (ys ∥ xs))

---
**t4**

&nbsp;&nbsp;&nbsp;&nbsp;size (xs ∥ ys) = size (ys ∥ xs)

---
**inter_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ interleave xs ys ≠ [ ]

---
**perm_is_equal**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set (permutations ys) ⟹ evaluate xs = evaluate ys

---
&nbsp;&nbsp;&nbsp;&nbsp;evaluate (xs ∥ ys) = evaluate (ys ∥ xs)

---
## CNF_concurrency.thy

&nbsp;&nbsp;&nbsp;&nbsp;(a@b)∥c =(a∥c)@(b∥c)

---
**fact_eq**

&nbsp;&nbsp;&nbsp;&nbsp;factorial n = fact n

---
**factorial_mod_product**

&nbsp;&nbsp;&nbsp;&nbsp;factorial (a + b) mod (factorial a * factorial b) = (0::nat)

---
**factorial_bound**

&nbsp;&nbsp;&nbsp;&nbsp;factorial n > 0

---
**simp_div**

&nbsp;&nbsp;&nbsp;&nbsp;a mod b = 0 ⟹ c mod b = 0 ⟹ (a::nat) div b + c div b = (a + c) div b

---
**exits_mulit**

&nbsp;&nbsp;&nbsp;&nbsp;∃t::nat. n*t=m ⟹ m mod n = 0

---
&nbsp;&nbsp;&nbsp;&nbsp;nmb_interleavings_pre (nmb_interleavings_pre x y) z = nmb_interleavings_pre x (nmb_interleavings_pre y z)

---
**number_interleav**

&nbsp;&nbsp;&nbsp;&nbsp;length (xs ⫴ ys) = nmb_interleavings xs ys

---
**monoton_fact**

&nbsp;&nbsp;&nbsp;&nbsp;a < b ⟹ factorial a < factorial b

---
**interleave_size**

&nbsp;&nbsp;&nbsp;&nbsp;size xs * size ys < size (xs ⫴ ys)

---
**list_comp_size**

&nbsp;&nbsp;&nbsp;&nbsp;size [f path_m path_n. path_m ← xs, path_n ← ys] > size xs * size ys

---
**interleav_lower_bound**

&nbsp;&nbsp;&nbsp;&nbsp;size (xs ⫴ ys) > 1

---
**concat_prop**

&nbsp;&nbsp;&nbsp;&nbsp;∀x ∈ set xs. size x > 1 ⟹ size (concat xs) > size xs

---
**conc_size**

&nbsp;&nbsp;&nbsp;&nbsp;size xs * size ys < size (xs ∥ ys)

---
**size_one1**

&nbsp;&nbsp;&nbsp;&nbsp;size (xs ∥ ys) = 1 ⟹ size xs = 1

---
**size_one2**

&nbsp;&nbsp;&nbsp;&nbsp;size (xs ∥ ys) = 1 ⟹ size ys = 1

---
**sum_1**

&nbsp;&nbsp;&nbsp;&nbsp;size (concat xs) = sum [size x. x←xs]

---
**path_decomp**

&nbsp;&nbsp;&nbsp;&nbsp;path ∈ set (p ∥ q) ⟹ ∃path_p path_q. path_p ∈ set p ∧ path_q ∈ set q ∧ path ∈ set (path_p ⫴ path_q)

---
**path_decomp2**

&nbsp;&nbsp;&nbsp;&nbsp;path_p ∈ set p ⟹ path_q ∈ set q ⟹ path ∈ set (path_p ⫴ path_q) ⟹ path ∈ set (p ∥ q)

---
**inter_leav1**

&nbsp;&nbsp;&nbsp;&nbsp;(p#path) ∈ set ((x#xs) ⫴ (y#ys)) ⟹ ((p=x) ∧ path ∈ set (xs ⫴ (y#ys))) ∨ ((p=y) ∧ path ∈ set ((x#xs) ⫴ (ys)))

---
**inter_leav2**

&nbsp;&nbsp;&nbsp;&nbsp;((p=y) ∧ path ∈ set ((x#xs) ⫴ (ys))) ⟹ (p#path) ∈ set ((x#xs) ⫴ (y#ys))

---
**inter_leav3**

&nbsp;&nbsp;&nbsp;&nbsp;((p=x) ∧ path ∈ set (xs ⫴ (y#ys))) ⟹ (p#path) ∈ set ((x#xs) ⫴ (y#ys))

---
**conc_lem1**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs ∥ ys) = ⋃ {set (path_x ⫴ path_y) |path_x path_y. path_x ∈ set xs ∧ path_y ∈ set ys}

---
&nbsp;&nbsp;&nbsp;&nbsp;set ((x#xs) ∥ ys) = set ([x]∥ys) ∪ set (xs∥ys)

---
**assoc_1**

&nbsp;&nbsp;&nbsp;&nbsp;set (([x] ∥ [y]) ∥ [z]) ⊆ set ([x] ∥ ([y] ∥ [z]))

---
**assoc_2**

&nbsp;&nbsp;&nbsp;&nbsp;set ([x] ∥ ([y] ∥ [z])) ⊆ set (([x] ∥ [y]) ∥ [z])

---
**assoc_3**

&nbsp;&nbsp;&nbsp;&nbsp;set (([x] ∥ [y]) ∥ [z]) ⊆ set (((x#xs) ∥ (y#ys)) ∥ (z#zs))

---
**assoc_4**

&nbsp;&nbsp;&nbsp;&nbsp;set ([x] ∥ ([y] ∥ [z])) ⊆ set ((x#xs) ∥ ((y#ys) ∥ (z#zs)))

---
**assoc_5**

&nbsp;&nbsp;&nbsp;&nbsp;set xs = set xs' ⟹ set ys = set ys' ⟹ set (xs ∥ ys) = set (xs' ∥ ys')

---
**assoc_6**

&nbsp;&nbsp;&nbsp;&nbsp;y ∈ set ys ⟹ x ∈ set xs ⟹ set ((x#xs) ∥ (y#ys)) =  set ((xs) ∥ (ys))

---
**assoc_7**

&nbsp;&nbsp;&nbsp;&nbsp;set ((xs ∥ ys) ∥ zs) ⊆ set (xs ∥ (ys ∥ zs))

---
**assoc_8**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs ∥ (ys ∥ zs)) ⊆ set ((xs ∥ ys) ∥ zs)

---
**assoc_9**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs ∥ (ys ∥ zs)) = set ((xs ∥ ys) ∥ zs)

---
**inter_size**

&nbsp;&nbsp;&nbsp;&nbsp;size (x ⫴ y) > 0" apply (cases "x=[ ]

---
**inter_size2**

&nbsp;&nbsp;&nbsp;&nbsp;size (x ⫴ y) = 1 ⟹ size x = 0 ∨ size y = 0

---
**inter_size3**

&nbsp;&nbsp;&nbsp;&nbsp;size x = 0 ∨ size y = 0 ⟹ size (x ⫴ y) = 1

---
**interleaving_lemma**

&nbsp;&nbsp;&nbsp;&nbsp;size ([x] ∥ [y]) =  nmb_interleavings_pre (size x) (size y)

---
**inter_size4**

&nbsp;&nbsp;&nbsp;&nbsp;size (xs ∥ ys) = 1 ⟹ size xs = 1 ∨ size ys = 1

---
**conc_prop**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∥ [[ ]] = xs

---
**conc_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;[[ ]] ∥ xs = xs

---
**assoc_10**

&nbsp;&nbsp;&nbsp;&nbsp;size (xs ∥ (ys ∥ zs)) = 1 ⟹ size ((xs ∥ ys) ∥ zs) = 1

---
**assoc_11**

&nbsp;&nbsp;&nbsp;&nbsp;size ((xs ∥ ys) ∥ zs) = 1 ⟹ size (xs ∥ (ys ∥ zs)) = 1

---
**assoc_12**

&nbsp;&nbsp;&nbsp;&nbsp;size (xs ∥ (ys ∥ zs)) = 1 ≡ size ((xs ∥ ys) ∥ zs) = 1

---
**assoc_cnf1**

&nbsp;&nbsp;&nbsp;&nbsp;equal_cnf ((xs ∥ ys) ∥ zs)  (xs ∥ (ys ∥ zs))

---
**assoc_cnf**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate ((xs ∥ ys) ∥ zs) = evaluate (xs ∥ (ys ∥ zs))

---
**cnf_prop**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ evaluate [x#xs] C = x ; (evaluate [xs] C)

---
**cnf_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ evaluate [xs@[x]] C = (evaluate [xs] C) ; x

---
**restrict_cnf1**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ evaluate ([x] /<sub>c</sub> C) D = (evaluate [x] D) /<sub>p</sub> C

---
**restr_distrib**

&nbsp;&nbsp;&nbsp;&nbsp;a /<sub>p</sub> C ∪<sub>p</sub> b /<sub>p</sub> C = (a ∪<sub>p</sub> b) /<sub>p</sub> C

---
**restrict_cnf**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ evaluate (xs /<sub>c</sub> C) D = (evaluate xs D) /<sub>p</sub> C

---
**corestrict_cnf1**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ evaluate ([x] ∖<sub>c</sub> C) D = (evaluate [x] D) ∖<sub>p</sub> C

---
**corestrict_cnf**

&nbsp;&nbsp;&nbsp;&nbsp;D ⊆ C ⟹ evaluate (xs ∖<sub>c</sub> C) D= (evaluate xs D) ∖<sub>p</sub> C

---
**conc_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs ∥ ys) ⊆ set (xs ∥ (y#ys))

---
**conc_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs ∥ ys) ⊆ set (xs ∥ (ys ∪<sub>c</sub> zs))

---
**conc_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs ∥ (ys ∪<sub>c</sub> zs)) = set (xs ∥ (zs ∪<sub>c</sub> ys))

---
**conc_choice1_1**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs ∥ (ys ∪<sub>c</sub> zs)) = set ((xs ∥ ys) ∪<sub>c</sub> (xs ∥ zs))

---
**choice_size1**

&nbsp;&nbsp;&nbsp;&nbsp;size (xs ∥ (ys ∪<sub>c</sub> zs)) = 1 ⟹ size ((xs ∥ ys) ∪<sub>c</sub> (xs ∥ zs)) = 1

---
**choice_size2**

&nbsp;&nbsp;&nbsp;&nbsp;size ((xs ∥ ys) ∪<sub>c</sub> (xs ∥ zs)) = 1 ⟹ size (xs ∥ (ys ∪<sub>c</sub> zs)) = 1

---
**Conc_choice1_1**

&nbsp;&nbsp;&nbsp;&nbsp;equal_cnf ((xs ∥ ys) ∪<sub>c</sub> (xs ∥ zs)) (xs ∥ (ys ∪<sub>c</sub> zs))

---
**Conc_choice1_**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate ((xs ∥ ys) ∪<sub>c</sub> (xs ∥ zs)) = evaluate (xs ∥ (ys ∪<sub>c</sub> zs))

---
**conc_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs ∥ ys) ⊆ set ((x#xs) ∥ ys)

---
**conc_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs ∥ ys) ⊆ set ((xs ∪<sub>c</sub> zs) ∥ ys)

---
**conc_prop7**

&nbsp;&nbsp;&nbsp;&nbsp;set ((zs ∪<sub>c</sub> xs) ∥ ys) = set ((xs ∪<sub>c</sub> zs) ∥ ys)

---
**conc_choice2_1**

&nbsp;&nbsp;&nbsp;&nbsp;set ((xs ∪<sub>c</sub> ys) ∥ zs) = set ((xs ∥ zs) ∪<sub>c</sub> (ys ∥ zs))

---
**choice_size3**

&nbsp;&nbsp;&nbsp;&nbsp;size ((xs ∪<sub>c</sub> ys) ∥ zs) = 1 ⟹ size ((xs ∥ zs) ∪<sub>c</sub> (ys ∥ zs)) = 1

---
**choice_size4**

&nbsp;&nbsp;&nbsp;&nbsp;size ((xs ∥ zs) ∪<sub>c</sub> (ys ∥ zs)) = 1 ⟹ size ((xs ∪<sub>c</sub> ys) ∥ zs) = 1

---
**Conc_choice2_1**

&nbsp;&nbsp;&nbsp;&nbsp;equal_cnf ((xs ∥ zs) ∪<sub>c</sub> (ys ∥ zs)) ((xs ∪<sub>c</sub> ys) ∥ zs)

---
**Conc_choice2_**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate ((xs ∥ zs) ∪<sub>c</sub> (ys ∥ zs)) = evaluate ((xs ∪<sub>c</sub> ys) ∥ zs)

---
**eval_specialize**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate ys C ⊆<sub>p</sub> evaluate (y # ys) C

---
**eval_specialize2**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate [y] C ⊆<sub>p</sub> evaluate (y # ys) C

---
**eval_specialize3**

&nbsp;&nbsp;&nbsp;&nbsp;set xs ⊆ set [y] ⟹ evaluate xs C ⊆<sub>p</sub> evaluate [y] C

---
**eval_specialize4**

&nbsp;&nbsp;&nbsp;&nbsp;set [x] ⊆ set ys ⟹ evaluate [x] C ⊆<sub>p</sub> evaluate ys C

---
**eval_specialize5**

&nbsp;&nbsp;&nbsp;&nbsp;size xs > 1 ⟹ equal_cnf xs zs ⟹ evaluate xs C = evaluate [ ] C ∪<sub>p</sub> evaluate zs C

---
**eval_specialize6**

&nbsp;&nbsp;&nbsp;&nbsp;size (ys @ zs) > 1 ⟹ evaluate ys C ∪<sub>p</sub> evaluate zs C = evaluate (ys ∪<sub>c</sub> zs) C

---
**eval_specialize7**

&nbsp;&nbsp;&nbsp;&nbsp;size xs ≠ 1 ⟹ equal_cnf xs (ys ∪<sub>c</sub> zs) ⟹ evaluate xs C = evaluate ys C ∪<sub>p</sub> evaluate zs C

---
**eval_specialize8**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate [x. x ← xs, f x] C ⊆<sub>p</sub> evaluate xs C

---
**eval_specialize9**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate [x. x ← (x#xx#xs), f x] C ∪<sub>p</sub> evaluate [x. x ← x#xx#xs, ¬f x] C = (evaluate [x] C ∪<sub>p</sub> evaluate [xx] C) ∪<sub>p</sub> (evaluate [x. x ← (xs), f x] C ∪<sub>p</sub> evaluate [x. x ← xs, ¬f x] C)

---
**eval_specialize10**

&nbsp;&nbsp;&nbsp;&nbsp;(evaluate [x] C ∪<sub>p</sub> evaluate [xx] C) ∪<sub>p</sub> (evaluate [x. x ← (xs), f x] C ∪<sub>p</sub> evaluate [x. x ← xs, ¬f x] C) = (evaluate [x] C ∪<sub>p</sub> evaluate [xx] C) ∪<sub>p</sub> (evaluate xs C)

---
**eval_specialize11**

&nbsp;&nbsp;&nbsp;&nbsp;size xs > 1 ⟹ evaluate [x. x ← xs, f x] C ∪<sub>p</sub> evaluate [x. x ← xs, ¬f x] C = evaluate xs C

---
**eval_specialize12**

&nbsp;&nbsp;&nbsp;&nbsp;set xs ⊆ set ys ⟹ evaluate xs C⊆<sub>p</sub> evaluate ys C

---
**subset1**

&nbsp;&nbsp;&nbsp;&nbsp;set (p ;<sub>c</sub> xs) ⊆ set (p ;<sub>c</sub> (x#xs))

---
**subset2**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs ;<sub>c</sub> p) ⊆ set ((x#xs) ;<sub>c</sub> p)

---
**subset3**

&nbsp;&nbsp;&nbsp;&nbsp;set (p ∪<sub>c</sub> xs) ⊆ set (p ∪<sub>c</sub> (x#xs))

---
**subset4**

&nbsp;&nbsp;&nbsp;&nbsp;set (xs ∪<sub>c</sub> p) ⊆ set ((x#xs) ∪<sub>c</sub> p)

---
**subset5**

&nbsp;&nbsp;&nbsp;&nbsp;set q ⊆ set q' ⟹ set (p ;<sub>c</sub> q) ⊆ set (p ;<sub>c</sub> q')

---
**subset6**

&nbsp;&nbsp;&nbsp;&nbsp;set q ⊆ set q' ⟹ set (q ;<sub>c</sub> p) ⊆ set (q' ;<sub>c</sub> p)

---
**subset7**

&nbsp;&nbsp;&nbsp;&nbsp;set q ⊆ set q' ⟹ set (p ∪<sub>c</sub> q) ⊆ set (p ∪<sub>c</sub> q')

---
**subset8**

&nbsp;&nbsp;&nbsp;&nbsp;set q ⊆ set q' ⟹ set (q ∪<sub>c</sub> p) ⊆ set (q' ∪<sub>c</sub> p)

---
**subset9**

&nbsp;&nbsp;&nbsp;&nbsp;set q ⊆ set q' ⟹ set (p ∥ q) ⊆ set (p ∥ q')

---
**subset10**

&nbsp;&nbsp;&nbsp;&nbsp;set q ⊆ set q' ⟹ set (q ∥ p) ⊆ set (q' ∥ p)

---
**interleav_prop**

&nbsp;&nbsp;&nbsp;&nbsp;ps @ rs ∈ set (ps ⫴ rs)

---
**prop5**

&nbsp;&nbsp;&nbsp;&nbsp;set (map (λxs. xs @ [p]) (ps ⫴ (qs @ [q]))) = {tr @ [p] |tr. tr ∈ set (ps ⫴ (qs @ [q]))}

---
**prop6**

&nbsp;&nbsp;&nbsp;&nbsp;set (map (λxs. xs @ [q]) ((ps @ [p]) ⫴ qs )) = {tr @ [q] |tr. tr ∈ set ((ps @ [p]) ⫴ qs)}

---
**prop3_1**

&nbsp;&nbsp;&nbsp;&nbsp;[x] ⫴ ys = insert_all x ys

---
**prop3_2**

&nbsp;&nbsp;&nbsp;&nbsp;ys ⫴ [x] = rev (insert_all x ys)

---
**prop3_3**

&nbsp;&nbsp;&nbsp;&nbsp;set ([x] ⫴ (y#ys)) = {x#y#ys} ∪ {y#x#ys} ∪ ((#) y) ` set ([x] ⫴ ys)

---
**prop3_4**

&nbsp;&nbsp;&nbsp;&nbsp;set ([x] ⫴ (ys@[y])) = {ys@[x,y]} ∪ {ys@[y,x]} ∪ (λtr. tr@[y]) ` set ([x] ⫴ ys)

---
**prop3_5**

&nbsp;&nbsp;&nbsp;&nbsp;set ([x] ⫴ rev (y#ys)) = {(rev ys)@[x,y]} ∪ {(rev ys)@[y,x]} ∪ (λtr. tr@[y]) ` set ([x] ⫴ (rev ys))

---
**prop3_6**

&nbsp;&nbsp;&nbsp;&nbsp;{rev tr |tr. tr ∈ set ([x] ⫴ (ys))} = set ([x] ⫴ rev ys)

---
**prop3_7**

&nbsp;&nbsp;&nbsp;&nbsp;rev ` set ([x] ⫴ ys) = set ([x] ⫴ rev ys)

---
**prop3_8**

&nbsp;&nbsp;&nbsp;&nbsp;(λtr. tr @ [y]) ` set ([x] ⫴ ys) ⊆ set ([x] ⫴ (ys @ [y]))

---
**prop3_9**

&nbsp;&nbsp;&nbsp;&nbsp;tr ∈ set ([x] ⫴ rev ys) ⟹ tr @ [y] ∈ set ([x] ⫴ (rev ys @ [y]))

---
**prop3_10**

&nbsp;&nbsp;&nbsp;&nbsp;(map (λzs. zs@[y]) (insert_all x ys)) @ [ys@[y,x]] = insert_all x (ys@[y])

---
**prop3_10_1**

&nbsp;&nbsp;&nbsp;&nbsp;map (λtr. tr @ [y]) ([x] ⫴ ys) @ [ys@[y,x]] = insert_all x (ys@[y])

---
**prop3_11**

&nbsp;&nbsp;&nbsp;&nbsp;xa ∈ set ([x] ⫴ (rev ys @ [y])) ⟹ xa ∉ (λtr. tr @ [y]) ` set ([x] ⫴ rev ys) ⟹ xa = rev ys @ [y, x]

---
**prop3_12**

&nbsp;&nbsp;&nbsp;&nbsp;x≠y ⟹ set (map ((#) y) ((x#xs) ⫴ ys)) ∩ set (map ((#) x) (xs ⫴ (y#ys))) = {}

---
**prop3_13**

&nbsp;&nbsp;&nbsp;&nbsp;x≠y ⟹ set (map ((#) x) (xs ⫴ (y#ys))) = set ((x#xs) ⫴ (y#ys)) - set (map ((#) y) ((x#xs) ⫴ ys))

---
**prop3_14**

&nbsp;&nbsp;&nbsp;&nbsp;(x#xs) ⫴ (x#ys) = map ((#) x) ((xs ⫴ (x#ys)) @ ((x#xs) ⫴ ys))

---
**prop3_15**

&nbsp;&nbsp;&nbsp;&nbsp;set [(xs @ [x, y])] ∪ (λtr. tr @ [x]) ` set ((xs ⫴ [y])) = set (((xs @ [x]) ⫴ [y]))

---
**prop3_16**

&nbsp;&nbsp;&nbsp;&nbsp;set (map (λtr. tr@[y]) (rev (x#xs) ⫴ rev ys)) ∪ set (map (λtr. tr@[x]) (rev xs ⫴ rev (y#ys))) = set (rev (x # xs) ⫴ rev (y # ys))

---
**prop3**

&nbsp;&nbsp;&nbsp;&nbsp;set (map rev (xs ⫴ ys)) = set (rev xs ⫴ rev ys)

---
**prop4**

&nbsp;&nbsp;&nbsp;&nbsp;set ((ps @ [p]) ⫴ (qs @ [q])) = {tr @ [p] |tr. tr ∈ set (ps ⫴ (qs @ [q]))} ∪ {tr @ [q] |tr. tr ∈ set ((ps @ [p]) ⫴ qs)}

---
**prop7**

&nbsp;&nbsp;&nbsp;&nbsp;set ((ps@[p]) ⫴ (qs@[q])) = set (map (λxs. xs@[p]) (ps ⫴ (qs@[q])) @ map (λxs. xs@[q]) ((ps@[p]) ⫴ qs))

---
**prop8**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set ys ⟹ xs@[x] ∈ set (map (λt. t@[x]) ys)

---
**prop9**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set (p ⫴ q) ⟹ xs @ r ∈ set (p ⫴ (q @ r))

---
**prop9_1**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set ((p ⫴ r)) ⟹ q @ xs ∈  set (p ⫴ (q @ r))

---
**prop10**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] ∥ [q] ;<sub>c</sub> [r]) ⊆ set ([p] ∥ ([q] ;<sub>c</sub> [r]))

---
**prop10_1**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] ∥ [r] ;<sub>c</sub> [q]) ⊆ set (([p] ;<sub>c</sub> [q]) ∥ [r])

---
**prop10_2**

&nbsp;&nbsp;&nbsp;&nbsp;set ([q] ;<sub>c</sub> [p] ∥ [r]) ⊆ set ([p] ∥ ([q] ;<sub>c</sub> [r]))

---
**prop10_3**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] ;<sub>c</sub> [q] ∥ [r]) ⊆ set (([p] ;<sub>c</sub> [q]) ∥ [r])

---
**inter1**

&nbsp;&nbsp;&nbsp;&nbsp;set ((ps ⫴ qs) ;<sub>c</sub> (rs ⫴ vs)) ⊆ set ((ps @ rs) ⫴ (qs @ vs))

---
**prop10_3_1**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] ∥ [q] ;<sub>c</sub> [r] ∥ [v]) ⊆ set (([p] ;<sub>c</sub> [r]) ∥ ([q] ;<sub>c</sub> [v]))

---
**prop10_4**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] ∥ [q] ;<sub>c</sub> [r] ∥ vs) ⊆ set (([p] ;<sub>c</sub> [r]) ∥ ([q] ;<sub>c</sub> vs))

---
**prop11**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] ∥ qs ;<sub>c</sub> [r]) ⊆ set ([p] ∥ (qs ;<sub>c</sub> [r]))

---
**prop12**

&nbsp;&nbsp;&nbsp;&nbsp;set (([p] ∥ rs) ;<sub>c</sub> [q]) ⊆ set (([p] ;<sub>c</sub> [q]) ∥ rs)

---
**prop13**

&nbsp;&nbsp;&nbsp;&nbsp;set ([q] ;<sub>c</sub> [p] ∥ rs) ⊆ set ([p] ∥ ([q] ;<sub>c</sub> rs))

---
**prop14**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] ;<sub>c</sub> qs ∥ [r]) ⊆ set (([p] ;<sub>c</sub> qs) ∥ [r])

---
**prop15**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] ∥ ([q]) ;<sub>c</sub> rs ∥ s) ⊆ set (([p] ;<sub>c</sub> rs) ∥ ([q] ;<sub>c</sub> s))

---
**subset12**

&nbsp;&nbsp;&nbsp;&nbsp;set (ps ∥ q ;<sub>c</sub> [r]) ⊆ set (ps ∥ (q ;<sub>c</sub> [r]))

---
**subset13**

&nbsp;&nbsp;&nbsp;&nbsp;set ((ps ∥ r) ;<sub>c</sub> [q]) ⊆ set ((ps ;<sub>c</sub> [q]) ∥ r)

---
**subset14**

&nbsp;&nbsp;&nbsp;&nbsp;set ([q] ;<sub>c</sub> ps ∥ r) ⊆ set (ps ∥ ([q] ;<sub>c</sub> r))

---
**subset15**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] ;<sub>c</sub> q ∥ rs) ⊆ set (([p] ;<sub>c</sub> q) ∥ rs)

---
**subset16**

&nbsp;&nbsp;&nbsp;&nbsp;set ([p] ∥ qs ;<sub>c</sub> r ∥ s) ⊆ set (([p] ;<sub>c</sub> r) ∥ (qs ;<sub>c</sub> s))

---
**Conc_composeright_1**

&nbsp;&nbsp;&nbsp;&nbsp;set ((p ∥ q) ;<sub>c</sub> rs) ⊆ set (p ∥ (q ;<sub>c</sub> rs))

---
**Conc_composeright1_1**

&nbsp;&nbsp;&nbsp;&nbsp;set ((p ∥ r) ;<sub>c</sub> qs) ⊆ set ((p ;<sub>c</sub> qs) ∥ r)

---
**Conc_composeleft1_1**

&nbsp;&nbsp;&nbsp;&nbsp;set (qs ;<sub>c</sub> (p ∥ r)) ⊆ set (p ∥ (qs ;<sub>c</sub> r))

---
**Conc_composeright_2**

&nbsp;&nbsp;&nbsp;&nbsp;set (ps ;<sub>c</sub> (q ∥ r)) ⊆ set ((ps ;<sub>c</sub> q) ∥ r)

---
**Conc_composeleft**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate ((p ∥ q) ;<sub>c</sub> r) C ⊆<sub>p</sub> evaluate (p ∥ (q ;<sub>c</sub> r)) C

---
**Conc_composeleftright**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate (q ;<sub>c</sub> (p ∥ r)) C ⊆<sub>p</sub> evaluate (p ∥ (q ;<sub>c</sub> r)) C

---
**Conc_composeright**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate (p ;<sub>c</sub> (q ∥ r)) C ⊆<sub>p</sub> evaluate ((p ;<sub>c</sub> q) ∥ r) C

---
**Conc_composerightleft**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate ((p ∥ r) ;<sub>c</sub> q) C ⊆<sub>p</sub> evaluate ((p ;<sub>c</sub> q) ∥ r) C

---
**Conc_composegeneral**

&nbsp;&nbsp;&nbsp;&nbsp;set (([p] ;<sub>c</sub> [q]) ∥ ([u] ;<sub>c</sub> [v])) ⊆ set (([p] ;<sub>c</sub> [u]) ∥ ([q] ;<sub>c</sub> [v]))

---
**Conc_composegeneral**

&nbsp;&nbsp;&nbsp;&nbsp;set (([p] ;<sub>c</sub> [u]) ∥ ([q] ;<sub>c</sub> [v])) ⊆ set (([p] ;<sub>c</sub> [q]) ∥ ([u] ;<sub>c</sub> [v]))

---
**Conc_composegeneral**

&nbsp;&nbsp;&nbsp;&nbsp;set ((p ;<sub>c</sub> q) ∥ (u ;<sub>c</sub> v)) ⊆ set ((p ;<sub>c</sub> u) ∥ (q ;<sub>c</sub> v))

---
**Conc_composegeneral_1**

&nbsp;&nbsp;&nbsp;&nbsp;set ((ps ∥ q) ;<sub>c</sub> (r ∥ s)) ⊆ set ((ps ;<sub>c</sub> r) ∥ (q ;<sub>c</sub> s))

---
**Conc_composegeneral**

&nbsp;&nbsp;&nbsp;&nbsp;evaluate ((p ∥ q) ;<sub>c</sub> (r ∥ s)) C ⊆<sub>p</sub> evaluate ((p ;<sub>c</sub> r) ∥ (q ;<sub>c</sub> s)) C

---
&nbsp;&nbsp;&nbsp;&nbsp;foldl (+) (b::nat) xs = b + foldl (+) 0 xs

---
**cnf_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;cnf_concurrency2 [[x]] [[y]] C = evaluate ([x] ⫴ [y]) C

---
&nbsp;&nbsp;&nbsp;&nbsp;is_rounded a ⟹ (a;b) ∪<sub>p</sub> (a;c) = a;(b ∪<sub>p</sub> c)

---
**cnf2_prop**

&nbsp;&nbsp;&nbsp;&nbsp;cnf_feasible ([y]#ys) ⟹ complete_cnf_state ([y]#ys) ⊆ C ⟹ ⋃<sub>p</sub> (map ((λxs. Concat xs C) ∘ (#) y) (ys)) ≡<sub>p</sub> y ; ⋃<sub>p</sub> (map (λxs. Concat xs C) (ys))

---
**cnf2_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;cnf_feasible xs ⟹ is_feasible x ⟹ cnf_feasible (map ((#) x) (xs))

---
**cnf2_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;cnf_feasible xs ⟹ cnf_feasible ys ⟹ cnf_feasible (xs@ys)

---
**cnf2_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible (xs@ys) ⟹ cnf_feasible (xs ⫴ ys)

---
**cnf2_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ complete_cnf_state (map ((#) x) xs) = S x ∪ complete_cnf_state xs

---
**cnf2_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;complete_cnf_state xs ∪ complete_cnf_state ys = complete_cnf_state (xs@ys)

---
**cnf2_prop7**

&nbsp;&nbsp;&nbsp;&nbsp;complete_state xs ∪ complete_state ys = complete_cnf_state (xs ⫴ ys)

---
**cnf2_prop8**

&nbsp;&nbsp;&nbsp;&nbsp;S y ⊆ C ⟹ is_feasible y ⟹ ⋃<sub>p</sub> (map ((λxs. Concat xs C) ∘ (#) y) ys) ≡<sub>p</sub> ⋃<sub>p</sub> (map (λxs. y ; Concat xs C) ys)

---
**cnf2_prop9**

&nbsp;&nbsp;&nbsp;&nbsp;⋃<sub>p</sub> (map (λxs. y ; Concat xs C) xs) ≡<sub>p</sub> y ;  ⋃<sub>p</sub> (map (λxs. Concat xs C) xs)

---
**cnf2_prop10**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible y ⟹ S y ⊆ C ⟹ y ; ⋃<sub>p</sub> (map (λxs. Concat xs C) ([x] ⫴ ys)) ≡<sub>p</sub> ⋃<sub>p</sub> (map ((λxs. Concat xs C) ∘ (#) y) ([x] ⫴ ys))

---
**cnf2_prop11**

&nbsp;&nbsp;&nbsp;&nbsp;size xs = size ys ⟹ ∀z ∈ set (zip xs ys). fst z ≡<sub>p</sub> snd z ⟹ ⋃<sub>p</sub> xs ≡<sub>p</sub> ⋃<sub>p</sub> ys

---
**cnf2_prop12**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible x ⟹ S x ⊆ C ⟹ evaluate (map ((#) x) xs) C ≡<sub>p</sub> x ; evaluate xs C

---
**cnf_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible (xs@ys) ⟹ complete_state (xs@ys) ⊆ C ⟹ cnf_concurrency2 [xs] [ys] C ≡<sub>p</sub> evaluate (xs ⫴ ys) C

---
**cnf_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible (x#ys) ⟹ complete_state (x#ys) ⊆ C ⟹ cnf_concurrency2 [[x]] [ys] C ≡<sub>p</sub> evaluate ([x] ⫴ ys) C

---
**cnf2_prop13**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible (x#xs@[y]) ⟹ complete_state (x#xs@[y]) ⊆ C ⟹ x ; cnf_concurrency2 [xs] [[y]] C ≡<sub>p</sub> evaluate (map ((#) x) (xs ⫴ [y])) C

---
**cnf2_prop14**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible (xs@ys) ⟹ complete_state (xs@ys) ⊆ C ⟹ cnf_concurrency2 [xs] [ys] C ≡<sub>p</sub> evaluate ([xs] ∥ [ys]) C

---
**cnf2_prop15**

&nbsp;&nbsp;&nbsp;&nbsp;cnf_feasible (x#ys) ⟹ complete_cnf_state (x#ys) ⊆ C ⟹ cnf_concurrency2 [x] ys C ≡<sub>p</sub> evaluate(concat (map ((⫴) x) ys)) C

---
**cnf2_prop16**

&nbsp;&nbsp;&nbsp;&nbsp;cnf_feasible (xs @ ys) ⟹ cnf_feasible ys

---
**cnf2_prop17**

&nbsp;&nbsp;&nbsp;&nbsp;cnf_feasible (xs @ ys) ⟹ cnf_feasible xs

---
&nbsp;&nbsp;&nbsp;&nbsp;cnf_feasible (xs @ ys) ⟹ complete_cnf_state (xs @ ys) ⊆ C ⟹ cnf_concurrency2 xs ys C ≡<sub>p</sub> evaluate (xs ∥ ys) C

---
## Complex_operation_interactions.thy

**cond_distrib2_1**

&nbsp;&nbsp;&nbsp;&nbsp;GC [(C<sub>1</sub>, p), (C<sub>2</sub>, q)] /<sub>p</sub> D = GC [((D ∩ C<sub>1</sub>), p), ((D ∩ C<sub>2</sub>), q)]

---
**Cond_distrib2_2**

&nbsp;&nbsp;&nbsp;&nbsp;GC [(C<sub>1</sub>, p), (C<sub>2</sub>, q)] /<sub>p</sub> D ≡<sub>p</sub> GC [((D ∩ C<sub>1</sub>), p), ((D ∩ C<sub>2</sub>), q)]

---
**restriction_ite**

&nbsp;&nbsp;&nbsp;&nbsp;(ITE C a b) /<sub>p</sub> D = (ITE C (a/<sub>p</sub>D) (b/<sub>p</sub>D))

---
**restriction_ite**

&nbsp;&nbsp;&nbsp;&nbsp;(ITE C a b) /<sub>p</sub> D = (ITE C (a/<sub>p</sub>D) (b/<sub>p</sub>D))

---
**restriction_ite**

&nbsp;&nbsp;&nbsp;&nbsp;(ITE C a b) /<sub>p</sub> D ≡<sub>p</sub> (ITE C (a/<sub>p</sub>D) (b/<sub>p</sub>D))

---
**restriction_fixed_repetition_1**

&nbsp;&nbsp;&nbsp;&nbsp;0<n ⟹ (p<sup>n + 1</sup>) /<sub>p</sub> C ≡<sub>p</sub> (p /<sub>p</sub> C);(p<sup>n</sup>)

---
**restriction_fixed_repetition_2**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ (p<sup>n</sup>) /<sub>p</sub> C ≡<sub>p</sub> (Skip (S p) /<sub>p</sub> C);(p<sup>n</sup>)

---
**restriction_fixed_repetition_3**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sup>n</sup>) /<sub>p</sub> C ≡<sub>p</sub> (Skip C);(p<sup>n</sup>)

---
&nbsp;&nbsp;&nbsp;&nbsp;loop p s f /<sub>p</sub> C ≡<sub>p</sub> Skip C ; loop p s f

---
**cond_distrib1_gc_1**

&nbsp;&nbsp;&nbsp;&nbsp;GC [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, (p<sub>2</sub> ∪<sub>p</sub> p<sub>3</sub>))] = (GC [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, p<sub>2</sub>)]) ∪<sub>p</sub> (GC [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, p<sub>3</sub>)])

---
**cond_distrib1_gc_2**

&nbsp;&nbsp;&nbsp;&nbsp;GC [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, (p<sub>2</sub> ∪<sub>p</sub> p<sub>3</sub>))] ≡<sub>p</sub> (GC [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, p<sub>2</sub>)]) ∪<sub>p</sub> (GC [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, p<sub>3</sub>)])

---
**cond_distrib1_gc_3**

&nbsp;&nbsp;&nbsp;&nbsp;GC [(C<sub>1</sub>, (p<sub>1</sub> ∪<sub>p</sub> p<sub>3</sub>)), (C<sub>2</sub>, p<sub>2</sub>)] = GC [(C<sub>1</sub>, p<sub>1</sub>), ( C<sub>2</sub>, p<sub>2</sub>)] ∪<sub>p</sub> GC [(C<sub>1</sub>, p<sub>3</sub>), ( C<sub>2</sub>, p<sub>2</sub>)]

---
**cond_distrib1_gc_4**

&nbsp;&nbsp;&nbsp;&nbsp;GC [(C<sub>1</sub>, (p<sub>1</sub> ∪<sub>p</sub> p<sub>3</sub>)), ( C<sub>2</sub>, p<sub>2</sub>)] ≡<sub>p</sub> GC [(C<sub>1</sub>, p<sub>1</sub>), ( C<sub>2</sub>, p<sub>2</sub>)] ∪<sub>p</sub> GC [(C<sub>1</sub>, p<sub>3</sub>), ( C<sub>2</sub>, p<sub>2</sub>)]

---
**cond_distrib1_ite_1**

&nbsp;&nbsp;&nbsp;&nbsp;(ITE C p<sub>1</sub> (p<sub>2</sub> ∪<sub>p</sub> p<sub>3</sub>)) = (ITE C p<sub>1</sub> p<sub>2</sub>) ∪<sub>p</sub> (ITE C p<sub>1</sub> p<sub>3</sub>)

---
**cond_distrib1_ite_2**

&nbsp;&nbsp;&nbsp;&nbsp;(ITE C p<sub>1</sub> (p<sub>2</sub> ∪<sub>p</sub> p<sub>3</sub>)) ≡<sub>p</sub> (ITE C p<sub>1</sub> p<sub>2</sub>) ∪<sub>p</sub> (ITE C p<sub>1</sub> p<sub>3</sub>)

---
**cond_distrib1_ite_3**

&nbsp;&nbsp;&nbsp;&nbsp;(ITE C (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>) p<sub>3</sub>) = (ITE C p<sub>1</sub> p<sub>3</sub>) ∪<sub>p</sub> (ITE C p<sub>2</sub> p<sub>3</sub>)

---
**cond_distrib1_ite_4**

&nbsp;&nbsp;&nbsp;&nbsp;(ITE C (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>) p<sub>3</sub>) ≡<sub>p</sub> (ITE C p<sub>1</sub> p<sub>3</sub>) ∪<sub>p</sub> (ITE C p<sub>2</sub> p<sub>3</sub>)

---
**guard_ifthenelse**

&nbsp;&nbsp;&nbsp;&nbsp;ITE C p<sub>1</sub> p<sub>2</sub> = GC [(C, p<sub>1</sub>), ((-C), p<sub>2</sub>)]

---
**until_def_lemma**

&nbsp;&nbsp;&nbsp;&nbsp;until_loop a C b n ≡<sub>p</sub> a;(loop (b/<sub>p</sub>(-C)) 0 n)∖<sub>p</sub>C

---
## Fixed_repetition.thy

**state_space_is_same**

&nbsp;&nbsp;&nbsp;&nbsp;S p = S (p <sup> </sup>n)

---
**state_space_is_same2**

&nbsp;&nbsp;&nbsp;&nbsp;State (p<sup>n</sup>) = S p

---
**fixed_pre_decreases**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (p<sup>n + 1</sup>) ⊆ Pre (p<sup>n</sup>)

---
**fixed_rep_one_1**

&nbsp;&nbsp;&nbsp;&nbsp;p<sup>1</sup> ≡<sub>p</sub> p /<sub>p</sub> (Pre p)

---
**fixed_rep_one_2**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ p<sup>1</sup> ≡<sub>p</sub> p

---
**fixed_rep_one_3**

&nbsp;&nbsp;&nbsp;&nbsp;x;p<sup>1</sup> ≡<sub>p</sub> x;p

---
**fixed_rep_two_1**

&nbsp;&nbsp;&nbsp;&nbsp;p<sup>2</sup> ≡<sub>p</sub> p ; p

---
**fixed_rep_decomp_front**

&nbsp;&nbsp;&nbsp;&nbsp;0<i ⟹ p<sup>i + 1</sup> ≡<sub>p</sub> p;p<sup>i</sup>

---
**fixed_rep_decomp_back**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ p<sup>i + 1</sup> ≡<sub>p</sub> p<sup>i</sup>;p

---
**fixed_rep_feasibility**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ is_feasible (p<sup>n</sup>)

---
**fixed_rep_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;p<sup>i + 1</sup> ≡<sub>p</sub> p<sup>i</sup>;p

---
**range_decreases_fixed_repetition**

&nbsp;&nbsp;&nbsp;&nbsp;0 < n ⟹ Range_p (x <sup> </sup>n) ⊆ Range_p x

---
**range_decreases_fixed_repetition_2**

&nbsp;&nbsp;&nbsp;&nbsp;0 < n ⟹ Range_p (x <sup> </sup>n + 1) ⊆ Range_p (x <sup> </sup>n)

---
**fixed_prop**

&nbsp;&nbsp;&nbsp;&nbsp;x<sup>1</sup> = Skip (Pre x) ; x

---
**skip_choice**

&nbsp;&nbsp;&nbsp;&nbsp;Skip (Pre x) ; x ∪<sub>p</sub> Skip (Pre y) ; y = Skip (Pre x ∪ Pre y) ; (x ∪<sub>p</sub> y)

---
**comp_prop**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p a ∩ Pre d = {} ⟹ Range_p c ∩ Pre b = {} ⟹ a;b ∪<sub>p</sub> c;d = (a ∪<sub>p</sub> c);(b ∪<sub>p</sub> d)

---
**arbitrary_repetition_simplification**

&nbsp;&nbsp;&nbsp;&nbsp;0<n ⟹ all_feasible [x,y] ⟹ Range_p x ∩ Pre y = {} ⟹ Range_p y ∩ Pre x = {} ⟹ x<sup>n</sup> ∪<sub>p</sub> y<sup>n</sup> = (x ∪<sub>p</sub> y)<sup>n</sup>

---
**arbitrary_repetition_simplification2**

&nbsp;&nbsp;&nbsp;&nbsp;0<n ⟹ all_feasible [x,y] ⟹ Range_p x ∩ Pre y = {} ⟹ Range_p y ∩ Pre x = {} ⟹ x<sup>n</sup> ∪<sub>p</sub> y<sup>n</sup> ≡<sub>p</sub> (x ∪<sub>p</sub> y)<sup>n</sup>

---
**equality_is_maintained_by_fixed_repetition**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> = p<sub>2</sub> ⟹ p<sub>1</sub><sup>n</sup> = p<sub>2</sub><sup>n</sup>

---
**equiv_is_maintained_by_fixed_repetition**

&nbsp;&nbsp;&nbsp;&nbsp;0<n ⟹ all_feasible [p<sub>1</sub>, p<sub>2</sub>] ⟹ p<sub>1</sub> ≡<sub>p</sub> p<sub>2</sub> ⟹ p<sub>1</sub><sup>n</sup> ≡<sub>p</sub> p<sub>2</sub><sup>n</sup>

---
**skip_compose_r_of_fixed_rep_1**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ p<sup>n</sup> ≡<sub>p</sub> p<sup>n</sup> ; Skip (S p)

---
**skip_compose_l_of_fixed_rep_1**

&nbsp;&nbsp;&nbsp;&nbsp;p<sup>n</sup> ≡<sub>p</sub> Skip (S p) ; p<sup>n</sup>

---
**fail_stays_fail_fixed**

&nbsp;&nbsp;&nbsp;&nbsp;p<sup>n</sup> ≡<sub>p</sub> Fail {} ⟹ p<sup>n</sup> + 1 ≡<sub>p</sub> Fail {}

---
**repetition_fail**

&nbsp;&nbsp;&nbsp;&nbsp;i<j ⟹ p<sup>i</sup> ≡<sub>p</sub> Fail {} ⟹ p<sup>j</sup> ≡<sub>p</sub> Fail {}

---
**fix_rep_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;0<i ⟹ p<sup>i</sup> = Skip (S p) /<sub>p</sub> (Pre p) ; Concat [p . t ← [1 .. int i]] (S p)

---
**fix_rep_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;p<sup>i</sup> = Concat ((Skip (S p) /<sub>p</sub> (Pre p))#[p . t ← [1 .. int i]]) (S p)

---
## Guarded_conditional.thy

**gc_S**

&nbsp;&nbsp;&nbsp;&nbsp;S (GC ((C,p)#xs)) = S p ∪ S (GC xs)

---
**gc_S_1**

&nbsp;&nbsp;&nbsp;&nbsp;S (GC (xs)) = complete_state ([snd t. t ← (xs)])

---
**cond_helper_1**

&nbsp;&nbsp;&nbsp;&nbsp;GC (x#xs) = GC (xs @ [x])

---
**cond_helper_2**

&nbsp;&nbsp;&nbsp;&nbsp;xs≠[ ] ⟹ GC (x#xs) = GC [x] ∪<sub>p</sub> GC xs

---
**cond_helper_3**

&nbsp;&nbsp;&nbsp;&nbsp;a ≠[ ] ⟹ b≠ [ ] ⟹ GC (a@b) = GC a ∪<sub>p</sub> GC b

---
**cond_commute**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set (permutations ys) ⟹ GC xs = GC ys

---
**cond_sub1**

&nbsp;&nbsp;&nbsp;&nbsp;D<sub>1</sub> ⊆ C<sub>1</sub> ⟹ D<sub>2</sub> ⊆ C<sub>2</sub> ⟹ (GC [(D<sub>1</sub>, p), (D<sub>2</sub>, q)]) ⊆<sub>p</sub> (GC [(C<sub>1</sub>, p), (C<sub>2</sub>, q)])

---
**property_on_gc_3**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p<sub>1</sub>, p<sub>2</sub>] ⟹ GC [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, p<sub>2</sub>)] ⊑<sub>p</sub> p<sub>1</sub> /<sub>p</sub> C<sub>1</sub>

---
**property_on_gc_3_1**

&nbsp;&nbsp;&nbsp;&nbsp;weakens (GC [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, p<sub>2</sub>)]) (p<sub>1</sub> /<sub>p</sub> C<sub>1</sub>)

---
**property_on_gc_3_2**

&nbsp;&nbsp;&nbsp;&nbsp;strengthens (p<sub>1</sub> /<sub>p</sub> C<sub>1</sub>) (GC [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, p<sub>2</sub>)])

---
**cond_sub4**

&nbsp;&nbsp;&nbsp;&nbsp;(p<sub>1</sub> /<sub>p</sub> C<sub>1</sub>) ⊆<sub>p</sub> (GC [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, p<sub>2</sub>)])

---
**refinement_safety_gc_1**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p, q] ⟹ D<sub>1</sub> ⊆ C<sub>1</sub> ⟹ D<sub>2</sub> ⊆ C<sub>2</sub> ⟹ GC [(D<sub>1</sub>, p), (D<sub>2</sub>, q)] ⊑<sub>p</sub> GC [(C<sub>1</sub>, p), (C<sub>2</sub>, q)]

---
**refinement_safety_gc_2**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p, q] ⟹ D<sub>1</sub> ⊆ C<sub>1</sub> ⟹ D<sub>2</sub> ⊆ C<sub>2</sub> ⟹ GC [(C<sub>1</sub>, p), (C<sub>2</sub>, q)] ⊑<sub>p</sub> GC [(D<sub>1</sub>, p), (D<sub>2</sub>, q)]

---
**refinement_safety_gc_weakens**

&nbsp;&nbsp;&nbsp;&nbsp;D<sub>1</sub> ⊆ C<sub>1</sub> ⟹ D<sub>2</sub> ⊆ C<sub>2</sub> ⟹ weakens (GC [(C<sub>1</sub>, p), (C<sub>2</sub>, q)]) (GC [(D<sub>1</sub>, p), (D<sub>2</sub>, q)])

---
**refinement_safety_gc_strengthens**

&nbsp;&nbsp;&nbsp;&nbsp;D<sub>1</sub> ⊆ C<sub>1</sub> ⟹ D<sub>2</sub> ⊆ C<sub>2</sub> ⟹ strengthens (GC [(D<sub>1</sub>, p), (D<sub>2</sub>, q)]) (GC [(C<sub>1</sub>, p), (C<sub>2</sub>, q)])

---
**cond_refine1**

&nbsp;&nbsp;&nbsp;&nbsp;D<sub>1</sub> ⊆ C<sub>1</sub> ⟹ D<sub>2</sub> ⊆ C<sub>2</sub> ⟹ (GC [(D<sub>1</sub>, p), (D<sub>2</sub>, q)]) ⊑<sub>p</sub> (GC [(C<sub>1</sub>, p), (C<sub>2</sub>, q)])

---
**cond_refine2**

&nbsp;&nbsp;&nbsp;&nbsp;q<sub>1</sub> ⊑<sub>p</sub> p<sub>1</sub> ⟹ q<sub>2</sub> ⊑<sub>p</sub> p<sub>2</sub> ⟹ GC [(C, q<sub>1</sub>), (C, q<sub>2</sub>)] ⊑<sub>p</sub> GC [(C, p<sub>1</sub>), (C, p<sub>2</sub>)]

---
**refinement_safety_gc_3**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p<sub>1</sub>, p<sub>2</sub>, q<sub>1</sub>, q<sub>2</sub>] ⟹ strengthens q<sub>1</sub> p<sub>2</sub> ⟹ strengthens q<sub>2</sub> p<sub>1</sub> ⟹ q<sub>1</sub> ⊑<sub>p</sub> p<sub>1</sub> ⟹ q<sub>2</sub> ⊑<sub>p</sub> p<sub>2</sub> ⟹ GC [(C, q<sub>1</sub>), (C, q<sub>2</sub>)] ⊑<sub>p</sub> GC [(C, p<sub>1</sub>), (C, p<sub>2</sub>)]

---
**refinement_safety_gc_4**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [p<sub>1</sub>, p<sub>2</sub>, q<sub>1</sub>, q<sub>2</sub>] ⟹ independent q<sub>1</sub> p<sub>2</sub> ⟹ independent q<sub>2</sub> p<sub>1</sub> ⟹ q<sub>1</sub> ⊑<sub>p</sub> p<sub>1</sub> ⟹ q<sub>2</sub> ⊑<sub>p</sub> p<sub>2</sub> ⟹ GC [(C, q<sub>1</sub>), (C, q<sub>2</sub>)] ⊑<sub>p</sub> GC [(C, p<sub>1</sub>), (C, p<sub>2</sub>)]

---
**cond_refine4**

&nbsp;&nbsp;&nbsp;&nbsp;GC [(C<sub>1</sub>, p<sub>1</sub>), (C<sub>2</sub>, p<sub>2</sub>)] ⊑<sub>p</sub> p<sub>1</sub> /<sub>p</sub> C<sub>1</sub>

---
**cond_sub2**

&nbsp;&nbsp;&nbsp;&nbsp;q<sub>1</sub> ⊆<sub>p</sub> p<sub>1</sub> ⟹ q<sub>2</sub> ⊆<sub>p</sub> p<sub>2</sub> ⟹ GC [(C, q<sub>1</sub>), (C, q<sub>2</sub>)] ⊆<sub>p</sub> GC [(C, p<sub>1</sub>), (C, p<sub>2</sub>)]

---
**cond_distrib**

&nbsp;&nbsp;&nbsp;&nbsp;GC xs /<sub>p</sub> C ≡<sub>p</sub> GC [(fst t ∩ C, snd t) . t ← xs]

---
**GC_prop_22**

&nbsp;&nbsp;&nbsp;&nbsp;a ∪<sub>p</sub> GC (x#xs) = a ∪<sub>p</sub> (GC [x] ∪<sub>p</sub> GC xs)

---
**gc_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;S (snd x) ⊆ complete_state (map snd xs) ⟹ fst x = FALSE ⟹ 1 < length xs ⟹ GC (x # xs) = GC xs

---
**gc_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;S (snd x) ⊆ complete_state (map snd (a@b)) ⟹ fst x = FALSE ⟹ size (a@b) > 1 ⟹ GC (a@x#b) = GC(a@b)

---
**if_false2**

&nbsp;&nbsp;&nbsp;&nbsp;fst x = FALSE ⟹ GC (a@x#b) ≡<sub>p</sub> GC(a@b)

---
**gc_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;S (snd x) ⊆ complete_state (map snd (a@b)) ⟹ fst x = FALSE ⟹ size (a@b) = 0 ⟹ GC (a@x#b) = GC(a@b)

---
**fail_choice**

&nbsp;&nbsp;&nbsp;&nbsp;S q ⊆ S p ⟹ q ≡<sub>p</sub> Fail {} ⟹ q ∪<sub>p</sub> p = Fail {} ∪<sub>p</sub> p

---
**gc_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;S (snd x) ⊆ complete_state (map snd (a@b)) ⟹ fst x = FALSE ⟹ size (a@b) = 1 ⟹ GC (a@x#b) = Fail {} ∪<sub>p</sub> GC(a@b)

---
**cond_one**

&nbsp;&nbsp;&nbsp;&nbsp;GC [(C,p)] = p/<sub>p</sub>C

---
**gc_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;x /<sub>p</sub> C ⊆<sub>p</sub> GC ((C,x) # xs)

---
**gc_prop7**

&nbsp;&nbsp;&nbsp;&nbsp;GC a ⊆<sub>p</sub> GC (a@b)

---
**cond_sub3**

&nbsp;&nbsp;&nbsp;&nbsp;(C, x) ∈ set (xs) ⟹ x/<sub>p</sub>C ⊆<sub>p</sub> GC xs

---
## If_then_else.thy

**ite_S**

&nbsp;&nbsp;&nbsp;&nbsp;S (ITE C q<sub>1</sub> q<sub>2</sub>) = S q<sub>1</sub> ∪ S q<sub>2</sub>

---
**cond_swap**

&nbsp;&nbsp;&nbsp;&nbsp;ITE C p<sub>1</sub> p<sub>2</sub> = ITE (-C) p<sub>2</sub> p<sub>1</sub>

---
**property_on_ite_2**

&nbsp;&nbsp;&nbsp;&nbsp;Pre (p /<sub>p</sub> C) = Pre (ITE C p (Skip (S p)))

---
**cond_refine3**

&nbsp;&nbsp;&nbsp;&nbsp;q<sub>1</sub> ⊑<sub>p</sub> p<sub>1</sub> ⟹ q<sub>2</sub> ⊑<sub>p</sub> p<sub>2</sub> ⟹ ITE C q<sub>1</sub> q<sub>2</sub> ⊑<sub>p</sub> ITE C p<sub>1</sub> p<sub>2</sub>

---
**cond_refine4**

&nbsp;&nbsp;&nbsp;&nbsp;q<sub>1</sub> ⊆<sub>p</sub> p<sub>1</sub> ⟹ q<sub>2</sub> ⊆<sub>p</sub> p<sub>2</sub> ⟹ ITE C q<sub>1</sub> q<sub>2</sub> ⊆<sub>p</sub> ITE C p<sub>1</sub> p<sub>2</sub>

---
## Non_atomic_concurrency.thy

**non_atomic_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;[ ] ∥ x = x

---
**non_atomic_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;((a # xs) ∥ x) ≡<sub>p</sub> a;(xs ∥ x) ∪<sub>p</sub> Concat (x#a#xs)

---
**compose_distrib**

&nbsp;&nbsp;&nbsp;&nbsp;(b ∪<sub>p</sub> (a ; c ∪<sub>p</sub> a ; d)) = (b ∪<sub>p</sub> a ; (c ∪<sub>p</sub> d))

---
**concur_two**

&nbsp;&nbsp;&nbsp;&nbsp;[a]∥b = a;b ∪<sub>p</sub> b;a

---
**concur_commute**

&nbsp;&nbsp;&nbsp;&nbsp;[a]∥b = ([b]∥a)

---
**compose_distrib2**

&nbsp;&nbsp;&nbsp;&nbsp;∀x ∈ set xs. x ≠ [ ] ⟹ xs ≠ [ ] ⟹ b ∪<sub>p</sub> ⋃<sub>p</sub> [a;(Concat t). t ← xs] = b ∪<sub>p</sub>  a;⋃<sub>p</sub> [(Concat t). t ← xs]

---
**concur_recursive**

&nbsp;&nbsp;&nbsp;&nbsp;((a # xs) ∥ x) = a;(xs ∥ x) ∪<sub>p</sub> Concat (x#a#xs)

---
**non_atomic_conc_S**

&nbsp;&nbsp;&nbsp;&nbsp;S (xs∥x) = complete_state (x#xs)

---
**concor_three_1**

&nbsp;&nbsp;&nbsp;&nbsp;[p<sub>1</sub>, p<sub>2</sub>] ∥ q = ((q;p<sub>1</sub>);p<sub>2</sub> ∪<sub>p</sub> ((p<sub>1</sub>;q);p<sub>2</sub>)) ∪<sub>p</sub> ((p<sub>1</sub>;p<sub>2</sub>);q)

---
**concor_three_2**

&nbsp;&nbsp;&nbsp;&nbsp;[p<sub>1</sub>, p<sub>2</sub>] ∥ q = ((q;p<sub>1</sub>);p<sub>2</sub> ∪<sub>p</sub> ((p<sub>1</sub>;q);p<sub>2</sub>)) ∪<sub>p</sub> ((p<sub>1</sub>;p<sub>2</sub>);q)

---
**concor_three_3**

&nbsp;&nbsp;&nbsp;&nbsp;[p<sub>1</sub>, p<sub>2</sub>] ∥ q ≡<sub>p</sub> ((q;p<sub>1</sub>);p<sub>2</sub> ∪<sub>p</sub> ((p<sub>1</sub>;q);p<sub>2</sub>)) ∪<sub>p</sub> ((p<sub>1</sub>;p<sub>2</sub>);q)

---
**Concat_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible xs ⟹ is_feasible (Concat xs)

---
**Choice_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible xs ⟹ is_feasible (⋃<sub>p</sub> xs)

---
**all_feasible_prop**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible xs ⟹ x ∈ set xs ⟹ is_feasible x

---
**all_feasible_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;∀x ∈ set xs. is_feasible x ≡ all_feasible xs

---
**all_feasible_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set (permutations ys) ⟹ all_feasible ys ⟹ all_feasible xs

---
**non_atomic_conc_feasible_preserving**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible (x#xs) ⟹ is_feasible (xs ∥ x)

---
**atomic_conc_refinement_safe**

&nbsp;&nbsp;&nbsp;&nbsp;q<sub>1</sub> ⊑<sub>p</sub> p<sub>1</sub> ⟹ q<sub>2</sub> ⊑<sub>p</sub> p<sub>2</sub> ⟹ q<sub>3</sub> ⊑<sub>p</sub> p<sub>3</sub> ⟹ ([q<sub>1</sub>, q<sub>2</sub>] ∥ q<sub>3</sub>) ⊑<sub>p</sub> ([p<sub>1</sub>, p<sub>2</sub>] ∥ p<sub>3</sub>)

---
&nbsp;&nbsp;&nbsp;&nbsp;((ys@[x])@xs) ∥<sub>G</sub> q ≡<sub>p</sub> (ys@([x]@xs)) ∥<sub>G</sub> q

---
**atomic_restrict_1**

&nbsp;&nbsp;&nbsp;&nbsp;(xs ∥ x) /<sub>p</sub> C ≡<sub>p</sub>  ⋃<sub>p</sub> [Concat t /<sub>p</sub> C. t ← insert_all x xs]

---
**concur_restrict**

&nbsp;&nbsp;&nbsp;&nbsp;(xs ∥ x) /<sub>p</sub> C =  ⋃<sub>p</sub> [Concat t /<sub>p</sub> C. t ← insert_all x xs]

---
**atomic_corestrict_1**

&nbsp;&nbsp;&nbsp;&nbsp;(xs ∥ x) ∖<sub>p</sub> C ≡<sub>p</sub>  ⋃<sub>p</sub> [Concat t ∖<sub>p</sub> C. t ← insert_all x xs]

---
**equiv_list_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;equiv_list xs ys ⟹ ⋃<sub>p</sub> xs ≡<sub>p</sub> ⋃<sub>p</sub> ys

---
**equiv_list_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;∀a ∈ set xs. a ≠ [ ] ⟹ equiv_list [Concat t /<sub>p</sub> C. t ← xs] [Concat (hd t /<sub>p</sub> C # tl t). t ← xs]

---
**equiv_list_prop_3**

&nbsp;&nbsp;&nbsp;&nbsp;∀a ∈ set xs. a ≠ [ ] ⟹ equiv_list [Concat t ∖<sub>p</sub> C. t ← xs] [Concat (butlast t @ [(last t)∖<sub>p</sub> C]). t ← xs]

---
**concur_restrict**

&nbsp;&nbsp;&nbsp;&nbsp;(xs ∥ x) /<sub>p</sub> C ≡<sub>p</sub>  ⋃<sub>p</sub> [Concat (hd t/<sub>p</sub>C#tl t). t ← insert_all x xs]

---
**concur_corestrict**

&nbsp;&nbsp;&nbsp;&nbsp;(xs ∥ x) ∖<sub>p</sub> C ≡<sub>p</sub>  ⋃<sub>p</sub> [Concat (butlast t @ [(last t)∖<sub>p</sub> C]). t ← insert_all x xs]

---
**concur_specialize1**

&nbsp;&nbsp;&nbsp;&nbsp;p ; q ⊆<sub>p</sub> ([p] ∥ q)

---
**non_atomic_specialize**

&nbsp;&nbsp;&nbsp;&nbsp;ys ∈ set (insert_all x xs) ⟹ (Concat ys) ⊆<sub>p</sub> (xs ∥ x)

---
**commute_compose**

&nbsp;&nbsp;&nbsp;&nbsp;commute_programs3 a b ⟹ [a] ∥ b ≡<sub>p</sub> a;b

---
**concur_distrib1**

&nbsp;&nbsp;&nbsp;&nbsp;xs∥(b ∪<sub>p</sub> c) ≡<sub>p</sub> (xs∥b) ∪<sub>p</sub> (xs∥c)

---
**concur_choice1**

&nbsp;&nbsp;&nbsp;&nbsp;[a∪<sub>p</sub>b]∥(c) = ([a]∥c) ∪<sub>p</sub> ([b]∥c)

---
**concur_choice2**

&nbsp;&nbsp;&nbsp;&nbsp;xs∥(b ∪<sub>p</sub> c) = (xs∥b) ∪<sub>p</sub> (xs∥c)

---
**concur_specialize2**

&nbsp;&nbsp;&nbsp;&nbsp;([Concat xs] ∥ x) ⊆<sub>p</sub> (xs ∥ x)

---
## Permutations.thy

**simp_2**

&nbsp;&nbsp;&nbsp;&nbsp;∀x<sub>1</sub> x<sub>2</sub> x<sub>3</sub>. f (f x<sub>1</sub> x<sub>2</sub>) x<sub>3</sub> = f  x<sub>1</sub> (f x<sub>2</sub> x<sub>3</sub>) ⟹ foldl f (f a x) xs = f a (foldl f x xs)

---
**fold_composition_assoc**

&nbsp;&nbsp;&nbsp;&nbsp;foldl (;) x (as @ [a]) = (foldl (;) x as) ; a

---
**S_foldl_composition**

&nbsp;&nbsp;&nbsp;&nbsp;S (foldl (;) x as) = ⋃ (S ` (set (x # as)))

---
**main_theorem**

&nbsp;&nbsp;&nbsp;&nbsp;S (foldl (;) x (a # as)) = S ((foldl (;) x as) ; a)

---
**skip_fold_complete_state**

&nbsp;&nbsp;&nbsp;&nbsp;S (Skip (complete_state (x # xs))) ∪ S x ∪ S (foldl (;) x xs) = complete_state (x # xs) ∪ S x ∪ complete_state xs

---
**simp_5**

&nbsp;&nbsp;&nbsp;&nbsp;S (foldl (;) (Skip (complete_state xs)) xs) = complete_state xs

---
**simp_4_right**

&nbsp;&nbsp;&nbsp;&nbsp;S (foldl (;) (Skip (complete_state xs)) xs) ⊆ complete_state xs

---
**fold_composition_state_inv**

&nbsp;&nbsp;&nbsp;&nbsp;S (fold (;) t b) = S (foldl (;) b t)

---
&nbsp;&nbsp;&nbsp;&nbsp;S (fold (;) t (Skip (complete_state t))) = S (foldl (;) (Skip (complete_state t)) t)

---
**permutation_fold_subset_complete_state**

&nbsp;&nbsp;&nbsp;&nbsp;t ∈ set (permutations xs) ⟹ S (fold (;) t (Skip (complete_state t))) ⊆ complete_state xs

---
**state_composition**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ S a ⟹ x ∈ S (a ; b)

---
**state_composition_1**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ S p ⟹ x ∈ S (foldl (;) p (xs))

---
**state_composition_2**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ S a ⟹ x ∈ S (foldl (;) p (a#xs))

---
**state_composition_3**

&nbsp;&nbsp;&nbsp;&nbsp;x ∈ S a ⟹ x ∈ S (foldl (;) p (ys@a#xs))

---
**complete_state_subset**

&nbsp;&nbsp;&nbsp;&nbsp;complete_state xs ⊆ S (Skip (complete_state xs))

---
**foldl_composition_preserves_state**

&nbsp;&nbsp;&nbsp;&nbsp;S p ⊆ S (foldl (;) p xs)

---
**Union_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;⋃ (set (xs@[x])) = x ∪ ⋃ (set xs)

---
**Union_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;⋃ (xs ∪ {x}) = x ∪ ⋃ xs

---
**fold_comp_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ foldl (;) x xs = foldl (;) (x;Skip (S x)) xs

---
**fold_comp_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ foldl (;) x xs = foldl (;) (x;Skip (complete_state (x#xs))) xs

---
**fold_comp_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;S (foldl (;) x xs) = complete_state (x # xs)

---
**fold_comp_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;xs ≠ [ ] ⟹ foldl (;) x xs = foldl (;) (x;Skip (complete_state (xs))) xs

---
**perm_prop_1**

&nbsp;&nbsp;&nbsp;&nbsp;(filter (p) xs) @ (filter (λx. ¬p x) xs) ∈ set (permutations xs)

---
**perm_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;xs ∈ set (permutations ys) ⟹ map p xs ∈ set (permutations (map p ys))

---
## Until_loop.thy

**until_conncetion**

&nbsp;&nbsp;&nbsp;&nbsp;until_loop a C b n = until_support a C b 0 n

---
**until_decomposition**

&nbsp;&nbsp;&nbsp;&nbsp;until_loop a C b (n + 1) ≡<sub>p</sub> a;((b/<sub>p</sub>(-C))<sup>n + 1</sup> ∪<sub>p</sub> (loop (b/<sub>p</sub>(-C)) 0 n)) ∖<sub>p</sub> C

---
**until_decomposition_2**

&nbsp;&nbsp;&nbsp;&nbsp;until_loop a C b (n + 1) ≡<sub>p</sub> a;((b/<sub>p</sub>(-C))<sup>n + 1</sup>) ∖<sub>p</sub> C ∪<sub>p</sub> until_loop a C b n

---
**until_def_lemma_3**

&nbsp;&nbsp;&nbsp;&nbsp;until_loop a C b n ≡<sub>p</sub> a;((Skip (S (b/<sub>p</sub>(-C))) /<sub>p</sub> (Pre (b/<sub>p</sub>(-C)))) ∪<sub>p</sub> (loop (b/<sub>p</sub>(-C)) 1 n)) ∖<sub>p</sub> C

---
**loop_choice1**

&nbsp;&nbsp;&nbsp;&nbsp;until_loop a C b n ≡<sub>p</sub> ⋃<sub>p</sub> [a;((b /<sub>p</sub> (- C))<sup>nat i</sup>)∖<sub>p</sub>C. i ← [0..int n]]

---
**loop_choice2**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p (until_loop a C b n) = ⋃ (set [Range_p (a;((b /<sub>p</sub> (- C))<sup>nat i</sup>)∖<sub>p</sub>C). i ← [0..int n]])

---
**until_loop_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [a, b] ⟹ is_feasible (until_loop a C b n)

---
**equiv_is_maintained_by_until_loop_2**

&nbsp;&nbsp;&nbsp;&nbsp;a<sub>1</sub> ≡<sub>p</sub> a<sub>2</sub> ⟹ b<sub>1</sub> ≡<sub>p</sub> b<sub>2</sub> ⟹ S b<sub>1</sub> = S b<sub>2</sub> ⟹ all_feasible [b<sub>1</sub>, b<sub>2</sub>] ⟹ until_loop a<sub>1</sub> C b<sub>1</sub> n ≡<sub>p</sub> until_loop a<sub>2</sub> C b<sub>2</sub> n

---
**until_decom**

&nbsp;&nbsp;&nbsp;&nbsp;k<n ⟹ until_loop a C b n ≡<sub>p</sub> until_loop a C b n ∪<sub>p</sub> until_loop a C b k

---
**range_until_loop_1**

&nbsp;&nbsp;&nbsp;&nbsp;m<n ⟹ x ∉ Range_p (until_loop a C b n) ⟹ x ∉ Range_p (until_loop a C b m)

---
**range_until_loop_2**

&nbsp;&nbsp;&nbsp;&nbsp;m<n ⟹ x ∉ Range_p (until_loop a C b n) ⟹ x ∉ Range_p (until_support a C b s m)

---
**loop_range**

&nbsp;&nbsp;&nbsp;&nbsp;Range_p (until_loop a C b n) ⊆ C

---
**split_front**

&nbsp;&nbsp;&nbsp;&nbsp;until_loop (x;a) C b n ≡<sub>p</sub> x ; until_loop a C b n

---
**fail_until**

&nbsp;&nbsp;&nbsp;&nbsp;until_loop a C b (n + 1) ≡<sub>p</sub> Fail {} ⟹ until_loop a C b n ≡<sub>p</sub> Fail {}

---
**fail_until_2**

&nbsp;&nbsp;&nbsp;&nbsp;k<n ⟹ until_loop a C b n ≡<sub>p</sub> Fail {} ⟹ until_loop a C b k ≡<sub>p</sub> Fail {}

---
**loop_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;S (loop (b/<sub>p</sub>(-C)) 0 n) = S b

---
**loop_prop2**

&nbsp;&nbsp;&nbsp;&nbsp;State (loop (b/<sub>p</sub>(-C)) 0 n) = S b

---
**loop_prop3**

&nbsp;&nbsp;&nbsp;&nbsp;S (until_loop a C b n) = S a ∪ S b

---
**loop_prop4**

&nbsp;&nbsp;&nbsp;&nbsp;State (until_loop a C b n) = S (until_loop a C b n)

---
**loop_prop5**

&nbsp;&nbsp;&nbsp;&nbsp;State (until_loop a C b n) = S a ∪ S b

---
**loop_prop6**

&nbsp;&nbsp;&nbsp;&nbsp;until_loop (Skip D) FALSE (Skip D) n = Fail D

---
## Until_support.thy

**until_decomp_1**

&nbsp;&nbsp;&nbsp;&nbsp;until_support a C b 0 n ≡<sub>p</sub> until_support a C b 0 0 ∪<sub>p</sub> until_support a C b (0 + 1) n

---
**until_decomp_2**

&nbsp;&nbsp;&nbsp;&nbsp;until_support a C b 0 (n + 1) ≡<sub>p</sub> until_support a C b 0 n ∪<sub>p</sub> until_support a C b (n + 1) (n + 1)

---
**until_decomp_3**

&nbsp;&nbsp;&nbsp;&nbsp;s < f ⟹ until_support a C b s f ≡<sub>p</sub> until_support a C b s s ∪<sub>p</sub> until_support a C b (s + 1) f

---
**until_decomp_4**

&nbsp;&nbsp;&nbsp;&nbsp;s < f ⟹ until_support a C b s (f + 1) ≡<sub>p</sub> until_support a C b (f + 1) (f + 1) ∪<sub>p</sub> until_support a C b s f

---
**until_decomp_5**

&nbsp;&nbsp;&nbsp;&nbsp;0 < k ⟹ k < n ⟹ until_support a C b 0 n ≡<sub>p</sub> until_support a C b 0 k ∪<sub>p</sub> until_support a C b (k + 1) n

---
**until_decomp_6**

&nbsp;&nbsp;&nbsp;&nbsp;s < k ⟹ k < f ⟹ until_support a C b s f ≡<sub>p</sub> until_support a C b s k ∪<sub>p</sub> until_support a C b (k + 1) f

---
**until_decomp_7**

&nbsp;&nbsp;&nbsp;&nbsp;s = f ⟹ until_support a C b s f ≡<sub>p</sub> a ; ((b /<sub>p</sub> (- C))<sup>f</sup>) ∖<sub>p</sub> C

---
**until_support_feasible**

&nbsp;&nbsp;&nbsp;&nbsp;all_feasible [a, b] ⟹ is_feasible (until_support a C b s f)

---
**equiv_is_maintained_by_until_support_1**

&nbsp;&nbsp;&nbsp;&nbsp;a<sub>1</sub> ≡<sub>p</sub> a<sub>2</sub> ⟹ b<sub>1</sub> ≡<sub>p</sub> b<sub>2</sub> ⟹ S b<sub>1</sub> = S b<sub>2</sub> ⟹ all_feasible [b<sub>1</sub>, b<sub>2</sub>] ⟹ until_support a<sub>1</sub> C b<sub>1</sub> s f ≡<sub>p</sub> until_support a<sub>2</sub> C b<sub>2</sub> s f

---
**equiv_is_maintained_by_until_support_2**

&nbsp;&nbsp;&nbsp;&nbsp;a<sub>1</sub> ≡<sub>p</sub> a<sub>2</sub> ⟹ b<sub>1</sub> ≡<sub>p</sub> b<sub>2</sub> ⟹ 0<s ⟹ all_feasible [b<sub>1</sub>, b<sub>2</sub>] ⟹ until_support a<sub>1</sub> C b<sub>1</sub> s f ≡<sub>p</sub> until_support a<sub>2</sub> C b<sub>2</sub> s f

---
**bad_index_is_fail_support**

&nbsp;&nbsp;&nbsp;&nbsp;f < s ⟹ until_support a C b s f ≡<sub>p</sub> Fail {}

---
**bad_index_range_support**

&nbsp;&nbsp;&nbsp;&nbsp;f < s ⟹ Range_p (until_support a C b s f) = {}

---
**until_support_decomp**

&nbsp;&nbsp;&nbsp;&nbsp;s<s' ⟹ f'<f ⟹ until_support a C b s f ≡<sub>p</sub> until_support a C b s f ∪<sub>p</sub> until_support a C b s' f'

---
## Contract.thy

**consequence_rule**

&nbsp;&nbsp;&nbsp;&nbsp;post<sub>1</sub> ⊆ post<sub>2</sub> ⟹ Pre<sub>2</sub> ⊆ Pre<sub>1</sub> ⟹ is_correct 〈a_specification=〈State=Pre<sub>1</sub> ∪ Field post<sub>2</sub>, Pre=Pre<sub>1</sub>, post=post<sub>1</sub>〉, a_implementation=b〉 ⟹ is_correct 〈a_specification=〈State=Pre<sub>1</sub> ∪ Field post<sub>2</sub>, Pre=Pre<sub>2</sub>, post=post<sub>2</sub>〉, a_implementation=b〉

---
**post_charac_old**

&nbsp;&nbsp;&nbsp;&nbsp;is_correct 〈a_specification=s, a_implementation=b〉 ⟹ b sp (Pre s) ⊆ post s

---
**pre_charac_old**

&nbsp;&nbsp;&nbsp;&nbsp;is_correct 〈a_specification=s, a_implementation=b〉 ⟹ Pre s ⊆ b wp (post s)

---
**correct_program_1**

&nbsp;&nbsp;&nbsp;&nbsp;is_correct 〈a_specification=s, a_implementation=b〉 ⟹ Pre s ⊆ Pre b - Domain (post b - post s)

---
**correct_program_2**

&nbsp;&nbsp;&nbsp;&nbsp;S s = S b ⟹ is_feasible b ⟹ Pre s ⊆ Pre b - Domain (post b - post s) ⟹ is_correct 〈a_specification=s, a_implementation=b〉

---
**correct_program**

&nbsp;&nbsp;&nbsp;&nbsp;S s = S b ⟹ is_feasible b ⟹ is_correct 〈a_specification=s, a_implementation=b〉 = (Pre s ⊆ Pre b - Domain (post b - post s))

---
**fail_false**

&nbsp;&nbsp;&nbsp;&nbsp;b sp FALSE = FALSE

---
**false_fail**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible b ⟹ b wp FALSE = FALSE

---
&nbsp;&nbsp;&nbsp;&nbsp;b wp FALSE = Pre b - Domain (post b)

---
**fail_pre**

&nbsp;&nbsp;&nbsp;&nbsp;Fail S' sp Pre' = {}

---
**sp_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;p sp TRUE (S p) = post p

---
**wp_prop1**

&nbsp;&nbsp;&nbsp;&nbsp;p wp TRUE<sub>r</sub> (S p) = Pre p

---
&nbsp;&nbsp;&nbsp;&nbsp;Havoc C sp pre = {(x,y). x ∈ pre ∧ x ∈ C ∧ y ∈ C}

---
&nbsp;&nbsp;&nbsp;&nbsp;Havoc C sp pre = post (Havoc C) /<sub>r</sub> pre

---
**fail_post**

&nbsp;&nbsp;&nbsp;&nbsp;Fail S' wp post' = FALSE

---
**sp_distrib**

&nbsp;&nbsp;&nbsp;&nbsp;b sp (p ∪ q) = b sp p ∪ b sp q

---
**wp_distrib2**

&nbsp;&nbsp;&nbsp;&nbsp;(b wp p) ∪ (b wp q) ⊆ b wp (p ∪ q)

---
**sanity**

&nbsp;&nbsp;&nbsp;&nbsp;q ⊑<sub>p</sub> p ⟹  〈a_specification=s, a_implementation=q〉 ⊑<sub>c</sub>  〈a_specification=s, a_implementation=p〉

---
**mai_theorem_1**

&nbsp;&nbsp;&nbsp;&nbsp;is_feasible p ⟹ is_correct (MAI p)

---
**state_feasible_1**

&nbsp;&nbsp;&nbsp;&nbsp;(∀s ∈ Pre p . is_trivial (post p) s ∨ is_relevant (post p) s) = is_feasible p

---
&nbsp;&nbsp;&nbsp;&nbsp;(Infeas D) wp C = TRUE D

---
&nbsp;&nbsp;&nbsp;&nbsp;(Infeas D) sp C = FALSE

---
&nbsp;&nbsp;&nbsp;&nbsp;(Havoc D) sp C = (TRUE<sub>r</sub> D) /<sub>r</sub> C

---
&nbsp;&nbsp;&nbsp;&nbsp;(Infeas D) sp C = FALSE

---
**post_charac**

&nbsp;&nbsp;&nbsp;&nbsp;implements a b ⟹ a sp (Pre b) ⊆ post b

---
**pre_charac**

&nbsp;&nbsp;&nbsp;&nbsp;implements i s ⟹ Pre s ⊆ i wp (post s)

---
## Invariant.thy

**invariant_disjoint_from_pre**

&nbsp;&nbsp;&nbsp;&nbsp;I ∩ (Pre p) = {} ⟹ is_invariant I p

---
**false_is_invariant**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant FALSE p

---
**equiv_inv**

&nbsp;&nbsp;&nbsp;&nbsp;p<sub>1</sub> ≡<sub>p</sub> p<sub>2</sub> ⟹ is_invariant I p<sub>1</sub> = is_invariant I p<sub>2</sub>

---
**invariant_relation_1**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I p ⟹ is_invariant J p ⟹ is_invariant (I ∪ J) p

---
**invariant_relation_2**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I p ⟹ is_invariant J p ⟹ is_invariant (I ∩ J) p

---
**invariant_refinement**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I p<sub>1</sub> ⟹ p<sub>2</sub> ⊑<sub>p</sub> p<sub>1</sub> ⟹ is_invariant I (p<sub>2</sub> /<sub>p</sub> (Pre p<sub>1</sub>))

---
**invariant_prop_specialize**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I p<sub>1</sub> ⟹ p<sub>2</sub> ⊆<sub>p</sub> p<sub>1</sub> ⟹ is_invariant I (p<sub>2</sub>)

---
**invariant_prop_2**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I (Fail C)

---
**invariant_prop_3**

&nbsp;&nbsp;&nbsp;&nbsp;C ⊆ I ⟹ is_invariant I (Havoc C)

---
**invariant_prop_4**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I (Skip C)

---
**composition_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I p<sub>1</sub> ⟹ is_invariant I p<sub>2</sub> ⟹ is_invariant I (p<sub>1</sub> ; p<sub>2</sub>)

---
**choice_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I p<sub>1</sub> ⟹ is_invariant I p<sub>2</sub> ⟹ is_invariant I (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>)

---
**choice_invariant_preserve_2**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>) ⟹ is_invariant I p<sub>1</sub>

---
**choice_invariant_preserve_3**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>) ⟹ is_invariant I p<sub>2</sub>

---
**choice_invariant_preserve_4**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I (p<sub>1</sub> ∪<sub>p</sub> p<sub>2</sub>) = (is_invariant I p<sub>1</sub> ∧ is_invariant I p<sub>2</sub>)

---
**restriction_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I p ⟹ is_invariant I (p /<sub>p</sub> C)

---
**restriction_invariant_preserve_2**

&nbsp;&nbsp;&nbsp;&nbsp;I ⊆ C ⟹ is_invariant I (p /<sub>p</sub> C) ⟹ is_invariant I p

---
**corestriction_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I p ⟹ is_invariant I (p ∖<sub>p</sub> C)

---
**c_is_invariant**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant C (p ∖<sub>p</sub> C)

---
**guarded_conditional_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I p ⟹ is_invariant I q ⟹ is_invariant I (GC [(C, p), (D, q)])

---
**if_then_else_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I p ⟹ is_invariant I q ⟹ is_invariant I (ITE C p q)

---
**fixed_repetition_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp; is_invariant I p ⟹ is_invariant I (p<sup>n</sup>)

---
**arbitrary_repetition_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I p ⟹ is_invariant I (loop p s f)

---
**until_support_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;0<s ⟹ is_invariant I a ⟹ is_invariant I b ⟹ is_invariant I (until_support a C b s f)

---
**until_loop_invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I a ⟹ is_invariant I b ⟹ is_invariant I (until_loop a C b n)

---
**inverse_is_not_invariant_preseving**

&nbsp;&nbsp;&nbsp;&nbsp;Pre p ⊆ I ⟹ is_invariant I p ⟹ is_invariant I (p<sup>-</sup><sup>1</sup>)

---
**true_is_invariant**

&nbsp;&nbsp;&nbsp;&nbsp;S p ⊆ C ⟹ is_invariant (TRUE C) p

---
**invariant_exp**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I b ⟹ x ∈ Pre b ⟹ (x,y) ∈ post b  ⟹ x ∈ I ⟹ y ∈ I

---
**invariant_preserve**

&nbsp;&nbsp;&nbsp;&nbsp;is_invariant I b ⟹ Range_p a ⊆ I ⟹ x ∈ Pre a ⟹ (x,y) ∈ post (a;b) ⟹ y ∈ I

---
## Loop_invariant.thy

**false_is_loop_invariant**

&nbsp;&nbsp;&nbsp;&nbsp;is_loop_invariant FALSE a C b

---
**true_is_loop_invariant**

&nbsp;&nbsp;&nbsp;&nbsp;S a ∪ S b ∪ C ⊆ D ⟹ is_loop_invariant (TRUE D) a C b

---
**loop_invariant_is_invariant_of_loop**

&nbsp;&nbsp;&nbsp;&nbsp;0<s ⟹ is_loop_invariant I a C b ⟹ is_invariant I (loop (b/<sub>p</sub>(-C)) s n)

---
**loop_correct_1**

&nbsp;&nbsp;&nbsp;&nbsp;is_loop_invariant I a C b ⟹ Range_p (a ; loop (b /<sub>p</sub> (- C)) n n) ⊆ I

---
**loop_correct_2**

&nbsp;&nbsp;&nbsp;&nbsp;is_loop_invariant I a C b ⟹ Range_p (until_support a C b n n) ⊆ I

---
**loop_correct_3**

&nbsp;&nbsp;&nbsp;&nbsp;s<f ⟹ is_loop_invariant I a C b ⟹ Range_p (until_support a C b s f) ⊆ I

---
**loop_correct**

&nbsp;&nbsp;&nbsp;&nbsp;is_loop_invariant I a C b ⟹ Range_p (until_loop a C b n) ⊆ C ∩ I

---
**is_invariant_is_preserved**

&nbsp;&nbsp;&nbsp;&nbsp;p ≡<sub>p</sub> q ⟹ is_invariant I p ⟹ is_invariant I q

---
**is_loop_invariant_is_preserved**

&nbsp;&nbsp;&nbsp;&nbsp;a ≡<sub>p</sub> a' ⟹ b ≡<sub>p</sub> b' ⟹ is_loop_invariant I a C b ⟹ is_loop_invariant I a' C b'

---
**loop_inv_is_inv_for_a**

&nbsp;&nbsp;&nbsp;&nbsp;is_loop_invariant I a C b ⟹ is_invariant I a

---
**Loop_inv_1**

&nbsp;&nbsp;&nbsp;&nbsp;is_loop_invariant I a C b ⟹ is_invariant I (b /<sub>p</sub> (- C))

---
**loop_inv_is_inv_of_loop**

&nbsp;&nbsp;&nbsp;&nbsp;is_loop_invariant I a C b ⟹ is_invariant I (loop (b/<sub>p</sub>(-C)) 0 n)

---
**Loop_invinv**

&nbsp;&nbsp;&nbsp;&nbsp;is_loop_invariant I a C b ⟹ is_invariant I (until_loop a C b n)

---
