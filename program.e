note
	description: "A Representation of the programs as defined in `Theory of Programs'."
	author: "Reto Weber"
	date: "$Date$"
	revision: "$Revision$"

--	explicit: contracts

class
	PROGRAM [T -> ANY]

inherit
	ANY
		redefine
			default_create,
			is_equal,
			out
		end

create
	default_create, create_with_pre_and_post, create_fail, create_havoc, create_skip

feature
	default_create
		note
			status: creator
		do
			create state_space.default_create
			create post.default_create
			create pre.default_create
		end

	create_with_pre_and_post (a_post: MML_RELATION [T, T]; a_pre, a_state_space: MML_SET [T])
		note
			status: creator
		do
			state_space := a_state_space
			pre := a_pre
			post := a_post
		end

feature -- class methods
	fail (a_state_space: MML_SET [T]): PROGRAM [T]
		do
			create Result.create_fail (a_state_space)
		ensure
			Result.is_feasible
			class
		end

	havoc (a_state_space: MML_SET [T]): PROGRAM [T]
		do
			create Result.create_havoc (a_state_space)
		ensure
			Result.is_feasible
			class
		end

	skip (a_state_space: MML_SET [T]): PROGRAM [T]
		do
			create Result.create_skip (a_state_space)
		ensure
			Result.is_feasible
			class
		end

feature {PROGRAM} -- hidden creation procedures

	create_skip (a_state_space: MML_SET [T])
		note
			status: creator
		local
			state_space_arr: ARRAY [T]
		do
			state_space := a_state_space
			pre := a_state_space
			state_space_arr := a_state_space.to_array
			create post.make_from_arrays (state_space_arr, state_space_arr)
		end

	create_fail (a_state_space: MML_SET [T])
		note
			status: creator
		do
			state_space := a_state_space
			create post.default_create
			create pre.default_create
		end

	create_havoc (a_state_space: MML_SET [T])
		note
			status: creator
		local
			lefts, rights, state_space_arr: ARRAY [T]
			l_index, r_index, total_index, size: INTEGER
		do
			state_space := a_state_space
			pre := a_state_space

				-- initialize lefts and rights of the relation to the right size
			size := a_state_space.count
			size := size
			create lefts.make_empty
			create rights.make_empty
			lefts.grow (size * size)
			rights.grow (size * size)

				-- iterate over all combinations of the array
			from
				l_index := 1
				total_index := 1
				state_space_arr := a_state_space.to_array
			until
				l_index > a_state_space.count
			loop
				from
					r_index := 1
				until
					r_index > a_state_space.count
				loop
					lefts [total_index] := state_space_arr [l_index]
					rights [total_index] := state_space_arr [r_index]

						-- index increase
					total_index := total_index + 1
					r_index := r_index + 1
				end
					-- index increase
				l_index := l_index + 1
			end
			create post.make_from_arrays (lefts, rights)
		end

feature -- io
	out: STRING
		do
			Result := "<" + post.out + ", " + pre.out + ">"
		end

feature -- Attirbutes
	state_space: MML_SET [T]

	post: MML_RELATION [T, T]

	pre: MML_SET [T]

feature -- Comparison
	is_equal (other: like Current): BOOLEAN
		do
			Result := pre ~ other.pre ∧ post ~ other.post
		ensure then
			Result = (pre ~ other.pre ∧ post ~ other.post)
			same_pre: Result ⇒ pre ~ other.pre
			same_post: Result ⇒ post ~ other.post
		end

	refines alias "⊆" (refinee: like Current): BOOLEAN
		do
			Result := p1 (refinee, Current) ∧ p2 (refinee, Current) ∧ p3 (refinee, Current)
		ensure
			Result = (refinee.state_space ⊆ state_space ∧ refinee.pre ⊆ pre ∧ (post / refinee.pre).to_set ⊆ refinee.post.to_set)
		end

	specifies (refiner: like Current): BOOLEAN
		do
			Result := refiner ⊆ Current
		end

feature -- Propperties

	is_deterministic: BOOLEAN
			-- If post is a function the program is called deterministic
		do
				-- TODO
			Result := True
		end

	is_functional: BOOLEAN
			-- The definition in the paper is: ∀C ⊆ state_space ¦ post.image(C).intersection (C).is_empty
			-- The subset C canonly share an element with its image iff there is an element in C and post.image(C)
			-- If there exists such a C then it means the element is also shared between domain and range.
			-- If there is no such C then it means domain an range do not share a single element. (Can be proven by contradiction.)
		do
			Result := ∅= (post.domain ∩ post.range)
		end

	implements (other: PROGRAM [T]): BOOLEAN
			-- An implementation of `other' is a feasible refinment of `other'
		note
			status: functional
		do
			Result := is_feasible ∧ Current ⊆ other
		end

	is_feasible: BOOLEAN
		note
			status: functional
		do
			Result := pre ⊆ post.domain
		end

	p1 (refinee, refiner: PROGRAM [T]): BOOLEAN
			-- Extension
		note
			status: functional
		do
			Result := refiner.state_space ⊇ refinee.state_space
		ensure
			class
		end

	p2 (refinee, refiner: PROGRAM [T]): BOOLEAN
			-- Weakening
		note
			status: functional
		do
			Result := refiner.pre ⊇ refinee.pre
		ensure
			class
		end

	p3 (refinee, refiner: PROGRAM [T]): BOOLEAN
			-- Strengthening
		note
			status: functional
		do
			Result := (refiner.post / refinee.pre).to_set ⊆ refinee.post.to_set
		ensure
			class
		end

	p4 (pr1, pr2, pr3: PROGRAM [T]): BOOLEAN
			-- Refinment is a preorder
		note
			status: functional
		do
			Result := refinment_is_reflexive (pr1) ∧ refinment_is_transitive (pr1, pr2, pr3)
		ensure
			class
			Result
		end

	p5 (implementation, specification: PROGRAM [T]): BOOLEAN
			-- A specification/program having an implementation is feasible.
		note
			status: functional
		do
			Result := implementation.implements (specification) ⇒ specification.is_feasible
		ensure
			class
			Result
		end

	p6 (pr1, pr2: PROGRAM [T]; c: MML_SET [T]): BOOLEAN
			-- For feasible operands and arbitrary conditions, the above operators yield feasible programs.
			-- c3 does not hold for:
			-- `pr := <{[1, 1], [1, 2]}, {1}>'
			-- `c := {2}'
			-- Then `pr ← c = <{}, {1}>' which is not feasible
		local
			c1, c2, c3: BOOLEAN
		do
			c1 := pr1.is_feasible ∧ pr2.is_feasible ⇒ (pr1 ∪ pr2).is_feasible
			c2 := pr1.is_feasible ∧ pr2.is_feasible ⇒ (pr1 ○ pr2).is_feasible
			c3 := pr1.is_feasible ⇒ (pr1 ← c).is_feasible
			Result := c1 ∧ c2 ∧ c3
		ensure
			class
			Result
		end

	p7 (pr: PROGRAM [T]; c1, c2: MML_SET [T]): BOOLEAN
			-- Restriction is commutative.
		note
			status: functional
		do
			Result := ((pr ← c2) ← c1) ~ ((pr ← c1) ← c2)
		ensure
			class
			Result
		end

	p8 (pr: PROGRAM [T]; c1, c2: MML_SET [T]): BOOLEAN
			-- Restriction is commutative.
		note
			status: functional
		do
			Result := ((pr ← c2) ← c1) ~ (pr ← (c1 ∩ c2))
		ensure
			class
			Result
		end

	p9 (pr1, pr2: PROGRAM [T]; c: MML_SET [T]): BOOLEAN
			-- Restriction is commutative.
		note
			status: functional
		do
			Result := ((pr1 ∪ pr2) ← c) ~ ((pr1 ← c) ∪ (pr2 ← c))
		ensure
			class
			Result
		end

	p10 (pr1, pr2: PROGRAM [T]; c: MML_SET [T]): BOOLEAN
			-- Composition absorbs restriction.
			-- This does not hold
			-- Let `pr1 := <{[1, 1], [1, 2]}, {1}>'
			-- Let `pr2 := <{[1, 1], [2, 2]}, {1}>'
			-- Let `c := {2}'
			-- Then `(pr1 ○ pr2) ← c = <{}, {1}>'
			-- But `(pr1 ← c) ○ pr2 = <{}, {}>'
		note
			status: functional
		do
			Result := ((pr1 ○ pr2) ← c) ~ ((pr1 ← c) ○ pr2)
		ensure
			class
			Result
		end

	p11 (pr1, pr2, pr3: PROGRAM [T]): BOOLEAN
			-- Composition distributes left...
		note
			status: functional
		do
			Result := (pr3 ○ (pr1 ∪ pr2)) ~ ((pr3 ○ pr1) ∪ (pr3 ○ pr2))
		ensure
			class
			Result
		end

	p12 (pr1, pr2, pr3: PROGRAM [T]): BOOLEAN
			-- ... and right over choice.
		note
			status: functional
		do
			Result := ((pr1 ∪ pr2) ○ pr3) ~ ((pr1 ○ pr3) ∪ (pr2 ○ pr3))
		ensure
			class
			Result
		end

	p13 (pr: PROGRAM [T]): BOOLEAN
			-- This does not hold
			-- `Skip := <{[1,1], [2,2]}, {1, 2}>'
			-- Counter example: `Skip ○ <{[1,1], [2,2]}, {1}> = <{[1, 1]}, {1}>'
			-- Skip removes parts of the post condition if they unreachable by pre
		local
			l_skip: PROGRAM [T]
		do
			l_skip := {PROGRAM [T]}.skip (pr.state_space)
			Result := (pr ○ l_skip) ~ (l_skip ○ pr) ∧ (l_skip ○ pr) ~ pr
		ensure
			class
			Result
		end

	p14 (pr: PROGRAM [T]): BOOLEAN
		local
			l_fail: PROGRAM [T]
		do
			l_fail := {PROGRAM [T]}.fail (pr.state_space)
			Result := (pr ∪ l_fail) ~ (l_fail ∪ pr) ∧ (l_fail ∪ pr) ~ pr
		ensure
			class
			Result
		end

	p15 (pr: PROGRAM [T]): BOOLEAN
		local
			l_fail: PROGRAM [T]
		do
			l_fail := {PROGRAM [T]}.fail (pr.state_space)
			Result := (pr ○ l_fail) ~ (l_fail ○ pr) ∧ (l_fail ○ pr) ~ l_fail
		ensure
			class
			Result
		end

	p16 (pr: PROGRAM [T]): BOOLEAN
		local
			l_havoc: PROGRAM [T]
		do
			l_havoc := {PROGRAM [T]}.havoc (pr.state_space)
			Result := (pr ∪ l_havoc) ~ (l_havoc ∪ pr) ∧ (l_havoc ∪ pr) ~ l_havoc
		ensure
			class
			Result
		end

	p17 (pr: PROGRAM [T]): BOOLEAN
			-- This does not hold
			-- `pr := <{[1,1], [1,2]}, {1}>'
			-- `havoc := <{[1,1], [1,2], [2,1], [2,2]}, {1,2}>'
			-- precondition of `pr ○ havoc' is `{1}'
			-- precondition of `havoc ← pr.pre'  is `{1, 2}'
		local
			l_havoc: PROGRAM [T]
		do
			l_havoc := {PROGRAM [T]}.havoc (pr.state_space)
			Result := (pr ○ l_havoc) ~ (l_havoc ← pr.pre)
		ensure
			class
			Result
		end

	p18 (pr: PROGRAM [T]; c: MML_SET [T]): BOOLEAN
			-- This does not hold (I think it is the other way around `(pr ← c) ⊆ pr'
			-- `pr := <{[1, 1], [1, 2]}, {1}>'
			-- `c := {2}'
			-- `pr ← c = <{}, {1}> ' pr does not refine this
		do
			Result := pr ⊆ (pr ← c)
		ensure
			class
			Result
		end

	p19 (pr: PROGRAM [T]; c1, c2: MML_SET [T]): BOOLEAN
			-- Order reversal (precondition weakening).
		do
			Result := True
			if c1 ⊆ c2 then
				Result := (pr ← c1) ⊆ (pr ← c2)
			end
		ensure
			class
			Result
		end

	p20 (pr1, pr2: PROGRAM [T]; c: MML_SET [T]): BOOLEAN
			-- Refinement safety
		do
			Result := True
			if pr1 ⊆ pr2 then
				Result := (pr1 ← c) ⊆ (pr2 ← c)
			end
		ensure
			class
			Result
		end

	p21 (pr1, pr2, q1, q2: PROGRAM [T]): BOOLEAN
		do
			Result := True
			if q1 ⊆ pr1 ∧ q2 ⊆ pr2 then
				Result := ((q1 ∪ q1) ⊆ (pr1 ∪ pr2)) ∧ ((q1 ○ q2) ⊆ (pr1 ○ pr2))
			end
		ensure
			class
			Result
		end

feature -- Operations
	choice alias "∪" (pr2: PROGRAM [T]): PROGRAM [T]
			-- Performs like `Current' or like `pr2'
		local
			l_pre: MML_SET [T]
			l_post: MML_RELATION [T, T]
			l_state_space: MML_SET [T]
		do
			l_pre := pre ∪ pr2.pre
			l_post := post ∪ pr2.post
			l_state_space := state_space ∪ pr2.state_space
			create Result.create_with_pre_and_post (l_post, l_pre, l_state_space)
		end

	composition alias "○" (pr2: PROGRAM [T]): PROGRAM [T]
			-- Performs first like `Current' then like `pr2'
		local
			l_pre: MML_SET [T]
			l_post: MML_RELATION [T, T]
			l_state_space: MML_SET [T]
			l_composer: MML_RELATION_COMPOSITION [T, T, T]
		do
			create l_composer
			l_pre := pre ∩ post.inverse.image (pr2.pre)
			l_post := l_composer.compose (post \ pr2.pre, pr2.post)
			l_state_space := state_space
			create Result.create_with_pre_and_post (l_post, l_pre, l_state_space)
		end

	restriction alias "←" (constraint: MML_SET [T]): PROGRAM [T]
			-- Performs first like `Current' on `constraint'
		local
			l_post: MML_RELATION [T, T]
		do
			l_post := post / constraint
			create Result.create_with_pre_and_post (l_post, pre, state_space)
		end

feature -- Theorems and Lemmas

	refinment_is_reflexive (pr: PROGRAM [T]): BOOLEAN
		do
--			check assume: should_not_be_needed_1 (post, post.domain) end
			Result := pr ⊆ pr
		ensure
			class
			Result
		end

	refinment_is_transitive (pr1, pr2, pr3: PROGRAM [T]): BOOLEAN
		note
			status: functional
		do
			Result := pr1 ⊆ pr2 ∧ pr2 ⊆ pr3 ⇒ pr1 ⊆ pr3
		ensure
			class
			Result
		end

feature -- helpers
	random_program: PROGRAM [T]
		do
			create Result.default_create
		ensure
			attached Result
		end

feature -- should not be needed
--	should_not_be_needed_1 (rel: MML_RELATION [T, T]; domain_set: MML_SET [T]): BOOLEAN
--		do
--			Result := (rel / domain_set).to_set ⊆ rel.to_set
----			check assume: Result end -- should not be needed
--		ensure
--			(rel / domain_set).to_set ⊆ rel.to_set
--			Result
--		end

--	should_not_be_needed_2 (rel: MML_RELATION [T, T]; domain_1, domain_2: MML_SET [T]): BOOLEAN
--		require
--			domain_1 ⊆ domain_2
--		do
--			Result := (rel / domain_1).to_set ⊆ (rel / domain_2).to_set
--		ensure
--			Result
--		end

--	should_not_be_needed_X (pr1, pr2, pr3: PROGRAM [T]): BOOLEAN
--		require
--			pr3 ⊆ pr2
--			pr2 ⊆ pr1
--		do
--			check pr2.pre ⊇ pr1.pre end
--			check p1 (pr1, pr3) end
--			check p2 (pr1, pr3) end
----			check p3 (pr1, pr3) end

--			check (pr3.post / pr2.pre).to_set ⊆ pr2.post.to_set end
--			check pr3.pre ⊇ pr2.pre end
--			check pr2.pre ⊇ pr1.pre end
--			check pr3.pre ⊇ pr1.pre end
--			check (pr3.post / pr1.pre).to_set ⊆ (pr3.post / pr2.pre).to_set end
--			check (pr3.post / pr1.pre).to_set ⊆ pr2.post.to_set end
----			check ∀r: pr3.post ¦ r.left  end
--			check (pr2.post / pr1.pre).to_set ⊆ pr1.post.to_set end
--			check (pr3.post / pr1.pre).to_set ⊆ pr1.post.to_set end
--			Result := (pr3.post / pr1.pre).to_set ⊆ pr1.post.to_set

--		ensure
--			pr2.pre ⊇ pr1.pre ⇒ Result
--			Result
--		end

invariant
	precondition_is_in_state_space: pre ⊆ state_space
	domain_of_postcondition_is_in_state_space: post.domain ⊆ state_space
	range_of_postcondition_is_in_state_space: post.range ⊆ state_space

--	snbn1: should_not_be_needed_1 (post, post.domain)
--	snbn2: should_not_be_needed_1 (post, pre)

end
