note
	description: "Summary description for {PROGRAM}."
	author: ""
	date: "$Date$"
	revision: "$Revision$"

--	explicit: contracts

class
	PROGRAM [T -> ANY]

inherit
	ANY
		redefine
			default_create,
			out
		end

create
	default_create, create_with_pre_and_post

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
	is_equivalent (other: like Current): BOOLEAN
		do
			Result := pre = other.pre ∧ post = other.post
		ensure
			Result = (pre = other.pre ∧ post = other.post)
			same_pre: Result ⇒ pre = other.pre
			same_post: Result ⇒ post = other.post
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
		end

	p2 (refinee, refiner: PROGRAM [T]): BOOLEAN
			-- Weakening
		note
			status: functional
		do
			Result := refiner.pre ⊇ refinee.pre
		end

	p3 (refinee, refiner: PROGRAM [T]): BOOLEAN
			-- Strengthening
		note
			status: functional
		do
			Result := (refiner.post / refinee.pre).to_set ⊆ refinee.post.to_set
		end

	p4: BOOLEAN
			-- Refinment is a preorder
		note
			status: functional
		do
			Result := lemma_refinment_is_reflexive ∧ lemma_is_transitive
		ensure
			Result
		end

	p5 (implementation: PROGRAM [T]): BOOLEAN
			-- A specification/program having an implementation is feasible.
		note
			status: functional
		do
			Result := implementation.implements (Current) ⇒ Current.is_feasible
		ensure
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
		do
			l_pre := pre ∩ post.inverse.image (pr2.pre)
			l_post := {MML_RELATION_COMPOSITION [T, T, T]}.compose (post \ pr2.pre, pr2.post)
			l_state_space := state_space
			create Result.create_with_pre_and_post (l_post, l_pre, l_state_space)
		end

	restriction alias "→" (constraint: MML_SET [T]): PROGRAM [T]
			-- Performs first like `Current' on `constraint'
		local
			l_post: MML_RELATION [T, T]
		do
			l_post := post / constraint
			create Result.create_with_pre_and_post (l_post, pre, state_space)
		end

feature -- Theorems and Lemmas

	lemma_refinment_is_reflexive: BOOLEAN
		require
			is_wrapped
		do
			check assume: should_not_be_needed_1 (post, post.domain) end
			Result := Current ⊆ Current
		ensure
			Current ⊆ Current
			Result = True
		end

	lemma_is_transitive: BOOLEAN
		note
			status: functional
		local
			a, b, c: PROGRAM [T]
		do
			a := random_program
			b := random_program
			c := random_program
			Result := a ⊆ b ∧ b ⊆ c ⇒ a ⊆ c
		ensure
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
	should_not_be_needed_1 (rel: MML_RELATION [T, T]; domain_set: MML_SET [T]): BOOLEAN
		do
			Result := (rel / domain_set).to_set ⊆ rel.to_set
--			check assume: Result end -- should not be needed
		ensure
			(rel / domain_set).to_set ⊆ rel.to_set
			Result
		end

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
