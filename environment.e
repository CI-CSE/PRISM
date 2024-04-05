note
	description: "top (Theory of Programs) application root class"
	author: "Reto Weber"
	date: "$Date$"
	revision: "$Revision$"

class
	ENVIRONMENT

create
	make

feature {NONE} -- Initialization

	make
		local
			state_space: MML_SET [INTEGER]
		do
			create state_space.make_from_array (<<1, 2>>)
			do_systematic_checks (state_space)
		end

	do_manual_example
		local
			p1, p2, res: PROGRAM [INTEGER]
			pre, state_space, c1, c2, c3: MML_SET [INTEGER]
			post: MML_RELATION [INTEGER, INTEGER]
		do
			create state_space.make_from_array (<<1, 2>>)

			create pre.make_from_array (<<1>>)
			create post.make_from_arrays (<<1, 1>>, <<1, 2>>)
			create p1.create_with_pre_and_post (post, pre, state_space)

			create pre.make_from_array (<<1>>)
			create post.make_from_arrays (<<1, 2>>, <<1, 2>>)
			create p2.create_with_pre_and_post (post, pre, state_space)

			create c1.make_from_array (<<1>>)
			create c2.make_from_array (<<2>>)
			create c3.make_from_array (<<1, 2>>)

			res := p1 ○ p2
			print (p1.out + " ○ " + p2.out + " = " + res.out + "%N")

			print ("FAIL: " + {PROGRAM [INTEGER]}.fail (state_space).out + "%N")

			print ("HAVOC: " + {PROGRAM [INTEGER]}.havoc (state_space).out + "%N")

			print ("SKIP: " + {PROGRAM [INTEGER]}.skip (state_space).out + "%N")

			do_one_program_checks (p1)
			do_one_program_checks (p2)
			do_one_program_checks (res)

			do_one_program_checks_with_one_constraint (p1, c1)
			do_one_program_checks_with_one_constraint (p1, c2)
			do_one_program_checks_with_one_constraint (p1, c3)

			do_one_program_checks_with_one_constraint (p2, c1)
			do_one_program_checks_with_one_constraint (p2, c2)
			do_one_program_checks_with_one_constraint (p2, c3)

			do_one_program_checks_with_one_constraint (res, c1)
			do_one_program_checks_with_one_constraint (res, c2)
			do_one_program_checks_with_one_constraint (res, c3)

			do_one_program_checks_with_two_constraints (p1, c1, c2)
			do_one_program_checks_with_two_constraints (p1, c1, c3)
			do_one_program_checks_with_two_constraints (p1, c2, c3)

			do_one_program_checks_with_two_constraints (p2, c1, c2)
			do_one_program_checks_with_two_constraints (p2, c1, c3)
			do_one_program_checks_with_two_constraints (p2, c2, c3)

			do_one_program_checks_with_two_constraints (res, c1, c2)
			do_one_program_checks_with_two_constraints (res, c1, c3)
			do_one_program_checks_with_two_constraints (res, c2, c3)

			do_two_program_checks (p1, p2)
			do_two_program_checks (p1, res)
			do_two_program_checks (p2, res)

			do_two_program_checks_with_one_constraint (p1, p2, c1)
			do_two_program_checks_with_one_constraint (p1, p2, c2)
			do_two_program_checks_with_one_constraint (p1, p2, c3)

			do_two_program_checks_with_one_constraint (p1, res, c1)
			do_two_program_checks_with_one_constraint (p1, res, c2)
			do_two_program_checks_with_one_constraint (p1, res, c3)

			do_two_program_checks_with_one_constraint (res, p2, c1)
			do_two_program_checks_with_one_constraint (res, p2, c2)
			do_two_program_checks_with_one_constraint (res, p2, c3)

			do_three_program_checks (p1, p2, res)
		end

	do_systematic_checks (state_space: MML_SET [INTEGER])
		local
			all_state_sets: MML_SET [MML_SET [INTEGER]]
			all_post_conditions: MML_SET [MML_RELATION [INTEGER, INTEGER]]
			all_programs: MML_SET [PROGRAM [INTEGER]]
			all_combinations: ARRAY [MML_SET [PROGRAM [INTEGER]]]
			all_constraint_combinations: ARRAY [MML_SET [MML_SET [INTEGER]]]
			i, j: INTEGER

			all_combinations_set: MML_SET [MML_SET [PROGRAM [INTEGER]]]
			all_constraint_combinations_set: MML_SET [MML_SET [MML_SET [INTEGER]]]
		do
			all_state_sets := {POWERSET [INTEGER]}.from_set (state_space)
			all_post_conditions := {POWERRELATION [INTEGER]}.from_set (state_space)
			all_programs := {POWERPROGRAM [INTEGER]}.from_state_space (state_space)
			-- |pre|=2^S,  |post|=|pre|^S  |program|=|pre|*|post| = 2^(S*(S+1))   S state programs
			-- |pre|=4,    |post|=16       |program|=64                           two state programs
			-- |pre|=8,    |post|=512      |program|=4096                         three state programs
			-- |pre|=16,   |post|=65536    |program|=1048576                      four state programs


			-- Do 1 Program checks
			all_combinations_set := {POWERSET [PROGRAM [INTEGER]]}.all_n_combinations (1, all_programs)
			all_combinations := all_combinations_set.to_array
			from i := 1
			until i > all_combinations.count
			loop
				check attached all_combinations [i].to_array as progs then
					do_one_program_checks (progs [1])
				end
				i := i + 1
			end


			-- Do 2 Program checks
			all_combinations_set := {POWERSET [PROGRAM [INTEGER]]}.all_n_combinations (2, all_programs)
			all_combinations := all_combinations_set.to_array
			from i := 1
			until i > all_combinations.count
			loop
				check attached all_combinations [i].to_array as progs then
					do_two_program_checks (progs [1], progs [2])
				end
				i := i + 1
			end


			-- Do 1 Program 2 conditions checks
			all_combinations_set := {POWERSET [PROGRAM [INTEGER]]}.all_n_combinations (1, all_programs)
			all_combinations := all_combinations_set.to_array
			all_constraint_combinations_set := {POWERSET [MML_SET [INTEGER]]}.all_n_combinations (2, all_state_sets)
			all_constraint_combinations := all_constraint_combinations_set.to_array
			from i := 1
			until i > all_combinations.count
			loop
				check attached all_combinations [i].to_array as progs then
					from j := 1
					until j > all_constraint_combinations.count
					loop
						check attached all_constraint_combinations [j].to_array as constraints then
							do_one_program_checks_with_two_constraints (progs [1], constraints [1], constraints [2])
						end
						j := j + 1
					end
				end
				i := i + 1
			end

			-- Do 3 Program checks
			all_combinations_set := {POWERSET [PROGRAM [INTEGER]]}.all_n_combinations (3, all_programs)
			all_combinations := all_combinations_set.to_array
			from i := 1
			until i > all_combinations.count
			loop
				check attached all_combinations [i].to_array as progs then
					do_three_program_checks (progs [1], progs [2], progs [3])
				end
				i := i + 1
			end

			-- Do 4 Program checks
			all_combinations_set := {POWERSET [PROGRAM [INTEGER]]}.all_n_combinations (4, all_programs)
			all_combinations := all_combinations_set.to_array
			from i := 1
			until i > all_combinations.count
			loop
				check attached all_combinations [i].to_array as progs then
					do_four_program_checks (progs [1], progs [2], progs [3], progs [4])
				end
				i := i + 1
			end

		end

	do_one_program_checks (pr: PROGRAM [INTEGER])
		do
			check {PROGRAM [INTEGER]}.p4 (pr, pr, pr) end
			check {PROGRAM [INTEGER]}.p5 (pr, pr) end
--			check {PROGRAM [INTEGER]}.p13 (pr) end  -- This does not hold in general
			check {PROGRAM [INTEGER]}.p14 (pr) end
			check {PROGRAM [INTEGER]}.p15 (pr) end
			check {PROGRAM [INTEGER]}.p16 (pr) end
--			check {PROGRAM [INTEGER]}.p17 (pr) end  -- This does not hold in general
		end

	do_one_program_checks_with_one_constraint (pr: PROGRAM [INTEGER]; c: MML_SET [INTEGER])
		do
--			check {PROGRAM [INTEGER]}.p18 (pr, c) end -- This does not hold
		end

	do_one_program_checks_with_two_constraints (pr: PROGRAM [INTEGER]; c1, c2: MML_SET [INTEGER])
		do
			check {PROGRAM [INTEGER]}.p7 (pr, c1, c2) end
			check {PROGRAM [INTEGER]}.p7 (pr, c2, c1) end
			check {PROGRAM [INTEGER]}.p8 (pr, c1, c2) end
			check {PROGRAM [INTEGER]}.p8 (pr, c2, c1) end
			check {PROGRAM [INTEGER]}.p19 (pr, c1, c2) end
			check {PROGRAM [INTEGER]}.p19 (pr, c2, c1) end
		end

	do_two_program_checks (pr1, pr2: PROGRAM [INTEGER])
		do
			check {PROGRAM [INTEGER]}.p5 (pr1, pr2) end
			check {PROGRAM [INTEGER]}.p5 (pr2, pr1) end
		end

	do_two_program_checks_with_one_constraint (pr1, pr2: PROGRAM [INTEGER]; c: MML_SET [INTEGER])
		do
--			check {PROGRAM [INTEGER]}.p6 (pr1, pr2, c) end -- This does not hold in general
--			check {PROGRAM [INTEGER]}.p6 (pr2, pr1, c) end
			check {PROGRAM [INTEGER]}.p9 (pr1, pr2, c) end
			check {PROGRAM [INTEGER]}.p9 (pr2, pr1, c) end
--			check {PROGRAM [INTEGER]}.p10 (pr1, pr2, c) end -- This does not hold in general
--			check {PROGRAM [INTEGER]}.p10 (pr2, pr1, c) end -- This does not hold in general
			check {PROGRAM [INTEGER]}.p20 (pr1, pr2, c) end
			check {PROGRAM [INTEGER]}.p20 (pr2, pr1, c) end
		end

	do_three_program_checks (pr1, pr2, pr3: PROGRAM [INTEGER])
			-- Check the theorems for these instances without repeating themself
		do
			check {PROGRAM [INTEGER]}.p4 (pr1, pr2, pr3) end
			check {PROGRAM [INTEGER]}.p4 (pr1, pr3, pr2) end
			check {PROGRAM [INTEGER]}.p4 (pr2, pr1, pr3) end
			check {PROGRAM [INTEGER]}.p4 (pr2, pr3, pr1) end
			check {PROGRAM [INTEGER]}.p4 (pr3, pr1, pr2) end
			check {PROGRAM [INTEGER]}.p4 (pr3, pr2, pr1) end

			check {PROGRAM [INTEGER]}.p11 (pr1, pr2, pr3) end
			check {PROGRAM [INTEGER]}.p11 (pr1, pr3, pr2) end
			check {PROGRAM [INTEGER]}.p11 (pr2, pr1, pr3) end
			check {PROGRAM [INTEGER]}.p11 (pr2, pr3, pr1) end
			check {PROGRAM [INTEGER]}.p11 (pr3, pr1, pr2) end
			check {PROGRAM [INTEGER]}.p11 (pr3, pr2, pr1) end

			check {PROGRAM [INTEGER]}.p12 (pr1, pr2, pr3) end
			check {PROGRAM [INTEGER]}.p12 (pr1, pr3, pr2) end
			check {PROGRAM [INTEGER]}.p12 (pr2, pr1, pr3) end
			check {PROGRAM [INTEGER]}.p12 (pr2, pr3, pr1) end
			check {PROGRAM [INTEGER]}.p12 (pr3, pr1, pr2) end
			check {PROGRAM [INTEGER]}.p12 (pr3, pr2, pr1) end
		end

	do_four_program_checks (pr1, pr2, pr3, pr4: PROGRAM [INTEGER])
		do
			check {PROGRAM [INTEGER]}.p21 (pr1, pr2, pr3, pr4) end
			check {PROGRAM [INTEGER]}.p21 (pr1, pr2, pr4, pr3) end
			check {PROGRAM [INTEGER]}.p21 (pr1, pr3, pr2, pr4) end
			check {PROGRAM [INTEGER]}.p21 (pr1, pr3, pr4, pr2) end
			check {PROGRAM [INTEGER]}.p21 (pr1, pr4, pr2, pr3) end
			check {PROGRAM [INTEGER]}.p21 (pr1, pr4, pr3, pr2) end

			check {PROGRAM [INTEGER]}.p21 (pr2, pr1, pr3, pr4) end
			check {PROGRAM [INTEGER]}.p21 (pr2, pr1, pr4, pr3) end
			check {PROGRAM [INTEGER]}.p21 (pr2, pr3, pr1, pr4) end
			check {PROGRAM [INTEGER]}.p21 (pr2, pr3, pr4, pr1) end
			check {PROGRAM [INTEGER]}.p21 (pr2, pr4, pr1, pr3) end
			check {PROGRAM [INTEGER]}.p21 (pr2, pr4, pr3, pr1) end

			check {PROGRAM [INTEGER]}.p21 (pr3, pr1, pr2, pr4) end
			check {PROGRAM [INTEGER]}.p21 (pr3, pr1, pr4, pr2) end
			check {PROGRAM [INTEGER]}.p21 (pr3, pr2, pr1, pr4) end
			check {PROGRAM [INTEGER]}.p21 (pr3, pr2, pr4, pr1) end
			check {PROGRAM [INTEGER]}.p21 (pr3, pr4, pr1, pr2) end
			check {PROGRAM [INTEGER]}.p21 (pr3, pr4, pr2, pr1) end

			check {PROGRAM [INTEGER]}.p21 (pr4, pr1, pr2, pr3) end
			check {PROGRAM [INTEGER]}.p21 (pr4, pr1, pr3, pr2) end
			check {PROGRAM [INTEGER]}.p21 (pr4, pr2, pr1, pr3) end
			check {PROGRAM [INTEGER]}.p21 (pr4, pr2, pr3, pr1) end
			check {PROGRAM [INTEGER]}.p21 (pr4, pr3, pr1, pr2) end
			check {PROGRAM [INTEGER]}.p21 (pr4, pr3, pr2, pr1) end

		end

end
