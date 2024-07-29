note
	description: "Creating the powerset of a set."
	author: "Reto Weber"
	date: "$Date$"
	revision: "$Revision$"

class
	POWERSET [T -> ANY]

feature
	from_set (set: MML_SET [T]): MML_SET [MML_SET [T]]
		local
			elem: T
			elem_set: MML_SET [T]
			elem_set_of_sets: MML_SET [MML_SET [T]]
		do
			if set.count = 0 then
				create Result.singleton (create {MML_SET [T]}.default_create)
			else
				elem := set.any_item
				create elem_set.singleton (elem)
				create elem_set_of_sets.singleton (elem_set)
				Result := from_set (set - elem_set) ∪ add_element_to_each_set (from_set (set - elem_set), elem) ∪ elem_set_of_sets
			end
		ensure
			class
		end

	all_n_combinations (n: INTEGER; set: MML_SET [T]): MML_SET [MML_SET [T]]
			-- Without repetition
		local
			elem: T
			elem_set: MML_SET [T]
			elem_set_of_sets: MML_SET [MML_SET [T]]
		do
			if set.count = 0 then
				create Result.default_create
--				create Result.singleton (create {MML_SET [T]}.singleton (set.any_item))
			elseif n = 1 then
				elem := set.any_item
				create elem_set.singleton (elem)
				create elem_set_of_sets.singleton (elem_set)
				Result := elem_set_of_sets ∪ all_n_combinations (1, set - elem_set)
			else
				elem := set.any_item
				create elem_set.singleton (elem)
				Result := add_element_to_each_set (all_n_combinations (n - 1, set - elem_set), elem) ∪ all_n_combinations (n, set - elem_set)
			end
		ensure
			class
		end

feature {NONE} -- convinience
	add_element_to_each_set (set_of_sets: MML_SET [MML_SET [T]]; elem: T): MML_SET [MML_SET [T]]
		local
			step_1: ARRAY [MML_SET [T]]
			step_2: ARRAY [ARRAY [T]]
			temp_set: MML_SET [T]
			i: INTEGER
		do
				-- first convert the set_of_sets to an array of arrays
			step_1 := set_of_sets.to_array
			create step_2.make_filled (create {ARRAY [T]}.make_empty, 1, step_1.count)
			from i := 1
			until i > step_1.count
			loop
				step_2 [i] := step_1 [i].to_array
				i := i + 1
			end

				-- fill the result with the sets each has the element added to it
			from i := 1; create Result
			until i > step_2.count
			loop
				create temp_set.make_from_array (step_2 [i])
				Result := Result & (temp_set & elem)
				i := i + 1
			end
		ensure
			class
		end

end
