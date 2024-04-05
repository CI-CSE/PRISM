note
	description: "Create all relation for a set of elements."
	author: "Reto Weber"
	date: "$Date$"
	revision: "$Revision$"

class
	POWERRELATION [T -> ANY]
feature
	from_set (set: MML_SET [T]): MML_SET [MML_RELATION [T, T]]
		local
			all_relations: MML_SET [MML_PAIR [T, T]]
			all_post_conditions_as_set: MML_SET [MML_SET [MML_PAIR [T, T]]]
			i: INTEGER
		do
			create Result.default_create
			all_relations := {PROGRAM [T]}.havoc (set).post.to_set
			all_post_conditions_as_set := {POWERSET [MML_PAIR [T, T]]}.from_set (all_relations)

			create Result.default_create
			from i := 1
			until i > all_post_conditions_as_set.count
			loop
				Result := Result & create {MML_RELATION [T, T]}.make_from_set (all_post_conditions_as_set.to_array [i])
				i := i + 1
			end

		ensure
			class
		end
end
