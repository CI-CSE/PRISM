note
	description: "Produces all programs for a given state space. (WARNING: VERY EXPONENTIAL)"
	author: "Reto Weber"
	date: "$Date$"
	revision: "$Revision$"

class
	POWERPROGRAM [T -> ANY]

feature
	from_state_space (a_state_space: MML_SET [T]): MML_SET [PROGRAM [T]]
		local
			pre_set_as_arr: ARRAY [MML_SET [T]]
			post_set_as_arr: ARRAY [MML_RELATION [T, T]]
			pre_ind, post_ind: INTEGER
		do
			create Result.default_create
			pre_set_as_arr := {POWERSET [T]}.from_set (a_state_space).to_array
			post_set_as_arr := {POWERRELATION [T]}.from_set (a_state_space).to_array

			from pre_ind := 1
			until pre_ind > pre_set_as_arr.count
			loop
				from post_ind := 1
				until post_ind > post_set_as_arr.count
				loop
					Result := Result & create {PROGRAM [T]}.create_with_pre_and_post (post_set_as_arr [post_ind], pre_set_as_arr [pre_ind], a_state_space)
					post_ind := post_ind + 1
				end
				pre_ind := pre_ind + 1
			end
		ensure
			class
		end

end
