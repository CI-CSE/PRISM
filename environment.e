note
	description: "top (Theory of Programs) application root class"
	date: "$Date$"
	revision: "$Revision$"

class
	ENVIRONMENT

create
	make

feature {NONE} -- Initialization

	make
		local
			p1, p2, res: PROGRAM [INTEGER]
			pre, state_space: MML_SET [INTEGER]
			post: MML_RELATION [INTEGER, INTEGER]
		do

			create pre.make_from_array (<<1>>)
			create state_space.make_from_array (<<1, 2>>)
			create post.make_from_arrays (<<1, 1>>, <<1, 2>>)
			create p1.create_with_pre_and_post (post, pre, state_space)
			print (p1.out)

			create pre.make_from_array (<<1>>)
			create state_space.make_from_array (<<1, 2>>)
			create post.make_from_arrays (<<1, 2>>, <<1, 2>>)
			create p2.create_with_pre_and_post (post, pre, state_space)

			res := p1 ○ p2

		end

end
