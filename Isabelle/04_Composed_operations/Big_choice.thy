theory Big_choice
  imports 
"../T_03_Basic_programs"
begin
section \<open>Big choice for top\<close>

lemma Choice_prop_1: "\<Union>\<^sub>p (xs@[x]) \<equiv>\<^sub>p x \<union>\<^sub>p \<Union>\<^sub>p xs"
proof (induction xs)
  case Nil
  then show ?case
    by (simp add: equiv_is_reflexive)
next
  case (Cons a xs)
  assume IH: "\<Union>\<^sub>p (xs @ [x]) \<equiv>\<^sub>p x \<union>\<^sub>p \<Union>\<^sub>p xs"
  have l1: "\<Union>\<^sub>p ((a # xs) @ [x]) \<equiv>\<^sub>p a \<union>\<^sub>p \<Union>\<^sub>p (xs @ [x])"
    using equiv_is_reflexive by fastforce
  have l2: "a \<union>\<^sub>p \<Union>\<^sub>p (xs @ [x]) \<equiv>\<^sub>p a \<union>\<^sub>p (x \<union>\<^sub>p \<Union>\<^sub>p xs)"
    by (simp add: IH equiv_is_reflexive equivalence_is_maintained_by_choice)
  have l2: "a \<union>\<^sub>p \<Union>\<^sub>p (xs @ [x]) \<equiv>\<^sub>p x \<union>\<^sub>p (a \<union>\<^sub>p \<Union>\<^sub>p xs)"
    by (metis choice_assoc_1 choice_commute l2)
  then show "\<Union>\<^sub>p ((a # xs) @ [x]) \<equiv>\<^sub>p x \<union>\<^sub>p \<Union>\<^sub>p (a # xs)"
    by simp
qed

lemma Union_prop_1: "\<Union>\<^sub>s (xs@[x]) = x \<union> \<Union>\<^sub>s xs"
proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs)
  assume IH: "\<Union>\<^sub>s (xs @ [x]) = x \<union> \<Union>\<^sub>s xs"
  have l1: "\<Union>\<^sub>s ((a # xs) @ [x]) = a \<union> \<Union>\<^sub>s (xs @ [x])"
    using equiv_is_reflexive by fastforce
  have l2: "a \<union> \<Union>\<^sub>s (xs @ [x]) = a \<union> (x \<union> \<Union>\<^sub>s xs)"
    by (simp add: IH equiv_is_reflexive equivalence_is_maintained_by_choice)
  have l2: "a \<union> \<Union>\<^sub>s (xs @ [x]) = x \<union> (a \<union> \<Union>\<^sub>s xs)"
    by (simp add: inf_sup_aci(7) l2)
  then show "\<Union>\<^sub>s ((a # xs) @ [x]) = x \<union> \<Union>\<^sub>s (a # xs)"
    by simp
qed
end