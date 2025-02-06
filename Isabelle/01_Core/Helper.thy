theory Helper
  imports Main Definitions
begin
section \<open>Helper for top\<close>

theorem rel_id_prop: "Field a \<subseteq> C \<Longrightarrow> a O Id_on C = a"
  by (auto simp: Field_def relcomp_unfold Id_on_def)


theorem list_comp_prop_1: "\<forall>p. [p i. i \<leftarrow> [0..((int (Suc n)))]] = [p i. i \<leftarrow> [0..(int n)]] @ [p ((int (Suc n)))]"
    apply (induction n)
    apply (simp add: upto_rec2)
  by (simp add: upto_rec2)

theorem orig_is_permutation_1: "List.member (insert_all x xs) (x#xs)"
  apply (induction xs)
  by (auto simp: member_rec(1))

theorem permutation_reflexive:  "List.member (permutations xs) xs"
  apply (induction xs)
  apply (simp add: member_rec(1))
  apply (auto simp: member_def)
  by (metis insert_all.simps(1) insert_all.simps(2) list.set_intros(1) permutations.elims)

lemma l1: "set (insert_all x (ps)) \<noteq> {}"
  apply (cases "ps = []")
  apply auto
    by (metis insert_all.simps(2) neq_Nil_conv)

lemma l2: "x#xs \<in> set (insert_all x xs)" 
  apply (induction xs arbitrary: x)
  by auto

lemma l3: "xs@[x] \<in> set (insert_all x xs)" 
  apply (induction xs arbitrary: x)
  by auto

lemma l4: "a@x#b \<in> set (insert_all x (a@b))" 
  apply (induction a arbitrary: x b)
  apply auto
  by (simp add: l2)

primrec h_hd :: "'a list \<Rightarrow> 'a list" where
  hd_base: "h_hd [] = []" |
  hd_step: "h_hd (x#xs) = [x]"

primrec h_tl :: "'a list \<Rightarrow> 'a list" where
  tl_base: "h_tl [] = []" |
  tl_step: "h_tl (x#xs) = xs"

lemma l5: "p \<in> set (insert_all x (a # xs)) \<Longrightarrow> (hd p = x) \<or> (hd p = a)" by auto
lemma l5_2: "p \<in> set (insert_all x (a # xs)) \<Longrightarrow> (h_hd p = [x]) \<or> (h_hd p = [a])" by auto

lemma l6: "h_hd p = [x] \<Longrightarrow> hd p = x"
  by (metis hd_Cons_tl hd_base hd_step list.distinct(1) list.inject)

lemma l7: "h_tl p = x \<equiv> tl p = x"
  by (smt (verit) list.collapse list.sel(2) tl_base tl_step)

lemma l8: "(h_hd p)@(h_tl p) = p"
  apply (induction p)
  by auto

lemma l9: "a#p \<in> set (insert_all x (a # xs)) \<Longrightarrow> p \<in> set (insert_all x xs)"
proof -
  assume a1: "a#p \<in> set (insert_all x (a # xs))"
  have def_insert_all: "insert_all x (a # xs) = (x#a#xs) # (map (\<lambda>zs. a#zs) (insert_all x xs))" by simp
  with a1 have "a#p \<in> set ((x#a#xs) # (map (\<lambda>zs. a#zs) (insert_all x xs)))" by simp
  hence l1: "a#p = x#a#xs \<or> a#p \<in> set (map (\<lambda>zs. a#zs) (insert_all x xs))" by simp
  thus "p \<in> set (insert_all x xs)"
  proof
    assume "a#p = x#a#xs"
    hence "p = a#xs" by simp
    thus ?thesis using l1 l2 by fastforce
  next
    assume "a#p \<in> set (map (\<lambda>zs. a#zs) (insert_all x xs))"
    then obtain ys where ys_def: "ys \<in> set (insert_all x xs)" and "a#p = a#ys" by auto
    hence "\<exists>ys. ys \<in> set (insert_all x xs) \<and> p = ys" by simp
    thus ?thesis by simp
  qed
qed

lemma l10: "p \<in> set (insert_all x xs) \<Longrightarrow> \<exists>a b. a@x#b=p"
proof (induction xs arbitrary: x p)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  assume IH: "\<And> x' p'. p' \<in> set (insert_all x' xs) \<Longrightarrow> \<exists>a b. a @ x' # b = p'"
  assume a1: "p \<in> set (insert_all x (a # xs))"
  then show "\<exists>a b. a @ x # b = p"
  proof (cases "h_hd p = [x]")
    case True
    have "(h_hd p)@(h_tl p) = p" by (simp add: l8)
    then show ?thesis by (metis True append_Cons self_append_conv2) 
  next
    case False
    have "h_hd p = [a]" using l5_2 a1 by (metis False)
    then obtain p_tl where o1: "p_tl = h_tl p" by auto
    have "p_tl \<in> set (insert_all x xs)" using o1 a1 l9 by (metis \<open>h_hd p = [a]\<close> append_Cons append_self_conv2 l8) 
    then have "\<exists>a b. a @ x # b = p_tl" using IH by auto
    then show "\<exists>a b. a @ x # b = p" by (metis append.assoc l8 o1) 
  qed
qed

lemma l11: "p \<in> set (insert_all x ps) \<Longrightarrow> x \<in> set p"
proof (induction ps arbitrary: x)
  case Nil
  then show ?case by auto
next
  case (Cons a ps)
  assume IH: "\<And>x'. p \<in> set (insert_all x' ps) \<Longrightarrow> x' \<in> set p"
  assume a1: "p \<in> set (insert_all x (a # ps))"
  then show "x \<in> set p" using l10 by fastforce
qed

lemma l12: "y \<in> set p \<Longrightarrow> p \<in> set (insert_all x (a # ps)) \<Longrightarrow> y \<noteq> a \<Longrightarrow> p' \<in> set (insert_all x ps) \<Longrightarrow> y \<in> set p'"
proof (induction ps arbitrary: x a p p' y)
  case Nil
  then show ?case by auto
next
  case (Cons b ps')
  assume IH: "\<And>x a p p' y. y \<in> set p \<Longrightarrow> p \<in> set (insert_all x (a # ps')) \<Longrightarrow> y \<noteq> a \<Longrightarrow> p' \<in> set (insert_all x ps') \<Longrightarrow> y \<in> set p'"
  assume a1: "y \<in> set p"
  assume a2: "p \<in> set (insert_all x (a # (b # ps')))"
  assume a3: "y \<noteq> a"
  assume a4: "p' \<in> set (insert_all x (b # ps'))"

  from a2 have "p = x # a # b # ps' \<or> p \<in> set (map (\<lambda>zs. a # zs) (insert_all x (b # ps')))" by simp
  thus "y \<in> set p'"
  proof
    assume "p = x # a # b # ps'"
    with a1 a3 have "y = x \<or> y = b \<or> y \<in> set ps'" by auto
    thus ?thesis
    proof
      assume "y = x"
      with a4 show ?thesis using l11 by metis
    next
      assume "y = b \<or> y \<in> set ps'"
      with a4 show ?thesis apply auto
        by (meson IH l2 list.set_intros(2))
    qed
  next
    assume h1: "p \<in> set (map (\<lambda>zs. a # zs) (insert_all x (b # ps')))"
    then obtain q where q_def: "q \<in> set (insert_all x (b # ps'))" and p_def: "p = a # q" by auto
    with a1 a3 have "y \<in> set q" by auto
    with q_def show ?thesis
    proof (cases "q = x # b # ps'")
      case True
      with \<open>y \<in> set q\<close> have "y = x \<or> y = b \<or> y \<in> set ps'" by auto
      thus ?thesis
      proof
        assume "y = x"
        with a4 show ?thesis using l11 by metis
      next
        assume "y = b \<or> y \<in> set ps'"
        with a4 show ?thesis apply auto
          by (meson IH \<open>y \<in> set q\<close> q_def)
      qed
    next
      case False
      with q_def obtain q' where q'_def: "q' \<in> set (insert_all x ps')" and q_def2: "q = b # q'" by auto
      with \<open>y \<in> set q\<close> have "y = b \<or> y \<in> set q'" by auto
      thus ?thesis
      proof
        assume "y = b"
        with a4 show ?thesis by auto
      next
        assume "y \<in> set q'"
        with q'_def a4 show ?thesis
        proof (cases "p' = x # b # ps'")
          case True
          then show ?thesis
            by (metis IH \<open>y \<in> set q\<close> in_set_member l2 member_rec(1) q_def)
        next
          case False
          with a4 obtain p'' where p''_def: "p'' \<in> set (insert_all x ps')" and p'_def: "p' = b # p''" by auto
          with \<open>y \<in> set q'\<close> q'_def show ?thesis using IH
            by (metis \<open>y \<in> set q\<close> list.set_intros(1) list.set_intros(2) q_def)
        qed
      qed
    qed
  qed
qed

lemma l13: "y \<in> set p \<Longrightarrow> p \<in> set (insert_all x ps) \<Longrightarrow> y \<notin> set ps \<Longrightarrow> y = x"proof (induction ps arbitrary: x y p)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  assume IH: "\<And>x y p. y \<in> set p \<Longrightarrow> p \<in> set (insert_all x ps) \<Longrightarrow> y \<notin> set ps \<Longrightarrow> y = x"
  assume a1: "y \<in> set p"
  assume a2: "p \<in> set (insert_all x (a # ps))"
  assume a3: "y \<notin> set (a # ps)"

  from a2 have "p = x # a # ps \<or> p \<in> set (map (\<lambda>zs. a # zs) (insert_all x ps))" by simp
  thus "y = x"
  proof
    assume "p = x # a # ps"
    with a1 a3 show ?thesis by simp
  next
    assume h1: "p \<in> set (map (\<lambda>zs. a # zs) (insert_all x ps))"
    then obtain q where q_def: "q \<in> set (insert_all x ps)" and p_def: "p = a # q" by auto
    from a1 p_def have "y = a \<or> y \<in> set q" by simp
    moreover from a3 have "y \<noteq> a" by simp
    ultimately have "y \<in> set q" by simp
    moreover from a3 have "y \<notin> set ps" by simp
    ultimately show ?thesis using IH q_def by blast
  qed
qed

lemma permutation_symmetric_1: "List.member (permutations xs) p \<Longrightarrow> List.member p y \<Longrightarrow> List.member xs y"
proof (induction xs arbitrary: p y)
  case Nil
  then show ?case by (simp add: List.member_def)
next
  case (Cons x xs)
  assume IH: "\<And>p y. List.member (permutations xs) p \<Longrightarrow> List.member p y \<Longrightarrow> List.member xs y"
  assume a1: "List.member (permutations (x # xs)) p"
  assume a2: "List.member p y"

  from a1 have "List.member (concat (map (insert_all x) (permutations xs))) p" by simp
  then obtain ps where ps_def: "List.member (permutations xs) ps" 
                    and p_def: "List.member (insert_all x ps) p"
    by (auto simp: List.member_def)

  show "List.member (x # xs) y"
  proof (cases "y = x")
    case True
    then show ?thesis by (simp add: member_rec(1))
  next
    case False
    with p_def a2 have "y \<in> set ps \<or> y = x"
      apply (auto simp: List.member_def)
      by (metis l13)
    thus ?thesis
    proof
      assume "y \<in> set ps"
      hence "List.member ps y" by (simp add: List.member_def)
      with IH ps_def show ?thesis
        by (simp add: member_rec(1))
    next
      assume "y = x"
      then show ?thesis
        by (simp add: False)
    qed
  qed
qed

lemma l14: "p \<in> set (insert_all x ps) \<Longrightarrow> \<exists>a b. p = a @ x # b \<and> ps = a @ b"
proof (induction ps arbitrary: p)
  case Nil
  then show ?case by auto
next
  case (Cons y ys)
  assume IH: "\<And>p. p \<in> set (insert_all x ys) \<Longrightarrow> \<exists>a b. p = a @ x # b \<and> ys = a @ b"
  assume "p \<in> set (insert_all x (y # ys))"
  
  then show ?case
  proof (cases "p = x # y # ys")
    case True
    then show ?thesis 
      by (rule_tac x="[]" in exI, rule_tac x="y # ys" in exI, auto)
  next
    case False
    with Cons.prems have "p \<in> set (map (\<lambda>zs. y # zs) (insert_all x ys))" by auto
    then obtain p' where p'_def: "p' \<in> set (insert_all x ys)" and p_def: "p = y # p'"
      by (auto simp: image_iff)
    
    from IH p'_def obtain a b where
      a_b_def: "p' = a @ x # b" "ys = a @ b" by blast
    
    have "p = (y # a) @ x # b"
      by (simp add: a_b_def(1) p_def)
    have p_split: "p = (y # a) @ x # b"
      by (simp add: \<open>p = (y # a) @ x # b\<close>)
    
    have "y # ys = y # (a @ b)" by (simp add: a_b_def)
    
    from p_split `y # ys = y # (a @ b)` 
    show ?thesis
      by (rule_tac x="y # a" in exI, rule_tac x="b" in exI, auto)
  qed
qed

theorem count_invariant: "List.member (permutations xs) p \<Longrightarrow> count_list p y = count_list xs y"
proof (induction xs arbitrary: p)
  case Nil
  then show ?case by (simp add: List.member_def)
next
  case (Cons x xs)
  assume IH: "\<And>p. List.member (permutations xs) p \<Longrightarrow> count_list p y = count_list xs y"
  assume a1: "List.member (permutations (x # xs)) p"

  from a1 have "List.member (concat (map (insert_all x) (permutations xs))) p" by simp
  then obtain ps where ps_def: "List.member (permutations xs) ps" 
                    and p_def: "List.member (insert_all x ps) p"
    by (auto simp: List.member_def)

  from IH ps_def have count_eq: "count_list ps y = count_list xs y" by simp

  from p_def have "\<exists>a b. p = a @ x # b \<and> ps = a @ b"
    by (simp add: in_set_member l14)

  then obtain a b where p_split: "p = a @ x # b" and ps_split: "ps = a @ b" by auto

  have "count_list p y = count_list (a @ x # b) y"
    by (simp add: p_split)
  also have "... = count_list (x # xs) y"
    using \<open>\<exists>a b. p = a @ x # b \<and> ps = a @ b\<close> ab_semigroup_add_class.add_ac(1) count_eq count_list.simps(2) count_list_append p_split by fastforce
  finally show ?case .
qed

theorem permutation_split: "List.member (permutations (x#xs)) xs' \<Longrightarrow> \<exists>a b. a@x#b = xs'"
proof -
  assume "List.member (permutations (x#xs)) xs'"
  then have "xs' \<in> set (permutations (x#xs))" by (simp add: List.member_def)
  then have "xs' \<in> set (concat (map (insert_all x) (permutations xs)))" by simp
  then obtain ps where ps_def: "ps \<in> set (permutations xs)" and xs'_def: "xs' \<in> set (insert_all x ps)"
    by auto

  from xs'_def have "\<exists>a b. xs' = a @ x # b \<and> ps = a @ b"
    by (rule l14)
  then obtain a b where "xs' = a @ x # b" by auto
  then show ?thesis by blast
qed

theorem permutation_size: "List.member (permutations x1) x2 \<Longrightarrow> size x2 = size x1"
proof (induction x1 arbitrary: x2)
  case Nil
  then show ?case 
    by (simp add: List.member_def)
next
  case (Cons a x1)
  assume IH: "\<And>x2. List.member (permutations x1) x2 \<Longrightarrow> size x2 = size x1"
  assume "List.member (permutations (a # x1)) x2"

  then have "x2 \<in> set (concat (map (insert_all a) (permutations x1)))"
    by (simp add: List.member_def)
  then obtain ps where ps_def: "ps \<in> set (permutations x1)" 
                    and x2_def: "x2 \<in> set (insert_all a ps)"
    by auto

  from ps_def have "List.member (permutations x1) ps"
    by (simp add: List.member_def)
  with IH have size_ps: "size ps = size x1" by simp

  from x2_def have "\<exists>b c. x2 = b @ a # c \<and> ps = b @ c"
    by (rule l14)
  then obtain b c where x2_split: "x2 = b @ a # c" and ps_split: "ps = b @ c"
    by auto

  have "size x2 = size (a # x1)"
    using ps_split size_ps x2_split by auto 
  show ?case
    by (simp add: \<open>length x2 = length (a # x1)\<close>)
qed

lemma insert_perm_rel: "x \<in> set (insert_all a xs) \<Longrightarrow> x \<in> set (permutations (a#xs))"
  apply auto
  by (meson in_set_member permutation_reflexive)

lemma insert_all_set_equality: "p1 \<in> set (insert_all x ps) \<Longrightarrow> set p1 = insert x (set ps)"
proof (induction ps arbitrary: p1)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then show ?case
  proof (cases "p1 = x # y # ys")
    case True
    then show ?thesis by simp
  next
    case False
    then have "p1 \<in> set (map (\<lambda>zs. y # zs) (insert_all x ys))"
      using Cons.prems insert_all.simps(2) by auto
    then obtain zs where zs_def: "zs \<in> set (insert_all x ys)" "p1 = y # zs"
      by auto
    have IH: "set zs = insert x (set ys)" using Cons.IH zs_def(1) by simp
    have "set p1 = insert y (set zs)" using zs_def(2) by simp
    also have "... = insert y (insert x (set ys))" using IH by simp
    also have "... = insert x (insert y (set ys))" by auto
    also have "... = insert x (set (y # ys))" by simp
    finally show ?thesis .
  qed
qed

lemma permutation_set_equality: "p1 \<in> set (permutations xs) \<Longrightarrow> set xs = set p1"
proof (induction xs arbitrary: p1)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case 
  proof -
    from Cons.prems have "p1 \<in> set (concat (map (insert_all x) (permutations xs)))"
      by simp
    then obtain ps where ps_def: 
      "ps \<in> set (permutations xs)" "p1 \<in> set (insert_all x ps)"
      by auto

    have "set xs = set ps" using Cons.IH ps_def(1) by simp
    moreover have "set p1 = insert x (set ps)" using ps_def(2)
      by (metis insert_all_set_equality)
    ultimately have "set p1 = insert x (set xs)" by simp
    then show ?thesis by simp
  qed
qed

lemma permutation_set_equality_2: "p1 \<in> set (permutations xs) \<Longrightarrow> p2 \<in> set (permutations xs) \<Longrightarrow> set p1 = set p2"
proof (induction xs arbitrary: p1 p2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case 
  proof -
    from Cons.prems have p1_def: "p1 \<in> set (concat (map (insert_all x) (permutations xs)))"
      by simp
    from Cons.prems have p2_def: "p2 \<in> set (concat (map (insert_all x) (permutations xs)))"
      by simp

    from p1_def obtain ps1 where ps1_def: 
      "ps1 \<in> set (permutations xs)" "p1 \<in> set (insert_all x ps1)"
      by auto
    from p2_def obtain ps2 where ps2_def: 
      "ps2 \<in> set (permutations xs)" "p2 \<in> set (insert_all x ps2)"
      by auto

    have "set ps1 = set ps2" using Cons.IH ps1_def(1) ps2_def(1)
      by blast

    have "set p1 = insert x (set ps1)" using ps1_def(2)
      by (metis insert_all_set_equality)
    moreover have "set p2 = insert x (set ps2)" using ps2_def(2)
      by (metis insert_all_set_equality)
    ultimately show ?thesis using \<open>set ps1 = set ps2\<close> by simp
  qed
qed

lemma permutation_split_set: "x2 \<in> set (permutations (a # x1)) \<Longrightarrow> \<exists>y z. x2 = y @ a # z \<and> y @ z \<in> set (permutations x1)"
proof -
  assume "x2 \<in> set (permutations (a # x1))"
  then have "x2 \<in> set (concat (map (insert_all a) (permutations x1)))"
    by simp
  then obtain ps where ps_def: "ps \<in> set (permutations x1)" and "x2 \<in> set (insert_all a ps)"
    by auto
  from this(2) obtain y z where yz_def: "x2 = y @ a # z" and "ps = y @ z"
    using l14
    by force
  from ps_def this(2) have "y @ z \<in> set (permutations x1)"
    by simp
  with yz_def show ?thesis
    by blast
qed

theorem insert_4: "(xs @ ([x] @ ys)) \<in> set (insert_all x (xs @ ys))"
  using l4 by fastforce

theorem count_eq_member: "List.count_list p y > 0 = List.member p y"
proof (induction p)
  case Nil
  then show ?case by (simp add: member_rec(2))
next
  case (Cons a p)
  assume IH: "(0 < count_list p y) = List.member p y"
  then show "(0 < count_list (a # p) y) = List.member (a # p) y"
  proof (cases "a=y")
    case True
    assume eq: "a=y"
    have l1: "List.member (y # p) y" by (simp add: member_rec(1))
    have l2: "(0 < count_list (y # p) y)" by simp
    then show ?thesis by (auto simp: l1 l2 eq)
  next
    case False
    assume neq: "a \<noteq> y"
    then show ?thesis by (simp add: IH member_rec(1))
  qed
qed

theorem member_invariant: "p \<in> set (permutations xs) \<Longrightarrow> List.member p y \<Longrightarrow> List.member xs y"
  by (metis in_set_member permutation_set_equality)

lemma length_prop_1: "List.member xs x \<Longrightarrow> \<exists>a b. a@[x]@b = xs"
proof (induction xs)
  case Nil
  then show ?case
    by (simp add: member_rec(2)) 
next
  case (Cons a xs)
  assume IH: "List.member xs x \<Longrightarrow> \<exists>a b. a @ [x] @ b = xs"
  assume a1: "List.member (a # xs) x"
  then show ?case
    by (metis Cons_eq_append_conv append_self_conv2 in_set_member split_list_first)
qed

lemma length_prop_2: "count_list (a @ [x] @ b) x = Suc (count_list (a @ b) x)"
proof (induction a)
  case Nil
  then show ?case apply (induction b)
  apply simp
  by (metis Cons_eq_append_conv Suc_eq_plus1 count_list.simps(2))
next
  case (Cons a1 a2)
  assume IH: "count_list (a2 @ [x] @ b) x = Suc (count_list (a2 @ b) x)"
  then show "count_list ((a1 # a2) @ [x] @ b) x = Suc (count_list ((a1 # a2) @ b) x)"
  proof (cases "a1=x")
    case True
    have "count_list ((a1 # a2) @ [x] @ b) x = Suc (count_list ((a2) @ [x] @ b) x)" using True by auto
    moreover have "count_list ((a2) @ [x] @ b) x = Suc (count_list (a2 @ b) x)" using IH by auto
    moreover have "Suc (count_list (a2 @ b) x) = count_list ((a1 # a2) @ b) x" by (simp add: True)
    then show ?thesis using IH calculation(1) by presburger
  next
    case False
    have "count_list ((a1 # a2) @ [x] @ b) x = count_list ((a2) @ [x] @ b) x" using False by auto
    moreover have "... = Suc (count_list (a2 @ b) x)" using IH by auto
    moreover have "... = Suc (count_list ((a1 # a2) @ b) x)" using calculation(1) by auto
    then show ?thesis
      using IH calculation(1) by presburger
  qed
qed

lemma length_prop_3: "x\<^sub>1\<noteq>x\<^sub>2 \<Longrightarrow> xs = a@[x\<^sub>2]@b \<Longrightarrow> count_list (xs) x\<^sub>1 = count_list (a@b) x\<^sub>1"
  by simp

lemma length_prop_4: "x\<^sub>1=x\<^sub>2 \<Longrightarrow> xs = a@[x\<^sub>2]@b \<Longrightarrow> count_list (xs) x\<^sub>1 = Suc (count_list (a@b) x\<^sub>1)"
  by simp

lemma length_prop_5: "\<forall>x\<^sub>1. count_list (a # xs) x\<^sub>1 = count_list (a # xs') x\<^sub>1 \<Longrightarrow> \<forall>x\<^sub>1. count_list (xs) x\<^sub>1 = count_list (xs') x\<^sub>1"
proof -
  assume a1: "\<forall>x\<^sub>1. count_list (a # xs) x\<^sub>1 = count_list (a # xs') x\<^sub>1"
  have l1: "\<forall>x\<^sub>1. x\<^sub>1\<noteq>a \<longrightarrow> count_list (xs) x\<^sub>1 = count_list (xs') x\<^sub>1" using a1 apply auto
    by metis 
  have l2: "count_list (xs) a = count_list (xs') a" using a1 apply auto
    by (meson add_right_cancel) 
  show "\<forall>x\<^sub>1. count_list (xs) x\<^sub>1 = count_list (xs') x\<^sub>1" using l1 l2 by auto
qed

lemma length_prop_6: "\<forall>x\<^sub>1. count_list xs x\<^sub>1 = count_list xs' x\<^sub>1 \<Longrightarrow> length xs = length xs'"
proof (induction xs arbitrary: xs')
  case Nil
  then show ?case
    by (metis Suc_eq_plus1 count_list.simps(1) count_list.simps(2) length_0_conv length_greater_0_conv neq_Nil_conv zero_less_Suc)
next
  case (Cons a xs)
  assume a1: "\<And>xs''. \<forall>x\<^sub>1. count_list xs x\<^sub>1 = count_list xs'' x\<^sub>1 \<Longrightarrow> length xs = length xs''"
  assume a2: "\<forall>x\<^sub>1. count_list (a # xs) x\<^sub>1 = count_list xs' x\<^sub>1"
  have "List.member xs' a"
    by (metis Cons.prems count_eq_member member_rec(1))
  then obtain xs'1 xs'2 where o1: "xs' = xs'1 @ [a] @ xs'2" using length_prop_1
    by metis
  then have "xs' = xs'1 @ a # xs'2" by simp

  hence "length xs' = length xs'1 + 1 + length xs'2" by simp
  moreover have "\<forall>x\<^sub>1. x\<^sub>1 \<noteq> a \<longrightarrow> count_list xs x\<^sub>1 = count_list (xs'1 @ xs'2) x\<^sub>1" using Cons.prems by (metis o1 append_Cons eq_Nil_appendI length_prop_3)
  moreover have "count_list xs a = count_list xs' a - 1" by (metis Suc_eq_plus1 a2 count_list.simps(2) diff_Suc_1)
  moreover have "count_list xs' a = count_list (xs'1 @ xs'2) a + 1" using o1 by auto
  moreover have "count_list xs a = count_list (xs'1 @ xs'2) a" by (simp add: calculation(3) calculation(4))
  moreover have "\<forall>x\<^sub>1. count_list xs x\<^sub>1 = count_list (xs'1 @ xs'2) x\<^sub>1" using calculation(2) calculation(5) by auto
  thus ?case
    by (metis Cons.IH add.assoc add.left_commute calculation(1) length_Cons length_append plus_1_eq_Suc)
qed

theorem length_inv: "x \<in> set (permutations xs) \<Longrightarrow> length x = length xs"
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof -
    from Cons.prems have "x \<in> set (concat (map (insert_all a) (permutations xs)))"
      by simp
    then obtain ys where ys_def: "ys \<in> set (permutations xs)" and "x \<in> set (insert_all a ys)"
      by auto
    
    from ys_def have "length ys = length xs"
      by (simp add: Cons.IH)

    from `x \<in> set (insert_all a ys)` have "length x = length ys + 1"
    proof -
      have "\<exists>u v. x = u @ a # v \<and> ys = u @ v"
        using l14 `x \<in> set (insert_all a ys)`
        by fastforce
      then obtain u v where x_def: "x = u @ a # v" and ys_split: "ys = u @ v" by blast
      have "length x = length u + 1 + length v"
        using x_def by simp
      also have "... = length (u @ v) + 1"
        by simp
      also have "... = length ys + 1"
        using ys_split by simp
      finally show ?thesis .
    qed

    then have "length x = length xs + 1"
      using `length ys = length xs` by simp
    
    then show ?thesis by simp
  qed
qed

lemma perm_inv_2: "xb@xe \<in> set (permutations x1) \<Longrightarrow> xb@a#xe \<in> set (permutations (a # x1))"
proof -
  assume "xb@xe \<in> set (permutations x1)"
  
  have "xb@a#xe \<in> set (insert_all a (xb@xe))"
    by (simp add: l4)
  
  moreover have "set (insert_all a (xb@xe)) \<subseteq> set (permutations (a # x1))"
  proof -
    have "xb@xe \<in> set (permutations x1)"
      by (simp add: `xb@xe \<in> set (permutations x1)`)
    then have "set (insert_all a (xb@xe)) \<subseteq> set (concat (map (insert_all a) (permutations x1)))"
      by auto
    moreover have "set (concat (map (insert_all a) (permutations x1))) = set (permutations (a # x1))"
      by simp
    ultimately show ?thesis
      by simp
  qed
  
  ultimately show "xb@a#xe \<in> set (permutations (a # x1))"
    by auto
qed

lemma singleton_permutation: "[x] \<in> set (permutations xs) \<Longrightarrow> xs = [x]"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "[x] \<in> set (concat (map (insert_all a) (permutations xs)))"
    using Cons.prems by simp
  then obtain ys where ys_def: "[x] \<in> set (insert_all a ys)" and "ys \<in> set (permutations xs)"
    by auto
  have "x = a \<and> ys = []"
  proof -
    from ys_def have "\<exists>b c. [x] = b @ a # c \<and> ys = b @ c"
      using l14
      by fastforce
    then obtain b c where bc_def: "[x] = b @ a # c" and "ys = b @ c" by auto
    from bc_def have "b = [] \<and> c = []"
      by (simp add: Cons_eq_append_conv)
    with bc_def have "x = a" by simp
    with \<open>ys = b @ c\<close> have "ys = []"
      using \<open>b = [] \<and> c = []\<close> by auto
    thus ?thesis
      by (simp add: \<open>x = a\<close>)
  qed
  with \<open>ys \<in> set (permutations xs)\<close> have "xs = []"
    using Cons.IH
    using length_inv by fastforce
  show ?case
    by (simp add: \<open>x = a \<and> ys = []\<close> \<open>xs = []\<close>)
qed

theorem count_invariant_2: "\<forall>y. count_list p y = count_list xs y \<Longrightarrow> List.member (permutations xs) p"
proof (induction xs arbitrary: p)
  case Nil
  then show ?case apply (auto)
    by (metis count_list_0_iff in_set_member list.set_intros(1) list.set_sel(1))
next
  case (Cons a xs)
  assume IH: "\<And>p. \<forall>y. count_list p y = count_list xs y \<Longrightarrow> List.member (permutations xs) p"
  assume a1: "\<forall>y. count_list p y = count_list (a # xs) y"
  have a_in_p: "List.member p a"
    by (metis a1 count_list_0_iff in_set_member list.set_intros(1))
  then show ?case
  proof -
    obtain xb xe where p_split: "p = xb @ [a] @ xe"
      by (metis a_in_p length_prop_1)
    
    have count_eq: "\<forall>y. count_list (xb @ xe) y = count_list xs y"
    proof (rule allI)
      fix y
      show "count_list (xb @ xe) y = count_list xs y"
      proof (cases "y = a")
        case True
        then have "count_list p y = Suc (count_list (xb @ xe) y)"
          using p_split length_prop_2 by simp
        moreover have "count_list (a # xs) y = Suc (count_list xs y)"
          using True by simp
        ultimately show ?thesis
          using Cons.prems by simp
      next
        case False
        then have "count_list p y = count_list (xb @ xe) y"
          using p_split length_prop_3 by simp
        moreover have "count_list (a # xs) y = count_list xs y"
          using False by simp
        ultimately show ?thesis
          using Cons.prems by simp
      qed
    qed
    
    have "List.member (permutations xs) (xb @ xe)"
      using Cons.IH count_eq by simp
    then obtain p' where p'_def: "p' \<in> set (permutations xs)" "xb @ xe = p'"
      by (simp add: List.member_def)
    
    have "p \<in> set (insert_all a p')"
      using p_split p'_def(2) insert_4
      by fastforce
    moreover have "set (insert_all a p') \<subseteq> set (permutations (a # xs))"
      using p'_def(1) insert_perm_rel by auto
    ultimately show ?thesis
      by (metis in_set_member subsetD)
  qed
qed

lemma count_invariant_3: "x1 \<notin> set (permutations x2) \<Longrightarrow> \<exists>t. count_list x1 t \<noteq> count_list x2 t"
  by (meson count_invariant_2 in_set_member)

lemma permutations_set_equality: "x1 \<in> set (permutations x2) \<Longrightarrow> set (permutations x1) = set (permutations x2)"
proof
  assume "x1 \<in> set (permutations x2)"
  show "set (permutations x1) \<subseteq> set (permutations x2)"
  proof
    fix p
    assume "p \<in> set (permutations x1)"
    have "\<forall>y. count_list p y = count_list x1 y"
      using `p \<in> set (permutations x1)` count_invariant
      by (metis in_set_member)
    moreover have "\<forall>y. count_list x1 y = count_list x2 y"
      using `x1 \<in> set (permutations x2)` count_invariant
      by (metis in_set_member)
    ultimately have "\<forall>y. count_list p y = count_list x2 y"
      by simp
    thus "p \<in> set (permutations x2)"
      using count_invariant_2
      by (metis in_set_member)
  qed

  show "set (permutations x2) \<subseteq> set (permutations x1)"
  proof
    fix p
    assume "p \<in> set (permutations x2)"
    have "\<forall>y. count_list p y = count_list x2 y"
      using `p \<in> set (permutations x2)` count_invariant
      by (metis in_set_member)
    moreover have "\<forall>y. count_list x2 y = count_list x1 y"
      using `x1 \<in> set (permutations x2)` count_invariant
      by (metis in_set_member)
    ultimately have "\<forall>y. count_list p y = count_list x1 y"
      by simp
    thus "p \<in> set (permutations x1)"
      using count_invariant_2
      by (metis in_set_member)
  qed
qed

lemma perm_lemma_1: "x1 \<notin> set (permutations x2) \<Longrightarrow> a # x1 \<notin> set (permutations (a # x2))"
proof
  assume assm1: "x1 \<notin> set (permutations x2)"
  assume contra: "a # x1 \<in> set (permutations (a # x2))"
  
  then obtain b c where bc_def: "a # x1 = b @ a # c" and perm_bc: "b @ c \<in> set (permutations x2)"
    using permutation_split_set by metis

  have "x1 \<in> set (permutations (b @ c))"
    by (smt (verit) append_eq_Cons_conv append_self_conv2 assm1 bc_def insert_perm_rel l4 list.sel(3) perm_bc)
  have "set (permutations (b @ c)) \<subseteq> set (permutations x2)"
    using perm_bc permutation_set_equality apply auto
    using permutations_set_equality by blast

  then have "x1 \<in> set (permutations x2)"
    using \<open>x1 \<in> set (permutations (b @ c))\<close> by auto

  then show False
    using assm1 by contradiction
qed

lemma perm_split: "a # x1 \<in> set (permutations (y @ a # z)) \<Longrightarrow> x1 \<in> set (permutations (y @ z))"
  by (metis insert_perm_rel l4 perm_lemma_1 permutations_set_equality)

lemma perm_inv_3: "x1 \<in> set (permutations x2) \<Longrightarrow> x2 \<in> set (permutations x1)"
proof -
  assume "x1 \<in> set (permutations x2)"
  
  have "set x1 = set x2"
    using permutation_set_equality \<open>x1 \<in> set (permutations x2)\<close>
    by auto
  
  moreover have "length x1 = length x2"
    using length_inv \<open>x1 \<in> set (permutations x2)\<close>
    by auto
  
  ultimately have "\<forall>y. count_list x1 y = count_list x2 y"
    by (meson \<open>x1 \<in> set (permutations x2)\<close> count_invariant in_set_member)
  
  hence "x2 \<in> set (permutations x1)"
    by (metis count_invariant_3)
  thus ?thesis .
qed

theorem orig_is_permutation_3: "List.member (permutations x1) x2 \<Longrightarrow> List.member (permutations x2) x1"
  by (meson in_set_member perm_inv_3)

theorem complete_state_prop_1: "fold (\<lambda> p s. S p \<union> s) xs C = foldl (\<lambda> s p. S p \<union> s) C xs"
  by (simp add: foldl_conv_fold)

theorem complete_state_prop_2: "complete_state xs = fold (\<union>) (map (\<lambda>p. S p) xs) {}"
  apply (simp add: complete_state_def)
  by (metis (mono_tags, lifting) List.fold_cong comp_apply fold_map)

theorem complete_state_prop_3: "fold (\<lambda> p s. S p \<union> s) xs C = fold (\<union>) (map (\<lambda>p. S p) xs) C"
  by (metis (mono_tags, lifting) List.fold_cong comp_apply fold_map)

theorem complete_state_prop_4: "fold (\<union>) xs C = fold (\<union>) xs {} \<union> C"
  apply (induction xs)
  apply simp
  by (metis List.finite_set Sup_fin.insert Sup_fin.set_eq_fold insert_not_empty list.simps(15) sup_bot_right sup_commute)

theorem complete_state_prop_5: "fold (\<union>) (map (\<lambda>p. S p) xs) C = fold (\<union>) (map (\<lambda>p. S p) xs) {} \<union> C"
  by (meson complete_state_prop_4)

theorem complete_state_prop: "complete_state (x # xs) = complete_state xs \<union> S x"
  apply (simp add: complete_state_def)
  by (metis complete_state_prop_3 complete_state_prop_5)

theorem permutation_complete_state_equality: "x1 \<in> set (permutations x2) \<Longrightarrow> complete_state x2 = complete_state x1"
proof -
  assume a1: "x1 \<in> set (permutations x2)"
  have "set x1 = set x2"
    using permutation_set_equality a1 by blast
  have "fold (\<union>) (map (\<lambda>p. S p) x1) {} = fold (\<union>) (map (\<lambda>p. S p) x2) {}"
    by (metis Sup_set_fold \<open>set x1 = set x2\<close> image_set)
  then have "fold (\<lambda>p s. S p \<union> s) x1 {} = fold (\<lambda>p s. S p \<union> s) x2 {}"
    by (simp add: complete_state_prop_3)
  thus ?thesis
    unfolding complete_state_def by simp
qed

lemma permutation_S_equiv: "x1 \<in> set (permutations x2) \<Longrightarrow> fold (\<union>) (map (\<lambda>p. S p) x1) {} \<equiv> fold (\<union>) (map (\<lambda>p. S p) x2) {}"
  by (smt (verit, del_insts) complete_state_def complete_state_prop_3 permutation_complete_state_equality)

lemma complete_state_union_1: "complete_state (a # xs) = complete_state (xs) \<union> complete_state ([a])"
  apply (auto simp: complete_state_def)
  apply (metis Un_iff complete_state_prop_3 complete_state_prop_5)
  apply (metis UnCI complete_state_prop_3 complete_state_prop_5)
  by (metis UnCI complete_state_prop_3 complete_state_prop_4)

lemma complete_state_union_2: "complete_state (xs) = complete_state (xs) \<union> complete_state ([])"
  by (auto simp: complete_state_def)


lemma complete_state_union_3: "complete_state (a @ b) = complete_state a \<union> complete_state b"
  apply (induction a)
  apply (metis append_self_conv2 complete_state_union_2 inf_sup_aci(5))
  by (metis (no_types, lifting) Cons_eq_appendI complete_state_union_1 sup_assoc sup_commute)

theorem perm_1: "x \<in> set (permutations xs) \<Longrightarrow> a#x \<in> set (permutations (a#xs))"
  by (metis append_self_conv2 perm_inv_2)

theorem perm_2: "set (permutations (a#xs)) = set (permutations (xs@[a]))"
  by (metis insert_perm_rel l3 permutations_set_equality)

theorem perm_3: "set (permutations ([a]@st@ed)) = set (permutations (st@[a]@ed))"
  by (metis eq_Nil_appendI insert_4 insert_perm_rel permutations_set_equality)

theorem "x \<in> set (permutations xs) \<Longrightarrow> y \<in> set (permutations ys) \<Longrightarrow> x@y \<in> set (permutations (xs@ys))"
proof (induction ys arbitrary: x xs y)
  case Nil
  then show ?case
    using length_inv by fastforce
next
  case (Cons a ys)
  assume IH: "\<And>x xs y. x \<in> set (permutations xs) \<Longrightarrow> y \<in> set (permutations ys) \<Longrightarrow> x @ y \<in> set (permutations (xs @ ys))"
  assume a1: "x \<in> set (permutations xs)"
  assume a2: "y \<in> set (permutations (a # ys))"
  from a1 perm_inv_2 have l1: "x @ [a] \<in> set (permutations (a#xs))"
    by (metis append.right_neutral)
  from a1 l1 have l2: "set (permutations (a#xs)) = set (permutations (xs@[a]))"
    by (metis perm_2)
  from l1 l2 have l3: "x @ [a] \<in> set (permutations (xs@[a]))"
    by blast
  obtain st ed where l4: "st@a#ed = y"
    by (metis a2 permutation_split_set)
  have l5: "st@ed \<in> set (permutations ys)"
    by (metis a2 local.l4 perm_inv_3 perm_split)
  have l6: "x@[a]@st@ed \<in> set (permutations (xs@[a]@ys))"
    using IH local.l3 local.l5 by fastforce
  have l7: "set (permutations (x@[a]@st@ed)) = set (permutations (x@st@[a]@ed))"
    by (metis append_assoc perm_3)
  from l7 have l8: "x@st@a#ed \<in> set (permutations (xs@[a]@ys))"
    by (metis Cons_eq_appendI eq_Nil_appendI local.l6 perm_inv_3)
  then show "x @ y \<in> set (permutations (xs @ a # ys))"
    by (simp add: local.l4)
qed


theorem elements_atomic: "x \<in> get_atomic p \<Longrightarrow> is_atomic x"
  by (auto simp: get_atomic_def is_atomic_def S_def) 

theorem empty_prop1: "finite s \<Longrightarrow> set_to_list s = [] \<equiv> s = {}"
  apply (auto simp: set_to_list_def)
  by (smt (verit) finite_distinct_list set_empty some_eq_imp)

theorem empty_prop2: "is_feasible p \<Longrightarrow> get_atomic p = {} \<Longrightarrow> Pre p = {}"
  by (auto simp: get_atomic_def equal_def Fail_def Domain_iff Field_def Range_iff is_feasible_def)

theorem finite_prop1: "finite xs \<Longrightarrow> finite ys \<Longrightarrow> finite {f a b | a b . a \<in> xs \<and> b \<in> ys}"
proof (induction xs rule: "finite_induct")
  case empty
  then show ?case by simp
next
  case (insert x xs')
  have IH: "finite {f a b |a b. a \<in> xs' \<and> b \<in> ys}" using insert(4) insert(3) by simp
  moreover have "{f a b |a b. a \<in> insert x xs' \<and> b \<in> ys} = {f a b |a b. a \<in> xs' \<and> b \<in> ys} \<union> {f a b |a b. a \<in> {x} \<and> b \<in> ys}" by auto
  moreover have "finite {f a b |a b. a \<in> {x} \<and> b \<in> ys}"
    using insert(4) apply (induction ys rule: "finite_induct") by auto
  ultimately show "finite {f a b |a b. a \<in> insert x xs' \<and> b \<in> ys}" by auto 
qed

theorem finite_prop2: "finite xs \<Longrightarrow> finite ys \<Longrightarrow> finite {f a b | a b . (a, b) \<in> xs \<and> a \<notin> ys}"
proof (induction xs rule: "finite_induct")
  case empty
  then show ?case by simp
next
  case (insert x xs)
  have IH: "finite {f a b |a b. (a, b) \<in> xs \<and> a \<notin> ys}"
    by (simp add: insert.IH insert.prems)
  moreover have "{f a b |a b. (a, b) \<in> insert x xs \<and> a \<notin> ys} = {f a b |a b. (a, b) \<in> xs \<and> a \<notin> ys} \<union> {f a b |a b. (a, b) \<in> {x} \<and> a \<notin> ys}" by auto
  moreover from insert(4) have "finite {f a b |a b. (a, b) \<in> {x} \<and> a \<notin> ys}"
    apply (cases "\<exists>t. t \<in> {f a b |a b. (a, b) \<in> {x} \<and> a \<notin> ys}")
    apply auto
    using not_finite_existsD by force
  ultimately show ?case by auto
qed

theorem finite_relation: "finite r \<equiv> finite (Field r)"
proof -
  have "finite r \<Longrightarrow> finite (Field r)"
    by (simp add: finite_Field)
  moreover have "finite (Field r) \<Longrightarrow> finite r"
  proof (induction "Field r" rule: "finite_induct")
    case empty
    then show ?case by (simp add: Field_def Range_empty_iff)
  next
    case (insert x F)
    obtain old_r where o1: "old_r = {(a,b)| a b. a \<in> F \<and> b \<in> F \<and> (a,b) \<in> r}" by simp
    obtain diff_r where o2: "diff_r = {(a,b)| a b. ((a = x \<and> b \<in> F) \<or> (a \<in> F \<and> b = x) \<or> (a=x \<and> b=x)) \<and> (a,b) \<in> r}" by simp
    have "old_r \<union> diff_r = r" using insert(2) insert(4) by (auto simp: o1 o2 Field_def Un_def Domain_iff Range_iff)
    have "finite old_r" using o1 insert apply auto
      by (metis \<open>old_r \<union> diff_r = r\<close> finite.insertI finite_SigmaI finite_trancl inf_sup_ord(3) rev_finite_subset trancl_subset_Field2)
    have "finite diff_r" using o2 insert apply auto
      by (metis \<open>old_r \<union> diff_r = r\<close> finite.insertI finite_SigmaI finite_trancl inf_sup_ord(4) rev_finite_subset trancl_subset_Field2)
    then show ?case
      using \<open>finite old_r\<close> \<open>old_r \<union> diff_r = r\<close> by auto
  qed
  ultimately show "finite r \<equiv> finite (Field r)"
    by argo
qed

theorem decomp_program: 
  assumes "finite (S p)"
  assumes "x \<notin> F"
  assumes "S p = insert x F"
  assumes "q = \<lparr>State={s|s. s \<in> State p \<and> s \<in> F}, Pre={s|s. s \<in> Pre p \<and> s \<in> F}, post={(a,b)|a b. a \<in> F \<and> b \<in> F \<and> (a,b) \<in> post p}\<rparr>"
  assumes "r = \<lparr>State={s|s. s \<in> State p}, Pre={s|s. s \<in> Pre p}, post={(a,b)|a b. (a = x \<or> b = x) \<and> (a,b) \<in> post p}\<rparr>"
  shows "p \<equiv>\<^sub>p q \<union>\<^sub>p r"
  using assms by (auto simp: choice_def restr_post_def S_def restrict_r_def Field_def equiv_def)


theorem decomp_program2: 
  assumes "finite (S p)"
  assumes "x \<notin> F"
  assumes "S p = insert x F"
  shows "finite (S \<lparr>State={s|s. s \<in> State p \<and> s \<in> F}, Pre={s|s. s \<in> Pre p \<and> s \<in> F}, post={(a,b)|a b. a \<in> F \<and> b \<in> F \<and> (a,b) \<in> post p}\<rparr>)"
proof-
  obtain r where o1: "r = \<lparr>State={s|s. s \<in> State p \<and> s \<in> F}, Pre={s|s. s \<in> Pre p \<and> s \<in> F}, post={(a,b)|a b. a \<in> F \<and> b \<in> F \<and> (a,b) \<in> post p}\<rparr>" by simp
  have l1: "finite F" using assms by auto
  from l1 have "finite (S r)" using assms(1) by (auto simp: o1 S_def Field_def)
  then show ?thesis using o1 by auto
qed


theorem decomp_program3: 
  assumes "finite (S p)"
  assumes "x \<notin> F"
  assumes "S p = insert x F"
  shows "finite (S \<lparr>State={s|s. s \<in> State p}, Pre={s|s. s \<in> Pre p}, post={(a,b)|a b. (a = x \<or> b = x) \<and> (a,b) \<in> post p}\<rparr>)"
proof-
  obtain r where o1: "r = \<lparr>State={s|s. s \<in> State p}, Pre={s|s. s \<in> Pre p}, post={(a,b)|a b. (a = x \<or> b = x) \<and> (a,b) \<in> post p}\<rparr>" by simp
  have l1: "finite F" using assms by auto
  have l2: "finite (post p)" using assms finite_relation by (auto simp: S_def Field_def Domain_iff)
  have l3: "finite (State r)" using assms by (auto simp: o1 S_def)
  have l4: "finite (Pre r)" using assms by (auto simp: o1 S_def)
  have l5: "post r \<subseteq> post p" by (auto simp: o1)
  have l6: "finite (post p)" using assms(1) finite_relation
    by (simp add: l2)
  have l7: "finite (post r)"
    using l5 l6 rev_finite_subset by auto
  from l1 have "finite (S r)"
    by (simp add: S_def finite_Field l3 l4 l7)
  then show ?thesis using o1 by auto
qed

theorem card_prop: assumes "finite a" shows "b \<inter> c = {} \<Longrightarrow> a = b \<union> c \<Longrightarrow> card a = card b + card c"
  using assms (1) apply (induction a rule: "finite_induct") apply auto
  by (metis card_Un_disjoint finite_Un finite_insert)

theorem card_prop2: assumes "finite b" assumes "finite c" shows "b \<inter> c = {} \<Longrightarrow> a = b \<union> c \<Longrightarrow> card a = card b + card c"
  using assms (1) proof (induction b rule: "finite_induct")
  case empty
  then show ?case by auto
next
  case (insert x F)
  have "finite (insert x F)" using insert by auto
  show "card a = card (insert x F) + card c"
    using \<open>finite (insert x F)\<close> assms(2) card_Un_disjoint insert.prems(1) insert.prems(2) by blast
qed

theorem finite_prop3: "finite x \<Longrightarrow> finite {f a |a . a \<in> x}" by auto

theorem finite_prop4: "finite x \<Longrightarrow> finite {f a b |a b. (a, b) \<in> x}"
proof -
  assume a1: "finite x"
  obtain f' where "f' = (\<lambda> t. f (fst t) (snd t))" by simp
  have "{f a b |a b. (a, b) \<in> x} = {f' y |y. y \<in> x}"
    using \<open>f' = (\<lambda>t. f (fst t) (snd t))\<close> by auto
  have "finite {f' y |y. y \<in> x}" using a1 finite_prop3 by blast
  show ?thesis
    using \<open>finite {f' y |y. y \<in> x}\<close> \<open>{f a b |a b. (a, b) \<in> x} = {f' y |y. y \<in> x}\<close> by presburger
qed

theorem finite_prop5: "finite (S p) \<Longrightarrow> finite (get_atomic p)"
proof -
  assume a1: "finite (S p)"
  show "finite (get_atomic p)"
  using a1 proof (induction "S p" rule: "finite_induct")
    case empty
    have l1: "Pre p = {}" using empty by (auto simp: S_def)
    have l2: "post p = {}" using empty by (auto simp: S_def Field_def)
    have l3: "State p = {}" using empty by (auto simp: S_def)
    from l1 l2 l3 have "{\<lparr>State={a,b}, Pre={a}, post={(a, b)}\<rparr> | a b .     (a,b) \<in> post p \<and> a \<in> Pre p} = {}" by auto
    moreover from l1 l2 l3 have "{\<lparr>State={a,b}, Pre={},  post={(a, b)}\<rparr> | a b .     (a,b) \<in> post p \<and> a \<notin> Pre p} = {}" by auto
    moreover from l1 l2 l3 have "{\<lparr>State={a  }, Pre={a}, post={}      \<rparr> | a   . a \<notin> Domain (post p) \<and> a \<in> Pre p} = {}" by auto
    moreover from l1 l2 l3 have "{\<lparr>State={a  }, Pre={},  post={}      \<rparr> | a   . a \<notin> Field (restr_post p) \<and> a \<notin> Pre p \<and> a \<in> State p} = {}" by auto
    ultimately show ?case by (auto simp: get_atomic_def)
  next
    case (insert x F)
    have l1: "finite (Pre p)" using insert 
      apply (auto simp: S_def)
      using a1 insert.hyps(4) by auto
    have l2: "finite (post p)" using insert  
      apply (auto simp: S_def)
      using a1 finite_relation insert.hyps(4) by auto
    have l3: "finite (State p)" using insert
      by (metis S_def a1 finite_Un)
    have l4: "\<forall>f::('a \<Rightarrow> 'a \<Rightarrow> 'a Program). finite {f a b | a b . (a,b) \<in> post p}"
      using l2 apply (induction "post p" rule: "finite_induct")
      by (auto simp: finite_prop4 l2)
    from l1 l2 l3 have "finite {\<lparr>State={a,b}, Pre={a}, post={(a, b)}\<rparr> | a b .  (a,b) \<in> post p \<and> a \<in> Pre p}"
    proof -
      have "finite {\<lparr>State={a,b}, Pre={a}, post={(a, b)}\<rparr> | a b . (a,b) \<in> post p}" using l4 by auto
      moreover have "{\<lparr>State={a,b}, Pre={a}, post={(a, b)}\<rparr> | a b . (a,b) \<in> post p \<and> a \<in> Pre p} \<subseteq> {\<lparr>State={a,b}, Pre={a}, post={(a, b)}\<rparr> | a b . (a,b) \<in> post p}" by blast
      ultimately show "finite {\<lparr>State={a,b}, Pre={a}, post={(a, b)}\<rparr> | a b . (a,b) \<in> post p \<and> a \<in> Pre p}"
        by (meson finite_subset)
    qed
    moreover from l1 l2 l3 have "finite {\<lparr>State={a,b}, Pre={},  post={(a, b)}\<rparr> | a b . (a,b) \<in> post p \<and> a \<notin> Pre p}"
    proof -
      have "finite {\<lparr>State={a,b}, Pre={}, post={(a, b)}\<rparr> | a b . (a,b) \<in> post p}" using l4 by auto
      moreover have "{\<lparr>State={a,b}, Pre={},  post={(a, b)}\<rparr> | a b . (a,b) \<in> post p \<and> a \<notin> Pre p} \<subseteq> {\<lparr>State={a,b}, Pre={}, post={(a, b)}\<rparr> | a b . (a,b) \<in> post p}" by blast
      ultimately show "finite {\<lparr>State={a,b}, Pre={}, post={(a, b)}\<rparr> | a b . (a,b) \<in> post p \<and> a \<notin> Pre p}"
        by (meson finite_subset)
    qed
    moreover from l1 l2 l3 have "finite {\<lparr>State={a  }, Pre={a}, post={} \<rparr> | a . a \<notin> Domain (post p) \<and> a \<in> Pre p}" by auto
    moreover from l1 l2 l3 have "finite {\<lparr>State={a  }, Pre={},  post={} \<rparr> | a . a \<notin> Field (restr_post p) \<and> a \<notin> Pre p \<and> a \<in> State p}" by auto
    ultimately show ?case by (auto simp: get_atomic_def)
  qed
qed

theorem atomic_idem: "is_atomic p \<Longrightarrow> (get_atomic p) \<union> {p} = get_atomic (p \<union>\<^sub>p p)"
  apply (auto simp: get_atomic_def is_atomic_def choice_def restr_post_def restrict_r_def S_def Field_def Domain_iff Range_iff Un_def)
proof-
  fix p::"'a Program"
  assume a1: "card (post p) = Suc 0" and
    a2: "card (Pre p) = Suc 0" and
    a3: "State p = {x. x \<in> Pre p \<or> (\<exists>y. (x, y) \<in> post p) \<or> (\<exists>y. (y, x) \<in> post p)}" and 
    a4: "fst (THE x. x \<in> post p) = (THE x. x \<in> Pre p)"
  then obtain x where o1: "Pre p = {x}"
    by (meson card_1_singleton_iff)
  then obtain x' y where o2: "post p = {(x',y)}" using a4 a1 apply auto
    by (metis One_nat_def is_singleton_altdef is_singleton_the_elem old.prod.exhaust)
  have l1: "x' = x" using o1 o2 a4 by (auto simp: )
  have o2: "post p = {(x,y)}" using o2 l1 by auto
  have "State p = {x, y}" using a3 o1 o2 apply simp by auto
  then have "p = \<lparr>State = {x, y}, Pre = {x}, post = {(x, y)}\<rparr>" using o2 o1 by auto
  then have "p = \<lparr>State = {x, y}, Pre = {x}, post = {(x, y)}\<rparr> \<and> (x, y) \<in> post p \<and> x \<in> Pre p"
    using o1 o2 by blast
  then show "\<exists>a b. p = \<lparr>State = {a, b}, Pre = {a}, post = {(a, b)}\<rparr> \<and> (a, b) \<in> post p \<and> a \<in> Pre p" by auto
qed

theorem atomic_state: "is_atomic x \<Longrightarrow> S x = State x"
  by (auto simp: S_def is_atomic_def)

theorem atomic_prop1: "is_atomic x \<Longrightarrow> \<exists>a b. \<lparr>State={a,b}, Pre={a}, post={(a,b)}\<rparr> = x"
proof -
  assume a1: "is_atomic x"
  obtain a where o1: "Pre x = {a}" using a1 apply (auto simp: is_atomic_def)
    by (meson card_1_singleton_iff)
  obtain a' b where o2: "post x = {(a',b)}" using a1 apply (auto simp: is_atomic_def)
    by (metis One_nat_def is_singletonE is_singleton_altdef old.prod.exhaust)
  have l1: "a' = a" using o1 o2 a1 by (auto simp: is_atomic_def)
  have "State x = {a,b}" using a1 o1 o2 l1 apply (simp add: is_atomic_def)
    by (simp add: insert_commute)
  have "\<lparr>State={a,b}, Pre={a}, post={(a,b)}\<rparr> = x"
    by (simp add: \<open>State x = {a, b}\<close> l1 o1 o2)
  then show ?thesis by auto
qed

theorem atomic_prop2: "\<exists>a b. \<lparr>State={a,b}, Pre={a}, post={(a,b)}\<rparr> = x \<Longrightarrow> is_atomic x"
  by (auto simp: is_atomic_def S_def)

theorem atomic_prop3: "\<exists>a b. \<lparr>State={a,b}, Pre={a}, post={(a,b)}\<rparr> = x \<equiv> is_atomic x"
  using atomic_prop1 atomic_prop2
  by (smt (verit, ccfv_SIG))

theorem atomic_post: "is_atomic x \<Longrightarrow> restr_post x = post x"
proof -
  assume a1: "is_atomic x"
  obtain a b where o1: "\<lparr>State={a,b}, Pre={a}, post={(a,b)}\<rparr> = x"
    by (meson a1 atomic_prop1)
  have "restr_post \<lparr>State={a,b}, Pre={a}, post={(a,b)}\<rparr> = post \<lparr>State={a,b}, Pre={a}, post={(a,b)}\<rparr>" by (auto simp: restr_post_def restrict_r_def)
  then show ?thesis using o1 by auto
qed

theorem atomic_monotone: "get_atomic p \<subseteq> get_atomic (p \<union>\<^sub>p q)"
  by (auto simp: get_atomic_def choice_def restr_post_def restrict_r_def)

theorem atomic_split: "finite (get_atomic p) \<Longrightarrow> finite (get_atomic q) \<Longrightarrow> (get_atomic p) \<union> (get_atomic q) = get_atomic (p \<union>\<^sub>p q)"
  by (auto simp: get_atomic_def choice_def restr_post_def restrict_r_def)


theorem assumes "is_atomic x" shows "(get_atomic p) \<union> {x} = get_atomic (p \<union>\<^sub>p x)"
  apply (auto simp: get_atomic_def choice_def restr_post_def restrict_r_def)
  using assms(1) atomic_prop1 apply force
  using assms(1) atomic_prop1 apply fastforce
  using assms(1) atomic_prop1 apply fastforce
  using assms(1) atomic_prop1 by fastforce

theorem fail_atomic: "get_atomic (Fail {}) = {}" by (auto simp: get_atomic_def Fail_def)

theorem set_list_set: "finite xs \<Longrightarrow> set (set_to_list xs) = xs" apply (auto simp: set_to_list_def)
  apply (metis (mono_tags, lifting) finite_distinct_list some_eq_imp)
  by (metis (mono_tags, lifting) finite_distinct_list some_eq_imp)

theorem set_list_prop: "finite F \<Longrightarrow> xs = set_to_list (insert x F) \<Longrightarrow> \<exists>a b. a@x#b = xs"
proof -
  assume a1: "finite F"
  assume a2: "xs = set_to_list (insert x F)"
  have "x \<in> set xs" using a1 a2 set_list_set
    by (metis finite.insertI insertI1)
  show ?thesis
    by (metis \<open>x \<in> set xs\<close> in_set_conv_decomp_first)
qed

theorem set_to_list_distinct: "xs = set_to_list F \<Longrightarrow> distinct xs"
  apply (cases "finite F") apply (auto simp: set_to_list_def)
  by (metis (mono_tags, lifting) finite_distinct_list verit_sko_ex')


theorem set_to_list_size: "size (set_to_list F) = card F"
proof (cases "finite F")
  case True
  obtain xs where o1: "xs = set_to_list F" by simp
  have "distinct xs"
    by (simp add: o1 set_to_list_distinct)
  have "\<forall>x. x \<in> set xs \<longrightarrow> x \<in> F"
    by (simp add: True o1 set_list_set)
  have "\<forall>x. x \<in> F \<longrightarrow> x \<in> set xs"
    by (simp add: True o1 set_list_set)
  then show ?thesis
    by (metis True \<open>distinct xs\<close> distinct_card o1 set_list_set)
next
  case False
  then show ?thesis by (auto simp: set_to_list_def)
qed

theorem set_to_list_one: "set_to_list {x} = [x]"
proof -
  have "set (set_to_list {x}) = {x}"
    by (simp add: set_list_set)
  have "size (set_to_list {x}) = 1" using card_1_singleton_iff distinct_card distinct_singleton apply (auto simp: set_to_list_def)
    by (smt (z3) Collect_empty_eq_bot bot_nat_def card_1_singleton_iff card_distinct distinct_card empty_Collect_eq empty_def length_replicate set_replicate_Suc singleton_conv some_eq_imp)
  show ?thesis
    by (metis One_nat_def \<open>length (set_to_list {x}) = 1\<close> \<open>set (set_to_list {x}) = {x}\<close> append_Nil append_butlast_last_id append_eq_append_conv diff_Suc_1' empty_set insert_not_empty last_in_set length_butlast list.size(3) singleton_iff)
qed

theorem atomic_prop_1: "is_atomic x \<Longrightarrow> get_atomic x = {x}"
proof-
  assume a1: "is_atomic x"
  obtain a b where o1: "x = \<lparr>State={a,b}, Pre={a}, post={(a,b)}\<rparr>"
    using a1 atomic_prop1 by blast
  have "get_atomic \<lparr>State={a,b}, Pre={a}, post={(a,b)}\<rparr> = {\<lparr>State={a,b}, Pre={a}, post={(a,b)}\<rparr>}" by (auto simp: get_atomic_def)
  then show ?thesis using o1 by auto
qed

theorem Consistent_feasible: "is_feasible (feasible_version p)"
  by (auto simp: is_feasible_def feasible_version_def)

theorem Consistent_round: "is_rounded (rounded_version p)"
  by (auto simp: is_rounded_def rounded_version_def restrict_r_def)

theorem Consistent_exact: "is_exact (exact_version p)"
  by (auto simp: is_exact_def exact_version_def is_rounded_def is_feasible_def restrict_r_def)

theorem Feas_round: "is_feasible p \<Longrightarrow> is_feasible (rounded_version p)"
  by (auto simp: is_feasible_def rounded_version_def restrict_r_def Domain_iff subset_iff)

theorem Round_feas: "is_rounded p \<Longrightarrow> is_rounded (feasible_version p)"
  by (auto simp: is_rounded_def feasible_version_def)

theorem Equiv_prog: "a \<equiv>\<^sub>p b \<equiv> (Pre (rounded_version a) = Pre (rounded_version b) \<and> post (rounded_version a) = post (rounded_version b))"
  by (auto simp: rounded_version_def restrict_r_def equiv_def restr_post_def)

theorem Charrel_restriction: "rounded_version (p \<sslash>\<^sub>p C) = rounded_version p \<sslash>\<^sub>p C" \<comment> \<open>/Charrel_restriction/\<close>
  by (auto simp: rounded_version_def restrict_p_def restrict_r_def S_def Field_def)

theorem Charrel_choice: "rounded_version (p \<union>\<^sub>p q) = rounded_version p \<union>\<^sub>p rounded_version q"
  by (auto simp: rounded_version_def choice_def restr_post_def restrict_r_def S_def)

theorem Charrel_composition: "rounded_version (p ; q) = rounded_version p ; rounded_version q"
  by (auto simp: rounded_version_def composition_def restr_post_def restrict_r_def S_def Field_def corestrict_r_def)

theorem Charrel_corestriction: "rounded_version (p \<setminus>\<^sub>p C) = rounded_version p \<setminus>\<^sub>p C"
  by (auto simp: rounded_version_def corestrict_p_def corestrict_r_def restrict_r_def S_def Field_def)

theorem Restrict_rounded: "is_rounded p \<Longrightarrow> is_rounded (p \<sslash>\<^sub>p C)"
  by (auto simp: is_rounded_def restrict_p_def restrict_r_def)

theorem Choice_rounded: "is_rounded (p \<union>\<^sub>p q)"
  by (auto simp: is_rounded_def choice_def restr_post_def restrict_r_def)

theorem "is_rounded q \<Longrightarrow> is_rounded p \<Longrightarrow> is_rounded (p;q)"
  by (auto simp: is_rounded_def composition_def corestrict_r_def restr_post_def restrict_r_def)

theorem Corestrict_feasible: "is_feasible p \<Longrightarrow> is_feasible ((p \<sslash>\<^sub>p (Pre p \<inter> Domain (post p \<setminus>\<^sub>r C))) \<setminus>\<^sub>p C)" \<comment> \<open>/Corestrict_feasible/\<close>
  by (auto simp: is_feasible_def restrict_p_def restrict_r_def corestrict_p_def corestrict_r_def)
end