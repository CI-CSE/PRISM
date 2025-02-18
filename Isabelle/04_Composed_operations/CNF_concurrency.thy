theory CNF_concurrency
  imports Big_choice
begin

theorem "(a@b)\<parallel>c =(a\<parallel>c)@(b\<parallel>c)"
  by (auto simp: cnf_concurrency_def)

primrec factorial :: "nat \<Rightarrow> nat" where
  "factorial 0 = 1" |
  "factorial (Suc n) = (Suc n) * factorial n"

theorem fact_eq: "factorial n = fact n"
  apply (induction n) by auto

theorem factorial_mod_product: "factorial (a + b) mod (factorial a * factorial b) = (0::nat)"
  using fact_eq
  by (metis binomial_fact_lemma diff_add_inverse2 le_add2 mod_mult_self1_is_0 mult.commute)


theorem factorial_bound: "factorial n > 0"
  apply (induction n) by auto

theorem simp_div: "a mod b = 0 \<Longrightarrow> c mod b = 0 \<Longrightarrow> (a::nat) div b + c div b = (a + c) div b"
  apply (induction a) apply auto
  by (metis add_Suc div_add)

theorem exits_mulit: "\<exists>t::nat. n*t=m \<Longrightarrow> m mod n = 0" by auto

definition nmb_interleavings_pre :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "nmb_interleavings_pre x y \<equiv> factorial (x + y) div (factorial x * factorial y)"

value "nmb_interleavings_pre 1 0"

theorem "nmb_interleavings_pre (nmb_interleavings_pre x y) z = nmb_interleavings_pre x (nmb_interleavings_pre y z)"
  oops

definition nmb_interleavings :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat"
  where
    "nmb_interleavings xs ys \<equiv> nmb_interleavings_pre (size xs) (size ys)"

theorem number_interleav: "length (xs \<interleave> ys) = nmb_interleavings xs ys"
    apply (auto simp: nmb_interleavings_def nmb_interleavings_pre_def)
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case apply auto apply (induction ys) apply auto
    by (simp add: factorial_bound)
next
  case Cons1: (Cons x xs)
  then show ?case
  proof (induction ys)
    case Nil
    have "(factorial (length xs) + length xs * factorial (length xs)) \<noteq> 0"
      apply (auto)
      using factorial_bound not_gr_zero by blast
    then show ?case by auto
  next
    case (Cons y ys)
    have "size ((x # xs) \<interleave> (y # ys)) = size (xs \<interleave> (y#ys)) + size ((x#xs) \<interleave> ys)" by simp
    have "size (xs \<interleave> (y#ys)) = factorial (length xs + Suc (length ys)) div (factorial (length xs) * factorial (Suc (length ys)))"
      by (simp add: Cons1)
    have "size ((x#xs) \<interleave> ys) = factorial (Suc (length xs) + length ys) div (factorial (Suc (length xs)) * factorial (length ys))"
      by (simp add: Cons.IH Cons1)
    obtain sx where "sx = size xs" by simp
    obtain sy where "sy = size ys" by simp
    have "factorial sx * factorial sy * Suc sx * Suc sy = factorial (Suc sx) * factorial (Suc sy)"
      by (metis ab_semigroup_mult_class.mult_ac(1) factorial.simps(2) mult.commute)
    have "factorial (sx + Suc sy) = factorial (sx + sy + 1)" by auto
    have "factorial (Suc sx + sy) = factorial (sx + sy + 1)" by auto

    have "factorial (sx + sy + 1)*Suc sx mod (factorial (Suc sx) * factorial (Suc sy)) = 0"
      by (metis \<open>factorial (Suc sx + sy) = factorial (sx + sy + 1)\<close> ab_semigroup_mult_class.mult_ac(1) add_Suc_shift factorial.simps(2) factorial_mod_product mod_mult_mult2 mult.commute mult_is_0)
    have "factorial (sx + sy + 1)*Suc sy mod (factorial (Suc sx) * factorial (Suc sy)) = 0"
      by (metis \<open>factorial (sx + Suc sy) = factorial (sx + sy + 1)\<close> ab_semigroup_mult_class.mult_ac(1) add_Suc_shift factorial.simps(2) factorial_mod_product mod_mult_mult2 mult.commute mult_is_0)
    have "factorial (sx + Suc sy) div (factorial sx * factorial (Suc sy)) +
          factorial (Suc sx + sy) div (factorial (Suc sx) * factorial sy) =
          factorial (sx + sy + 1) div (factorial sx * factorial sy * Suc sy) +
          factorial (sx + sy + 1) div (factorial sx * factorial sy * Suc sx)"
      by (smt (verit, ccfv_SIG) Suc_eq_plus1 add.commute add_Suc_right factorial.simps(2) mult.commute mult.left_commute)
    have "... = factorial (sx + sy + 1)*Suc sy div (factorial sx * factorial sy * Suc sy * Suc sy) +
                factorial (sx + sy + 1)*Suc sx div (factorial sx * factorial sy * Suc sx * Suc sx)"
      by (metis add_is_0 div_mult_mult2 plus_1_eq_Suc zero_neq_one)
    have "... = factorial (sx + sy + 1)*Suc sy div (factorial sx * factorial sy * Suc sx * Suc sy) +
                factorial (sx + sy + 1)*Suc sx div (factorial sx * factorial sy * Suc sx * Suc sy)"
      by (smt (verit) add.commute add_is_0 div_mult2_eq div_mult_mult2 plus_1_eq_Suc zero_neq_one)
    have "... = factorial (sx + sy + 1)*Suc sy div (factorial (Suc sx) * factorial (Suc sy)) +
                factorial (sx + sy + 1)*Suc sx div (factorial (Suc sx) * factorial (Suc sy))"
      using \<open>factorial sx * factorial sy * Suc sx * Suc sy = factorial (Suc sx) * factorial (Suc sy)\<close> by presburger
    have "... = (factorial (sx + sy + 1)*(Suc sx)+factorial (sx + sy + 1)*(Suc sy)) div
                (factorial sx * factorial sy * Suc sy * Suc sx)"
      by (smt (verit) \<open>factorial (sx + sy + 1) * Suc sx mod (factorial (Suc sx) * factorial (Suc sy)) = 0\<close> \<open>factorial (sx + sy + 1) * Suc sy mod (factorial (Suc sx) * factorial (Suc sy)) = 0\<close> \<open>factorial sx * factorial sy * Suc sx * Suc sy = factorial (Suc sx) * factorial (Suc sy)\<close> add.commute mult.commute mult.left_commute simp_div)
    have "... = factorial (Suc sx + Suc sy) div (factorial (Suc sx) * factorial (Suc sy))"
      by (metis \<open>factorial (Suc sx + sy) = factorial (sx + sy + 1)\<close> add_Suc_right distrib_left factorial.simps(2) mult.commute mult.left_commute)
    then show ?case
      by (metis \<open>factorial (sx + Suc sy) div (factorial sx * factorial (Suc sy)) + factorial (Suc sx + sy) div (factorial (Suc sx) * factorial sy) = factorial (sx + sy + 1) div (factorial sx * factorial sy * Suc sy) + factorial (sx + sy + 1) div (factorial sx * factorial sy * Suc sx)\<close> \<open>factorial (sx + sy + 1) * Suc sy div (factorial (Suc sx) * factorial (Suc sy)) + factorial (sx + sy + 1) * Suc sx div (factorial (Suc sx) * factorial (Suc sy)) = (factorial (sx + sy + 1) * Suc sx + factorial (sx + sy + 1) * Suc sy) div (factorial sx * factorial sy * Suc sy * Suc sx)\<close> \<open>factorial (sx + sy + 1) * Suc sy div (factorial sx * factorial sy * Suc sy * Suc sy) + factorial (sx + sy + 1) * Suc sx div (factorial sx * factorial sy * Suc sx * Suc sx) = factorial (sx + sy + 1) * Suc sy div (factorial sx * factorial sy * Suc sx * Suc sy) + factorial (sx + sy + 1) * Suc sx div (factorial sx * factorial sy * Suc sx * Suc sy)\<close> \<open>factorial (sx + sy + 1) div (factorial sx * factorial sy * Suc sy) + factorial (sx + sy + 1) div (factorial sx * factorial sy * Suc sx) = factorial (sx + sy + 1) * Suc sy div (factorial sx * factorial sy * Suc sy * Suc sy) + factorial (sx + sy + 1) * Suc sx div (factorial sx * factorial sy * Suc sx * Suc sx)\<close> \<open>factorial sx * factorial sy * Suc sx * Suc sy = factorial (Suc sx) * factorial (Suc sy)\<close> \<open>length ((x # xs) \<interleave> (y # ys)) = length (xs \<interleave> (y # ys)) + length ((x # xs) \<interleave> ys)\<close> \<open>length ((x # xs) \<interleave> ys) = factorial (Suc (length xs) + length ys) div (factorial (Suc (length xs)) * factorial (length ys))\<close> \<open>length (xs \<interleave> (y # ys)) = factorial (length xs + Suc (length ys)) div (factorial (length xs) * factorial (Suc (length ys)))\<close> \<open>sx = length xs\<close> \<open>sy = length ys\<close> length_Suc_conv)
  qed
qed

theorem monoton_fact: "a \<le> b \<Longrightarrow> factorial a \<le> factorial b"
proof -
  assume "a \<le> b"
  then show "factorial a \<le> factorial b"
  proof (induction a arbitrary: b)
    case 0
    then show ?case
      by (metis bot_nat_0.not_eq_extremum factorial.simps(1) factorial_bound less_one verit_comp_simplify1(3))
  next
    case (Suc a)
    have "factorial a \<le> factorial b"
      using Suc.IH Suc.prems Suc_leD by blast
    have "factorial (Suc a) = factorial a * Suc a"
      by simp
    then show "factorial (Suc a) \<le> factorial b"
    proof (cases "Suc a = b")
      case True
      then show ?thesis by auto
    next
      case False
      then show ?thesis
        using Suc.prems fact_eq fact_mono_nat by presburger
    qed
  qed
qed

theorem interleave_size: "size xs * size ys \<le> size (xs \<interleave> ys)"
proof (induction "xs" arbitrary: ys)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then show ?case
  proof (induction ys)
    case Nil
    then show ?case by auto
  next
    case (Cons y ys)
    have "size ((x # xs) \<interleave> (y # ys)) = size (xs \<interleave> (y#ys)) + size ((x#xs) \<interleave> ys)" by auto
    have "length xs * length (y#ys) \<le> size (xs \<interleave> (y#ys))"
      using Cons.prems by blast
    have "length (x#xs) * length ys \<le> size ((x#xs) \<interleave> ys)"
      using Cons.IH Cons.prems by auto
    have "length (x#xs) * length ys + length xs * length (y#ys) \<le> length ((x # xs) \<interleave> (y # ys))"
      using \<open>length ((x # xs) \<interleave> (y # ys)) = length (xs \<interleave> (y # ys)) + length ((x # xs) \<interleave> ys)\<close> \<open>length (x # xs) * length ys \<le> length ((x # xs) \<interleave> ys)\<close> \<open>length xs * length (y # ys) \<le> length (xs \<interleave> (y # ys))\<close> add_le_mono by presburger
    have "xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> length (x#xs) * length (y#ys) \<le> length (x#xs) * length ys + length xs * length (y#ys)" apply auto
      using not_less_eq_eq by auto
    then show "length (x # xs) * length (y # ys) \<le> length ((x # xs) \<interleave> (y # ys))"
      apply (cases "xs=[]") apply auto
      using \<open>length (x # xs) * length ys \<le> length ((x # xs) \<interleave> ys)\<close> apply fastforce
      apply (cases "ys=[]") apply auto
      using \<open>length xs * length (y # ys) \<le> length (xs \<interleave> (y # ys))\<close> apply auto[1]
      by (metis \<open>\<lbrakk>xs \<noteq> []; ys \<noteq> []\<rbrakk> \<Longrightarrow> length (x # xs) * length (y # ys) \<le> length (x # xs) * length ys + length xs * length (y # ys)\<close> \<open>length ((x # xs) \<interleave> (y # ys)) = length (xs \<interleave> (y # ys)) + length ((x # xs) \<interleave> ys)\<close> \<open>length (x # xs) * length ys + length xs * length (y # ys) \<le> length ((x # xs) \<interleave> (y # ys))\<close> add_Suc le_trans length_Cons mult.commute mult_Suc)
  qed
qed

lemma list_comp_size: "size [f path_m path_n. path_m \<leftarrow> xs, path_n \<leftarrow> ys] \<ge> size xs * size ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then show ?case
  proof (induction ys)
    case Nil
    then show ?case by auto
  next
    case (Cons y ys)
    have "size [f path_m path_n. path_m \<leftarrow> xs, path_n \<leftarrow> ys] \<ge> size xs * size ys" using Cons(2)[of ys] by auto
    have "size [f path_m path_n. path_m \<leftarrow> (x#xs), path_n \<leftarrow> ys] \<ge> size (x#xs) * size ys" using Cons(2)[of ys] by auto
    have "size [f path_m path_n. path_m \<leftarrow> xs, path_n \<leftarrow> (y#ys)] \<ge> size xs * size (y#ys)" using Cons.prems by blast
    have "[f path_m path_n. path_m \<leftarrow> (x#xs), path_n \<leftarrow> (y#ys)] = [f x path_n. path_n \<leftarrow> (y#ys)] @ [f path_m path_n. path_m \<leftarrow> (xs), path_n \<leftarrow> (y#ys)]" by simp
    have "size ([f x path_n. path_n \<leftarrow> (y#ys)] @ [f path_m path_n. path_m \<leftarrow> (xs), path_n \<leftarrow> (y#ys)]) \<ge> size (y#ys) + (size xs * size (y#ys))"
      using \<open>length xs * length (y # ys) \<le> length (concat (map (\<lambda>path_m. map (f path_m) (y # ys)) xs))\<close> by force
    have "size (y#ys) + (size xs * size (y#ys)) = size (y#ys) * size (x#xs)"
      by simp
    then show "size [f path_m path_n. path_m \<leftarrow> (x#xs), path_n \<leftarrow> (y#ys)] \<ge> size (x#xs) * size (y#ys)"
      using \<open>length (y # ys) + length xs * length (y # ys) \<le> length (map (f x) (y # ys) @ concat (map (\<lambda>path_m. map (f path_m) (y # ys)) xs))\<close> by fastforce
  qed
qed

lemma interleav_lower_bound: "size (xs \<interleave> ys) \<ge> 1"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then show ?case
proof (induction ys)
  case Nil
  then show ?case by auto
next
  case (Cons y ys)
  have "1 \<le> length (xs \<interleave> ys)"
    using Cons.prems by auto
  have "1 \<le> length ((x # xs) \<interleave> ys)"
    using Cons.IH Cons.prems by auto
  have "1 \<le> length (xs \<interleave> (y # ys))"
    using Cons.prems by auto
  have "(x # xs) \<interleave> (y # ys) = map ((#) x) (xs \<interleave> (y#ys)) @  map ((#) y) ((x#xs) \<interleave> ys)" by simp
  have "size (map ((#) x) (xs \<interleave> (y#ys))) \<ge> 1"
    using \<open>1 \<le> length (xs \<interleave> (y # ys))\<close> by auto
  then show "1 \<le> length ((x # xs) \<interleave> (y # ys))"
    by simp
qed
qed 

lemma concat_prop: "\<forall>x \<in> set xs. size x \<ge> 1 \<Longrightarrow> size (concat xs) \<ge> size xs"
  apply (induction xs) by auto

theorem conc_size: "size xs * size ys \<le> size (xs \<parallel> ys)"
proof -
  have "xs \<parallel> ys = concat [path_m \<interleave> path_n. path_m \<leftarrow> xs, path_n \<leftarrow> ys]" by (simp add: cnf_concurrency_def)
  have "\<forall>x \<in> set [path_m \<interleave> path_n. path_m \<leftarrow> xs, path_n \<leftarrow> ys]. size x \<ge> 1" using interleav_lower_bound by auto
  have "size [path_m \<interleave> path_n. path_m \<leftarrow> xs, path_n \<leftarrow> ys] \<ge> size xs * size ys" using list_comp_size by auto
  show ?thesis apply (simp add: cnf_concurrency_def)
    using CNF_concurrency.concat_prop \<open>\<forall>x\<in>set (concat (map (\<lambda>path_m. map ((\<interleave>) path_m) ys) xs)). 1 \<le> length x\<close> \<open>length xs * length ys \<le> length (concat (map (\<lambda>path_m. map ((\<interleave>) path_m) ys) xs))\<close> dual_order.trans by blast
qed

theorem size_one1: "size (xs \<parallel> ys) = 1 \<Longrightarrow> size xs = 1"
proof -
  assume "size (xs \<parallel> ys) = 1 "
  have "xs \<parallel> ys = concat (concat (map (\<lambda>path_m. map ((\<interleave>) path_m) ys) xs))" by (auto simp: cnf_concurrency_def)
  have "size xs \<noteq> 1 \<Longrightarrow> size (xs \<parallel> ys) \<noteq> 1"
  proof (cases "xs=[]")
    case True
    assume "size xs \<noteq> 1"
    have "size xs = 0"
      by (simp add: True)
    have "length ([] \<parallel> ys) = 0" by (auto simp: cnf_concurrency_def)
    then show ?thesis
      by (simp add: True)
  next
    case f1: False
    assume "size xs \<noteq> 1"
    then show ?thesis
    proof (cases "ys=[]")
      case True
      have "length (xs \<parallel> []) = 0" by (auto simp: cnf_concurrency_def)
      then show ?thesis
        by (simp add: True)
    next
      case f2: False
      then show ?thesis using f1 f2
        by (metis One_nat_def \<open>length xs \<noteq> 1\<close> conc_size divisors_zero le_SucE le_zero_eq length_0_conv nat_mult_eq_1_iff)
    qed
  qed
  then show ?thesis
    using \<open>length (xs \<parallel> ys) = 1\<close> by auto
qed

theorem size_one2: "size (xs \<parallel> ys) = 1 \<Longrightarrow> size ys = 1"
proof -
  assume "size (xs \<parallel> ys) = 1"
  have "size (ys \<parallel> xs) = 1"
    by (simp add: \<open>length (xs \<parallel> ys) = 1\<close> t4)
  show "size ys = 1" using size_one1
    using \<open>length (ys \<parallel> xs) = 1\<close> by auto
qed


primrec sum :: "nat list \<Rightarrow> nat" where
  "sum [] = 0" |
  "sum (x#xs) = x + sum xs"

theorem sum_1: "size (concat xs) = sum [size x. x\<leftarrow>xs]"
  apply (induction xs) by auto


theorem path_decomp: "path \<in> set (p \<parallel> q) \<Longrightarrow> \<exists>path_p path_q. path_p \<in> set p \<and> path_q \<in> set q \<and> path \<in> set (path_p \<interleave> path_q)"
  apply (induction p) by (auto simp: cnf_concurrency_def)

theorem path_decomp2: "path_p \<in> set p \<Longrightarrow> path_q \<in> set q \<Longrightarrow> path \<in> set (path_p \<interleave> path_q) \<Longrightarrow> path \<in> set (p \<parallel> q)"
  apply (induction p) by (auto simp: cnf_concurrency_def)


theorem inter_leav1: "(p#path) \<in> set ((x#xs) \<interleave> (y#ys)) \<Longrightarrow> ((p=x) \<and> path \<in> set (xs \<interleave> (y#ys))) \<or> ((p=y) \<and> path \<in> set ((x#xs) \<interleave> (ys)))"
  by (auto simp:)

theorem inter_leav2: "((p=y) \<and> path \<in> set ((x#xs) \<interleave> (ys))) \<Longrightarrow> (p#path) \<in> set ((x#xs) \<interleave> (y#ys))"
  by (auto simp:)
theorem inter_leav3: "((p=x) \<and> path \<in> set (xs \<interleave> (y#ys))) \<Longrightarrow> (p#path) \<in> set ((x#xs) \<interleave> (y#ys))"
  by (auto simp:)


theorem conc_lem1:  "set (xs \<parallel> ys) = \<Union> {set (path_x \<interleave> path_y) |path_x path_y. path_x \<in> set xs \<and> path_y \<in> set ys}"
  by (auto simp: cnf_concurrency_def)

theorem "set ((x#xs) \<parallel> ys) = set ([x]\<parallel>ys) \<union> set (xs\<parallel>ys)"
  by (auto simp: cnf_concurrency_def)

lemma assoc_1: "set (([x] \<parallel> [y]) \<parallel> [z]) \<subseteq> set ([x] \<parallel> ([y] \<parallel> [z]))"
proof (induction x arbitrary: y z)
  case Nil
  then show ?case by (auto simp: cnf_concurrency_def)
next
  case Cons1: (Cons xx x)
  then show ?case
  proof (induction y arbitrary: x z)
    case Nil
    then show ?case by (auto simp: cnf_concurrency_def)
  next
    case Cons2: (Cons yy y)
    then show ?case 
    proof (induction z arbitrary: x y)
      case Nil
      then show ?case by (auto simp: cnf_concurrency_def)
    next
      case Cons3: (Cons zz z)
      have "set (([x] \<parallel> [yy#y]) \<parallel> [zz#z]) \<subseteq> set ([x] \<parallel> ([yy#y] \<parallel> [zz#z]))"
        using Cons3.prems(2) by auto
      have "set (([xx#x] \<parallel> [y]) \<parallel> [zz#z]) \<subseteq> set ([xx#x] \<parallel> ([y] \<parallel> [zz#z]))"
        by (simp add: Cons3.prems(1) Cons3.prems(2))
      have "set (([xx#x] \<parallel> [yy#y]) \<parallel> [z]) \<subseteq> set ([xx#x] \<parallel> ([yy#y] \<parallel> [z]))"
        using Cons3.IH Cons3.prems(1) Cons3.prems(2) by blast

      have "set ([xx # x] \<parallel> [yy # y]) = {xx#path | path. path \<in> set ([x]\<parallel>[yy#y])} \<union> {yy#path | path. path \<in> set ([xx#x]\<parallel>[y])}" by (auto simp: cnf_concurrency_def)
      have "set (([xx # x] \<parallel> [yy # y]) \<parallel> [zz # z]) = {xx#path | path. path \<in> set (([x] \<parallel> [yy # y]) \<parallel> [zz # z])} \<union> {yy#path | path. path \<in> set (([xx#x] \<parallel> [y]) \<parallel> [zz # z])} \<union> {zz#path | path. path \<in> set (([xx#x] \<parallel> [yy # y]) \<parallel> [z])}"
        by (auto simp: cnf_concurrency_def)
      have "set ([xx # x] \<parallel> ([yy # y] \<parallel> [zz # z])) = {xx#path | path. path \<in> set ([x] \<parallel> ([yy # y] \<parallel> [zz # z]))} \<union> {yy#path | path. path \<in> set ([xx#x] \<parallel> ([y] \<parallel> [zz # z]))} \<union> {zz#path | path. path \<in> set ([xx#x] \<parallel> ([yy # y] \<parallel> [z]))}"
        by (auto simp: cnf_concurrency_def)

      then have "{xx#path | path. path \<in> set (([x] \<parallel> [yy # y]) \<parallel> [zz # z])} \<subseteq> {xx#path | path. path \<in> set ([x] \<parallel> ([yy # y] \<parallel> [zz # z]))}"
        using \<open>set (([x] \<parallel> [yy # y]) \<parallel> [zz # z]) \<subseteq> set ([x] \<parallel> ([yy # y] \<parallel> [zz # z]))\<close> by force

      then have "{yy#path | path. path \<in> set (([xx#x] \<parallel> [y]) \<parallel> [zz # z])} \<subseteq> {yy#path | path. path \<in> set ([xx#x] \<parallel> ([ y] \<parallel> [zz # z]))}"
        using \<open>set (([xx # x] \<parallel> [y]) \<parallel> [zz # z]) \<subseteq> set ([xx # x] \<parallel> ([y] \<parallel> [zz # z]))\<close> by fastforce

      then have "{zz#path | path. path \<in> set (([xx#x] \<parallel> [yy#y]) \<parallel> [z])} \<subseteq> {zz#path | path. path \<in> set ([xx#x] \<parallel> ([yy # y] \<parallel> [z]))}"
        using \<open>set (([xx # x] \<parallel> [yy # y]) \<parallel> [z]) \<subseteq> set ([xx # x] \<parallel> ([yy # y] \<parallel> [z]))\<close> by fastforce 

      then show "set (([xx # x] \<parallel> [yy # y]) \<parallel> [zz # z]) \<subseteq> set ([xx # x] \<parallel> ([yy # y] \<parallel> [zz # z]))"
        by (metis (no_types, lifting) Un_mono \<open>set (([xx # x] \<parallel> [yy # y]) \<parallel> [zz # z]) = {xx # path |path. path \<in> set (([x] \<parallel> [yy # y]) \<parallel> [zz # z])} \<union> {yy # path |path. path \<in> set (([xx # x] \<parallel> [y]) \<parallel> [zz # z])} \<union> {zz # path |path. path \<in> set (([xx # x] \<parallel> [yy # y]) \<parallel> [z])}\<close> \<open>set ([xx # x] \<parallel> ([yy # y] \<parallel> [zz # z])) = {xx # path |path. path \<in> set ([x] \<parallel> ([yy # y] \<parallel> [zz # z]))} \<union> {yy # path |path. path \<in> set ([xx # x] \<parallel> ([y] \<parallel> [zz # z]))} \<union> {zz # path |path. path \<in> set ([xx # x] \<parallel> ([yy # y] \<parallel> [z]))}\<close> \<open>{xx # path |path. path \<in> set (([x] \<parallel> [yy # y]) \<parallel> [zz # z])} \<subseteq> {xx # path |path. path \<in> set ([x] \<parallel> ([yy # y] \<parallel> [zz # z]))}\<close> \<open>{yy # path |path. path \<in> set (([xx # x] \<parallel> [y]) \<parallel> [zz # z])} \<subseteq> {yy # path |path. path \<in> set ([xx # x] \<parallel> ([y] \<parallel> [zz # z]))}\<close>)
    qed
  qed
qed 

lemma assoc_2: "set ([x] \<parallel> ([y] \<parallel> [z])) \<subseteq> set (([x] \<parallel> [y]) \<parallel> [z])"
proof (induction x arbitrary: y z)
  case Nil
  then show ?case by (auto simp: cnf_concurrency_def)
next
  case Cons1: (Cons xx x)
  then show ?case
  proof (induction y arbitrary: x z)
    case Nil
    then show ?case by (auto simp: cnf_concurrency_def)
  next
    case Cons2: (Cons yy y)
    then show ?case 
    proof (induction z arbitrary: x y)
      case Nil
      then show ?case by (auto simp: cnf_concurrency_def)
    next
      case Cons3: (Cons zz z)
      have "set (([x] \<parallel> [yy#y]) \<parallel> [zz#z]) \<supseteq> set ([x] \<parallel> ([yy#y] \<parallel> [zz#z]))"
        using Cons3.prems(2) by auto
      have "set (([xx#x] \<parallel> [y]) \<parallel> [zz#z]) \<supseteq> set ([xx#x] \<parallel> ([y] \<parallel> [zz#z]))"
        by (simp add: Cons3.prems(1) Cons3.prems(2))
      have "set (([xx#x] \<parallel> [yy#y]) \<parallel> [z]) \<supseteq> set ([xx#x] \<parallel> ([yy#y] \<parallel> [z]))"
        using Cons3.IH Cons3.prems(1) Cons3.prems(2) by blast

      have "set ([xx # x] \<parallel> [yy # y]) = {xx#path | path. path \<in> set ([x]\<parallel>[yy#y])} \<union> {yy#path | path. path \<in> set ([xx#x]\<parallel>[y])}" by (auto simp: cnf_concurrency_def)
      have "set (([xx # x] \<parallel> [yy # y]) \<parallel> [zz # z]) = {xx#path | path. path \<in> set (([x] \<parallel> [yy # y]) \<parallel> [zz # z])} \<union> {yy#path | path. path \<in> set (([xx#x] \<parallel> [y]) \<parallel> [zz # z])} \<union> {zz#path | path. path \<in> set (([xx#x] \<parallel> [yy # y]) \<parallel> [z])}"
        by (auto simp: cnf_concurrency_def)
      have "set ([xx # x] \<parallel> ([yy # y] \<parallel> [zz # z])) = {xx#path | path. path \<in> set ([x] \<parallel> ([yy # y] \<parallel> [zz # z]))} \<union> {yy#path | path. path \<in> set ([xx#x] \<parallel> ([y] \<parallel> [zz # z]))} \<union> {zz#path | path. path \<in> set ([xx#x] \<parallel> ([yy # y] \<parallel> [z]))}"
        by (auto simp: cnf_concurrency_def)

      then have "{xx#path | path. path \<in> set (([x] \<parallel> [yy # y]) \<parallel> [zz # z])} \<supseteq> {xx#path | path. path \<in> set ([x] \<parallel> ([yy # y] \<parallel> [zz # z]))}"
        using \<open>set (([x] \<parallel> [yy # y]) \<parallel> [zz # z]) \<supseteq> set ([x] \<parallel> ([yy # y] \<parallel> [zz # z]))\<close> by force

      then have "{yy#path | path. path \<in> set (([xx#x] \<parallel> [y]) \<parallel> [zz # z])} \<supseteq> {yy#path | path. path \<in> set ([xx#x] \<parallel> ([ y] \<parallel> [zz # z]))}"
        using \<open>set (([xx # x] \<parallel> [y]) \<parallel> [zz # z]) \<supseteq> set ([xx # x] \<parallel> ([y] \<parallel> [zz # z]))\<close> by fastforce

      then have "{zz#path | path. path \<in> set (([xx#x] \<parallel> [yy#y]) \<parallel> [z])} \<supseteq> {zz#path | path. path \<in> set ([xx#x] \<parallel> ([yy # y] \<parallel> [z]))}"
        using \<open>set (([xx # x] \<parallel> [yy # y]) \<parallel> [z]) \<supseteq> set ([xx # x] \<parallel> ([yy # y] \<parallel> [z]))\<close> by fastforce 

      then show "set (([xx # x] \<parallel> [yy # y]) \<parallel> [zz # z]) \<supseteq> set ([xx # x] \<parallel> ([yy # y] \<parallel> [zz # z]))"
        by (metis (no_types, lifting) Un_mono \<open>set (([xx # x] \<parallel> [yy # y]) \<parallel> [zz # z]) = {xx # path |path. path \<in> set (([x] \<parallel> [yy # y]) \<parallel> [zz # z])} \<union> {yy # path |path. path \<in> set (([xx # x] \<parallel> [y]) \<parallel> [zz # z])} \<union> {zz # path |path. path \<in> set (([xx # x] \<parallel> [yy # y]) \<parallel> [z])}\<close> \<open>set ([xx # x] \<parallel> ([yy # y] \<parallel> [zz # z])) = {xx # path |path. path \<in> set ([x] \<parallel> ([yy # y] \<parallel> [zz # z]))} \<union> {yy # path |path. path \<in> set ([xx # x] \<parallel> ([y] \<parallel> [zz # z]))} \<union> {zz # path |path. path \<in> set ([xx # x] \<parallel> ([yy # y] \<parallel> [z]))}\<close> \<open>{xx # path |path. path \<in> set ([x] \<parallel> ([yy # y] \<parallel> [zz # z]))} \<subseteq> {xx # path |path. path \<in> set (([x] \<parallel> [yy # y]) \<parallel> [zz # z])}\<close> \<open>{yy # path |path. path \<in> set ([xx # x] \<parallel> ([y] \<parallel> [zz # z]))} \<subseteq> {yy # path |path. path \<in> set (([xx # x] \<parallel> [y]) \<parallel> [zz # z])}\<close>)
    qed
  qed
qed 

lemma assoc_3: "set (([x] \<parallel> [y]) \<parallel> [z]) \<subseteq> set (((x#xs) \<parallel> (y#ys)) \<parallel> (z#zs))"
  by (auto simp: cnf_concurrency_def)

lemma assoc_4: "set ([x] \<parallel> ([y] \<parallel> [z])) \<subseteq> set ((x#xs) \<parallel> ((y#ys) \<parallel> (z#zs)))"
  by (auto simp: cnf_concurrency_def)

lemma assoc_5: "set xs = set xs' \<Longrightarrow> set ys = set ys' \<Longrightarrow> set (xs \<parallel> ys) = set (xs' \<parallel> ys')"
  apply (induction xs) apply (auto simp: cnf_concurrency_def)
  by (metis insertE)

lemma assoc_6: "y \<in> set ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> set ((x#xs) \<parallel> (y#ys)) =  set ((xs) \<parallel> (ys))"
  using assoc_5[of xs "x#xs" ys "y#ys"]
  by auto
  
lemma assoc_7: "set ((xs \<parallel> ys) \<parallel> zs) \<subseteq> set (xs \<parallel> (ys \<parallel> zs))"
  apply auto
proof -
  fix path
  assume "path \<in> set ((xs \<parallel> ys) \<parallel> zs)"
  obtain p_xy p_z where "path \<in> set (p_xy \<interleave> p_z) \<and> p_xy \<in> set (xs \<parallel> ys) \<and> p_z \<in> set zs"
    using \<open>path \<in> set ((xs \<parallel> ys) \<parallel> zs)\<close> path_decomp by blast
  obtain p_x p_y where "p_xy \<in> set (p_x \<interleave> p_y) \<and> p_x \<in> set xs \<and> p_y \<in> set ys"
    using \<open>path \<in> set (p_xy \<interleave> p_z) \<and> p_xy \<in> set (xs \<parallel> ys) \<and> p_z \<in> set zs\<close> path_decomp by blast
  
  have "path \<in> set (([p_x] \<parallel> [p_y]) \<parallel> [p_z])" apply (auto simp: cnf_concurrency_def)
    using \<open>p_xy \<in> set (p_x \<interleave> p_y) \<and> p_x \<in> set xs \<and> p_y \<in> set ys\<close> \<open>path \<in> set (p_xy \<interleave> p_z) \<and> p_xy \<in> set (xs \<parallel> ys) \<and> p_z \<in> set zs\<close> by auto
  have "path \<in> set ([p_x] \<parallel> ([p_y] \<parallel> [p_z]))"
    using \<open>path \<in> set (([p_x] \<parallel> [p_y]) \<parallel> [p_z])\<close> assoc_1 by blast
  have "path \<in> set ((p_x#xs) \<parallel> ((p_y#ys) \<parallel> (p_z#zs)))"
    using \<open>path \<in> set ([p_x] \<parallel> ([p_y] \<parallel> [p_z]))\<close> assoc_4 by blast
  show "path \<in> set (xs \<parallel> (ys \<parallel> zs))"
    by (smt (verit, ccfv_threshold) \<open>p_xy \<in> set (p_x \<interleave> p_y) \<and> p_x \<in> set xs \<and> p_y \<in> set ys\<close> \<open>path \<in> set ((p_x # xs) \<parallel> ((p_y # ys) \<parallel> (p_z # zs)))\<close> \<open>path \<in> set (p_xy \<interleave> p_z) \<and> p_xy \<in> set (xs \<parallel> ys) \<and> p_z \<in> set zs\<close> assoc_5 path_decomp path_decomp2 set_ConsD)
qed

theorem assoc_8: "set (xs \<parallel> (ys \<parallel> zs)) \<subseteq> set ((xs \<parallel> ys) \<parallel> zs)"
  apply auto
proof -
  fix path
  assume "path \<in> set (xs \<parallel> (ys \<parallel> zs))"
  obtain p_x p_yz where "path \<in> set (p_x \<interleave> p_yz) \<and> p_x \<in> set xs \<and> p_yz \<in> set (ys \<parallel> zs)"
    using \<open>path \<in> set (xs \<parallel> (ys \<parallel> zs))\<close> path_decomp by blast
  obtain p_y p_z where "p_yz \<in> set (p_y \<interleave> p_z) \<and> p_y \<in> set ys \<and> p_z \<in> set zs"
    by (meson \<open>path \<in> set (p_x \<interleave> p_yz) \<and> p_x \<in> set xs \<and> p_yz \<in> set (ys \<parallel> zs)\<close> path_decomp)
  
  have "path \<in> set ([p_x] \<parallel> ([p_y] \<parallel> [p_z]))" apply (auto simp: cnf_concurrency_def)
    using \<open>p_yz \<in> set (p_y \<interleave> p_z) \<and> p_y \<in> set ys \<and> p_z \<in> set zs\<close> \<open>path \<in> set (p_x \<interleave> p_yz) \<and> p_x \<in> set xs \<and> p_yz \<in> set (ys \<parallel> zs)\<close> by blast
  have "path \<in> set (([p_x] \<parallel> [p_y]) \<parallel> [p_z])"
    using \<open>path \<in> set ([p_x] \<parallel> ([p_y] \<parallel> [p_z]))\<close> assoc_2 by blast
  have "path \<in> set (((p_x#xs) \<parallel> (p_y#ys)) \<parallel> (p_z#zs))"
    by (meson \<open>path \<in> set (([p_x] \<parallel> [p_y]) \<parallel> [p_z])\<close> assoc_3 subsetD)
  show "path \<in> set ((xs \<parallel> ys) \<parallel> zs)"
    by (smt (verit, ccfv_threshold) \<open>p_yz \<in> set (p_y \<interleave> p_z) \<and> p_y \<in> set ys \<and> p_z \<in> set zs\<close> \<open>path \<in> set (((p_x # xs) \<parallel> (p_y # ys)) \<parallel> (p_z # zs))\<close> \<open>path \<in> set (p_x \<interleave> p_yz) \<and> p_x \<in> set xs \<and> p_yz \<in> set (ys \<parallel> zs)\<close> path_decomp path_decomp2 set_ConsD)
qed

theorem assoc_9: "set (xs \<parallel> (ys \<parallel> zs)) = set ((xs \<parallel> ys) \<parallel> zs)"
  by (simp add: assoc_7 assoc_8 subset_antisym)

theorem inter_size: "size (x \<interleave> y) > 0" apply (cases "x=[]") apply auto
  by (simp add: inter_prop1)

theorem inter_size2: "size (x \<interleave> y) = 1 \<Longrightarrow> size x = 0 \<or> size y = 0"
  apply auto apply (induction x) apply auto apply (induction y) apply auto
  by (metis inter_size less_numeral_extra(3) one_is_add)

theorem inter_size3: "size x = 0 \<or> size y = 0 \<Longrightarrow> size (x \<interleave> y) = 1"
  by auto

theorem interleaving_lemma: "size ([x] \<parallel> [y]) =  nmb_interleavings_pre (size x) (size y)"
  apply (auto simp: cnf_concurrency_def)
  by (simp add: nmb_interleavings_def number_interleav)

theorem inter_size4: "size (xs \<parallel> ys) = 1 \<Longrightarrow> size xs = 1 \<or> size ys = 1" apply (auto simp: cnf_concurrency_def)
  by (metis One_nat_def cnf_concurrency_def size_one1)

theorem conc_prop: "xs \<parallel> [[]] = xs" apply (induction xs) by (auto simp: cnf_concurrency_def)
theorem conc_prop2: "[[]] \<parallel> xs = xs" apply (induction xs) by (auto simp: cnf_concurrency_def)

theorem assoc_10: "size (xs \<parallel> (ys \<parallel> zs)) = 1 \<Longrightarrow> size ((xs \<parallel> ys) \<parallel> zs) = 1"
proof -
  assume a1: "size (xs \<parallel> (ys \<parallel> zs)) = 1"
  then obtain x where "xs = [x]" using size_one1[of xs "ys \<parallel> zs"]
    by (metis One_nat_def length_0_conv length_Suc_conv)
  from a1 obtain y where "ys = [y]" using size_one2[of xs "ys \<parallel> zs"] apply auto using size_one1[of ys zs]
    by (metis Suc_length_conv a1 length_0_conv)
  from a1 obtain z where "zs = [z]" using size_one2[of xs "ys \<parallel> zs"] apply auto using size_one2[of ys zs]
    by (metis Suc_length_conv a1 length_0_conv)
  have "size ([x] \<parallel> ([y] \<parallel> [z])) = 1"
    using \<open>xs = [x]\<close> \<open>ys = [y]\<close> \<open>zs = [z]\<close> a1 by auto
  then have "size (concat (map ((\<interleave>) x) (y \<interleave> z))) = 1" by (auto simp: cnf_concurrency_def)
  then have "size (y \<interleave> z) = 1" apply auto
    by (metis \<open>length ([x] \<parallel> ([y] \<parallel> [z])) = 1\<close> \<open>length (concat (map ((\<interleave>) x) (y \<interleave> z))) = 1\<close> interleaving_lemma nmb_interleavings_def number_interleav size_one2)
  have "y = [] \<or> z = []"
    using \<open>length (y \<interleave> z) = 1\<close> inter_size2 by auto
  have "size (([x] \<parallel> [y]) \<parallel> [z]) = 1"
  proof (cases "y = []")
    case True
    have "[x] \<parallel> [[]] = [x]"
      by (simp add: conc_prop)
    have "([x] \<parallel> [[]]) \<parallel> [z] = [x] \<parallel> [z]"
      by (simp add: \<open>[x] \<parallel> [[]] = [x]\<close>)
    then show ?thesis
      by (metis True \<open>length ([x] \<parallel> ([y] \<parallel> [z])) = 1\<close> conc_prop2)
  next
    case False
    have "z = []"
      using False \<open>y = [] \<or> z = []\<close> by auto
    then show ?thesis apply auto
      by (metis One_nat_def \<open>length ([x] \<parallel> ([y] \<parallel> [z])) = 1\<close> conc_prop)
  qed
  show "size ((xs \<parallel> ys) \<parallel> zs) = 1"
    by (simp add: \<open>length (([x] \<parallel> [y]) \<parallel> [z]) = 1\<close> \<open>xs = [x]\<close> \<open>ys = [y]\<close> \<open>zs = [z]\<close>)
qed

theorem assoc_11: "size ((xs \<parallel> ys) \<parallel> zs) = 1 \<Longrightarrow> size (xs \<parallel> (ys \<parallel> zs)) = 1"
  by (metis assoc_10 t4)
theorem assoc_12: "size (xs \<parallel> (ys \<parallel> zs)) = 1 \<equiv> size ((xs \<parallel> ys) \<parallel> zs) = 1"
  by (smt (verit, ccfv_threshold) assoc_10 assoc_11)

theorem assoc_cnf1: "equal_cnf ((xs \<parallel> ys) \<parallel> zs)  (xs \<parallel> (ys \<parallel> zs))"
  using equal_cnf_def assoc_10 assoc_11 assoc_9 by blast

theorem assoc_cnf: "evaluate ((xs \<parallel> ys) \<parallel> zs) = evaluate (xs \<parallel> (ys \<parallel> zs))" using equal_eval2
  using assoc_cnf1 by blast

theorem cnf_prop: "xs \<noteq> [] \<Longrightarrow> evaluate [x#xs] C = x ; (evaluate [xs] C)"
  apply (auto simp: evaluate_def)
  by (simp add: Concat_prop_10)

theorem cnf_prop2: "xs \<noteq> [] \<Longrightarrow> evaluate [xs@[x]] C = (evaluate [xs] C) ; x"
  apply (auto simp: evaluate_def)
  by (simp add: Concat_prop_2)

lemma restrict_cnf1: "D \<subseteq> C \<Longrightarrow> evaluate ([x] \<sslash>\<^sub>c C) D = (evaluate [x] D) \<sslash>\<^sub>p C"
proof (cases x)
  case Nil
  assume "D \<subseteq> C"
  then show ?thesis using Nil by (auto simp: evaluate_def Skip_def restriction_cnf_def restrict_p_def restrict_r_def S_def Field_def)
next
  case (Cons xx x)
  assume "D \<subseteq> C"
  have "evaluate ([xx#x] \<sslash>\<^sub>c C) D = evaluate [xx#x] D \<sslash>\<^sub>p C"
  proof (cases "x = []")
    case True
    then show ?thesis by (auto simp: evaluate_def restriction_cnf_def)
  next
    case False
    have "evaluate ([xx#x] \<sslash>\<^sub>c C) D = xx \<sslash>\<^sub>p C ; evaluate [x] D" apply (auto simp: evaluate_def restriction_cnf_def)
      by (simp add: Concat_prop_10 False)
    then show ?thesis
      by (simp add: False cnf_prop compose_absorb_1)
  qed
  then show ?thesis using Cons by auto
qed

theorem restr_distrib: "a \<sslash>\<^sub>p C \<union>\<^sub>p b \<sslash>\<^sub>p C = (a \<union>\<^sub>p b) \<sslash>\<^sub>p C"
  by (auto simp: choice_def restrict_p_def restr_post_def restrict_r_def S_def Field_def)

theorem restrict_cnf: "D \<subseteq> C \<Longrightarrow> evaluate (xs \<sslash>\<^sub>c C) D = (evaluate xs D) \<sslash>\<^sub>p C"
proof (induction xs)
  case Nil
  then show ?case  apply (auto simp: restriction_cnf_def evaluate_def restrict_p_def Fail_def S_def restrict_r_def) [1] done
next
  case (Cons x xs)
  then show "evaluate ((x#xs) \<sslash>\<^sub>c C) D = (evaluate (x#xs) D) \<sslash>\<^sub>p C"
  proof (cases "xs=[]")
    case True
    then show ?thesis
      by (simp add: Cons.prems restrict_cnf1)
  next
    case False
    have "(x#xs) \<sslash>\<^sub>c C = ([x] \<sslash>\<^sub>c C) @ (xs \<sslash>\<^sub>c C)" by (auto simp: restriction_cnf_def)
    have "evaluate ((x#xs) \<sslash>\<^sub>c C) D = evaluate (([x] \<sslash>\<^sub>c C) @ (xs \<sslash>\<^sub>c C)) D"
      by (simp add: \<open>(x # xs) \<sslash>\<^sub>c C = [x] \<sslash>\<^sub>c C @ xs \<sslash>\<^sub>c C\<close>)
    have "... = evaluate ([x] \<sslash>\<^sub>c C) D \<union>\<^sub>p evaluate (xs \<sslash>\<^sub>c C) D" using False apply (auto simp: evaluate_def)
      by (metis Choice_prop_7 choice_commute list.map_disc_iff not_Cons_self2 restriction_cnf_def)
    have "... = evaluate [x] D \<sslash>\<^sub>p C \<union>\<^sub>p evaluate xs D \<sslash>\<^sub>p C"
      by (simp add: local.Cons restrict_cnf1)
    have "... = (evaluate [x] D \<union>\<^sub>p evaluate xs D) \<sslash>\<^sub>p C"
      by (simp add: restr_distrib)
    have "... = (evaluate (x#xs) D) \<sslash>\<^sub>p C"
      by (simp add: False concat_prop3)
    then show ?thesis
      using \<open>evaluate ((x # xs) \<sslash>\<^sub>c C) D = evaluate ([x] \<sslash>\<^sub>c C @ xs \<sslash>\<^sub>c C) D\<close> \<open>evaluate ([x] \<sslash>\<^sub>c C @ xs \<sslash>\<^sub>c C) D = evaluate ([x] \<sslash>\<^sub>c C) D \<union>\<^sub>p evaluate (xs \<sslash>\<^sub>c C) D\<close> \<open>evaluate ([x] \<sslash>\<^sub>c C) D \<union>\<^sub>p evaluate (xs \<sslash>\<^sub>c C) D = evaluate [x] D \<sslash>\<^sub>p C \<union>\<^sub>p evaluate xs D \<sslash>\<^sub>p C\<close> \<open>evaluate [x] D \<sslash>\<^sub>p C \<union>\<^sub>p evaluate xs D \<sslash>\<^sub>p C = (evaluate [x] D \<union>\<^sub>p evaluate xs D) \<sslash>\<^sub>p C\<close> by presburger
  qed
qed

lemma corestrict_cnf1: "D \<subseteq> C \<Longrightarrow> evaluate ([x] \<setminus>\<^sub>c C) D = (evaluate [x] D) \<setminus>\<^sub>p C"
proof (induction x rule: rev_induct)
  case Nil
  then show ?case by (auto simp: evaluate_def Skip_def corestriction_cnf_def corestrict_p_def corestrict_r_def restrict_p_def restrict_r_def S_def Field_def)
next
  case (snoc xx x)
  have "evaluate ([x@[xx]] \<setminus>\<^sub>c C) D = evaluate [x@[xx]] D \<setminus>\<^sub>p C"
  proof (cases "x = []")
    case True
    have "Concat (corestrict_path [xx] C) D = xx \<setminus>\<^sub>p C"
      by (metis (no_types, lifting) Concat.simps(2) append1_eq_conv append_self_conv2 corestrict_path.elims list.distinct(1))
    then show ?thesis apply (auto simp: evaluate_def corestriction_cnf_def corestrict_p_def corestrict_r_def S_def Field_def)
      using True by auto
  next
    case False
    have "evaluate ([x@[xx]] \<setminus>\<^sub>c C) D = evaluate [x] D ; xx \<setminus>\<^sub>p C" apply (auto simp: evaluate_def corestriction_cnf_def)
      by (simp add: Concat_prop_2 False)
    then show ?thesis
      by (simp add: False cnf_prop2 corestrict_compose)
  qed
  then show ?case using Cons by auto
qed

theorem corestrict_cnf: "D \<subseteq> C \<Longrightarrow> evaluate (xs \<setminus>\<^sub>c C) D= (evaluate xs D) \<setminus>\<^sub>p C"
proof (induction xs)
  case Nil
  then show ?case  apply (auto simp: corestriction_cnf_def evaluate_def restrict_p_def Fail_def S_def restrict_r_def corestrict_p_def corestrict_r_def) [1] done
next
  case (Cons x xs)
  then show "evaluate ((x#xs) \<setminus>\<^sub>c C) D = (evaluate (x#xs) D) \<setminus>\<^sub>p C"
  proof (cases "xs=[]")
    case True
    then show ?thesis
      using Cons.prems corestrict_cnf1 by auto
  next
    case False
    have "(x#xs) \<setminus>\<^sub>c C = ([x] \<setminus>\<^sub>c C) @ (xs \<setminus>\<^sub>c C)" by (auto simp: corestriction_cnf_def)
    have "evaluate ((x#xs) \<setminus>\<^sub>c C) D = evaluate (([x] \<setminus>\<^sub>c C) @ (xs \<setminus>\<^sub>c C)) D"
      by (simp add: \<open>(x # xs) \<setminus>\<^sub>c C = [x] \<setminus>\<^sub>c C @ xs \<setminus>\<^sub>c C\<close>)
    have "... = evaluate ([x] \<setminus>\<^sub>c C) D \<union>\<^sub>p evaluate (xs \<setminus>\<^sub>c C) D" using False apply (auto simp: evaluate_def)
      by (metis Choice_prop_7 choice_commute list.map_disc_iff not_Cons_self2 corestriction_cnf_def)
    have "... = evaluate [x] D \<setminus>\<^sub>p C \<union>\<^sub>p evaluate xs D \<setminus>\<^sub>p C"
      by (simp add: local.Cons corestrict_cnf1)
    have "... = (evaluate [x] D \<union>\<^sub>p evaluate xs D) \<setminus>\<^sub>p C"
      by (simp add: corestrict_choice_1)
    have "... = (evaluate (x#xs) D) \<setminus>\<^sub>p C"
      by (simp add: False concat_prop3)
    then show ?thesis
      using \<open>evaluate ((x # xs) \<setminus>\<^sub>c C) D = evaluate ([x] \<setminus>\<^sub>c C @ xs \<setminus>\<^sub>c C) D\<close> \<open>evaluate ([x] \<setminus>\<^sub>c C @ xs \<setminus>\<^sub>c C) D = evaluate ([x] \<setminus>\<^sub>c C) D \<union>\<^sub>p evaluate (xs \<setminus>\<^sub>c C) D\<close> \<open>evaluate ([x] \<setminus>\<^sub>c C) D \<union>\<^sub>p evaluate (xs \<setminus>\<^sub>c C) D = evaluate [x] D \<setminus>\<^sub>p C \<union>\<^sub>p evaluate xs D \<setminus>\<^sub>p C\<close> \<open>evaluate [x] D \<setminus>\<^sub>p C \<union>\<^sub>p evaluate xs D \<setminus>\<^sub>p C = (evaluate [x] D \<union>\<^sub>p evaluate xs D) \<setminus>\<^sub>p C\<close> by presburger
  qed
qed
value "[[]] \<union>\<^sub>c []::nat CNF"
value "[[\<lparr>State = {}, Pre = {}, post = {}\<rparr>::nat Program]] \<parallel> ([[]] \<union>\<^sub>c [])"

theorem conc_prop1: "set (xs \<parallel> ys) \<subseteq> set (xs \<parallel> (y#ys))"
  apply auto
  by (meson list.set_intros(2) path_decomp path_decomp2)

theorem conc_prop3: "set (xs \<parallel> ys) \<subseteq> set (xs \<parallel> (ys \<union>\<^sub>c zs))"
proof (induction zs)
  case Nil
  then show ?case by (auto simp: choice_cnf_def)
next
  case (Cons z zs)
  have "set (xs \<parallel> ys) \<subseteq> set (xs \<parallel> (ys \<union>\<^sub>c (zs)))"
    by (simp add: local.Cons)
  have "set (ys \<union>\<^sub>c (z # zs)) = set ((z # zs) \<union>\<^sub>c ys)" by (auto simp: choice_cnf_def)
  have "set (xs \<parallel> (ys \<union>\<^sub>c (z # zs))) = set (xs \<parallel> ((z # zs) \<union>\<^sub>c ys))" 
    using assoc_5 [of xs xs "ys \<union>\<^sub>c (z # zs)" "(z # zs) \<union>\<^sub>c ys"] by (auto simp: choice_cnf_def)
  have "set (xs \<parallel> (ys \<union>\<^sub>c (zs))) = set (xs \<parallel> (zs \<union>\<^sub>c ys))"
    using assoc_5 [of xs xs "ys \<union>\<^sub>c zs" "zs \<union>\<^sub>c ys"] by (auto simp: choice_cnf_def)
  have "set (xs \<parallel> (ys \<union>\<^sub>c (zs))) \<subseteq> set (xs \<parallel> ((z # zs) \<union>\<^sub>c ys))"
    by (metis \<open>set (xs \<parallel> (ys \<union>\<^sub>c zs)) = set (xs \<parallel> (zs \<union>\<^sub>c ys))\<close> choice_cnf_commute cnf_choice2 conc_prop1)
  then show "set (xs \<parallel> ys) \<subseteq> set (xs \<parallel> (ys \<union>\<^sub>c (z # zs)))"
    using \<open>set (xs \<parallel> (ys \<union>\<^sub>c (z # zs))) = set (xs \<parallel> ((z # zs) \<union>\<^sub>c ys))\<close> local.Cons by auto 
qed
 
theorem conc_prop4: "set (xs \<parallel> (ys \<union>\<^sub>c zs)) = set (xs \<parallel> (zs \<union>\<^sub>c ys))"
  using assoc_5[of xs xs "ys \<union>\<^sub>c zs" "zs \<union>\<^sub>c ys"] by (auto simp: choice_cnf_def)

lemma conc_choice1_1: "set (xs \<parallel> (ys \<union>\<^sub>c zs)) = set ((xs \<parallel> ys) \<union>\<^sub>c (xs \<parallel> zs))" \<comment> \<open>/Conc_choice1/\<close>
  apply auto
   apply (smt (verit, del_insts) Un_iff choice_cnf_def path_decomp path_decomp2 set_append)
proof -
  fix x
  assume "x \<in> set (xs \<parallel> ys \<union>\<^sub>c xs \<parallel> zs)"
  then have "x \<in> set (xs \<parallel> ys) \<or> x \<in> set (xs \<parallel> zs)" by (auto simp: choice_cnf_def)
  show "x \<in> set (xs \<parallel> (ys \<union>\<^sub>c zs))"
  proof (cases "x \<in> set (xs \<parallel> ys)")
    case True
    then show ?thesis
      using conc_prop3 by auto 
  next
    case False
    then have "x \<in> set (xs \<parallel> zs)"
      using \<open>x \<in> set (xs \<parallel> ys) \<or> x \<in> set (xs \<parallel> zs)\<close> by auto
    have "set (xs \<parallel> (ys \<union>\<^sub>c zs)) = set (xs \<parallel> (zs \<union>\<^sub>c ys))"
      by (simp add: conc_prop4)
    then show ?thesis
      using \<open>x \<in> set (xs \<parallel> zs)\<close> conc_prop3 by blast 
  qed
qed

lemma choice_size1: "size (xs \<parallel> (ys \<union>\<^sub>c zs)) = 1 \<Longrightarrow> size ((xs \<parallel> ys) \<union>\<^sub>c (xs \<parallel> zs)) = 1"
proof -
  assume "size (xs \<parallel> (ys \<union>\<^sub>c zs)) = 1"
  have "size xs = 1"
    using \<open>length (xs \<parallel> (ys \<union>\<^sub>c zs)) = 1\<close> size_one1 size_one2 by auto
  have "size (ys \<union>\<^sub>c zs) = 1"
    using \<open>length (xs \<parallel> (ys \<union>\<^sub>c zs)) = 1\<close> size_one1 size_one2 by auto
  then have "size ys = 0 \<or> size zs = 0" apply (auto simp: choice_cnf_def)
    by (simp add: add_is_1)
  show "size ((xs \<parallel> ys) \<union>\<^sub>c (xs \<parallel> zs)) = 1"
  proof (cases "size xs = 0")
    case True
    have "length ([] \<parallel> ys \<union>\<^sub>c [] \<parallel> zs) = 1" apply auto
      using True \<open>length xs = 1\<close> by auto
    then show ?thesis
      using True by blast
  next
    case f1: False
    then show ?thesis
    proof (cases "size ys = 0")
      case True
      then show ?thesis
        by (metis \<open>length (xs \<parallel> (ys \<union>\<^sub>c zs)) = 1\<close> cnf_choice1 in_set_conv_nth less_nat_zero_code list.exhaust list.set_intros(1) path_decomp)
    next
      case False
      have "size zs = 0"
        using False \<open>length ys = 0 \<or> length zs = 0\<close> by auto
      then show ?thesis using \<open>length (xs \<parallel> (ys \<union>\<^sub>c zs)) = 1\<close> in_set_conv_nth less_nat_zero_code list.exhaust list.set_intros(1) path_decomp
        by (metis choice_cnf_def self_append_conv)
    qed
  qed
qed

lemma choice_size2: "size ((xs \<parallel> ys) \<union>\<^sub>c (xs \<parallel> zs)) = 1 \<Longrightarrow> size (xs \<parallel> (ys \<union>\<^sub>c zs)) = 1"
proof -
  assume "size ((xs \<parallel> ys) \<union>\<^sub>c (xs \<parallel> zs)) = 1"
  then have "size (xs \<parallel> zs) = 0 \<or> size (xs \<parallel> ys) = 0" apply (auto simp: choice_cnf_def)
    by (simp add: add_is_1)
  show "size (xs \<parallel> (ys \<union>\<^sub>c zs)) = 1"
  proof (cases "xs = []")
    case True
    then show ?thesis
      by (metis \<open>length (xs \<parallel> ys \<union>\<^sub>c xs \<parallel> zs) = 1\<close> \<open>length (xs \<parallel> zs) = 0 \<or> length (xs \<parallel> ys) = 0\<close> choice_cnf_def cnf_choice1 length_0_conv self_append_conv size_one1 zero_neq_one)
  next
    case f1: False
    then show ?thesis
    proof (cases "size (xs \<parallel> zs) = 0")
      case True
      then have "size zs = 0" using f1 apply (auto simp: cnf_concurrency_def)
        by (metis inter_prop1 interleave.simps(1) list.set_intros(1) neq_Nil_conv)
      then show ?thesis
        by (metis True \<open>length (xs \<parallel> ys \<union>\<^sub>c xs \<parallel> zs) = 1\<close> append.right_neutral choice_cnf_def length_0_conv)
    next
      case False
      then have "size (xs \<parallel> ys) = 0"
        using \<open>length (xs \<parallel> zs) = 0 \<or> length (xs \<parallel> ys) = 0\<close> by auto
      then have "size ys = 0" using f1 apply (auto simp: cnf_concurrency_def)
        by (metis inter_prop1 interleave.simps(1) list.set_intros(1) neq_Nil_conv)
      then show ?thesis
        by (metis \<open>length (xs \<parallel> ys \<union>\<^sub>c xs \<parallel> zs) = 1\<close> \<open>length (xs \<parallel> ys) = 0\<close> cnf_choice1 length_0_conv)
    qed
  qed
qed

lemma Conc_choice1_1: "equal_cnf ((xs \<parallel> ys) \<union>\<^sub>c (xs \<parallel> zs)) (xs \<parallel> (ys \<union>\<^sub>c zs))"
  using choice_size1 choice_size2 conc_choice1_1 equal_cnf_def by fastforce

theorem Conc_choice1_: "evaluate ((xs \<parallel> ys) \<union>\<^sub>c (xs \<parallel> zs)) = evaluate (xs \<parallel> (ys \<union>\<^sub>c zs))"
  using Conc_choice1_1 equal_eval by blast









theorem conc_prop5: "set (xs \<parallel> ys) \<subseteq> set ((x#xs) \<parallel> ys)"
  apply auto
  by (meson list.set_intros(2) path_decomp path_decomp2)

theorem conc_prop6: "set (xs \<parallel> ys) \<subseteq> set ((xs \<union>\<^sub>c zs) \<parallel> ys)"
proof (induction zs)
  case Nil
  then show ?case by (auto simp: choice_cnf_def)
next
  case (Cons z zs)
  have "set (xs \<parallel> ys) \<subseteq> set ((xs \<union>\<^sub>c zs) \<parallel> ys)"
    by (simp add: local.Cons)
  have "set (ys \<union>\<^sub>c (z # zs)) = set ((z # zs) \<union>\<^sub>c ys)" by (auto simp: choice_cnf_def)
  have "set ((xs \<union>\<^sub>c (z # zs)) \<parallel> ys) = set (((z # zs) \<union>\<^sub>c xs) \<parallel> ys)"
    using conc_prop4 is_permutation permutation_set_equality by blast 
  have "set ((xs \<union>\<^sub>c zs) \<parallel> ys) = set ((zs \<union>\<^sub>c xs) \<parallel> ys)"
    using conc_prop4 is_permutation permutation_set_equality by blast
  have "set ((zs \<union>\<^sub>c xs) \<parallel> ys) \<subseteq> set (((z # zs) \<union>\<^sub>c xs) \<parallel> ys)" using \<open>set ((xs \<union>\<^sub>c zs) \<parallel> ys) = set ((zs \<union>\<^sub>c xs) \<parallel> ys)\<close> choice_cnf_commute cnf_choice2
    by (metis conc_prop5)
  then show ?case
    using \<open>set ((xs \<union>\<^sub>c (z # zs)) \<parallel> ys) = set (((z # zs) \<union>\<^sub>c xs) \<parallel> ys)\<close> \<open>set ((xs \<union>\<^sub>c zs) \<parallel> ys) = set ((zs \<union>\<^sub>c xs) \<parallel> ys)\<close> local.Cons by auto
qed
 
theorem conc_prop7: "set ((zs \<union>\<^sub>c xs) \<parallel> ys) = set ((xs \<union>\<^sub>c zs) \<parallel> ys)"
  using conc_prop4 is_permutation permutation_set_equality by blast

lemma conc_choice2_1: "set ((xs \<union>\<^sub>c ys) \<parallel> zs) = set ((xs \<parallel> zs) \<union>\<^sub>c (ys \<parallel> zs))"
  apply auto
   apply (smt (verit, del_insts) Un_iff choice_cnf_def path_decomp path_decomp2 set_append)
  using choice_prop conc_prop6 conc_prop7 by blast

lemma choice_size3: "size ((xs \<union>\<^sub>c ys) \<parallel> zs) = 1 \<Longrightarrow> size ((xs \<parallel> zs) \<union>\<^sub>c (ys \<parallel> zs)) = 1"
proof -
  assume "size ((xs \<union>\<^sub>c ys) \<parallel> zs) = 1"
  have "size zs = 1"
    by (metis \<open>length ((xs \<union>\<^sub>c ys) \<parallel> zs) = 1\<close> size_one1 t4)
  have "size (xs \<union>\<^sub>c ys) = 1"
    by (metis \<open>length ((xs \<union>\<^sub>c ys) \<parallel> zs) = 1\<close> size_one2 t4)
  then have "size xs = 0 \<or> size ys = 0" apply (auto simp: choice_cnf_def)
    by (simp add: add_is_1)
  show "size ((xs \<parallel> zs) \<union>\<^sub>c (ys \<parallel> zs)) = 1"
  proof (cases "size zs = 0")
    case True
    have "length (xs \<parallel> [] \<union>\<^sub>c ys \<parallel> []) = 1" apply auto
      using True \<open>length zs = 1\<close> by auto
    then show ?thesis
      using True by blast
  next
    case f1: False
    then show ?thesis
    proof (cases "size ys = 0")
      case True
      then show ?thesis using \<open>length ((xs \<union>\<^sub>c ys) \<parallel> zs) = 1\<close> cnf_choice1 in_set_conv_nth less_nat_zero_code list.exhaust list.set_intros(1) path_decomp
      proof -
        have "\<forall>ps pss pssa. (\<exists>psa psb. (ps::'a Program list) \<in> set (psa \<interleave> psb) \<and> psb \<in> set pssa \<and> psa \<in> set pss) \<or> ps \<notin> set (pss \<parallel> pssa)"
          using path_decomp by blast
        then obtain pps :: "'a Program list \<Rightarrow> 'a Program list list \<Rightarrow> 'a Program list list \<Rightarrow> 'a Program list" and ppsa :: "'a Program list \<Rightarrow> 'a Program list list \<Rightarrow> 'a Program list list \<Rightarrow> 'a Program list" and ppsb :: "'a Program list \<Rightarrow> 'a Program list list \<Rightarrow> 'a Program list list \<Rightarrow> 'a Program list" and ppsc :: "'a Program list \<Rightarrow> 'a Program list list \<Rightarrow> 'a Program list list \<Rightarrow> 'a Program list" where
          f1: "\<forall>ps pss pssa. ps \<in> set (pps ps pss pssa \<interleave> ppsa ps pss pssa) \<and> ppsa ps pss pssa \<in> set pssa \<and> pps ps pss pssa \<in> set pss \<or> ps \<notin> set (pss \<parallel> pssa)"
          by metis
        obtain ppsd :: "'a Program list list \<Rightarrow> 'a Program list" and ppss :: "'a Program list list \<Rightarrow> 'a Program list list" and ppse :: "'a Program list list \<Rightarrow> 'a Program list" and ppssa :: "'a Program list list \<Rightarrow> 'a Program list list" where
          f2: "\<forall>pss. ppsd pss # ppss pss = pss \<or> [] = pss"
          by (metis (no_types) list.exhaust)
        have f3: "\<forall>ps pss. 0 < length ((ps::'a Program list) # pss)"
          by (metis length_pos_if_in_set list.set_intros(1))
        have f4: "\<forall>pss. ppsd pss \<in> set pss \<or> [] = pss"
          using f2 by (metis (no_types) list.set_intros(1))
        have f5: "[] = ys"
          using True by blast
        have f6: "\<forall>ps. (ps::'a Program list) \<notin> set []"
          by fastforce
        then have f7: "\<forall>pss. equal_cnf ((pss::'a Program list list) \<union>\<^sub>c []) pss"
          using f4 f1 by (metis (no_types) Conc_choice1_1 cnf_choice2 conc_prop)
        then have "1 = length xs"
          using f5 by (metis (no_types) \<open>length (xs \<union>\<^sub>c ys) = 1\<close> equal_cnf_def)
        then show ?thesis
          using f7 f6 f4 f3 f2 f1 by (metis (no_types) True \<open>length ((xs \<union>\<^sub>c ys) \<parallel> zs) = 1\<close> cnf_choice2 diff_is_0_eq diff_less impossible_Cons less_nat_zero_code less_one)
      qed
    next
      case False
      have "size xs = 0"
        using False \<open>length xs = 0 \<or> length ys = 0\<close> by auto
      then show ?thesis using cnf_choice1 in_set_conv_nth less_nat_zero_code list.exhaust list.set_intros(1) path_decomp
        by (metis \<open>length ((xs \<union>\<^sub>c ys) \<parallel> zs) = 1\<close>)
    qed
  qed
qed

lemma choice_size4: "size ((xs \<parallel> zs) \<union>\<^sub>c (ys \<parallel> zs)) = 1 \<Longrightarrow> size ((xs \<union>\<^sub>c ys) \<parallel> zs) = 1"
proof -
  assume "size ((xs \<parallel> zs) \<union>\<^sub>c (ys \<parallel> zs)) = 1"
  then have "size (xs \<parallel> zs) = 0 \<or> size (ys \<parallel> zs) = 0" apply (auto simp: choice_cnf_def)
    by (simp add: add_is_1)
  show "size ((xs \<union>\<^sub>c ys) \<parallel> zs) = 1"
  proof (cases "zs = []")
    case True
    then show ?thesis
      by (metis \<open>length (xs \<parallel> zs \<union>\<^sub>c ys \<parallel> zs) = 1\<close> \<open>length (xs \<parallel> zs) = 0 \<or> length (ys \<parallel> zs) = 0\<close> choice_cnf_def cnf_choice1 length_0_conv self_append_conv size_one2 zero_neq_one)
  next
    case f1: False
    then show ?thesis
    proof (cases "size (xs \<parallel> zs) = 0")
      case True
      then have "size xs = 0" using f1 apply (auto simp: cnf_concurrency_def)
        by (metis inter_prop1 interleave.simps(1) list.set_intros(1) neq_Nil_conv)
      then show ?thesis
        by (metis True \<open>length (xs \<parallel> zs \<union>\<^sub>c ys \<parallel> zs) = 1\<close> cnf_choice1 length_0_conv)
    next
      case False
      then have "size (ys \<parallel> zs) = 0"
        using \<open>length (xs \<parallel> zs) = 0 \<or> length (ys \<parallel> zs) = 0\<close> by blast
      then have "size ys = 0" using f1 apply (auto simp: cnf_concurrency_def)
        by (metis inter_prop1 interleave.simps(1) list.set_intros(1) neq_Nil_conv)
      then show ?thesis
        by (metis \<open>length (xs \<parallel> zs \<union>\<^sub>c ys \<parallel> zs) = 1\<close> \<open>length (ys \<parallel> zs) = 0\<close> choice_cnf_def length_0_conv self_append_conv)
    qed
  qed
qed

lemma Conc_choice2_1: "equal_cnf ((xs \<parallel> zs) \<union>\<^sub>c (ys \<parallel> zs)) ((xs \<union>\<^sub>c ys) \<parallel> zs)"
  using choice_size3 choice_size4 conc_choice2_1 equal_cnf_def by fastforce

theorem Conc_choice2_: "evaluate ((xs \<parallel> zs) \<union>\<^sub>c (ys \<parallel> zs)) = evaluate ((xs \<union>\<^sub>c ys) \<parallel> zs)"
  using Conc_choice2_1 equal_eval by blast

theorem eval_subprogram: "evaluate ys C \<preceq>\<^sub>p evaluate (y # ys) C"
  apply (auto simp: evaluate_def)
  by (metis Choice.simps(1) Choice_prop_1 Choice_prop_1_2 Choice_prop_3 fail_subprogram3 program_is_subprogram_of_choice)

theorem eval_subprogram2: "evaluate [y] C \<preceq>\<^sub>p evaluate (y # ys) C"
  apply (auto simp: evaluate_def)
  by (metis Choice.simps(2) Choice_prop_1_2 program_is_subprogram_of_choice subprogram_is_preorder)

lemma eval_subprogram3:"set xs \<subseteq> set [y] \<Longrightarrow> evaluate xs C \<preceq>\<^sub>p evaluate [y] C"
  apply (induction xs) apply (auto simp:)
  apply (simp add: eval_subprogram)
  by (metis choice_suprogram_prop concat_prop3 eval_subprogram2)

lemma eval_subprogram4:"set [x] \<subseteq> set ys \<Longrightarrow> evaluate [x] C \<preceq>\<^sub>p evaluate ys C"
  apply (induction ys) apply (auto simp:)
  apply (simp add: eval_subprogram2)
  by (meson eval_subprogram subprogram_is_transitive)

lemma eval_subprogram5: "size xs > 1 \<Longrightarrow> equal_cnf xs zs \<Longrightarrow> evaluate xs C = evaluate [] C \<union>\<^sub>p evaluate zs C"
proof -
  assume a1: "size xs > 1" and a2: "equal_cnf xs zs"
  have "evaluate xs C = evaluate zs C"
    by (simp add: a2 equal_eval)
  have "zs \<noteq> []"
    using a1 a2 equal_empty by force
  have "size zs > 1" using a1 a2 apply (auto simp: equal_cnf_def)
    by (simp add: Suc_lessI \<open>zs \<noteq> []\<close>)
  have "evaluate [] C \<union>\<^sub>p evaluate zs C = evaluate zs C" apply (auto simp: evaluate_def Fail_def)
    by (metis Choice_prop_18 Fail_def \<open>1 < length zs\<close> choice_commute length_map)
  show "evaluate xs C = evaluate [] C \<union>\<^sub>p evaluate zs C"
    by (simp add: \<open>evaluate [] C \<union>\<^sub>p evaluate zs C = evaluate zs C\<close> \<open>evaluate xs C = evaluate zs C\<close>)
qed

theorem eval_subprogram6: "size (ys @ zs) > 1 \<Longrightarrow> evaluate ys C \<union>\<^sub>p evaluate zs C = evaluate (ys \<union>\<^sub>c zs) C"
  apply (induction ys) apply (auto simp: choice_cnf_def evaluate_def)
  apply (metis Choice_prop_18 One_nat_def choice_commute length_map)
  apply (smt (verit, ccfv_threshold) Choice_prop_19 Cons_eq_appendI add_gr_0 choice_commute length_Cons length_append length_greater_0_conv length_map less_add_same_cancel1 plus_1_eq_Suc)
  by (smt (verit) Choice.simps(2) Choice_prop_1_2 Choice_prop_22 Choice_prop_7 Cons_eq_appendI choice_commute list.discI map_is_Nil_conv self_append_conv)

theorem eval_subprogram7: "size xs \<noteq> 1 \<Longrightarrow> equal_cnf xs (ys \<union>\<^sub>c zs) \<Longrightarrow> evaluate xs C = evaluate ys C \<union>\<^sub>p evaluate zs C"
  apply (cases "xs = []") apply (auto simp: choice_cnf_def)
  apply (simp add: equal_cnf_def evaluate_split1)
  apply (cases "ys = []") apply auto
  apply (simp add: Suc_lessI eval_subprogram5)
   apply (cases "zs = []")
  apply (simp add: equal_empty)
   apply (simp add: Suc_lessI eval_subprogram5)
  apply (cases "size ys = 1") using concat_prop3 equal_eval 
  apply (metis (no_types, lifting) Cons_eq_appendI One_nat_def append.right_neutral append_eq_append_conv append_eq_append_conv2 length_0_conv length_Suc_conv)
  apply (cases "size zs = 1") using equal_eval
  apply (metis (no_types, lifting) One_nat_def eval_prop1 length_0_conv length_Suc_conv)
proof -
  assume "length xs \<noteq> Suc 0" and "equal_cnf xs (ys @ zs)" and "xs \<noteq> []" and  "ys \<noteq> []" and "length ys \<noteq> 1" and "length zs \<noteq> 1"
  have "set xs = set ys \<union> set zs"
    by (metis \<open>equal_cnf xs (ys @ zs)\<close> equal_cnf_def set_append)
  have "evaluate ys C \<union>\<^sub>p evaluate zs C = evaluate (ys \<union>\<^sub>c zs) C"
    by (metis \<open>length ys \<noteq> 1\<close> \<open>ys \<noteq> []\<close> append.right_neutral choice_cnf_def evaluate_split evaluate_split1)
  show "evaluate xs C = evaluate ys C \<union>\<^sub>p evaluate zs C"
    by (simp add: \<open>equal_cnf xs (ys @ zs)\<close> \<open>evaluate ys C \<union>\<^sub>p evaluate zs C = evaluate (ys \<union>\<^sub>c zs) C\<close> choice_cnf_def equal_eval)
qed

lemma eval_subprogram8: "evaluate [x. x \<leftarrow> xs, f x] C \<preceq>\<^sub>p evaluate xs C"
proof (induction xs)
  case Nil
  then show ?case apply (simp add: subprogram_is_preorder) done
next
  case (Cons x xs)
  then show "evaluate [x. x \<leftarrow> (x#xs), f x] C \<preceq>\<^sub>p evaluate (x#xs) C"
  proof (cases "xs=[]")
    case True
    then show ?thesis apply auto
      apply (simp add: eval_subprogram2)
      by (simp add: eval_subprogram)
  next
    case f1: False
    then show ?thesis
  proof (cases "f x")
    case t1: True
    have "[x. x \<leftarrow> (x#xs), f x] = x#[x. x \<leftarrow> xs, f x]"
      by (simp add: t1)
    have "equal_cnf [x. x \<leftarrow> (x#xs), f x] ([x. x \<leftarrow> [x], f x] \<union>\<^sub>c [x. x \<leftarrow> xs, f x])" by (auto simp: equal_cnf_def choice_cnf_def)
    then show ?thesis
    proof (cases "[x. x \<leftarrow> xs, f x] = []")
      case True
      then show ?thesis apply auto
        apply (simp add: True eval_subprogram2)
        using local.t1 by blast
    next
      case False
    then have "evaluate [x. x \<leftarrow> (x#xs), f x] C = evaluate [x. x \<leftarrow> [x], f x] C \<union>\<^sub>p evaluate [x. x \<leftarrow> xs, f x] C" 
      using eval_subprogram7[of "[x. x \<leftarrow> (x#xs), f x]" "[x. x \<leftarrow> [x], f x]" "[x. x \<leftarrow> xs, f x]"]
      using \<open>concat (map (\<lambda>x. if f x then [x] else []) (x # xs)) = x # concat (map (\<lambda>x. if f x then [x] else []) xs)\<close> \<open>equal_cnf (concat (map (\<lambda>x. if f x then [x] else []) (x # xs))) (concat (map (\<lambda>x. if f x then [x] else []) [x]) \<union>\<^sub>c concat (map (\<lambda>x. if f x then [x] else []) xs))\<close> by fastforce
    have "evaluate [x. x \<leftarrow> xs, f x] C \<preceq>\<^sub>p evaluate xs C"
      by (simp add: local.Cons)
    then show ?thesis
      by (metis (no_types, lifting) False \<open>concat (map (\<lambda>x. if f x then [x] else []) (x # xs)) = x # concat (map (\<lambda>x. if f x then [x] else []) xs)\<close> choice_commute choice_safety1 concat_prop3 f1)
  qed
next
  case False
  show ?thesis
    using False eval_subprogram local.Cons subprogram_is_order by fastforce
qed
qed
qed

lemma eval_subprogram9: "evaluate [x. x \<leftarrow> (x#xx#xs), f x] C \<union>\<^sub>p evaluate [x. x \<leftarrow> x#xx#xs, \<not>f x] C = (evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (evaluate [x. x \<leftarrow> (xs), f x] C \<union>\<^sub>p evaluate [x. x \<leftarrow> xs, \<not>f x] C)"
proof (induction xs)
  case Nil
  have "(evaluate [x. x \<leftarrow> [], f x] C \<union>\<^sub>p evaluate [x. x \<leftarrow> [], \<not>f x] C) = Fail {}" by(auto simp: evaluate_def Fail_def choice_def restr_post_def S_def restrict_r_def)
  have "evaluate [x. x \<leftarrow> [x,xx], f x] C \<union>\<^sub>p evaluate [x. x \<leftarrow> [x,xx], \<not>f x] C = (evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (Fail {})"
    by (smt (z3) append.right_neutral choice_commute cnf_choice2 concat.simps(1) concat.simps(2) concat_prop2 concat_prop3 list.map_disc_iff list.simps(9) non_empty7 self_append_conv2 skip_prop_12 special_empty1)
  then show "evaluate [x. x \<leftarrow> [x,xx], f x] C \<union>\<^sub>p evaluate [x. x \<leftarrow> [x,xx], \<not>f x] C = (evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (evaluate [x. x \<leftarrow> [], f x] C \<union>\<^sub>p evaluate [x. x \<leftarrow> [], \<not>f x] C)"
    using \<open>evaluate (concat (map (\<lambda>x. if f x then [x] else []) [])) C \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) [])) C = Fail {}\<close> by argo
next
  case (Cons a xs)
  then show ?case
  proof (cases "f a")
    case True
    then have "evaluate [x. x \<leftarrow> (x#xx#a#xs), f x] C \<union>\<^sub>p evaluate [x. x \<leftarrow> x#xx#a#xs, \<not>f x] C = (evaluate [a] C \<union>\<^sub>p evaluate [x. x \<leftarrow> (x#xx#xs), f x] C) \<union>\<^sub>p evaluate [x. x \<leftarrow> x#xx#xs, \<not>f x] C"
      apply (auto simp add: evaluate_def)
      apply (smt (verit) Choice_prop_22 choice_assoc_1 choice_commute)
      apply (metis (no_types, lifting) Choice_prop_1_4 foldl_Cons list.distinct(1))
      apply (smt (z3) Choice.simps(2) Choice_prop_1_2 Choice_prop_1_4 choice_assoc_1 choice_commute foldl_Nil)
      by (simp add: fold_choice)
    have "... = evaluate [a] C \<union>\<^sub>p ((evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p ((evaluate [x. x \<leftarrow> xs, f x] C) \<union>\<^sub>p evaluate [x. x \<leftarrow> xs, \<not>f x] C))"
      by (metis (no_types, lifting) choice_assoc_1 local.Cons)
    have "... = ((evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (evaluate [a] C \<union>\<^sub>p ((evaluate [x. x \<leftarrow> xs, f x] C) \<union>\<^sub>p evaluate [x. x \<leftarrow> xs, \<not>f x] C)))"
      by (smt (verit, del_insts) choice_assoc_1 choice_commute)
    have "... = (evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (evaluate [x. x \<leftarrow> (a#xs), f x] C \<union>\<^sub>p evaluate [x. x \<leftarrow> (a#xs), \<not>f x] C)"
      apply (auto simp: evaluate_def)
      apply (simp add: True)
      by (smt (z3) Choice_prop_22 choice_assoc_1 choice_commute)
    then show ?thesis
      using \<open>(evaluate [a] C \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if f x then [x] else []) (x # xx # xs))) C) \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) (x # xx # xs))) C = evaluate [a] C \<union>\<^sub>p ((evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (evaluate (concat (map (\<lambda>x. if f x then [x] else []) xs)) C \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) xs)) C))\<close> \<open>evaluate (concat (map (\<lambda>x. if f x then [x] else []) (x # xx # a # xs))) C \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) (x # xx # a # xs))) C = (evaluate [a] C \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if f x then [x] else []) (x # xx # xs))) C) \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) (x # xx # xs))) C\<close> \<open>evaluate [a] C \<union>\<^sub>p ((evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (evaluate (concat (map (\<lambda>x. if f x then [x] else []) xs)) C \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) xs)) C)) = (evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (evaluate [a] C \<union>\<^sub>p (evaluate (concat (map (\<lambda>x. if f x then [x] else []) xs)) C \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) xs)) C))\<close> by argo
  next
    case False
    then have "evaluate [x. x \<leftarrow> (x#xx#a#xs), f x] C \<union>\<^sub>p evaluate [x. x \<leftarrow> x#xx#a#xs, \<not>f x] C = evaluate [x. x \<leftarrow> (x#xx#xs), f x] C \<union>\<^sub>p (evaluate [a] C \<union>\<^sub>p evaluate [x. x \<leftarrow> x#xx#xs, \<not>f x] C)"
      apply (auto simp add: evaluate_def)
      apply (smt (verit) Choice_prop_22 choice_assoc_1 choice_commute)
      apply (metis (no_types, lifting) Choice_prop_1_4 foldl_Cons list.distinct(1))
      apply (smt (z3) Choice.simps(2) Choice_prop_1_2 Choice_prop_1_4 choice_assoc_1 choice_commute foldl_Nil)
      by (simp add: fold_choice)
    have "... = evaluate [a] C \<union>\<^sub>p ((evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p ((evaluate [x. x \<leftarrow> xs, f x] C) \<union>\<^sub>p evaluate [x. x \<leftarrow> xs, \<not>f x] C))"
      by (smt (verit, best) choice_assoc_1 choice_commute local.Cons)
    have "... = ((evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (evaluate [a] C \<union>\<^sub>p ((evaluate [x. x \<leftarrow> xs, f x] C) \<union>\<^sub>p evaluate [x. x \<leftarrow> xs, \<not>f x] C)))"
      by (smt (verit, del_insts) choice_assoc_1 choice_commute)
    have "... = (evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (evaluate [x. x \<leftarrow> (a#xs), f x] C \<union>\<^sub>p evaluate [x. x \<leftarrow> (a#xs), \<not>f x] C)"
      apply (auto simp: evaluate_def)
      apply (smt (verit, ccfv_threshold) Choice_prop_22 choice_assoc_1 choice_commute)
      by (smt (z3) Choice_prop_22 choice_assoc_1 choice_commute)
    then show ?thesis
      using \<open>evaluate (concat (map (\<lambda>x. if f x then [x] else []) (x # xx # a # xs))) C \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) (x # xx # a # xs))) C = evaluate (concat (map (\<lambda>x. if f x then [x] else []) (x # xx # xs))) C \<union>\<^sub>p (evaluate [a] C \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) (x # xx # xs))) C)\<close> \<open>evaluate (concat (map (\<lambda>x. if f x then [x] else []) (x # xx # xs))) C \<union>\<^sub>p (evaluate [a] C \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) (x # xx # xs))) C) = evaluate [a] C \<union>\<^sub>p ((evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (evaluate (concat (map (\<lambda>x. if f x then [x] else []) xs)) C \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) xs)) C))\<close> \<open>evaluate [a] C \<union>\<^sub>p ((evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (evaluate (concat (map (\<lambda>x. if f x then [x] else []) xs)) C \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) xs)) C)) = (evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (evaluate [a] C \<union>\<^sub>p (evaluate (concat (map (\<lambda>x. if f x then [x] else []) xs)) C \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) xs)) C))\<close> by argo
  qed
qed

lemma eval_subprogram10: "(evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (evaluate [x. x \<leftarrow> (xs), f x] C \<union>\<^sub>p evaluate [x. x \<leftarrow> xs, \<not>f x] C) = (evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (evaluate xs C)"
proof (induction xs)
  case Nil
  then show ?case apply (auto simp: evaluate_def)
    by (metis choice_assoc_1 choice_commute choice_idem_5)
next
  case (Cons a xs)
  then show ?case apply (auto simp: evaluate_def)
    apply (smt (z3) Choice_prop_22 choice_assoc_1 choice_commute)
    by (smt (z3) Choice_prop_22 choice_assoc_1 choice_commute)
qed

lemma eval_subprogram11: "size xs > 1 \<Longrightarrow> evaluate [x. x \<leftarrow> xs, f x] C \<union>\<^sub>p evaluate [x. x \<leftarrow> xs, \<not>f x] C = evaluate xs C"
proof -
  assume "size xs > 1"
  then obtain x xx xs' where "xs=x#xx#xs'" apply auto
    by (metis length_0_conv length_Cons less_irrefl_nat less_nat_zero_code remdups_adj.cases)
  have "evaluate (x#xx#xs') C = (evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p evaluate xs' C"
    by (metis \<open>1 < length xs\<close> \<open>xs = x # xx # xs'\<close> choice_cnf_def cnf_choice2 cnf_choice3 concat_prop3 eval_subprogram6 list.distinct(1))
  have "evaluate [x. x \<leftarrow> (x#xx#xs'), f x] C \<union>\<^sub>p evaluate [x. x \<leftarrow> x#xx#xs', \<not>f x] C = (evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (evaluate [x. x \<leftarrow> (xs'), f x] C \<union>\<^sub>p evaluate [x. x \<leftarrow> xs', \<not>f x] C)"
    using eval_subprogram9 by blast
  have "... = (evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (evaluate xs' C)"
    using eval_subprogram10 by blast
  have "evaluate [x. x \<leftarrow> (x#xx#xs'), f x] C \<union>\<^sub>p evaluate [x. x \<leftarrow> x#xx#xs', \<not>f x] C = evaluate (x#xx#xs') C"
    using \<open>(evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (evaluate (concat (map (\<lambda>x. if f x then [x] else []) xs')) C \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) xs')) C) = (evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p evaluate xs' C\<close> \<open>evaluate (concat (map (\<lambda>x. if f x then [x] else []) (x # xx # xs'))) C \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) (x # xx # xs'))) C = (evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p (evaluate (concat (map (\<lambda>x. if f x then [x] else []) xs')) C \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) xs')) C)\<close> \<open>evaluate (x # xx # xs') C = (evaluate [x] C \<union>\<^sub>p evaluate [xx] C) \<union>\<^sub>p evaluate xs' C\<close> by argo
  show "evaluate [x. x \<leftarrow> xs, f x] C \<union>\<^sub>p evaluate [x. x \<leftarrow> xs, \<not>f x] C = evaluate xs C"
    using \<open>evaluate (concat (map (\<lambda>x. if f x then [x] else []) (x # xx # xs'))) C \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) (x # xx # xs'))) C = evaluate (x # xx # xs') C\<close> \<open>xs = x # xx # xs'\<close> by blast
qed


theorem eval_subprogram12: "set xs \<subseteq> set ys \<Longrightarrow> evaluate xs C\<preceq>\<^sub>p evaluate ys C"
  apply (cases "xs = []") apply auto
   apply (simp add: concat_prop2 fail_subprogram3)
  apply (cases "ys = []")
   apply simp
  apply (cases "size ys = 1")
   apply (metis One_nat_def eval_subprogram3 length_0_conv length_Suc_conv)
  apply (cases "size xs = 1")
   apply (metis One_nat_def Suc_length_conv eval_subprogram4 length_0_conv)
proof -
  assume a1: "set xs \<subseteq> set ys" and a2: "xs \<noteq> []" and a3: "ys \<noteq> []" and a4: "length ys \<noteq> 1" and a5: "length xs \<noteq> 1"
  have "size xs > 1"
    using \<open>length xs \<noteq> 1\<close> \<open>xs \<noteq> []\<close> nat_neq_iff by auto
  have "size ys > 1"
    using \<open>length ys \<noteq> 1\<close> \<open>ys \<noteq> []\<close> nat_neq_iff by auto
  obtain ys' where o1: "ys' = [y. y \<leftarrow> ys, y \<in> set xs]" by simp
  obtain ys'' where o2: "ys'' = [y. y \<leftarrow> ys, y \<notin> set xs]" by simp
  have "evaluate ys' C \<preceq>\<^sub>p evaluate ys C" apply (simp add: o1) using eval_subprogram8[of "\<lambda>y. y \<in> set xs" ys] by auto
  have "set ys' \<union> set ys'' = set ys" using o1 o2 by auto
  have "set ys' = set xs" using o1 a1 by auto
  have "size ys' > 0" apply auto
    using \<open>set ys' = set xs\<close> a2 by auto
  have "evaluate ys' C \<union>\<^sub>p evaluate ys'' C = evaluate ys C" apply (simp add: o1 o2) using eval_subprogram11[of ys "\<lambda>y. y \<in> set xs"] apply auto
    using \<open>1 < length ys\<close>
    using \<open>\<And>C. 1 < length ys \<Longrightarrow> evaluate (concat (map (\<lambda>x. if x \<in> set xs then [x] else []) ys)) C \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if x \<notin> set xs then [x] else []) ys)) C = evaluate ys C\<close> by blast
  show "evaluate xs C \<preceq>\<^sub>p evaluate ys C"
  proof (cases "size ys' = 1")
    case True
    have "card (set xs) = 1"
      by (metis True \<open>0 < length ys'\<close> \<open>set ys' = set xs\<close> le_numeral_extra(4) length_greater_0_conv rotate1_fixpoint_card rotate1_length01)
    then obtain x where "set xs = {x}" apply auto
      using \<open>card (set xs) = 1\<close> card_1_singletonE by blast
    have "evaluate xs C = evaluate [x] C \<union>\<^sub>p evaluate [x] C"
      by (metis \<open>1 < length xs\<close> \<open>set xs = {x}\<close> evaluate_prop2 singleton_iff)
    then show ?thesis
    proof (cases "set xs = set ys")
      case True
      then show ?thesis
        by (simp add: \<open>evaluate xs C = evaluate [x] C \<union>\<^sub>p evaluate [x] C\<close> \<open>set xs = {x}\<close> choice_decomp_1 eval_subprogram4)
    next
      case False
      have "ys'' \<noteq> []"
        using False \<open>set ys' = set xs\<close> \<open>set ys' \<union> set ys'' = set ys\<close> by fastforce
      then show ?thesis
        by (metis \<open>evaluate xs C = evaluate [x] C \<union>\<^sub>p evaluate [x] C\<close> \<open>set xs = {x}\<close> a1 choice_decomp_1 empty_set eval_subprogram4 list.simps(15))
    qed
  next
    case False
    have "size ys' > 1"
      using False \<open>0 < length ys'\<close> nat_neq_iff by auto
    have "equal_cnf xs ys'" apply (auto simp: equal_cnf_def)
      apply (auto simp add: \<open>set ys' = set xs\<close>)
      using \<open>1 < length xs\<close> apply auto
      using False by linarith
    have "evaluate xs C = evaluate ys' C"
      by (simp add: \<open>equal_cnf xs ys'\<close> equal_eval)

    then show ?thesis
      by (simp add: \<open>evaluate ys' C \<preceq>\<^sub>p evaluate ys C\<close>)
  qed
qed

(*
definition p :: "nat CNF"
  where "p = [[\<lparr>State = {}, Pre = {}, post = {}\<rparr>]]"
definition q :: "nat CNF"
  where "q = [[]]"
definition r :: "nat CNF"
  where "r = [[\<lparr>State = {}, Pre = {}, post = {}\<rparr>]]"

value "(p \<parallel> q) ;\<^sub>c r"
value "p \<parallel> (q ;\<^sub>c r)"
*)

lemma subset1: "set (p ;\<^sub>c xs) \<subseteq> set (p ;\<^sub>c (x#xs))"
  by (auto simp: composition_cnf_def)

lemma subset2: "set (xs ;\<^sub>c p) \<subseteq> set ((x#xs) ;\<^sub>c p)"
  by (auto simp: composition_cnf_def)

lemma subset3: "set (p \<union>\<^sub>c xs) \<subseteq> set (p \<union>\<^sub>c (x#xs))"
  by (auto simp: choice_cnf_def)

lemma subset4: "set (xs \<union>\<^sub>c p) \<subseteq> set ((x#xs) \<union>\<^sub>c p)"
  by (auto simp: choice_cnf_def)

lemma subset5: "set q \<subseteq> set q' \<Longrightarrow> set (p ;\<^sub>c q) \<subseteq> set (p ;\<^sub>c q')"
  by (auto simp: composition_cnf_def)

lemma subset6: "set q \<subseteq> set q' \<Longrightarrow> set (q ;\<^sub>c p) \<subseteq> set (q' ;\<^sub>c p)"
  by (auto simp: composition_cnf_def)

lemma subset7: "set q \<subseteq> set q' \<Longrightarrow> set (p \<union>\<^sub>c q) \<subseteq> set (p \<union>\<^sub>c q')"
  by (auto simp: choice_cnf_def)

lemma subset8: "set q \<subseteq> set q' \<Longrightarrow> set (q \<union>\<^sub>c p) \<subseteq> set (q' \<union>\<^sub>c p)"
  by (auto simp: choice_cnf_def)

lemma subset9: "set q \<subseteq> set q' \<Longrightarrow> set (p \<parallel> q) \<subseteq> set (p \<parallel> q')"
proof (induction q' arbitrary: q)
  case Nil
  then show ?case by auto
next
  case (Cons a q')
  then show "set (p \<parallel> q) \<subseteq> set (p \<parallel> (a # q'))"
  proof (cases "a \<in> set q'")
    case True
    then show ?thesis
      by (metis (no_types, lifting) Cons.IH Cons.prems conc_prop1 set_ConsD subset_code(1))
  next
    case f1: False
    then show ?thesis
    proof (cases "a \<in> set q")
      case True
      obtain q'' where "set q'' = set q - {a}"
        by (meson set_removeAll)
      have "set (p \<parallel> (q'')) \<subseteq> set (p \<parallel> (q'))"
        by (metis Cons.IH Cons.prems True \<open>set q'' = set q - {a}\<close> list.simps(15) subset_insert_iff)
      then have "set (p \<parallel> (a # q'')) \<subseteq> set (p \<parallel> (a # q'))"
        apply (auto simp: cnf_concurrency_def)
        by (metis (mono_tags, lifting) Cons.prems Diff_iff \<open>set q'' = set q - {a}\<close> in_mono insert_iff set_ConsD)
      then show ?thesis
        by (smt (verit) True \<open>set q'' = set q - {a}\<close> assoc_5 insert_Diff list.simps(15))
    next
      case False
      then show ?thesis
        by (metis (no_types, lifting) Cons.IH Cons.prems conc_prop1 set_ConsD subset_code(1))
    qed
  qed
qed


lemma subset10: "set q \<subseteq> set q' \<Longrightarrow> set (q \<parallel> p) \<subseteq> set (q' \<parallel> p)"
proof (induction q' arbitrary: q)
  case Nil
  then show ?case by auto
next
  case (Cons a q')
  then show "set (q \<parallel> p) \<subseteq> set ((a # q') \<parallel> p)"
  proof (cases "a \<in> set q'")
    case True
    then show ?thesis
      by (metis Cons.prems is_permutation permutation_set_equality subset9)
  next
    case f1: False
    then show ?thesis
    proof (cases "a \<in> set q")
      case True
      obtain q'' where "set q'' = set q - {a}"
        by (meson set_removeAll)
      have "set (q'' \<parallel> p) \<subseteq> set (q' \<parallel> p)"
        by (metis Cons.IH Cons.prems True \<open>set q'' = set q - {a}\<close> list.simps(15) subset_insert_iff)
      then have "set ((a # q'') \<parallel> p) \<subseteq> set ((a # q') \<parallel> p)"
        by (auto simp: cnf_concurrency_def)
      then show ?thesis
        by (smt (verit) True \<open>set q'' = set q - {a}\<close> assoc_5 insert_Diff list.simps(15))
    next
      case False
      then show ?thesis
        by (metis Cons.prems is_permutation permutation_set_equality subset9)
    qed
  qed
qed

lemma interleav_prop: "ps @ rs \<in> set (ps \<interleave> rs)"
proof (induction "ps")
  case Nil
  then show ?case by auto
next
  case Cons1: (Cons p ps)
  then show ?case
  proof (induction "rs")
    case Nil
    then show ?case by auto
  next
    case (Cons r rs)
    have "(p#ps) \<interleave> (r#rs) = map ((#) p) (ps \<interleave> (r#rs)) @ map ((#) r) ((p#ps) \<interleave> rs)" by simp
    have "(ps) @ (r#rs) \<in> set (ps \<interleave> (r#rs))"
      by (simp add: Cons.prems)
    then have "(ps) @ (r#rs) \<in> set ((ps \<interleave> (r#rs)) @ map ((#) r) (ps \<interleave> rs))"
      by auto
    then have "(p#ps) @ (r#rs) \<in> set (map ((#) p) (ps \<interleave> (r#rs)) @ map ((#) r) ((p#ps) \<interleave> rs))"
      apply auto
      by (smt (verit) image_eqI inter_leav2 interleave.elims list.set_intros(1) self_append_conv2)
    have "(p#ps) @ (r#rs) \<in> set ((p#ps) \<interleave> (r#rs))"
      using \<open>(p # ps) @ r # rs \<in> set (map ((#) p) (ps \<interleave> (r # rs)) @ map ((#) r) ((p # ps) \<interleave> rs))\<close> \<open>(p # ps) \<interleave> (r # rs) = map ((#) p) (ps \<interleave> (r # rs)) @ map ((#) r) ((p # ps) \<interleave> rs)\<close> by presburger
    then show ?case
      using Cons1 local.Cons by blast
  qed
qed



lemma prop5: "set (map (\<lambda>xs. xs @ [p]) (ps \<interleave> (qs @ [q]))) = {tr @ [p] |tr. tr \<in> set (ps \<interleave> (qs @ [q]))}"
proof -
  have "set (map (\<lambda>xs. xs @ [q]) ((ps @ [p]) \<interleave> qs )) = set (map (\<lambda>xs. xs @ [q]) (qs \<interleave> (ps @ [p])))"
    by (meson inter_perm perm_prop_2 permutation_set_equality)
  have "{tr @ [q] |tr. tr \<in> set ((ps @ [p]) \<interleave> qs)} = {tr @ [q] |tr. tr \<in> set (qs \<interleave> (ps @ [p]))}"
    using inter_perm permutation_set_equality by blast
  show ?thesis
    by auto
qed

lemma prop6: "set (map (\<lambda>xs. xs @ [q]) ((ps @ [p]) \<interleave> qs )) = {tr @ [q] |tr. tr \<in> set ((ps @ [p]) \<interleave> qs)}"
proof -
  have "set (map (\<lambda>xs. xs @ [q]) ((ps @ [p]) \<interleave> qs )) = set (map (\<lambda>xs. xs @ [q]) (qs \<interleave> (ps @ [p])))"
    by (meson inter_perm perm_prop_2 permutation_set_equality)
  have "{tr @ [q] |tr. tr \<in> set ((ps @ [p]) \<interleave> qs)} = {tr @ [q] |tr. tr \<in> set (qs \<interleave> (ps @ [p]))}"
    using inter_perm permutation_set_equality by blast
  show ?thesis
    by auto
qed

lemma prop3_1: "[x] \<interleave> ys = insert_all x ys"
  apply (induction ys) by auto

lemma prop3_2: "ys \<interleave> [x] = rev (insert_all x ys)"
  apply (induction ys) apply auto
  by (simp add: rev_map)

lemma prop3_3: "set ([x] \<interleave> (y#ys)) = {x#y#ys} \<union> {y#x#ys} \<union> ((#) y) ` set ([x] \<interleave> ys)"
  apply auto
  by (auto simp add: l2 prop3_1)

lemma prop3_4: "set ([x] \<interleave> (ys@[y])) = {ys@[x,y]} \<union> {ys@[y,x]} \<union> (\<lambda>tr. tr@[y]) ` set ([x] \<interleave> ys)"
  apply (induction ys) by auto

lemma prop3_5: "set ([x] \<interleave> rev (y#ys)) = {(rev ys)@[x,y]} \<union> {(rev ys)@[y,x]} \<union> (\<lambda>tr. tr@[y]) ` set ([x] \<interleave> (rev ys))"
  apply (induction ys) apply auto[1]
  by (metis prop3_4 rev.simps(2))

lemma prop3_6: "{rev tr |tr. tr \<in> set ([x] \<interleave> (ys))} = set ([x] \<interleave> rev ys)"
proof (induction ys)
  case Nil
  then show ?case by auto
next
  case (Cons y ys)
  have "set ([x] \<interleave> (y # ys)) = {x#y#ys} \<union> {y#x#ys} \<union> ((#) y) ` set ([x] \<interleave> ys)"
    by (meson prop3_3)
  have "rev ` (set ([x] \<interleave> ys)) = set ([x] \<interleave> rev ys)" using Cons Setcompr_eq_image[of rev "set ([x] \<interleave> ys)"] by auto
  have "rev ` ((#) y) ` set ([x] \<interleave> ys) = (\<lambda>tr. tr@[y]) ` set ([x] \<interleave> rev ys)" apply auto
    using local.Cons apply auto[1]
    using \<open>rev ` set ([x] \<interleave> ys) = set ([x] \<interleave> rev ys)\<close> image_iff by fastforce

  have "set ([x] \<interleave> rev (y # ys)) = {(rev ys)@[x,y]} \<union> {(rev ys)@[y,x]} \<union> (\<lambda>tr. tr@[y]) ` set ([x] \<interleave> rev ys)"
    by (metis prop3_5)

  have "{rev tr |tr. tr \<in> set ([x] \<interleave> (y # ys))} = rev ` set ([x] \<interleave> (y # ys))" apply auto
    by (metis Cons_eq_appendI append_assoc rev.simps(2) self_append_conv2)
  have "... = {(rev ys)@[x,y]} \<union> {(rev ys)@[y,x]} \<union> (\<lambda>tr. tr@[y]) ` rev ` set ([x] \<interleave> ys)"
    by (smt (verit, del_insts) Un_commute Un_empty_left Un_insert_left \<open>rev ` (#) y ` set ([x] \<interleave> ys) = (\<lambda>tr. tr @ [y]) ` set ([x] \<interleave> rev ys)\<close> \<open>rev ` set ([x] \<interleave> ys) = set ([x] \<interleave> rev ys)\<close> \<open>set ([x] \<interleave> (y # ys)) = {x # y # ys} \<union> {y # x # ys} \<union> (#) y ` set ([x] \<interleave> ys)\<close> append_assoc hd_step image_insert l8 rev.simps(2) tl_step)

  have "(\<lambda>tr. tr@[y]) ` set ([x] \<interleave> rev ys) = (\<lambda>tr. tr@[y]) ` rev ` set ([x] \<interleave> ys)"
    by (simp add: \<open>rev ` set ([x] \<interleave> ys) = set ([x] \<interleave> rev ys)\<close>)

  then show "{rev tr |tr. tr \<in> set ([x] \<interleave> (y # ys))} = set ([x] \<interleave> rev (y # ys))"
    using \<open>rev ` set ([x] \<interleave> (y # ys)) = {rev ys @ [x, y]} \<union> {rev ys @ [y, x]} \<union> (\<lambda>tr. tr @ [y]) ` rev ` set ([x] \<interleave> ys)\<close> \<open>set ([x] \<interleave> rev (y # ys)) = {rev ys @ [x, y]} \<union> {rev ys @ [y, x]} \<union> (\<lambda>tr. tr @ [y]) ` set ([x] \<interleave> rev ys)\<close> \<open>{rev tr |tr. tr \<in> set ([x] \<interleave> (y # ys))} = rev ` set ([x] \<interleave> (y # ys))\<close> by argo
qed

lemma prop3_7: "rev ` set ([x] \<interleave> ys) = set ([x] \<interleave> rev ys)" using prop3_6[of x ys] by auto

lemma prop3_8: "(\<lambda>tr. tr @ [y]) ` set ([x] \<interleave> ys) \<subseteq> set ([x] \<interleave> (ys @ [y]))" apply (induction ys) by auto

lemma prop3_9: "tr \<in> set ([x] \<interleave> rev ys) \<Longrightarrow> tr @ [y] \<in> set ([x] \<interleave> (rev ys @ [y]))"
proof -
  assume "tr \<in> set ([x] \<interleave> rev ys)"
  have "(\<lambda>tr. tr @ [y]) ` set ([x] \<interleave> (rev ys)) \<subseteq> set ([x] \<interleave> (rev ys @ [y]))" using prop3_8[of y x "rev ys"] by auto
  show ?thesis
    using \<open>(\<lambda>tr. tr @ [y]) ` set ([x] \<interleave> rev ys) \<subseteq> set ([x] \<interleave> (rev ys @ [y]))\<close> \<open>tr \<in> set ([x] \<interleave> rev ys)\<close> by blast
qed

lemma prop3_10: "(map (\<lambda>zs. zs@[y]) (insert_all x ys)) @ [ys@[y,x]] = insert_all x (ys@[y])"
proof (induction ys)
  case Nil
  then show ?case by auto
next
  case (Cons a ys)
  have "insert_all x ((a # ys) @ [y]) = [x#a#ys@[y]] @ (map ((#) a) (insert_all x ((ys) @ [y])))" by auto
  have "insert_all x (a # ys) = [x#a#ys] @ (map ((#) a) (insert_all x ys))" by auto

  have "map (\<lambda>zs. zs @ [y]) ([x#a#ys] @ (map ((#) a) (insert_all x ys))) @ [(a # ys) @ [y, x]] =
        ([x#a#ys@[y]] @ map (\<lambda>zs. zs @ [y]) (map ((#) a) (insert_all x ys))) @ [(a # ys) @ [y, x]]"
    by auto

  have "(map (\<lambda>zs. zs @ [y]) (map ((#) a) (insert_all x ys))) @ [(a # ys) @ [y, x]] = 
        (map ((#) a) ((map (\<lambda>zs. zs@[y]) (insert_all x ys))) @ [a # ys@[y,x]])" by auto

  then have "(map (\<lambda>zs. zs @ [y]) (map ((#) a) (insert_all x ys))) @ [(a # ys) @ [y, x]] = 
        (map ((#) a) ((map (\<lambda>zs. zs@[y]) (insert_all x ys)) @ [ys@[y,x]]))"
    by auto

  have "(map (\<lambda>zs. zs @ [y]) (map ((#) a) (insert_all x ys))) @ [(a # ys) @ [y, x]] = 
        (map ((#) a) (insert_all x ((ys) @ [y])))"
    using \<open>map (\<lambda>zs. zs @ [y]) (map ((#) a) (insert_all x ys)) @ [(a # ys) @ [y, x]] = map ((#) a) (map (\<lambda>zs. zs @ [y]) (insert_all x ys) @ [ys @ [y, x]])\<close> local.Cons by auto
  then show "map (\<lambda>zs. zs @ [y]) (insert_all x (a # ys)) @ [(a # ys) @ [y, x]] = insert_all x ((a # ys) @ [y])"
    by simp
qed

lemma prop3_10_1: "map (\<lambda>tr. tr @ [y]) ([x] \<interleave> ys) @ [ys@[y,x]] = insert_all x (ys@[y])"
proof -
  have "[x] \<interleave> ys = insert_all x ys"
    by (simp add: prop3_1)
  have "map (\<lambda>tr. tr @ [y]) ([x] \<interleave> ys) @ [ys@[y,x]] = map (\<lambda>tr. tr @ [y]) (insert_all x ys) @ [ys@[y,x]]"
    by (simp add: \<open>[x] \<interleave> ys = insert_all x ys\<close>)
  have "... = insert_all x (ys@[y])"
    by (simp add: prop3_10)
  show ?thesis
    by (simp add: \<open>map (\<lambda>tr. tr @ [y]) ([x] \<interleave> ys) @ [ys @ [y, x]] = map (\<lambda>tr. tr @ [y]) (insert_all x ys) @ [ys @ [y, x]]\<close> \<open>map (\<lambda>tr. tr @ [y]) (insert_all x ys) @ [ys @ [y, x]] = insert_all x (ys @ [y])\<close>)
qed

lemma prop3_11: "xa \<in> set ([x] \<interleave> (rev ys @ [y])) \<Longrightarrow> xa \<notin> (\<lambda>tr. tr @ [y]) ` set ([x] \<interleave> rev ys) \<Longrightarrow> xa = rev ys @ [y, x]"
proof -
  assume "xa \<in> set ([x] \<interleave> (rev ys @ [y]))"
  assume "xa \<notin> (\<lambda>tr. tr @ [y]) ` set ([x] \<interleave> rev ys)"
  have "set ([x] \<interleave> (rev ys @ [y])) = set (insert_all x (rev ys @ [y]))"
    by (simp add: prop3_1)
  have "set ([x] \<interleave> rev ys) = set (insert_all x (rev ys))"
    by (simp add: prop3_1)

  have "map (\<lambda>tr. tr @ [y]) ([x] \<interleave> rev ys) @ [rev ys@[y,x]] = insert_all x (rev ys@[y])"
    by (simp add: prop3_1 prop3_10)
    
  have "(\<lambda>tr. tr @ [y]) ` set ([x] \<interleave> rev ys) = set (insert_all x (rev ys@[y])) - {rev ys@[y,x]}"
    by (smt (verit) Diff_insert_absorb \<open>map (\<lambda>tr. tr @ [y]) ([x] \<interleave> rev ys) @ [rev ys @ [y, x]] = insert_all x (rev ys @ [y])\<close> \<open>xa \<in> set ([x] \<interleave> (rev ys @ [y]))\<close> \<open>xa \<notin> (\<lambda>tr. tr @ [y]) ` set ([x] \<interleave> rev ys)\<close> append.right_neutral image_set insert_all_set_equality l13 l4 prop3_1)
  show "xa = rev ys @ [y, x]"
    using \<open>(\<lambda>tr. tr @ [y]) ` set ([x] \<interleave> rev ys) = set (insert_all x (rev ys @ [y])) - {rev ys @ [y, x]}\<close> \<open>set ([x] \<interleave> (rev ys @ [y])) = set (insert_all x (rev ys @ [y]))\<close> \<open>xa \<in> set ([x] \<interleave> (rev ys @ [y]))\<close> \<open>xa \<notin> (\<lambda>tr. tr @ [y]) ` set ([x] \<interleave> rev ys)\<close> by fastforce
qed

lemma prop3_12: "x\<noteq>y \<Longrightarrow> set (map ((#) y) ((x#xs) \<interleave> ys)) \<inter> set (map ((#) x) (xs \<interleave> (y#ys))) = {}" by (auto)

lemma prop3_13: "x\<noteq>y \<Longrightarrow> set (map ((#) x) (xs \<interleave> (y#ys))) = set ((x#xs) \<interleave> (y#ys)) - set (map ((#) y) ((x#xs) \<interleave> ys))" by auto

lemma prop3_14: "(x#xs) \<interleave> (x#ys) = map ((#) x) ((xs \<interleave> (x#ys)) @ ((x#xs) \<interleave> ys))" by auto


lemma prop3_15: "set [(xs @ [x, y])] \<union> (\<lambda>tr. tr @ [x]) ` set ((xs \<interleave> [y])) = set (((xs @ [x]) \<interleave> [y]))"
  proof (induction "xs" arbitrary: x y)
    case Nil
    then show ?case by auto
  next
    case (Cons a xs)
    have "set ((a # xs) \<interleave> [y]) = set (map ((#) a) ((xs) \<interleave> (y#[])) @  map ((#) y) ((a#(xs)) \<interleave> []))" by auto
    have "... = insert (y # a # xs) ((#) a ` set (xs \<interleave> [y])) " by simp

    have "set ((a # xs @ [x]) \<interleave> [y]) = set (map ((#) a) ((xs @ [x]) \<interleave> (y#[]))) \<union> set (map ((#) y) ((a#(xs @ [x])) \<interleave> []))" by auto
    have "... = insert (y # a # xs @ [x]) ((#) a ` set ((xs @ [x]) \<interleave> [y]))" by auto

    have "(((\<lambda>tr. tr @ [x]) ` ((#) a ` set (xs \<interleave> [y])))) = 
          (((#) a ` (\<lambda>tr. tr @ [x]) ` set (xs \<interleave> [y])))" by auto

    have "set [a # xs @ [x, y]] \<union>  (insert (y # a # xs @ [x]) ((\<lambda>tr. tr @ [x]) ` ((#) a ` set (xs \<interleave> [y])))) = 
          insert (y # a # xs @ [x]) ((set [a#xs @ [x, y]] \<union> (#) a ` (\<lambda>tr. tr @ [x]) ` set (xs \<interleave> [y])))"
      by (simp add: \<open>(\<lambda>tr. tr @ [x]) ` (#) a ` set (xs \<interleave> [y]) = (#) a ` (\<lambda>tr. tr @ [x]) ` set (xs \<interleave> [y])\<close>)

    then have "set [a # xs @ [x, y]] \<union> (\<lambda>tr. tr @ [x]) ` (insert (y # a # xs) ((#) a ` set (xs \<interleave> [y]))) = 
          insert (y # a # xs @ [x]) ((#) a ` set ((xs @ [x]) \<interleave> [y]))" using Cons[of x y]
      by (smt (verit) Cons_eq_appendI empty_set image_insert insert_is_Un list.simps(15))
    then show ?case
      by force
  qed

lemma prop3_16: "set (map (\<lambda>tr. tr@[y]) (rev (x#xs) \<interleave> rev ys)) \<union> set (map (\<lambda>tr. tr@[x]) (rev xs \<interleave> rev (y#ys))) = set (rev (x # xs) \<interleave> rev (y # ys))"
proof (induction xs arbitrary: ys rule: rev_induct)
  case Nil
  have "set (map (\<lambda>tr. tr @ [y]) (rev [x] \<interleave> rev ys)) = set (map (\<lambda>tr. tr @ [y]) ([x] \<interleave> rev ys))" by auto
  have "set (map (\<lambda>tr. tr @ [x]) (rev [] \<interleave> rev (y # ys))) = set (map (\<lambda>tr. tr @ [x]) ([rev (y # ys)]))" by auto
  have "set (rev [x] \<interleave> rev (y # ys)) = set ([x] \<interleave> rev (y # ys))" by auto
  have "set (map (\<lambda>tr. tr @ [y]) ([x] \<interleave> rev ys)) \<union> set (map (\<lambda>tr. tr @ [x]) ([rev (y # ys)])) = set ([x] \<interleave> rev (y # ys))" apply auto
    apply (metis Cons_eq_appendI append.right_neutral append_assoc insert_4 prop3_1 rev.simps(1) rev.simps(2) rev_singleton_conv)
    apply (meson prop3_9) using prop3_11[of ]
    by metis
  then show "set (map (\<lambda>tr. tr @ [y]) (rev [x] \<interleave> rev ys)) \<union> set (map (\<lambda>tr. tr @ [x]) (rev [] \<interleave> rev (y # ys))) = set (rev [x] \<interleave> rev (y # ys))"
    by simp
next
  case (snoc x' xs)
  then show ?case
proof (induction ys rule: rev_induct)
  case Nil
  have "set (rev (x # xs @ [x']) \<interleave> rev [y]) = set ((x' # rev xs @ [x]) \<interleave> [y])"
    by auto
  have "... = set (map ((#) x') ((rev xs @ [x]) \<interleave> [y]) @ map ((#) y) [x' # rev xs @ [x]])" by auto
  have "... = set (map ((#) x') ((rev xs @ [x]) \<interleave> [y])) \<union> set (map ((#) y) [x' # rev xs @ [x]])" by auto
  have "set (map (\<lambda>tr. tr @ [y]) (rev (x # xs @ [x']) \<interleave> rev [])) = set (map (\<lambda>tr. tr @ [y]) ([(x' # rev xs @ [x])]))" by auto
  have "set (map (\<lambda>tr. tr @ [x]) (rev (xs @ [x']) \<interleave> rev [y])) = set (map (\<lambda>tr. tr @ [x]) ((x' # rev xs ) \<interleave> [y]))" by auto

  have "set (map (\<lambda>tr. tr @ [x]) ((x' # rev xs ) \<interleave> [y])) = set (map (\<lambda>tr. tr @ [x]) (map ((#) x') ((rev xs) \<interleave> (y#[])) @  map ((#) y) ((x'#(rev xs)) \<interleave> [])))" by auto
  have "... = (\<lambda>tr. tr @ [x]) ` set (map ((#) x') (rev xs \<interleave> [y])) \<union> (\<lambda>tr. tr @ [x]) ` set (map ((#) y) [x' # rev xs])" by auto

  have "set (map (\<lambda>tr. tr @ [y]) ([(x' # rev xs @ [x])])) = set [(x' # rev xs @ [x, y])]" by auto

  have "set (map ((#) y) [x' # rev xs @ [x]]) = set ([y # x' # rev xs @ [x]])" by auto

  have "set (map ((#) y) [x' # rev xs]) = set ([y # x' # rev xs])" by auto
  have "(\<lambda>tr. tr @ [x]) ` set ([y # x' # rev xs]) = set ([y # x' # rev xs @ [x]])" by auto

  have "set [(rev xs @ [x, y])] \<union> (\<lambda>tr. tr @ [x]) ` set ((rev xs \<interleave> [y])) = 
        set (((rev xs @ [x]) \<interleave> [y]))" using prop3_15[of "rev xs" x y] by auto

  then have "set [(x' # rev xs @ [x, y])] \<union> (\<lambda>tr. tr @ [x]) ` set (map ((#) x') (rev xs \<interleave> [y])) = 
        set (map ((#) x') ((rev xs @ [x]) \<interleave> [y]))" apply auto by blast

  then have "set [(x' # rev xs @ [x, y])] \<union> (\<lambda>tr. tr @ [x]) ` set (map ((#) x') (rev xs \<interleave> [y])) \<union> set ([y # x' # rev xs @ [x]]) = 
        set (map ((#) x') ((rev xs @ [x]) \<interleave> [y])) \<union> set ([y # x' # rev xs @ [x]])"
    by blast
  have "set (map (\<lambda>tr. tr @ [y]) (rev (x # xs @ [x']) \<interleave> rev [])) \<union> set (map (\<lambda>tr. tr @ [x]) (rev (xs @ [x']) \<interleave> rev [y])) = set (rev (x # xs @ [x']) \<interleave> rev [y])"
    using \<open>set (map (\<lambda>tr. tr @ [x]) (map ((#) x') (rev xs \<interleave> [y]) @ map ((#) y) ((x' # rev xs) \<interleave> []))) = (\<lambda>tr. tr @ [x]) ` set (map ((#) x') (rev xs \<interleave> [y])) \<union> (\<lambda>tr. tr @ [x]) ` set (map ((#) y) [x' # rev xs])\<close> \<open>set [x' # rev xs @ [x, y]] \<union> (\<lambda>tr. tr @ [x]) ` set (map ((#) x') (rev xs \<interleave> [y])) = set (map ((#) x') ((rev xs @ [x]) \<interleave> [y]))\<close> by auto
    
  then show ?case by simp
next
  case (snoc y' ys)
  have "set (map (\<lambda>tr. tr @ [y]) (rev (x # xs) \<interleave> rev ys)) \<union> set (map (\<lambda>tr. tr @ [x]) (rev xs \<interleave> rev (y # ys))) = set (rev (x # xs) \<interleave> rev (y # ys))"
    using snoc.prems by auto
  have "set (map (\<lambda>tr. tr @ [y]) (rev (x # xs @ [x']) \<interleave> rev (ys @ [y']))) = (\<lambda>tr. tr @ [y]) ` set (((x' # rev xs @ [x]) \<interleave> (y' # rev ys)))"
    using snoc.prems by auto
  have "set (map (\<lambda>tr. tr @ [x]) (rev (xs @ [x']) \<interleave> rev (y # ys @ [y']))) = (\<lambda>tr. tr @ [x]) ` set (((x'#rev xs) \<interleave> (y' # rev ys @ [y])))"
    using list.set_map rev_eq_Cons_iff rev_rev_ident by force
  
  have "set (rev (x # xs @ [x']) \<interleave> rev (y # ys @ [y'])) = set ((x' # rev xs @ [x]) \<interleave> (y' # rev ys @ [y]))" by auto
  have "... = set (map ((#) x') ((rev xs @ [x]) \<interleave> (y'#(rev ys @ [y])))) \<union> set (map ((#) y') ((x'#(rev xs @ [x])) \<interleave> (rev ys @ [y])))" by auto
  have "... = (#) x' ` set ( ((rev xs @ [x]) \<interleave> (y'#(rev ys @ [y])))) \<union> (#) y' ` set (((x'#(rev xs @ [x])) \<interleave> (rev ys @ [y])))" by auto

  have "set ((x' # rev xs @ [x]) \<interleave> (y' # rev ys @ [y])) = set (map ((#) x') ((rev xs @ [x]) \<interleave> (y' # rev ys @ [y]))) \<union> set (map ((#) y') ((x' # rev xs @ [x]) \<interleave> (rev ys @ [y])))"
    by auto


    have "set ((rev xs @ [x]) \<interleave> (y' # rev ys @ [y])) = (\<lambda>tr. tr@[y]) ` set ((rev xs @ [x]) \<interleave> (y' # rev ys)) \<union> (\<lambda>tr. tr@[x]) ` set ((rev xs) \<interleave> (y' # rev ys @ [y]))"
      by (metis Cons_eq_appendI list.set_map rev.simps(2) rev_swap snoc.prems)
    have "set ((x' # rev xs @ [x]) \<interleave> (rev ys @ [y])) = (\<lambda>tr. tr@[y]) ` set ((x' # rev xs @ [x]) \<interleave> (rev ys)) \<union> (\<lambda>tr. tr@[x]) ` set ((x' # rev xs) \<interleave> (rev ys @ [y]))"
      using snoc.IH snoc.prems by auto

    have "set (rev (x # xs @ [x']) \<interleave> rev (ys @ [y'])) = set ((x' # (rev xs) @ [x]) \<interleave> (y'# rev ys))" by auto
    have "... = set (map ((#) x') ((rev xs @ [x]) \<interleave> (y' # rev ys))) \<union> set (map ((#) y') ((x' # rev xs @ [x]) \<interleave> rev ys))" by auto
    have " ... = (#) x' ` (set ((rev xs @ [x]) \<interleave> (y' # rev ys))) \<union> (#) y' ` set ((x' # rev xs @ [x]) \<interleave> (rev ys))" by auto

    have "set (rev (xs @ [x']) \<interleave> rev (y # ys @ [y'])) = set ((x' # (rev xs)) \<interleave> (y'# rev ys @ [y]))" by auto
    have "... = set (map ((#) x') ((rev xs) \<interleave> (y' # rev ys @ [y]))) \<union> set (map ((#) y') ((x' # rev xs) \<interleave> (rev ys @ [y])))" by auto
    have " ... = (#) x' ` (set ((rev xs) \<interleave> (y' # rev ys @ [y]))) \<union> (#) y' ` set ((x' # rev xs) \<interleave> (rev ys @ [y]))" by auto

    have "set (map (\<lambda>tr. tr @ [y]) (rev (x # xs @ [x']) \<interleave> rev (ys @ [y']))) \<union> 
          set (map (\<lambda>tr. tr @ [x]) (rev (xs @ [x']) \<interleave> rev (y # ys @ [y']))) =
          (\<lambda>tr. tr @ [x]) ` (#) x' ` (set ((rev xs) \<interleave> (y' # rev ys @ [y]))) \<union> 
          (\<lambda>tr. tr @ [x]) ` (#) y' ` set ((x' # rev xs) \<interleave> (rev ys @ [y])) \<union>
          (\<lambda>tr. tr @ [y]) ` (#) x' ` (set ((rev xs @ [x]) \<interleave> (y' # rev ys))) \<union> 
          (\<lambda>tr. tr @ [y]) ` (#) y' ` set ((x' # rev xs @ [x]) \<interleave> (rev ys))"
      by (smt (verit, best) \<open>set ((x' # rev xs @ [x]) \<interleave> (y' # rev ys)) = set (map ((#) x') ((rev xs @ [x]) \<interleave> (y' # rev ys))) \<union> set (map ((#) y') ((x' # rev xs @ [x]) \<interleave> rev ys))\<close> \<open>set ((x' # rev xs) \<interleave> (y' # rev ys @ [y])) = set (map ((#) x') (rev xs \<interleave> (y' # rev ys @ [y]))) \<union> set (map ((#) y') ((x' # rev xs) \<interleave> (rev ys @ [y])))\<close> \<open>set (map (\<lambda>tr. tr @ [x]) (rev (xs @ [x']) \<interleave> rev (y # ys @ [y']))) = (\<lambda>tr. tr @ [x]) ` set ((x' # rev xs) \<interleave> (y' # rev ys @ [y]))\<close> \<open>set (map (\<lambda>tr. tr @ [y]) (rev (x # xs @ [x']) \<interleave> rev (ys @ [y']))) = (\<lambda>tr. tr @ [y]) ` set ((x' # rev xs @ [x]) \<interleave> (y' # rev ys))\<close> image_Un inf_sup_aci(5) inf_sup_aci(6) list.set_map)

    have "... = (#) x' ` ((\<lambda>tr. tr @ [x]) ` (set ((rev xs) \<interleave> (y' # rev ys @ [y]))) \<union> (\<lambda>tr. tr @ [y]) ` (set ((rev xs @ [x]) \<interleave> (y' # rev ys)))) \<union> 
          (#) y' ` ((\<lambda>tr. tr @ [x]) ` set ((x' # rev xs) \<interleave> (rev ys @ [y])) \<union> (\<lambda>tr. tr @ [y]) ` set ((x' # rev xs @ [x]) \<interleave> (rev ys)))" by auto

    have "(\<lambda>tr. tr@[y]) ` set ((rev xs @ [x]) \<interleave> (y' # rev ys)) \<union> (\<lambda>tr. tr@[y]) ` set ((x' # rev xs @ [x]) \<interleave> (rev ys)) = 
          (\<lambda>tr. tr@[y]) ` (set ((rev xs @ [x]) \<interleave> (y' # rev ys)) \<union> set ((x' # rev xs @ [x]) \<interleave> (rev ys)))" by auto

    then show ?case
      by (metis Un_commute \<open>(\<lambda>tr. tr @ [x]) ` (#) x' ` set (rev xs \<interleave> (y' # rev ys @ [y])) \<union> (\<lambda>tr. tr @ [x]) ` (#) y' ` set ((x' # rev xs) \<interleave> (rev ys @ [y])) \<union> (\<lambda>tr. tr @ [y]) ` (#) x' ` set ((rev xs @ [x]) \<interleave> (y' # rev ys)) \<union> (\<lambda>tr. tr @ [y]) ` (#) y' ` set ((x' # rev xs @ [x]) \<interleave> rev ys) = (#) x' ` ((\<lambda>tr. tr @ [x]) ` set (rev xs \<interleave> (y' # rev ys @ [y])) \<union> (\<lambda>tr. tr @ [y]) ` set ((rev xs @ [x]) \<interleave> (y' # rev ys))) \<union> (#) y' ` ((\<lambda>tr. tr @ [x]) ` set ((x' # rev xs) \<interleave> (rev ys @ [y])) \<union> (\<lambda>tr. tr @ [y]) ` set ((x' # rev xs @ [x]) \<interleave> rev ys))\<close> \<open>set ((rev xs @ [x]) \<interleave> (y' # rev ys @ [y])) = (\<lambda>tr. tr @ [y]) ` set ((rev xs @ [x]) \<interleave> (y' # rev ys)) \<union> (\<lambda>tr. tr @ [x]) ` set (rev xs \<interleave> (y' # rev ys @ [y]))\<close> \<open>set ((x' # rev xs @ [x]) \<interleave> (rev ys @ [y])) = (\<lambda>tr. tr @ [y]) ` set ((x' # rev xs @ [x]) \<interleave> rev ys) \<union> (\<lambda>tr. tr @ [x]) ` set ((x' # rev xs) \<interleave> (rev ys @ [y]))\<close> \<open>set ((x' # rev xs @ [x]) \<interleave> (y' # rev ys @ [y])) = set (map ((#) x') ((rev xs @ [x]) \<interleave> (y' # rev ys @ [y]))) \<union> set (map ((#) y') ((x' # rev xs @ [x]) \<interleave> (rev ys @ [y])))\<close> \<open>set (map ((#) x') ((rev xs @ [x]) \<interleave> (y' # rev ys @ [y]))) \<union> set (map ((#) y') ((x' # rev xs @ [x]) \<interleave> (rev ys @ [y]))) = (#) x' ` set ((rev xs @ [x]) \<interleave> (y' # rev ys @ [y])) \<union> (#) y' ` set ((x' # rev xs @ [x]) \<interleave> (rev ys @ [y]))\<close> \<open>set (map (\<lambda>tr. tr @ [y]) (rev (x # xs @ [x']) \<interleave> rev (ys @ [y']))) \<union> set (map (\<lambda>tr. tr @ [x]) (rev (xs @ [x']) \<interleave> rev (y # ys @ [y']))) = (\<lambda>tr. tr @ [x]) ` (#) x' ` set (rev xs \<interleave> (y' # rev ys @ [y])) \<union> (\<lambda>tr. tr @ [x]) ` (#) y' ` set ((x' # rev xs) \<interleave> (rev ys @ [y])) \<union> (\<lambda>tr. tr @ [y]) ` (#) x' ` set ((rev xs @ [x]) \<interleave> (y' # rev ys)) \<union> (\<lambda>tr. tr @ [y]) ` (#) y' ` set ((x' # rev xs @ [x]) \<interleave> rev ys)\<close> \<open>set (rev (x # xs @ [x']) \<interleave> rev (y # ys @ [y'])) = set ((x' # rev xs @ [x]) \<interleave> (y' # rev ys @ [y]))\<close>)

  qed
qed

theorem prop3: "set (map rev (xs \<interleave> ys)) = set (rev xs \<interleave> rev ys)"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by auto
next
  case Cons1: (Cons x xs)
  then show ?case
  proof (induction ys)
    case Nil
    then show ?case by auto
  next
    case (Cons y ys)
    have "rev ` set ([x] \<interleave> ys) = set ([x] \<interleave> rev ys)"
      by (simp add: prop3_7)
    then show "set (map rev ((x # xs) \<interleave> (y # ys))) = set (rev (x # xs) \<interleave> rev (y # ys))"
    proof (cases "xs=[]")
      case True
      from Cons True show ?thesis
        by (metis list.set_map prop3_7 singleton_rev_conv)
    next
      case False
      have "set (map rev (xs \<interleave> ys)) = set (rev xs \<interleave> rev ys)" using Cons(2)
        by meson
      then have l1: "set (map rev ((x # xs) \<interleave> ys)) = set (rev (x # xs) \<interleave> rev ys)" using Cons(1)
        using Cons1 by blast

      have "set (map rev ((x # xs) \<interleave> (y # ys))) = rev ` set (map ((#) x) (xs \<interleave> (y#ys))) \<union> rev ` set (map ((#) y) ((x#xs) \<interleave> ys))"
        by (metis image_Un interleave.simps(3) list.set_map set_append)
      have "rev ` set (map ((#) x) (xs \<interleave> (y#ys))) = set (map (\<lambda>tr. tr@[x]) (rev xs \<interleave> rev (y#ys)))" apply auto
        apply (metis (no_types, lifting) Cons1 image_eqI list.set_map rev.simps(2))
        using Cons.prems apply auto  apply (induction ys) apply auto
        using image_iff apply fastforce
        using image_iff by fastforce

      have "rev ` set (map ((#) y) ((x # xs) \<interleave> ys)) = rev ` ((#) y) ` set ((x # xs) \<interleave> ys)" by simp
      have "... =(\<lambda>tr. tr@[y]) ` rev ` set ((x # xs) \<interleave> ys)" apply auto
        by (simp add: image_iff)
      have "rev ` set (map ((#) y) ((x # xs) \<interleave> ys)) = set (map (\<lambda>tr. tr@[y]) (rev (x#xs) \<interleave> rev ys))"
        using Cons.IH Cons1 \<open>rev ` (#) y ` set ((x # xs) \<interleave> ys) = (\<lambda>tr. tr @ [y]) ` rev ` set ((x # xs) \<interleave> ys)\<close> by force
      
      have "set (map (\<lambda>tr. tr@[y]) (rev (x#xs) \<interleave> rev ys)) \<union> set (map (\<lambda>tr. tr@[x]) (rev xs \<interleave> rev (y#ys))) = set (rev (x # xs) \<interleave> rev (y # ys))"
        by (metis prop3_16)

      then show "set (map rev ((x # xs) \<interleave> (y # ys))) = set (rev (x # xs) \<interleave> rev (y # ys))"
        using \<open>rev ` set (map ((#) x) (xs \<interleave> (y # ys))) = set (map (\<lambda>tr. tr @ [x]) (rev xs \<interleave> rev (y # ys)))\<close> \<open>rev ` set (map ((#) y) ((x # xs) \<interleave> ys)) = set (map (\<lambda>tr. tr @ [y]) (rev (x # xs) \<interleave> rev ys))\<close> \<open>set (map rev ((x # xs) \<interleave> (y # ys))) = rev ` set (map ((#) x) (xs \<interleave> (y # ys))) \<union> rev ` set (map ((#) y) ((x # xs) \<interleave> ys))\<close> by auto
    qed
  qed
qed


lemma prop4: "set ((ps @ [p]) \<interleave> (qs @ [q])) = {tr @ [p] |tr. tr \<in> set (ps \<interleave> (qs @ [q]))} \<union> {tr @ [q] |tr. tr \<in> set ((ps @ [p]) \<interleave> qs)}"
proof -
  have "(p # rev ps) \<interleave> (q # rev qs) = map ((#) p) (rev ps \<interleave> (q # rev qs)) @ map ((#) q) ((p # rev ps) \<interleave> rev qs)" by auto

  have "set ((ps @ [p]) \<interleave> (qs @ [q])) = set (map rev ((p#(rev ps)) \<interleave> (q#(rev qs))))"
    by (metis prop3 rev.simps(2) rev_rev_ident)
  have "... = rev ` set ((p # rev ps) \<interleave> (q # rev qs))"
    by (meson list.set_map) 
  have "rev ` set ((p # rev ps) \<interleave> (q # rev qs)) = rev ` set (map ((#) p) (rev ps \<interleave> (q # rev qs))) \<union> rev ` set (map ((#) q) ((p # rev ps) \<interleave> rev qs))"
    by (simp add: image_Un)

  have "rev ` (#) p ` set (rev ps \<interleave> (q # rev qs)) = (\<lambda>tr. tr@[p]) ` rev `  set (rev ps \<interleave> (q # rev qs))" apply auto
    by (simp add: image_iff)
  have "rev ` set (map ((#) p) (rev ps \<interleave> (q # rev qs))) = {tr @ [p] |tr. tr \<in> set (ps \<interleave> (qs @ [q]))}" apply auto
    using prop3 apply fastforce
    by (metis (no_types, lifting) image_eqI list.set_map prop3 rev.simps(2) rev_rev_ident)

  have "rev ` set (map ((#) q) ((p # rev ps) \<interleave> rev qs)) = {tr @ [q] |tr. tr \<in> set ((ps @ [p]) \<interleave> qs)}"  apply auto
    using prop3 apply fastforce
    by (metis (no_types, lifting) image_eqI list.set_map prop3 rev.simps(2) rev_rev_ident)

  show ?thesis
    using \<open>rev ` set ((p # rev ps) \<interleave> (q # rev qs)) = rev ` set (map ((#) p) (rev ps \<interleave> (q # rev qs))) \<union> rev ` set (map ((#) q) ((p # rev ps) \<interleave> rev qs))\<close> \<open>rev ` set (map ((#) p) (rev ps \<interleave> (q # rev qs))) = {tr @ [p] |tr. tr \<in> set (ps \<interleave> (qs @ [q]))}\<close> \<open>rev ` set (map ((#) q) ((p # rev ps) \<interleave> rev qs)) = {tr @ [q] |tr. tr \<in> set ((ps @ [p]) \<interleave> qs)}\<close> \<open>set ((ps @ [p]) \<interleave> (qs @ [q])) = set (map rev ((p # rev ps) \<interleave> (q # rev qs)))\<close> \<open>set (map rev ((p # rev ps) \<interleave> (q # rev qs))) = rev ` set ((p # rev ps) \<interleave> (q # rev qs))\<close> by argo
qed

lemma prop7: "set ((ps@[p]) \<interleave> (qs@[q])) = set (map (\<lambda>xs. xs@[p]) (ps \<interleave> (qs@[q])) @ map (\<lambda>xs. xs@[q]) ((ps@[p]) \<interleave> qs))"
proof -
  have "{tr @ [p] |tr. tr \<in> set (ps \<interleave> (qs @ [q]))} = set (map (\<lambda>xs. xs @ [p]) (ps \<interleave> (qs @ [q])))" using prop5[of p ps qs q] by auto
  have "{tr @ [q] |tr. tr \<in> set ((ps @ [p]) \<interleave> qs)} = set (map (\<lambda>xs. xs @ [q]) ((ps @ [p]) \<interleave> qs))" using prop6[of q ps p qs] by auto

  have "set ((ps@[p]) \<interleave> (qs@[q])) = {tr @ [p] |tr. tr \<in> set (ps \<interleave> (qs @ [q]))} \<union> {tr @ [q] |tr. tr \<in> set ((ps @ [p]) \<interleave> qs)}"
    by (metis prop4)
  have "... = set (map (\<lambda>xs. xs@[p]) (ps \<interleave> (qs@[q]))) \<union> set (map (\<lambda>xs. xs@[q]) ((ps@[p]) \<interleave> qs))"
    by auto
  show ?thesis
    by (simp add: \<open>set ((ps @ [p]) \<interleave> (qs @ [q])) = {tr @ [p] |tr. tr \<in> set (ps \<interleave> (qs @ [q]))} \<union> {tr @ [q] |tr. tr \<in> set ((ps @ [p]) \<interleave> qs)}\<close> \<open>{tr @ [p] |tr. tr \<in> set (ps \<interleave> (qs @ [q]))} \<union> {tr @ [q] |tr. tr \<in> set ((ps @ [p]) \<interleave> qs)} = set (map (\<lambda>xs. xs @ [p]) (ps \<interleave> (qs @ [q]))) \<union> set (map (\<lambda>xs. xs @ [q]) ((ps @ [p]) \<interleave> qs))\<close>)
qed

lemma prop8: "xs \<in> set ys \<Longrightarrow> xs@[x] \<in> set (map (\<lambda>t. t@[x]) ys)"
  apply (induction xs) by auto

lemma prop9: "xs \<in> set (p \<interleave> q) \<Longrightarrow> xs @ r \<in> set (p \<interleave> (q @ r))"
proof -
  assume "xs \<in> set (p \<interleave> q)"
  then show "xs @ r \<in> set (p \<interleave> (q @ r))"
  proof (induction r rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc rr r)
    then have "xs @ r \<in> set (p \<interleave> (q @ r))" by simp
    then show "xs @ r @ [rr] \<in> set (p \<interleave> (q @ r @ [rr]))"
    proof (induction p rule: rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc pp p)
      have "set ((p @ [pp]) \<interleave> (q @ r @ [rr])) = set (map (\<lambda>xs. xs@[pp]) (p \<interleave> (q @ r @[rr])) @ map (\<lambda>xs. xs@[rr]) ((p@[pp]) \<interleave> (q @ r)))"
        by (metis (no_types, lifting) append_assoc map_eq_conv prop7)
      have "set ((p @ [pp]) \<interleave> (q @ r @ [rr])) = set (map (\<lambda>xs. xs@[pp]) (p \<interleave> (q @ r @[rr]))) \<union> set (map (\<lambda>xs. xs@[rr]) ((p@[pp]) \<interleave> (q @ r)))"
        by (simp add: \<open>set ((p @ [pp]) \<interleave> (q @ r @ [rr])) = set (map (\<lambda>xs. xs @ [pp]) (p \<interleave> (q @ r @ [rr])) @ map (\<lambda>xs. xs @ [rr]) ((p @ [pp]) \<interleave> (q @ r)))\<close>)
      have "xs @ r @ [rr] \<in> set (map (\<lambda>xs. xs@[rr]) ((p@[pp]) \<interleave> (q @ r)))"
      proof -
        have "xs @ r \<in> set (((p@[pp]) \<interleave> (q @ r)))"
          by (simp add: snoc.prems)
        show "xs @ r @ [rr] \<in> set (map (\<lambda>xs. xs@[rr]) ((p@[pp]) \<interleave> (q @ r)))"
          using prop5[of "xs @ r" "((p@[pp]) \<interleave> (q @ r))"]
          by (simp add: snoc.prems)
      qed
      then show ?case
        by (simp add: \<open>set ((p @ [pp]) \<interleave> (q @ r @ [rr])) = set (map (\<lambda>xs. xs @ [pp]) (p \<interleave> (q @ r @ [rr]))) \<union> set (map (\<lambda>xs. xs @ [rr]) ((p @ [pp]) \<interleave> (q @ r)))\<close>)
    qed
  qed
qed

lemma prop9_1: "xs \<in> set ((p \<interleave> r)) \<Longrightarrow> q @ xs \<in>  set (p \<interleave> (q @ r))"
proof -
  assume "xs \<in> set ((p \<interleave> r))"
  then show "q @ xs \<in>  set (p \<interleave> (q @ r))"
  proof (induction q)
    case Nil
    then show ?case by auto
  next
    case (Cons qq q)
    then show "(qq # q) @ xs \<in> set (p \<interleave> ((qq # q) @ r))"
      apply (induction p) by auto
  qed
qed

lemma prop10: "set ([p] \<parallel> [q] ;\<^sub>c [r]) \<subseteq> set ([p] \<parallel> ([q] ;\<^sub>c [r]))"
proof -
  have "([p] \<parallel> [q]) ;\<^sub>c [r] = (p \<interleave> q) ;\<^sub>c [r]" by (auto simp: cnf_concurrency_def composition_cnf_def)
  have "[p] \<parallel> ([q] ;\<^sub>c [r]) = [p] \<parallel> ([q @ r])" by (auto simp: cnf_concurrency_def composition_cnf_def)
  have "... = p \<interleave> (q @ r)" by (auto simp: cnf_concurrency_def composition_cnf_def)
  have "set ((p \<interleave> q) ;\<^sub>c [r]) \<subseteq> set (p \<interleave> (q @ r))"
    using prop9 by (auto simp: composition_cnf_def)
  show ?thesis
    by (simp add: \<open>[p] \<parallel> ([q] ;\<^sub>c [r]) = [p] \<parallel> [q @ r]\<close> \<open>[p] \<parallel> [q @ r] = p \<interleave> (q @ r)\<close> \<open>[p] \<parallel> [q] ;\<^sub>c [r] = (p \<interleave> q) ;\<^sub>c [r]\<close> \<open>set ((p \<interleave> q) ;\<^sub>c [r]) \<subseteq> set (p \<interleave> (q @ r))\<close>)
qed

lemma prop10_1: "set ([p] \<parallel> [r] ;\<^sub>c [q]) \<subseteq> set (([p] ;\<^sub>c [q]) \<parallel> [r])"
proof -
  have "[p] \<parallel> [r] ;\<^sub>c [q] = (p \<interleave> r) ;\<^sub>c [q]" by (auto simp: cnf_concurrency_def composition_cnf_def)
  have "([p] ;\<^sub>c [q]) \<parallel> [r] = (p @ q) \<interleave> r" by (auto simp: cnf_concurrency_def composition_cnf_def)
  have "set ((p \<interleave> r) ;\<^sub>c [q]) \<subseteq> set ((p @ q) \<interleave> r)"
    apply (auto simp: composition_cnf_def)
    by (metis inter_perm permutation_set_equality prop9)
  show ?thesis
    by (simp add: \<open>([p] ;\<^sub>c [q]) \<parallel> [r] = (p @ q) \<interleave> r\<close> \<open>[p] \<parallel> [r] ;\<^sub>c [q] = (p \<interleave> r) ;\<^sub>c [q]\<close> \<open>set ((p \<interleave> r) ;\<^sub>c [q]) \<subseteq> set ((p @ q) \<interleave> r)\<close>)
qed

lemma prop10_2: "set ([q] ;\<^sub>c [p] \<parallel> [r]) \<subseteq> set ([p] \<parallel> ([q] ;\<^sub>c [r]))"
proof -
  have "[q] ;\<^sub>c [p] \<parallel> [r] = [q] ;\<^sub>c (p \<interleave> r)" by (auto simp: cnf_concurrency_def composition_cnf_def)
  have "[p] \<parallel> ([q] ;\<^sub>c [r]) = p \<interleave> (q @ r)" by (auto simp: cnf_concurrency_def composition_cnf_def)
  have "set ([q] ;\<^sub>c (p \<interleave> r)) \<subseteq> set (p \<interleave> (q @ r))"
    using prop9_1 by (auto simp: composition_cnf_def)
  show ?thesis
    by (simp add: \<open>[p] \<parallel> ([q] ;\<^sub>c [r]) = p \<interleave> (q @ r)\<close> \<open>[q] ;\<^sub>c [p] \<parallel> [r] = [q] ;\<^sub>c (p \<interleave> r)\<close> \<open>set ([q] ;\<^sub>c (p \<interleave> r)) \<subseteq> set (p \<interleave> (q @ r))\<close>)
qed

lemma prop10_3: "set ([p] ;\<^sub>c [q] \<parallel> [r]) \<subseteq> set (([p] ;\<^sub>c [q]) \<parallel> [r])"
proof -
  have "[p] ;\<^sub>c [q] \<parallel> [r] = [p] ;\<^sub>c (q \<interleave> r)" by (auto simp: cnf_concurrency_def composition_cnf_def)
  have "([p] ;\<^sub>c [q]) \<parallel> [r] = (p @ q) \<interleave> r" by (auto simp: cnf_concurrency_def composition_cnf_def)
  have "set ([p] ;\<^sub>c (q \<interleave> r)) \<subseteq> set ((p @ q) \<interleave> r)"
    apply (auto simp: composition_cnf_def)
    by (metis inter_perm permutation_set_equality prop9_1)
  show ?thesis
    using \<open>([p] ;\<^sub>c [q]) \<parallel> [r] = (p @ q) \<interleave> r\<close> \<open>[p] ;\<^sub>c [q] \<parallel> [r] = [p] ;\<^sub>c (q \<interleave> r)\<close> \<open>set ([p] ;\<^sub>c (q \<interleave> r)) \<subseteq> set ((p @ q) \<interleave> r)\<close> by auto
qed

lemma prop11: "set ([p] \<parallel> qs ;\<^sub>c [r]) \<subseteq> set ([p] \<parallel> (qs ;\<^sub>c [r]))"
proof (induction qs)
  case Nil
  then show ?case by (auto simp: composition_cnf_def cnf_concurrency_def)
next
  case (Cons q qs)
  have "set ([p] \<parallel> (q # qs) ;\<^sub>c [r]) = set ([p] \<parallel> [q] ;\<^sub>c [r]) \<union> set ([p] \<parallel> qs ;\<^sub>c [r])"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set ([p] \<parallel> ((q # qs) ;\<^sub>c [r])) = set ([p] \<parallel> ([q] ;\<^sub>c [r])) \<union> set ([p] \<parallel> (qs ;\<^sub>c [r]))"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set ([p] \<parallel> [q] ;\<^sub>c [r]) \<subseteq> set ([p] \<parallel> ([q] ;\<^sub>c [r]))"
    by (simp add: prop10)
  have "set ([p] \<parallel> qs ;\<^sub>c [r]) \<subseteq> set ([p] \<parallel> (qs ;\<^sub>c [r]))"
    by (simp add: local.Cons)
  then show "set ([p] \<parallel> (q # qs) ;\<^sub>c [r]) \<subseteq> set ([p] \<parallel> ((q # qs) ;\<^sub>c [r]))"
    using \<open>set ([p] \<parallel> ((q # qs) ;\<^sub>c [r])) = set ([p] \<parallel> ([q] ;\<^sub>c [r])) \<union> set ([p] \<parallel> (qs ;\<^sub>c [r]))\<close> \<open>set ([p] \<parallel> (q # qs) ;\<^sub>c [r]) = set ([p] \<parallel> [q] ;\<^sub>c [r]) \<union> set ([p] \<parallel> qs ;\<^sub>c [r])\<close> \<open>set ([p] \<parallel> [q] ;\<^sub>c [r]) \<subseteq> set ([p] \<parallel> ([q] ;\<^sub>c [r]))\<close> by auto
qed


lemma prop12: "set (([p] \<parallel> rs) ;\<^sub>c [q]) \<subseteq> set (([p] ;\<^sub>c [q]) \<parallel> rs)"
proof (induction rs)
  case Nil
  then show ?case by (auto simp: composition_cnf_def cnf_concurrency_def)
next
  case (Cons r rs)
  have "set ([p] \<parallel> (r # rs) ;\<^sub>c [q]) = set ([p] \<parallel> [r] ;\<^sub>c [q]) \<union> set ([p] \<parallel> rs ;\<^sub>c [q])"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set (([p] ;\<^sub>c [q]) \<parallel> (r # rs)) = set (([p] ;\<^sub>c [q]) \<parallel> [r]) \<union> set (([p] ;\<^sub>c [q]) \<parallel> rs)"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set ([p] \<parallel> [r] ;\<^sub>c [q]) \<subseteq> set (([p] ;\<^sub>c [q]) \<parallel> [r])"
    by (simp add: prop10_1)
  have "set ([p] \<parallel> rs ;\<^sub>c [q]) \<subseteq> set (([p] ;\<^sub>c [q]) \<parallel> rs)"
    by (simp add: local.Cons)
  then show "set ([p] \<parallel> (r # rs) ;\<^sub>c [q]) \<subseteq> set (([p] ;\<^sub>c [q]) \<parallel> (r # rs))"
    using \<open>set (([p] ;\<^sub>c [q]) \<parallel> (r # rs)) = set (([p] ;\<^sub>c [q]) \<parallel> [r]) \<union> set (([p] ;\<^sub>c [q]) \<parallel> rs)\<close> \<open>set ([p] \<parallel> (r # rs) ;\<^sub>c [q]) = set ([p] \<parallel> [r] ;\<^sub>c [q]) \<union> set ([p] \<parallel> rs ;\<^sub>c [q])\<close> \<open>set ([p] \<parallel> [r] ;\<^sub>c [q]) \<subseteq> set (([p] ;\<^sub>c [q]) \<parallel> [r])\<close> by auto
qed

lemma prop13: "set ([q] ;\<^sub>c [p] \<parallel> rs) \<subseteq> set ([p] \<parallel> ([q] ;\<^sub>c rs))"
proof (induction rs)
  case Nil
  then show ?case by (auto simp: composition_cnf_def cnf_concurrency_def)
next
  case (Cons r rs)
  have "set ([q] ;\<^sub>c [p] \<parallel> (r # rs)) = set ([q] ;\<^sub>c [p] \<parallel> [r]) \<union> set ([q] ;\<^sub>c [p] \<parallel> rs)"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set ([p] \<parallel> ([q] ;\<^sub>c (r # rs))) = set ([p] \<parallel> ([q] ;\<^sub>c [r])) \<union> set ([p] \<parallel> ([q] ;\<^sub>c rs))"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set ([q] ;\<^sub>c [p] \<parallel> [r]) \<subseteq> set ([p] \<parallel> ([q] ;\<^sub>c [r]))"
    by (simp add: prop10_2)
  have "set ([q] ;\<^sub>c [p] \<parallel> rs) \<subseteq> set ([p] \<parallel> ([q] ;\<^sub>c rs))"
    by (simp add: local.Cons)
  then show "set ([q] ;\<^sub>c [p] \<parallel> (r # rs)) \<subseteq> set ([p] \<parallel> ([q] ;\<^sub>c (r # rs)))"
    using \<open>set ([p] \<parallel> ([q] ;\<^sub>c (r # rs))) = set ([p] \<parallel> ([q] ;\<^sub>c [r])) \<union> set ([p] \<parallel> ([q] ;\<^sub>c rs))\<close> \<open>set ([q] ;\<^sub>c [p] \<parallel> (r # rs)) = set ([q] ;\<^sub>c [p] \<parallel> [r]) \<union> set ([q] ;\<^sub>c [p] \<parallel> rs)\<close> \<open>set ([q] ;\<^sub>c [p] \<parallel> [r]) \<subseteq> set ([p] \<parallel> ([q] ;\<^sub>c [r]))\<close> by auto
qed

lemma prop14: "set ([p] ;\<^sub>c qs \<parallel> [r]) \<subseteq> set (([p] ;\<^sub>c qs) \<parallel> [r])"
proof (induction qs)
  case Nil
  then show ?case by (auto simp: composition_cnf_def cnf_concurrency_def)
next
  case (Cons q qs)
  have "set ([p] ;\<^sub>c (q # qs) \<parallel> [r]) = set ([p] ;\<^sub>c [q] \<parallel> [r]) \<union> set ([p] ;\<^sub>c qs \<parallel> [r])"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set (([p] ;\<^sub>c (q # qs)) \<parallel> [r]) = set (([p] ;\<^sub>c [q]) \<parallel> [r]) \<union> set (([p] ;\<^sub>c qs) \<parallel> [r])"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set ([p] ;\<^sub>c [q] \<parallel> [r]) \<subseteq> set (([p] ;\<^sub>c [q]) \<parallel> [r])"
    by (simp add: prop10_3)
  have "set ([p] ;\<^sub>c qs \<parallel> [r]) \<subseteq> set (([p] ;\<^sub>c qs) \<parallel> [r])"
    by (simp add: local.Cons)
  then show "set ([p] ;\<^sub>c (q # qs) \<parallel> [r]) \<subseteq> set (([p] ;\<^sub>c (q # qs)) \<parallel> [r])"
    using \<open>set (([p] ;\<^sub>c (q # qs)) \<parallel> [r]) = set (([p] ;\<^sub>c [q]) \<parallel> [r]) \<union> set (([p] ;\<^sub>c qs) \<parallel> [r])\<close> \<open>set ([p] ;\<^sub>c (q # qs) \<parallel> [r]) = set ([p] ;\<^sub>c [q] \<parallel> [r]) \<union> set ([p] ;\<^sub>c qs \<parallel> [r])\<close> \<open>set ([p] ;\<^sub>c [q] \<parallel> [r]) \<subseteq> set (([p] ;\<^sub>c [q]) \<parallel> [r])\<close> by auto
qed


lemma subset12: "set (ps \<parallel> q ;\<^sub>c [r]) \<subseteq> set (ps \<parallel> (q ;\<^sub>c [r]))"
proof (induction ps)
  case Nil
  then show ?case by (auto simp: composition_cnf_def cnf_concurrency_def)
next
  case (Cons p ps)
  have "set ((p # ps) \<parallel> q ;\<^sub>c [r]) = set ([p] \<parallel> q ;\<^sub>c [r]) \<union> set (ps \<parallel> q ;\<^sub>c [r])"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set ((p # ps) \<parallel> (q ;\<^sub>c [r])) = set ([p] \<parallel> (q ;\<^sub>c [r])) \<union> set (ps \<parallel> (q ;\<^sub>c [r]))"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set ([p] \<parallel> q ;\<^sub>c [r]) \<subseteq> set ([p] \<parallel> (q ;\<^sub>c [r]))"
    by (simp add: prop11)
  have "set (ps \<parallel> q ;\<^sub>c [r]) \<subseteq> set (ps \<parallel> (q ;\<^sub>c [r]))"
    by (simp add: local.Cons)
  then show "set ((p # ps) \<parallel> q ;\<^sub>c [r]) \<subseteq> set ((p # ps) \<parallel> (q ;\<^sub>c [r]))"
    using \<open>set ((p # ps) \<parallel> (q ;\<^sub>c [r])) = set ([p] \<parallel> (q ;\<^sub>c [r])) \<union> set (ps \<parallel> (q ;\<^sub>c [r]))\<close> \<open>set ((p # ps) \<parallel> q ;\<^sub>c [r]) = set ([p] \<parallel> q ;\<^sub>c [r]) \<union> set (ps \<parallel> q ;\<^sub>c [r])\<close> \<open>set ([p] \<parallel> q ;\<^sub>c [r]) \<subseteq> set ([p] \<parallel> (q ;\<^sub>c [r]))\<close> by auto
qed


lemma subset13: "set ((ps \<parallel> r) ;\<^sub>c [q]) \<subseteq> set ((ps ;\<^sub>c [q]) \<parallel> r)"
proof (induction ps)
  case Nil
  then show ?case by (auto simp: composition_cnf_def cnf_concurrency_def)
next
  case (Cons p ps)
  have "set (((p#ps) \<parallel> r) ;\<^sub>c [q]) = set ((ps \<parallel> r) ;\<^sub>c [q]) \<union> set (([p] \<parallel> r) ;\<^sub>c [q])"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set (((p#ps) ;\<^sub>c [q]) \<parallel> r) = set (([p] ;\<^sub>c [q]) \<parallel> r) \<union> set ((ps ;\<^sub>c [q]) \<parallel> r)"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set (([p] \<parallel> r) ;\<^sub>c [q]) \<subseteq> set (([p] ;\<^sub>c [q]) \<parallel> r)"
    by (simp add: prop12)
  have "set ((ps \<parallel> r) ;\<^sub>c [q]) \<subseteq> set ((ps ;\<^sub>c [q]) \<parallel> r)"
    by (simp add: local.Cons)
  then show ?case
    using \<open>set (((p # ps) ;\<^sub>c [q]) \<parallel> r) = set (([p] ;\<^sub>c [q]) \<parallel> r) \<union> set ((ps ;\<^sub>c [q]) \<parallel> r)\<close> \<open>set ((p # ps) \<parallel> r ;\<^sub>c [q]) = set (ps \<parallel> r ;\<^sub>c [q]) \<union> set ([p] \<parallel> r ;\<^sub>c [q])\<close> \<open>set ([p] \<parallel> r ;\<^sub>c [q]) \<subseteq> set (([p] ;\<^sub>c [q]) \<parallel> r)\<close> by auto
qed

lemma subset14: "set ([q] ;\<^sub>c ps \<parallel> r) \<subseteq> set (ps \<parallel> ([q] ;\<^sub>c r))"
proof (induction ps)
  case Nil
  then show ?case by (auto simp: composition_cnf_def cnf_concurrency_def)
next
  case (Cons p ps)
  have "set ([q] ;\<^sub>c (p # ps) \<parallel> r) = set ([q] ;\<^sub>c [p] \<parallel> r) \<union> set ([q] ;\<^sub>c ps \<parallel> r)"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set ((p # ps) \<parallel> ([q] ;\<^sub>c r)) = set ([p] \<parallel> ([q] ;\<^sub>c r)) \<union> set (ps \<parallel> ([q] ;\<^sub>c r))"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set ([q] ;\<^sub>c [p] \<parallel> r) \<subseteq> set ([p] \<parallel> ([q] ;\<^sub>c r))"
    by (simp add: prop13)
  have "set ([q] ;\<^sub>c ps \<parallel> r) \<subseteq> set (ps \<parallel> ([q] ;\<^sub>c r))"
    by (simp add: local.Cons)
  then show "set ([q] ;\<^sub>c (p # ps) \<parallel> r) \<subseteq> set ((p # ps) \<parallel> ([q] ;\<^sub>c r))"
    using \<open>set ((p # ps) \<parallel> ([q] ;\<^sub>c r)) = set ([p] \<parallel> ([q] ;\<^sub>c r)) \<union> set (ps \<parallel> ([q] ;\<^sub>c r))\<close> \<open>set ([q] ;\<^sub>c (p # ps) \<parallel> r) = set ([q] ;\<^sub>c [p] \<parallel> r) \<union> set ([q] ;\<^sub>c ps \<parallel> r)\<close> \<open>set ([q] ;\<^sub>c [p] \<parallel> r) \<subseteq> set ([p] \<parallel> ([q] ;\<^sub>c r))\<close> by auto
qed

lemma subset15: "set ([p] ;\<^sub>c q \<parallel> rs) \<subseteq> set (([p] ;\<^sub>c q) \<parallel> rs)"
proof (induction rs)
  case Nil
  then show ?case by (auto simp: composition_cnf_def cnf_concurrency_def)
next
  case (Cons r rs)
  have "set ([p] ;\<^sub>c q \<parallel> (r # rs)) = set ([p] ;\<^sub>c q \<parallel> [r]) \<union> set ([p] ;\<^sub>c q \<parallel> rs)"
    apply (auto simp: composition_cnf_def cnf_concurrency_def)
    by (meson UN_I image_eqI)
  have "set (([p] ;\<^sub>c q) \<parallel> (r # rs)) = set (([p] ;\<^sub>c q) \<parallel> [r]) \<union> set (([p] ;\<^sub>c q) \<parallel> rs)"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set ([p] ;\<^sub>c q \<parallel> [r]) \<subseteq> set (([p] ;\<^sub>c q) \<parallel> [r])"
    by (simp add: prop14)
  have "set ([p] ;\<^sub>c q \<parallel> rs) \<subseteq> set (([p] ;\<^sub>c q) \<parallel> rs)"
    by (simp add: local.Cons)
  then show "set ([p] ;\<^sub>c q \<parallel> (r # rs)) \<subseteq> set (([p] ;\<^sub>c q) \<parallel> (r # rs))"
    using \<open>set (([p] ;\<^sub>c q) \<parallel> (r # rs)) = set (([p] ;\<^sub>c q) \<parallel> [r]) \<union> set (([p] ;\<^sub>c q) \<parallel> rs)\<close> \<open>set ([p] ;\<^sub>c q \<parallel> (r # rs)) = set ([p] ;\<^sub>c q \<parallel> [r]) \<union> set ([p] ;\<^sub>c q \<parallel> rs)\<close> \<open>set ([p] ;\<^sub>c q \<parallel> [r]) \<subseteq> set (([p] ;\<^sub>c q) \<parallel> [r])\<close> by auto
qed

theorem Conc_composeright_1: "set ((p \<parallel> q) ;\<^sub>c rs) \<subseteq> set (p \<parallel> (q ;\<^sub>c rs))"
proof -
  fix rs
  show "set ((p \<parallel> q) ;\<^sub>c rs) \<subseteq> set (p \<parallel> (q ;\<^sub>c rs))"
proof (induction rs)
  case Nil
  then show ?case by (auto simp: composition_cnf_def)
next
  case (Cons r rs)
  have "set (p \<parallel> q ;\<^sub>c (r # rs)) = set (p \<parallel> q ;\<^sub>c [r]) \<union> set (p \<parallel> q ;\<^sub>c rs)"
    by (auto simp: composition_cnf_def)
  have "set (p \<parallel> (q ;\<^sub>c (r # rs))) = set (p \<parallel> (q ;\<^sub>c [r])) \<union> set (p \<parallel> (q ;\<^sub>c rs))"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set (p \<parallel> q ;\<^sub>c [r]) \<subseteq> set (p \<parallel> (q ;\<^sub>c [r]))"
    by (simp add: subset12)
  have "set (p \<parallel> q ;\<^sub>c (r # rs)) \<subseteq> set (p \<parallel> (q ;\<^sub>c (r # rs)))"
    using \<open>set (p \<parallel> (q ;\<^sub>c (r # rs))) = set (p \<parallel> (q ;\<^sub>c [r])) \<union> set (p \<parallel> (q ;\<^sub>c rs))\<close> \<open>set (p \<parallel> q ;\<^sub>c (r # rs)) = set (p \<parallel> q ;\<^sub>c [r]) \<union> set (p \<parallel> q ;\<^sub>c rs)\<close> \<open>set (p \<parallel> q ;\<^sub>c [r]) \<subseteq> set (p \<parallel> (q ;\<^sub>c [r]))\<close> local.Cons by auto
  then show ?case
    by simp
qed
qed

theorem Conc_composeright1_1: "set ((p \<parallel> r) ;\<^sub>c qs) \<subseteq> set ((p ;\<^sub>c qs) \<parallel> r)"
proof -
  fix qs
  show "set ((p \<parallel> r) ;\<^sub>c qs) \<subseteq> set ((p ;\<^sub>c qs) \<parallel> r)"
proof (induction qs)
  case Nil
  then show ?case by (auto simp: composition_cnf_def)
next
  case (Cons q qs)
  have "set ((p \<parallel> r) ;\<^sub>c (q#qs)) = set ((p \<parallel> r) ;\<^sub>c [q]) \<union> set ((p \<parallel> r) ;\<^sub>c qs)"
    by (auto simp: composition_cnf_def)
  have "set ((p ;\<^sub>c (q#qs)) \<parallel> r) = set ((p ;\<^sub>c [q]) \<parallel> r) \<union> set ((p ;\<^sub>c qs) \<parallel> r)"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set ((p \<parallel> r) ;\<^sub>c [q]) \<subseteq> set ((p ;\<^sub>c [q]) \<parallel> r)"
    by (simp add: subset13)
  have "set ((p \<parallel> r) ;\<^sub>c qs) \<subseteq> set ((p ;\<^sub>c qs) \<parallel> r)"
    by (simp add: local.Cons)
  then show ?case
    using \<open>set ((p ;\<^sub>c (q # qs)) \<parallel> r) = set ((p ;\<^sub>c [q]) \<parallel> r) \<union> set ((p ;\<^sub>c qs) \<parallel> r)\<close> \<open>set (p \<parallel> r ;\<^sub>c (q # qs)) = set (p \<parallel> r ;\<^sub>c [q]) \<union> set (p \<parallel> r ;\<^sub>c qs)\<close> \<open>set (p \<parallel> r ;\<^sub>c [q]) \<subseteq> set ((p ;\<^sub>c [q]) \<parallel> r)\<close> by auto
qed
qed



theorem Conc_composeleft1_1: "set (qs ;\<^sub>c (p \<parallel> r)) \<subseteq> set (p \<parallel> (qs ;\<^sub>c r))"
proof -
  fix qs
  show "set (qs ;\<^sub>c (p \<parallel> r)) \<subseteq> set (p \<parallel> (qs ;\<^sub>c r))"
proof (induction qs)
  case Nil
  then show ?case by (auto simp: composition_cnf_def)
next
  case (Cons q qs)
  have "set ((q # qs) ;\<^sub>c p \<parallel> r) = set ([q] ;\<^sub>c p \<parallel> r) \<union> set (qs ;\<^sub>c p \<parallel> r)"
    by (auto simp: composition_cnf_def)
  have "set (p \<parallel> ((q # qs) ;\<^sub>c r)) = set (p \<parallel> ([q] ;\<^sub>c r)) \<union> set (p \<parallel> (qs ;\<^sub>c r))"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set ([q] ;\<^sub>c p \<parallel> r) \<subseteq> set (p \<parallel> ([q] ;\<^sub>c r))"
    by (simp add: subset14)
  have "set (qs ;\<^sub>c p \<parallel> r) \<subseteq> set (p \<parallel> (qs ;\<^sub>c r))"
    by (simp add: local.Cons)
  then show "set ((q # qs) ;\<^sub>c p \<parallel> r) \<subseteq> set (p \<parallel> ((q # qs) ;\<^sub>c r))"
    using \<open>set ((q # qs) ;\<^sub>c p \<parallel> r) = set ([q] ;\<^sub>c p \<parallel> r) \<union> set (qs ;\<^sub>c p \<parallel> r)\<close> \<open>set ([q] ;\<^sub>c p \<parallel> r) \<subseteq> set (p \<parallel> ([q] ;\<^sub>c r))\<close> \<open>set (p \<parallel> ((q # qs) ;\<^sub>c r)) = set (p \<parallel> ([q] ;\<^sub>c r)) \<union> set (p \<parallel> (qs ;\<^sub>c r))\<close> by auto
qed
qed


theorem Conc_composeright_2: "set (ps ;\<^sub>c (q \<parallel> r)) \<subseteq> set ((ps ;\<^sub>c q) \<parallel> r)"
proof -
  fix ps
  show "set (ps ;\<^sub>c (q \<parallel> r)) \<subseteq> set ((ps ;\<^sub>c q) \<parallel> r)"
proof (induction ps)
  case Nil
  then show ?case by (auto simp: composition_cnf_def cnf_concurrency_def)
next
  case (Cons p ps)
  have "set ((p # ps) ;\<^sub>c q \<parallel> r) = set ([p] ;\<^sub>c q \<parallel> r) \<union> set (ps ;\<^sub>c q \<parallel> r)"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set (((p # ps) ;\<^sub>c q) \<parallel> r) = set (([p] ;\<^sub>c q) \<parallel> r) \<union> set ((ps ;\<^sub>c q) \<parallel> r)"
    by (auto simp: composition_cnf_def cnf_concurrency_def)
  have "set ([p] ;\<^sub>c q \<parallel> r) \<subseteq> set (([p] ;\<^sub>c q) \<parallel> r)"
    by (simp add: subset15)
  have " set (ps ;\<^sub>c q \<parallel> r) \<subseteq> set ((ps ;\<^sub>c q) \<parallel> r)"
    by (simp add: local.Cons)
  then show "set ((p # ps) ;\<^sub>c q \<parallel> r) \<subseteq> set (((p # ps) ;\<^sub>c q) \<parallel> r)"
    using \<open>set (((p # ps) ;\<^sub>c q) \<parallel> r) = set (([p] ;\<^sub>c q) \<parallel> r) \<union> set ((ps ;\<^sub>c q) \<parallel> r)\<close> \<open>set ((p # ps) ;\<^sub>c q \<parallel> r) = set ([p] ;\<^sub>c q \<parallel> r) \<union> set (ps ;\<^sub>c q \<parallel> r)\<close> \<open>set ([p] ;\<^sub>c q \<parallel> r) \<subseteq> set (([p] ;\<^sub>c q) \<parallel> r)\<close> by auto
qed
qed

theorem Conc_composeleft: "evaluate ((p \<parallel> q) ;\<^sub>c r) C \<preceq>\<^sub>p evaluate (p \<parallel> (q ;\<^sub>c r)) C" \<comment> \<open>Conc_composeleft\<close>
  by (simp add: Conc_composeright_1 eval_subprogram12)
theorem Conc_composeleftright: "evaluate (q ;\<^sub>c (p \<parallel> r)) C \<preceq>\<^sub>p evaluate (p \<parallel> (q ;\<^sub>c r)) C" \<comment> \<open>Conc_composeleftright\<close>
  by (simp add: Conc_composeleft1_1 eval_subprogram12)
theorem Conc_composeright: "evaluate (p ;\<^sub>c (q \<parallel> r)) C \<preceq>\<^sub>p evaluate ((p ;\<^sub>c q) \<parallel> r) C" \<comment> \<open>Conc_composeright\<close>
  by (simp add: Conc_composeright_2 eval_subprogram12)
theorem Conc_composerightleft: "evaluate ((p \<parallel> r) ;\<^sub>c q) C \<preceq>\<^sub>p evaluate ((p ;\<^sub>c q) \<parallel> r) C" \<comment> \<open>Conc_composerightleft\<close>
  by (simp add: Conc_composeright1_1 eval_subprogram12)

theorem Conc_composegeneral: "set (([p] ;\<^sub>c [q]) \<parallel> ([u] ;\<^sub>c [v])) \<subseteq> set (([p] ;\<^sub>c [u]) \<parallel> ([q] ;\<^sub>c [v]))"
  oops
theorem Conc_composegeneral: "set (([p] ;\<^sub>c [u]) \<parallel> ([q] ;\<^sub>c [v])) \<subseteq> set (([p] ;\<^sub>c [q]) \<parallel> ([u] ;\<^sub>c [v]))"
  oops
theorem Conc_composegeneral: "set ((p ;\<^sub>c q) \<parallel> (u ;\<^sub>c v)) \<subseteq> set ((p ;\<^sub>c u) \<parallel> (q ;\<^sub>c v))" \<comment> \<open>Conc_composegeneral\<close>
  oops

end