theory CNF_concurrency
  imports Big_choice
begin

theorem "(a@b)\<parallel>c =(a\<parallel>c)@(b\<parallel>c)"
  by (auto simp: cnf_concurrency_def)

(*
theorem "evaluate (c\<parallel>(a@b)) = evaluate ((c\<parallel>a)@(c\<parallel>b))"
  sorry
*)
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


theorem conc_size: "size xs * size ys \<le> size (xs \<parallel> ys)"
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
    case Cons2: (Cons y ys)
    have "length (xs) * length (y # ys) \<le> length ((xs) \<parallel> (y # ys))"
      using Cons2.prems by blast
    have "length (x # xs) * length (ys) \<le> length ((x # xs) \<parallel> (ys))"
      using Cons1 Cons2.IH by auto
    have "(x # xs) \<parallel> (y # ys) = x \<interleave> y @ concat (map ((\<interleave>) x) ys) @ concat (concat (map (\<lambda>path_m. path_m \<interleave> y # map ((\<interleave>) path_m) ys) xs))"  by (auto simp: cnf_concurrency_def)
    have "size ((x # xs) \<parallel> (y # ys)) = size (x \<interleave> y) + size (concat (map ((\<interleave>) x) ys)) + size (concat (concat (map (\<lambda>path_m. path_m \<interleave> y # map ((\<interleave>) path_m) ys) xs)))"
      by (simp add: \<open>(x # xs) \<parallel> (y # ys) = x \<interleave> y @ concat (map ((\<interleave>) x) ys) @ concat (concat (map (\<lambda>path_m. path_m \<interleave> y # map ((\<interleave>) path_m) ys) xs))\<close>)
    have "size (concat (concat (map (\<lambda>path_m. path_m \<interleave> y # map ((\<interleave>) path_m) ys) xs))) \<ge> size (concat (concat (map (\<lambda>path_m. map ((\<interleave>) path_m) ys) xs)))" sorry
    then show "length (x # xs) * length (y # ys) \<le> length ((x # xs) \<parallel> (y # ys))" sorry
  qed
qed

value "map (\<lambda>path_m. map ((\<interleave>) path_m) ([[]]::nat list list)) [[]]"

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

theorem assoc_cnf: "evaluate ((xs \<parallel> ys) \<parallel> zs) = evaluate (xs \<parallel> (ys \<parallel> zs))"
  by (simp add: assoc_cnf1 equal_eval)

theorem cnf_prop: "xs \<noteq> [] \<Longrightarrow> evaluate [x#xs] = x ; (evaluate [xs])"
  apply (auto simp: evaluate_def)
  by (simp add: Concat_prop_10)

theorem cnf_prop2: "xs \<noteq> [] \<Longrightarrow> evaluate [xs@[x]] = (evaluate [xs]) ; x"
  apply (auto simp: evaluate_def)
  by (simp add: Concat_prop_2)

lemma restrict_cnf1: "evaluate ([x] \<sslash>\<^sub>c C) = (evaluate [x]) \<sslash>\<^sub>p C"
proof (cases x)
  case Nil
  then show ?thesis by (auto simp: evaluate_def Skip_def restriction_cnf_def restrict_p_def restrict_r_def S_def)
next
  case (Cons xx x)
  have "evaluate ([xx#x] \<sslash>\<^sub>c C) = evaluate [xx#x] \<sslash>\<^sub>p C"
  proof (cases "x = []")
    case True
    then show ?thesis by (auto simp: evaluate_def restriction_cnf_def)
  next
    case False
    have "evaluate ([xx#x] \<sslash>\<^sub>c C) = xx \<sslash>\<^sub>p C ; evaluate [x]" apply (auto simp: evaluate_def restriction_cnf_def)
      by (simp add: Concat_prop_10 False)
    then show ?thesis
      by (simp add: False cnf_prop compose_absorb_1)
  qed
  then show ?thesis using Cons by auto
qed

theorem restr_distrib: "a \<sslash>\<^sub>p C \<union>\<^sub>p b \<sslash>\<^sub>p C = (a \<union>\<^sub>p b) \<sslash>\<^sub>p C"
  by (auto simp: choice_def restrict_p_def restr_post_def restrict_r_def S_def Field_def)

theorem restrict_cnf: "evaluate (xs \<sslash>\<^sub>c C) = (evaluate xs) \<sslash>\<^sub>p C"
proof (induction xs)
  case Nil
  then show ?case  apply (auto simp: restriction_cnf_def evaluate_def restrict_p_def Fail_def S_def restrict_r_def) [1] done
next
  case (Cons x xs)
  then show "evaluate ((x#xs) \<sslash>\<^sub>c C) = (evaluate (x#xs)) \<sslash>\<^sub>p C"
  proof (cases "xs=[]")
    case True
    then show ?thesis
      by (simp add: restrict_cnf1) 
  next
    case False
    have "(x#xs) \<sslash>\<^sub>c C = ([x] \<sslash>\<^sub>c C) @ (xs \<sslash>\<^sub>c C)" by (auto simp: restriction_cnf_def)
    have "evaluate ((x#xs) \<sslash>\<^sub>c C) = evaluate (([x] \<sslash>\<^sub>c C) @ (xs \<sslash>\<^sub>c C))"
      by (simp add: \<open>(x # xs) \<sslash>\<^sub>c C = [x] \<sslash>\<^sub>c C @ xs \<sslash>\<^sub>c C\<close>)
    have "... = evaluate ([x] \<sslash>\<^sub>c C) \<union>\<^sub>p evaluate (xs \<sslash>\<^sub>c C)" using False apply (auto simp: evaluate_def)
      by (metis Choice_prop_7 choice_commute list.map_disc_iff not_Cons_self2 restriction_cnf_def)
    have "... = evaluate [x] \<sslash>\<^sub>p C \<union>\<^sub>p evaluate xs \<sslash>\<^sub>p C"
      by (simp add: local.Cons restrict_cnf1)
    have "... = (evaluate [x] \<union>\<^sub>p evaluate xs) \<sslash>\<^sub>p C"
      by (simp add: restr_distrib)
    have "... = (evaluate (x#xs)) \<sslash>\<^sub>p C"
      by (simp add: False concat_prop3)
    then show ?thesis
      by (metis \<open>(x # xs) \<sslash>\<^sub>c C = [x] \<sslash>\<^sub>c C @ xs \<sslash>\<^sub>c C\<close> \<open>evaluate ([x] \<sslash>\<^sub>c C @ xs \<sslash>\<^sub>c C) = evaluate ([x] \<sslash>\<^sub>c C) \<union>\<^sub>p evaluate (xs \<sslash>\<^sub>c C)\<close> \<open>evaluate [x] \<sslash>\<^sub>p C \<union>\<^sub>p evaluate xs \<sslash>\<^sub>p C = (evaluate [x] \<union>\<^sub>p evaluate xs) \<sslash>\<^sub>p C\<close> local.Cons restrict_cnf1)
  qed
qed

lemma corestrict_cnf1: "evaluate ([x] \<setminus>\<^sub>c C) = (evaluate [x]) \<setminus>\<^sub>p C"
proof (induction x rule: rev_induct)
  case Nil
  then show ?case by (auto simp: evaluate_def Skip_def corestriction_cnf_def corestrict_p_def corestrict_r_def restrict_p_def restrict_r_def S_def)
next
  case (snoc xx x)
  have "evaluate ([x@[xx]] \<setminus>\<^sub>c C) = evaluate [x@[xx]] \<setminus>\<^sub>p C"
  proof (cases "x = []")
    case True
    have "Concat (corestrict_path [xx] C) = xx \<setminus>\<^sub>p C"
      by (metis (no_types, lifting) Concat.simps(2) append1_eq_conv append_self_conv2 corestrict_path.elims list.distinct(1))
    then show ?thesis apply (auto simp: evaluate_def corestriction_cnf_def corestrict_p_def corestrict_r_def S_def Field_def)
      using True by auto
  next
    case False
    have "evaluate ([x@[xx]] \<setminus>\<^sub>c C) = evaluate [x] ; xx \<setminus>\<^sub>p C" apply (auto simp: evaluate_def corestriction_cnf_def)
      by (simp add: Concat_prop_2 False)
    then show ?thesis
      by (simp add: False cnf_prop2 corestrict_compose)
  qed
  then show ?case using Cons by auto
qed

theorem corestrict_cnf: "evaluate (xs \<setminus>\<^sub>c C) = (evaluate xs) \<setminus>\<^sub>p C"
proof (induction xs)
  case Nil
  then show ?case  apply (auto simp: corestriction_cnf_def evaluate_def restrict_p_def Fail_def S_def restrict_r_def corestrict_p_def corestrict_r_def) [1] done
next
  case (Cons x xs)
  then show "evaluate ((x#xs) \<setminus>\<^sub>c C) = (evaluate (x#xs)) \<setminus>\<^sub>p C"
  proof (cases "xs=[]")
    case True
    then show ?thesis
      by (simp add: corestrict_cnf1) 
  next
    case False
    have "(x#xs) \<setminus>\<^sub>c C = ([x] \<setminus>\<^sub>c C) @ (xs \<setminus>\<^sub>c C)" by (auto simp: corestriction_cnf_def)
    have "evaluate ((x#xs) \<setminus>\<^sub>c C) = evaluate (([x] \<setminus>\<^sub>c C) @ (xs \<setminus>\<^sub>c C))"
      by (simp add: \<open>(x # xs) \<setminus>\<^sub>c C = [x] \<setminus>\<^sub>c C @ xs \<setminus>\<^sub>c C\<close>)
    have "... = evaluate ([x] \<setminus>\<^sub>c C) \<union>\<^sub>p evaluate (xs \<setminus>\<^sub>c C)" using False apply (auto simp: evaluate_def)
      by (metis Choice_prop_7 choice_commute list.map_disc_iff not_Cons_self2 corestriction_cnf_def)
    have "... = evaluate [x] \<setminus>\<^sub>p C \<union>\<^sub>p evaluate xs \<setminus>\<^sub>p C"
      by (simp add: local.Cons corestrict_cnf1)
    have "... = (evaluate [x] \<union>\<^sub>p evaluate xs) \<setminus>\<^sub>p C"
      by (simp add: corestrict_choice_1)
    have "... = (evaluate (x#xs)) \<setminus>\<^sub>p C"
      by (simp add: False concat_prop3)
    then show ?thesis
      using \<open>evaluate ((x # xs) \<setminus>\<^sub>c C) = evaluate ([x] \<setminus>\<^sub>c C @ xs \<setminus>\<^sub>c C)\<close> \<open>evaluate ([x] \<setminus>\<^sub>c C @ xs \<setminus>\<^sub>c C) = evaluate ([x] \<setminus>\<^sub>c C) \<union>\<^sub>p evaluate (xs \<setminus>\<^sub>c C)\<close> \<open>evaluate ([x] \<setminus>\<^sub>c C) \<union>\<^sub>p evaluate (xs \<setminus>\<^sub>c C) = evaluate [x] \<setminus>\<^sub>p C \<union>\<^sub>p evaluate xs \<setminus>\<^sub>p C\<close> \<open>evaluate [x] \<setminus>\<^sub>p C \<union>\<^sub>p evaluate xs \<setminus>\<^sub>p C = (evaluate [x] \<union>\<^sub>p evaluate xs) \<setminus>\<^sub>p C\<close> by presburger
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
      then show ?thesis using \<open>length (xs \<parallel> (ys \<union>\<^sub>c zs)) = 1\<close> cnf_choice1 in_set_conv_nth less_nat_zero_code list.exhaust list.set_intros(1) path_decomp
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

theorem eval_subprogram: "evaluate ys \<preceq>\<^sub>p evaluate (y # ys)"
  apply (auto simp: evaluate_def)
  by (metis Choice.simps(1) Choice_prop_1 Choice_prop_1_2 Choice_prop_3 fail_subprogram3 program_is_subprogram_of_choice)

theorem eval_subprogram2: "evaluate [y] \<preceq>\<^sub>p evaluate (y # ys)"
  apply (auto simp: evaluate_def)
  by (metis Choice.simps(2) Choice_prop_1_2 program_is_subprogram_of_choice subprogram_is_preorder)

lemma eval_subprogram3:"set xs \<subseteq> set [y] \<Longrightarrow> evaluate xs \<preceq>\<^sub>p evaluate [y]"
  apply (induction xs) apply (auto simp:)
  apply (simp add: eval_subprogram)
  by (metis choice_suprogram_prop concat_prop3 eval_subprogram2)

lemma eval_subprogram4:"set [x] \<subseteq> set ys \<Longrightarrow> evaluate [x] \<preceq>\<^sub>p evaluate ys"
  apply (induction ys) apply (auto simp:)
  apply (simp add: eval_subprogram2)
  by (meson eval_subprogram subprogram_is_transitive)

lemma eval_subprogram5: "size xs > 1 \<Longrightarrow> equal_cnf xs zs \<Longrightarrow> evaluate xs = evaluate [] \<union>\<^sub>p evaluate zs"
proof -
  assume a1: "size xs > 1" and a2: "equal_cnf xs zs"
  have "evaluate xs = evaluate zs"
    by (simp add: a2 equal_eval)
  have "zs \<noteq> []"
    using a1 a2 equal_empty by force
  have "size zs > 1" using a1 a2 apply (auto simp: equal_cnf_def)
    by (simp add: Suc_lessI \<open>zs \<noteq> []\<close>)
  have "evaluate [] \<union>\<^sub>p evaluate zs = evaluate zs" apply (auto simp: evaluate_def Fail_def)
    by (metis Choice_prop_18 Fail_def \<open>1 < length zs\<close> length_map)
  show "evaluate xs = evaluate [] \<union>\<^sub>p evaluate zs"
    by (simp add: \<open>evaluate [] \<union>\<^sub>p evaluate zs = evaluate zs\<close> \<open>evaluate xs = evaluate zs\<close>)
qed

theorem eval_subprogram6: "size (ys @ zs) > 1 \<Longrightarrow> evaluate ys \<union>\<^sub>p evaluate zs = evaluate (ys \<union>\<^sub>c zs)"
  apply (induction ys) apply (auto simp: choice_cnf_def evaluate_def)
  apply (metis Choice_prop_18 One_nat_def choice_commute length_map)
  apply (smt (verit, ccfv_threshold) Choice_prop_19 Cons_eq_appendI add_gr_0 choice_commute length_Cons length_append length_greater_0_conv length_map less_add_same_cancel1 plus_1_eq_Suc)
  by (smt (verit) Choice.simps(2) Choice_prop_1_2 Choice_prop_22 Choice_prop_7 Cons_eq_appendI choice_commute list.discI map_is_Nil_conv self_append_conv)

theorem eval_subprogram7: "size xs \<noteq> 1 \<Longrightarrow> equal_cnf xs (ys \<union>\<^sub>c zs) \<Longrightarrow> evaluate xs = evaluate ys \<union>\<^sub>p evaluate zs"
  apply (cases "xs = []") apply (auto simp: choice_cnf_def)
  apply (smt (verit) Choice_prop_19 Nil_is_append_conv choice_cnf_def cnf_choice2 equal_empty equal_sym eval_prop eval_prop1 evaluate_def length_greater_0_conv list.size(3) map_append non_empty2 non_empty4 non_empty9 not_Cons_self2)
  apply (cases "ys = []") apply auto 
   apply (cases "zs = []")
  apply (simp add: equal_empty)
   apply (simp add: Suc_lessI eval_subprogram5)
  apply (cases "size ys = 1") using concat_prop3 equal_eval 
  apply (metis (no_types, lifting) Cons_eq_appendI One_nat_def append.right_neutral append_eq_append_conv append_eq_append_conv2 equal_cnf_def length_0_conv length_Suc_conv)
  apply (cases "size zs = 1") using equal_eval
  apply (metis (no_types, lifting) One_nat_def eval_prop1 length_0_conv length_Suc_conv)
proof -
  assume "length xs \<noteq> Suc 0" and "equal_cnf xs (ys @ zs)" and "xs \<noteq> []" and  "ys \<noteq> []" and "length ys \<noteq> 1" and "length zs \<noteq> 1"
  have "set xs = set ys \<union> set zs"
    by (metis \<open>equal_cnf xs (ys @ zs)\<close> equal_cnf_def set_append)
  have "evaluate ys \<union>\<^sub>p evaluate zs = evaluate (ys \<union>\<^sub>c zs)"
    by (metis One_nat_def Suc_lessI \<open>equal_cnf xs (ys @ zs)\<close> \<open>length xs \<noteq> Suc 0\<close> \<open>length zs \<noteq> 1\<close> \<open>xs \<noteq> []\<close> append.right_neutral choice_cnf_def equal_eval eval_subprogram6 length_append length_greater_0_conv trans_less_add2)
  show "evaluate xs = evaluate ys \<union>\<^sub>p evaluate zs"
    by (simp add: \<open>equal_cnf xs (ys @ zs)\<close> \<open>evaluate ys \<union>\<^sub>p evaluate zs = evaluate (ys \<union>\<^sub>c zs)\<close> choice_cnf_def equal_eval)
qed

lemma eval_subprogram8: "evaluate [x. x \<leftarrow> xs, f x] \<preceq>\<^sub>p evaluate xs"
proof (induction xs)
  case Nil
  then show ?case apply (simp add: subprogram_is_preorder) done
next
  case (Cons x xs)
  then show "evaluate [x. x \<leftarrow> (x#xs), f x] \<preceq>\<^sub>p evaluate (x#xs)"
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
    then have "evaluate [x. x \<leftarrow> (x#xs), f x] = evaluate [x. x \<leftarrow> [x], f x] \<union>\<^sub>p evaluate [x. x \<leftarrow> xs, f x]" 
      using eval_subprogram7[of "[x. x \<leftarrow> (x#xs), f x]" "[x. x \<leftarrow> [x], f x]" "[x. x \<leftarrow> xs, f x]"]
      using \<open>concat (map (\<lambda>x. if f x then [x] else []) (x # xs)) = x # concat (map (\<lambda>x. if f x then [x] else []) xs)\<close> \<open>equal_cnf (concat (map (\<lambda>x. if f x then [x] else []) (x # xs))) (concat (map (\<lambda>x. if f x then [x] else []) [x]) \<union>\<^sub>c concat (map (\<lambda>x. if f x then [x] else []) xs))\<close> by fastforce
    have "evaluate [x. x \<leftarrow> xs, f x] \<preceq>\<^sub>p evaluate xs"
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

lemma eval_subprogram9: "evaluate [x. x \<leftarrow> (x#xx#xs), f x] \<union>\<^sub>p evaluate [x. x \<leftarrow> x#xx#xs, \<not>f x] = (evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (evaluate [x. x \<leftarrow> (xs), f x] \<union>\<^sub>p evaluate [x. x \<leftarrow> xs, \<not>f x])"
proof (induction xs)
  case Nil
  have "(evaluate [x. x \<leftarrow> [], f x] \<union>\<^sub>p evaluate [x. x \<leftarrow> [], \<not>f x]) = Fail {}" by(auto simp: evaluate_def Fail_def choice_def restr_post_def S_def restrict_r_def)
  have "evaluate [x. x \<leftarrow> [x,xx], f x] \<union>\<^sub>p evaluate [x. x \<leftarrow> [x,xx], \<not>f x] = (evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (Fail {})"
    by (smt (z3) append.right_neutral choice_commute cnf_choice2 concat.simps(1) concat.simps(2) concat_prop2 concat_prop3 list.map_disc_iff list.simps(9) non_empty7 self_append_conv2 skip_prop_12 special_empty1)
  then show "evaluate [x. x \<leftarrow> [x,xx], f x] \<union>\<^sub>p evaluate [x. x \<leftarrow> [x,xx], \<not>f x] = (evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (evaluate [x. x \<leftarrow> [], f x] \<union>\<^sub>p evaluate [x. x \<leftarrow> [], \<not>f x])"
    using \<open>evaluate (concat (map (\<lambda>x. if f x then [x] else []) [])) \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) [])) = Fail {}\<close> by presburger
next
  case (Cons a xs)
  then show ?case
  proof (cases "f a")
    case True
    then have "evaluate [x. x \<leftarrow> (x#xx#a#xs), f x] \<union>\<^sub>p evaluate [x. x \<leftarrow> x#xx#a#xs, \<not>f x] = (evaluate [a] \<union>\<^sub>p evaluate [x. x \<leftarrow> (x#xx#xs), f x]) \<union>\<^sub>p evaluate [x. x \<leftarrow> x#xx#xs, \<not>f x]"
      apply (auto simp add: evaluate_def)
      apply (smt (verit) Choice_prop_22 choice_assoc_1 choice_commute)
      apply (metis (no_types, lifting) Choice_prop_1_4 foldl_Cons list.distinct(1))
      apply (smt (z3) Choice.simps(2) Choice_prop_1_2 Choice_prop_1_4 choice_assoc_1 choice_commute foldl_Nil)
      by (simp add: fold_choice)
    have "... = evaluate [a] \<union>\<^sub>p ((evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p ((evaluate [x. x \<leftarrow> xs, f x]) \<union>\<^sub>p evaluate [x. x \<leftarrow> xs, \<not>f x]))"
      by (metis (no_types, lifting) choice_assoc_1 local.Cons)
    have "... = ((evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (evaluate [a] \<union>\<^sub>p ((evaluate [x. x \<leftarrow> xs, f x]) \<union>\<^sub>p evaluate [x. x \<leftarrow> xs, \<not>f x])))"
      by (smt (verit, del_insts) choice_assoc_1 choice_commute)
    have "... = (evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (evaluate [x. x \<leftarrow> (a#xs), f x] \<union>\<^sub>p evaluate [x. x \<leftarrow> (a#xs), \<not>f x])"
      apply (auto simp: evaluate_def)
      apply (simp add: True)
      by (smt (z3) Choice_prop_22 choice_assoc_1 choice_commute)
    then show ?thesis
      using \<open>(evaluate [a] \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if f x then [x] else []) (x # xx # xs)))) \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) (x # xx # xs))) = evaluate [a] \<union>\<^sub>p ((evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (evaluate (concat (map (\<lambda>x. if f x then [x] else []) xs)) \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) xs))))\<close> \<open>evaluate (concat (map (\<lambda>x. if f x then [x] else []) (x # xx # a # xs))) \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) (x # xx # a # xs))) = (evaluate [a] \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if f x then [x] else []) (x # xx # xs)))) \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) (x # xx # xs)))\<close> \<open>evaluate [a] \<union>\<^sub>p ((evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (evaluate (concat (map (\<lambda>x. if f x then [x] else []) xs)) \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) xs)))) = (evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (evaluate [a] \<union>\<^sub>p (evaluate (concat (map (\<lambda>x. if f x then [x] else []) xs)) \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) xs))))\<close> by argo
  next
    case False
    then have "evaluate [x. x \<leftarrow> (x#xx#a#xs), f x] \<union>\<^sub>p evaluate [x. x \<leftarrow> x#xx#a#xs, \<not>f x] = evaluate [x. x \<leftarrow> (x#xx#xs), f x] \<union>\<^sub>p (evaluate [a] \<union>\<^sub>p evaluate [x. x \<leftarrow> x#xx#xs, \<not>f x])"
      apply (auto simp add: evaluate_def)
      apply (smt (verit) Choice_prop_22 choice_assoc_1 choice_commute)
      apply (metis (no_types, lifting) Choice_prop_1_4 foldl_Cons list.distinct(1))
      apply (smt (z3) Choice.simps(2) Choice_prop_1_2 Choice_prop_1_4 choice_assoc_1 choice_commute foldl_Nil)
      by (simp add: fold_choice)
    have "... = evaluate [a] \<union>\<^sub>p ((evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p ((evaluate [x. x \<leftarrow> xs, f x]) \<union>\<^sub>p evaluate [x. x \<leftarrow> xs, \<not>f x]))"
      by (smt (verit, best) choice_assoc_1 choice_commute local.Cons)
    have "... = ((evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (evaluate [a] \<union>\<^sub>p ((evaluate [x. x \<leftarrow> xs, f x]) \<union>\<^sub>p evaluate [x. x \<leftarrow> xs, \<not>f x])))"
      by (smt (verit, del_insts) choice_assoc_1 choice_commute)
    have "... = (evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (evaluate [x. x \<leftarrow> (a#xs), f x] \<union>\<^sub>p evaluate [x. x \<leftarrow> (a#xs), \<not>f x])"
      apply (auto simp: evaluate_def)
      apply (smt (verit, ccfv_threshold) Choice_prop_22 choice_assoc_1 choice_commute)
      by (smt (z3) Choice_prop_22 choice_assoc_1 choice_commute)
    then show ?thesis
      using \<open>evaluate (concat (map (\<lambda>x. if f x then [x] else []) (x # xx # a # xs))) \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) (x # xx # a # xs))) = evaluate (concat (map (\<lambda>x. if f x then [x] else []) (x # xx # xs))) \<union>\<^sub>p (evaluate [a] \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) (x # xx # xs))))\<close> \<open>evaluate (concat (map (\<lambda>x. if f x then [x] else []) (x # xx # xs))) \<union>\<^sub>p (evaluate [a] \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) (x # xx # xs)))) = evaluate [a] \<union>\<^sub>p ((evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (evaluate (concat (map (\<lambda>x. if f x then [x] else []) xs)) \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) xs))))\<close> \<open>evaluate [a] \<union>\<^sub>p ((evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (evaluate (concat (map (\<lambda>x. if f x then [x] else []) xs)) \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) xs)))) = (evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (evaluate [a] \<union>\<^sub>p (evaluate (concat (map (\<lambda>x. if f x then [x] else []) xs)) \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) xs))))\<close> by argo
  qed
qed

lemma eval_subprogram10: "(evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (evaluate [x. x \<leftarrow> (xs), f x] \<union>\<^sub>p evaluate [x. x \<leftarrow> xs, \<not>f x]) = (evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (evaluate xs)"
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

lemma eval_subprogram11: "size xs > 1 \<Longrightarrow> evaluate [x. x \<leftarrow> xs, f x] \<union>\<^sub>p evaluate [x. x \<leftarrow> xs, \<not>f x] = evaluate xs"
proof -
  assume "size xs > 1"
  then obtain x xx xs' where "xs=x#xx#xs'" apply auto
    by (metis length_0_conv length_Cons less_irrefl_nat less_nat_zero_code remdups_adj.cases)
  have "evaluate (x#xx#xs') = (evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p evaluate xs'"
    by (metis \<open>1 < length xs\<close> \<open>xs = x # xx # xs'\<close> choice_cnf_def cnf_choice2 cnf_choice3 concat_prop3 eval_subprogram6 list.distinct(1))
  have "evaluate [x. x \<leftarrow> (x#xx#xs'), f x] \<union>\<^sub>p evaluate [x. x \<leftarrow> x#xx#xs', \<not>f x] = (evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (evaluate [x. x \<leftarrow> (xs'), f x] \<union>\<^sub>p evaluate [x. x \<leftarrow> xs', \<not>f x])"
    using eval_subprogram9 by blast
  have "... = (evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (evaluate xs')"
    using eval_subprogram10 by blast
  have "evaluate [x. x \<leftarrow> (x#xx#xs'), f x] \<union>\<^sub>p evaluate [x. x \<leftarrow> x#xx#xs', \<not>f x] = evaluate (x#xx#xs')"
    using \<open>(evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (evaluate (concat (map (\<lambda>x. if f x then [x] else []) xs')) \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) xs'))) = (evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p evaluate xs'\<close> \<open>evaluate (concat (map (\<lambda>x. if f x then [x] else []) (x # xx # xs'))) \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) (x # xx # xs'))) = (evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p (evaluate (concat (map (\<lambda>x. if f x then [x] else []) xs')) \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) xs')))\<close> \<open>evaluate (x # xx # xs') = (evaluate [x] \<union>\<^sub>p evaluate [xx]) \<union>\<^sub>p evaluate xs'\<close> by presburger
  show "evaluate [x. x \<leftarrow> xs, f x] \<union>\<^sub>p evaluate [x. x \<leftarrow> xs, \<not>f x] = evaluate xs"
    using \<open>evaluate (concat (map (\<lambda>x. if f x then [x] else []) (x # xx # xs'))) \<union>\<^sub>p evaluate (concat (map (\<lambda>x. if \<not> f x then [x] else []) (x # xx # xs'))) = evaluate (x # xx # xs')\<close> \<open>xs = x # xx # xs'\<close> by blast
qed


theorem eval_subprogram12: "set xs \<subseteq> set ys \<Longrightarrow> evaluate xs \<preceq>\<^sub>p evaluate ys"
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
  have "evaluate ys' \<preceq>\<^sub>p evaluate ys" apply (simp add: o1) using eval_subprogram8[of "\<lambda>y. y \<in> set xs" ys] by auto
  have "set ys' \<union> set ys'' = set ys" using o1 o2 by auto
  have "set ys' = set xs" using o1 a1 by auto
  have "size ys' > 0" apply auto
    using \<open>set ys' = set xs\<close> a2 by auto
  have "evaluate ys' \<union>\<^sub>p evaluate ys'' = evaluate ys" apply (simp add: o1 o2) using eval_subprogram11[of ys "\<lambda>y. y \<in> set xs"] apply auto
    using \<open>1 < length ys\<close> by linarith
  show "evaluate xs \<preceq>\<^sub>p evaluate ys"
  proof (cases "size ys' = 1")
    case True
    have "card (set xs) = 1"
      by (metis True \<open>0 < length ys'\<close> \<open>set ys' = set xs\<close> le_numeral_extra(4) length_greater_0_conv rotate1_fixpoint_card rotate1_length01)
    then obtain x where "set xs = {x}" apply auto
      using \<open>card (set xs) = 1\<close> card_1_singletonE by blast
    have "evaluate xs = evaluate [x] \<union>\<^sub>p evaluate [x]"
      using \<open>1 < length xs\<close> \<open>set xs = {x}\<close> evaluate_prop2 by auto
    then show ?thesis
    proof (cases "set xs = set ys")
      case True
      then show ?thesis
        by (simp add: \<open>evaluate xs = evaluate [x] \<union>\<^sub>p evaluate [x]\<close> \<open>set xs = {x}\<close> choice_decomp_1 eval_subprogram4)
    next
      case False
      have "ys'' \<noteq> []"
        using False \<open>set ys' = set xs\<close> \<open>set ys' \<union> set ys'' = set ys\<close> by fastforce
      then show ?thesis
        by (metis \<open>evaluate xs = evaluate [x] \<union>\<^sub>p evaluate [x]\<close> \<open>set xs = {x}\<close> a1 choice_decomp_1 empty_set eval_subprogram4 list.simps(15))
    qed
  next
    case False
    have "size ys' > 1"
      using False \<open>0 < length ys'\<close> nat_neq_iff by auto
    have "equal_cnf xs ys'" apply (auto simp: equal_cnf_def)
      apply (auto simp add: \<open>set ys' = set xs\<close>)
      using \<open>1 < length xs\<close> apply auto
      using False by linarith
    have "evaluate xs = evaluate ys'"
      by (simp add: \<open>equal_cnf xs ys'\<close> equal_eval)

    then show ?thesis
      by (simp add: \<open>evaluate ys' \<preceq>\<^sub>p evaluate ys\<close>)
  qed
qed

definition p :: "nat CNF"
  where "p = [[\<lparr>State = {}, Pre = {}, post = {}\<rparr>]]"
definition q :: "nat CNF"
  where "q = [[]]"
definition r :: "nat CNF"
  where "r = [[\<lparr>State = {}, Pre = {}, post = {}\<rparr>]]"
value "(p \<parallel> q) ;\<^sub>c r"
value "p \<parallel> (q ;\<^sub>c r)"
theorem "set ((p \<parallel> q) ;\<^sub>c r) \<subseteq> set (p \<parallel> (q ;\<^sub>c r))"

end