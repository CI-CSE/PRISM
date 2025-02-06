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
    have "size (([x] \<parallel> [[]]) \<parallel> [z]) = 1"
      by (metis (no_types, opaque_lifting) Para_basic True \<open>length ([x] \<parallel> ([y] \<parallel> [z])) = 1\<close> \<open>length (concat (map ((\<interleave>) x) (y \<interleave> z))) = 1\<close> concat.simps(1) concat.simps(2) inter_size2 interleave.simps(1) length_0_conv list.map_disc_iff list.simps(9) self_append_conv size_one2)
    then show ?thesis
      by (simp add: True)
  next
    case False
    have "size (([x] \<parallel> [y]) \<parallel> [[]]) = 1"
      by (metis False Para_basic \<open>length ([x] \<parallel> ([y] \<parallel> [z])) = 1\<close> \<open>y = [] \<or> z = []\<close>)
    then show ?thesis
      using False \<open>y = [] \<or> z = []\<close> by auto
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

end