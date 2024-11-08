theory Trace_top
  imports Main Trace_semantics
    Theory_of_programs
begin

definition program_from_trace_set :: "('a list) set \<Rightarrow> 'a Program"
  where
    "program_from_trace_set s \<equiv> \<lparr>State =state_of_trace_set s, Pre=pre_of_trace_set s, post=relation_from_traces s\<rparr>"

definition trace_set_from_program :: "'a Program \<Rightarrow> ('a list) set"
  where
    "trace_set_from_program p \<equiv> traces_from_relation (char_rel p)"

theorem top_tr_1: "p \<equiv>\<^sub>p q \<Longrightarrow> traces_from_relation (char_rel p) = traces_from_relation (char_rel q)"
  by (auto simp: traces_from_relation_def char_rel_def restrict_r_def equiv_def restr_post_def)

theorem top_tr_2: "all_feasible [p, q] \<Longrightarrow> \<not>p \<equiv>\<^sub>p q \<Longrightarrow> char_rel p \<noteq> char_rel q"
  by (simp add: equiv_charrel2)

theorem top_tr_3: "p = q \<Longrightarrow> traces_from_relation (p) = traces_from_relation (q)"
  by simp

lemma top_tr_4: "(traces_from_relation (p) = {}) = (p = {})"
  by (auto simp: traces_from_relation_def)


definition equiv_rel_trace :: "'a rel \<Rightarrow> ('a list) set \<Rightarrow> bool"
  where
    "equiv_rel_trace R S' \<equiv> (\<forall>r \<in> R. \<exists> s \<in> S'. fst r = hd s \<and> snd r = hd (tl s)) \<and> (\<forall>s \<in> S'. \<exists> r \<in> R. fst r = hd s \<and> snd r = hd (tl s))"

theorem equiv_tm_1: "equiv_rel_trace r (traces_from_relation r)"
  apply (auto simp: equiv_rel_trace_def traces_from_relation_def)
  apply fastforce
  by (meson fst_conv snd_conv)

theorem top_tr_5: "traces_from_relation (p) \<noteq> traces_from_relation (q) \<Longrightarrow> p \<noteq> q"
  apply (simp add: traces_from_relation_def)
  by auto

theorem top_tr_6: "p \<noteq> q \<Longrightarrow> traces_from_relation (p) \<noteq> traces_from_relation (q)"
  apply (simp add: traces_from_relation_def)
proof -
  assume a1: "p \<noteq> q"
  from a1 have l1: "(\<exists>r \<in> p. r \<notin> q) \<or> (\<exists>r \<in> q. r \<notin> p)" by (auto)
  show "{[x, y] |x y. (x, y) \<in> p} \<noteq> {[x, y] |x y. (x, y) \<in> q}"
  proof (cases "(\<exists>r \<in> p. r \<notin> q)")
    case True
    obtain r where o1: "r\<in>p \<and> r \<notin> q"
      by (meson True)
    have l1: "[fst r, snd r] \<in> {[x, y] |x y. (x, y) \<in> p}"
      by (simp add: o1)
    have l2: "[fst r, snd r] \<notin> {[x, y] |x y. (x, y) \<in> q}"
      by (simp add: o1)
    then show ?thesis
      by (metis l1)
  next
    case False
    then have l1: "(\<exists>r \<in> q. r \<notin> p)" using l1 by auto
    obtain r where o1: "r \<in> q \<and> r \<notin> p"
      by (meson l1)
    have l1: "[fst r, snd r] \<notin> {[x, y] |x y. (x, y) \<in> p}"
      by (simp add: o1)
    have l2: "[fst r, snd r] \<in> {[x, y] |x y. (x, y) \<in> q}"
      by (simp add: o1)
    then show ?thesis
      using l1 by blast
  qed
qed

theorem top_tr_7: "traces_from_relation (p) = traces_from_relation (q) \<equiv> p = q"
  by (smt (verit, best) top_tr_6)
  
theorem top_tr_8: "p \<equiv>\<^sub>p q \<Longrightarrow> trace_set_from_program p = trace_set_from_program q"
  by (simp add: top_tr_1 trace_set_from_program_def)

theorem top_tr_9: "all_feasible [p, q] \<Longrightarrow> trace_set_from_program p = trace_set_from_program q \<Longrightarrow> p \<equiv>\<^sub>p q"
  by (metis top_tr_2 top_tr_6 trace_set_from_program_def)

theorem top_tr_10: "is_feasible p \<Longrightarrow> program_from_trace_set (trace_set_from_program p) \<equiv>\<^sub>p p"
  apply (auto simp: program_from_trace_set_def trace_set_from_program_def state_of_trace_set_def all_elements_from_trace_def traces_from_relation_def char_rel_def restrict_r_def equiv_def pre_of_trace_set_def is_feasible_def subset_iff Domain_iff restr_post_def relation_from_traces_def)
  apply (metis list.distinct(1) list.sel(1))
  apply (metis last.simps list.distinct(1) list.sel(1))
  by (metis list.distinct(1) list.sel(1))

theorem top_tr_11: "relation_from_traces (traces_from_relation p) = p"
  apply (auto simp: relation_from_traces_def traces_from_relation_def)
  by force

theorem top_tr_12: "trace_set_from_program (program_from_trace_set p) \<equiv>\<^sub>T p"
  apply (auto simp: trace_set_from_program_def program_from_trace_set_def equiv_t_def traces_from_relation_def relation_from_traces_def pre_of_trace_set_def state_of_trace_set_def all_elements_from_trace_def char_rel_def restrict_r_def)
  apply metis
  by (metis last.simps list.distinct(1) list.sel(1))

theorem eq_of_choice_1: "trace_set_from_program (a \<union>\<^sub>p b) \<equiv>\<^sub>T trace_set_from_program a \<union> trace_set_from_program b"
  by (auto simp: equiv_t_def choice_def trace_set_from_program_def relation_from_traces_def traces_from_relation_def char_rel_def restr_post_def restrict_r_def)

theorem eq_of_choice_2: "program_from_trace_set (a \<union> b) \<equiv>\<^sub>p program_from_trace_set a \<union>\<^sub>p program_from_trace_set b"
  by (auto simp: equiv_def choice_def program_from_trace_set_def pre_of_trace_set_def restr_post_def relation_from_traces_def restrict_r_def)

theorem top_tr_13: "(x,y) \<in> char_rel p \<equiv> [x,y] \<in> trace_set_from_program p"
  by (auto simp: char_rel_def trace_set_from_program_def restrict_r_def traces_from_relation_def)

theorem top_tr_14: "x \<in> trace_set_from_program a \<Longrightarrow> length x = 2"
  by (auto simp: trace_set_from_program_def traces_from_relation_def)

theorem top_tr_15: "x \<in> trace_set_from_program a ;\<^sub>T trace_set_from_program b \<Longrightarrow> length x = 3"
  by (auto simp: trace_set_from_program_def traces_from_relation_def CONCAT_def)

definition same_length :: "('a list) set \<Rightarrow> bool"
  where
    "same_length A \<equiv> \<forall>x \<in> A. \<forall> y \<in> A. length x = length y"

theorem top_tr_16: "same_length (trace_set_from_program a)" 
  by (auto simp: same_length_def trace_set_from_program_def traces_from_relation_def)

theorem top_tr_17: "same_length A \<Longrightarrow> same_length B \<Longrightarrow> same_length (A ;\<^sub>T B)"
  apply (auto simp: same_length_def CONCAT_def last_first_eq_def)
  by (smt (verit) concatt.elims last_first_eq_def length_append length_tl list.sel(3))

theorem top_tr_18:
  assumes "same_length A" and "same_length B" and "a \<in> A" and "b \<in> B" and "c \<in> (A ;\<^sub>T B)" 
  shows "Suc (length c) = length a + length b"
proof (cases "[] \<in> A")
  case True
  have l1: "length a = 0" using True assms(1) apply (auto simp: same_length_def) using assms(3) by auto
  have l2: "c \<in> {concatt x y | x y . x \<in> A \<and> y \<in> B \<and> last_first_eq x y}" using CONCAT_def assms(5) by blast
  obtain x y where l3: "concatt x y = c" using l2 by auto
  have "False" using CONCAT_def True assms(1) assms(5) concat_eq2_def length_0_conv mem_Collect_eq same_length_def simps_17
    by (smt (verit))
  then show ?thesis by simp
next
  case False
  assume a1: "[] \<notin> A"
  have l2: "c \<in> {concatt x y | x y . x \<in> A \<and> y \<in> B \<and> last_first_eq x y}" using CONCAT_def assms(5) by blast
  then show ?thesis
  proof (cases "[] \<in> B")
    case True
  have l1: "length b = 0" using True assms(2) apply (auto simp: same_length_def) using assms(4) by auto
  obtain x y where l3: "concatt x y = c" using l2 by auto
  have "False" using CONCAT_def True assms(1) assms(5) concat_eq2_def length_0_conv mem_Collect_eq same_length_def simps_17
    by (smt (verit, del_insts) assms(2) simps_23)
    then show ?thesis by simp
  next
    case False
    assume a2: "[] \<notin> B"
    obtain x y where l3: "concatt x y = c \<and> x \<in> A \<and> y \<in> B \<and> last_first_eq x y" using l2 concatt.simps(1) by blast
    have l4: "length (concatt x y) > 0"
      using assms(5) l3 simps_42 by fastforce
    show ?thesis
      by (metis assms(1) assms(2) assms(3) assms(4) l3 same_length_def simps_43)
  qed
qed


theorem top_tr_19: "[x, mid, y] \<in> trace_set_from_program a ;\<^sub>T trace_set_from_program b \<Longrightarrow> [x, mid] \<in> trace_set_from_program a"
  by (auto simp: CONCAT_def trace_set_from_program_def traces_from_relation_def char_rel_def)

theorem top_tr_20: "[x, mid, y] \<in> trace_set_from_program a ;\<^sub>T trace_set_from_program b \<Longrightarrow> [mid, y] \<in> trace_set_from_program b"
  by (auto simp: CONCAT_def trace_set_from_program_def traces_from_relation_def char_rel_def restrict_r_def last_first_eq_def)

theorem top_tr_21: "x \<in> Pre (a ; b) \<Longrightarrow> (x, y) \<in> post (a ; b) \<Longrightarrow> [x, y] \<in> trace_set_from_program (a ; b)"
  by (auto simp: trace_set_from_program_def composition_def restr_post_def restrict_r_def corestrict_r_def traces_from_relation_def char_rel_def)

theorem top_tr_22: "(x,y) \<in> post (program_from_trace_set a) \<Longrightarrow> x \<in>  Pre (program_from_trace_set a)"
  by (auto simp: program_from_trace_set_def relation_from_traces_def pre_of_trace_set_def)

theorem top_tr_23: "x \<in>  Pre (program_from_trace_set a) \<Longrightarrow> \<exists>y. (x,y) \<in> post (program_from_trace_set a)"
  by (auto simp: program_from_trace_set_def pre_of_trace_set_def relation_from_traces_def)

theorem top_tr_24: "(x,z) \<in> post (program_from_trace_set a) \<Longrightarrow> \<exists>t \<in> a. hd t = x \<and> last t = z"
  by (auto simp: program_from_trace_set_def relation_from_traces_def)

definition undef :: "'a" where "undef = hd []"

theorem eq_of_composition_1: "trace_set_from_program (a ; b) \<equiv>\<^sub>T trace_set_from_program a ;\<^sub>T trace_set_from_program b"
  apply (auto simp: equiv_t_def)
proof -
  fix x y assume a1: "(x, y) \<in> relation_from_traces (trace_set_from_program (a ; b))"
  have l1: "(x,y) \<in> char_rel (a ; b)"
    by (metis a1 top_tr_11 trace_set_from_program_def)
  obtain z where l2: "(x,z) \<in> char_rel a \<and> (z,y) \<in> char_rel b"
    by (metis char_rel_composition l1 relcomp.cases)
  obtain ab where l3: "ab = trace_set_from_program a ;\<^sub>T trace_set_from_program b" by simp
  have l4: "[x,z,y] \<in> ab" using simps_39 l3
    by (metis l2 top_tr_13)
  from l4 have l5: "(x,y) \<in> relation_from_traces ab"
    by (metis concatt.simps(3) list.distinct(1) simps_26 simps_40)
  show "(x, y) \<in> relation_from_traces (trace_set_from_program a ;\<^sub>T trace_set_from_program b)"
    using l3 l5 by auto
  next
  fix x y assume a1: "(x, y) \<in> relation_from_traces (trace_set_from_program a ;\<^sub>T trace_set_from_program b)"
  show "(x, y) \<in> relation_from_traces (trace_set_from_program (a ; b))"
  proof (cases "\<exists>mid. [x] @ mid @ [y] \<in> trace_set_from_program a ;\<^sub>T trace_set_from_program b")
    case True
    then obtain mid where l1: "[x] @ mid @ [y] \<in> trace_set_from_program a ;\<^sub>T trace_set_from_program b" by auto
    have l2: "length mid = 1" using top_tr_15 l1 by fastforce
    obtain mid' where l3: "mid = [mid']" by (metis Suc_diff_1 gr0I l2 length_0_conv length_Suc_conv less_numeral_extra(1) less_numeral_extra(4) zero_less_diff)
    have l4: "[x, mid', y] \<in> trace_set_from_program a ;\<^sub>T trace_set_from_program b" using l1 l3 by auto
    have l5: "\<forall>x \<in> trace_set_from_program a. length x = 2" by (simp add: top_tr_14)
    have l6: "[x, mid'] \<in> (trace_set_from_program a)" using l3 l1 by (metis l4 top_tr_19)
    have l7: "[mid', y] \<in> (trace_set_from_program b)" by (meson l4 top_tr_20)
    have l8: "x \<in> Pre a" using l6 by (auto simp: trace_set_from_program_def traces_from_relation_def char_rel_def restrict_r_def)
    have l9: "(x, mid') \<in> (post a)" using l6 by (auto simp: trace_set_from_program_def traces_from_relation_def char_rel_def restrict_r_def)
    have l10: "mid' \<in> Pre b" using l7 by (auto simp: trace_set_from_program_def traces_from_relation_def char_rel_def restrict_r_def)
    have l11: "(mid', y) \<in> (post b)" using l7 by (auto simp: trace_set_from_program_def traces_from_relation_def char_rel_def restrict_r_def)
    have l12: "x \<in> Pre (a;b)" using l8 l9 l10 l11 by (auto simp: composition_def corestrict_r_def)
    have l13: "(x,y) \<in> post (a;b)" using l8 l9 l10 l11 by (auto simp: composition_def corestrict_r_def restr_post_def restrict_r_def)
    have l14: "[x, y] \<in> trace_set_from_program (a ; b)" using l12 l13
      by (simp add: top_tr_21)
    then show ?thesis
      by (simp add: top_tr_11 top_tr_13 trace_set_from_program_def) 
  next
    case False
    obtain ab where l1: "ab = trace_set_from_program a ;\<^sub>T trace_set_from_program b" by simp
    have l2: "\<forall>x \<in> ab. length x = 3"
      by (simp add: top_tr_15 l1)
    from False l1 a1 have l2: "ab = {}" apply (auto simp: trace_set_from_program_def traces_from_relation_def char_rel_def restrict_r_def relation_from_traces_def CONCAT_def last_first_eq_def)
      by (smt (verit) False a1 distinct_adj_Cons_Cons distinct_adj_Nil l1 list.inject mem_Collect_eq simps_10 simps_41)
    then show ?thesis
      using a1 l1 simps_41 by fastforce
  qed
qed

lemma eq_of_composition_2_pre: "Pre (program_from_trace_set (a ;\<^sub>T b)) = Pre (program_from_trace_set a ; program_from_trace_set b)"
  apply (cases "a = {}")
  apply (auto simp: program_from_trace_set_def composition_def CONCAT_def pre_of_trace_set_def last_first_eq_def relation_from_traces_def corestrict_r_def Domain_iff restr_post_def restrict_r_def relcomp_unfold equiv_def) [1]
  apply (cases "b = {}")
   apply (auto simp: program_from_trace_set_def composition_def CONCAT_def pre_of_trace_set_def last_first_eq_def relation_from_traces_def corestrict_r_def Domain_iff restr_post_def restrict_r_def relcomp_unfold equiv_def) [1]
  apply (auto simp: equiv_def)
  apply (auto simp: program_from_trace_set_def composition_def CONCAT_def pre_of_trace_set_def last_first_eq_def relation_from_traces_def corestrict_r_def Domain_iff restr_post_def restrict_r_def relcomp_unfold equiv_def) [1]
  apply (smt (verit) append_is_Nil_conv concatt.elims hd_concatt list.sel(1) simps_11 simps_27 simps_35)
     apply (metis concat_eq2_def hd_concatt last.simps last_append list.collapse neq_Nil_conv rev_exhaust simps_28 last.simps)
proof -
  fix x 
  obtain ap where l1: "ap = program_from_trace_set a" by simp
  obtain bp where l2: "bp = program_from_trace_set b" by simp
  assume a3: "x \<in> Pre (program_from_trace_set a ; program_from_trace_set b)"
  have l3: "x \<in> Pre (ap)"
    by (metis a3 composition_pre in_mono l1)
  obtain x_tr where l4: "x_tr \<in> a \<and> hd x_tr = x" using a3 l3 l1 by (auto simp: program_from_trace_set_def composition_def pre_of_trace_set_def)
  have l5: "\<exists>ab_tr \<in> a ;\<^sub>T b. hd ab_tr = x" using a3 l1 l3 apply (auto simp: program_from_trace_set_def composition_def corestrict_r_def relation_from_traces_def pre_of_trace_set_def state_of_trace_set_def all_elements_from_trace_def CONCAT_def last_first_eq_def) sorry
  obtain ab_tr where l6: "ab_tr \<in> a ;\<^sub>T b \<and> hd ab_tr = x" using l5 by auto
  have l7: "(hd ab_tr, last ab_tr) \<in> post (program_from_trace_set (a ;\<^sub>T b))" using l6 apply (auto simp: CONCAT_def program_from_trace_set_def relation_from_traces_def last_first_eq_def)
    by (metis l6 simps_42)
  have l8: "hd ab_tr \<in> Pre (program_from_trace_set (a ;\<^sub>T b))" using l6 apply (auto simp: CONCAT_def program_from_trace_set_def relation_from_traces_def last_first_eq_def pre_of_trace_set_def)
    by (metis l6 simps_42)
  show "x \<in> Pre (program_from_trace_set (a ;\<^sub>T b))"
    using l6 l8 by blast
qed

lemma eq_of_composition_2_post_1: "post (program_from_trace_set (a ;\<^sub>T b)) \<subseteq> post (program_from_trace_set a ; program_from_trace_set b)"
    apply (auto simp: restr_post_def program_from_trace_set_def composition_def CONCAT_def restrict_r_def corestrict_r_def relation_from_traces_def pre_of_trace_set_def last_first_eq_def relcomp_unfold Domain_iff)
  by (smt (verit) concatt.elims hd_concatt last_concatt)

lemma eq_of_composition_2_post_2: "[] \<notin> a \<Longrightarrow> [] \<notin> b \<Longrightarrow> post (program_from_trace_set a ; program_from_trace_set b) \<subseteq> post (program_from_trace_set (a ;\<^sub>T b))"
  apply (auto)
proof -
    fix x y
    assume a1: "[] \<notin> a"
    assume a2: "[] \<notin> b"
    assume a3: "(x, y) \<in> post (program_from_trace_set a ; program_from_trace_set b)"
    have l1: "restr_post (program_from_trace_set a ; program_from_trace_set b) = post (program_from_trace_set a ; program_from_trace_set b)"
      apply (auto simp: restr_post_def program_from_trace_set_def composition_def CONCAT_def restrict_r_def corestrict_r_def relation_from_traces_def pre_of_trace_set_def last_first_eq_def relcomp_unfold Domain_iff)
      by auto
    have l2: "restr_post (program_from_trace_set (a ;\<^sub>T b)) = post (program_from_trace_set (a ;\<^sub>T b))"
      apply (auto simp: restr_post_def program_from_trace_set_def composition_def CONCAT_def restrict_r_def corestrict_r_def relation_from_traces_def pre_of_trace_set_def last_first_eq_def relcomp_unfold Domain_iff)
      by auto
    have l3: "(x, y) \<in> post (program_from_trace_set a ; program_from_trace_set b)" using a3 l1 by auto
    obtain z where l4: "(x,z) \<in> post (program_from_trace_set a) \<and> (z,y) \<in> post (program_from_trace_set b)" by (meson connecting_element l3)
    obtain t_a where l5: "t_a \<in> a \<and> hd t_a = x \<and> last t_a = z" using top_tr_24 l4 by fastforce
    obtain t_b where l6: "t_b \<in> b \<and> hd t_b = z \<and> last t_b = y" using top_tr_24 l4 by fastforce
    have l6_1: "last t_a = hd t_b" by (simp add: l5 l6)
    have l6_2: "t_a \<noteq> []" using a1 l5 by auto
    have l6_3: "t_b \<noteq> []" using a2 l6 by auto
    have l7: "last_first_eq t_a t_b" by (simp add: l6_1 l6_2 l6_3 last_first_eq_def)
    have l8: "concatt t_a t_b \<in> {concatt x y | x y . x \<in> a \<and> y \<in> b \<and> last_first_eq x y  \<and> x \<noteq> [] \<and> y \<noteq> []}" using l5 l6 l7
      by (smt (verit, ccfv_SIG) last_first_eq_def length_greater_0_conv mem_Collect_eq)
    have l9: "concatt t_a t_b \<in> a ;\<^sub>T b" using CONCAT_def l8 by blast
    have l10: "(x, y) \<in> relation_from_traces (a ;\<^sub>T b)" using l8 l9 l5 l6
      by (smt (verit) hd_concatt l7 last_concatt mem_Collect_eq relation_from_traces_def simps_42)
    have l11: "(x, y) \<in> post (program_from_trace_set (a ;\<^sub>T b))" using l10 by (auto simp: program_from_trace_set_def)
    show"(x, y) \<in> post (program_from_trace_set (a ;\<^sub>T b))" using l11 l2 by auto
  qed


theorem eq_of_composition_2: "[] \<notin> a \<Longrightarrow> [] \<notin> b \<Longrightarrow> program_from_trace_set (a ;\<^sub>T b) \<equiv>\<^sub>p program_from_trace_set a ; program_from_trace_set b"
  apply (auto simp: equiv_def)
  using eq_of_composition_2_pre apply force
  apply (simp add: eq_of_composition_2_pre)
  apply (cases "a = {}")
  apply (auto simp: program_from_trace_set_def composition_def CONCAT_def pre_of_trace_set_def last_first_eq_def relation_from_traces_def corestrict_r_def Domain_iff restr_post_def restrict_r_def relcomp_unfold equiv_def) [1]
  apply (cases "b = {}")
   apply (auto simp: program_from_trace_set_def composition_def CONCAT_def pre_of_trace_set_def last_first_eq_def relation_from_traces_def corestrict_r_def Domain_iff restr_post_def restrict_r_def relcomp_unfold equiv_def) [1]
proof -
  assume a1: "[] \<notin> a"
  assume a2: "[] \<notin> b"
  fix x y assume a3: "(x, y) \<in> restr_post (program_from_trace_set (a ;\<^sub>T b))"
  assume a4: "a \<noteq> {}"
  assume a5: "b \<noteq> {}"
  show "(x, y) \<in> restr_post (program_from_trace_set a ; program_from_trace_set b)"
    using a3 apply (auto simp: restr_post_def program_from_trace_set_def composition_def CONCAT_def restrict_r_def corestrict_r_def relation_from_traces_def pre_of_trace_set_def last_first_eq_def relcomp_unfold Domain_iff)
    apply (smt (verit) concatt.elims hd_concatt last_concatt)
    apply (smt (verit) concatt.elims hd_concatt)
    by (smt (verit) concatt.elims hd_concatt)
  next
    fix x y
    assume a1: "[] \<notin> a"
    assume a2: "[] \<notin> b"
    assume a3: "(x, y) \<in> restr_post (program_from_trace_set a ; program_from_trace_set b)"
    have l1: "restr_post (program_from_trace_set a ; program_from_trace_set b) = post (program_from_trace_set a ; program_from_trace_set b)"
      apply (auto simp: restr_post_def program_from_trace_set_def composition_def CONCAT_def restrict_r_def corestrict_r_def relation_from_traces_def pre_of_trace_set_def last_first_eq_def relcomp_unfold Domain_iff)
      by auto
    have l2: "restr_post (program_from_trace_set (a ;\<^sub>T b)) = post (program_from_trace_set (a ;\<^sub>T b))"
      apply (auto simp: restr_post_def program_from_trace_set_def composition_def CONCAT_def restrict_r_def corestrict_r_def relation_from_traces_def pre_of_trace_set_def last_first_eq_def relcomp_unfold Domain_iff)
      by auto
    have l3: "(x, y) \<in> post (program_from_trace_set a ; program_from_trace_set b)" using a3 l1 by auto
    obtain z where l4: "(x,z) \<in> post (program_from_trace_set a) \<and> (z,y) \<in> post (program_from_trace_set b)" by (meson connecting_element l3)
    obtain t_a where l5: "t_a \<in> a \<and> hd t_a = x \<and> last t_a = z" using top_tr_24 l4 by fastforce
    obtain t_b where l6: "t_b \<in> b \<and> hd t_b = z \<and> last t_b = y" using top_tr_24 l4 by fastforce
    have l6_1: "last t_a = hd t_b" by (simp add: l5 l6)
    have l6_2: "t_a \<noteq> []" using a1 l5 by auto
    have l6_3: "t_b \<noteq> []" using a2 l6 by auto
    have l7: "last_first_eq t_a t_b" by (simp add: l6_1 l6_2 l6_3 last_first_eq_def)
    have l8: "concatt t_a t_b \<in> {concatt x y | x y . x \<in> a \<and> y \<in> b \<and> last_first_eq x y  \<and> x \<noteq> [] \<and> y \<noteq> []}" using l5 l6 l7
      by (smt (verit, ccfv_SIG) last_first_eq_def length_greater_0_conv mem_Collect_eq)
    have l9: "concatt t_a t_b \<in> a ;\<^sub>T b" using CONCAT_def l8 by blast
    have l10: "(x, y) \<in> relation_from_traces (a ;\<^sub>T b)" using l8 l9 l5 l6
      by (smt (verit) hd_concatt l7 last_concatt mem_Collect_eq relation_from_traces_def simps_42)
    have l11: "(x, y) \<in> post (program_from_trace_set (a ;\<^sub>T b))" using l10 by (auto simp: program_from_trace_set_def)
    show"(x, y) \<in> restr_post (program_from_trace_set (a ;\<^sub>T b))" using l11 l2 by auto
  qed

definition predicate_to_set :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set" where
  "predicate_to_set C \<equiv> {x. C x}"

definition set_to_predicate :: "'a set \<Rightarrow> ('a \<Rightarrow> bool)" where
  "set_to_predicate C \<equiv> \<lambda>x. x \<in> C"

theorem eq_of_restriction_1: "trace_set_from_program (a \<sslash>\<^sub>p C) \<equiv>\<^sub>T set_to_predicate C \<sslash> trace_set_from_program a"
  by (auto simp: trace_set_from_program_def equiv_t_def relation_from_traces_def traces_from_relation_def char_rel_def restrict_p_def restrict_r_def set_to_predicate_def restrict_def)

theorem eq_of_restriction_2: "program_from_trace_set (C \<sslash> a) \<equiv>\<^sub>p program_from_trace_set a \<sslash>\<^sub>p predicate_to_set C"
  by (auto simp: trace_set_from_program_def equiv_def program_from_trace_set_def restrict_def pre_of_trace_set_def predicate_to_set_def restrict_p_def relation_from_traces_def restr_post_def restrict_r_def)

theorem eq_of_corestriction_1: "trace_set_from_program (a \<setminus>\<^sub>p C) \<equiv>\<^sub>T trace_set_from_program a \<setminus> set_to_predicate C"
  apply (auto simp: trace_set_from_program_def equiv_t_def relation_from_traces_def traces_from_relation_def char_rel_def corestrict_p_def corestrict_r_def restrict_r_def set_to_predicate_def corestrict_def Domain_iff)
  by (metis last.simps list.distinct(1) list.sel(1))

theorem eq_of_corestriction_2: "program_from_trace_set (a \<setminus> C) \<equiv>\<^sub>p (program_from_trace_set a) \<setminus>\<^sub>p (predicate_to_set C)"
  by (auto simp: trace_set_from_program_def equiv_def program_from_trace_set_def corestrict_def pre_of_trace_set_def predicate_to_set_def corestrict_p_def relation_from_traces_def restr_post_def corestrict_r_def restrict_r_def)

end