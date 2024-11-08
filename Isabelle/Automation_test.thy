theory Automation_test
  imports Main
begin

record 'a Program =
  State :: "'a set"
  Pre :: "'a set"
  post :: "'a rel"

definition restrict_r :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" (infix "\<sslash>\<^sub>r" 150)
  where
    "restrict_r R S = {r \<in> R. fst r \<in> S}"

definition corestrict_r :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" (infix "\<setminus>\<^sub>r" 150)
  where
    "corestrict_r R S = {r \<in> R. snd r \<in> S}"

definition S :: "'a Program \<Rightarrow> 'a set"
  where
    "S p = State p \<union> Pre p \<union> Field (post p)"

definition is_feasible :: "'a Program \<Rightarrow> bool"
  where
    "is_feasible p = (Pre p \<subseteq> Domain (post p))"

primrec all_feasible :: "('a Program) list \<Rightarrow> bool"
  where
    "all_feasible [] = True" |
    "all_feasible (x # xs) = (all_feasible xs \<and> is_feasible x)"

definition is_valid :: "'a Program \<Rightarrow> bool"
  where
    "is_valid p \<equiv> S p = State p"

primrec all_valid :: "('a Program) list \<Rightarrow> bool"
  where
    "all_valid [] = True" |
    "all_valid (x#xs) = (all_valid xs \<and> is_valid x)"

definition is_total :: "'a Program \<Rightarrow> bool"
  where
    "is_total p = (Pre p = S p)"

definition restr_post :: "'a Program \<Rightarrow> 'a  rel"
  where
    "restr_post p = post p \<sslash>\<^sub>r Pre p"

definition equal :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" (infix "\<triangleq>" 48)
  where
    "p\<^sub>1 \<triangleq> p\<^sub>2 \<equiv> (Pre p\<^sub>1 = Pre p\<^sub>2 \<and> post p\<^sub>1 = post p\<^sub>2 \<and> S p\<^sub>1 = S p\<^sub>2)"

definition equiv :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" (infix "\<equiv>\<^sub>p" 49)
  where
    "p\<^sub>1 \<equiv>\<^sub>p p\<^sub>2 \<equiv> (Pre p\<^sub>1 = Pre p\<^sub>2 \<and> restr_post p\<^sub>1 = restr_post p\<^sub>2)"

definition Range_p :: "'a Program \<Rightarrow> 'a set"
  where
    "Range_p p = Range (post p \<sslash>\<^sub>r Pre p)"

definition inverse :: "'a Program \<Rightarrow> 'a Program"
  where
    "inverse p \<equiv> \<lparr>State=S p, Pre=Range_p p, post=(restr_post p)\<inverse>\<rparr>"

notation inverse ("_\<^sup>-\<^sup>1" [50] 50)

definition extends :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool"
  where
    "extends p\<^sub>2 p\<^sub>1 = (S p\<^sub>1 \<subseteq> S p\<^sub>2)"

definition weakens :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool"
  where
    "weakens p\<^sub>2 p\<^sub>1 = (Pre p\<^sub>1 \<subseteq> Pre p\<^sub>2)"

definition strengthens :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" \<comment> \<open>NEW DEFINITION\<close>
  where
    "strengthens p\<^sub>2 p\<^sub>1 \<equiv> ((post p\<^sub>2) \<sslash>\<^sub>r Pre p\<^sub>2) \<sslash>\<^sub>r (Pre p\<^sub>1) \<subseteq> post p\<^sub>1"
  
definition refines :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" (infix "\<subseteq>\<^sub>p" 50) \<comment> \<open>D7\<close>
  where
    "p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>1 = (extends p\<^sub>2 p\<^sub>1 \<and> weakens p\<^sub>2 p\<^sub>1 \<and> strengthens p\<^sub>2 p\<^sub>1)"

definition subprogram :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool" (infix "\<preceq>\<^sub>p" 50)
  where
    "p\<^sub>1 \<preceq>\<^sub>p p\<^sub>2 \<equiv> extends p\<^sub>2 p\<^sub>1 \<and> weakens p\<^sub>2 p\<^sub>1 \<and> strengthens p\<^sub>1 p\<^sub>2"

definition implements :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> bool"
  where
    "implements p\<^sub>2 p\<^sub>1 = (p\<^sub>2 \<subseteq>\<^sub>p p\<^sub>1 \<and> is_feasible p\<^sub>2)"

definition choice :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix "\<union>\<^sub>p" 151)
  where
    "p\<^sub>1 \<union>\<^sub>p p\<^sub>2 = \<lparr>State= S p\<^sub>1 \<union> S p\<^sub>2, Pre = Pre p\<^sub>1 \<union> Pre p\<^sub>2, post = restr_post p\<^sub>1 \<union> restr_post p\<^sub>2\<rparr>"

definition composition :: "'a Program \<Rightarrow> 'a Program \<Rightarrow> 'a Program" (infix ";" 152)
  where
    "p\<^sub>1 ; p\<^sub>2 = \<lparr>
      State = S p\<^sub>1 \<union> S p\<^sub>2,
      Pre = Pre p\<^sub>1 \<inter> Domain (post p\<^sub>1 \<setminus>\<^sub>r Pre p\<^sub>2),
      post = (post p\<^sub>1) O (restr_post p\<^sub>2)\<rparr>"

definition restrict_p :: "'a Program \<Rightarrow> 'a set \<Rightarrow> 'a Program" (infix "\<sslash>\<^sub>p" 153)
  where
    "restrict_p p C = \<lparr>State= S p, Pre=Pre p \<inter> C, post=post p\<rparr>"

definition corestrict_p :: "'a Program \<Rightarrow> 'a set \<Rightarrow> 'a Program" (infix "\<setminus>\<^sub>p" 154)
  where
    "corestrict_p p C = \<lparr>State= S p, 
        Pre=Pre p \<inter> Domain (post p \<setminus>\<^sub>r C),
        post=post p \<setminus>\<^sub>r C\<rparr>"

definition Fail :: "'a set \<Rightarrow> 'a Program"
  where
    "Fail s = \<lparr> State = s, Pre = {}, post = {}\<rparr>"

definition Havoc :: "'a set \<Rightarrow> 'a Program"
  where
    "Havoc s = \<lparr> State = s, Pre = s, post = {(x,y). x \<in> s \<and> y \<in> s}\<rparr>"

definition Skip :: "'a set \<Rightarrow> 'a Program"
  where
    "Skip s = \<lparr> State = s, Pre = s, post = {(x,y). x \<in> s \<and> x = y} \<rparr>"

theorem "Range_p (p \<sslash>\<^sub>p a) \<subseteq> Range_p p"
  apply (simp add: Range_p_def restrict_p_def restrict_r_def)
  sledgehammer [provers = cvc4 verit vampire, timeout=15]
  done
end