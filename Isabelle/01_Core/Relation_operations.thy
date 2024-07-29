theory Relation_operations
  imports Main
begin
section \<open>Relation operations\<close>

definition restrict_r :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" (infix "\<sslash>\<^sub>r" 150)
  where
    "restrict_r R S = {r \<in> R. fst r \<in> S}"

definition inv_restrict_r :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" (infix "\<sslash>\<^sub>-\<^sub>r" 150)
  where
    "inv_restrict_r R S = {r \<in> R. fst r \<notin> S}"

definition corestrict_r :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" (infix "\<setminus>\<^sub>r" 150)
  where
    "corestrict_r R S = {r \<in> R. snd r \<in> S}"

definition inv_corestrict_r :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" (infix "\<setminus>\<^sub>-\<^sub>r" 150)
  where
    "inv_corestrict_r R S = {r \<in> R. snd r \<notin> S}"

definition is_function :: "'a rel \<Rightarrow> bool"
  where
    "is_function R = (\<forall>r\<^sub>1 \<in> R.\<forall>r\<^sub>2\<in>R. fst r\<^sub>1 = fst r\<^sub>2 \<longrightarrow> snd r\<^sub>1 = snd r\<^sub>2)"

theorem corestriction_restriction_on_relcomp: "r\<^sub>1 \<setminus>\<^sub>r s\<^sub>1 O r\<^sub>2 = r\<^sub>1 O r\<^sub>2 \<sslash>\<^sub>r s\<^sub>1" \<comment> \<open>NEW\<close>
  by (auto simp: corestrict_r_def restrict_r_def)

theorem restrict_prop_1 [simp]: "r\<^sub>1 \<in> r \<Longrightarrow> fst r\<^sub>1 \<in> Domain r"
  by (simp add: Domain_fst)

theorem restrict_prop_2 [simp]: "r\<^sub>1 \<in> r \<Longrightarrow> fst r\<^sub>1 \<in> s \<Longrightarrow> fst r\<^sub>1 \<in> Domain (r \<sslash>\<^sub>r s)"
  by (simp add: restrict_r_def)

theorem restrict_prop_3 [simp]: "Domain r = Domain (r \<sslash>\<^sub>r s) \<union> Domain (r \<sslash>\<^sub>r (Field r - s))"
  apply (auto simp: restrict_r_def Field_def)
  using Domain.simps by fastforce

theorem restrict_prop_4 [simp]: "a \<sslash>\<^sub>r b \<union> a \<sslash>\<^sub>-\<^sub>r b = a"
  by (auto simp: restrict_r_def inv_restrict_r_def)

theorem corestrict_prop_1 [simp]: "r\<^sub>1 \<in> r \<Longrightarrow> snd r\<^sub>1 \<in> Range r"
  by (simp add: Range_snd)

theorem corestrict_prop_2 [simp]: "r\<^sub>1 \<in> r \<Longrightarrow> snd r\<^sub>1 \<in> s \<Longrightarrow> snd r\<^sub>1 \<in> Range (r \<setminus>\<^sub>r s)"
  by (simp add: corestrict_r_def)

theorem corestrict_prop_3 [simp]: "Domain r = Domain (r \<setminus>\<^sub>r s) \<union> Domain (r \<setminus>\<^sub>r (Field r - s))"
  apply (auto simp: corestrict_r_def Field_def)
  using Domain.simps by fastforce

theorem corestrict_prop_4 [simp]: "a \<setminus>\<^sub>r b \<union> a \<setminus>\<^sub>-\<^sub>r b = a"
  by (auto simp: corestrict_r_def inv_corestrict_r_def)

end
