theory Probability_Theory 
  imports "HOL-Probability.Probability"
begin

section "Basics from Measure Theory"

subsection "Sets"

definition disjoint :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "disjoint A B \<equiv> \<not>(\<exists>x. x\<in>A \<and> x\<in>B)"

lemma disj_iff_empty_inter: "(disjoint A B) = (A \<inter> B = {})"
  by (simp add: disjoint_def disjoint_iff)

definition power_set :: "'a set \<Rightarrow> ('a set) set"
  where "power_set A = {S. S \<subseteq> A}"

definition non_decreasing :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool"
  where "non_decreasing A\<^sub>n \<equiv> \<forall>n. A\<^sub>n n \<subseteq> A\<^sub>n (n + 1)"

definition non_increasing :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool"
  where "non_increasing A\<^sub>n \<equiv> \<forall>n. A\<^sub>n (n + 1) \<subseteq> A\<^sub>n n"

definition countable_union :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
  where "countable_union A\<^sub>n = {x. \<exists>n. x \<in> A\<^sub>n n}"

definition countable_union_sub :: "nat set \<Rightarrow> (nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
  where "countable_union_sub I A\<^sub>n = {x. \<exists>n\<in>I. x \<in> A\<^sub>n n}"

lemma countable_union_UNIV: "countable_union_sub UNIV A\<^sub>n = countable_union A\<^sub>n"
proof - 
  have "countable_union A\<^sub>n = {x. \<exists>n. x \<in> A\<^sub>n n}"
    using countable_union_def by metis 
  hence "countable_union A\<^sub>n = {x. \<exists>n\<in>UNIV. x \<in> A\<^sub>n n}"
    by auto 
  thus ?thesis 
    using countable_union_sub_def by metis 
qed 

lemma countable_union_empty: "countable_union_sub {} A\<^sub>n = {}"
proof - 
  have "\<not>(\<exists>x. x \<in> {y. \<exists>n\<in>{}. y \<in> A\<^sub>n n})"
    by simp
  hence "\<not>(\<exists>x. x \<in> countable_union_sub {} A\<^sub>n)"
    using countable_union_sub_def by metis 
  thus ?thesis
    by simp 
qed 

definition countable_intersection :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
  where "countable_intersection A\<^sub>n = {x. \<forall>n. x \<in> A\<^sub>n n}"

definition countable_intersection_sub :: "nat set \<Rightarrow> (nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
  where "countable_intersection_sub I A\<^sub>n = {x. \<forall>n\<in>I. x \<in> A\<^sub>n n}"

lemma countable_intersection_UNIV: "countable_intersection_sub UNIV A\<^sub>n = countable_intersection A\<^sub>n"
proof - 
  have "countable_intersection A\<^sub>n = {x. \<forall>n. x \<in> A\<^sub>n n}"
    using countable_intersection_def by metis 
  hence "countable_intersection A\<^sub>n = {x. \<forall>n\<in>UNIV. x \<in> A\<^sub>n n}"
    by auto 
  thus ?thesis 
    using countable_intersection_sub_def by metis 
qed 

lemma countable_intersection_empty: "countable_intersection_sub {} A\<^sub>n = UNIV"
proof - 
  have "\<not>(\<exists>x. x \<notin> {y. \<forall>n\<in>{}. y \<in> A\<^sub>n n})"
    by simp
  hence "\<not>(\<exists>x. x \<notin> countable_intersection_sub {} A\<^sub>n)"
    using countable_intersection_sub_def by metis 
  thus ?thesis
    by auto
qed 

subsubsection "Limits of Sets"

end