theory Probability_Theory 
  imports "HOL-Probability.Probability"
begin

section "Basics from Measure Theory"

subsection "Sets"

subsubsection "Set Operations"

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

definition general_union :: "'a set set \<Rightarrow> 'a set"
  where "general_union A = {x. \<exists>S. S \<in> A \<and> x \<in> S}"

lemma general_union_empty: "general_union {} = {}"
proof - 
  have "\<not>(\<exists>x. x \<in> {y. \<exists>A. A \<in> {} \<and> y \<in> A})"
    by simp
  hence "\<not>(\<exists>x. x \<in> general_union {})"
    using general_union_def by metis 
  thus ?thesis
    by simp 
qed 

lemma general_union_singleton: "general_union {A} = A"
  by (simp add: general_union_def)

lemma general_union_UNIV: "general_union UNIV = UNIV"
  using general_union_def by fast 


definition general_intersection :: "'a set set \<Rightarrow> 'a set"
  where "general_intersection A = {x. \<forall>S. S \<in> A \<longrightarrow> x \<in> S}"

lemma general_intersection_empty: "general_intersection {} = UNIV"
proof - 
  have "\<not>(\<exists>x. x \<notin> {y. \<forall>A. A \<in> {} \<longrightarrow> y \<in> A})"
    by simp
  hence "\<not>(\<exists>x. x \<notin> general_intersection {})"
    using general_intersection_def by metis 
  thus ?thesis
    by auto  
qed 

lemma general_intersection_singleton: "general_intersection {A} = A"
  by (simp add: general_intersection_def)

lemma general_intersection_UNIV: "general_intersection UNIV = {}"
proof -  
  have "\<forall>x. x \<notin> {y. \<forall>A. A \<in> UNIV \<longrightarrow> y \<in> A}" 
    by auto 
  hence "\<forall>x. x \<notin> general_intersection UNIV"
    using general_intersection_def by metis
  thus ?thesis
    by simp 
qed


definition set_complement :: "'a set \<Rightarrow> 'a set"
  where "set_complement A = {x. x \<notin> A}"

lemma general_de_morgan1: "set_complement (general_union A) = 
                           general_intersection {C. \<exists>S\<in>A. C = set_complement S}"
proof
  show "set_complement (general_union A) \<subseteq> general_intersection {C. \<exists>S\<in>A. C = set_complement S}" 
  proof 
    fix x 
    assume "x \<in> set_complement (general_union A)"
    hence "\<forall>S. S \<in> A \<longrightarrow> x \<in> (set_complement S)"
      by (simp add: set_complement_def general_union_def)
    hence "\<forall>C. (\<exists>S\<in>A. C = set_complement S) \<longrightarrow> x \<in> C" 
      by auto
    thus "x \<in> general_intersection {C. \<exists>S\<in>A. C = set_complement S}"
      by (simp add: general_intersection_def)  
  qed 
next 
  show "general_intersection {C. \<exists>S\<in>A. C = set_complement S} \<subseteq> set_complement (general_union A)"
  proof 
    fix x 
    assume "x \<in> general_intersection {C. \<exists>S\<in>A. C = set_complement S}"
    hence "\<forall>C. (\<exists>S\<in>A. C = set_complement S) \<longrightarrow> x \<in> C"
      by (simp add: general_intersection_def) 
    hence "\<not>(\<exists>S. S \<in> A \<and> x \<in> S)"
      using set_complement_def by fastforce 
    thus "x \<in> set_complement (general_union A)"
      by (simp add: set_complement_def general_union_def)  
  qed 
qed

lemma general_de_morgan2: "set_complement (general_intersection A) = 
                           general_union {C. \<exists>S\<in>A. C = set_complement S}"
proof 
  show "set_complement (general_intersection A) \<subseteq> general_union {C. \<exists>S\<in>A. C = set_complement S}"
  proof 
    fix x 
    assume "x \<in> set_complement (general_intersection A)"
    hence "\<exists>S. S \<in> A \<and> x \<in> set_complement S"
      by (simp add: set_complement_def general_intersection_def)
    thus "x \<in> general_union {C. \<exists>S\<in>A. C = set_complement S}"
      using general_union_def by fastforce
  qed 
next 
  show "general_union {C. \<exists>S\<in>A. C = set_complement S} \<subseteq> set_complement (general_intersection A)"
  proof
    fix x 
    assume "x \<in> general_union {C. \<exists>S\<in>A. C = set_complement S}"
    hence "\<exists>C. \<exists>S\<in>A. C = set_complement S \<and> x \<in> C"
      by (simp add: general_union_def)
    hence "\<exists>S\<in>A. x \<notin> S"
      by (metis set_complement_def mem_Collect_eq) 
    thus "x \<in> set_complement (general_intersection A)" 
      using set_complement_def general_intersection_def by fastforce
  qed
qed

subsubsection "Limits of Sets"

end