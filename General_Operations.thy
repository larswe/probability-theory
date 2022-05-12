theory General_Operations 
  imports "HOL-Analysis.Sigma_Algebra"
begin

section "Basics from Measure Theory"

subsection "Sets"

subsubsection "Set Operations"

definition disjoint :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "disjoint A B \<equiv> \<not>(\<exists>x. x\<in>A \<and> x\<in>B)"

lemma disj_iff_empty_inter: "(disjoint A B) = (A \<inter> B = {})"
  by (simp add: disjoint_def disjoint_iff)

(* Power set is Pow. *)

definition non_decreasing :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool"
  where "non_decreasing A\<^sub>n \<equiv> \<forall>n. A\<^sub>n n \<subseteq> A\<^sub>n (n + 1)"

lemma non_decreasing_multistep: 
  assumes non_dec: "non_decreasing A\<^sub>n"
      and leq: "n \<le> m"
    shows "A\<^sub>n n \<subseteq> A\<^sub>n m"
proof - 
  have "\<forall>n y. y \<in> A\<^sub>n n \<longrightarrow> y \<in> A\<^sub>n (Suc n)"
    using non_dec non_decreasing_def Suc_eq_plus1 subset_iff by metis
  hence "\<forall>n. \<forall>d\<ge>0. (A\<^sub>n n \<subseteq> A\<^sub>n (n+d))" 
      using add.commute le_add2 lift_Suc_mono_le subset_iff by metis
  thus "A\<^sub>n n \<subseteq> A\<^sub>n m"
    by (metis bot_nat_0.extremum le_iff_add leq)
qed 

lemma non_decreasing_stay_in: 
  assumes non_dec: "non_decreasing A\<^sub>n"
      and base: "x \<in> A\<^sub>n n"
    shows "\<forall>m\<ge>n. x \<in> A\<^sub>n m"
  using base non_dec non_decreasing_multistep by auto

definition non_increasing :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool"
  where "non_increasing A\<^sub>n \<equiv> \<forall>n. A\<^sub>n (n + 1) \<subseteq> A\<^sub>n n"

lemma non_increasing_multistep: 
  assumes non_inc: "non_increasing A\<^sub>n"
      and leq: "n \<le> m"
    shows "A\<^sub>n m \<subseteq> A\<^sub>n n"
proof - 
  have "\<forall>n y. y \<in> A\<^sub>n (Suc n) \<longrightarrow> y \<in> A\<^sub>n n"
    using non_inc non_increasing_def Suc_eq_plus1 subset_iff by metis
  hence "\<forall>n. \<forall>d\<ge>0. (A\<^sub>n (n+d) \<subseteq> A\<^sub>n n)" 
      using add.commute le_add2 subset_iff lift_Suc_antimono_le by metis 
  thus "A\<^sub>n m \<subseteq> A\<^sub>n n"
    by (metis bot_nat_0.extremum le_iff_add leq)
qed 

lemma non_increasing_stay_out: 
  assumes non_inc: "non_increasing A\<^sub>n"
      and base: "x \<notin> A\<^sub>n n"
    shows "\<forall>m\<ge>n. x \<notin> A\<^sub>n m"
  using base non_inc non_increasing_multistep by auto


definition general_union :: "'a set set \<Rightarrow> 'a set"
  where "general_union A = {x. \<exists>S. S \<in> A \<and> x \<in> S}"

lemma notin_general_union:
  assumes x_notin: "x \<notin> general_union A"
  shows "\<forall>S\<in>A. x \<notin> S"
  using x_notin general_union_def by fastforce

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

lemma general_union_binary: 
  "general_union {A, B} = A \<union> B"
proof - 
  have "general_union {A, B} = {x. \<exists>S. S \<in> {A, B} \<and> x \<in> S}"
    by (simp add: general_union_def)
  hence "general_union {A, B} = {x. x \<in> A \<or> x \<in> B}"
    by fast 
  thus ?thesis
    by auto 
qed

lemma general_union_UNIV: "general_union UNIV = UNIV"
  using general_union_def by fast 

lemma general_union_sequence: "general_union {A. \<exists>n. A = A\<^sub>n n} =
                                      {x. \<exists>n. x \<in> A\<^sub>n n}"
proof 
  show "general_union {A. \<exists>n. A = A\<^sub>n n} \<subseteq> {x. \<exists>n. x \<in> A\<^sub>n n}"
  proof 
    fix x 
    assume "x \<in> general_union {A. \<exists>n. A = A\<^sub>n n}"
    hence "\<exists>S. S \<in> {A. \<exists>n. A = A\<^sub>n n} \<and> x \<in> S"
      by (simp add: general_union_def)
    thus "x \<in> {x. \<exists>n. x \<in> A\<^sub>n n}"  
      by auto 
  qed
next 
  show "{x. \<exists>n. x \<in> A\<^sub>n n} \<subseteq> general_union {A. \<exists>n. A = A\<^sub>n n}"
  proof 
    fix x 
    assume "x \<in> {x. \<exists>n. x \<in> A\<^sub>n n}"
    hence "\<exists>S. S \<in> {A. \<exists>n. A = A\<^sub>n n} \<and> x \<in> S"
      by auto 
    thus "x \<in> general_union {A. \<exists>n. A = A\<^sub>n n}"
      by (simp add: general_union_def)
  qed
qed 


definition general_intersection :: "'a set set \<Rightarrow> 'a set"
  where "general_intersection A = {x. \<forall>S. S \<in> A \<longrightarrow> x \<in> S}"

lemma general_intersection_binary: 
  "general_intersection {A, B} = A \<inter> B"
proof - 
  have "general_intersection {A, B} = {x. \<forall>S. S \<in> {A, B} \<longrightarrow> x \<in> S}"
    by (simp add: general_intersection_def)
  hence "general_intersection {A, B} = {x. x \<in> A \<and> x \<in> B}"
    by fast 
  thus ?thesis
    by auto 
qed

lemma notin_general_intersection:
  shows "(x \<notin> general_intersection A) = (\<exists>S\<in>A. x \<notin> S)"
  using general_intersection_def by fast 

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

lemma general_intersection_sequence: "general_intersection {A. \<exists>n. A = A\<^sub>n n} =
                                      {x. \<forall>n. x \<in> A\<^sub>n n}"
proof 
  show "general_intersection {A. \<exists>n. A = A\<^sub>n n} \<subseteq> {x. \<forall>n. x \<in> A\<^sub>n n}"
  proof 
    fix x 
    assume "x \<in> general_intersection {A. \<exists>n. A = A\<^sub>n n}"
    hence "\<forall>S. S \<in> {A. \<exists>n. A = A\<^sub>n n} \<longrightarrow> x \<in> S"
      by (simp add: general_intersection_def)
    thus "x \<in> {x. \<forall>n. x \<in> A\<^sub>n n}"  
      by auto 
  qed
next 
  show "{x. \<forall>n. x \<in> A\<^sub>n n} \<subseteq> general_intersection {A. \<exists>n. A = A\<^sub>n n}"
  proof 
    fix x 
    assume "x \<in> {x. \<forall>n. x \<in> A\<^sub>n n}"
    hence "\<forall>S. S \<in> {A. \<exists>n. A = A\<^sub>n n} \<longrightarrow> x \<in> S"
      by auto 
    thus "x \<in> general_intersection {A. \<exists>n. A = A\<^sub>n n}"
      by (simp add: general_intersection_def)
  qed
qed 


(* The union/intersection of a set collection is a subset of any set that all members belong to.*)
lemma collection_union_subseq: 
  assumes subseq: "\<forall>A\<in>\<A>. A \<subseteq> \<Omega>" 
  shows "general_union \<A> \<subseteq> \<Omega>"
proof 
  fix x 
  assume "x \<in> general_union \<A>"
  hence "\<exists>S. S \<in> \<A> \<and> x \<in> S"
    by (simp add: general_union_def)
  then obtain S where "S \<in> \<A> \<and> x \<in> S"
    by fast 
  moreover have "S \<subseteq> \<Omega>"
    by (simp add: calculation subseq)
  ultimately show "x \<in> \<Omega>"
    by auto 
qed 

lemma collection_inter_subseq: 
  assumes subseq: "\<forall>A\<in>\<A>. A \<subseteq> \<Omega>"
      and non_empty: "\<A> \<noteq> {}"
  shows "general_intersection \<A> \<subseteq> \<Omega>"
proof 
  fix x 
  assume x_in_inter: "x \<in> general_intersection \<A>"
  hence "\<forall>S. S \<in> \<A> \<longrightarrow> x \<in> S"
    by (simp add: general_intersection_def)
  then obtain S where "S \<in> \<A> \<and> x \<in> S"
    using non_empty by fast
  moreover have "S \<subseteq> \<Omega>"
    by (simp add: calculation subseq)
  ultimately show "x \<in> \<Omega>"
    by auto
qed 


definition set_complement :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "set_complement A \<Omega> = (THE B. B = {x\<in>\<Omega>. x \<notin> A} \<and> A \<subseteq> \<Omega>)"

lemma set_complement_meaning: 
  assumes subseq: "A \<subseteq> B"
  shows "set_complement A B = {x\<in>B. x \<notin> A}"
  by (simp add: set_complement_def subseq)

lemma set_complement_diff: 
  assumes subseq: "A \<subseteq> B"
  shows "set_complement A B = B - A"
  using Diff_iff subseq set_complement_meaning by auto 

lemma set_complement_self_inverse: 
  assumes subseq: "A \<subseteq> B"
    shows "set_complement (set_complement A B) B = A"
  by (simp add: double_diff set_complement_diff subseq)

lemma de_morgan_general_1: 
  assumes subseq: "\<forall>A\<in>\<A>. A \<subseteq> \<Omega>" 
      and non_empty_collection: "\<A> \<noteq> {}"
  shows "set_complement (general_union \<A>) \<Omega> = 
         general_intersection {C. \<exists>S\<in>\<A>. C = set_complement S \<Omega>}"
proof
  show "set_complement (general_union \<A>) \<Omega> \<subseteq> general_intersection {C. \<exists>S\<in>\<A>. C = set_complement S \<Omega>}" 
  proof 
    fix x 
    assume "x \<in> set_complement (general_union \<A>) \<Omega>"
    moreover have "(general_union \<A>) \<subseteq> \<Omega>"
      using subseq collection_union_subseq by auto 
    hence "set_complement (general_union \<A>) \<Omega> = {x\<in>\<Omega>. x \<notin> (general_union \<A>)}"
      using set_complement_meaning by auto 
    ultimately have "x \<in> \<Omega> \<and> x \<notin> general_union \<A>" 
      by simp 
    hence "x \<in> \<Omega> \<and> \<not>(\<exists>S. S \<in> \<A> \<and> x \<in> S)"
      using general_union_def by fast
    hence "x \<in> \<Omega> \<and> (\<forall>S. S \<notin> \<A> \<or> x \<notin> S)"
      by auto 
    hence "\<forall>S\<in>\<A>. x \<in> set_complement S \<Omega>"
      by (simp add: set_complement_meaning subseq) 
    thus "x \<in> general_intersection {C. \<exists>S\<in>\<A>. C = set_complement S \<Omega>}"
      using general_intersection_def by fastforce 
  qed 
next 
  show "general_intersection {C. \<exists>S\<in>\<A>. C = set_complement S \<Omega>} \<subseteq> set_complement (general_union \<A>) \<Omega>"
  proof 
    fix x 
    assume "x \<in> general_intersection {C. \<exists>S\<in>\<A>. C = set_complement S \<Omega>}"
    hence "\<forall>C. (\<exists>S\<in>\<A>. C = set_complement S \<Omega>) \<longrightarrow> x \<in> C"
      by (simp add: general_intersection_def)
    hence "\<forall>S\<in>\<A>. x \<in> set_complement S \<Omega>"
      by auto 
    moreover have "\<forall>S\<in>\<A>. set_complement S \<Omega> = {x\<in>\<Omega>. x \<notin> S}"
      using set_complement_meaning subseq by auto 
    ultimately have "\<forall>S\<in>\<A>. (x \<in> \<Omega> \<and> x \<notin> S)" 
      by simp
    hence "x \<in> \<Omega> \<and> (\<forall>S\<in>\<A>. x \<notin> S)"
      using non_empty_collection by auto 
    hence "x \<in> \<Omega> \<and> x \<notin> general_union \<A>"
      by (simp add: general_union_def)
    thus "x \<in> set_complement (general_union \<A>) \<Omega>"
      by (simp add: collection_union_subseq set_complement_meaning subseq) 
  qed 
qed

lemma de_morgan_general_2: 
  assumes subseq: "\<forall>A\<in>\<A>. A \<subseteq> \<Omega>" 
      and non_empty_collection: "\<A> \<noteq> {}"
    shows "set_complement (general_intersection \<A>) \<Omega> = 
           general_union {C. \<exists>S\<in>\<A>. C = set_complement S \<Omega>}"
proof 
  show "set_complement (general_intersection \<A>) \<Omega> \<subseteq> general_union {C. \<exists>S\<in>\<A>. C = set_complement S \<Omega>}"
  proof 
    fix x 
    assume "x \<in> set_complement (general_intersection \<A>) \<Omega>"
    moreover have "(general_intersection \<A>) \<subseteq> \<Omega>"
      using subseq non_empty_collection collection_inter_subseq by auto 
    hence "set_complement (general_intersection \<A>) \<Omega> = {x\<in>\<Omega>. x \<notin> (general_intersection \<A>)}"
      using set_complement_meaning by auto 
    ultimately have "x \<in> \<Omega> \<and> x \<notin> general_intersection \<A>" 
      by simp 
    hence "\<exists>S\<in>\<A>. x \<notin> S \<and> x \<in> \<Omega>"
      by (metis notin_general_intersection)
    hence "\<exists>S\<in>\<A>. x \<in> set_complement S \<Omega>"
      by (simp add: set_complement_meaning subseq)
    thus "x \<in> general_union {C. \<exists>S\<in>\<A>. C = set_complement S \<Omega>}"
      using general_union_def by fast
  qed 
next 
  show "general_union {C. \<exists>S\<in>\<A>. C = set_complement S \<Omega>} \<subseteq> set_complement (general_intersection \<A>) \<Omega>"
  proof
    fix x 
    assume "x \<in> general_union {C. \<exists>S\<in>\<A>. C = set_complement S \<Omega>}"
    hence "\<exists>C. \<exists>S\<in>\<A>. C = set_complement S \<Omega> \<and> x \<in> C"
      by (simp add: general_union_def)
    hence "\<exists>S\<in>\<A>. x \<in> set_complement S \<Omega>"
      by auto 
    hence "x \<in> \<Omega> \<and> (\<exists>S\<in>\<A>. x \<notin> S)"
      by (simp add: subseq set_complement_meaning)
    hence "x \<in> \<Omega> \<and> x \<notin> general_intersection \<A>"
      by (simp add: notin_general_intersection)
    thus "x \<in> set_complement (general_intersection \<A>) \<Omega>"
      by (simp add: collection_inter_subseq non_empty_collection set_complement_diff subseq) 
  qed
qed

lemma de_morgan_binary_1: 
assumes A_subseq: "A \<subseteq> \<Omega>" 
    and B_subseq: "B \<subseteq> \<Omega>" 
  shows "set_complement (A \<union> B) \<Omega> = (set_complement A \<Omega>) \<inter> (set_complement B \<Omega>)"
proof - 
  have "A \<union> B = general_union {A, B}"
    by (simp add: general_union_binary)
  moreover have "(set_complement A \<Omega>) \<inter> (set_complement B \<Omega>) = 
                 general_intersection {set_complement A \<Omega>, set_complement B \<Omega>}"
    by (simp add: general_intersection_binary)
  moreover have "{set_complement A \<Omega>, set_complement B \<Omega>} = {C. \<exists>S\<in>{A, B}. C = set_complement S \<Omega>}"
    by auto 
  moreover have "set_complement (general_union {A, B}) \<Omega> = 
                 general_intersection {C. \<exists>S\<in>{A, B}. C = set_complement S \<Omega>}"
    by (simp add: A_subseq B_subseq de_morgan_general_1)
  ultimately show ?thesis 
    by simp 
qed

lemma de_morgan_binary_2: 
assumes A_subseq: "A \<subseteq> \<Omega>" 
    and B_subseq: "B \<subseteq> \<Omega>" 
  shows "set_complement (A \<inter> B) \<Omega> = (set_complement A \<Omega>) \<union> (set_complement B \<Omega>)"
proof - 
  have "A \<inter> B = general_intersection {A, B}"
    by (simp add: general_intersection_binary)
  moreover have "(set_complement A \<Omega>) \<union> (set_complement B \<Omega>) = 
                 general_union {set_complement A \<Omega>, set_complement B \<Omega>}"
    by (simp add: general_union_binary)
  moreover have "{set_complement A \<Omega>, set_complement B \<Omega>} = {C. \<exists>S\<in>{A, B}. C = set_complement S \<Omega>}"
    by auto 
  moreover have "set_complement (general_intersection {A, B}) \<Omega> = 
                 general_union {C. \<exists>S\<in>{A, B}. C = set_complement S \<Omega>}"
    by (simp add: A_subseq B_subseq de_morgan_general_2)
  ultimately show ?thesis 
    by simp 
qed

subsubsection "Limits of Sets"

definition liminf :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
  where "liminf A = 
         general_union {B. \<exists>n. B = general_intersection {C. \<exists>k. k \<ge> n \<and> C = A k}}"

lemma liminf_greater_n: "(x \<in> liminf A) = (\<exists>n. \<forall>k. (k \<ge> n \<longrightarrow> x \<in> A k))"
proof - 
  have "(x \<in> liminf A) = 
         (\<exists>S. \<exists>n. S = general_intersection {C. \<exists>k. k \<ge> n \<and> C = A k} \<and> x \<in> S)"
    by (simp add: liminf_def general_union_def)
  hence "(x \<in> liminf A) = (\<exists>n. x \<in> general_intersection {C. \<exists>k. k \<ge> n \<and> C = A k})"
    by auto
  hence "(x \<in> liminf A) = (\<exists>n. \<forall>S. (S \<in> {C. \<exists>k. k \<ge> n \<and> C = A k} \<longrightarrow> x \<in> S))"
    by (simp add: general_intersection_def)
  thus ?thesis
    by auto
qed

lemma liminf_greater_n_set: "liminf A = {x. \<exists>n. \<forall>k. k \<ge> n \<longrightarrow> x \<in> A k}"
proof 
  show "liminf A \<subseteq> {x. \<exists>n. \<forall>k\<ge>n. x \<in> A k}"
  proof 
    fix x 
    assume "x \<in> liminf A"
    hence "\<exists>n. \<forall>k. (k \<ge> n \<longrightarrow> x \<in> A k)"
      by (simp add: liminf_greater_n) 
    thus "x \<in> {x. \<exists>n. \<forall>k. k \<ge> n \<longrightarrow> x \<in> A k}" 
      by auto 
  qed 
next 
  show "{x. \<exists>n. \<forall>k\<ge>n. x \<in> A k} \<subseteq> liminf A"
  proof 
    fix x 
    assume "x \<in> {x. \<exists>n. \<forall>k\<ge>n. x \<in> A k}"
    hence "\<exists>n. \<forall>k. (k \<ge> n \<longrightarrow> x \<in> A k)"
      by auto 
    thus "x \<in> liminf A" 
      by (simp add: liminf_greater_n) 
  qed
qed
   

definition limsup :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
  where "limsup A = general_intersection {B. \<exists>n. B = general_union {C. \<exists>m. m \<ge> n \<and> C = A m}}"

lemma limsup_greater_n: "(x \<in> limsup A) = (\<forall>n. \<exists>m. m \<ge> n \<and> x \<in> A m)"
proof - 
  have "(x \<in> limsup A) = 
        (x \<in> general_intersection {B. \<exists>n. B = general_union {C. \<exists>m. m \<ge> n \<and> C = A m}})"
    using limsup_def by fast 
  hence "(x \<in> limsup A) = (\<forall>S. (\<exists>n. S = {x. \<exists>S'. S' \<in> {C. \<exists>m. m \<ge> n \<and> C = A m} \<and> x \<in> S'}) \<longrightarrow> x \<in> S)"
    by (simp add: general_union_def general_intersection_def) 
  hence "(x \<in> limsup A) = (\<forall>n. \<exists>S'. (\<exists>m. m \<ge> n \<and> S' = A m) \<and> x \<in> S')"
    by auto 
  thus ?thesis 
    by fast 
qed

lemma limsup_greater_n_set: "limsup A = {x. \<forall>n. \<exists>m. m \<ge> n \<and> x \<in> A m}"
proof 
  show "limsup A \<subseteq> {x. \<forall>n. \<exists>m. m \<ge> n \<and> x \<in> A m}"
  proof 
    fix x 
    assume "x \<in> limsup A"
    hence "\<forall>n. \<exists>m. m \<ge> n \<and> x \<in> A m"
      by (simp add: limsup_greater_n) 
    thus "x \<in> {x. \<forall>n. \<exists>m. m \<ge> n \<and> x \<in> A m}" 
      by auto 
  qed 
next 
  show "{x. \<forall>n. \<exists>m. m \<ge> n \<and> x \<in> A m} \<subseteq> limsup A"
  proof 
    fix x 
    assume "x \<in> {x. \<forall>n. \<exists>m. m \<ge> n \<and> x \<in> A m}"
    hence "\<forall>n. \<exists>m. m \<ge> n \<and> x \<in> A m"
      by auto 
    thus "x \<in> limsup A" 
      by (simp add: limsup_greater_n) 
  qed
qed

lemma liminf_sub_limsup: "liminf A \<subseteq> limsup A"
proof 
  fix x 
  assume "x \<in> liminf A"
  hence "\<exists>n. \<forall>m. (m \<ge> n \<longrightarrow> x \<in> A m)"
    by (simp add: liminf_greater_n)
  hence "\<forall>n. \<exists>m. m \<ge> n \<and> x \<in> A m"
    by (meson nat_le_linear)  
  thus "x \<in> limsup A" 
    by (simp add: limsup_greater_n) 
qed

lemma liminf_limsup_eq_cond: 
  assumes limsup_sub_liminf: "limsup A \<subseteq> liminf A" 
  shows "liminf A = limsup A"
  by (simp add: limsup_sub_liminf liminf_sub_limsup subset_antisym)


definition set_limit :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
  where "set_limit A = (THE S. S = liminf A \<and> S = limsup A)"

lemma set_limit_eq_liminf: 
  assumes lim_defined: "liminf A = limsup A"
  shows "set_limit A = liminf A"
  by (simp add: lim_defined set_limit_def)

lemma set_limit_eq_limsup: 
  assumes lim_defined: "liminf A = limsup A"
  shows "set_limit A = limsup A"
  by (simp add: lim_defined set_limit_def)

lemma non_decreasing_set_limit: 
  assumes non_decreasing: "non_decreasing A\<^sub>n"
  shows "set_limit A\<^sub>n = general_union {A. \<exists>n. A = A\<^sub>n n}"
proof - 
  have "limsup A\<^sub>n = general_union {A. \<exists>n. A = A\<^sub>n n}" 
  proof 
    show "limsup A\<^sub>n \<subseteq> general_union {A. \<exists>n. A = A\<^sub>n n}"
    proof 
      fix x 
      assume "x \<in> limsup A\<^sub>n"
      hence "(\<exists>m. m \<ge> 1 \<and> x \<in> A\<^sub>n m)"
        by (simp add: limsup_greater_n) 
      hence "(\<exists>m. x \<in> A\<^sub>n m)"
        by auto 
      thus "x \<in> general_union {A. \<exists>n. A = A\<^sub>n n}" 
        using general_union_sequence by fast  
    qed
  next 
    show "general_union {A. \<exists>n. A = A\<^sub>n n} \<subseteq> limsup A\<^sub>n"
    proof 
      fix x 
      assume "x \<in> general_union {A. \<exists>n. A = A\<^sub>n n}" 
      hence "x \<in> {x. \<exists>n. x \<in> A\<^sub>n n}"
        using general_union_sequence by metis 
      hence "\<exists>n. x \<in> A\<^sub>n n"
        by auto 
      then obtain n where "x \<in> A\<^sub>n n" 
        by auto 
      hence "\<forall>m\<ge>n. x \<in> A\<^sub>n m"
        by (meson non_decreasing non_decreasing_stay_in)
      thus "x \<in> limsup A\<^sub>n"
        by (meson limsup_greater_n nat_le_linear) 
    qed
  qed

  moreover have "limsup A\<^sub>n = liminf A\<^sub>n" 
  proof - 
    have "limsup A\<^sub>n \<subseteq> liminf A\<^sub>n"
    proof 
      fix x 
      assume "x \<in> limsup A\<^sub>n"
      hence "\<forall>n. \<exists>m. m \<ge> n \<and> x \<in> A\<^sub>n m"
        by (simp add: limsup_greater_n)
      hence "\<exists>n. \<forall>k. (k \<ge> n \<longrightarrow> x \<in> A\<^sub>n k)"
        by (meson non_decreasing non_decreasing_stay_in)
      thus "x \<in> liminf A\<^sub>n"
        by (simp add: liminf_greater_n)
    qed
    thus ?thesis
      using liminf_limsup_eq_cond by auto 
  qed

  ultimately show ?thesis
    by (simp add: set_limit_eq_limsup) 
qed

lemma non_increasing_set_limit: 
  assumes non_increasing: "non_increasing A\<^sub>n"
  shows "set_limit A\<^sub>n = general_intersection {A. \<exists>n. A = A\<^sub>n n}"
proof - 
  have "limsup A\<^sub>n = general_intersection {A. \<exists>n. A = A\<^sub>n n}" 
  proof 
    show "limsup A\<^sub>n \<subseteq> general_intersection {A. \<exists>n. A = A\<^sub>n n}"
    proof 
      fix x 
      assume "x \<in> limsup A\<^sub>n"
      hence "\<forall>n. \<exists>m. m \<ge> n \<and> x \<in> A\<^sub>n m"
        by (simp add: limsup_greater_n) 
      hence "\<forall>m. x \<in> A\<^sub>n m"
        using non_increasing non_increasing_stay_out by metis 
      thus "x \<in> general_intersection {A. \<exists>n. A = A\<^sub>n n}"
        using general_intersection_sequence by fast 
    qed
  next 
    show "general_intersection {A. \<exists>n. A = A\<^sub>n n} \<subseteq> limsup A\<^sub>n"
    proof 
      fix x 
      assume "x \<in> general_intersection {A. \<exists>n. A = A\<^sub>n n}" 
      hence "\<forall>n. x \<in> A\<^sub>n n"
        using general_intersection_sequence by fast 
      thus "x \<in> limsup A\<^sub>n"
        by (meson limsup_greater_n order_refl)
    qed
  qed

  moreover have "limsup A\<^sub>n = liminf A\<^sub>n" 
  proof - 
    have "limsup A\<^sub>n \<subseteq> liminf A\<^sub>n"
    proof 
      fix x 
      assume "x \<in> limsup A\<^sub>n"
      hence "\<forall>n. \<exists>m. m \<ge> n \<and> x \<in> A\<^sub>n m"
        by (simp add: limsup_greater_n)
      hence "\<exists>n. \<forall>k\<ge>n. x \<in> A\<^sub>n k"
        by (meson non_increasing non_increasing_stay_out)
      thus "x \<in> liminf A\<^sub>n"
        by (simp add: liminf_greater_n) 
    qed
    thus ?thesis
      using liminf_limsup_eq_cond by auto 
  qed

  ultimately show ?thesis
    by (simp add: set_limit_eq_limsup) 
qed

subsection "Collections of Sets"

definition complement_stable :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "complement_stable \<A> \<Omega> \<equiv> \<A> \<noteq> {} \<and> (\<forall>A\<in>\<A>. set_complement A \<Omega> \<in> \<A>)"

definition finite_union_stable :: "'a set set \<Rightarrow> bool"
  where "finite_union_stable \<A> \<equiv> \<A> \<noteq> {} \<and> (\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A\<union>B \<in> \<A>)"

definition finite_inter_stable :: "'a set set \<Rightarrow> bool"
  where "finite_inter_stable \<A> \<equiv> \<A> \<noteq> {} \<and> (\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A\<inter>B \<in> \<A>)"

lemma c_fu_imp_fi_stable: 
  assumes c_stable: "complement_stable \<A> \<Omega>"
      and fu_stable: "finite_union_stable \<A>" 
      and subseq: "\<forall>S\<in>\<A>. S \<subseteq> \<Omega>"
    shows "finite_inter_stable \<A>"
proof - 
  have "\<A> \<noteq> {}"
    using fu_stable finite_union_stable_def by auto 

  moreover have "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A\<inter>B \<in> \<A>"
  proof 
    fix A
    assume A_in: "A \<in> \<A>"
    show "\<forall>B\<in>\<A>. A \<inter> B \<in> \<A>"
    proof 
      fix B
      assume B_in: "B \<in> \<A>"
      have "set_complement A \<Omega> \<in> \<A>"
        using A_in c_stable complement_stable_def by auto
      moreover have "set_complement B \<Omega> \<in> \<A>"
        using B_in c_stable complement_stable_def by auto 
      ultimately have "(set_complement A \<Omega>) \<union> (set_complement B \<Omega>) \<in> \<A>"
        using finite_union_stable_def fu_stable by fast
      moreover have "(set_complement A \<Omega>) \<union> (set_complement B \<Omega>) = set_complement (A \<inter> B) \<Omega>"
        by (simp add: A_in B_in de_morgan_binary_2 subseq)
      ultimately have "set_complement (set_complement (A \<inter> B) \<Omega>) \<Omega> \<in> \<A>"
        using c_stable complement_stable_def by auto
      thus "A \<inter> B \<in> \<A>"
        by (metis A_in le_sup_iff set_complement_self_inverse subseq sup_inf_absorb) 
    qed
  qed

  ultimately show "finite_inter_stable \<A>"
    by (simp add: finite_inter_stable_def) 
qed

(* TODO: c_fi_imp_fu_stable*)

definition set_diff_stable :: "'a set set \<Rightarrow> bool"
  where "set_diff_stable \<A> \<equiv> \<A> \<noteq> {} \<and> (\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. B \<subseteq> A \<longrightarrow> A-B \<in> \<A>)"

definition countable_union_stable :: "'a set set \<Rightarrow> bool"
  where "countable_union_stable \<A> \<equiv> \<A> \<noteq> {} \<and> (\<forall>A\<^sub>n. (\<forall>n::nat. A\<^sub>n n \<in> \<A>) \<longrightarrow> 
  (general_union {S. \<exists>n. S = A\<^sub>n n} \<in> \<A>))"

(* TODO - disjoint_countable_union_stable *) 

definition countable_inter_stable :: "'a set set \<Rightarrow> bool"
  where "countable_inter_stable \<A> \<equiv> \<A> \<noteq> {} \<and> (\<forall>A\<^sub>n. (\<forall>n::nat. A\<^sub>n n \<in> \<A>) \<longrightarrow> 
  (general_intersection {S. \<exists>n. S = A\<^sub>n n} \<in> \<A>))"

end