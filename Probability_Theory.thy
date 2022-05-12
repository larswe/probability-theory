theory Probability_Theory 
  imports "HOL-Analysis.Sigma_Algebra"
begin

chapter "Basics from Measure Theory"

section "Sets"

subsection "Set operations"

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


subsection "Limits of Sets"

definition liminf :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
  where "liminf A\<^sub>n = (\<Union>n. (\<Inter>m\<in>{m'. m' \<ge> n}. A\<^sub>n m))"

lemma liminf_greater_n: "(x \<in> liminf A\<^sub>n) = (\<exists>n.\<forall>m\<ge>n. x \<in> A\<^sub>n m)"
  by (simp add: liminf_def) 

definition limsup :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
  where "limsup A\<^sub>n = (\<Inter>n. (\<Union>m\<in>{m'. m' \<ge> n}. A\<^sub>n m))"

lemma limsup_greater_n: "(x \<in> limsup A\<^sub>n) = (\<forall>n.\<exists>m\<ge>n. x \<in> A\<^sub>n m)"
  by (simp add: limsup_def) 

lemma liminf_subseq_limsup: "liminf A\<^sub>n \<subseteq> limsup A\<^sub>n"
proof 
  fix x 
  assume "x \<in> liminf A\<^sub>n"
  hence "\<exists>n.\<forall>m\<ge>n. x \<in> A\<^sub>n m"
    by (simp add: liminf_greater_n)
  hence "\<forall>n.\<exists>m\<ge>n. x \<in> A\<^sub>n m"
    by (metis nat_le_linear)
  thus "x \<in> limsup A\<^sub>n"
    by (simp add: limsup_greater_n)
qed 

lemma liminf_limsup_eq_cond: 
  assumes limsup_subseq_liminf: "limsup A \<subseteq> liminf A" 
  shows "liminf A = limsup A"
  by (simp add: limsup_subseq_liminf liminf_subseq_limsup subset_antisym)

definition set_limit :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
  where "set_limit A = (THE S. S = liminf A \<and> S = limsup A)"

lemma set_limit_eq_liminf: 
  assumes limsup_subseq_liminf: "limsup A \<subseteq> liminf A" 
  shows "set_limit A = liminf A"
proof - 
  have "limsup A = liminf A"
    by (simp add: liminf_limsup_eq_cond limsup_subseq_liminf)
  thus ?thesis 
    by (simp add: set_limit_def) 
qed

lemma set_limit_eq_limsup: 
  assumes limsup_subseq_liminf: "limsup A \<subseteq> liminf A" 
  shows "set_limit A = limsup A"
  by (simp add: liminf_limsup_eq_cond limsup_subseq_liminf set_limit_eq_liminf)

proposition non_decreasing_set_limit: 
  assumes non_decreasing: "non_decreasing A\<^sub>n"
  shows "set_limit A\<^sub>n = \<Union>(range A\<^sub>n)" 
proof - 
  have "limsup A\<^sub>n = \<Union>(range A\<^sub>n)" 
  proof 
    show "limsup A\<^sub>n \<subseteq> \<Union>(range A\<^sub>n)"
    proof 
      fix x 
      assume "x \<in> limsup A\<^sub>n"
      hence "(\<exists>m. m \<ge> 1 \<and> x \<in> A\<^sub>n m)"
        by (simp add: limsup_greater_n) 
      thus "x \<in> \<Union>(range A\<^sub>n)"
        by auto 
    qed
  next 
    show "\<Union>(range A\<^sub>n) \<subseteq> limsup A\<^sub>n"
    proof 
      fix x 
      assume "x \<in> \<Union>(range A\<^sub>n)" 
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
      hence "\<forall>n.\<exists>m\<ge>n. x \<in> A\<^sub>n m"
        by (simp add: limsup_greater_n)
      hence "\<exists>n.\<forall>m\<ge>n. x \<in> A\<^sub>n m"
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

proposition non_increasing_set_limit: 
  assumes non_increasing: "non_increasing A\<^sub>n"
  shows "set_limit A\<^sub>n = \<Inter>(range A\<^sub>n)" 
proof - 
  have "limsup A\<^sub>n = \<Inter>(range A\<^sub>n)" 
  proof 
    show "limsup A\<^sub>n \<subseteq> \<Inter>(range A\<^sub>n)"
    proof 
      fix x 
      assume "x \<in> limsup A\<^sub>n"
      hence "\<forall>n. \<exists>m. m \<ge> n \<and> x \<in> A\<^sub>n m"
        by (simp add: limsup_greater_n) 
      hence "\<forall>m. x \<in> A\<^sub>n m"
        using non_increasing non_increasing_stay_out by metis 
      thus "x \<in> \<Inter>(range A\<^sub>n)"
        by simp 
    qed
  next 
    show "\<Inter>(range A\<^sub>n) \<subseteq> limsup A\<^sub>n"
    proof 
      fix x 
      assume "x \<in> \<Inter>(range A\<^sub>n)" 
      hence "\<forall>m. x \<in> A\<^sub>n m"
        by simp 
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


section "Collections of Sets"

subsection "Rules for Collections of Sets"

definition complement_stable :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "complement_stable \<A> \<Omega> = ((\<A> \<noteq> {}) \<and> (\<forall>A\<in>\<A>. \<Omega> - A \<in> \<A>))"

definition finite_union_stable :: "'a set set \<Rightarrow> bool"
  where "finite_union_stable \<A> = ((\<A> \<noteq> {}) \<and> (\<forall>A\<in>\<A>.\<forall>B\<in>\<A>. A \<union> B \<in> \<A>))"

lemma fu_stable_finite: 
  assumes fu_stable: "finite_union_stable \<A>"
      and family_in: "\<forall>i\<in>I. A\<^sub>n i \<in> \<A>"
      and finite: "finite I"
      and non_empty: "I \<noteq> {}"
    shows "(\<Union>i\<in>I. A\<^sub>n i) \<in> \<A>"
  using finite non_empty family_in fu_stable
proof (induction I rule: finite_induct)
  case empty
  then show ?case
    by auto 
next
  case (insert x F)
  show ?case 
  proof (cases "F = {}")
    case True
    hence "\<Union> (A\<^sub>n ` insert x F) = A\<^sub>n x"
      by simp
    then show "\<Union> (A\<^sub>n ` insert x F) \<in> \<A>"
      by (simp add: insert.prems(2)) 
  next
    case False
    hence "(\<Union>i\<in>F. A\<^sub>n i) \<in> \<A>"
      by (simp add: fu_stable insert.IH insert.prems(2)) 
    moreover have "A\<^sub>n x \<in> \<A>"
      by (simp add: insert.prems(2))
    moreover have "\<Union> (A\<^sub>n ` insert x F) = (\<Union>i\<in>F. A\<^sub>n i) \<union> (A\<^sub>n x)"
      by auto 
    ultimately show "\<Union> (A\<^sub>n ` insert x F) \<in> \<A>"
      by (metis finite_union_stable_def fu_stable) 
  qed
qed 
    

definition finite_inter_stable :: "'a set set \<Rightarrow> bool"
  where "finite_inter_stable \<A> = ((\<A> \<noteq> {}) \<and> (\<forall>A\<in>\<A>.\<forall>B\<in>\<A>. A \<inter> B \<in> \<A>))"

lemma fi_stable_finite: 
  assumes fi_stable: "finite_inter_stable \<A>"
      and family_in: "\<forall>i\<in>I. A\<^sub>n i \<in> \<A>"
      and finite: "finite I"
      and non_empty: "I \<noteq> {}"
    shows "(\<Inter>i\<in>I. A\<^sub>n i) \<in> \<A>"
  using finite non_empty family_in fi_stable
proof (induction I rule: finite_induct)
  case empty
  then show ?case
    by auto 
next
  case (insert x F)
  show ?case 
  proof (cases "F = {}")
    case True
    hence "\<Inter> (A\<^sub>n ` insert x F) = A\<^sub>n x"
      by simp
    then show "\<Inter> (A\<^sub>n ` insert x F) \<in> \<A>"
      by (simp add: insert.prems(2)) 
  next
    case False
    hence "(\<Inter>i\<in>F. A\<^sub>n i) \<in> \<A>"
      by (simp add: fi_stable insert.IH insert.prems(2)) 
    moreover have "A\<^sub>n x \<in> \<A>"
      by (simp add: insert.prems(2))
    moreover have "\<Inter> (A\<^sub>n ` insert x F) = (\<Inter>i\<in>F. A\<^sub>n i) \<inter> (A\<^sub>n x)"
      by auto 
    ultimately show "\<Inter> (A\<^sub>n ` insert x F) \<in> \<A>"
      by (metis finite_inter_stable_def fi_stable) 
  qed
qed 

lemma c_fu_imp_fi_stable: 
  assumes c_stable: "complement_stable \<A> \<Omega>"
      and fu_stable: "finite_union_stable \<A>" 
      and subseq: "\<forall>S\<in>\<A>. S \<subseteq> \<Omega>"
    shows "finite_inter_stable \<A>"
proof - 
  have "\<A> \<noteq> {}"
    using c_stable complement_stable_def by auto 

  moreover have "\<forall>A\<in>\<A>.\<forall>B\<in>\<A>. A \<inter> B \<in> \<A>" 
  proof 
    fix A
    assume A_in: "A\<in>\<A>"
    show "\<forall>B\<in>\<A>. A \<inter> B \<in> \<A>"
    proof 
      fix B
      assume "B\<in>\<A>"
      hence "\<Omega>-B \<in> \<A>"
        using c_stable complement_stable_def by fast
      moreover have "\<Omega>-A \<in> \<A>"
        using A_in c_stable complement_stable_def by fast
      ultimately have "(\<Omega>-A) \<union> (\<Omega>-B) \<in> \<A>"
        using fu_stable finite_union_stable_def by fast 
      hence "\<Omega> - (A \<inter> B) \<in> \<A>"
        by (simp add: Diff_Int)
      hence "\<Omega> - (\<Omega> - (A \<inter> B)) \<in> \<A>"
        using c_stable complement_stable_def by fast
      moreover have "\<Omega> - (\<Omega> - (A \<inter> B)) = A \<inter> B"
        using A_in subseq by auto 
      ultimately show "A \<inter> B \<in> \<A>" 
        by simp 
    qed
  qed 
    
  ultimately show ?thesis 
    by (simp add: finite_inter_stable_def) 
qed 

lemma c_fi_imp_fu_stable: 
  assumes c_stable: "complement_stable \<A> \<Omega>"
      and fi_stable: "finite_inter_stable \<A>" 
      and subseq: "\<forall>S\<in>\<A>. S \<subseteq> \<Omega>"
    shows "finite_union_stable \<A>"
proof - 
  have "\<A> \<noteq> {}"
    using c_stable complement_stable_def by auto 

  moreover have "\<forall>A\<in>\<A>.\<forall>B\<in>\<A>. A \<union> B \<in> \<A>" 
  proof 
    fix A
    assume A_in: "A\<in>\<A>"
    show "\<forall>B\<in>\<A>. A \<union> B \<in> \<A>"
    proof 
      fix B
      assume B_in: "B\<in>\<A>"
      hence "\<Omega>-B \<in> \<A>"
        using c_stable complement_stable_def by fast
      moreover have "\<Omega>-A \<in> \<A>"
        using A_in c_stable complement_stable_def by fast
      ultimately have "(\<Omega>-A) \<inter> (\<Omega>-B) \<in> \<A>"
        using fi_stable finite_inter_stable_def by fast 
      hence "\<Omega> - (A \<union> B) \<in> \<A>"
        by (simp add: Diff_Un)
      hence "\<Omega> - (\<Omega> - (A \<union> B)) \<in> \<A>"
        using c_stable complement_stable_def by fast
      moreover have "\<Omega> - (\<Omega> - (A \<union> B)) = A \<union> B"
        using A_in B_in subseq by auto 
      ultimately show "A \<union> B \<in> \<A>" 
        by simp 
    qed
  qed 
    
  ultimately show ?thesis 
    by (simp add: finite_union_stable_def) 
qed

definition set_diff_stable :: "'a set set \<Rightarrow> bool"
  where "set_diff_stable \<A> = ((\<A> \<noteq> {}) \<and> (\<forall>A\<in>\<A>.\<forall>B. (B \<subseteq> A) \<longrightarrow> (A - B \<in> \<A>)))"

definition countable_union_stable :: "'a set set \<Rightarrow> bool"
  where "countable_union_stable \<A> = ((\<A> \<noteq> {}) \<and> (\<forall>A\<^sub>n. (range A\<^sub>n \<subseteq> \<A>) \<longrightarrow> ((\<Union>i::nat. A\<^sub>n i) \<in> \<A>)))"

lemma cu_imp_fu_stable: 
  assumes cu_stable: "countable_union_stable \<A>"
  shows "finite_union_stable \<A>"
proof - 
  have "\<A> \<noteq> {}" 
    using cu_stable countable_union_stable_def by auto 

  moreover have "\<forall>A\<in>\<A>.\<forall>B\<in>\<A>. A \<union> B \<in> \<A>" 
  proof 
    fix A
    assume A_in: "A \<in> \<A>"
    show "\<forall>B\<in>\<A>. A \<union> B \<in> \<A>"
    proof 
      fix B
      let ?A\<^sub>n = "(\<lambda>n. if n = (1::nat) then A else B)"
      let ?U = "(\<Union>i. ?A\<^sub>n i)"
      assume "B \<in> \<A>"
      hence "range ?A\<^sub>n \<subseteq> \<A>"
        using A_in by auto 
      hence "?U \<in> \<A>"
        using cu_stable countable_union_stable_def by metis
      moreover have "?U = A \<union> B" 
      proof 
        show "?U \<subseteq> A \<union> B"
          by simp
      next 
        show "A \<union> B \<subseteq> ?U" 
        proof 
          fix x 
          assume "x \<in> A \<union> B"
          then consider (A) "x \<in> A" | (B) "x \<in> B"
            by fast 
          thus "x \<in> ?U"  
          proof cases
            case A
            hence "x \<in> ?A\<^sub>n 1"
              by simp
            thus ?thesis 
              by fast 
          next
            case B
            hence "x \<in> ?A\<^sub>n 0"
              by simp
            thus ?thesis 
              by fast 
          qed 
        qed
      qed
      ultimately show "A \<union> B \<in> \<A>" 
        by simp 
    qed
  qed

  ultimately show ?thesis 
    using finite_union_stable_def by auto 
qed

definition disj_countable_union_stable :: "'a set set \<Rightarrow> bool"
  where "disj_countable_union_stable \<A> = 
        ((\<A> \<noteq> {}) \<and> (\<forall>A\<^sub>n. (range A\<^sub>n \<subseteq> \<A> \<and> disjoint_family A\<^sub>n) \<longrightarrow> ((\<Union>i::nat. A\<^sub>n i) \<in> \<A>)))"

definition countable_inter_stable :: "'a set set \<Rightarrow> bool"
  where "countable_inter_stable \<A> = ((\<A> \<noteq> {}) \<and> (\<forall>A\<^sub>n. (range A\<^sub>n \<subseteq> \<A>) \<longrightarrow> ((\<Inter>i::nat. A\<^sub>n i) \<in> \<A>)))"

lemma ci_imp_fi_stable: 
  assumes ci_stable: "countable_inter_stable \<A>"
  shows "finite_inter_stable \<A>"
proof - 
  have "\<A> \<noteq> {}" 
    using ci_stable countable_inter_stable_def by auto 

  moreover have "\<forall>A\<in>\<A>.\<forall>B\<in>\<A>. A \<inter> B \<in> \<A>" 
  proof 
    fix A
    assume A_in: "A \<in> \<A>"
    show "\<forall>B\<in>\<A>. A \<inter> B \<in> \<A>"
    proof 
      fix B
      let ?A\<^sub>n = "(\<lambda>n. if n = (1::nat) then A else B)"
      let ?I = "(\<Inter>i. ?A\<^sub>n i)"
      assume "B \<in> \<A>"
      hence "range ?A\<^sub>n \<subseteq> \<A>"
        using A_in by auto 
      hence "?I \<in> \<A>"
        using ci_stable countable_inter_stable_def by metis
      moreover have "?I = A \<inter> B" 
      proof 
        show "?I \<subseteq> A \<inter> B"
        proof 
          fix x 
          assume x_in: "x \<in> ?I"
          hence "\<forall>i. x \<in> ?A\<^sub>n i"
            by fast 
          moreover have "?A\<^sub>n 0 = B \<and> ?A\<^sub>n 1 = A"
            by auto 
          ultimately show "x \<in> A \<inter> B" 
            by fast 
        qed
      next 
        show "A \<inter> B \<subseteq> ?I"
          by auto 
      qed
      ultimately show "A \<inter> B \<in> \<A>" 
        by simp 
    qed
  qed

  ultimately show ?thesis 
    using finite_inter_stable_def by auto 
qed

lemma c_cu_imp_ci_stable: 
  assumes c_stable: "complement_stable \<A> \<Omega>"
      and cu_stable: "countable_union_stable \<A>" 
      and subseq: "\<forall>S\<in>\<A>. S \<subseteq> \<Omega>"
    shows "countable_inter_stable \<A>"
proof - 
  have "\<A> \<noteq> {}"
    using c_stable complement_stable_def by auto 

  moreover have "\<forall>A\<^sub>n. (range A\<^sub>n \<subseteq> \<A>) \<longrightarrow> ((\<Inter>i::nat. A\<^sub>n i) \<in> \<A>)" 
  proof (rule allI; rule impI)
    fix A\<^sub>n :: "nat \<Rightarrow> 'a set"
    assume seq_in: "range A\<^sub>n \<subseteq> \<A>"
    hence "range (\<lambda>n. \<Omega> - A\<^sub>n n) \<subseteq> \<A>"
      using c_stable complement_stable_def by auto
    hence "(\<Union>i::nat. \<Omega> - A\<^sub>n i) \<in> \<A>"
      using countable_union_stable_def cu_stable by metis
    hence "\<Omega> - (\<Union>i::nat. \<Omega> - A\<^sub>n i) \<in> \<A>" 
      using c_stable complement_stable_def by auto

    moreover have "\<forall>i. A\<^sub>n i \<subseteq> \<Omega>"
      using seq_in subseq by auto 
    hence "\<Omega> - (\<Union>i. \<Omega> - A\<^sub>n i) = (\<Inter>i. A\<^sub>n i)" 
      by blast 

    ultimately show "(\<Inter>i::nat. A\<^sub>n i) \<in> \<A>"
      by simp 
  qed 
    
  ultimately show ?thesis
    by (simp add: countable_inter_stable_def) 
qed 

lemma c_ci_imp_cu_stable: 
  assumes c_stable: "complement_stable \<A> \<Omega>"
      and ci_stable: "countable_inter_stable \<A>" 
      and subseq: "\<forall>S\<in>\<A>. S \<subseteq> \<Omega>"
    shows "countable_union_stable \<A>"
proof - 
  have "\<A> \<noteq> {}"
    using c_stable complement_stable_def by auto 

  moreover have "\<forall>A\<^sub>n. (range A\<^sub>n \<subseteq> \<A>) \<longrightarrow> ((\<Union>i::nat. A\<^sub>n i) \<in> \<A>)" 
  proof (rule allI; rule impI)
    fix A\<^sub>n :: "nat \<Rightarrow> 'a set"
    assume seq_in: "range A\<^sub>n \<subseteq> \<A>"
    hence "range (\<lambda>n. \<Omega> - A\<^sub>n n) \<subseteq> \<A>"
      using c_stable complement_stable_def by auto
    hence "(\<Inter>i::nat. \<Omega> - A\<^sub>n i) \<in> \<A>"
      using countable_inter_stable_def ci_stable by metis
    hence "\<Omega> - (\<Inter>i::nat. \<Omega> - A\<^sub>n i) \<in> \<A>" 
      using c_stable complement_stable_def by auto

    moreover have "\<forall>i. A\<^sub>n i \<subseteq> \<Omega>"
      using seq_in subseq by auto 
    hence "\<Omega> - (\<Inter>i. \<Omega> - A\<^sub>n i) = (\<Union>i. A\<^sub>n i)" 
      by blast 

    ultimately show "(\<Union>i::nat. A\<^sub>n i) \<in> \<A>"
      by simp 
  qed 
    
  ultimately show ?thesis
    by (simp add: countable_union_stable_def) 
qed 

definition non_decreasing_union_stable :: "'a set set \<Rightarrow> bool"
  where "non_decreasing_union_stable \<A> = 
        ((\<A> \<noteq> {}) \<and> (\<forall>A\<^sub>n. (range A\<^sub>n \<subseteq> \<A> \<and> non_decreasing A\<^sub>n) \<longrightarrow> ((\<Union>i::nat. A\<^sub>n i) \<in> \<A>)))"

definition non_increasing_inter_stable :: "'a set set \<Rightarrow> bool"
  where "non_increasing_inter_stable \<A> = 
        ((\<A> \<noteq> {}) \<and> (\<forall>A\<^sub>n. (range A\<^sub>n \<subseteq> \<A> \<and> non_increasing A\<^sub>n) \<longrightarrow> ((\<Inter>i::nat. A\<^sub>n i) \<in> \<A>)))"


subsection "Algebras and Systems"

lemma algebra_omega_c_fu_stable: 
  shows "algebra \<Omega> \<A> = (\<A> \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> \<A> \<and> complement_stable \<A> \<Omega> \<and> finite_union_stable \<A>)"
proof 
  assume alg: "algebra \<Omega> \<A>"
  hence "\<A> \<subseteq> Pow \<Omega> \<and> {} \<in> \<A> \<and> complement_stable \<A> \<Omega> \<and> finite_union_stable \<A>"
    using algebra_iff_Un complement_stable_def finite_union_stable_def by fastforce
  moreover have "\<Omega> \<in> \<A>"
    by (simp add: alg algebra.top) 
  ultimately show "\<A> \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> \<A> \<and> complement_stable \<A> \<Omega> \<and> finite_union_stable \<A>" 
    by simp 
next 
  assume "\<A> \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> \<A> \<and> complement_stable \<A> \<Omega> \<and> finite_union_stable \<A>"
  moreover have "{} \<in> \<A>"
    using calculation complement_stable_def Diff_cancel by metis 
  ultimately show "algebra \<Omega> \<A>" 
    by (simp add: algebra_iff_Un complement_stable_def finite_union_stable_def) 
qed 

lemma sigma_algebra_omega_c_cu_stable: 
  shows "sigma_algebra \<Omega> \<A> = (\<A> \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> \<A> \<and> complement_stable \<A> \<Omega> \<and> countable_union_stable \<A>)"
proof -
  have "sigma_algebra \<Omega> \<A> = (algebra \<Omega> \<A> \<and> (\<forall>A\<^sub>n. range A\<^sub>n \<subseteq> \<A> \<longrightarrow> (\<Union>i::nat. A\<^sub>n i) \<in> \<A>))"
    using sigma_algebra_iff by simp 
  hence "sigma_algebra \<Omega> \<A> = (\<A> \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> \<A> \<and> complement_stable \<A> \<Omega> \<and> finite_union_stable \<A>
        \<and> (\<forall>A\<^sub>n. range A\<^sub>n \<subseteq> \<A> \<longrightarrow> (\<Union>i::nat. A\<^sub>n i) \<in> \<A>))"
    by (simp add: algebra_omega_c_fu_stable)
  thus ?thesis
    by (metis countable_union_stable_def empty_iff cu_imp_fu_stable)
qed

end