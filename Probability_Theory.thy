theory Probability_Theory 
  imports "HOL-Analysis.Sigma_Algebra"
begin

chapter "Basics from Measure Theory"

section "Sets"

subsection "Set operations"

definition non_decreasing :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool"
  where "non_decreasing A \<equiv> \<forall>n. A n \<subseteq> A (n + 1)"

lemma non_decreasing_multistep: 
  assumes non_dec: "non_decreasing A"
      and leq: "n \<le> m"
    shows "A n \<subseteq> A m"
proof - 
  have "\<forall>n y. y \<in> A n \<longrightarrow> y \<in> A (Suc n)"
    using non_dec non_decreasing_def Suc_eq_plus1 subset_iff by metis
  hence "\<forall>n. \<forall>d\<ge>0. (A n \<subseteq> A (n+d))" 
      using add.commute le_add2 lift_Suc_mono_le subset_iff by metis
  thus "A n \<subseteq> A m"
    by (metis bot_nat_0.extremum le_iff_add leq)
qed 

lemma non_decreasing_stay_in: 
  assumes non_dec: "non_decreasing A"
      and base: "x \<in> A n"
    shows "\<forall>m\<ge>n. x \<in> A m"
  using base non_dec non_decreasing_multistep by auto


definition non_increasing :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool"
  where "non_increasing A \<equiv> \<forall>n. A (n + 1) \<subseteq> A n"

lemma non_increasing_multistep: 
  assumes non_inc: "non_increasing A"
      and leq: "n \<le> m"
    shows "A m \<subseteq> A n"
proof - 
  have "\<forall>n y. y \<in> A (Suc n) \<longrightarrow> y \<in> A n"
    using non_inc non_increasing_def Suc_eq_plus1 subset_iff by metis
  hence "\<forall>n. \<forall>d\<ge>0. (A (n+d) \<subseteq> A n)" 
      using add.commute le_add2 subset_iff lift_Suc_antimono_le by metis 
  thus "A m \<subseteq> A n"
    by (metis bot_nat_0.extremum le_iff_add leq)
qed 

lemma non_increasing_stay_out: 
  assumes non_inc: "non_increasing A"
      and base: "x \<notin> A n"
    shows "\<forall>m\<ge>n. x \<notin> A m"
  using base non_inc non_increasing_multistep by auto


subsection "Limits of Sets"

definition liminf :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
  where "liminf A = (\<Union>n. (\<Inter>m\<in>{m'. m' \<ge> n}. A m))"

lemma liminf_greater_n: "(x \<in> liminf A) = (\<exists>n.\<forall>m\<ge>n. x \<in> A m)"
  by (simp add: liminf_def) 

definition limsup :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
  where "limsup A = (\<Inter>n. (\<Union>m\<in>{m'. m' \<ge> n}. A m))"

lemma limsup_greater_n: "(x \<in> limsup A) = (\<forall>n.\<exists>m\<ge>n. x \<in> A m)"
  by (simp add: limsup_def) 

lemma liminf_subseq_limsup: "liminf A \<subseteq> limsup A"
proof 
  fix x 
  assume "x \<in> liminf A"
  hence "\<exists>n.\<forall>m\<ge>n. x \<in> A m"
    by (simp add: liminf_greater_n)
  hence "\<forall>n.\<exists>m\<ge>n. x \<in> A m"
    by (metis nat_le_linear)
  thus "x \<in> limsup A"
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
  assumes non_decreasing: "non_decreasing A"
  shows "set_limit A = \<Union>(range A)" 
proof - 
  have "limsup A = \<Union>(range A)" 
  proof 
    show "limsup A \<subseteq> \<Union>(range A)"
    proof 
      fix x 
      assume "x \<in> limsup A"
      hence "(\<exists>m. m \<ge> 1 \<and> x \<in> A m)"
        by (simp add: limsup_greater_n) 
      thus "x \<in> \<Union>(range A)"
        by auto 
    qed
  next 
    show "\<Union>(range A) \<subseteq> limsup A"
    proof 
      fix x 
      assume "x \<in> \<Union>(range A)" 
      then obtain n where "x \<in> A n" 
        by auto 
      hence "\<forall>m\<ge>n. x \<in> A m"
        by (meson non_decreasing non_decreasing_stay_in)
      thus "x \<in> limsup A"
        by (meson limsup_greater_n nat_le_linear) 
    qed
  qed

  moreover have "limsup A = liminf A" 
  proof - 
    have "limsup A \<subseteq> liminf A"
    proof 
      fix x 
      assume "x \<in> limsup A"
      hence "\<forall>n.\<exists>m\<ge>n. x \<in> A m"
        by (simp add: limsup_greater_n)
      hence "\<exists>n.\<forall>m\<ge>n. x \<in> A m"
        by (meson non_decreasing non_decreasing_stay_in)
      thus "x \<in> liminf A"
        by (simp add: liminf_greater_n)
    qed
    thus ?thesis
      using liminf_limsup_eq_cond by auto 
  qed

  ultimately show ?thesis
    by (simp add: set_limit_eq_limsup) 
qed

proposition non_increasing_set_limit: 
  assumes non_increasing: "non_increasing A"
  shows "set_limit A = \<Inter>(range A)" 
proof - 
  have "limsup A = \<Inter>(range A)" 
  proof 
    show "limsup A \<subseteq> \<Inter>(range A)"
    proof 
      fix x 
      assume "x \<in> limsup A"
      hence "\<forall>n. \<exists>m. m \<ge> n \<and> x \<in> A m"
        by (simp add: limsup_greater_n) 
      hence "\<forall>m. x \<in> A m"
        using non_increasing non_increasing_stay_out by metis 
      thus "x \<in> \<Inter>(range A)"
        by simp 
    qed
  next 
    show "\<Inter>(range A) \<subseteq> limsup A"
    proof 
      fix x 
      assume "x \<in> \<Inter>(range A)" 
      hence "\<forall>m. x \<in> A m"
        by simp 
      thus "x \<in> limsup A"
        by (meson limsup_greater_n nat_le_linear) 
    qed
  qed

  moreover have "limsup A = liminf A" 
  proof - 
    have "limsup A \<subseteq> liminf A"
    proof 
      fix x 
      assume "x \<in> limsup A"
      hence "\<forall>n. \<exists>m. m \<ge> n \<and> x \<in> A m"
        by (simp add: limsup_greater_n)
      hence "\<exists>n. \<forall>k\<ge>n. x \<in> A k"
        by (meson non_increasing non_increasing_stay_out)
      thus "x \<in> liminf A"
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
  where "complement_stable M \<Omega> = ((M \<noteq> {}) \<and> (\<forall>S\<in>M. \<Omega> - S \<in> M))"

definition finite_union_stable :: "'a set set \<Rightarrow> bool"
  where "finite_union_stable M = ((M \<noteq> {}) \<and> (\<forall>S\<in>M.\<forall>T\<in>M. S \<union> T \<in> M))"

lemma fu_stable_finite: 
  assumes fu_stable: "finite_union_stable M"
      and family_in: "\<forall>i\<in>I. A i \<in> M"
      and finite: "finite I"
      and non_empty: "I \<noteq> {}"
    shows "(\<Union>i\<in>I. A i) \<in> M"
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
    hence "\<Union> (A ` insert x F) = A x"
      by simp
    then show "\<Union> (A ` insert x F) \<in> M"
      by (simp add: insert.prems(2)) 
  next
    case False
    hence "(\<Union>i\<in>F. A i) \<in> M"
      by (simp add: fu_stable insert.IH insert.prems(2)) 
    moreover have "A x \<in> M"
      by (simp add: insert.prems(2))
    moreover have "\<Union> (A ` insert x F) = (\<Union>i\<in>F. A i) \<union> (A x)"
      by auto 
    ultimately show "\<Union> (A ` insert x F) \<in> M"
      by (metis finite_union_stable_def fu_stable) 
  qed
qed 
    

definition finite_inter_stable :: "'a set set \<Rightarrow> bool"
  where "finite_inter_stable M = ((M \<noteq> {}) \<and> (\<forall>S\<in>M.\<forall>T\<in>M. S \<inter> T \<in> M))"

lemma fi_stable_finite: 
  assumes fi_stable: "finite_inter_stable M"
      and family_in: "\<forall>i\<in>I. A i \<in> M"
      and finite: "finite I"
      and non_empty: "I \<noteq> {}"
    shows "(\<Inter>i\<in>I. A i) \<in> M"
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
    hence "\<Inter> (A ` insert x F) = A x"
      by simp
    then show "\<Inter> (A ` insert x F) \<in> M"
      by (simp add: insert.prems(2)) 
  next
    case False
    hence "(\<Inter>i\<in>F. A i) \<in> M"
      by (simp add: fi_stable insert.IH insert.prems(2)) 
    moreover have "A x \<in> M"
      by (simp add: insert.prems(2))
    moreover have "\<Inter> (A ` insert x F) = (\<Inter>i\<in>F. A i) \<inter> (A x)"
      by auto 
    ultimately show "\<Inter> (A ` insert x F) \<in> M"
      by (metis finite_inter_stable_def fi_stable) 
  qed
qed 

lemma c_fu_imp_fi_stable: 
  assumes c_stable: "complement_stable M \<Omega>"
      and fu_stable: "finite_union_stable M" 
      and subseq: "\<forall>S\<in>M. S \<subseteq> \<Omega>"
    shows "finite_inter_stable M"
proof - 
  have "M \<noteq> {}"
    using c_stable complement_stable_def by auto 

  moreover have "\<forall>S\<in>M.\<forall>T\<in>M. S \<inter> T \<in> M" 
  proof 
    fix S
    assume S_in: "S\<in>M"
    show "\<forall>T\<in>M. S \<inter> T \<in> M"
    proof 
      fix T
      assume "T\<in>M"
      hence "\<Omega>-T \<in> M"
        using c_stable complement_stable_def by fast
      moreover have "\<Omega>-S \<in> M"
        using S_in c_stable complement_stable_def by fast
      ultimately have "(\<Omega>-S) \<union> (\<Omega>-T) \<in> M"
        using fu_stable finite_union_stable_def by fast 
      hence "\<Omega> - (S \<inter> T) \<in> M"
        by (simp add: Diff_Int)
      hence "\<Omega> - (\<Omega> - (S \<inter> T)) \<in> M"
        using c_stable complement_stable_def by fast
      moreover have "\<Omega> - (\<Omega> - (S \<inter> T)) = S \<inter> T"
        using S_in subseq by auto 
      ultimately show "S \<inter> T \<in> M" 
        by simp 
    qed
  qed 
    
  ultimately show ?thesis 
    by (simp add: finite_inter_stable_def) 
qed 

lemma c_fi_imp_fu_stable: 
  assumes c_stable: "complement_stable M \<Omega>"
      and fi_stable: "finite_inter_stable M" 
      and subseq: "\<forall>S\<in>M. S \<subseteq> \<Omega>"
    shows "finite_union_stable M"
proof - 
  have "M \<noteq> {}"
    using c_stable complement_stable_def by auto 

  moreover have "\<forall>S\<in>M.\<forall>T\<in>M. S \<union> T \<in> M" 
  proof 
    fix S
    assume S_in: "S\<in>M"
    show "\<forall>T\<in>M. S \<union> T \<in> M"
    proof 
      fix T
      assume T_in: "T\<in>M"
      hence "\<Omega>-T \<in> M"
        using c_stable complement_stable_def by fast
      moreover have "\<Omega>-S \<in> M"
        using S_in c_stable complement_stable_def by fast
      ultimately have "(\<Omega>-S) \<inter> (\<Omega>-T) \<in> M"
        using fi_stable finite_inter_stable_def by fast 
      hence "\<Omega> - (S \<union> T) \<in> M"
        by (simp add: Diff_Un)
      hence "\<Omega> - (\<Omega> - (S \<union> T)) \<in> M"
        using c_stable complement_stable_def by fast
      moreover have "\<Omega> - (\<Omega> - (S \<union> T)) = S \<union> T"
        using S_in T_in subseq by auto 
      ultimately show "S \<union> T \<in> M" 
        by simp 
    qed
  qed 
    
  ultimately show ?thesis 
    by (simp add: finite_union_stable_def) 
qed

definition set_diff_stable :: "'a set set \<Rightarrow> bool"
  where "set_diff_stable M = ((M \<noteq> {}) \<and> (\<forall>S\<in>M.\<forall>T. (T \<subseteq> S) \<longrightarrow> (S - T \<in> M)))"

definition countable_union_stable :: "'a set set \<Rightarrow> bool"
  where "countable_union_stable M = ((M \<noteq> {}) \<and> (\<forall>A. (range A \<subseteq> M) \<longrightarrow> ((\<Union>i::nat. A i) \<in> M)))"

lemma cu_imp_fu_stable: 
  assumes cu_stable: "countable_union_stable M"
  shows "finite_union_stable M"
proof - 
  have "M \<noteq> {}" 
    using cu_stable countable_union_stable_def by auto 

  moreover have "\<forall>S\<in>M.\<forall>T\<in>M. S \<union> T \<in> M" 
  proof 
    fix S
    assume S_in: "S \<in> M"
    show "\<forall>T\<in>M. S \<union> T \<in> M"
    proof 
      fix T
      let ?A = "(\<lambda>n. if n = (1::nat) then S else T)"
      let ?U = "(\<Union>i. ?A i)"
      assume "T \<in> M"
      hence "range ?A \<subseteq> M"
        using S_in by auto 
      hence "?U \<in> M"
        using cu_stable countable_union_stable_def by metis
      moreover have "?U = S \<union> T" 
      proof 
        show "?U \<subseteq> S \<union> T"
          by simp
      next 
        show "S \<union> T \<subseteq> ?U" 
        proof 
          fix x 
          assume "x \<in> S \<union> T"
          then consider (S) "x \<in> S" | (T) "x \<in> T"
            by fast 
          thus "x \<in> ?U"  
          proof cases
            case S
            hence "x \<in> ?A 1"
              by simp
            thus ?thesis 
              by fast 
          next
            case T
            hence "x \<in> ?A 0"
              by simp
            thus ?thesis 
              by fast 
          qed 
        qed
      qed
      ultimately show "S \<union> T \<in> M" 
        by simp 
    qed
  qed

  ultimately show ?thesis 
    using finite_union_stable_def by auto 
qed

definition disj_countable_union_stable :: "'a set set \<Rightarrow> bool"
  where "disj_countable_union_stable M = 
        ((M \<noteq> {}) \<and> (\<forall>A. (range A \<subseteq> M \<and> disjoint_family A) \<longrightarrow> ((\<Union>i::nat. A i) \<in> M)))"

definition countable_inter_stable :: "'a set set \<Rightarrow> bool"
  where "countable_inter_stable M = ((M \<noteq> {}) \<and> (\<forall>A. (range A \<subseteq> M) \<longrightarrow> ((\<Inter>i::nat. A i) \<in> M)))"

lemma ci_imp_fi_stable: 
  assumes ci_stable: "countable_inter_stable M"
  shows "finite_inter_stable M"
proof - 
  have "M \<noteq> {}" 
    using ci_stable countable_inter_stable_def by auto 

  moreover have "\<forall>S\<in>M.\<forall>T\<in>M. S \<inter> T \<in> M" 
  proof 
    fix S
    assume S_in: "S \<in> M"
    show "\<forall>T\<in>M. S \<inter> T \<in> M"
    proof 
      fix T
      let ?A = "(\<lambda>n. if n = (1::nat) then S else T)"
      let ?U = "(\<Inter>i. ?A i)"
      assume "T \<in> M"
      hence "range ?A \<subseteq> M"
        using S_in by auto 
      hence "?U \<in> M"
        using ci_stable countable_inter_stable_def by metis
      moreover have "?U = S \<inter> T" 
      proof 
        show "?U \<subseteq> S \<inter> T"
        proof 
          fix x 
          assume x_in: "x \<in> ?U"
          hence "\<forall>i. x \<in> ?A i"
            by fast 
          moreover have "?A 0 = T \<and> ?A 1 = S"
            by auto 
          ultimately show "x \<in> S \<inter> T" 
            by fast 
        qed
      next 
        show "S \<inter> T \<subseteq> ?U"
          by auto 
      qed
      ultimately show "S \<inter> T \<in> M" 
        by simp 
    qed
  qed

  ultimately show ?thesis 
    using finite_inter_stable_def by auto 
qed

lemma c_cu_imp_ci_stable: 
  assumes c_stable: "complement_stable M \<Omega>"
      and cu_stable: "countable_union_stable M" 
      and subseq: "\<forall>S\<in>M. S \<subseteq> \<Omega>"
    shows "countable_inter_stable M"
proof - 
  have "M \<noteq> {}"
    using c_stable complement_stable_def by auto 

  moreover have "\<forall>A. (range A \<subseteq> M) \<longrightarrow> ((\<Inter>i::nat. A i) \<in> M)" 
  proof (rule allI; rule impI)
    fix A :: "nat \<Rightarrow> 'a set"
    assume seq_in: "range A \<subseteq> M"
    hence "range (\<lambda>n. \<Omega> - A n) \<subseteq> M"
      using c_stable complement_stable_def by auto
    hence "(\<Union>i::nat. \<Omega> - A i) \<in> M"
      using countable_union_stable_def cu_stable by metis
    hence "\<Omega> - (\<Union>i::nat. \<Omega> - A i) \<in> M" 
      using c_stable complement_stable_def by auto

    moreover have "\<forall>i. A i \<subseteq> \<Omega>"
      using seq_in subseq by auto 
    hence "\<Omega> - (\<Union>i. \<Omega> - A i) = (\<Inter>i. A i)" 
      by blast 

    ultimately show "(\<Inter>i::nat. A i) \<in> M"
      by simp 
  qed 
    
  ultimately show ?thesis
    by (simp add: countable_inter_stable_def) 
qed 

lemma c_ci_imp_cu_stable: 
  assumes c_stable: "complement_stable M \<Omega>"
      and ci_stable: "countable_inter_stable M" 
      and subseq: "\<forall>S\<in>M. S \<subseteq> \<Omega>"
    shows "countable_union_stable M"
proof - 
  have "M \<noteq> {}"
    using c_stable complement_stable_def by auto 

  moreover have "\<forall>A. (range A \<subseteq> M) \<longrightarrow> ((\<Union>i::nat. A i) \<in> M)" 
  proof (rule allI; rule impI)
    fix A :: "nat \<Rightarrow> 'a set"
    assume seq_in: "range A \<subseteq> M"
    hence "range (\<lambda>n. \<Omega> - A n) \<subseteq> M"
      using c_stable complement_stable_def by auto
    hence "(\<Inter>i::nat. \<Omega> - A i) \<in> M"
      using countable_inter_stable_def ci_stable by metis
    hence "\<Omega> - (\<Inter>i::nat. \<Omega> - A i) \<in> M" 
      using c_stable complement_stable_def by auto

    moreover have "\<forall>i. A i \<subseteq> \<Omega>"
      using seq_in subseq by auto 
    hence "\<Omega> - (\<Inter>i. \<Omega> - A i) = (\<Union>i. A i)" 
      by blast 

    ultimately show "(\<Union>i::nat. A i) \<in> M"
      by simp 
  qed 
    
  ultimately show ?thesis
    by (simp add: countable_union_stable_def) 
qed 

definition non_decreasing_union_stable :: "'a set set \<Rightarrow> bool"
  where "non_decreasing_union_stable M = 
        ((M \<noteq> {}) \<and> (\<forall>A. (range A \<subseteq> M \<and> non_decreasing A) \<longrightarrow> ((\<Union>i::nat. A i) \<in> M)))"

definition non_increasing_inter_stable :: "'a set set \<Rightarrow> bool"
  where "non_increasing_inter_stable M = 
        ((M \<noteq> {}) \<and> (\<forall>A. (range A \<subseteq> M \<and> non_increasing A) \<longrightarrow> ((\<Inter>i::nat. A i) \<in> M)))"


subsection "Algebras and Systems"

lemma algebra_omega_c_fu_stable: 
  shows "algebra \<Omega> M = (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable M \<Omega> \<and> finite_union_stable M)"
proof 
  assume alg: "algebra \<Omega> M"
  hence "M \<subseteq> Pow \<Omega> \<and> {} \<in> M \<and> complement_stable M \<Omega> \<and> finite_union_stable M"
    using algebra_iff_Un complement_stable_def finite_union_stable_def by fastforce
  moreover have "\<Omega> \<in> M"
    by (simp add: alg algebra.top) 
  ultimately show "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable M \<Omega> \<and> finite_union_stable M" 
    by simp 
next 
  assume "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable M \<Omega> \<and> finite_union_stable M"
  moreover have "{} \<in> M"
    using calculation complement_stable_def Diff_cancel by metis 
  ultimately show "algebra \<Omega> M" 
    by (simp add: algebra_iff_Un complement_stable_def finite_union_stable_def) 
qed 

lemma sigma_algebra_omega_c_cu_stable: 
  shows "sigma_algebra \<Omega> M = (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable M \<Omega> \<and> countable_union_stable M)"
proof -
  have "sigma_algebra \<Omega> M = (algebra \<Omega> M \<and> (\<forall>A. range A \<subseteq> M \<longrightarrow> (\<Union>i::nat. A i) \<in> M))"
    using sigma_algebra_iff by simp 
  hence "sigma_algebra \<Omega> M = (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable M \<Omega> \<and> finite_union_stable M
        \<and> (\<forall>A. range A \<subseteq> M \<longrightarrow> (\<Union>i::nat. A i) \<in> M))"
    by (simp add: algebra_omega_c_fu_stable)
  thus ?thesis
    by (metis countable_union_stable_def empty_iff cu_imp_fu_stable)
qed

locale monotone_class = subset_class + 
  assumes ndu_stable: "non_decreasing_union_stable M"
      and ncdi_stable: "non_increasing_inter_stable M"

end