theory Probability_Theory 
  imports "HOL-Analysis.Sigma_Algebra"
begin

chapter "Basics from Measure Theory"

section "Sets"

subsection "Set operations"

text "Some sequences of sets behave monotonically with respect to the partial order of subsets."

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

text "Let's think about what the limit of a sequence of sets could be. 
Whatever it is, it should at least contain those elements that eventually occur in every 
single set of the sequence after some finite cutoff. 

We call this minimal notion of a limit liminf."

definition liminf :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
  where "liminf A = (\<Union>n. (\<Inter>m\<in>{m'. m' \<ge> n}. A m))"

lemma liminf_greater_n: "(x \<in> liminf A) = (\<exists>n.\<forall>m\<ge>n. x \<in> A m)"
  by (simp add: liminf_def) 

text "Any sensible limit of a sequence of sets should include at least the elements of liminf.
On the other hand, the limit should certainly not include any elements that do not occur in even a 
single set after some finite cutoff.

In other words, limsup contains all elements that, no matter how sparsely they may occur, never
stop appearing as elements of sets in the sequence indefinitely. Elements that are not in this set
should certainly not be a part of a any sensible limit of a sequence of sets."

definition limsup :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
  where "limsup A = (\<Inter>n. (\<Union>m\<in>{m'. m' \<ge> n}. A m))"

lemma limsup_greater_n: "(x \<in> limsup A) = (\<forall>n.\<exists>m\<ge>n. x \<in> A m)"
  by (simp add: limsup_def) 

text "Reassuringly, liminf, our favourite selection of elements that have to be in the limiting set,
does not contain any elements that we have categorically excluded on pain of them not occuring in limsup.

This is expected. Elements that eventually appear in every set do not disappear indefinitely."

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

text "It's handy to notice that, if we wanted to know whether liminf and limsup are the same, say
to define an unambiguous limit, we would only have to check whether liminf contains all elements 
of limsup."

lemma liminf_limsup_eq_cond: 
  assumes limsup_subseq_liminf: "limsup A \<subseteq> liminf A" 
  shows "liminf A = limsup A"
  by (simp add: limsup_subseq_liminf liminf_subseq_limsup subset_antisym)

text "At the end of the day, it could reasonably be argued in favour of or against excluding 
elements that are not in liminf, and elements that are not in limsup in our 'limit'. 
Because we don't want to argue with anyone, we only define the limit in the case that it is uniquely
determined by the two rules we have proposed."

definition set_limit :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
  where "set_limit A = (THE S. S = liminf A \<and> S = limsup A)"

text "If the limit exists, it's then equal to both candidates. No surprise."

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

text "There are two more or less obvious cases of when a set limit exists. 

If all elements that appear in some set of the sequence also appear at all greater indices,
any element that doesn't disappear from the sequence indefinitely will eventually start appearing 
forever. Then the limit of the sequence is equal to the set of all elements that ever appear in
a set of the sequence, as those are also the ones that appear forever."

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

text "Secondly, if any element that disappears from the sequence is gone for good, all elements 
that do not stop appearing forever (limsup) necessarily have to occur at every single index,
which means they're in liminf. Notably, this limit has the property that all elements in the limit
appear at every single index of the sequence.

[There's some antisymmetry here. The elements not in the limit in the non-decreasing case had a 
similar property, but with respect to being outside the sequence at every index from 0 to infinity.

I wonder if, if a set collection is closed under complements and non-decreasing unions, 
they are also closed under non-increasing intersections. I think so, because given the intersection
of a nonincreasing sequence of sets, the sequence of its complements is non-decreasing. 
The limit of that sequence is in the collection. Hence, so is its complement. And that's the limit
of the initial sequence, as suggested by the antisymmetry above. 

Sigma algebras are like that. So sigma algebras are monotone classes. Neat.]"

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

subsection "Auxiliary lemmas"

text "Every non-empty set of natural numbers has a least element."
lemma min_nat_elem: 
  assumes non_empty: "\<exists>n::nat. n \<in> S" 
  shows "\<exists>n. n \<in> S \<and> (\<forall>m\<in>S. m \<ge> n)" 
proof -
  obtain P where P_fun: "P = (\<lambda>n. n \<in> S)"
    by simp
  have "(\<exists>n. P n) = (\<exists>n. P n \<and> (\<forall>m<n. \<not> P m))"
    using exists_least_iff by auto
  thus ?thesis using P_fun non_empty
    using leI by auto
qed 

subsection "Rules for Collections of Sets"

text "Set collections are commonly selected according to whether they are closed under certain 
operations.  
A collection of sets may, for instance, be closed under 
(i) The complement.
(ii) Finite unions.
(iii) Finite intersections.

Note: (i), (ii) and (i), (iii) are equivalent, due to deMorgan's formulas.

Note: We defined (ii) and (iii) with just a normal binary union / intersection. That's enough, it
      follows for all finite families by induction.

(iv) Set differences with respect to ones subset, provided that it's also in the collection 

Note: If the subsets we want to be able to remove weren't required to be in the collection, this
      condition would just mean 'closed under taking subsets'. 

(v) Countable unions.
(vi) Countable union of a family of sets as long as it is disjoint. 

Note: This does not hold for finite, disjoint unions unless {} is in the set. That is because
      there may be no infinite disjoint sequences of sets in the collection. 

(vii) Countable intersections.

Note: Yes, (i), (v) and (i), (vii) are also equivalent, also deMorgan.

Note: If a set is closed under countable un./in., it is of course so under finite ones as well.

(viii) The (countable) union (limit!) of non-decreasing sequences of sets.
(ix) The (countable) intersection (limit!) of non-increasing sequences of sets. 
"

subsubsection "Complements, finite unions and intersections"

definition complement_closed :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool"
  where "complement_closed \<Omega> M = ((M \<noteq> {}) \<and> (\<forall>S\<in>M. \<Omega> - S \<in> M))"

definition finite_union_closed :: "'a set set \<Rightarrow> bool"
  where "finite_union_closed M = ((M \<noteq> {}) \<and> (\<forall>S\<in>M.\<forall>T\<in>M. S \<union> T \<in> M))"

lemma fu_closed_finite: 
  assumes fu_closed: "finite_union_closed M"
      and family_in: "\<forall>i\<in>I. A i \<in> M"
      and finite: "finite I"
      and non_empty: "I \<noteq> {}"
    shows "(\<Union>i\<in>I. A i) \<in> M"
  using finite non_empty family_in fu_closed
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
      by (simp add: fu_closed insert.IH insert.prems(2)) 
    moreover have "A x \<in> M"
      by (simp add: insert.prems(2))
    moreover have "\<Union> (A ` insert x F) = (\<Union>i\<in>F. A i) \<union> (A x)"
      by auto 
    ultimately show "\<Union> (A ` insert x F) \<in> M"
      by (metis finite_union_closed_def fu_closed) 
  qed
qed 
    

definition finite_inter_closed :: "'a set set \<Rightarrow> bool"
  where "finite_inter_closed M = ((M \<noteq> {}) \<and> (\<forall>S\<in>M.\<forall>T\<in>M. S \<inter> T \<in> M))"

lemma fi_closed_finite: 
  assumes fi_closed: "finite_inter_closed M"
      and family_in: "\<forall>i\<in>I. A i \<in> M"
      and finite: "finite I"
      and non_empty: "I \<noteq> {}"
    shows "(\<Inter>i\<in>I. A i) \<in> M"
  using finite non_empty family_in fi_closed
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
      by (simp add: fi_closed insert.IH insert.prems(2)) 
    moreover have "A x \<in> M"
      by (simp add: insert.prems(2))
    moreover have "\<Inter> (A ` insert x F) = (\<Inter>i\<in>F. A i) \<inter> (A x)"
      by auto 
    ultimately show "\<Inter> (A ` insert x F) \<in> M"
      by (metis finite_inter_closed_def fi_closed) 
  qed
qed 

lemma c_fu_imp_fi_closed: 
  assumes c_closed: "complement_closed \<Omega> M"
      and fu_closed: "finite_union_closed M" 
      and subseq: "\<forall>S\<in>M. S \<subseteq> \<Omega>"
    shows "finite_inter_closed M"
proof - 
  have "M \<noteq> {}"
    using c_closed complement_closed_def by auto 

  moreover have "\<forall>S\<in>M.\<forall>T\<in>M. S \<inter> T \<in> M" 
  proof 
    fix S
    assume S_in: "S\<in>M"
    show "\<forall>T\<in>M. S \<inter> T \<in> M"
    proof 
      fix T
      assume "T\<in>M"
      hence "\<Omega>-T \<in> M"
        using c_closed complement_closed_def by fast
      moreover have "\<Omega>-S \<in> M"
        using S_in c_closed complement_closed_def by fast
      ultimately have "(\<Omega>-S) \<union> (\<Omega>-T) \<in> M"
        using fu_closed finite_union_closed_def by fast 
      hence "\<Omega> - (S \<inter> T) \<in> M"
        by (simp add: Diff_Int)
      hence "\<Omega> - (\<Omega> - (S \<inter> T)) \<in> M"
        using c_closed complement_closed_def by fast
      moreover have "\<Omega> - (\<Omega> - (S \<inter> T)) = S \<inter> T"
        using S_in subseq by auto 
      ultimately show "S \<inter> T \<in> M" 
        by simp 
    qed
  qed 
    
  ultimately show ?thesis 
    by (simp add: finite_inter_closed_def) 
qed 

lemma c_fi_imp_fu_closed: 
  assumes c_closed: "complement_closed \<Omega> M"
      and fi_closed: "finite_inter_closed M" 
      and subseq: "\<forall>S\<in>M. S \<subseteq> \<Omega>"
    shows "finite_union_closed M"
proof - 
  have "M \<noteq> {}"
    using c_closed complement_closed_def by auto 

  moreover have "\<forall>S\<in>M.\<forall>T\<in>M. S \<union> T \<in> M" 
  proof 
    fix S
    assume S_in: "S\<in>M"
    show "\<forall>T\<in>M. S \<union> T \<in> M"
    proof 
      fix T
      assume T_in: "T\<in>M"
      hence "\<Omega>-T \<in> M"
        using c_closed complement_closed_def by fast
      moreover have "\<Omega>-S \<in> M"
        using S_in c_closed complement_closed_def by fast
      ultimately have "(\<Omega>-S) \<inter> (\<Omega>-T) \<in> M"
        using fi_closed finite_inter_closed_def by fast 
      hence "\<Omega> - (S \<union> T) \<in> M"
        by (simp add: Diff_Un)
      hence "\<Omega> - (\<Omega> - (S \<union> T)) \<in> M"
        using c_closed complement_closed_def by fast
      moreover have "\<Omega> - (\<Omega> - (S \<union> T)) = S \<union> T"
        using S_in T_in subseq by auto 
      ultimately show "S \<union> T \<in> M" 
        by simp 
    qed
  qed 
    
  ultimately show ?thesis 
    by (simp add: finite_union_closed_def) 
qed

subsubsection "Set Difference"

definition set_diff_closed :: "'a set set \<Rightarrow> bool"
  where "set_diff_closed M = ((M \<noteq> {}) \<and> (\<forall>S\<in>M.\<forall>T\<in>M. (T \<subseteq> S) \<longrightarrow> (S - T \<in> M)))"

lemma sd_omega_imp_c_closed: 
  assumes sd_closed: "set_diff_closed M"
      and omega: "\<Omega> \<in> M"
      and M_pow: "M \<subseteq> Pow \<Omega>"
    shows "complement_closed \<Omega> M"
proof - 
  have "M \<noteq> {}"
    using omega by auto
  moreover have "\<forall>S\<in>M. \<Omega> - S \<in> M"
    by (meson M_pow PowD in_mono omega sd_closed set_diff_closed_def)
  ultimately show ?thesis
    by (simp add: complement_closed_def) 
qed

lemma c_fu_omega_imp_sd_closed:
  assumes c_closed: "complement_closed \<Omega> M" 
      and fu_closed: "finite_union_closed M"
      and omega: "\<Omega> \<in> M"
      and M_pow: "M \<subseteq> Pow \<Omega>"
    shows "set_diff_closed M"
proof - 
  have "M \<noteq> {}"
    using omega by auto
  moreover have "\<forall>S\<in>M. \<forall>T\<in>M. T \<subseteq> S \<longrightarrow> S - T \<in> M"
  proof (rule ; rule ; rule) 
    fix S T :: "'a set"
    assume T_M: "T \<in> M" and S_M: "S \<in> M" and T_S: "T \<subseteq> S"
    hence "S - T = \<Omega> - ((\<Omega> - S) \<union> T)"
      using M_pow by auto
    moreover have "\<Omega> - S \<in> M"
      using S_M c_closed complement_closed_def by blast
    hence "(\<Omega> - S) \<union> T \<in> M"
      using T_M fu_closed unfolding finite_union_closed_def by simp 
    ultimately show "S - T \<in> M"  
      using c_closed M_pow unfolding complement_closed_def by simp 
  qed 
  ultimately show ?thesis 
    unfolding set_diff_closed_def by auto 
qed
  

subsubsection "Countable unions and intersections"

definition countable_union_closed :: "'a set set \<Rightarrow> bool"
  where "countable_union_closed M = ((M \<noteq> {}) \<and> (\<forall>A. (range A \<subseteq> M) \<longrightarrow> ((\<Union>i::nat. A i) \<in> M)))"

lemma cu_imp_fu_closed: 
  assumes cu_closed: "countable_union_closed M"
  shows "finite_union_closed M"
proof - 
  have "M \<noteq> {}" 
    using cu_closed countable_union_closed_def by auto 

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
        using cu_closed countable_union_closed_def by metis
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
    using finite_union_closed_def by auto 
qed

definition countable_inter_closed :: "'a set set \<Rightarrow> bool"
  where "countable_inter_closed M = ((M \<noteq> {}) \<and> (\<forall>A. (range A \<subseteq> M) \<longrightarrow> ((\<Inter>i::nat. A i) \<in> M)))"

lemma ci_imp_fi_closed: 
  assumes ci_closed: "countable_inter_closed M"
  shows "finite_inter_closed M"
proof - 
  have "M \<noteq> {}" 
    using ci_closed countable_inter_closed_def by auto 

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
        using ci_closed countable_inter_closed_def by metis
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
    using finite_inter_closed_def by auto 
qed

lemma c_cu_imp_ci_closed: 
  assumes c_closed: "complement_closed \<Omega> M"
      and cu_closed: "countable_union_closed M" 
      and subseq: "\<forall>S\<in>M. S \<subseteq> \<Omega>"
    shows "countable_inter_closed M"
proof - 
  have "M \<noteq> {}"
    using c_closed complement_closed_def by auto 

  moreover have "\<forall>A. (range A \<subseteq> M) \<longrightarrow> ((\<Inter>i::nat. A i) \<in> M)" 
  proof (rule allI; rule impI)
    fix A :: "nat \<Rightarrow> 'a set"
    assume seq_in: "range A \<subseteq> M"
    hence "range (\<lambda>n. \<Omega> - A n) \<subseteq> M"
      using c_closed complement_closed_def by auto
    hence "(\<Union>i::nat. \<Omega> - A i) \<in> M"
      using countable_union_closed_def cu_closed by metis
    hence "\<Omega> - (\<Union>i::nat. \<Omega> - A i) \<in> M" 
      using c_closed complement_closed_def by auto

    moreover have "\<forall>i. A i \<subseteq> \<Omega>"
      using seq_in subseq by auto 
    hence "\<Omega> - (\<Union>i. \<Omega> - A i) = (\<Inter>i. A i)" 
      by blast 

    ultimately show "(\<Inter>i::nat. A i) \<in> M"
      by simp 
  qed 
    
  ultimately show ?thesis
    by (simp add: countable_inter_closed_def) 
qed 

lemma c_ci_imp_cu_closed: 
  assumes c_closed: "complement_closed \<Omega> M"
      and ci_closed: "countable_inter_closed M" 
      and subseq: "\<forall>S\<in>M. S \<subseteq> \<Omega>"
    shows "countable_union_closed M"
proof - 
  have "M \<noteq> {}"
    using c_closed complement_closed_def by auto 

  moreover have "\<forall>A. (range A \<subseteq> M) \<longrightarrow> ((\<Union>i::nat. A i) \<in> M)" 
  proof (rule allI; rule impI)
    fix A :: "nat \<Rightarrow> 'a set"
    assume seq_in: "range A \<subseteq> M"
    hence "range (\<lambda>n. \<Omega> - A n) \<subseteq> M"
      using c_closed complement_closed_def by auto
    hence "(\<Inter>i::nat. \<Omega> - A i) \<in> M"
      using countable_inter_closed_def ci_closed by metis
    hence "\<Omega> - (\<Inter>i::nat. \<Omega> - A i) \<in> M" 
      using c_closed complement_closed_def by auto

    moreover have "\<forall>i. A i \<subseteq> \<Omega>"
      using seq_in subseq by auto 
    hence "\<Omega> - (\<Inter>i. \<Omega> - A i) = (\<Union>i. A i)" 
      by blast 

    ultimately show "(\<Union>i::nat. A i) \<in> M"
      by simp 
  qed 
    
  ultimately show ?thesis
    by (simp add: countable_union_closed_def) 
qed 

subsubsection "Disjoint unions"

definition disj_countable_union_closed :: "'a set set \<Rightarrow> bool"
  where "disj_countable_union_closed M = 
        ((M \<noteq> {}) \<and> (\<forall>A. (range A \<subseteq> M \<and> disjoint_family A) \<longrightarrow> ((\<Union>i::nat. A i) \<in> M)))"


definition disj_finite_union_closed :: "'a set set \<Rightarrow> bool"
  where "disj_finite_union_closed M = ((M \<noteq> {}) \<and> (\<forall>S\<in>M. \<forall>T\<in>M. (S \<inter> T = {}) \<longrightarrow> (S \<union> T \<in> M)))"

(* TODO - Could show by induction that this suffices for finite unions of size n *)
  
lemma dcu_imp_dfu_closed:
  assumes dcu_closed: "disj_countable_union_closed M"
      and empty_in: "{} \<in> M"
  shows "disj_finite_union_closed M"
proof -
  have "M \<noteq> {}" 
    using dcu_closed unfolding disj_countable_union_closed_def by fast 

  moreover have "\<forall>S\<in>M. \<forall>T\<in>M. (S \<inter> T = {}) \<longrightarrow> (S \<union> T \<in> M)" 
  proof 
    fix S
    assume S_in: "S \<in> M"
    show "\<forall>T\<in>M. (S \<inter> T = {}) \<longrightarrow> (S \<union> T \<in> M)"
    proof 
      fix T
      assume T_in: "T \<in> M"
      show "(S \<inter> T = {}) \<longrightarrow> (S \<union> T \<in> M)"
      proof 
        assume disj: "S \<inter> T = {}"

        let ?A = "(\<lambda>n. if n = (0::nat) then S else if n = (1::nat) then T else {})"
        let ?U = "\<Union>(range ?A)"
      
        have "range ?A \<subseteq> M"
          using S_in T_in empty_in by auto 
        moreover have "disjoint_family ?A"
          by (simp add: Int_commute disj disjoint_family_on_def) 
        ultimately have"?U \<in> M"
          using dcu_closed disj unfolding disj_countable_union_closed_def by blast  
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
              hence "x \<in> ?A 0"
                by simp
              thus ?thesis 
                by fast 
            next
              case T
                hence "x \<in> ?A 1"
                  by simp
                thus ?thesis 
                  by fast 
            qed 
          qed
        qed

        ultimately show "S \<union> T \<in> M"
          by fastforce 
      qed
    qed
  qed
  ultimately show ?thesis
    by (simp add: disj_finite_union_closed_def)
qed



lemma dcu_c_empty_imp_sd_closed: 
  assumes dcu_closed: "disj_countable_union_closed M"
      and c_closed: "complement_closed \<Omega> M"
      and empty_in: "{} \<in> M"
      and M_pow: "M \<subseteq> Pow \<Omega>"
    shows "set_diff_closed M"
proof -  
  have dfu_closed: "disj_finite_union_closed M"
    by (simp add: dcu_imp_dfu_closed assms)

  have "M \<noteq> {}" 
    using c_closed complement_closed_def by auto 
  moreover have " \<forall>S\<in>M.\<forall>T\<in>M. (T \<subseteq> S) \<longrightarrow> (S - T \<in> M)" 
  proof 
    fix S
    assume S_in: "S \<in> M"
    show "\<forall>T\<in>M. T \<subseteq> S \<longrightarrow> S - T \<in> M"
    proof
      fix T
      assume T_in_collection: "T \<in> M"
      show "T \<subseteq> S \<longrightarrow> S - T \<in> M"
      proof 
        assume T_in_set: "T \<subseteq> S"
        have "\<Omega> - S \<in> M"
          using c_closed unfolding complement_closed_def using S_in by auto
        moreover have "T \<inter> (\<Omega> - S) = {}"
          using T_in_set by auto
        ultimately have "T \<union> (\<Omega> - S) \<in> M"  
          using dfu_closed unfolding disj_finite_union_closed_def using S_in T_in_collection by simp
        hence "\<Omega> - (T \<union> (\<Omega> - S)) \<in> M"
          using c_closed complement_closed_def by blast
        moreover have "\<Omega> - (T \<union> (\<Omega> - S)) = S - T"
          using Diff_Diff_Int M_pow S_in by auto 
        ultimately show "S - T \<in> M"
          by simp 
      qed
    qed
  qed
  ultimately show ?thesis
    by (simp add: set_diff_closed_def)
qed

subsubsection "Monotonic sequences"

definition non_decreasing_union_closed :: "'a set set \<Rightarrow> bool"
  where "non_decreasing_union_closed M = 
        ((M \<noteq> {}) \<and> (\<forall>A. (range A \<subseteq> M \<and> non_decreasing A) \<longrightarrow> ((\<Union>i::nat. A i) \<in> M)))"

lemma cu_imp_ndu_closed:
  assumes cu_closed: "countable_union_closed M"
  shows "non_decreasing_union_closed M"
  using cu_closed unfolding countable_union_closed_def non_decreasing_union_closed_def by simp

lemma sd_omega_imp_ndu_closed: 
  assumes sd_closed: "set_diff_closed M"
      and ndu_closed: "non_decreasing_union_closed M"
      and omega: "\<Omega> \<in> M"
      and M_pow: "M \<subseteq> Pow \<Omega>" 
    shows "disj_countable_union_closed M" 
proof - 
  have "M \<noteq> {}"
    using omega by auto  

  moreover have "\<forall>A. (range A \<subseteq> M \<and> disjoint_family A \<longrightarrow> (\<Union>i::nat. A i) \<in> M)"
  proof (rule ; rule)
    fix A :: "nat \<Rightarrow> 'a set"
    assume A_disj_in_M: "range A \<subseteq> M \<and> disjoint_family A"
    let ?B = "(\<lambda>n. (\<Union>i\<in>{i::nat. i \<le> n}. A i))"
    have "non_decreasing ?B" 
      unfolding non_decreasing_def by (simp add: UN_subset_iff UN_upper) 
      
    moreover have "\<forall>n. ?B n \<in> M" 
    proof 
      fix n 
      show "?B n \<in> M" 
        using A_disj_in_M
      proof (induction n)
        case 0
        thus "\<Union> (A ` {i::nat. i \<le> 0}) \<in> M"
          using A_disj_in_M by auto 
      next
        case (Suc n)
        have "{i::nat. i \<le> (Suc n)} = insert (Suc n) {i::nat. i \<le> n}" 
          unfolding insert_def by auto 
        hence "?B (Suc n) = A (Suc n) \<union> ?B n"
          by simp
        moreover have "A (Suc n) \<subseteq> \<Omega>"
          using A_disj_in_M M_pow by blast
        moreover have B_in_Omega: "?B n \<subseteq> \<Omega>"
          using M_pow Suc.IH Suc.prems by blast
        ultimately have "?B (Suc n) = \<Omega> - ((\<Omega> - A (Suc n)) - ?B n)"
          by blast 
      
        moreover have "(\<Omega> - A (Suc n)) \<in> M"
          by (meson A_disj_in_M M_pow complement_closed_def omega range_subsetD sd_closed 
             sd_omega_imp_c_closed)
        moreover have "?B n \<subseteq> (\<Omega> - A (Suc n))" 
        proof 
          fix x
          assume x_in_B: "x \<in> ?B n"
          hence x_in_smaller_A: "\<exists>m<(Suc n). x \<in> A m"
            using neq0_conv by fastforce 
          hence "x \<in> \<Omega>"
            using B_in_Omega x_in_B by blast
          moreover have "x \<notin> A (Suc n)"
            using x_in_smaller_A A_disj_in_M unfolding disjoint_family_on_def
            by (metis UNIV_I disjoint_iff less_SucI not_less_eq)
          ultimately show "x \<in> (\<Omega> - A (Suc n))"
            by simp 
        qed
        moreover have "((\<Omega> - A (Suc n)) - ?B n) \<in> M"
          using calculation sd_closed Suc.IH Suc.prems unfolding set_diff_closed_def by blast 
        ultimately show "\<Union> (A ` {i. i \<le> Suc n}) \<in> M"
          using omega sd_closed unfolding set_diff_closed_def by auto 
      qed
    qed  
    hence "range ?B \<subseteq> M" 
      by auto 

    ultimately have "\<Union> (range ?B) \<in> M"
      using ndu_closed unfolding non_decreasing_union_closed_def by blast 

    moreover have "\<Union> (range ?B) = \<Union> (range A)"
      by fastforce 

    ultimately show "(\<Union>i::nat. A i) \<in> M"
      by auto 
  qed 
  ultimately show ?thesis 
    using disj_countable_union_closed_def by metis 
qed

lemma ndu_fu_imp_cu_closed:
  assumes ndu_closed: "non_decreasing_union_closed M"
      and fu_closed: "finite_union_closed M"
    shows "countable_union_closed M"
proof - 
  have M_non_empty: "M \<noteq> {}"
    using fu_closed unfolding finite_union_closed_def by auto 

  moreover have "\<forall>A::(nat \<Rightarrow> 'a set). range A \<subseteq> M \<longrightarrow> \<Union> (range A) \<in> M"
  proof (rule ; rule)
    fix A :: "nat \<Rightarrow> 'a set"
    let ?B = "(\<lambda>n. (\<Union>i\<in>{0..n}. A i))"
    have "non_decreasing ?B" 
      unfolding non_decreasing_def by (simp add: UN_subset_iff UN_upper)
    moreover assume A_within_M: "range A \<subseteq> M"
    have "\<forall>n::nat. ?B n \<in> M" 
    proof (rule)
      fix n
      show "?B n \<in> M"
      proof (induction n)
        case 0
        have "\<Union> (A ` {0..0}) = A 0"
          by auto 
        then show "\<Union> (A ` {0..0}) \<in> M"
          using A_within_M by auto
      next
        case (Suc n)
   
        have "\<Union> (A ` {0..Suc n}) = \<Union> (A ` {0..n}) \<union> A (Suc n)" 
        proof (rule ; rule)
          fix x 
          assume "x \<in> \<Union> (A ` {0..Suc n})"
          hence "\<exists>m\<in>{0..Suc n}. x \<in> A m"
            by blast
          hence "(\<exists>m\<in>{0..n}. x \<in> A m) \<or> x \<in> A (Suc n)"
            by (metis atLeastAtMost_iff le_SucE) 
          thus "x \<in> \<Union> (A ` {0..n}) \<union> A (Suc n)"
            by blast
        next 
          fix x 
          assume "x \<in> \<Union> (A ` {0..n}) \<union> A (Suc n)"
          hence "(\<exists>m\<in>{0..n}. x \<in> A m) \<or> x \<in> A (Suc n)"
            by blast
          thus "x \<in> \<Union> (A ` {0..Suc n})"
            by auto
        qed

        moreover have "\<Union> (A ` {0..n}) \<in> M"
          using Suc by auto
        moreover have "A (Suc n) \<in> M"
          using A_within_M by auto    
        ultimately show "\<Union> (A ` {0..Suc n}) \<in> M"  
          using fu_closed unfolding finite_union_closed_def by auto  
      qed
    qed 
    hence "range ?B \<subseteq> M" 
      by blast 
   
    ultimately have "\<Union> (range ?B) \<in> M"
      using M_non_empty ndu_closed unfolding non_decreasing_union_closed_def by auto 
    moreover have "\<Union> (range ?B) = \<Union> (range A)" 
      by fastforce 
    ultimately show "\<Union> (range A) \<in> M" 
      by auto 
  qed

  ultimately show ?thesis
    unfolding countable_union_closed_def by auto
qed

lemma dcu_c_empty_imp_ndu_closed: 
  assumes dcu_closed: "disj_countable_union_closed M"
      and c_closed: "complement_closed \<Omega> M"
      and empty_in: "{} \<in> M"
      and M_pow: "M \<subseteq> Pow \<Omega>"
    shows "non_decreasing_union_closed M"
proof - 
  have "M \<noteq> {}"
    using empty_in by auto 

  moreover have "\<forall>A. (range A \<subseteq> M \<and> non_decreasing A) \<longrightarrow> ((\<Union>i::nat. A i) \<in> M)" 
  proof (rule allI; rule impI)
    fix A :: "nat \<Rightarrow> 'a set" 
    assume A_is_nondecreasing_within_M: "range A \<subseteq> M \<and> non_decreasing A"
    let ?B = "(\<lambda>n. if n = 0 then A 0 else A n - A (n-1))"

    have "disjoint_family ?B"
      unfolding disjoint_family_on_def
    proof (rule; rule; rule)
      fix m n :: nat 
      assume "m \<noteq> n" 
      then consider (M) "m > n" | (N) "n > m"
        using nat_neq_iff by blast
       thus "?B m \<inter> ?B n = {}"
        proof cases
          case M
          hence "\<forall>x\<in>?B m. \<forall>k<m. x \<notin> A k"
            using A_is_nondecreasing_within_M non_decreasing_stay_in by fastforce
          hence "\<forall>x\<in>?B m. \<forall>k<m. x \<notin> ?B k"
            using Diff_iff by metis 
          then show ?thesis
            using M by blast
        next
          case N
          hence "\<forall>x\<in>?B n. \<forall>k<n. x \<notin> A k"
            using A_is_nondecreasing_within_M non_decreasing_stay_in by fastforce 
          hence "\<forall>x\<in>?B n. \<forall>k<n. x \<notin> ?B k"
            by (metis Diff_iff)
          then show ?thesis
            using N by blast
        qed 
      qed
       
      moreover have sd_closed: "set_diff_closed M"
        using assms dcu_c_empty_imp_sd_closed by auto
      hence "\<forall>n. ?B n \<in> M" 
      proof - 
        have "\<forall>n. ?B n = A 0 \<or> ?B n = A n - A (n-1)"
          by simp
        moreover have "\<forall>n. A n \<in> M"
          using A_is_nondecreasing_within_M by blast
        ultimately show "\<forall>n. ?B n \<in> M"
          using sd_closed unfolding set_diff_closed_def
          by (simp add: A_is_nondecreasing_within_M non_decreasing_multistep) 
      qed
      hence "range ?B \<subseteq> M"
        by blast
        
      ultimately have "((\<Union>i::nat. ?B i) \<in> M)"
        using dcu_closed unfolding disj_countable_union_closed_def by blast

      moreover have "\<Union> (range A) \<subseteq> (\<Union>i. ?B i)"
      proof 
        fix x 
        assume "x \<in> \<Union> (range A)"
        hence "\<exists>n. n \<in> {n'. x \<in> A n'}"
          by simp 
        then obtain n where "n \<in> {n'. x \<in> A n'} \<and> (\<forall>m\<in>{n'. x \<in> A n'}. n \<le> m)"
          using min_nat_elem by meson
        hence "x \<in> ?B n"
          by fastforce 
        thus "x \<in> (\<Union>i::nat. ?B i)"
          by fast 
      qed
      hence "(\<Union>i::nat. A i) = (\<Union>i::nat. ?B i)" 
        by auto 

      ultimately show "((\<Union>i::nat. A i) \<in> M)"
        by simp 
    qed 

  ultimately show ?thesis
    by (simp add: non_decreasing_union_closed_def)
qed


definition non_increasing_inter_closed :: "'a set set \<Rightarrow> bool"
  where "non_increasing_inter_closed M = 
        ((M \<noteq> {}) \<and> (\<forall>A. (range A \<subseteq> M \<and> non_increasing A) \<longrightarrow> ((\<Inter>i::nat. A i) \<in> M)))"

lemma ci_imp_nii_closed: 
  assumes ci_closed: "countable_inter_closed M"
  shows "non_increasing_inter_closed M"
  using ci_closed unfolding countable_inter_closed_def non_increasing_inter_closed_def by simp 

lemma ndu_c_imp_nii_closed: 
  assumes ndu_closed: "non_decreasing_union_closed M"
      and c_closed: "complement_closed \<Omega> M"
      and M_pow: "M \<subseteq> Pow \<Omega>"
    shows "non_increasing_inter_closed M"
proof - 
  have "M \<noteq> {}"
    using c_closed complement_closed_def by auto

  moreover have "\<forall>A. range A \<subseteq> M \<and> non_increasing A \<longrightarrow> \<Inter> (range A) \<in> M"
  proof (rule; rule)
    fix A :: "nat \<Rightarrow> 'a set"
    let ?B = "(\<lambda>n. \<Omega> - A n)"
    assume A_non_inc_within_M: "range A \<subseteq> M \<and> non_increasing A"

    hence "non_decreasing ?B" 
      unfolding non_increasing_def non_decreasing_def by auto 
    moreover have "range ?B \<subseteq> M"
      using A_non_inc_within_M c_closed complement_closed_def by blast  
    ultimately have "\<Union> (range ?B) \<in> M" 
      using ndu_closed unfolding non_decreasing_union_closed_def by blast 
    hence "\<Omega> - \<Union> (range ?B) \<in> M" 
      using c_closed unfolding complement_closed_def by auto 

    moreover have "\<Inter> (range A) = \<Omega> - \<Union> (range ?B)" 
    proof (rule ; rule)
      fix x
      assume "x \<in> \<Inter> (range A)"
      hence x_in_all: "\<forall>n. x \<in> A n"
        by blast 
      moreover have "\<forall>n. A n \<in> M"
        by (simp add: A_non_inc_within_M range_subsetD) 
      ultimately have "x \<in> \<Omega>" 
        using M_pow by auto 
         
      moreover have "x \<notin> (\<Union>n. \<Omega> - A n)"
        by (simp add: x_in_all) 

      ultimately show "x \<in> \<Omega> - (\<Union>n. \<Omega> - A n)" 
        by auto 
    next 
      fix x
      assume "x \<in> \<Omega> - (\<Union>n. \<Omega> - A n)" 
      thus "x \<in> \<Inter> (range A)"
        by simp  
    qed 

    ultimately show "\<Inter> (range A) \<in> M"
      by presburger 
  qed

  ultimately show ?thesis 
    unfolding non_increasing_inter_closed_def by auto 
qed


subsection "Algebras and Systems"

subsubsection "Exemplary Set Collections"

text "For now, these are just some famous types of set collections that people choose when they want
to prove something and need a convenient set to do it. We'll soon see what they're useful for.

Approaching these set collections by studying their properties separately first seems really useful, 
as we get an abstract idea of of what the concepts represent and how they are related."

lemma algebra_omega_c_fu_closed: 
  shows "algebra \<Omega> M = (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> finite_union_closed M)"
proof 
  assume alg: "algebra \<Omega> M"
  hence "M \<subseteq> Pow \<Omega> \<and> {} \<in> M \<and> complement_closed \<Omega> M \<and> finite_union_closed M"
    using algebra_iff_Un complement_closed_def finite_union_closed_def by fastforce
  moreover have "\<Omega> \<in> M"
    by (simp add: alg algebra.top) 
  ultimately show "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> finite_union_closed M" 
    by simp 
next 
  assume "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> finite_union_closed M"
  moreover have "{} \<in> M"
    using calculation complement_closed_def Diff_cancel by metis 
  ultimately show "algebra \<Omega> M" 
    by (simp add: algebra_iff_Un complement_closed_def finite_union_closed_def) 
qed 

lemma algebra_omega_c_fi_closed: 
  shows "algebra \<Omega> M = (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> finite_inter_closed M)"
proof 
  assume "algebra \<Omega> M"
  hence "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> finite_union_closed M"
    by (simp add: algebra_omega_c_fu_closed)
  thus "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> finite_inter_closed M"
    by (meson Pow_iff c_fu_imp_fi_closed subset_iff)
next 
  assume "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> finite_inter_closed M"
  hence "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> finite_union_closed M"
    by (meson PowD c_fi_imp_fu_closed subset_eq)
  thus "algebra \<Omega> M"
    by (simp add: algebra_omega_c_fu_closed)
qed 

lemma sigma_algebra_omega_c_cu_closed: 
  shows "sigma_algebra \<Omega> M = (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> countable_union_closed M)"
proof -
  have "sigma_algebra \<Omega> M = (algebra \<Omega> M \<and> (\<forall>A. range A \<subseteq> M \<longrightarrow> (\<Union>i::nat. A i) \<in> M))"
    using sigma_algebra_iff by simp 
  hence "sigma_algebra \<Omega> M = (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> finite_union_closed M
        \<and> (\<forall>A. range A \<subseteq> M \<longrightarrow> (\<Union>i::nat. A i) \<in> M))"
    by (simp add: algebra_omega_c_fu_closed)
  thus ?thesis
    by (metis countable_union_closed_def empty_iff cu_imp_fu_closed)
qed

lemma sigma_algebra_omega_c_ci_closed: 
  shows "sigma_algebra \<Omega> M = (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> countable_inter_closed M)"
proof 
  assume "sigma_algebra \<Omega> M"
  hence "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> countable_union_closed M"
    by (simp add: sigma_algebra_omega_c_cu_closed)
  thus "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> countable_inter_closed M"
    by (meson Pow_iff c_cu_imp_ci_closed subset_iff)
next 
  assume "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> countable_inter_closed M"
  hence "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> countable_union_closed M"
    by (meson PowD c_ci_imp_cu_closed subset_eq)
  thus "sigma_algebra \<Omega> M"
    by (simp add: sigma_algebra_omega_c_cu_closed)
qed

locale monotone_class = subset_class + 
  assumes ndu_closed: "non_decreasing_union_closed M"
      and ncdi_closed: "non_increasing_inter_closed M"

locale pi_system = subset_class + 
  assumes fi_closed: "finite_inter_closed M"

lemma Dynkin_omega_c_disju_closed:
  shows "Dynkin_system \<Omega> M = (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> disj_countable_union_closed M)"
proof - 
  have "Dynkin_system \<Omega> M = (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> (\<forall>A. A \<in> M \<longrightarrow> \<Omega> - A \<in> M) \<and> 
       (\<forall>A::nat \<Rightarrow> 'a set. disjoint_family A \<longrightarrow> range A \<subseteq> M \<longrightarrow> \<Union> (range A) \<in> M))"
    unfolding Dynkin_system_def Dynkin_system_axioms_def subset_class_def by fast 
  thus ?thesis 
    using complement_closed_def disj_countable_union_closed_def empty_iff by metis
qed

text "We show an equivalent definition of a Dynkin system."
lemma Dynkin_omega_diff_ndu_closed:
  shows "Dynkin_system \<Omega> M = 
         (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> set_diff_closed M \<and> non_decreasing_union_closed M)"
proof
  assume dynk: "Dynkin_system \<Omega> M"
  hence "{} \<in> M"
    by (simp add: Dynkin_system.empty)
  thus "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> set_diff_closed M \<and> non_decreasing_union_closed M"
    by (metis Dynkin_omega_c_disju_closed dcu_c_empty_imp_ndu_closed dcu_c_empty_imp_sd_closed dynk)
next
  assume "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> set_diff_closed M \<and> non_decreasing_union_closed M"
  hence "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> disj_countable_union_closed M"
    using sd_omega_imp_c_closed sd_omega_imp_ndu_closed by auto
  thus "Dynkin_system \<Omega> M"
    using Dynkin_omega_c_disju_closed by auto 
qed 

subsubsection "Relations between Set Collections"

lemma algebra_is_pi_system:
  assumes a: "algebra \<Omega> M"
  shows "pi_system \<Omega> M"
proof - 
  have "subset_class \<Omega> M"
    by (meson algebra_omega_c_fi_closed a subset_class.intro)
  moreover have "finite_inter_closed M"
    using algebra_omega_c_fi_closed a by blast  
  ultimately show ?thesis
    by (simp add: pi_system.intro pi_system_axioms.intro) 
qed

lemma sigma_algebra_is_algebra: 
  assumes sa: "sigma_algebra \<Omega> M"
  shows "algebra \<Omega> M"
proof - 
  have "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> countable_union_closed M"
    by (meson sa sigma_algebra_omega_c_cu_closed)
  hence "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> finite_union_closed M"
    by (simp add: cu_imp_fu_closed)
  thus ?thesis
    by (simp add: algebra_omega_c_fu_closed) 
qed

lemma sigma_algebra_is_monotone_class: 
  assumes sa: "sigma_algebra \<Omega> M"
  shows "monotone_class \<Omega> M"
proof - 
  have sa_properties: "M \<subseteq> Pow \<Omega> \<and> complement_closed \<Omega> M \<and> countable_union_closed M"
    using sa sigma_algebra_omega_c_cu_closed by auto

  hence "M \<subseteq> Pow \<Omega>"
    by simp
  moreover have "non_decreasing_union_closed M"
    by (simp add: cu_imp_ndu_closed sa_properties)
  moreover have "non_increasing_inter_closed M"
    using sa_properties calculation ndu_c_imp_nii_closed by auto

  ultimately show ?thesis
    unfolding monotone_class_def monotone_class_axioms_def subset_class_def by auto 
qed

lemma algebra_is_sigma_algebra_iff_monotone: 
  assumes a: "algebra \<Omega> M"
  shows "sigma_algebra \<Omega> M = monotone_class \<Omega> M"
proof 
  assume "sigma_algebra \<Omega> M"
  thus "monotone_class \<Omega> M"
    by (simp add: sigma_algebra_is_monotone_class) 
next
  assume "monotone_class \<Omega> M"
  hence "{} \<in> M \<and> finite_union_closed M \<and> non_decreasing_union_closed M"
    by (metis algebra_iff_Int algebra_omega_c_fu_closed a monotone_class.ndu_closed)
  hence "countable_union_closed M"
    by (simp add: ndu_fu_imp_cu_closed)  
  thus "sigma_algebra \<Omega> M"
    by (meson algebra_omega_c_fi_closed a sigma_algebra_omega_c_cu_closed) 
qed

lemma sigma_algebra_is_Dynkin:
  assumes sa: "sigma_algebra \<Omega> M"
  shows "Dynkin_system \<Omega> M"
proof - 

  have "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M"
    by (metis sa sigma_algebra_omega_c_cu_closed)

  moreover have "finite_union_closed M"
    using cu_imp_fu_closed sa sigma_algebra_omega_c_cu_closed by auto

  moreover have "complement_closed \<Omega> M"
    using sa sigma_algebra_omega_c_cu_closed by auto  
  hence "set_diff_closed M"
    using c_fu_omega_imp_sd_closed calculation
    by auto 

  ultimately show ?thesis
    by (simp add: sa sigma_algebra_imp_Dynkin_system)
qed 

lemma Dynkin_is_sigma_algebra_iff_pi: 
  assumes dynk: "Dynkin_system \<Omega> M"
  shows "sigma_algebra \<Omega> M = pi_system \<Omega> M"
proof 
  assume "sigma_algebra \<Omega> M"
  thus "pi_system \<Omega> M"
    by (simp add: algebra_is_pi_system sigma_algebra_is_algebra)
next 
  assume "pi_system \<Omega> M"
  hence "finite_inter_closed M \<and> complement_closed \<Omega> M \<and> (\<forall>S\<in>M. S \<subseteq> \<Omega>) \<and> non_decreasing_union_closed M"
    using dynk Dynkin_omega_diff_ndu_closed Dynkin_omega_c_disju_closed 
    unfolding pi_system_def pi_system_axioms_def by blast 
  hence "finite_union_closed M \<and> non_decreasing_union_closed M"
    using c_fi_imp_fu_closed by auto 
  hence "countable_union_closed M"
    by (simp add: ndu_fu_imp_cu_closed) 

  moreover have "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M"
    by (metis Dynkin_omega_c_disju_closed dynk)
 
  ultimately show "sigma_algebra \<Omega> M"
    using sigma_algebra_omega_c_cu_closed by auto
qed

lemma Dynkin_is_monotone:
  assumes dynk: "Dynkin_system \<Omega> M"
  shows "monotone_class \<Omega> M"
proof - 
  have "M \<subseteq> Pow \<Omega> \<and> complement_closed \<Omega> M \<and> non_decreasing_union_closed M"
    by (meson Dynkin_omega_c_disju_closed Dynkin_omega_diff_ndu_closed dynk)
  hence "M \<subseteq> Pow \<Omega> \<and> non_decreasing_union_closed M \<and> non_increasing_inter_closed M"
    using ndu_c_imp_nii_closed by auto
  thus ?thesis
    by (simp add: monotone_class.intro monotone_class_axioms.intro subset_class.intro) 
qed

lemma sa_pow_is_sa:
  assumes sa: "sigma_algebra \<Omega> M"
      and subseq: "S \<in> M"
    shows "sigma_algebra S (Pow S)"
proof - 
  have "complement_closed S (Pow S)" 
    unfolding complement_closed_def by (simp add: Pow_not_empty complement_closed_def)
  moreover have "countable_union_closed (Pow S)" 
    unfolding countable_union_closed_def by blast 
  ultimately show ?thesis
    by (simp add: sigma_algebra_omega_c_cu_closed) 
qed 

lemma sa_inter_is_sa:
  assumes sas: "\<forall>M\<in>X. sigma_algebra \<Omega> M"
      and non_empty: "X \<noteq> {}"
    shows "sigma_algebra \<Omega> (\<Inter>M\<in>X. M)"
proof - 
  have sa_properties: "\<forall>M\<in>X. M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_closed \<Omega> M \<and> countable_union_closed M"
    by (meson sas sigma_algebra_omega_c_cu_closed)

  have "(\<Inter>M\<in>X. M) \<subseteq> Pow \<Omega>" 
  proof 
    fix x
    assume "x \<in> (\<Inter>M\<in>X. M)"
    then obtain M where "M \<in> X \<and> x \<in> M" 
      using non_empty by auto 
    thus "x \<in> Pow \<Omega>"
      using sa_properties by auto 
  qed 

  moreover have "\<Omega> \<in> (\<Inter>M\<in>X. M)"  
    using sa_properties non_empty by simp 
 
  moreover have "complement_closed \<Omega> (\<Inter>M\<in>X. M)" 
    using sa_properties unfolding complement_closed_def by blast

  moreover have "countable_union_closed (\<Inter>M\<in>X. M)" 
    unfolding countable_union_closed_def 
  proof 
    show "(\<Inter>M\<in>X. M) \<noteq> {}"
      using calculation(2) by auto
  next 
    show "\<forall>A :: (nat \<Rightarrow> 'a set). range A \<subseteq> (\<Inter>M\<in>X. M) \<longrightarrow> \<Union> (range A) \<in> (\<Inter>M\<in>X. M)"
    proof (rule ; rule)
      fix A :: "nat \<Rightarrow> 'a set"
      assume "range A \<subseteq> (\<Inter>M\<in>X. M)"
      hence "\<forall>M\<in>X. range A \<subseteq> M" by auto 
      thus "\<Union> (range A) \<in> (\<Inter>M\<in>X. M)" 
        using sa_properties unfolding countable_union_closed_def by simp
    qed
  qed

  ultimately show ?thesis
    by (simp add: sigma_algebra_omega_c_cu_closed)
qed

lemma sa_ndu_is_a:
  assumes sas: "\<forall>n::nat. sigma_algebra \<Omega> (X n)"
      and non_dec: "non_decreasing X"
    shows "algebra \<Omega> (\<Union>(range X))"
proof -
  have a_properties: "\<forall>n. X n \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> X n \<and> complement_closed \<Omega> (X n) \<and> countable_union_closed (X n)"
    by (meson sas sigma_algebra_omega_c_cu_closed)

  hence "(\<Union>(range X)) \<subseteq> Pow \<Omega>" 
    by fast 

  moreover have "\<Omega> \<in> (\<Union>(range X))"
    using a_properties by auto 

  moreover have "complement_closed \<Omega> (\<Union>(range X))"
    using a_properties unfolding complement_closed_def by blast 

  moreover have "finite_union_closed (\<Union>(range X))"
    unfolding finite_union_closed_def 
  proof 
    show "\<Union> (range X) \<noteq> {}"
      using calculation(2) by auto
  next 
    have fu_closed: "\<forall>n. finite_union_closed (X n)"
      by (simp add: a_properties cu_imp_fu_closed)
    show "\<forall>S\<in>\<Union> (range X). \<forall>T\<in>\<Union> (range X). S \<union> T \<in> \<Union> (range X)"
    proof (rule ; rule)
      fix S T
      assume "S \<in> \<Union> (range X)" and "T \<in> \<Union> (range X)"
      then obtain n m where S_n: "S \<in> X n" and T_m: "T \<in> X m"
        by blast
      thus "S \<union> T \<in> \<Union> (range X)"
      proof (cases "m \<ge> n")
        case True
        hence "S \<in> X m"
          by (metis S_n non_dec non_decreasing_stay_in)
        thus "S \<union> T \<in> \<Union> (range X)"
          using fu_closed T_m unfolding finite_union_closed_def by auto 
      next
        case False
        hence "T \<in> X n"
          by (meson T_m nle_le non_dec non_decreasing_stay_in)  
        thus "S \<union> T \<in> \<Union> (range X)"
          using fu_closed S_n unfolding finite_union_closed_def by auto 
      qed 
    qed
  qed

  ultimately show ?thesis
    by (simp add: algebra_omega_c_fu_closed) 
qed

end