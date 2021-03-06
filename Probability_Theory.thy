theory Probability_Theory 
  imports "HOL-Analysis.Sigma_Algebra" "HOL-Analysis.Infinite_Sum" "HOL-Library.Liminf_Limsup"
begin

chapter "Basics from Measure Theory"

section "Auxiliary lemmas"

(* Every non-empty set of natural numbers has a least element. *)
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

(* If the intersection of the family of sets fulfilling a property fulfils that property, it is the
   smallest set that does so. *)
lemma inter_is_Least_if_P:
  assumes P_inter: "P (\<Inter>S\<in>{S. P S}. S)"
  shows "(\<Inter>S\<in>{S. P S}. S) = Least P"
proof -  
  let ?U = "(\<Inter>S\<in>{S. P S}. S)"
  have "\<forall>S. P S \<longrightarrow> ?U \<subseteq> S"
    by auto 
  moreover have "P ?U"
    using P_inter by auto
  ultimately show ?thesis
    unfolding Least_def by (simp add: subset_antisym the_equality)
qed

(* The preimage of a set under a given mapping. *)
definition preimage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> 'a set"
  where "preimage f T = {s. \<exists>t\<in>T. f s = t}"

lemma preimage_union: 
  shows "preimage f (\<Union>M) = (\<Union>S\<in>M. preimage f S)"
proof (rule ; rule) 
  fix x 
  assume "x \<in> preimage f (\<Union>M)"
  hence "x \<in> {s. \<exists>t\<in>(\<Union>M). f s = t}"
    using preimage_def by metis 
  thus "x \<in> (\<Union>S\<in>M. preimage f S)"
    by (simp add: preimage_def)
next
  fix x 
  assume "x \<in> (\<Union>S\<in>M. preimage f S)"
  thus "x \<in> preimage f (\<Union>M)"
    by (simp add: preimage_def)
qed 

lemma preimage_set_diff: 
  shows "preimage f (R-S) = (preimage f R) - (preimage f S)"
proof (rule ; rule)
  fix x 
  assume "x \<in> preimage f (R - S)"
  hence "x \<in> {s. \<exists>t\<in>(R-S). f s = t}"
    using preimage_def by metis 
  thus "x \<in> preimage f R - preimage f S"
    by (simp add: preimage_def)
next 
  fix x
  assume "x \<in> preimage f R - preimage f S"
  thus "x \<in> preimage f (R - S)"
    by (simp add: preimage_def) 
qed 

(* This is shown with inj_on f A as assumption but the provers don't find that. *)
lemma inj_infinite_image:
  assumes inj: "inj f"
      and inf: "infinite A"
    shows "infinite (f ` A)"
  by (meson finite_imageD inf inj inj_def inj_onI)

lemma even_inf: 
  shows "infinite ((\<lambda>n::nat. 2 * n) ` UNIV)"
    by (simp add: range_inj_infinite injI)

lemma odd_inf: 
  shows "infinite ((\<lambda>n::nat. 2 * n + 1) ` UNIV)"
  by (simp add: range_inj_infinite injI)

lemma nat_remainder: 
  fixes x m :: nat
  assumes m_pos: "m > 0"
      and x_pos: "x > 0"
  shows "\<exists>k r :: nat. x = k * m + r \<and> r < m"  
proof (induction x)
  case 0
  then show ?case
    using m_pos by auto 
next
  case (Suc x)
  then obtain k r :: nat where ind_hyp: "x = k * m + r \<and> r < m"
    by auto
  then consider (l) "r + 1 < m" | (eq) "r + 1 = m"
    by linarith
  then show ?case 
  proof cases
    case l
    then show ?thesis
      by (metis Suc_eq_plus1 add_Suc_right ind_hyp) 
  next
    case eq
    then show ?thesis
      by (metis Suc_eq_plus1 add_0 add_diff_cancel_right' diff_cancel2 ind_hyp 
          linordered_semidom_class.add_diff_inverse m_pos mult_0 mult_Suc) 
  qed 
qed

lemma even_odd_UNIV: 
  shows "(UNIV :: nat set) = ((\<lambda>n::nat. 2 * n) ` UNIV) \<union> ((\<lambda>n::nat. 2 * n + 1) ` UNIV)"
proof -
  let ?E = "(\<lambda>n::nat. 2 * n) ` UNIV"
  let ?O = "(\<lambda>n::nat. 2 * n + 1) ` UNIV"
  have "\<forall>x. x \<in> ?E \<or> x \<in> ?O"
  proof 
    fix x :: nat
    consider (0) "x = 0" | (p) "x > 0"
      by auto
    thus "x \<in> ?E \<or> x \<in> ?O"
    proof cases
      case 0
      then show ?thesis
        by simp 
    next
      case p
      hence "\<exists>k r. x = k * 2 + r \<and> r < 2"
        by (simp add: nat_remainder)
      hence "\<exists>k r :: nat. x = k * 2 \<or> x = k * 2 + 1"
        by (metis div_mult_self1 div_mult_self_is_m mod2_gr_0 mod_less neq0_conv plus_nat.add_0)
      thus ?thesis by auto 
    qed
  qed 
  thus ?thesis
    by blast 
qed
  
lemma even_odd_disjoint: 
  shows "(\<lambda>n::nat. 2 * n) ` UNIV \<inter> (\<lambda>n::nat. 2 * n + 1) ` UNIV = {}"
proof (rule ; rule)
  let ?E = "(\<lambda>n::nat. 2 * n) ` UNIV"
  let ?O = "(\<lambda>n::nat. 2 * n + 1) ` UNIV"
  fix x :: nat
  assume "x \<in> ?E \<inter> ?O"
  then obtain n m :: nat where "x = 2 * n" and "x = 2 * m + 1"
    by blast 
  thus "x \<in> {}"
    by (metis Suc_eq_plus1 double_not_eq_Suc_double) 
qed
  

section "Sets"

subsection "Set operations"

subsubsection "Elementary operations"

text "Just as real (or complex) numbers can be added or multiplied, there exist operations on sets."

text "Union:"
corollary "A \<union> B = {x. x \<in> A \<or> x \<in> B}" 
  using Un_def by auto

text "Intersection:"
corollary "A \<inter> B = {x. x \<in> A \<and> x \<in> B}" 
  using Int_def by auto 

text "Complement:"
corollary "-A = {x. x \<notin> A}" 
  using Compl_eq by auto 

text "Difference:"
corollary "A - B = A \<inter> (-B)" 
  using Diff_eq by auto 

text "Symmetric difference:"
definition symm_diff :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "symm_diff A B = (A - B) \<union> (B - A)"

notation symm_diff (infix "\<Delta>" 50)

lemma symm_diff_xor: "A \<Delta> B = {x. (x\<in>A \<or> x\<in>B) \<and> \<not>(x\<in>A \<and> x\<in>B)}"
    by (simp add: Un_def symm_diff_def ; auto)

text "We also use standard notation for unions and intersections of finitely / countably many sets."

corollary 
  fixes A :: "nat \<Rightarrow> 'a set"
  shows "(\<Union>i\<in>{0..n}. A i) = {x. \<exists>i\<in>{0..n}. x \<in> A i}" 
  using UNION_eq by auto

corollary 
  fixes A :: "nat \<Rightarrow> 'a set"
  shows "(\<Inter>i. A i) = {x. \<forall>i\<in>{0..}. x \<in> A i}" 
  by blast 


subsubsection "Additional terminology"

text "Some additional terminology:"

text "The empty set:"
corollary "\<not>(\<exists>x. x \<in> {})"
  by simp

text "Subsets:"
corollary "A \<subseteq> B \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> x \<in> B)"
  by (simp add: subset_iff)

text "Disjoint:"
corollary "A \<inter> B = {} \<longleftrightarrow> \<not>(\<exists>x. x \<in> A \<and> x \<in> B)"
  by (simp add: disjoint_iff) 

text "Power set:"
corollary "Pow \<Omega> = {A. A \<subseteq> \<Omega>}"
  by (simp add: Pow_def)

text "{A n, n \<ge> 0} is non-decreasing:"
definition non_decreasing :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool"
  where "non_decreasing A \<equiv> \<forall>n. A n \<subseteq> A (n + 1)"

(* In a non-decreasing set sequence, any set is a subset of all the ones that follow. *)
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

(* Hence, once an element arises within a sequence, it will stay there for all of eternity. *)
lemma non_decreasing_stay_in: 
  assumes non_dec: "non_decreasing A"
      and base: "x \<in> A n"
    shows "\<forall>m\<ge>n. x \<in> A m"
  using base non_dec non_decreasing_multistep by auto

lemma non_dec_to_disj: 
  assumes non_dec: "non_decreasing A"
  shows "disjoint_family (\<lambda>n. if n = 0 then A 0 else A n - A (n - 1))"
  unfolding disjoint_family_on_def 
proof (rule ; rule ; rule) 
  let ?B = "(\<lambda>n. if n = 0 then A 0 else A n - A (n-1))"
  fix m n :: nat 
  assume "m \<noteq> n" 
  then consider (M) "m > n" | (N) "n > m"
    using nat_neq_iff by blast
  thus "?B m \<inter> ?B n = {}"
  proof cases
    case M
    hence "\<forall>x\<in>?B m. \<forall>k<m. x \<notin> A k"
      using non_dec non_decreasing_stay_in by fastforce
    hence "\<forall>x\<in>?B m. \<forall>k<m. x \<notin> ?B k"
      using Diff_iff by metis 
    then show ?thesis
      using M by blast
   next
     case N
     hence "\<forall>x\<in>?B n. \<forall>k<n. x \<notin> A k"
       using non_dec non_decreasing_stay_in by fastforce 
     hence "\<forall>x\<in>?B n. \<forall>k<n. x \<notin> ?B k"
       by (metis Diff_iff)
     then show ?thesis
       using N by blast
  qed 
qed

lemma non_dec_N_is_fu: 
  assumes non_dec: "non_decreasing A"
  shows "(\<Union>n\<in>{..N}. A n) = A N"
proof (rule ; rule)
  fix x 
  assume "x \<in> \<Union> (A ` {..N})"
  thus "x \<in> A N"
    by (metis UN_iff atMost_iff non_dec non_decreasing_stay_in)
next 
  fix x 
  assume "x \<in> A N" 
  thus "x \<in> \<Union> (A ` {..N})"
    by auto 
qed

lemma non_dec_is_disj_fu: 
  assumes non_dec: "non_decreasing A"
  shows "\<forall>N. A N = (\<Union>n\<in>{..N}. (\<lambda>n. if n = 0 then A 0 else A n - A (n - 1)) n)"
proof - 
  let ?B = "(\<lambda>n. if n = 0 then A 0 else A n - A (n - 1))"
  have "\<forall>N. (\<Union>n\<in>{..N}. A n) \<subseteq> (\<Union>n\<in>{..N}. ?B n)"
  proof (rule ; rule) 
    fix N x 
    obtain P where P_fun: "P = (\<lambda>n. n \<in> {..N} \<and> x \<in> A n)"
      by auto 

    assume "x \<in> \<Union> (A ` {..N})"
    hence "\<exists>n. P n"
      using P_fun by auto 
    hence "\<exists>n. P n \<and> (\<forall>m<n. \<not> P m)"
      using exists_least_iff by auto 
    then obtain n where n_choice: "n \<in> {..N} \<and> x \<in> A n \<and> (\<forall>m\<in>{..N}. m < n \<longrightarrow> x \<notin> A m)"
      using P_fun by auto 

    consider (0) "n = 0" | (Suc) "n = Suc (n - 1)"
      by linarith 
    hence "x \<in> A n \<and> (n = 0 \<or> x \<notin> A (n - 1))"
    proof cases
      case 0
      then show ?thesis
        using n_choice by auto 
    next
      case Suc
      then show ?thesis
        using n_choice by auto 
    qed

    hence "x \<in> ?B n"
      by auto
    thus "x \<in> \<Union> (?B ` {..N})"
      using n_choice by blast 
  qed 
  
  hence "\<forall>N. \<Union> (A ` {..N}) = (\<Union>n\<le>N. if n = 0 then A 0 else A n - A (n - 1))"
    by auto 
  thus ?thesis 
    using non_dec non_dec_N_is_fu by metis 
qed

lemma non_dec_to_disj_same_cu: 
  assumes non_dec: "non_decreasing A"
  shows "(\<Union>n. A n) = (\<Union>n. (\<lambda>n. if n = 0 then A 0 else A n - A (n - 1)) n)"
proof - 
  let ?B = "(\<lambda>n. if n = 0 then A 0 else A n - A (n - 1))"
  have "\<Union> (range A) \<subseteq> (\<Union>n. ?B n)"
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
  thus ?thesis by auto 
qed

text "{A n, n \<ge> 0} is non-increasing:"
definition non_increasing :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool"
  where "non_increasing A \<equiv> \<forall>n. A (n + 1) \<subseteq> A n"

(* In a non-decreasing set sequence, any set is a subset of all the ones that precede it. *)
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

(* Hence, once an element is absent from a set in the sequence, it will stay absent forever. *)
lemma non_increasing_stay_out: 
  assumes non_inc: "non_increasing A"
      and base: "x \<notin> A n"
    shows "\<forall>m\<ge>n. x \<notin> A m"
  using base non_inc non_increasing_multistep by auto

lemma non_inc_to_disj: 
  assumes non_inc: "non_increasing A"
  shows "disjoint_family (\<lambda>n. A n - A (n + 1))"
  unfolding disjoint_family_on_def 
proof (rule ; rule ; rule) 
  let ?B = "(\<lambda>n. A n - A (n + 1))"
  fix m n :: nat 
  assume "m \<noteq> n" 
  then consider (N) "m < n" | (M) "n < m"
    using nat_neq_iff by blast
  thus "?B m \<inter> ?B n = {}"
  proof cases
    case N
    hence "\<forall>x\<in>?B m. \<forall>k>m. x \<notin> A k"
      using non_inc non_increasing_stay_out by fastforce
    hence "\<forall>x\<in>?B m. \<forall>k>m. x \<notin> ?B k"
      using Diff_iff by metis 
    then show ?thesis
      using N by auto 
   next
     case M
     hence "\<forall>x\<in>?B n. \<forall>k>n. x \<notin> A k"
       using non_inc non_increasing_stay_out by fastforce 
     hence "\<forall>x\<in>?B n. \<forall>k>n. x \<notin> ?B k"
       by (metis Diff_iff)
     then show ?thesis
       using M by blast
  qed 
qed

lemma nd_complement_ni: 
  assumes nd: "non_decreasing A"
  shows "non_increasing (\<lambda>n. \<Omega> - A n)"
  using nd unfolding non_decreasing_def non_increasing_def by blast 

lemma ni_complement_nd: 
  assumes ni: "non_increasing A"
  shows "non_decreasing (\<lambda>n. \<Omega> - A n)"
  using ni unfolding non_decreasing_def non_increasing_def by blast 

text "The de Morgan formulas are as follows:

(i)  The elements that don't belong to any set in a family are exactly the ones that belong to every 
     complement of sets in the family.

(ii) The elements that don't belong to all sets in a family are exactly the ones that appear in some 
     complement of a set in the family."
corollary "-(\<Union>k\<in>I. A k) = (\<Inter>k\<in>I. -(A k))" by simp

corollary "-(\<Inter>k\<in>I. A k) = (\<Union>k\<in>I. -(A k))" by simp



subsection "Limits of Sets"

text "It is also possible to define limits of sets. However not every sequence of sets has a limit."

(* Any sensible notion of a limit should at least include these elements... *)
lemma liminf_set:
  fixes A :: "nat \<Rightarrow> ('a set)"
  shows "liminf A = (\<Union>n. (\<Inter>m\<in>{n..}. A m))"
    by (simp add: liminf_SUP_INF) 

(* ... as they eventually occur at every single index of the sequence. *)
lemma liminf_greater_n: "(x \<in> liminf A) = (\<exists>n.\<forall>m\<ge>n. x \<in> A m)"
  by (simp add: liminf_set atLeast_def) 

(* Any sensible notion of a limit should at most include these elements... *)
lemma limsup_set:
  fixes A :: "nat \<Rightarrow> ('a set)"
  shows "limsup A = (\<Inter> n. \<Union>m\<in>{n..}. A m)"
    by (simp add: limsup_INF_SUP) 

(* ... as all others eventually stop appearing forever. *)
lemma limsup_greater_n: "(x \<notin> limsup A) = (\<exists>n.\<forall>m\<ge>n. x \<notin> A m)"
  by (simp add: limsup_set atLeast_def) 

(* It's reassuring that the two requirements above never lead to a contradiction. *)
lemma liminf_subseq_limsup: "liminf A \<subseteq> limsup A"
proof 
  fix x 
  assume "x \<in> liminf A"
  hence "\<exists>n.\<forall>m\<ge>n. x \<in> A m"
    by (simp add: liminf_greater_n)
  hence "\<forall>n.\<exists>m\<ge>n. x \<in> A m"
    by (metis nat_le_linear)
  thus "x \<in> limsup A"
    by (metis limsup_greater_n)
qed 

(* We thus get a handy condition for checking whether liminf and limsup are the same. *)
lemma liminf_limsup_eq_cond: 
  shows "(liminf A = limsup A) \<longleftrightarrow> (limsup A \<subseteq> liminf A)"
  by (simp add: liminf_subseq_limsup set_eq_subset)

text "We say that a sequence of sets has a limit if the two above notions agree."
definition set_limit :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
  where "set_limit A = (THE S. S = liminf A \<and> S = limsup A)"

(* If the limit exists, it's of course equal to liminf... *)
lemma set_limit_eq_liminf: 
  assumes limsup_subseq_liminf: "limsup A \<subseteq> liminf A" 
  shows "set_limit A = liminf A"
proof - 
  have "limsup A = liminf A"
    using liminf_limsup_eq_cond limsup_subseq_liminf by fast
  thus ?thesis 
    by (simp add: set_limit_def) 
qed

(* ... and to limsup. *)
lemma set_limit_eq_limsup: 
  assumes limsup_subseq_liminf: "limsup A \<subseteq> liminf A" 
  shows "set_limit A = limsup A"
  by (simp add: liminf_limsup_eq_cond limsup_subseq_liminf set_limit_eq_liminf)

text "One instance when a limit exists is when the sequence of sets is monotone."

(* For a non-decreasing sequence of sets, any element that doesn't disappear forever will start
   appearing forever. These are precisely all elements that appear in the sequence at any point. 

   The limit is thus defined.*)
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
        using limsup_greater_n by fast
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
        by (metis limsup_greater_n)
      hence "\<exists>n.\<forall>m\<ge>n. x \<in> A m"
        by (meson non_decreasing non_decreasing_stay_in)
      thus "x \<in> liminf A"
        by (simp add: liminf_greater_n)
    qed
    thus ?thesis
      using liminf_limsup_eq_cond by fast 
  qed

  ultimately show ?thesis
    by (simp add: set_limit_eq_limsup) 
qed

(* For a non-increasing sequence of sets, any element that doesn't appear at every single index
   will eventually disappear forever.

   The limit is thus defined.*)
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
        by (meson limsup_greater_n)
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
        by (meson limsup_greater_n)
      hence "\<exists>n. \<forall>k\<ge>n. x \<in> A k"
        by (meson non_increasing non_increasing_stay_out)
      thus "x \<in> liminf A"
        by (simp add: liminf_greater_n) 
    qed
    thus ?thesis
      using liminf_limsup_eq_cond by fast  
  qed 

  ultimately show ?thesis
    by (simp add: set_limit_eq_limsup) 
qed

lemma nd_c_ni_set_limit: 
  assumes non_dec: "non_decreasing A"
    shows "set_limit (\<lambda>n. \<Omega> - A n) = \<Omega> - set_limit A"
proof - 
  let ?B = "(\<lambda>n. \<Omega> - A n)"
  have non_inc: "non_increasing ?B"
    by (simp add: nd_complement_ni non_dec)

  have "set_limit A = \<Union> (range A)"
    using non_dec non_decreasing_set_limit by auto
  moreover have "set_limit ?B = \<Inter> (range ?B)"
    using non_inc non_increasing_set_limit by auto
  hence "set_limit ?B = \<Omega> - \<Union> (range A)"
    by simp 
  ultimately show ?thesis
    by auto 
qed

lemma ni_c_nd_set_limit: 
  assumes non_inc: "non_increasing A"
  shows "set_limit (\<lambda>n. \<Omega> - A n) = \<Omega> - set_limit A"
proof - 
  let ?B = "(\<lambda>n. \<Omega> - A n)"
  have non_dec: "non_decreasing ?B"
    by (simp add: ni_complement_nd non_inc)

  have "set_limit A = \<Inter> (range A)"
    using non_inc non_increasing_set_limit by auto
  moreover have "set_limit ?B = \<Union> (range ?B)"
    using non_dec non_decreasing_set_limit by auto  
  hence "set_limit ?B = \<Omega> - \<Inter> (range A)"
    by simp 
  ultimately show ?thesis
    by blast
qed


section "Collections of Sets"

subsection "Rules for Collections of Sets"

text "Set collections are commonly selected according to whether they are stable under certain 
operations.  
A collection of sets may, for instance, be stable under 
(i) The complement.
(ii) Finite unions.
(iii) Finite intersections.

Note: (i), (ii) and (i), (iii) are equivalent, due to deMorgan's formulas.

Note: We defined (ii) and (iii) with just a normal binary union / intersection. That's enough, it
      follows for all finite families by induction.

(iv) Set differences with respect to ones subset, provided that it's also in the collection 

Note: If the subsets we want to be able to remove weren't required to be in the collection, this
      condition would just mean 'stable under taking subsets'. 

(v) Countable unions.
(vi) Countable union of a family of sets as long as it is disjoint. 

Note: This does not hold for finite, disjoint unions unless {} is in the set. Only then is it possible
      to represent any finite disjoint union as a countable disjoint union, where all but the first
      finitely many entries of the sequence that yields the union can be {}. 

(vii) Countable intersections.

Note: Yes, (i), (v) and (i), (vii) are also equivalent by deMorgan.

Note: If a set is stable under countable un./in., it is of course so under finite ones as well.

(viii) The (countable) union (limit!) of non-decreasing sequences of sets.
(ix) The (countable) intersection (limit!) of non-increasing sequences of sets. 
"

subsubsection "Complements, finite unions and intersections"

definition complement_stable :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool"
  where "complement_stable \<Omega> M = ((M \<noteq> {}) \<and> (\<forall>S\<in>M. \<Omega> - S \<in> M))"

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
  assumes c_stable: "complement_stable \<Omega> M"
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
  assumes c_stable: "complement_stable \<Omega> M"
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

subsubsection "Set Difference"

definition set_diff_stable :: "'a set set \<Rightarrow> bool"
  where "set_diff_stable M = ((M \<noteq> {}) \<and> (\<forall>S\<in>M.\<forall>T\<in>M. (T \<subseteq> S) \<longrightarrow> (S - T \<in> M)))"

lemma sd_omega_imp_c_stable: 
  assumes sd_stable: "set_diff_stable M"
      and omega: "\<Omega> \<in> M"
      and M_pow: "M \<subseteq> Pow \<Omega>"
    shows "complement_stable \<Omega> M"
proof - 
  have "M \<noteq> {}"
    using omega by auto
  moreover have "\<forall>S\<in>M. \<Omega> - S \<in> M"
    by (meson M_pow PowD in_mono omega sd_stable set_diff_stable_def)
  ultimately show ?thesis
    by (simp add: complement_stable_def) 
qed

lemma c_fu_omega_imp_sd_stable:
  assumes c_stable: "complement_stable \<Omega> M" 
      and fu_stable: "finite_union_stable M"
      and omega: "\<Omega> \<in> M"
      and M_pow: "M \<subseteq> Pow \<Omega>"
    shows "set_diff_stable M"
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
      using S_M c_stable complement_stable_def by blast
    hence "(\<Omega> - S) \<union> T \<in> M"
      using T_M fu_stable unfolding finite_union_stable_def by simp 
    ultimately show "S - T \<in> M"  
      using c_stable M_pow unfolding complement_stable_def by simp 
  qed 
  ultimately show ?thesis 
    unfolding set_diff_stable_def by auto 
qed
  

subsubsection "Countable unions and intersections"

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
  assumes c_stable: "complement_stable \<Omega> M"
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
  assumes c_stable: "complement_stable \<Omega> M"
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

subsubsection "Disjoint unions"

definition disj_countable_union_stable :: "'a set set \<Rightarrow> bool"
  where "disj_countable_union_stable M = 
        ((M \<noteq> {}) \<and> (\<forall>A. (range A \<subseteq> M \<and> disjoint_family A) \<longrightarrow> ((\<Union>i::nat. A i) \<in> M)))"


definition disj_finite_union_stable :: "'a set set \<Rightarrow> bool"
  where "disj_finite_union_stable M = ((M \<noteq> {}) \<and> (\<forall>S\<in>M. \<forall>T\<in>M. (S \<inter> T = {}) \<longrightarrow> (S \<union> T \<in> M)))"

(* TODO - Could show by induction that this suffices for unions of disjoint families of size n *)
  
lemma dcu_imp_dfu_stable:
  assumes dcu_stable: "disj_countable_union_stable M"
      and empty_in: "{} \<in> M"
  shows "disj_finite_union_stable M"
proof -
  have "M \<noteq> {}" 
    using dcu_stable unfolding disj_countable_union_stable_def by fast 

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
          using dcu_stable disj unfolding disj_countable_union_stable_def by blast  
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
    by (simp add: disj_finite_union_stable_def)
qed



lemma dcu_c_empty_imp_sd_stable: 
  assumes dcu_stable: "disj_countable_union_stable M"
      and c_stable: "complement_stable \<Omega> M"
      and empty_in: "{} \<in> M"
      and M_pow: "M \<subseteq> Pow \<Omega>"
    shows "set_diff_stable M"
proof -  
  have dfu_stable: "disj_finite_union_stable M"
    by (simp add: dcu_imp_dfu_stable assms)

  have "M \<noteq> {}" 
    using c_stable complement_stable_def by auto 
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
          using c_stable unfolding complement_stable_def using S_in by auto
        moreover have "T \<inter> (\<Omega> - S) = {}"
          using T_in_set by auto
        ultimately have "T \<union> (\<Omega> - S) \<in> M"  
          using dfu_stable unfolding disj_finite_union_stable_def using S_in T_in_collection by simp
        hence "\<Omega> - (T \<union> (\<Omega> - S)) \<in> M"
          using c_stable complement_stable_def by blast
        moreover have "\<Omega> - (T \<union> (\<Omega> - S)) = S - T"
          using Diff_Diff_Int M_pow S_in by auto 
        ultimately show "S - T \<in> M"
          by simp 
      qed
    qed
  qed
  ultimately show ?thesis
    by (simp add: set_diff_stable_def)
qed

subsubsection "Monotonic sequences"

definition non_decreasing_union_stable :: "'a set set \<Rightarrow> bool"
  where "non_decreasing_union_stable M = 
        ((M \<noteq> {}) \<and> (\<forall>A. (range A \<subseteq> M \<and> non_decreasing A) \<longrightarrow> ((\<Union>i::nat. A i) \<in> M)))"

lemma cu_imp_ndu_stable:
  assumes cu_stable: "countable_union_stable M"
  shows "non_decreasing_union_stable M"
  using cu_stable unfolding countable_union_stable_def non_decreasing_union_stable_def by simp

lemma sd_omega_imp_ndu_stable: 
  assumes sd_stable: "set_diff_stable M"
      and ndu_stable: "non_decreasing_union_stable M"
      and omega: "\<Omega> \<in> M"
      and M_pow: "M \<subseteq> Pow \<Omega>" 
    shows "disj_countable_union_stable M" 
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
          by (meson A_disj_in_M M_pow complement_stable_def omega range_subsetD sd_stable 
             sd_omega_imp_c_stable)
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
          using calculation sd_stable Suc.IH Suc.prems unfolding set_diff_stable_def by blast 
        ultimately show "\<Union> (A ` {i. i \<le> Suc n}) \<in> M"
          using omega sd_stable unfolding set_diff_stable_def by auto 
      qed
    qed  
    hence "range ?B \<subseteq> M" 
      by auto 

    ultimately have "\<Union> (range ?B) \<in> M"
      using ndu_stable unfolding non_decreasing_union_stable_def by blast 

    moreover have "\<Union> (range ?B) = \<Union> (range A)"
      by fastforce 

    ultimately show "(\<Union>i::nat. A i) \<in> M"
      by auto 
  qed 
  ultimately show ?thesis 
    using disj_countable_union_stable_def by metis 
qed

lemma ndu_fu_imp_cu_stable:
  assumes ndu_stable: "non_decreasing_union_stable M"
      and fu_stable: "finite_union_stable M"
    shows "countable_union_stable M"
proof - 
  have M_non_empty: "M \<noteq> {}"
    using fu_stable unfolding finite_union_stable_def by auto 

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
          using fu_stable unfolding finite_union_stable_def by auto  
      qed
    qed 
    hence "range ?B \<subseteq> M" 
      by blast 
   
    ultimately have "\<Union> (range ?B) \<in> M"
      using M_non_empty ndu_stable unfolding non_decreasing_union_stable_def by auto 
    moreover have "\<Union> (range ?B) = \<Union> (range A)" 
      by fastforce 
    ultimately show "\<Union> (range A) \<in> M" 
      by auto 
  qed

  ultimately show ?thesis
    unfolding countable_union_stable_def by auto
qed

lemma dcu_c_empty_imp_ndu_stable: 
  assumes dcu_stable: "disj_countable_union_stable M"
      and c_stable: "complement_stable \<Omega> M"
      and empty_in: "{} \<in> M"
      and M_pow: "M \<subseteq> Pow \<Omega>"
    shows "non_decreasing_union_stable M"
proof - 
  have "M \<noteq> {}"
    using empty_in by auto 

  moreover have "\<forall>A. (range A \<subseteq> M \<and> non_decreasing A) \<longrightarrow> ((\<Union>i::nat. A i) \<in> M)" 
  proof (rule allI; rule impI)
    fix A :: "nat \<Rightarrow> 'a set" 
    assume A_is_nondecreasing_within_M: "range A \<subseteq> M \<and> non_decreasing A"
    let ?B = "(\<lambda>n. if n = 0 then A 0 else A n - A (n-1))"

    have "disjoint_family ?B"
      by (simp add: A_is_nondecreasing_within_M non_dec_to_disj)
       
    moreover have sd_stable: "set_diff_stable M"
      using assms dcu_c_empty_imp_sd_stable by auto
    hence "\<forall>n. ?B n \<in> M" 
    proof - 
      have "\<forall>n. ?B n = A 0 \<or> ?B n = A n - A (n-1)"
        by simp
      moreover have "\<forall>n. A n \<in> M"
        using A_is_nondecreasing_within_M by blast
      ultimately show "\<forall>n. ?B n \<in> M"
        using sd_stable unfolding set_diff_stable_def
        by (simp add: A_is_nondecreasing_within_M non_decreasing_multistep) 
    qed
    hence "range ?B \<subseteq> M"
      by blast
        
    ultimately have "((\<Union>i::nat. ?B i) \<in> M)"
      using dcu_stable unfolding disj_countable_union_stable_def by blast

    moreover have "\<Union> (range A) = (\<Union>i. ?B i)"
      by (simp add: A_is_nondecreasing_within_M non_dec_to_disj_same_cu)

    ultimately show "((\<Union>i. A i) \<in> M)"
      by simp 
  qed 

  ultimately show ?thesis
    by (simp add: non_decreasing_union_stable_def)
qed


definition non_increasing_inter_stable :: "'a set set \<Rightarrow> bool"
  where "non_increasing_inter_stable M = 
        ((M \<noteq> {}) \<and> (\<forall>A. (range A \<subseteq> M \<and> non_increasing A) \<longrightarrow> ((\<Inter>i::nat. A i) \<in> M)))"

lemma ci_imp_nii_stable: 
  assumes ci_stable: "countable_inter_stable M"
  shows "non_increasing_inter_stable M"
  using ci_stable unfolding countable_inter_stable_def non_increasing_inter_stable_def by simp 

lemma ndu_c_imp_nii_stable: 
  assumes ndu_stable: "non_decreasing_union_stable M"
      and c_stable: "complement_stable \<Omega> M"
      and M_pow: "M \<subseteq> Pow \<Omega>"
    shows "non_increasing_inter_stable M"
proof - 
  have "M \<noteq> {}"
    using c_stable complement_stable_def by auto

  moreover have "\<forall>A. range A \<subseteq> M \<and> non_increasing A \<longrightarrow> \<Inter> (range A) \<in> M"
  proof (rule; rule)
    fix A :: "nat \<Rightarrow> 'a set"
    let ?B = "(\<lambda>n. \<Omega> - A n)"
    assume A_non_inc_within_M: "range A \<subseteq> M \<and> non_increasing A"

    hence "non_decreasing ?B" 
      unfolding non_increasing_def non_decreasing_def by auto 
    moreover have "range ?B \<subseteq> M"
      using A_non_inc_within_M c_stable complement_stable_def by blast  
    ultimately have "\<Union> (range ?B) \<in> M" 
      using ndu_stable unfolding non_decreasing_union_stable_def by blast 
    hence "\<Omega> - \<Union> (range ?B) \<in> M" 
      using c_stable unfolding complement_stable_def by auto 

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
    unfolding non_increasing_inter_stable_def by auto 
qed


subsection "Algebras and Systems"

subsubsection "Exemplary Set Collections"

text "For now, these are just some famous types of set collections that people choose when they want
to prove something and need a convenient set to do it. We'll soon see what they're useful for.

The following proofs will be pretty easy. The heavy lifting was done in the previous subsection."

lemma algebra_omega_c_fu_stable: 
  shows "algebra \<Omega> M = (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> finite_union_stable M)"
proof 
  assume alg: "algebra \<Omega> M"
  hence "M \<subseteq> Pow \<Omega> \<and> {} \<in> M \<and> complement_stable \<Omega> M \<and> finite_union_stable M"
    using algebra_iff_Un complement_stable_def finite_union_stable_def by fastforce
  moreover have "\<Omega> \<in> M"
    by (simp add: alg algebra.top) 
  ultimately show "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> finite_union_stable M" 
    by simp 
next 
  assume "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> finite_union_stable M"
  moreover have "{} \<in> M"
    using calculation complement_stable_def Diff_cancel by metis 
  ultimately show "algebra \<Omega> M" 
    by (simp add: algebra_iff_Un complement_stable_def finite_union_stable_def) 
qed 

lemma algebra_omega_c_fi_stable: 
  shows "algebra \<Omega> M = (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> finite_inter_stable M)"
proof 
  assume "algebra \<Omega> M"
  hence "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> finite_union_stable M"
    by (simp add: algebra_omega_c_fu_stable)
  thus "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> finite_inter_stable M"
    by (meson Pow_iff c_fu_imp_fi_stable subset_iff)
next 
  assume "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> finite_inter_stable M"
  hence "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> finite_union_stable M"
    by (meson PowD c_fi_imp_fu_stable subset_eq)
  thus "algebra \<Omega> M"
    by (simp add: algebra_omega_c_fu_stable)
qed 

lemma sigma_algebra_omega_c_cu_stable: 
  shows "sigma_algebra \<Omega> M = (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> countable_union_stable M)"
proof -
  have "sigma_algebra \<Omega> M = (algebra \<Omega> M \<and> (\<forall>A. range A \<subseteq> M \<longrightarrow> (\<Union>i::nat. A i) \<in> M))"
    using sigma_algebra_iff by simp 
  hence "sigma_algebra \<Omega> M = (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> finite_union_stable M
        \<and> (\<forall>A. range A \<subseteq> M \<longrightarrow> (\<Union>i::nat. A i) \<in> M))"
    by (simp add: algebra_omega_c_fu_stable)
  thus ?thesis
    by (metis countable_union_stable_def empty_iff cu_imp_fu_stable)
qed

lemma sigma_algebra_omega_c_ci_stable: 
  shows "sigma_algebra \<Omega> M = (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> countable_inter_stable M)"
proof 
  assume "sigma_algebra \<Omega> M"
  hence "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> countable_union_stable M"
    by (simp add: sigma_algebra_omega_c_cu_stable)
  thus "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> countable_inter_stable M"
    by (meson Pow_iff c_cu_imp_ci_stable subset_iff)
next 
  assume "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> countable_inter_stable M"
  hence "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> countable_union_stable M"
    by (meson PowD c_ci_imp_cu_stable subset_eq)
  thus "sigma_algebra \<Omega> M"
    by (simp add: sigma_algebra_omega_c_cu_stable)
qed

lemma sigma_sd_stable: 
  assumes sa: "sigma_algebra \<Omega> M"
  shows "set_diff_stable M"
  by (meson c_fu_omega_imp_sd_stable cu_imp_fu_stable sa sigma_algebra_omega_c_cu_stable)

lemma empty_in_sigma: 
  assumes sa: "sigma_algebra \<Omega> M"
  shows "{} \<in> M"
proof - 
  have "\<Omega> - \<Omega> \<in> M"
    using sigma_algebra_omega_c_ci_stable sa unfolding complement_stable_def by blast 
  thus ?thesis 
    by auto 
qed 

locale monotone_class = subset_class + 
  assumes ndu_stable: "non_decreasing_union_stable M"
      and ncdi_stable: "non_increasing_inter_stable M"

lemma monotone_classI:
  assumes "M \<subseteq> Pow \<Omega>"
      and "non_decreasing_union_stable M"
      and "non_increasing_inter_stable M"
    shows "monotone_class \<Omega> M"
  by (simp add: assms monotone_class_axioms.intro monotone_class_def subset_class.intro)

lemma monotone_class_trivial:
  shows "monotone_class A (Pow A)"
  by (meson cu_imp_ndu_stable monotone_classI ndu_c_imp_nii_stable sigma_algebra_Pow 
      sigma_algebra_omega_c_cu_stable)

locale pi_system = subset_class + 
  assumes fi_stable: "finite_inter_stable M"

lemma pi_systemI:
  assumes "M \<subseteq> Pow \<Omega>"
      and "finite_inter_stable M"
    shows "pi_system \<Omega> M"
  by (simp add: assms pi_system.intro pi_system_axioms.intro subset_class.intro)

lemma Dynkin_omega_c_disju_stable:
  shows "Dynkin_system \<Omega> M = (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> disj_countable_union_stable M)"
proof - 
  have "Dynkin_system \<Omega> M = (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> (\<forall>A. A \<in> M \<longrightarrow> \<Omega> - A \<in> M) \<and> 
       (\<forall>A::nat \<Rightarrow> 'a set. disjoint_family A \<longrightarrow> range A \<subseteq> M \<longrightarrow> \<Union> (range A) \<in> M))"
    unfolding Dynkin_system_def Dynkin_system_axioms_def subset_class_def by fast 
  thus ?thesis 
    using complement_stable_def disj_countable_union_stable_def empty_iff by metis
qed

text "We show an equivalent definition of a Dynkin system."
lemma Dynkin_omega_diff_ndu_stable:
  shows "Dynkin_system \<Omega> M = 
         (M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> set_diff_stable M \<and> non_decreasing_union_stable M)"
proof
  assume dynk: "Dynkin_system \<Omega> M"
  hence "{} \<in> M"
    by (simp add: Dynkin_system.empty)
  thus "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> set_diff_stable M \<and> non_decreasing_union_stable M"
    by (metis Dynkin_omega_c_disju_stable dcu_c_empty_imp_ndu_stable dcu_c_empty_imp_sd_stable dynk)
next
  assume "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> set_diff_stable M \<and> non_decreasing_union_stable M"
  hence "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> disj_countable_union_stable M"
    using sd_omega_imp_c_stable sd_omega_imp_ndu_stable by auto
  thus "Dynkin_system \<Omega> M"
    using Dynkin_omega_c_disju_stable by auto 
qed 

subsubsection "Relations between Set Collections"

theorem algebra_is_pi:
  assumes a: "algebra \<Omega> M"
  shows "pi_system \<Omega> M"
proof - 
  have "subset_class \<Omega> M"
    by (meson algebra_omega_c_fi_stable a subset_class.intro)
  moreover have "finite_inter_stable M"
    using algebra_omega_c_fi_stable a by blast  
  ultimately show ?thesis
    by (simp add: pi_system.intro pi_system_axioms.intro) 
qed

theorem sigma_is_algebra: 
  assumes sa: "sigma_algebra \<Omega> M"
  shows "algebra \<Omega> M"
proof - 
  have "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> countable_union_stable M"
    by (meson sa sigma_algebra_omega_c_cu_stable)
  hence "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> finite_union_stable M"
    by (simp add: cu_imp_fu_stable)
  thus ?thesis
    by (simp add: algebra_omega_c_fu_stable) 
qed

theorem sigma_is_mono: 
  assumes sa: "sigma_algebra \<Omega> M"
  shows "monotone_class \<Omega> M"
proof - 
  have sa_properties: "M \<subseteq> Pow \<Omega> \<and> complement_stable \<Omega> M \<and> countable_union_stable M"
    using sa sigma_algebra_omega_c_cu_stable by auto

  hence "M \<subseteq> Pow \<Omega>"
    by simp
  moreover have "non_decreasing_union_stable M"
    by (simp add: cu_imp_ndu_stable sa_properties)
  moreover have "non_increasing_inter_stable M"
    using sa_properties calculation ndu_c_imp_nii_stable by auto

  ultimately show ?thesis
    unfolding monotone_class_def monotone_class_axioms_def subset_class_def by auto 
qed

theorem algebra_is_sigma_iff_mono: 
  assumes a: "algebra \<Omega> M"
  shows "sigma_algebra \<Omega> M = monotone_class \<Omega> M"
proof 
  assume "sigma_algebra \<Omega> M"
  thus "monotone_class \<Omega> M"
    by (simp add: sigma_is_mono) 
next
  assume "monotone_class \<Omega> M"
  hence "{} \<in> M \<and> finite_union_stable M \<and> non_decreasing_union_stable M"
    by (metis algebra_iff_Int algebra_omega_c_fu_stable a monotone_class.ndu_stable)
  hence "countable_union_stable M"
    by (simp add: ndu_fu_imp_cu_stable)  
  thus "sigma_algebra \<Omega> M"
    by (meson algebra_omega_c_fi_stable a sigma_algebra_omega_c_cu_stable) 
qed

theorem sigma_is_Dynkin:
  assumes sa: "sigma_algebra \<Omega> M"
  shows "Dynkin_system \<Omega> M"
proof - 

  have "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M"
    by (metis sa sigma_algebra_omega_c_cu_stable)

  moreover have "finite_union_stable M"
    using cu_imp_fu_stable sa sigma_algebra_omega_c_cu_stable by auto

  moreover have "complement_stable \<Omega> M"
    using sa sigma_algebra_omega_c_cu_stable by auto  
  hence "set_diff_stable M"
    using c_fu_omega_imp_sd_stable calculation
    by auto 

  ultimately show ?thesis
    by (simp add: sa sigma_algebra_imp_Dynkin_system)
qed 

theorem Dynkin_is_sigma_iff_pi: 
  assumes dynk: "Dynkin_system \<Omega> M"
  shows "sigma_algebra \<Omega> M = pi_system \<Omega> M"
proof 
  assume "sigma_algebra \<Omega> M"
  thus "pi_system \<Omega> M"
    by (simp add: algebra_is_pi sigma_is_algebra)
next 
  assume "pi_system \<Omega> M"
  hence "finite_inter_stable M \<and> complement_stable \<Omega> M \<and> (\<forall>S\<in>M. S \<subseteq> \<Omega>) \<and> non_decreasing_union_stable M"
    using dynk Dynkin_omega_diff_ndu_stable Dynkin_omega_c_disju_stable 
    unfolding pi_system_def pi_system_axioms_def by blast 
  hence "finite_union_stable M \<and> non_decreasing_union_stable M"
    using c_fi_imp_fu_stable by auto 
  hence "countable_union_stable M"
    by (simp add: ndu_fu_imp_cu_stable) 

  moreover have "M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M"
    by (metis Dynkin_omega_c_disju_stable dynk)
 
  ultimately show "sigma_algebra \<Omega> M"
    using sigma_algebra_omega_c_cu_stable by auto
qed

theorem Dynkin_is_mono:
  assumes dynk: "Dynkin_system \<Omega> M"
  shows "monotone_class \<Omega> M"
proof - 
  have "M \<subseteq> Pow \<Omega> \<and> complement_stable \<Omega> M \<and> non_decreasing_union_stable M"
    by (meson Dynkin_omega_c_disju_stable Dynkin_omega_diff_ndu_stable dynk)
  hence "M \<subseteq> Pow \<Omega> \<and> non_decreasing_union_stable M \<and> non_increasing_inter_stable M"
    using ndu_c_imp_nii_stable by auto
  thus ?thesis
    by (simp add: monotone_class.intro monotone_class_axioms.intro subset_class.intro) 
qed

theorem sigma_Pow_is_sigma:
  assumes sa: "sigma_algebra \<Omega> M"
      and subseq: "S \<in> M"
    shows "sigma_algebra S (Pow S)"
proof - 
  have "complement_stable S (Pow S)" 
    unfolding complement_stable_def by (simp add: Pow_not_empty complement_stable_def)
  moreover have "countable_union_stable (Pow S)" 
    unfolding countable_union_stable_def by blast 
  ultimately show ?thesis
    by (simp add: sigma_algebra_omega_c_cu_stable) 
qed 

theorem sigma_inter_is_sigma:
  assumes sas: "\<forall>M\<in>X. sigma_algebra \<Omega> M"
      and non_empty: "X \<noteq> {}"
    shows "sigma_algebra \<Omega> (\<Inter>M\<in>X. M)"
proof - 
  let ?I = "(\<Inter>M\<in>X. M)"

  have sa_properties: "\<forall>M\<in>X. M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> complement_stable \<Omega> M \<and> countable_union_stable M"
    by (meson sas sigma_algebra_omega_c_cu_stable)

  have "?I \<subseteq> Pow \<Omega>" 
  proof 
    fix x
    assume "x \<in> ?I"
    then obtain M where "M \<in> X \<and> x \<in> M" 
      using non_empty by auto 
    thus "x \<in> Pow \<Omega>"
      using sa_properties by auto 
  qed 

  moreover have "\<Omega> \<in> ?I"  
    using sa_properties by simp 
 
  moreover have "complement_stable \<Omega> ?I" 
    using sa_properties unfolding complement_stable_def by blast

  moreover have "countable_union_stable ?I" 
    unfolding countable_union_stable_def 
  proof 
    show "?I \<noteq> {}"
      using calculation(2) by auto
  next 
    show "\<forall>A :: (nat \<Rightarrow> 'a set). range A \<subseteq> ?I \<longrightarrow> \<Union> (range A) \<in> ?I"
      using sa_properties unfolding countable_union_stable_def
      by (simp add: le_Inf_iff) 
  qed

  ultimately show ?thesis
    by (simp add: sigma_algebra_omega_c_cu_stable)
qed

lemma Dynkin_inter_is_Dynkin:
  assumes dynks: "\<forall>M\<in>X. Dynkin_system \<Omega> M"
      and non_empty: "X \<noteq> {}"
    shows "Dynkin_system \<Omega> (\<Inter>M\<in>X. M)"
proof - 
  let ?I = "(\<Inter>M\<in>X. M)"

  have dy_properties: "\<forall>M\<in>X. M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> M \<and> set_diff_stable M \<and> non_decreasing_union_stable M"
    by (metis Dynkin_omega_diff_ndu_stable dynks)

  have "?I \<subseteq> Pow \<Omega>" 
  proof 
    fix x
    assume "x \<in> ?I"
    then obtain M where "M \<in> X \<and> x \<in> M" 
      using non_empty by auto 
    thus "x \<in> Pow \<Omega>"
      using dy_properties by auto 
  qed 

  moreover have "\<Omega> \<in> ?I"  
    using dy_properties by simp 
 
  moreover have "set_diff_stable ?I" 
    using dy_properties unfolding set_diff_stable_def by auto 

  moreover have "non_decreasing_union_stable ?I" 
    unfolding non_decreasing_union_stable_def 
  proof 
    show "?I \<noteq> {}"
      using calculation(2) by auto
  next 
    show "\<forall>A. range A \<subseteq> ?I \<and> non_decreasing A \<longrightarrow> \<Union> (range A) \<in> ?I"
      using dy_properties unfolding non_decreasing_union_stable_def
      by (simp add: le_Inf_iff) 
  qed

  ultimately show ?thesis
    by (simp add: Dynkin_omega_diff_ndu_stable)
qed

theorem sigma_ndu_is_algebra:
  assumes sas: "\<forall>n::nat. sigma_algebra \<Omega> (X n)"
      and non_dec: "non_decreasing X"
    shows "algebra \<Omega> (\<Union>(range X))"
proof -
  have a_properties: "\<forall>n. X n \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> X n \<and> complement_stable \<Omega> (X n) \<and> countable_union_stable (X n)"
    by (meson sas sigma_algebra_omega_c_cu_stable)

  hence "(\<Union>(range X)) \<subseteq> Pow \<Omega>" 
    by fast 

  moreover have "\<Omega> \<in> (\<Union>(range X))"
    using a_properties by auto 

  moreover have "complement_stable \<Omega> (\<Union>(range X))"
    using a_properties unfolding complement_stable_def by blast 

  moreover have "finite_union_stable (\<Union>(range X))"
    unfolding finite_union_stable_def 
  proof 
    show "\<Union> (range X) \<noteq> {}"
      using calculation(2) by auto
  next 
    have fu_stable: "\<forall>n. finite_union_stable (X n)"
      by (simp add: a_properties cu_imp_fu_stable)
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
          by (meson S_n non_dec non_decreasing_stay_in)
        thus "S \<union> T \<in> \<Union> (range X)"
          using fu_stable T_m unfolding finite_union_stable_def by auto 
      next
        case False
        hence "T \<in> X n"
          by (meson T_m nle_le non_dec non_decreasing_stay_in)  
        thus "S \<union> T \<in> \<Union> (range X)"
          using fu_stable S_n unfolding finite_union_stable_def by auto 
      qed 
    qed
  qed

  ultimately show ?thesis
    by (simp add: algebra_omega_c_fu_stable) 
qed

text "If M is a \<sigma>-algebra, and R \<subseteq> \<Omega>, then 'R \<inter> M' = {R \<inter> S : S \<in> M} is a \<sigma>-algebra on R."

theorem sigma_inter_coll_is_sigma:
  assumes sa: "sigma_algebra \<Omega> M"
      and subseq: "R \<subseteq> \<Omega>"
    shows "sigma_algebra R {C. \<exists>A \<in> M. C = R \<inter> A}"
proof - 
  let ?N = "{C. \<exists>S \<in> M. C = R \<inter> S}"
  have "?N \<subseteq> Pow R"
    by auto 

  moreover have "\<Omega> \<in> M"
    using sigma_algebra_omega_c_ci_stable sa by auto 
  hence "R \<in> ?N"
    using subseq by auto 

  moreover have "\<forall>S\<in>?N. R - S \<in> ?N" 
  proof 
    fix S
    assume "S \<in> ?N"
    then obtain T where T_choice: "T \<in> M \<and> S = R \<inter> T"
      by blast
    hence "R - S = R \<inter> (\<Omega> - T)"
      using subseq by fast 
    moreover have "\<Omega> - T \<in> M"
      using sigma_algebra_omega_c_ci_stable T_choice sa unfolding complement_stable_def by fast 
    ultimately show "R - S \<in> ?N" 
      by auto 
  qed
  hence "complement_stable R ?N" 
    using calculation(2) unfolding complement_stable_def by auto 

  moreover have "\<forall>A :: (nat \<Rightarrow> 'a set). range A \<subseteq> ?N \<longrightarrow> \<Union> (range A) \<in> ?N"
  proof (rule ; rule)
    fix A :: "nat \<Rightarrow> 'a set"
    assume "range A \<subseteq> ?N"
    hence "\<forall>n. \<exists>S \<in> M. A n = R \<inter> S"
      by auto 
    then obtain B where B_choice: "\<forall>n. ((A n = R \<inter> B n) \<and> (B n \<in> M))"
      by metis 

    hence "\<Union>(range A) = R \<inter> \<Union>(range B)" 
      by blast 

    moreover have "range B \<subseteq> M"
      using B_choice by auto 
    hence "\<Union>(range B) \<in> M" 
      using sa sigma_algebra_omega_c_cu_stable unfolding countable_union_stable_def by blast 

    ultimately show "\<Union> (range A) \<in> ?N"
      by auto  
  qed 
  hence "countable_union_stable ?N" 
    using calculation(2) unfolding countable_union_stable_def by auto

  ultimately show "sigma_algebra R ?N"
    by (simp add: sigma_algebra_omega_c_cu_stable)
qed

text "If \<Omega> and \<Omega>' are sets, M' a \<sigma>-algebra on \<Omega>' and T: \<Omega> \<rightarrow> \<Omega>' a mapping, then the collection of 
preimages of sets in M' is a \<sigma>-algebra on \<Omega>."

theorem preimage_sigma_on_domain: 
  fixes f :: "'a \<Rightarrow> 'b"
  assumes sa: "sigma_algebra \<Omega>' M'"
    shows "sigma_algebra (preimage f \<Omega>') {R. \<exists>S'\<in>M'. R = preimage f S'}"
proof - 
  let ?N = "{R. \<exists>S'\<in>M'. R = preimage f S'}"
  let ?\<Omega> = "preimage f \<Omega>'"

  have "?N \<subseteq> Pow ?\<Omega>" 
  proof 
    fix S
    assume "S \<in> ?N"
    hence "\<exists>S'\<in>M'. S = preimage f S'"
      by simp
    then obtain S' where "S = preimage f S'" and "S' \<subseteq> \<Omega>'"
      using sa sigma_algebra_omega_c_cu_stable PowD subsetD by metis 
    thus "S \<in> Pow ?\<Omega>"
      unfolding preimage_def by auto 
  qed 

  moreover have "?\<Omega> \<in> ?N"
    using sa sigma_algebra_omega_c_cu_stable by auto

  moreover have "(\<forall>S\<in>?N. ?\<Omega> - S \<in> ?N)"
  proof 
    fix S
    assume "S \<in> ?N"
    then obtain S' where S'_M': "S' \<in> M'" and "S = preimage f S'"
      by blast
    hence "?\<Omega> - S = (preimage f \<Omega>') - (preimage f S')"
      by simp
    hence "?\<Omega> - S = preimage f (\<Omega>' - S')"
      by (simp add: preimage_set_diff)  
    moreover have "(\<Omega>' - S') \<in> M'" 
      using sigma_algebra_omega_c_ci_stable sa S'_M' unfolding complement_stable_def by blast
    ultimately show "?\<Omega> - S \<in> ?N "
      by auto
  qed 
  hence "complement_stable ?\<Omega> ?N"
    unfolding complement_stable_def using calculation(2) by blast 

  moreover have "\<forall>A :: nat \<Rightarrow> 'a set. range A \<subseteq> ?N \<longrightarrow> \<Union> (range A) \<in> ?N"
  proof (rule ; rule)
    fix A :: "nat \<Rightarrow> 'a set"
    assume "range A \<subseteq> ?N" 
    hence "\<forall>n. \<exists>S'\<in>M'. A n = preimage f S'" 
      by auto 
    then obtain B where B_choice: "\<forall>n. B n \<in> M' \<and> A n = preimage f (B n)"
      by metis 
    hence "\<Union>(range A) = (\<Union>S\<in>(range B). preimage f S)" 
      by simp  
    hence "\<Union>(range A) = preimage f (\<Union>(range B))"
      using preimage_union by metis 
    moreover have "range B \<subseteq> M'"
      by (simp add: B_choice image_subsetI)
    hence "(\<Union>(range B)) \<in> M'"
      using sa sigma_algebra_omega_c_cu_stable B_choice unfolding countable_union_stable_def by auto  
    ultimately show  "\<Union> (range A) \<in> ?N"
      by blast
  qed 
  hence "countable_union_stable ?N"
    unfolding countable_union_stable_def using calculation(2) by blast 

  ultimately show "sigma_algebra ?\<Omega> ?N"
    by (simp add: sigma_algebra_omega_c_cu_stable)
qed 

text "For the infinite set \<Omega>, M consists of all S \<subseteq> \<Omega>, such that either S or -S is finite, then 
M is an algebra..."

lemma finite_cofinite_algebra:
  assumes infinite_ground: "infinite \<Omega>"
  shows "algebra \<Omega> {S. S \<subseteq> \<Omega> \<and> (finite S \<or> finite (\<Omega>-S))}"
proof - 
  let ?M = "{S. S \<subseteq> \<Omega> \<and> (finite S \<or> finite (\<Omega>-S))}"
  
  have "?M \<subseteq> Pow \<Omega> \<and> \<Omega> \<in> ?M"
    by auto  

  moreover have "(\<forall>S\<in>?M. \<Omega> - S \<in> ?M)"  
  proof 
    fix S 
    assume S_in_M: "S \<in> ?M"
    thus "\<Omega> - S \<in> ?M"
    proof (cases "finite S")
      case True
      hence "finite (\<Omega>-(\<Omega>-S))"
        by (simp add: Diff_Diff_Int)
      then show ?thesis
        by simp 
    next
      case False
      then show ?thesis
        using S_in_M by auto
    qed
  qed
  hence "complement_stable \<Omega> ?M" 
    unfolding complement_stable_def by blast  
  
  moreover have "(\<forall>S\<in>?M. \<forall>T\<in>?M. S \<inter> T \<in> ?M)" 
  proof (rule ; rule)
    fix S T assume S_in_M: "S \<in> ?M" and T_in_M: "T \<in> ?M"
    then consider (F) "finite S \<or> finite T"  | (II) "infinite S \<and> infinite T"
      by auto
    thus "S \<inter> T \<in> ?M"
    proof cases
      case F
      then show ?thesis
        using S_in_M by blast 
    next
      case II
      consider (fin_int) "finite (S \<inter> T)" | (inf_int) "infinite (S \<inter> T)"
        by fast 
      then show ?thesis 
      proof cases
        case fin_int
        then show ?thesis
          using S_in_M by auto 
      next
        case inf_int
        moreover have "finite (\<Omega> - S)"
          using II S_in_M by auto
        moreover have "finite (\<Omega> - T)"
          using II T_in_M by auto
        moreover have "\<Omega> - (S \<inter> T) = (\<Omega> - S) \<union> (\<Omega> - T)"
          by auto 
        ultimately show ?thesis
          using S_in_M by auto 
      qed 
    qed 
  qed 
  hence "finite_inter_stable ?M"
    unfolding finite_inter_stable_def by blast 

  ultimately show "algebra \<Omega> ?M"
    by (simp add: algebra_omega_c_fi_stable) 
qed

text "...but not a \<sigma>-algebra."

lemma finite_cofinite_no_sigma:
  assumes infinite_ground: "infinite \<Omega>"
  shows "\<not>sigma_algebra \<Omega> {S. S \<subseteq> \<Omega> \<and> (finite S \<or> finite (\<Omega>-S))}"
proof - 
  let ?M = "{S. S \<subseteq> \<Omega> \<and> (finite S \<or> finite (\<Omega>-S))}"

  have "\<exists>A :: (nat \<Rightarrow> 'a set). range A \<subseteq> ?M \<and> \<Union> (range A) \<notin> ?M"
  proof (cases "countable \<Omega>")
    case True
    then obtain f :: "nat \<Rightarrow> 'a" where f_sur: "range f = \<Omega>" and f_inj: "inj f"
      by (metis countable_as_injective_image infinite_ground)
    let ?E = "(\<lambda>n::nat. 2 * n) ` UNIV"
    let ?O = "(\<lambda>n::nat. 2 * n + 1) ` UNIV"
    let ?A = "(\<lambda>n. if n\<in>?E then {f n} else {})"

    have "\<Union> (range ?A) = image f ?E"
      by auto

    moreover have "infinite (image f ?E)"
      using f_inj inj_infinite_image even_inf by blast

    moreover have "?O = UNIV - ?E"
      by (metis even_odd_disjoint even_odd_UNIV Diff_cancel 
          Diff_triv Int_Un_eq(2) Int_commute Un_Diff)
    hence "(\<Omega> - image f ?E) = image f ?O"
      by (metis Compl_eq_Diff_UNIV f_inj image_set_diff f_sur)
    hence "infinite (\<Omega> - image f ?E)"  
      using f_inj inj_infinite_image odd_inf by auto 

    ultimately have "\<Union> (range ?A) \<notin> ?M"
      by auto 

    moreover have "\<forall>n. finite (?A n) \<and> (?A n) \<subseteq> \<Omega>"
      using f_sur by auto
    hence "range ?A \<subseteq> ?M"
      by blast 

    ultimately show ?thesis
      by blast   
  next
    case False
    obtain f :: "nat \<Rightarrow> 'a" where f_range: "range f \<subseteq> \<Omega>" and f_inj: "inj f"
      using infinite_countable_subset infinite_ground by blast
    let ?A = "(\<lambda>n. {f n})"

    have "\<Union> (range ?A) = image f UNIV"
      by auto 
    moreover have "infinite (image f UNIV)" 
      using f_inj finite_imageD by auto 
    moreover have "uncountable \<Omega>"
      using False by auto 
    hence "infinite (\<Omega> - image f UNIV)"
      by (simp add: uncountable_infinite uncountable_minus_countable)   
    ultimately have "range ?A \<subseteq> ?M \<and> \<Union> (range ?A) \<notin> ?M" 
      using f_range by auto 
    thus ?thesis 
      by meson  
    qed
    hence "\<not>(countable_union_stable ?M)" 
      using countable_union_stable_def by (metis (no_types)) 

  thus "\<not>sigma_algebra \<Omega> ?M" 
    using sigma_algebra_omega_c_cu_stable by auto 
qed

section "Generators"

subsection "Least Set Collections"

subsubsection "Least Sigma Algebras"

(* 'sigma_sets \<Omega> M' describes the smallest sigma algebra containing all sets in M.
   The LEAST operator guarantees uniqueness. *)
lemma sigma_sets_Least: 
  assumes M_Pow: "M \<subseteq> Pow \<Omega>"
  shows "sigma_sets \<Omega> M = (LEAST N. M \<subseteq> N \<and> sigma_algebra \<Omega> N)"
proof - 
  have "{N. M \<subseteq> N \<and> sigma_algebra \<Omega> N} \<noteq> {}"
    using sigma_algebra_Pow M_Pow by auto 
  hence "sigma_algebra \<Omega> (\<Inter>N\<in>{N. M \<subseteq> N \<and> sigma_algebra \<Omega> N}. N)"
    by (metis (mono_tags, lifting) mem_Collect_eq sigma_inter_is_sigma)
  hence "(LEAST N. M \<subseteq> N \<and> sigma_algebra \<Omega> N) = (\<Inter>N\<in>{N. M \<subseteq> N \<and> sigma_algebra \<Omega> N}. N)"
    using inter_is_Least_if_P
    by (metis (mono_tags, lifting) Inf_greatest image_ident mem_Collect_eq) 
  thus ?thesis 
    using sigma_sets_least_sigma_algebra M_Pow image_ident by metis 
qed

corollary
  assumes M_Pow: "M \<subseteq> Pow \<Omega>"
  shows "sigma_algebra \<Omega> (sigma_sets \<Omega> M)"
  by (simp add: assms sigma_algebra_sigma_sets)

definition generates_sigma_algebra :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> bool"
  where "generates_sigma_algebra N \<Omega> M = (M = sigma_sets \<Omega> N)"

subsubsection "Least Dynkin systems"

lemma Dynkin_Least:
  assumes M_Pow: "M \<subseteq> Pow \<Omega>"
  shows "Dynkin \<Omega> M = (LEAST N. M \<subseteq> N \<and> Dynkin_system \<Omega> N)"
proof - 
  have "{N. M \<subseteq> N \<and> Dynkin_system \<Omega> N} \<noteq> {}"
    using Dynkin_system_trivial M_Pow by auto
  hence "Dynkin_system \<Omega> (\<Inter>N\<in>{N. M \<subseteq> N \<and> Dynkin_system \<Omega> N}. N)"
    by (metis (mono_tags, lifting) Dynkin_inter_is_Dynkin mem_Collect_eq)
  hence "(LEAST N. M \<subseteq> N \<and> Dynkin_system \<Omega> N) = (\<Inter>N\<in>{N. M \<subseteq> N \<and> Dynkin_system \<Omega> N}. N)"
    using inter_is_Least_if_P
    by (metis (mono_tags, lifting) INT_greatest mem_Collect_eq)
  thus ?thesis
    by (metis (mono_tags, lifting) Collect_cong Dynkin_def image_ident) 
qed

corollary
  assumes M_Pow: "M \<subseteq> Pow \<Omega>"
  shows "Dynkin_system \<Omega> (Dynkin \<Omega> M)"
  by (simp add: Dynkin_system_Dynkin assms)

definition generates_dynkin_system :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> bool"
  where "generates_dynkin_system N \<Omega> M = (M = Dynkin \<Omega> N)"

subsubsection "Least Monotone classes"

definition Mono :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set" where
  "Mono \<Omega> M =  (\<Inter>{N. monotone_class \<Omega> N \<and> M \<subseteq> N})"

lemma monotone_class_Mono:
  assumes M_Pow: "M \<subseteq> Pow (\<Omega>)"
      and non_empty: "M \<noteq> {}"
  shows "monotone_class \<Omega> (Mono \<Omega> M)"
proof (rule monotone_classI)
  show "Mono \<Omega> M \<subseteq> Pow \<Omega>"
  proof 
    fix x 
    assume "x \<in> Mono \<Omega> M"
    then obtain N where "monotone_class \<Omega> N \<and> x \<in> N"
      by (metis (no_types, lifting) Inter_iff Mono_def M_Pow mem_Collect_eq monotone_class_trivial)
    thus "x \<in> Pow \<Omega>"
      by (meson PowI monotone_class_def subset_class.sets_into_space)  
  qed 
next
  have "\<forall>A. range A \<subseteq> Mono \<Omega> M \<and> non_decreasing A \<longrightarrow> \<Union> (range A) \<in> Mono \<Omega> M"
  proof (rule ; rule ; erule conjE)
    fix A :: "nat \<Rightarrow> 'a set"
    assume A_range: "range A \<subseteq> Mono \<Omega> M" and A_nd: "non_decreasing A"
    thus "\<Union> (range A) \<in> Mono \<Omega> M" 
      unfolding Mono_def monotone_class_def monotone_class_axioms_def non_decreasing_union_stable_def
      by blast 
  qed 
  thus "non_decreasing_union_stable (Mono \<Omega> M)"
    unfolding non_decreasing_union_stable_def Mono_def 
    using monotone_class_trivial M_Pow non_empty by blast 
next
  have "\<forall>A. range A \<subseteq> Mono \<Omega> M \<and> non_increasing A \<longrightarrow> \<Inter> (range A) \<in> Mono \<Omega> M"
  proof (rule ; rule ; erule conjE)
    fix A :: "nat \<Rightarrow> 'a set"
    assume A_range: "range A \<subseteq> Mono \<Omega> M" and A_ni: "non_increasing A"
    thus "\<Inter> (range A) \<in> Mono \<Omega> M"
      unfolding Mono_def monotone_class_def monotone_class_axioms_def non_increasing_inter_stable_def
      by blast 
  qed 
  thus "non_increasing_inter_stable (Mono \<Omega> M)"
    unfolding non_increasing_inter_stable_def Mono_def 
    using monotone_class_trivial M_Pow non_empty by blast 
qed

lemma Mono_Least:
  assumes M_Pow: "M \<subseteq> Pow \<Omega>"
      and non_empty: "M \<noteq> {}"
  shows "Mono \<Omega> M = (LEAST N. M \<subseteq> N \<and> monotone_class \<Omega> N)"
proof - 
  have "monotone_class \<Omega> (\<Inter> {N. monotone_class \<Omega> N \<and> M \<subseteq> N})"
    using assms monotone_class_Mono unfolding Mono_def by blast 
  hence "(LEAST N. M \<subseteq> N \<and> monotone_class \<Omega> N) = (\<Inter>N\<in>{N. M \<subseteq> N \<and> monotone_class \<Omega> N}. N)"
    using inter_is_Least_if_P
    by (smt (verit) image_ident le_Inf_iff mem_Collect_eq set_eq_subset)
  thus ?thesis
    by (metis (mono_tags, lifting) Collect_cong Mono_def image_ident)
qed

definition generates_monotone_class :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> bool"
  where "generates_monotone_class N \<Omega> M = (M = Mono \<Omega> N)"

subsection "Relations between least collections"

text "If M = A, a single set, then \<sigma>{M} = \<sigma>{A} = {{}, A, \<Omega>-A, \<Omega>}."
corollary
  assumes subseq: "A \<subseteq> \<Omega>"
  shows "sigma_sets \<Omega> {A} = {{}, A, \<Omega>-A, \<Omega>}"
  by (simp add: sigma_sets_singleton subseq)

text "If M is a \<sigma>-algebra, then \<sigma>{M} = M"
corollary 
  assumes "sigma_algebra \<Omega> M"
  shows "sigma_sets \<Omega> M = M"
  by (simp add: assms sigma_algebra.sigma_sets_eq)

text "Let M be an algebra. Then \<MM>(M) = \<sigma>(M)."
theorem monotone_class_theorem:
  assumes alg: "algebra \<Omega> M"
  shows "Mono \<Omega> M = sigma_sets \<Omega> M"
proof 
  text "Since every \<sigma>-algebra is a monotone class and \<MM>(M) is the minimal monotone class containing
        M, we know from the outset that \<MM>(M) \<subseteq> \<sigma>(M)."
  have "sigma_algebra \<Omega> (sigma_sets \<Omega> M)"
    by (metis algebra_iff_Un assms sigma_algebra_sigma_sets)
  hence "monotone_class \<Omega> (sigma_sets \<Omega> M)"
    by (simp add: sigma_is_mono)
  moreover have "M \<subseteq> (sigma_sets \<Omega> M)"
    by (simp add: sigma_sets_superset_generator)
  moreover have M_non_empty_subseq: "M \<noteq> {} \<and> M \<subseteq> Pow \<Omega>"
    using algebra.top alg algebra_iff_Int empty_iff by metis 
  hence Mono_least: "Mono \<Omega> M = (LEAST N. M \<subseteq> N \<and> monotone_class \<Omega> N)"
    using Mono_Least by auto
  ultimately show "Mono \<Omega> M \<subseteq> sigma_sets \<Omega> M"
    by (metis (mono_tags, lifting) Inter_lower Mono_def mem_Collect_eq) 
next 
  have "M \<noteq> {} \<and> M \<subseteq> Pow \<Omega>"
    using algebra.top alg algebra_iff_Int empty_iff by metis 
  hence mono_mono: "monotone_class \<Omega> (Mono \<Omega> M)"
    by (simp add: monotone_class_Mono)
  text "To prove the opposite inclusion we must, due to the minimality of \<sigma>{M}, prove that \<MM>{M}
        is a \<sigma>-algebra, for which it is sufficient to prove that \<MM>{M} is an algebra."
  moreover have "algebra \<Omega> (Mono \<Omega> M)" 
  proof -
    have mono_Pow: "(Mono \<Omega> M) \<subseteq> Pow \<Omega>"
      using mono_mono monotone_class_def subset_class_def by blast
    moreover have M_subseq: "M \<subseteq> (Mono \<Omega> M)"
      unfolding Mono_def by auto 

    (* \<MM>(M) is complement-stable. *)
    moreover have "\<forall>S\<in>Mono \<Omega> M. \<forall>T\<in>Mono \<Omega> M. \<Omega> - S \<in> Mono \<Omega> M \<and> S \<union> T \<in> Mono \<Omega> M" 
    proof -
      let ?\<xi> = "{S\<in>Mono \<Omega> M. \<forall>T\<in>M. S \<union> T \<in> Mono \<Omega> M}"
      let ?\<xi>' = "{S\<in>Mono \<Omega> M. \<Omega> - S \<in> Mono \<Omega> M}"
      let ?\<xi>'' = "{S\<in>Mono \<Omega> M. \<forall>T\<in>Mono \<Omega> M. S \<union> T \<in> Mono \<Omega> M}"
        
      have "Mono \<Omega> M = ?\<xi>''"
      proof -
        have "{} \<in> ?\<xi>''"
          using M_subseq algebra_iff_Un assms by auto
        hence ne_xi'': "?\<xi>'' \<noteq> {}"
          by blast
        hence ne_xi: "?\<xi> \<noteq> {}"
          using M_subseq by blast 

        have "Mono \<Omega> M = ?\<xi>"
        proof 
          text "We first note that \<xi> is a monotone class via the identities 
                (\<Inter>n. A n) \<union> S = (\<Inter>n. A n \<union> S) and (\<Union>n. A n) \<union> S = (\<Union>n. A n \<union> S)."
          have "monotone_class \<Omega> ?\<xi>"
            unfolding monotone_class_def monotone_class_axioms_def subset_class_def 
          proof (rule ; rule)
            fix x
            assume "x \<in> ?\<xi>"
            thus "x \<in> Pow \<Omega>"
              using mono_Pow by auto
          next 
            have "\<forall>A. range A \<subseteq> ?\<xi> \<and> non_decreasing A \<longrightarrow> \<Union> (range A) \<in> ?\<xi>"
            proof (rule ; rule ; erule conjE)
              fix A :: "nat \<Rightarrow> 'a set"
              assume A_rng: "range A \<subseteq> ?\<xi>" and A_nd: "non_decreasing A"
              hence "range A \<subseteq> Mono \<Omega> M \<and> non_decreasing A"
                by auto
              hence "\<Union> (range A) \<in> Mono \<Omega> M" 
                using mono_mono 
                unfolding monotone_class_def monotone_class_axioms_def non_decreasing_union_stable_def
                by auto 
              moreover have "\<forall>T\<in>M. \<Union> (range A) \<union> T \<in> Mono \<Omega> M"  
              proof 
                fix T
                let ?B = "(\<lambda>n. A n \<union> T)"
                assume "T \<in> M"
                hence "\<forall>n. ?B n \<in> Mono \<Omega> M"
                  using A_rng by auto
                moreover have "non_decreasing ?B"
                  using A_nd unfolding non_decreasing_def by blast
                ultimately have "\<Union> (range ?B) \<in> Mono \<Omega> M" 
                  using mono_mono 
                  unfolding monotone_class_def monotone_class_axioms_def non_decreasing_union_stable_def
                  by auto 
                thus "\<Union> (range A) \<union> T \<in> Mono \<Omega> M" 
                  by auto 
              qed
               
              ultimately show "\<Union> (range A) \<in> ?\<xi>"
                by auto  
            qed
            thus "non_decreasing_union_stable ?\<xi>"
              using ne_xi unfolding non_decreasing_union_stable_def by auto  
          next 
            have "\<forall>A. range A \<subseteq> ?\<xi> \<and> non_increasing A \<longrightarrow> \<Inter> (range A) \<in> ?\<xi>"
            proof (rule ; rule ; erule conjE)
              fix A :: "nat \<Rightarrow> 'a set"
              assume A_rng: "range A \<subseteq> ?\<xi>" and A_ni: "non_increasing A"
              hence "range A \<subseteq> Mono \<Omega> M \<and> non_increasing A"
                by auto
              hence "\<Inter> (range A) \<in> Mono \<Omega> M" 
                using mono_mono 
                unfolding monotone_class_def monotone_class_axioms_def non_increasing_inter_stable_def
                by auto 
              moreover have "\<forall>T\<in>M. \<Inter> (range A) \<union> T \<in> Mono \<Omega> M"  
              proof 
                fix T
                let ?B = "(\<lambda>n. A n \<union> T)"
                assume "T \<in> M"
                hence "\<forall>n. ?B n \<in> Mono \<Omega> M"
                  using A_rng by blast 
                moreover have "non_increasing ?B"
                  using A_ni unfolding non_increasing_def by blast
                ultimately have "\<Inter> (range ?B) \<in> Mono \<Omega> M" 
                  using mono_mono 
                  unfolding monotone_class_def monotone_class_axioms_def non_increasing_inter_stable_def
                  by auto 
                thus "\<Inter> (range A) \<union> T \<in> Mono \<Omega> M" 
                  by auto 
              qed
               
              ultimately show "\<Inter> (range A) \<in> ?\<xi>"
                by auto  
            qed
            thus "non_increasing_inter_stable ?\<xi>"
              using ne_xi unfolding non_increasing_inter_stable_def by auto 
          qed 
          moreover have "M \<subseteq> ?\<xi>"
            by (smt (verit) Ball_Collect M_subseq algebra_iff_Un assms subset_iff)  
          text "\<MM>(M) \<subseteq> \<xi>, in view of minimality of \<MM>(M)."
          ultimately show "Mono \<Omega> M \<subseteq> ?\<xi>"
            unfolding Mono_def by blast 
        next 
          text "\<xi> \<subseteq> \<MM>(M), by construction."
          show "?\<xi> \<subseteq> Mono \<Omega> M" 
            by auto  
        qed
        hence "\<forall>S\<in>Mono \<Omega> M. \<forall>T\<in>M. S \<union> T \<in> Mono \<Omega> M"
          by blast
        hence "\<forall>T\<in>M. \<forall>S\<in>Mono \<Omega> M. T \<union> S \<in> Mono \<Omega> M"
          by (metis sup_commute)
        hence "M \<subseteq> ?\<xi>''"
          using M_subseq by blast 

        text "\<xi>'' is a monotone class due to the same identities as \<xi>."
        moreover have "monotone_class \<Omega> ?\<xi>''" 
        unfolding monotone_class_def monotone_class_axioms_def subset_class_def 
          proof (rule ; rule)
            fix x
            assume "x \<in> ?\<xi>''"
            thus "x \<in> Pow \<Omega>"
              using mono_Pow by auto
          next 
            have "\<forall>A. range A \<subseteq> ?\<xi>'' \<and> non_decreasing A \<longrightarrow> \<Union> (range A) \<in> ?\<xi>''"
            proof (rule ; rule ; erule conjE)
              fix A :: "nat \<Rightarrow> 'a set"
              assume A_rng: "range A \<subseteq> ?\<xi>''" and A_nd: "non_decreasing A"
              hence "range A \<subseteq> Mono \<Omega> M \<and> non_decreasing A"
                by auto
              hence "\<Union> (range A) \<in> Mono \<Omega> M" 
                using mono_mono 
                unfolding monotone_class_def monotone_class_axioms_def non_decreasing_union_stable_def
                by auto 
              moreover have "\<forall>T\<in>Mono \<Omega> M. \<Union> (range A) \<union> T \<in> Mono \<Omega> M"  
              proof 
                fix T
                let ?B = "(\<lambda>n. A n \<union> T)"
                assume "T \<in> Mono \<Omega> M"
                hence "\<forall>n. ?B n \<in> Mono \<Omega> M"
                  using A_rng by auto
                moreover have "non_decreasing ?B"
                  using A_nd unfolding non_decreasing_def by blast
                ultimately have "\<Union> (range ?B) \<in> Mono \<Omega> M" 
                  using mono_mono 
                  unfolding monotone_class_def monotone_class_axioms_def non_decreasing_union_stable_def
                  by auto 
                thus "\<Union> (range A) \<union> T \<in> Mono \<Omega> M" 
                  by auto 
              qed
               
              ultimately show "\<Union> (range A) \<in> ?\<xi>''"
                by auto  
            qed
            thus "non_decreasing_union_stable ?\<xi>''"
              using ne_xi'' unfolding non_decreasing_union_stable_def by auto 
          next 
            have "\<forall>A. range A \<subseteq> ?\<xi>'' \<and> non_increasing A \<longrightarrow> \<Inter> (range A) \<in> ?\<xi>''"
            proof (rule ; rule ; erule conjE)
              fix A :: "nat \<Rightarrow> 'a set"
              assume A_rng: "range A \<subseteq> ?\<xi>''" and A_ni: "non_increasing A"
              hence "range A \<subseteq> Mono \<Omega> M \<and> non_increasing A"
                by auto
              hence "\<Inter> (range A) \<in> Mono \<Omega> M" 
                using mono_mono 
                unfolding monotone_class_def monotone_class_axioms_def non_increasing_inter_stable_def
                by auto 
              moreover have "\<forall>T\<in>Mono \<Omega> M. \<Inter> (range A) \<union> T \<in> Mono \<Omega> M"  
              proof 
                fix T
                let ?B = "(\<lambda>n. A n \<union> T)"
                assume "T \<in> Mono \<Omega> M"
                hence "\<forall>n. ?B n \<in> Mono \<Omega> M"
                  using A_rng by blast 
                moreover have "non_increasing ?B"
                  using A_ni unfolding non_increasing_def by blast
                ultimately have "\<Inter> (range ?B) \<in> Mono \<Omega> M" 
                  using mono_mono 
                  unfolding monotone_class_def monotone_class_axioms_def non_increasing_inter_stable_def
                  by auto 
                thus "\<Inter> (range A) \<union> T \<in> Mono \<Omega> M" 
                  by auto 
              qed
              ultimately show "\<Inter> (range A) \<in> ?\<xi>''"
                by simp
            qed
            thus "non_increasing_inter_stable ?\<xi>''"
              using ne_xi'' unfolding non_increasing_inter_stable_def by auto 
          qed

        (* \<MM>(M) is finite-union-stable. *)
        ultimately show "Mono \<Omega> M = ?\<xi>''" 
          using Mono_def by blast 
      qed 

      moreover have "Mono \<Omega> M = ?\<xi>'"
      proof 
        have "?\<xi>' \<subseteq> Pow \<Omega>"
          using mono_Pow by auto  
        moreover have "\<forall>A. range A \<subseteq> ?\<xi>' \<and> non_decreasing A \<longrightarrow> \<Union> (range A) \<in> ?\<xi>'"
        proof (rule ; rule ; erule conjE)
          fix A :: "nat \<Rightarrow> 'a set"
          assume A_rng: "range A \<subseteq> ?\<xi>'" and A_nd: "non_decreasing A"
          hence "range A \<subseteq> Mono \<Omega> M \<and> non_decreasing A"
            by auto
          hence "\<Union> (range A) \<in> Mono \<Omega> M" 
            using mono_mono 
            unfolding monotone_class_def monotone_class_axioms_def non_decreasing_union_stable_def
             by simp 
          moreover have "\<Omega> - \<Union> (range A) \<in> Mono \<Omega> M" 
          proof - 
            let ?B = "(\<lambda>n. \<Omega> - A n)"
            have "range ?B \<subseteq> Mono \<Omega> M"
              using A_rng by blast
            moreover have "non_increasing ?B"
              by (simp add: A_nd nd_complement_ni) 
            moreover have "\<Omega> - \<Union> (range A) = \<Inter> (range ?B)" 
              by simp 
            ultimately show ?thesis
              using mono_mono 
              unfolding monotone_class_def monotone_class_axioms_def non_increasing_inter_stable_def
              by metis 
          qed
          ultimately show "\<Union> (range A) \<in> ?\<xi>'"
            by simp 
        qed 
        moreover have "\<forall>A. range A \<subseteq> ?\<xi>' \<and> non_increasing A \<longrightarrow> \<Inter> (range A) \<in> ?\<xi>'"
        proof (rule ; rule ; erule conjE)
          fix A :: "nat \<Rightarrow> 'a set"
          assume A_rng: "range A \<subseteq> ?\<xi>'" and A_ni: "non_increasing A"
          hence "range A \<subseteq> Mono \<Omega> M \<and> non_increasing A"
            by auto
          hence "\<Inter> (range A) \<in> Mono \<Omega> M" 
            using mono_mono 
            unfolding monotone_class_def monotone_class_axioms_def non_increasing_inter_stable_def
             by simp 
          moreover have "\<Omega> - \<Inter> (range A) \<in> Mono \<Omega> M" 
          proof - 
            let ?B = "(\<lambda>n. \<Omega> - A n)"
            have "range ?B \<subseteq> Mono \<Omega> M"
              using A_rng by blast
            moreover have "non_decreasing ?B"
              by (simp add: A_ni ni_complement_nd) 
            moreover have "\<Omega> - \<Inter> (range A) = \<Union> (range ?B)" 
              by simp 
            ultimately show ?thesis
              using mono_mono 
              unfolding monotone_class_def monotone_class_axioms_def non_decreasing_union_stable_def
              by metis 
          qed
          ultimately show "\<Inter> (range A) \<in> ?\<xi>'"
            by simp 
        qed
        moreover have "?\<xi>' \<noteq> {}"
          using M_subseq algebra.compl_sets algebra.top assms by blast
        ultimately have "monotone_class \<Omega> ?\<xi>'"
          using monotone_classI non_decreasing_union_stable_def non_increasing_inter_stable_def
          by (metis (no_types, lifting)) 
        moreover have "M \<subseteq> ?\<xi>'"
          using M_subseq algebra.compl_sets assms by auto 
        ultimately show "Mono \<Omega> M \<subseteq> ?\<xi>'" 
          unfolding Mono_def by blast 
      next  
        show "?\<xi>' \<subseteq> Mono \<Omega> M" by auto 
      qed 

      ultimately show ?thesis
        by blast  
    qed

    ultimately show ?thesis
      using complement_stable_def finite_union_stable_def unfolding algebra_omega_c_fu_stable
      using algebra_omega_c_fu_stable assms by fastforce 
  qed

  ultimately have "sigma_algebra \<Omega> (Mono \<Omega> M)"
    by (simp add: algebra_is_sigma_iff_mono)

  moreover have "sigma_sets \<Omega> M = (LEAST N. M \<subseteq> N \<and> sigma_algebra \<Omega> N)" 
    using sigma_sets_Least alg algebra_omega_c_fu_stable by metis

  ultimately show "sigma_sets \<Omega> M \<subseteq> Mono \<Omega> M"
    by (metis (no_types, lifting) Inter_greatest Mono_def mem_Collect_eq sigma_algebra.sigma_sets_subset)  
qed

text "By suppressing the minimality of the monotone class, the following corollary emerges."

lemma sigma_of_algebra_in_mono:
  assumes alg: "algebra \<Omega> M"
      and mono: "monotone_class \<Omega> N"
      and subseq: "M \<subseteq> N"
    shows "sigma_sets \<Omega> M \<subseteq> N"
proof - 
  have "Mono \<Omega> M \<subseteq> N"
    using mono subseq unfolding Mono_def by auto 
  thus ?thesis
    using alg monotone_class_theorem by auto 
qed

text "A related theorem, 'Dynkin's pi-lambda theorem', concerns the equality between the Dynkin
      system and the \<sigma>-algebra generated by the same \<pi>-system."

theorem dynkin_pi_lambda:
  assumes pi: "pi_system \<Omega> M"
  shows "Dynkin \<Omega> M = sigma_sets \<Omega> M"
proof 
  text "\<D>(M) \<subseteq> \<sigma>(M), since every \<sigma>-algebra is a Dynkin system."
  have "M \<subseteq> Pow \<Omega>"
    using pi pi_system_def subset_class.space_closed by blast
  hence "sigma_algebra \<Omega> (sigma_sets \<Omega> M)"
    using sigma_algebra_sigma_sets by auto
  hence "Dynkin_system \<Omega> (sigma_sets \<Omega> M)"
    by (simp add: sigma_algebra_imp_Dynkin_system)
  thus "Dynkin \<Omega> M \<subseteq> sigma_sets \<Omega> M"
    unfolding Dynkin_def by blast 
next 
  text "For the converse, we must show that \<D>(M) is a \<pi>-system."
  have "pi_system \<Omega> (Dynkin \<Omega> M)"
  proof - 
    text "In order to achieve this, let \<D> T = {S\<subseteq>\<Omega> : S \<inter> T \<in> Dynkin \<Omega> M} and show that this is a 
          Dynkin system."
    have Dynkin_dynk: "Dynkin_system \<Omega> (Dynkin \<Omega> M)"
      by (meson Dynkin_system_Dynkin pi pi_system.axioms(1) subset_class_def)
    hence Dynkin_Pow: "(Dynkin \<Omega> M) \<subseteq> Pow \<Omega>" 
      using Dynkin_omega_c_disju_stable by auto 

    let ?\<D> = "(\<lambda>T. {S. S \<subseteq> \<Omega> \<and> S \<inter> T \<in> Dynkin \<Omega> M})"
    have \<D>_Dynkin: "\<forall>T\<in>Dynkin \<Omega> M. Dynkin_system \<Omega> (?\<D> T)"
    proof 
      text "Let T \<in> \<D>(M)."
      fix T
      assume T_in_dynk: "T \<in> Dynkin \<Omega> M"
      text "Since \<Omega> \<inter> T = T, it follows that \<Omega> \<in> \<D> T."
      moreover have inter_is_T: "\<Omega> \<inter> T = T"
        using calculation Dynkin_Pow by auto
      ultimately have "\<Omega> \<in> ?\<D> T"
        by auto  

      text "If S \<in> \<D> T, then (\<Omega> - S) \<inter> T = (\<Omega> \<inter> T) - (S \<inter> T)."
      moreover have "complement_stable \<Omega> (?\<D> T)"
        unfolding complement_stable_def 
      proof (rule ; rule) 
        show "?\<D> T = {} \<Longrightarrow> False"
          using calculation by auto
      next 
        fix S
        assume "S \<in> ?\<D> T"
        hence "T - (S \<inter> T) \<in> Dynkin \<Omega> M"
          using Dynkin_system.diff T_in_dynk Dynkin_dynk by auto 
        hence "(\<Omega> \<inter> T) - (S \<inter> T) \<in> Dynkin \<Omega> M"
          using inter_is_T by auto
        moreover have "(\<Omega> - S) \<inter> T = (\<Omega> \<inter> T) - (S \<inter> T)"
          by auto 
        ultimately show "\<Omega> - S \<in> ?\<D> T" 
          by auto 
      qed

      text "If {B n, n \<ge> 1} are disjoint sets in \<D> T, then (\<Inter>n. B n) \<inter> T = (\<Inter>n. B n \<inter> T)."
      moreover have "disj_countable_union_stable (?\<D> T)" 
        unfolding disj_countable_union_stable_def
      proof (rule ; rule) 
        show "(?\<D> T) = {} \<Longrightarrow> False"
          using calculation(1) by auto
      next 
        fix A :: "nat \<Rightarrow> 'a set"
        show "range A \<subseteq> ?\<D> T \<and> disjoint_family A \<longrightarrow> \<Union> (range A) \<in> ?\<D> T"
        proof (rule ; rule ; erule conjE)
          assume A_rng: "range A \<subseteq> ?\<D> T" and A_disj: "disjoint_family A"
          hence "\<Union> (range A) \<subseteq> \<Omega>" 
            by auto 
          moreover have "\<Union> (range A) \<inter> T \<in> Dynkin \<Omega> M"
          proof - 
            let ?B = "(\<lambda>n. A n \<inter> T)"
            have "range ?B \<subseteq> Dynkin \<Omega> M"
              using A_rng by blast 
            moreover have "disjoint_family ?B"
              using A_disj unfolding disjoint_family_on_def by auto 
            moreover have "disj_countable_union_stable (Dynkin \<Omega> M)"
              using Dynkin_dynk Dynkin_omega_c_disju_stable by auto
            ultimately have "\<Union> (range ?B) \<in> Dynkin \<Omega> M"
              unfolding disj_countable_union_stable_def by blast 
            moreover have "\<Union> (range A) \<inter> T = \<Union> (range ?B)" 
              by auto 
            ultimately show "\<Union> (range A) \<inter> T \<in> Dynkin \<Omega> M"
              by presburger 
          qed
          ultimately show "\<Union> (range A) \<subseteq> \<Omega> \<and> \<Union> (range A) \<inter> T \<in> Dynkin \<Omega> M"
            by auto
        qed
      qed

      ultimately show "Dynkin_system \<Omega> (?\<D> T)"
        using Dynkin_omega_c_disju_stable by blast 
    qed
    text "Since, by definition, M \<subseteq> \<D> S for every S \<in> M, it follows that Dynkin \<Omega> M \<subseteq> \<D> S \<forall>S\<in>M."
    (* Because D_S is a Dynkin system containing all of M and Dynkin \<Omega> M is the smallest such coll. *)
    moreover have M_in_\<D>: "\<forall>S\<in>M. M \<subseteq> ?\<D> S"
      using pi pi_system.axioms(1) subset_class.sets_into_space 
      using pi_system.fi_stable unfolding finite_inter_stable_def by fast 
    ultimately have "\<forall>S\<in>M. Dynkin \<Omega> M \<subseteq> ?\<D> S"
      by (simp add: Dynkin_Basic Dynkin_system.Dynkin_subset)

    text "For T\<in>\<D>(M), we now have T\<inter>S \<in> \<D>(M) \<forall>S\<in>M, which implies that M \<subseteq> \<D> T and, hence, that
          \<D>(M) \<subseteq> \<D>(T) \<forall>T\<in>\<D>(M)."
    hence "\<forall>T\<in>Dynkin \<Omega> M. \<forall>S\<in>M. T \<inter> S \<in> Dynkin \<Omega> M"
      by auto
    hence "\<forall>T\<in>Dynkin \<Omega> M. M \<subseteq> ?\<D> T"
      by (smt (verit, best) M_in_\<D> inf_commute mem_Collect_eq subset_iff)
    hence "\<forall>T\<in>Dynkin \<Omega> M. Dynkin \<Omega> M \<subseteq> ?\<D> T"
      by (simp add: Dynkin_system.Dynkin_subset \<D>_Dynkin)
    hence "\<forall>T\<in>Dynkin \<Omega> M. \<forall>T'\<in>Dynkin \<Omega> M. T \<inter> T' \<in> Dynkin \<Omega> M"
      by blast
    moreover have "Dynkin \<Omega> M \<noteq> {}"
      using M_in_\<D> finite_inter_stable_def pi pi_system.fi_stable by fastforce
    ultimately have "finite_inter_stable (Dynkin \<Omega> M)"
      unfolding finite_inter_stable_def by auto 
    thus "pi_system \<Omega> (Dynkin \<Omega> M)"
      by (simp add: pi_systemI Dynkin_Pow) 
  qed
  moreover have "Dynkin_system \<Omega> (Dynkin \<Omega> M)"
    by (meson Dynkin_system_Dynkin pi pi_system_def subset_class_def)
  ultimately have "sigma_algebra \<Omega> (Dynkin \<Omega> M)"
    by (simp add: Dynkin_is_sigma_iff_pi)
  moreover have "M \<subseteq> Dynkin \<Omega> M"
    by (simp add: Dynkin_Basic subsetI)
  ultimately show "sigma_sets \<Omega> M \<subseteq> Dynkin \<Omega> M"
    by (simp add: sigma_algebra.sigma_sets_subset) 
qed

corollary mono_dynk_sigma_of_sigma: 
  assumes "sigma_algebra \<Omega> M"
  shows "Mono \<Omega> M = M \<and> Dynkin \<Omega> M = M \<and> sigma_sets \<Omega> M = M"
proof - 
  have "Mono \<Omega> M = M"
    by (simp add: monotone_class_theorem assms sigma_algebra.sigma_sets_eq sigma_is_algebra) 
  moreover have "Dynkin \<Omega> M = M"
    by (simp add: Dynkin_system.Dynkin_idem assms sigma_algebra_imp_Dynkin_system) 
  moreover have "sigma_sets \<Omega> M = M"
    by (simp add: assms sigma_algebra.sigma_sets_eq)
  ultimately show ?thesis
    by simp 
qed

section "Two Metatheorems"

theorem check_alg_in_mono_for_sigma:
  assumes mono: "monotone_class \<Omega> M"
      and P_on_M: "\<forall>S\<in>M. P S"
      and alg: "algebra \<Omega> N"
      and subseq: "N \<subseteq> M"
    shows "\<forall>S\<in>sigma_sets \<Omega> N. P S"
proof - 
  have "sigma_sets \<Omega> N \<subseteq> M"
    using alg mono sigma_of_algebra_in_mono subseq by blast
  thus ?thesis
    using P_on_M by fast 
qed

theorem check_pi_in_dynk_for_sigma: 
  assumes dynk: "Dynkin_system \<Omega> M"
      and P_on_M: "\<forall>S\<in>M. P S"
      and pi: "pi_system \<Omega> N"
      and subseq: "N \<subseteq> M"
    shows "\<forall>S\<in>sigma_sets \<Omega> N. P S"
proof - 
  have "sigma_sets \<Omega> N = Dynkin \<Omega> N"
    using dynkin_pi_lambda pi by auto
  hence "sigma_sets \<Omega> N \<subseteq> M"
    by (simp add: Dynkin_system.Dynkin_subset dynk subseq)
  thus ?thesis 
    using P_on_M by fast 
qed 

chapter "The Probability Space"

locale probability_space = 
    fixes \<Omega> :: "'a set"
      and \<F> :: "'a set set"
      and P :: "'a set \<Rightarrow> real"
  assumes \<F>_Pow: "\<F> \<subseteq> Pow \<Omega>"
      and sigma: "sigma_algebra \<Omega> \<F>"
      and non_neg_prob: "\<forall>A\<in>\<F>. P A \<ge> 0"
      and sample_space_prob_1: "P \<Omega> = 1"
      and countable_additivity: "disjoint_family (A :: nat \<Rightarrow> 'a set) \<and> range A \<subseteq> \<F> \<longrightarrow> 
                                 P (\<Union>(range A)) = infsum (\<lambda>n. P (A n)) UNIV"
begin

section "Moving towards an intuitive notion of probability"

subsection "Measurable Sets"

definition measurable :: "'a set \<Rightarrow> bool"
  where "measurable S = (S \<in> \<F>)"

lemma measurable_c: 
  assumes meas: "measurable S"
  shows "measurable (\<Omega> - S)"
  using sigma meas measurable_def complement_stable_def sigma_algebra_omega_c_cu_stable by metis 

lemma measurable_empty: 
  shows "measurable {}"
  using empty_in_sigma measurable_def sigma by auto

lemma measurable_omega: 
  shows "measurable \<Omega>"
  using measurable_c measurable_empty by fastforce

lemma countable_additivity_meas:
  assumes disj: "disjoint_family (A :: nat \<Rightarrow> 'a set)"
      and meas: "\<forall>n. measurable (A n)"
    shows "P (\<Union>(range A)) = infsum (\<lambda>n. P (A n)) (UNIV :: nat set)"
  using assms countable_additivity measurable_def by fast

lemma measurable_fu: 
  assumes meas_A: "measurable A"
      and meas_B: "measurable B"
    shows "measurable (A \<union> B)"
  using sigma assms measurable_def 
        sigma_algebra_omega_c_cu_stable cu_imp_fu_stable finite_union_stable_def by metis 

lemma measurable_fu_ind: 
  assumes meas: "\<forall>S\<in>M. measurable S"
      and fin: "finite M"
    shows "measurable (\<Union>S\<in>M. S)"
  using sigma assms sigma_algebra_omega_c_cu_stable cu_imp_fu_stable fu_stable_finite Union_empty 
        empty_in_sigma image_ident measurable_def by metis 

lemma measurable_cu:
  assumes meas: "\<forall>n::nat. measurable (A n)"
  shows "measurable (\<Union>(range A))"
proof - 
  have "range A \<subseteq> \<F>"
    by (meson image_subset_iff measurable_def meas)  
  moreover have "countable_union_stable \<F>"
    using sigma sigma_algebra_omega_c_cu_stable by auto
  ultimately have "(\<Union>(range A)) \<in> \<F>"
    unfolding countable_union_stable_def by auto 
  thus ?thesis 
    by (simp add: measurable_def) 
qed

lemma measurable_union:
  fixes I :: "nat set"
  assumes meas: "\<forall>n\<in>I. measurable (A n)"
  shows "measurable (\<Union>n\<in>I. A n)"
proof - 
  let ?A' = "(\<lambda>n. if n\<notin>I then {} else A n)"
  let ?U' = "(\<Union>(range ?A'))"

  have "\<forall>n. measurable (?A' n)"
  proof 
    fix n 
    consider (I) "n\<in>I" | (no_I) "n\<notin>I"
      by auto
    thus "measurable (?A' n)"
    proof cases
      case I
      then show ?thesis
        by (simp add: meas) 
    next
      case no_I
      then show ?thesis
        by (simp add: measurable_empty) 
    qed 
  qed

  hence "measurable ?U'"
    using measurable_cu by presburger 

  moreover have "?U' = (\<Union>n\<in>I. A n)" 
    by simp 

  ultimately show ?thesis 
    by simp   
qed


lemma measurable_fi: 
  assumes meas_A: "measurable A"
      and meas_B: "measurable B"
    shows "measurable (A \<inter> B)"
  using sigma assms measurable_def 
        sigma_algebra_omega_c_ci_stable ci_imp_fi_stable finite_inter_stable_def by metis 

lemma measurable_fi_ind: 
  assumes meas: "\<forall>S\<in>M. measurable S"
      and fin: "finite M"
      and non_empty: "M \<noteq> {}"
    shows "measurable (\<Inter>S\<in>M. S)"
  using sigma assms sigma_algebra_omega_c_ci_stable ci_imp_fi_stable fi_stable_finite measurable_def
    by metis 

lemma measurable_ci:
  assumes meas: "\<forall>n::nat. measurable (A n)"
    shows "measurable (\<Inter>(range A))"
proof - 
  have "range A \<subseteq> \<F>"
    by (meson image_subset_iff measurable_def meas)  
  moreover have "countable_inter_stable \<F>"
    using sigma sigma_algebra_omega_c_ci_stable by auto
  ultimately have "(\<Inter>(range A)) \<in> \<F>"
    unfolding countable_inter_stable_def by auto 
  thus ?thesis 
    by (simp add: measurable_def) 
qed 

lemma measurable_inter:
  fixes I :: "nat set"
  assumes meas: "\<forall>n\<in>I. measurable (A n)"
      and non_empty: "I \<noteq> {}"
  shows "measurable (\<Inter>n\<in>I. A n)"
proof - 
  let ?A' = "(\<lambda>n. if n\<notin>I then \<Omega> else A n)"
  let ?I' = "(\<Inter>(range ?A'))"

  have "\<forall>n. measurable (?A' n)"
  proof 
    fix n 
    consider (I) "n\<in>I" | (no_I) "n\<notin>I"
      by auto
    thus "measurable (?A' n)"
    proof cases
      case I
      then show ?thesis
        by (simp add: meas) 
    next
      case no_I
      then show ?thesis
        by (simp add: measurable_omega) 
    qed 
  qed

  hence "measurable ?I'"
    using measurable_ci by presburger

  moreover have "?I' = (\<Inter>n\<in>I. A n)"
  proof (rule ; rule) 
    show "\<And>x. x \<in> (\<Inter>n. if n \<notin> I then \<Omega> else A n) \<Longrightarrow> x \<in> \<Inter> (A ` I)"
      by simp 
  next 
    fix x
    assume x_in_sub_I: "x \<in> (\<Inter>n\<in>I. A n)"
    have "\<forall>n. x \<in> ?A' n"
    proof 
      fix n 
      consider (I) "n\<in>I" | (no_I) "n\<notin>I"
        by auto
      thus "x \<in> ?A' n"
      proof cases
        case I
        then show ?thesis 
          using x_in_sub_I by auto 
      next
        case no_I
        moreover have "x \<in> \<Omega>" 
          using x_in_sub_I non_empty \<F>_Pow measurable_def meas by fastforce 
        ultimately show ?thesis 
          by auto 
      qed 
    qed
    thus "x \<in> ?I'"
      by fastforce 
  qed 

  ultimately show ?thesis 
    by simp   
qed

lemma measurable_sd: 
  assumes meas_S: "measurable S"
      and meas_T: "measurable T"
    shows "measurable (S - T)"
  unfolding measurable_def 
proof - 
  have "(S \<inter> T) \<in> \<F>"
    using meas_S meas_T measurable_fi measurable_def by auto 
  hence "S - (S \<inter> T) \<in> \<F>"
    using meas_S sigma sigma_sd_stable unfolding set_diff_stable_def measurable_def by blast 
  thus "S - T \<in> \<F>"
    by (metis Diff_Int_distrib Int_Diff Int_absorb) 
qed

subsection "Probabilities of sets and their combinations"

text "Departing from the axioms (only!) one can now derive various relations between probabilities
of unions, subsets, complements and so on. Following is a list of some of them."

lemma P_empty:
  shows "P {} = 0" 
proof - 
  let ?A = "(\<lambda>n::nat. if n = 0 then \<Omega> else {})"
  let ?P = "(\<lambda>n. P (?A n))"
  let ?S = "(UNIV - {0}) :: nat set"

  have "\<forall>n. (n \<in> (UNIV - {0})) \<longrightarrow> (?P n = 0)"
  proof (rule ; rule) 
    fix n

    have "disjoint_family ?A"
      unfolding disjoint_family_on_def by auto 
    moreover have "\<forall>n. measurable (?A n)"
      using measurable_c measurable_empty by fastforce
    ultimately have "P (\<Union>(range ?A)) = infsum ?P UNIV"
      using countable_additivity_meas by presburger 
    hence UNIV_sum_1: "infsum ?P UNIV = 1"
      using sample_space_prob_1 by auto 
    hence "infsum ?P (UNIV - {0}) + infsum ?P {0} = 1"
      using infsum_Diff infsum_not_exists subset_UNIV summable_on_subset_banach by smt 
    hence non_0_sum_0: "infsum ?P (UNIV - {0}) = 0"
      by (simp add: sample_space_prob_1) 

    moreover assume "n \<in> ?S"

    moreover have "?P summable_on UNIV"
      using infsum_not_exists UNIV_sum_1 by fastforce 
    hence "has_sum ?P ?S 0"
      using non_0_sum_0 Diff_subset has_sum_infsum summable_on_subset_banach by metis 
    moreover have "(\<And>x. x \<in> ?S \<Longrightarrow> 0 \<le> ?P x)"
      using empty_in_sigma non_neg_prob sigma by auto
    ultimately show "?P n = 0"
      using nonneg_has_sum_le_0D by smt 
  qed 
  
  thus ?thesis
    by auto
qed

lemma binary_additivity:
  assumes disj: "A \<inter> B = {}"
      and meas_A: "measurable A"
      and meas_B: "measurable B"
    shows "P (A \<union> B) = P A + P B"
proof - 
  let ?A = "(\<lambda>n::nat. if n = 0 then A else if n = 1 then B else {})"
  let ?P = "(\<lambda>n. P (?A n))"
  have "disjoint_family ?A"
    using disj unfolding disjoint_family_on_def by auto 
  moreover have "\<forall>n. measurable (?A n)"
    using disj meas_A meas_B measurable_fi by fastforce 
  ultimately have "P (\<Union>(range ?A)) = infsum ?P UNIV"
    using countable_additivity_meas by presburger 
  moreover have "\<Union>(range ?A) = A \<union> B" 
    by auto 
  ultimately have "P (A \<union> B) = infsum ?P UNIV"
    by auto  
  moreover have "\<forall>n\<in>(UNIV - {0, 1}). ?P n = 0" 
    using P_empty by simp
  hence "infsum ?P UNIV = infsum ?P {0, 1}"
    using Diff_UNIV empty_iff infsum_cong_neutral by (metis (no_types, lifting)) 
  ultimately show ?thesis 
    by auto 
qed

lemma finite_additivity:
  assumes disj: "disjoint_family_on A S"
      and meas_As: "\<forall>n\<in>S. measurable (A n)"
      and fin: "finite S"
    shows "P (\<Union>n\<in>S. A n) = sum P (A ` S)" 
  using fin meas_As disj 
proof (induction S rule: finite_induct)
  case empty
  hence "P (\<Union> (A ` {})) = sum P {}"
    by (simp add: P_empty)
  thus ?case
    by auto 
next
  case (insert x F) 
  have "P (\<Union> (A ` insert x F)) = P ((\<Union> (A ` F)) \<union> A x)"
    by (simp add: Un_commute)
  moreover have "finite {T. \<exists>n\<in>F. T = A n} \<and> (\<forall>n\<in>F. measurable (A n))"
    by (simp add: insert.hyps(1) insert.prems(1)) 
  hence "measurable (\<Union>S\<in>{T. \<exists>n\<in>F. T = A n}. S)"
    by (smt (verit, best) measurable_fu_ind mem_Collect_eq)
  hence "measurable (\<Union> (A ` F))"
    by (smt (verit) Collect_cong UNION_eq mem_Collect_eq) 
  moreover have "measurable (A x)"
    by (simp add: insert.prems(1)) 
  moreover have "(\<Union> (A ` F)) \<inter> (A x) = {}" 
    using insert.prems(2) insert.hyps(2) unfolding disjoint_family_on_def by fastforce 
  ultimately have "P (\<Union> (A ` insert x F)) = P (\<Union> (A ` F)) + P (A x)"
    using binary_additivity by fastforce
  moreover have meas_F: "\<forall>n\<in>F. measurable (A n)"
    by (simp add: insert.prems(1))  
  moreover have disj_F: "disjoint_family_on A F"
    by (metis disjoint_family_on_insert insert.hyps(2) insert.prems(2))  
  ultimately have "P (\<Union> (A ` insert x F)) = sum P (A ` F) + P (A x)"
    using insert.IH by auto 
  thus ?case
    by (smt meas_F disj_F finite_imageI image_insert insert.IH insert.hyps(1) insert_absorb 
                    sum.insert)  
qed

lemma finite_additivity':
  assumes disj: "disjoint_family_on A S"
      and meas_As: "\<forall>n\<in>S. measurable (A n)"
      and fin: "finite S"
    shows "P (\<Union>n\<in>S. A n) = sum (\<lambda>n. P (A n)) S" 
proof - 
  have "P (\<Union>n\<in>S. A n) = sum P (A ` S)"
    by (simp add: disj fin finite_additivity meas_As)
  moreover have "sum (P \<circ> A) S = sum P (A ` S)" 
    using disj unfolding disjoint_family_on_def
    by (metis P_empty fin inf.idem sum.reindex_nontrivial) 
  ultimately show ?thesis 
    by simp 
qed

lemma P_set_diff: 
  assumes meas_S: "measurable S"
      and meas_T: "measurable T"
    shows "P (S - T) = P S - P (S \<inter> T)"
proof - 
  have "measurable (S \<inter> T)"
    by (simp add: meas_S meas_T measurable_fi)
  moreover have "measurable (S - T)"
    by (simp add: meas_S meas_T measurable_sd)
  ultimately have "P (S - T) + P (S \<inter> T) = P S"
    by (metis Int_Diff_disjoint Int_Diff_Un add.commute binary_additivity)
  thus ?thesis
    by simp 
qed

lemma P_subset_diff: 
  assumes meas_S: "measurable S"
      and meas_T: "measurable T"
      and subseq: "T \<subseteq> S"
    shows "P (S - T) = P S - P T"
  by (metis inf.absorb_iff2 meas_S meas_T P_set_diff subseq)

lemma P_complement: 
  assumes meas: "measurable S"
  shows "P (\<Omega> - S) = 1 - P S"
proof - 
  have "measurable \<Omega>"
    by (simp add: measurable_omega)
  moreover have "S \<subseteq> \<Omega>"
    using \<F>_Pow measurable_def meas by auto
  ultimately show ?thesis
    by (simp add: meas P_subset_diff sample_space_prob_1)
qed

lemma binary_incl_excl: 
  assumes meas_A: "measurable A"
      and meas_B: "measurable B"
    shows "P (A \<union> B) = P A + P B - P (A \<inter> B)"
proof - 
  have "measurable (B - A)"
    by (simp add: meas_A meas_B measurable_sd) 
  hence "P (A \<union> B) = P A + P (B - A)"
    using assms binary_additivity Diff_disjoint Un_Diff_cancel by metis 
  moreover have "P (B - A) = P B - P (A \<inter> B)"
    by (simp add: Int_commute meas_A meas_B P_set_diff)
  ultimately show ?thesis 
    by simp 
qed

lemma binary_subadditivty:
  assumes meas_A: "measurable A"
      and meas_B: "measurable B"
  shows "P (A \<union> B) \<le> P A + P B"
  using binary_incl_excl measurable_def meas_A meas_B measurable_fi non_neg_prob by auto  

(* TODO: Finite, countable subadditivity*)

lemma P_subseq: 
  assumes meas_S: "measurable S"
      and meas_T: "measurable T"
      and subseq: "S \<subseteq> T"
    shows "P S \<le> P T"
proof - 
  have meas_sd: "measurable (T - S)"
    by (simp add: meas_S meas_T measurable_sd)
  hence "P S + P (T - S) = P T"
    by (simp add: assms P_subset_diff)
  thus ?thesis 
    using meas_sd measurable_def non_neg_prob by auto 
qed 

lemma P_cu_cci_1: 
  assumes meas_As: "\<forall>n::nat. measurable (A n)"
  shows "P (\<Union>n. A n) + P (\<Inter>n. \<Omega> - A n) = 1"
proof - 
  have "measurable (\<Union>n. A n)"
    by (simp add: meas_As measurable_cu)
  moreover have "\<forall>n. measurable (\<Omega> - A n)"
    by (simp add: meas_As measurable_c)
  hence "measurable (\<Inter>n. \<Omega> - A n)"
    by (meson measurable_ci)
  moreover have "(\<Inter>n. \<Omega> - A n) = \<Omega> - (\<Union>n. A n)"
    by auto
  ultimately show ?thesis
    by (simp add: P_complement)
qed

section "Limits and Completeness"

lemma partial_sum_LIM_infsum: 
  fixes Q :: "nat \<Rightarrow> real"
  assumes smmble: "Q summable_on UNIV"
  shows "(\<lambda>N. sum Q {..N}) \<longlonglongrightarrow> infsum Q UNIV"
proof - 
  have "(sum Q \<longlongrightarrow> infsum Q UNIV) (finite_subsets_at_top UNIV)"
    using infsum_tendsto smmble by blast
  hence  "((\<lambda>N. sum Q {..N}) \<longlongrightarrow> infsum Q UNIV) at_top"
    using filterlim_atMost_at_top filterlim_compose by blast
  thus ?thesis
    by simp
qed

theorem non_dec_prob_limit: 
  fixes A :: "nat \<Rightarrow> 'a set"
  assumes meas_As: "\<forall>n. measurable (A n)"
      and non_dec: "non_decreasing A"
    shows "(\<lambda>n. P (A n)) \<longlonglongrightarrow> P (set_limit A)"
proof -
  let ?B = "(\<lambda>n. if n = 0 then A 0 else A n - A (n - 1))"

  have meas_B: "\<forall>n. measurable (?B n)"
      by (simp add: meas_As measurable_sd) 
  have disj_B: "disjoint_family ?B"
    by (simp add: non_dec non_dec_to_disj)

  have "\<forall>N. A N = \<Union> (?B ` {..N})"
    using non_dec non_dec_is_disj_fu by auto 
  hence "\<forall>N. P (A N) = P (\<Union> (?B ` {..N}))"
    by metis
  moreover have "\<forall>N. P (\<Union> (?B ` {..N})) = sum (\<lambda>n. P (?B n)) {..N}"
  proof 
    fix N
    have "disjoint_family_on ?B {..N}"  
      using disj_B unfolding disjoint_family_on_def by blast 
    thus "P (\<Union> (?B ` {..N})) = sum (\<lambda>n. P (?B n)) {..N}" 
      using finite_additivity' meas_B by blast  
  qed 
  ultimately have "\<forall>N. P (A N) = sum (\<lambda>n. P (?B n)) {..N}"  
    by auto 

  moreover consider (null) "\<forall>n. P (?B n) = 0" | (non_null) "\<exists>n. P (?B n) \<noteq> 0"
    by auto 
  hence "(\<lambda>n. P (?B n)) summable_on UNIV" 
  proof cases
    case null
    then show ?thesis by simp 
  next
    case non_null
    then obtain N where "P (?B N) \<noteq> 0"
      by auto 
    moreover have "measurable (?B N)"
      using meas_B by auto 
    ultimately have "P (?B N) > 0"
      using measurable_def non_neg_prob by auto 
    moreover have "measurable (\<Union> (range ?B))"
      using meas_B measurable_cu by presburger
    moreover have "?B N \<subseteq> (\<Union> (range ?B))"
      by blast 
    ultimately have "P (\<Union> (range ?B)) > 0"
      using P_subseq meas_B by (smt (verit)) 
    hence "infsum (\<lambda>n. P (?B n)) UNIV > 0"
      using countable_additivity_meas meas_B disj_B by fastforce 
    then show ?thesis
      using infsum_not_exists by fastforce 
  qed 
  hence "((\<lambda>N. sum (\<lambda>n. P (?B n)) {..N}) \<longlongrightarrow> infsum (\<lambda>n. P (?B n)) UNIV) at_top"
    using partial_sum_LIM_infsum by auto

  ultimately have "(\<lambda>N. P (A N)) \<longlonglongrightarrow> (\<Sum>\<^sub>\<infinity>n. P (?B n))" 
    by simp 
  moreover have "P (\<Union> (range ?B)) = (\<Sum>\<^sub>\<infinity>n. P (?B n))"
    using countable_additivity_meas meas_B disj_B by blast 
  moreover have "(\<Union> (range ?B)) = (\<Union> (range A))"
    by (simp add: non_dec non_dec_to_disj_same_cu)
  ultimately have "(\<lambda>N. P (A N)) \<longlonglongrightarrow> P (\<Union> (range A))"
    by simp  

  thus ?thesis 
    using non_dec non_decreasing_set_limit by fastforce 
qed


theorem non_inc_prob_limit: 
  fixes A :: "nat \<Rightarrow> 'a set"
  assumes meas_As: "\<forall>n. measurable (A n)"
      and non_inc: "non_increasing A"
    shows "(\<lambda>n. P (A n)) \<longlonglongrightarrow> P (set_limit A)"
proof -
  let ?B = "(\<lambda>n. \<Omega> - A n)"

  have non_dec: "non_decreasing ?B"
    by (simp add: ni_complement_nd non_inc)
  hence "(\<lambda>n. P (?B n)) \<longlonglongrightarrow> P (set_limit ?B)"
    using meas_As measurable_c non_dec_prob_limit by auto

  moreover have "\<forall>n. P (?B n) = 1 - P (A n)"
    by (simp add: P_complement meas_As)

  moreover have "P (set_limit ?B) = P (\<Omega> - set_limit A)"
    by (simp add: ni_c_nd_set_limit non_inc)
  hence "P (set_limit ?B) = 1 - P (set_limit A)"
    by (simp add: meas_As measurable_ci non_inc non_increasing_set_limit P_complement)

  ultimately have "(\<lambda>n. 1 - P (A n)) \<longlonglongrightarrow> 1 - P (set_limit A)"
    by simp   
  moreover have "\<forall>x y :: real. dist (1 - x) (1 - y) = dist x y"
    using dist_real_def by auto
  ultimately show ?thesis 
    by (simp add: tendsto_iff dist_real_def) 
qed

theorem P_liminf_le: 
  fixes A :: "nat \<Rightarrow> 'a set"
  assumes meas_As: "\<forall>n. measurable (A n)"
  shows "P (liminf A) \<le> liminf (\<lambda>n. P (A n))"
proof - 
  let ?I = "(\<lambda>n. \<Inter>m\<in>{n..}. A m)"

  have nd_I: "non_decreasing ?I"
    unfolding non_decreasing_def by (simp add: Inter_anti_mono image_mono)
  moreover have meas_Is: "\<forall>n. measurable (?I n)"
    by (simp add: meas_As measurable_inter) 
  ultimately have "(\<lambda>n. P (?I n)) \<longlonglongrightarrow> P (set_limit ?I)"
    by (simp add: non_dec_prob_limit) 
  hence "P (set_limit ?I) \<le> liminf (\<lambda>n. P (?I n))" sorry   

  moreover have "\<forall>n. ?I n \<subseteq> A n"
    by (simp add: INT_lower)
  hence "\<forall>n. P (?I n) \<le> P (A n)"
    using P_subseq meas_As meas_Is by auto
  hence "liminf (\<lambda>n. P (?I n)) \<le> liminf (\<lambda>n. P (A n))" sorry 

  ultimately have "P (set_limit ?I) \<le> liminf (\<lambda>n. P (A n))" 
    by simp 

  moreover have "liminf ?I = liminf A" 
    unfolding liminf_set by auto 

  moreover have "set_limit ?I = \<Union>(range ?I)" 
    using nd_I non_decreasing_set_limit by auto 
  
  ultimately show ?thesis
    by (simp add: liminf_set) 
qed

end

end