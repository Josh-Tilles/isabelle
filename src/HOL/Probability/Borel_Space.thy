(*  Title:      HOL/Probability/Borel_Space.thy
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

header {*Borel spaces*}

theory Borel_Space
  imports Sigma_Algebra "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
begin

section "Generic Borel spaces"

definition borel :: "'a::topological_space measure" where
  "borel = sigma UNIV {S. open S}"

abbreviation "borel_measurable M \<equiv> measurable M borel"

lemma in_borel_measurable:
   "f \<in> borel_measurable M \<longleftrightarrow>
    (\<forall>S \<in> sigma_sets UNIV {S. open S}. f -` S \<inter> space M \<in> sets M)"
  by (auto simp add: measurable_def borel_def)

lemma in_borel_measurable_borel:
   "f \<in> borel_measurable M \<longleftrightarrow>
    (\<forall>S \<in> sets borel.
      f -` S \<inter> space M \<in> sets M)"
  by (auto simp add: measurable_def borel_def)

lemma space_borel[simp]: "space borel = UNIV"
  unfolding borel_def by auto

lemma space_in_borel[measurable]: "UNIV \<in> sets borel"
  unfolding borel_def by auto

lemma pred_Collect_borel[measurable (raw)]: "Sigma_Algebra.pred borel P \<Longrightarrow> {x. P x} \<in> sets borel"
  unfolding borel_def pred_def by auto

lemma borel_open[measurable (raw generic)]:
  assumes "open A" shows "A \<in> sets borel"
proof -
  have "A \<in> {S. open S}" unfolding mem_Collect_eq using assms .
  thus ?thesis unfolding borel_def by auto
qed

lemma borel_closed[measurable (raw generic)]:
  assumes "closed A" shows "A \<in> sets borel"
proof -
  have "space borel - (- A) \<in> sets borel"
    using assms unfolding closed_def by (blast intro: borel_open)
  thus ?thesis by simp
qed

lemma borel_singleton[measurable]:
  "A \<in> sets borel \<Longrightarrow> insert x A \<in> sets (borel :: 'a::t1_space measure)"
  unfolding insert_def by (rule Un) auto

lemma borel_comp[measurable]: "A \<in> sets borel \<Longrightarrow> - A \<in> sets borel"
  unfolding Compl_eq_Diff_UNIV by simp

lemma borel_measurable_vimage:
  fixes f :: "'a \<Rightarrow> 'x::t2_space"
  assumes borel[measurable]: "f \<in> borel_measurable M"
  shows "f -` {x} \<inter> space M \<in> sets M"
  by simp

lemma borel_measurableI:
  fixes f :: "'a \<Rightarrow> 'x\<Colon>topological_space"
  assumes "\<And>S. open S \<Longrightarrow> f -` S \<inter> space M \<in> sets M"
  shows "f \<in> borel_measurable M"
  unfolding borel_def
proof (rule measurable_measure_of, simp_all)
  fix S :: "'x set" assume "open S" thus "f -` S \<inter> space M \<in> sets M"
    using assms[of S] by simp
qed

lemma borel_measurable_const:
  "(\<lambda>x. c) \<in> borel_measurable M"
  by auto

lemma borel_measurable_indicator:
  assumes A: "A \<in> sets M"
  shows "indicator A \<in> borel_measurable M"
  unfolding indicator_def [abs_def] using A
  by (auto intro!: measurable_If_set)

lemma borel_measurable_count_space[measurable (raw)]:
  "f \<in> borel_measurable (count_space S)"
  unfolding measurable_def by auto

lemma borel_measurable_indicator'[measurable (raw)]:
  assumes [measurable]: "{x\<in>space M. f x \<in> A x} \<in> sets M"
  shows "(\<lambda>x. indicator (A x) (f x)) \<in> borel_measurable M"
  unfolding indicator_def[abs_def]
  by (auto intro!: measurable_If)

lemma borel_measurable_indicator_iff:
  "(indicator A :: 'a \<Rightarrow> 'x::{t1_space, zero_neq_one}) \<in> borel_measurable M \<longleftrightarrow> A \<inter> space M \<in> sets M"
    (is "?I \<in> borel_measurable M \<longleftrightarrow> _")
proof
  assume "?I \<in> borel_measurable M"
  then have "?I -` {1} \<inter> space M \<in> sets M"
    unfolding measurable_def by auto
  also have "?I -` {1} \<inter> space M = A \<inter> space M"
    unfolding indicator_def [abs_def] by auto
  finally show "A \<inter> space M \<in> sets M" .
next
  assume "A \<inter> space M \<in> sets M"
  moreover have "?I \<in> borel_measurable M \<longleftrightarrow>
    (indicator (A \<inter> space M) :: 'a \<Rightarrow> 'x) \<in> borel_measurable M"
    by (intro measurable_cong) (auto simp: indicator_def)
  ultimately show "?I \<in> borel_measurable M" by auto
qed

lemma borel_measurable_subalgebra:
  assumes "sets N \<subseteq> sets M" "space N = space M" "f \<in> borel_measurable N"
  shows "f \<in> borel_measurable M"
  using assms unfolding measurable_def by auto

lemma borel_measurable_continuous_on1:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes "continuous_on UNIV f"
  shows "f \<in> borel_measurable borel"
  apply(rule borel_measurableI)
  using continuous_open_preimage[OF assms] unfolding vimage_def by auto

section "Borel spaces on euclidean spaces"

lemma borel_measurable_euclidean_component'[measurable]:
  "(\<lambda>x::'a::euclidean_space. x $$ i) \<in> borel_measurable borel"
  by (intro continuous_on_euclidean_component continuous_on_id borel_measurable_continuous_on1)

lemma borel_measurable_euclidean_component:
  "(f :: 'a \<Rightarrow> 'b::euclidean_space) \<in> borel_measurable M \<Longrightarrow>(\<lambda>x. f x $$ i) \<in> borel_measurable M"
  by simp

lemma [measurable]:
  fixes a b :: "'a\<Colon>ordered_euclidean_space"
  shows lessThan_borel: "{..< a} \<in> sets borel"
    and greaterThan_borel: "{a <..} \<in> sets borel"
    and greaterThanLessThan_borel: "{a<..<b} \<in> sets borel"
    and atMost_borel: "{..a} \<in> sets borel"
    and atLeast_borel: "{a..} \<in> sets borel"
    and atLeastAtMost_borel: "{a..b} \<in> sets borel"
    and greaterThanAtMost_borel: "{a<..b} \<in> sets borel"
    and atLeastLessThan_borel: "{a..<b} \<in> sets borel"
  unfolding greaterThanAtMost_def atLeastLessThan_def
  by (blast intro: borel_open borel_closed)+

lemma 
  shows hafspace_less_borel: "{x::'a::euclidean_space. a < x $$ i} \<in> sets borel"
    and hafspace_greater_borel: "{x::'a::euclidean_space. x $$ i < a} \<in> sets borel"
    and hafspace_less_eq_borel: "{x::'a::euclidean_space. a \<le> x $$ i} \<in> sets borel"
    and hafspace_greater_eq_borel: "{x::'a::euclidean_space. x $$ i \<le> a} \<in> sets borel"
  by simp_all

lemma borel_measurable_less[measurable]:
  fixes f :: "'a \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "{w \<in> space M. f w < g w} \<in> sets M"
proof -
  have "{w \<in> space M. f w < g w} = {x \<in> space M. \<exists>r. f x < of_rat r \<and> of_rat r < g x}"
    using Rats_dense_in_real by (auto simp add: Rats_def)
  with f g show ?thesis
    by simp
qed

lemma
  fixes f :: "'a \<Rightarrow> real"
  assumes f[measurable]: "f \<in> borel_measurable M"
  assumes g[measurable]: "g \<in> borel_measurable M"
  shows borel_measurable_le[measurable]: "{w \<in> space M. f w \<le> g w} \<in> sets M"
    and borel_measurable_eq[measurable]: "{w \<in> space M. f w = g w} \<in> sets M"
    and borel_measurable_neq: "{w \<in> space M. f w \<noteq> g w} \<in> sets M"
  unfolding eq_iff not_less[symmetric]
  by measurable

subsection "Borel space equals sigma algebras over intervals"

lemma borel_sigma_sets_subset:
  "A \<subseteq> sets borel \<Longrightarrow> sigma_sets UNIV A \<subseteq> sets borel"
  using sigma_sets_subset[of A borel] by simp

lemma borel_eq_sigmaI1:
  fixes F :: "'i \<Rightarrow> 'a::topological_space set" and X :: "'a::topological_space set set"
  assumes borel_eq: "borel = sigma UNIV X"
  assumes X: "\<And>x. x \<in> X \<Longrightarrow> x \<in> sets (sigma UNIV (range F))"
  assumes F: "\<And>i. F i \<in> sets borel"
  shows "borel = sigma UNIV (range F)"
  unfolding borel_def
proof (intro sigma_eqI antisym)
  have borel_rev_eq: "sigma_sets UNIV {S::'a set. open S} = sets borel"
    unfolding borel_def by simp
  also have "\<dots> = sigma_sets UNIV X"
    unfolding borel_eq by simp
  also have "\<dots> \<subseteq> sigma_sets UNIV (range F)"
    using X by (intro sigma_algebra.sigma_sets_subset[OF sigma_algebra_sigma_sets]) auto
  finally show "sigma_sets UNIV {S. open S} \<subseteq> sigma_sets UNIV (range F)" .
  show "sigma_sets UNIV (range F) \<subseteq> sigma_sets UNIV {S. open S}"
    unfolding borel_rev_eq using F by (intro borel_sigma_sets_subset) auto
qed auto

lemma borel_eq_sigmaI2:
  fixes F :: "'i \<Rightarrow> 'j \<Rightarrow> 'a::topological_space set"
    and G :: "'l \<Rightarrow> 'k \<Rightarrow> 'a::topological_space set"
  assumes borel_eq: "borel = sigma UNIV (range (\<lambda>(i, j). G i j))"
  assumes X: "\<And>i j. G i j \<in> sets (sigma UNIV (range (\<lambda>(i, j). F i j)))"
  assumes F: "\<And>i j. F i j \<in> sets borel"
  shows "borel = sigma UNIV (range (\<lambda>(i, j). F i j))"
  using assms by (intro borel_eq_sigmaI1[where X="range (\<lambda>(i, j). G i j)" and F="(\<lambda>(i, j). F i j)"]) auto

lemma borel_eq_sigmaI3:
  fixes F :: "'i \<Rightarrow> 'j \<Rightarrow> 'a::topological_space set" and X :: "'a::topological_space set set"
  assumes borel_eq: "borel = sigma UNIV X"
  assumes X: "\<And>x. x \<in> X \<Longrightarrow> x \<in> sets (sigma UNIV (range (\<lambda>(i, j). F i j)))"
  assumes F: "\<And>i j. F i j \<in> sets borel"
  shows "borel = sigma UNIV (range (\<lambda>(i, j). F i j))"
  using assms by (intro borel_eq_sigmaI1[where X=X and F="(\<lambda>(i, j). F i j)"]) auto

lemma borel_eq_sigmaI4:
  fixes F :: "'i \<Rightarrow> 'a::topological_space set"
    and G :: "'l \<Rightarrow> 'k \<Rightarrow> 'a::topological_space set"
  assumes borel_eq: "borel = sigma UNIV (range (\<lambda>(i, j). G i j))"
  assumes X: "\<And>i j. G i j \<in> sets (sigma UNIV (range F))"
  assumes F: "\<And>i. F i \<in> sets borel"
  shows "borel = sigma UNIV (range F)"
  using assms by (intro borel_eq_sigmaI1[where X="range (\<lambda>(i, j). G i j)" and F=F]) auto

lemma borel_eq_sigmaI5:
  fixes F :: "'i \<Rightarrow> 'j \<Rightarrow> 'a::topological_space set" and G :: "'l \<Rightarrow> 'a::topological_space set"
  assumes borel_eq: "borel = sigma UNIV (range G)"
  assumes X: "\<And>i. G i \<in> sets (sigma UNIV (range (\<lambda>(i, j). F i j)))"
  assumes F: "\<And>i j. F i j \<in> sets borel"
  shows "borel = sigma UNIV (range (\<lambda>(i, j). F i j))"
  using assms by (intro borel_eq_sigmaI1[where X="range G" and F="(\<lambda>(i, j). F i j)"]) auto

lemma halfspace_gt_in_halfspace:
  "{x\<Colon>'a. a < x $$ i} \<in> sigma_sets UNIV (range (\<lambda> (a, i). {x\<Colon>'a\<Colon>ordered_euclidean_space. x $$ i < a}))"
  (is "?set \<in> ?SIGMA")
proof -
  interpret sigma_algebra UNIV ?SIGMA
    by (intro sigma_algebra_sigma_sets) simp_all
  have *: "?set = (\<Union>n. UNIV - {x\<Colon>'a. x $$ i < a + 1 / real (Suc n)})"
  proof (safe, simp_all add: not_less)
    fix x :: 'a assume "a < x $$ i"
    with reals_Archimedean[of "x $$ i - a"]
    obtain n where "a + 1 / real (Suc n) < x $$ i"
      by (auto simp: inverse_eq_divide field_simps)
    then show "\<exists>n. a + 1 / real (Suc n) \<le> x $$ i"
      by (blast intro: less_imp_le)
  next
    fix x n
    have "a < a + 1 / real (Suc n)" by auto
    also assume "\<dots> \<le> x"
    finally show "a < x" .
  qed
  show "?set \<in> ?SIGMA" unfolding *
    by (auto del: Diff intro!: Diff)
qed

lemma borel_eq_halfspace_less:
  "borel = sigma UNIV (range (\<lambda>(a, i). {x::'a::ordered_euclidean_space. x $$ i < a}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI3[OF borel_def])
  fix S :: "'a set" assume "S \<in> {S. open S}"
  then have "open S" by simp
  from open_UNION[OF this]
  obtain I where *: "S =
    (\<Union>(a, b)\<in>I.
        (\<Inter> i<DIM('a). {x. (Chi (real_of_rat \<circ> op ! a)::'a) $$ i < x $$ i}) \<inter>
        (\<Inter> i<DIM('a). {x. x $$ i < (Chi (real_of_rat \<circ> op ! b)::'a) $$ i}))"
    unfolding greaterThanLessThan_def
    unfolding eucl_greaterThan_eq_halfspaces[where 'a='a]
    unfolding eucl_lessThan_eq_halfspaces[where 'a='a]
    by blast
  show "S \<in> ?SIGMA"
    unfolding *
    by (safe intro!: countable_UN Int countable_INT) (auto intro!: halfspace_gt_in_halfspace)
qed auto

lemma borel_eq_halfspace_le:
  "borel = sigma UNIV (range (\<lambda> (a, i). {x::'a::ordered_euclidean_space. x $$ i \<le> a}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI2[OF borel_eq_halfspace_less])
  fix a i
  have *: "{x::'a. x$$i < a} = (\<Union>n. {x. x$$i \<le> a - 1/real (Suc n)})"
  proof (safe, simp_all)
    fix x::'a assume *: "x$$i < a"
    with reals_Archimedean[of "a - x$$i"]
    obtain n where "x $$ i < a - 1 / (real (Suc n))"
      by (auto simp: field_simps inverse_eq_divide)
    then show "\<exists>n. x $$ i \<le> a - 1 / (real (Suc n))"
      by (blast intro: less_imp_le)
  next
    fix x::'a and n
    assume "x$$i \<le> a - 1 / real (Suc n)"
    also have "\<dots> < a" by auto
    finally show "x$$i < a" .
  qed
  show "{x. x$$i < a} \<in> ?SIGMA" unfolding *
    by (safe intro!: countable_UN) auto
qed auto

lemma borel_eq_halfspace_ge:
  "borel = sigma UNIV (range (\<lambda> (a, i). {x\<Colon>'a\<Colon>ordered_euclidean_space. a \<le> x $$ i}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI2[OF borel_eq_halfspace_less])
  fix a i have *: "{x::'a. x$$i < a} = space ?SIGMA - {x::'a. a \<le> x$$i}" by auto
  show "{x. x$$i < a} \<in> ?SIGMA" unfolding *
      by (safe intro!: compl_sets) auto
qed auto

lemma borel_eq_halfspace_greater:
  "borel = sigma UNIV (range (\<lambda> (a, i). {x\<Colon>'a\<Colon>ordered_euclidean_space. a < x $$ i}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI2[OF borel_eq_halfspace_le])
  fix a i have *: "{x::'a. x$$i \<le> a} = space ?SIGMA - {x::'a. a < x$$i}" by auto
  show "{x. x$$i \<le> a} \<in> ?SIGMA" unfolding *
    by (safe intro!: compl_sets) auto
qed auto

lemma borel_eq_atMost:
  "borel = sigma UNIV (range (\<lambda>a. {..a\<Colon>'a\<Colon>ordered_euclidean_space}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI4[OF borel_eq_halfspace_le])
  fix a i show "{x. x$$i \<le> a} \<in> ?SIGMA"
  proof cases
    assume "i < DIM('a)"
    then have *: "{x::'a. x$$i \<le> a} = (\<Union>k::nat. {.. (\<chi>\<chi> n. if n = i then a else real k)})"
    proof (safe, simp_all add: eucl_le[where 'a='a] split: split_if_asm)
      fix x
      from real_arch_simple[of "Max ((\<lambda>i. x$$i)`{..<DIM('a)})"] guess k::nat ..
      then have "\<And>i. i < DIM('a) \<Longrightarrow> x$$i \<le> real k"
        by (subst (asm) Max_le_iff) auto
      then show "\<exists>k::nat. \<forall>ia. ia \<noteq> i \<longrightarrow> ia < DIM('a) \<longrightarrow> x $$ ia \<le> real k"
        by (auto intro!: exI[of _ k])
    qed
    show "{x. x$$i \<le> a} \<in> ?SIGMA" unfolding *
      by (safe intro!: countable_UN) auto
  qed (auto intro: sigma_sets_top sigma_sets.Empty)
qed auto

lemma borel_eq_greaterThan:
  "borel = sigma UNIV (range (\<lambda>a\<Colon>'a\<Colon>ordered_euclidean_space. {a<..}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI4[OF borel_eq_halfspace_le])
  fix a i show "{x. x$$i \<le> a} \<in> ?SIGMA"
  proof cases
    assume "i < DIM('a)"
    have "{x::'a. x$$i \<le> a} = UNIV - {x::'a. a < x$$i}" by auto
    also have *: "{x::'a. a < x$$i} = (\<Union>k::nat. {(\<chi>\<chi> n. if n = i then a else -real k) <..})" using `i <DIM('a)`
    proof (safe, simp_all add: eucl_less[where 'a='a] split: split_if_asm)
      fix x
      from reals_Archimedean2[of "Max ((\<lambda>i. -x$$i)`{..<DIM('a)})"]
      guess k::nat .. note k = this
      { fix i assume "i < DIM('a)"
        then have "-x$$i < real k"
          using k by (subst (asm) Max_less_iff) auto
        then have "- real k < x$$i" by simp }
      then show "\<exists>k::nat. \<forall>ia. ia \<noteq> i \<longrightarrow> ia < DIM('a) \<longrightarrow> -real k < x $$ ia"
        by (auto intro!: exI[of _ k])
    qed
    finally show "{x. x$$i \<le> a} \<in> ?SIGMA"
      apply (simp only:)
      apply (safe intro!: countable_UN Diff)
      apply (auto intro: sigma_sets_top)
      done
  qed (auto intro: sigma_sets_top sigma_sets.Empty)
qed auto

lemma borel_eq_lessThan:
  "borel = sigma UNIV (range (\<lambda>a\<Colon>'a\<Colon>ordered_euclidean_space. {..<a}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI4[OF borel_eq_halfspace_ge])
  fix a i show "{x. a \<le> x$$i} \<in> ?SIGMA"
  proof cases
    fix a i assume "i < DIM('a)"
    have "{x::'a. a \<le> x$$i} = UNIV - {x::'a. x$$i < a}" by auto
    also have *: "{x::'a. x$$i < a} = (\<Union>k::nat. {..< (\<chi>\<chi> n. if n = i then a else real k)})" using `i <DIM('a)`
    proof (safe, simp_all add: eucl_less[where 'a='a] split: split_if_asm)
      fix x
      from reals_Archimedean2[of "Max ((\<lambda>i. x$$i)`{..<DIM('a)})"]
      guess k::nat .. note k = this
      { fix i assume "i < DIM('a)"
        then have "x$$i < real k"
          using k by (subst (asm) Max_less_iff) auto
        then have "x$$i < real k" by simp }
      then show "\<exists>k::nat. \<forall>ia. ia \<noteq> i \<longrightarrow> ia < DIM('a) \<longrightarrow> x $$ ia < real k"
        by (auto intro!: exI[of _ k])
    qed
    finally show "{x. a \<le> x$$i} \<in> ?SIGMA"
      apply (simp only:)
      apply (safe intro!: countable_UN Diff)
      apply (auto intro: sigma_sets_top)
      done
  qed (auto intro: sigma_sets_top sigma_sets.Empty)
qed auto

lemma borel_eq_atLeastAtMost:
  "borel = sigma UNIV (range (\<lambda>(a,b). {a..b} \<Colon>'a\<Colon>ordered_euclidean_space set))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI5[OF borel_eq_atMost])
  fix a::'a
  have *: "{..a} = (\<Union>n::nat. {- real n *\<^sub>R One .. a})"
  proof (safe, simp_all add: eucl_le[where 'a='a])
    fix x
    from real_arch_simple[of "Max ((\<lambda>i. - x$$i)`{..<DIM('a)})"]
    guess k::nat .. note k = this
    { fix i assume "i < DIM('a)"
      with k have "- x$$i \<le> real k"
        by (subst (asm) Max_le_iff) (auto simp: field_simps)
      then have "- real k \<le> x$$i" by simp }
    then show "\<exists>n::nat. \<forall>i<DIM('a). - real n \<le> x $$ i"
      by (auto intro!: exI[of _ k])
  qed
  show "{..a} \<in> ?SIGMA" unfolding *
    by (safe intro!: countable_UN)
       (auto intro!: sigma_sets_top)
qed auto

lemma borel_eq_greaterThanLessThan:
  "borel = sigma UNIV (range (\<lambda> (a, b). {a <..< b} :: 'a \<Colon> ordered_euclidean_space set))"
    (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI1[OF borel_def])
  fix M :: "'a set" assume "M \<in> {S. open S}"
  then have "open M" by simp
  show "M \<in> ?SIGMA"
    apply (subst open_UNION[OF `open M`])
    apply (safe intro!: countable_UN)
    apply auto
    done
qed auto

lemma borel_eq_atLeastLessThan:
  "borel = sigma UNIV (range (\<lambda>(a, b). {a ..< b :: real}))" (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI5[OF borel_eq_lessThan])
  have move_uminus: "\<And>x y::real. -x \<le> y \<longleftrightarrow> -y \<le> x" by auto
  fix x :: real
  have "{..<x} = (\<Union>i::nat. {-real i ..< x})"
    by (auto simp: move_uminus real_arch_simple)
  then show "{..< x} \<in> ?SIGMA"
    by (auto intro: sigma_sets.intros)
qed auto

lemma borel_eq_closed: "borel = sigma UNIV (Collect closed)"
  unfolding borel_def
proof (intro sigma_eqI sigma_sets_eqI, safe)
  fix x :: "'a set" assume "open x"
  hence "x = UNIV - (UNIV - x)" by auto
  also have "\<dots> \<in> sigma_sets UNIV (Collect closed)"
    by (rule sigma_sets.Compl)
       (auto intro!: sigma_sets.Basic simp: `open x`)
  finally show "x \<in> sigma_sets UNIV (Collect closed)" by simp
next
  fix x :: "'a set" assume "closed x"
  hence "x = UNIV - (UNIV - x)" by auto
  also have "\<dots> \<in> sigma_sets UNIV (Collect open)"
    by (rule sigma_sets.Compl)
       (auto intro!: sigma_sets.Basic simp: `closed x`)
  finally show "x \<in> sigma_sets UNIV (Collect open)" by simp
qed simp_all

lemma borel_eq_enumerated_basis:
  fixes f::"nat\<Rightarrow>'a::topological_space set"
  assumes "topological_basis (range f)"
  shows "borel = sigma UNIV (range f)"
  unfolding borel_def
proof (intro sigma_eqI sigma_sets_eqI, safe)
  interpret enumerates_basis proof qed (rule assms)
  fix x::"'a set" assume "open x"
  from open_enumerable_basisE[OF this] guess N .
  hence x: "x = (\<Union>n. if n \<in> N then f n else {})" by (auto split: split_if_asm)
  also have "\<dots> \<in> sigma_sets UNIV (range f)" by (auto intro!: sigma_sets.Empty Union)
  finally show "x \<in> sigma_sets UNIV (range f)" .
next
  fix n
  have "open (f n)" by (rule topological_basis_open[OF assms]) simp
  thus "f n \<in> sigma_sets UNIV (Collect open)" by auto
qed simp_all

lemma borel_eq_enum_basis:
  "borel = sigma UNIV (range enum_basis)"
  by (rule borel_eq_enumerated_basis[OF enum_basis_basis])

lemma borel_measurable_halfspacesI:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>ordered_euclidean_space"
  assumes F: "borel = sigma UNIV (range F)"
  and S_eq: "\<And>a i. S a i = f -` F (a,i) \<inter> space M" 
  and S: "\<And>a i. \<not> i < DIM('c) \<Longrightarrow> S a i \<in> sets M"
  shows "f \<in> borel_measurable M = (\<forall>i<DIM('c). \<forall>a::real. S a i \<in> sets M)"
proof safe
  fix a :: real and i assume i: "i < DIM('c)" and f: "f \<in> borel_measurable M"
  then show "S a i \<in> sets M" unfolding assms
    by (auto intro!: measurable_sets sigma_sets.Basic simp: assms(1))
next
  assume a: "\<forall>i<DIM('c). \<forall>a. S a i \<in> sets M"
  { fix a i have "S a i \<in> sets M"
    proof cases
      assume "i < DIM('c)"
      with a show ?thesis unfolding assms(2) by simp
    next
      assume "\<not> i < DIM('c)"
      from S[OF this] show ?thesis .
    qed }
  then show "f \<in> borel_measurable M"
    by (auto intro!: measurable_measure_of simp: S_eq F)
qed

lemma borel_measurable_iff_halfspace_le:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>ordered_euclidean_space"
  shows "f \<in> borel_measurable M = (\<forall>i<DIM('c). \<forall>a. {w \<in> space M. f w $$ i \<le> a} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_eq_halfspace_le]) auto

lemma borel_measurable_iff_halfspace_less:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>ordered_euclidean_space"
  shows "f \<in> borel_measurable M \<longleftrightarrow> (\<forall>i<DIM('c). \<forall>a. {w \<in> space M. f w $$ i < a} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_eq_halfspace_less]) auto

lemma borel_measurable_iff_halfspace_ge:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>ordered_euclidean_space"
  shows "f \<in> borel_measurable M = (\<forall>i<DIM('c). \<forall>a. {w \<in> space M. a \<le> f w $$ i} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_eq_halfspace_ge]) auto

lemma borel_measurable_iff_halfspace_greater:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>ordered_euclidean_space"
  shows "f \<in> borel_measurable M \<longleftrightarrow> (\<forall>i<DIM('c). \<forall>a. {w \<in> space M. a < f w $$ i} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_eq_halfspace_greater]) auto

lemma borel_measurable_iff_le:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. f w \<le> a} \<in> sets M)"
  using borel_measurable_iff_halfspace_le[where 'c=real] by simp

lemma borel_measurable_iff_less:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. f w < a} \<in> sets M)"
  using borel_measurable_iff_halfspace_less[where 'c=real] by simp

lemma borel_measurable_iff_ge:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. a \<le> f w} \<in> sets M)"
  using borel_measurable_iff_halfspace_ge[where 'c=real]
  by simp

lemma borel_measurable_iff_greater:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. a < f w} \<in> sets M)"
  using borel_measurable_iff_halfspace_greater[where 'c=real] by simp

lemma borel_measurable_euclidean_space:
  fixes f :: "'a \<Rightarrow> 'c::ordered_euclidean_space"
  shows "f \<in> borel_measurable M \<longleftrightarrow> (\<forall>i<DIM('c). (\<lambda>x. f x $$ i) \<in> borel_measurable M)"
proof safe
  fix i assume "f \<in> borel_measurable M"
  then show "(\<lambda>x. f x $$ i) \<in> borel_measurable M"
    by (auto intro: borel_measurable_euclidean_component)
next
  assume f: "\<forall>i<DIM('c). (\<lambda>x. f x $$ i) \<in> borel_measurable M"
  then show "f \<in> borel_measurable M"
    unfolding borel_measurable_iff_halfspace_le by auto
qed

subsection "Borel measurable operators"

lemma borel_measurable_continuous_on:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes f: "continuous_on UNIV f" and g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f (g x)) \<in> borel_measurable M"
  using measurable_comp[OF g borel_measurable_continuous_on1[OF f]] by (simp add: comp_def)

lemma borel_measurable_continuous_on_open':
  fixes f :: "'a::topological_space \<Rightarrow> 'b::t1_space"
  assumes cont: "continuous_on A f" "open A"
  shows "(\<lambda>x. if x \<in> A then f x else c) \<in> borel_measurable borel" (is "?f \<in> _")
proof (rule borel_measurableI)
  fix S :: "'b set" assume "open S"
  then have "open {x\<in>A. f x \<in> S}"
    by (intro continuous_open_preimage[OF cont]) auto
  then have *: "{x\<in>A. f x \<in> S} \<in> sets borel" by auto
  have "?f -` S \<inter> space borel = 
    {x\<in>A. f x \<in> S} \<union> (if c \<in> S then space borel - A else {})"
    by (auto split: split_if_asm)
  also have "\<dots> \<in> sets borel"
    using * `open A` by auto
  finally show "?f -` S \<inter> space borel \<in> sets borel" .
qed

lemma borel_measurable_continuous_on_open:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::t1_space"
  assumes cont: "continuous_on A f" "open A"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. if g x \<in> A then f (g x) else c) \<in> borel_measurable M"
  using measurable_comp[OF g borel_measurable_continuous_on_open'[OF cont], of c]
  by (simp add: comp_def)

lemma borel_measurable_uminus[measurable (raw)]:
  fixes g :: "'a \<Rightarrow> real"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. - g x) \<in> borel_measurable M"
  by (rule borel_measurable_continuous_on[OF _ g]) (auto intro: continuous_on_minus continuous_on_id)

lemma euclidean_component_prod:
  fixes x :: "'a :: euclidean_space \<times> 'b :: euclidean_space"
  shows "x $$ i = (if i < DIM('a) then fst x $$ i else snd x $$ (i - DIM('a)))"
  unfolding euclidean_component_def basis_prod_def inner_prod_def by auto

lemma borel_measurable_Pair[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> 'b::ordered_euclidean_space" and g :: "'a \<Rightarrow> 'c::ordered_euclidean_space"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. (f x, g x)) \<in> borel_measurable M"
proof (intro borel_measurable_iff_halfspace_le[THEN iffD2] allI impI)
  fix i and a :: real assume i: "i < DIM('b \<times> 'c)"
  have [simp]: "\<And>P A B C. {w. (P \<longrightarrow> A w \<and> B w) \<and> (\<not> P \<longrightarrow> A w \<and> C w)} = 
    {w. A w \<and> (P \<longrightarrow> B w) \<and> (\<not> P \<longrightarrow> C w)}" by auto
  from i f g show "{w \<in> space M. (f w, g w) $$ i \<le> a} \<in> sets M"
    by (auto simp: euclidean_component_prod)
qed

lemma continuous_on_fst: "continuous_on UNIV fst"
proof -
  have [simp]: "range fst = UNIV" by (auto simp: image_iff)
  show ?thesis
    using closed_vimage_fst
    by (auto simp: continuous_on_closed closed_closedin vimage_def)
qed

lemma continuous_on_snd: "continuous_on UNIV snd"
proof -
  have [simp]: "range snd = UNIV" by (auto simp: image_iff)
  show ?thesis
    using closed_vimage_snd
    by (auto simp: continuous_on_closed closed_closedin vimage_def)
qed

lemma borel_measurable_continuous_Pair:
  fixes f :: "'a \<Rightarrow> 'b::ordered_euclidean_space" and g :: "'a \<Rightarrow> 'c::ordered_euclidean_space"
  assumes [measurable]: "f \<in> borel_measurable M"
  assumes [measurable]: "g \<in> borel_measurable M"
  assumes H: "continuous_on UNIV (\<lambda>x. H (fst x) (snd x))"
  shows "(\<lambda>x. H (f x) (g x)) \<in> borel_measurable M"
proof -
  have eq: "(\<lambda>x. H (f x) (g x)) = (\<lambda>x. (\<lambda>x. H (fst x) (snd x)) (f x, g x))" by auto
  show ?thesis
    unfolding eq by (rule borel_measurable_continuous_on[OF H]) auto
qed

lemma borel_measurable_add[measurable (raw)]:
  fixes f g :: "'a \<Rightarrow> 'c::ordered_euclidean_space"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x + g x) \<in> borel_measurable M"
  using f g
  by (rule borel_measurable_continuous_Pair)
     (auto intro: continuous_on_fst continuous_on_snd continuous_on_add)

lemma borel_measurable_setsum[measurable (raw)]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> real"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Sum>i\<in>S. f i x) \<in> borel_measurable M"
proof cases
  assume "finite S"
  thus ?thesis using assms by induct auto
qed simp

lemma borel_measurable_diff[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x - g x) \<in> borel_measurable M"
  unfolding diff_minus using assms by simp

lemma borel_measurable_times[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x * g x) \<in> borel_measurable M"
  using f g
  by (rule borel_measurable_continuous_Pair)
     (auto intro: continuous_on_fst continuous_on_snd continuous_on_mult)

lemma continuous_on_dist:
  fixes f :: "'a :: t2_space \<Rightarrow> 'b :: metric_space"
  shows "continuous_on A f \<Longrightarrow> continuous_on A g \<Longrightarrow> continuous_on A (\<lambda>x. dist (f x) (g x))"
  unfolding continuous_on_eq_continuous_within by (auto simp: continuous_dist)

lemma borel_measurable_dist[measurable (raw)]:
  fixes g f :: "'a \<Rightarrow> 'b::ordered_euclidean_space"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. dist (f x) (g x)) \<in> borel_measurable M"
  using f g
  by (rule borel_measurable_continuous_Pair)
     (intro continuous_on_dist continuous_on_fst continuous_on_snd)
  
lemma borel_measurable_scaleR[measurable (raw)]:
  fixes g :: "'a \<Rightarrow> 'b::ordered_euclidean_space"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x *\<^sub>R g x) \<in> borel_measurable M"
  by (rule borel_measurable_continuous_Pair[OF f g])
     (auto intro!: continuous_on_scaleR continuous_on_fst continuous_on_snd)

lemma affine_borel_measurable_vector:
  fixes f :: "'a \<Rightarrow> 'x::real_normed_vector"
  assumes "f \<in> borel_measurable M"
  shows "(\<lambda>x. a + b *\<^sub>R f x) \<in> borel_measurable M"
proof (rule borel_measurableI)
  fix S :: "'x set" assume "open S"
  show "(\<lambda>x. a + b *\<^sub>R f x) -` S \<inter> space M \<in> sets M"
  proof cases
    assume "b \<noteq> 0"
    with `open S` have "open ((\<lambda>x. (- a + x) /\<^sub>R b) ` S)" (is "open ?S")
      by (auto intro!: open_affinity simp: scaleR_add_right)
    hence "?S \<in> sets borel" by auto
    moreover
    from `b \<noteq> 0` have "(\<lambda>x. a + b *\<^sub>R f x) -` S = f -` ?S"
      apply auto by (rule_tac x="a + b *\<^sub>R f x" in image_eqI, simp_all)
    ultimately show ?thesis using assms unfolding in_borel_measurable_borel
      by auto
  qed simp
qed

lemma borel_measurable_const_scaleR[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. b *\<^sub>R f x ::'a::real_normed_vector) \<in> borel_measurable M"
  using affine_borel_measurable_vector[of f M 0 b] by simp

lemma borel_measurable_const_add[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. a + f x ::'a::real_normed_vector) \<in> borel_measurable M"
  using affine_borel_measurable_vector[of f M a 1] by simp

lemma borel_measurable_setprod[measurable (raw)]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> real"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Prod>i\<in>S. f i x) \<in> borel_measurable M"
proof cases
  assume "finite S"
  thus ?thesis using assms by induct auto
qed simp

lemma borel_measurable_inverse[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. inverse (f x)) \<in> borel_measurable M"
proof -
  have "(\<lambda>x::real. if x \<in> UNIV - {0} then inverse x else 0) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_on_open' continuous_on_inverse continuous_on_id) auto
  also have "(\<lambda>x::real. if x \<in> UNIV - {0} then inverse x else 0) = inverse" by (intro ext) auto
  finally show ?thesis using f by simp
qed

lemma borel_measurable_divide[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. f x / g x::real) \<in> borel_measurable M"
  by (simp add: field_divide_inverse)

lemma borel_measurable_max[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. max (g x) (f x) :: real) \<in> borel_measurable M"
  by (simp add: max_def)

lemma borel_measurable_min[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. min (g x) (f x) :: real) \<in> borel_measurable M"
  by (simp add: min_def)

lemma borel_measurable_abs[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. \<bar>f x :: real\<bar>) \<in> borel_measurable M"
  unfolding abs_real_def by simp

lemma borel_measurable_nth[measurable (raw)]:
  "(\<lambda>x::real^'n. x $ i) \<in> borel_measurable borel"
  by (simp add: nth_conv_component)

lemma convex_measurable:
  fixes a b :: real
  assumes X: "X \<in> borel_measurable M" "X ` space M \<subseteq> { a <..< b}"
  assumes q: "convex_on { a <..< b} q"
  shows "(\<lambda>x. q (X x)) \<in> borel_measurable M"
proof -
  have "(\<lambda>x. if X x \<in> {a <..< b} then q (X x) else 0) \<in> borel_measurable M" (is "?qX")
  proof (rule borel_measurable_continuous_on_open[OF _ _ X(1)])
    show "open {a<..<b}" by auto
    from this q show "continuous_on {a<..<b} q"
      by (rule convex_on_continuous)
  qed
  also have "?qX \<longleftrightarrow> (\<lambda>x. q (X x)) \<in> borel_measurable M"
    using X by (intro measurable_cong) auto
  finally show ?thesis .
qed

lemma borel_measurable_ln[measurable (raw)]:
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. ln (f x)) \<in> borel_measurable M"
proof -
  { fix x :: real assume x: "x \<le> 0"
    { fix x::real assume "x \<le> 0" then have "\<And>u. exp u = x \<longleftrightarrow> False" by auto }
    from this[of x] x this[of 0] have "ln 0 = ln x"
      by (auto simp: ln_def) }
  note ln_imp = this
  have "(\<lambda>x. if f x \<in> {0<..} then ln (f x) else ln 0) \<in> borel_measurable M"
  proof (rule borel_measurable_continuous_on_open[OF _ _ f])
    show "continuous_on {0<..} ln"
      by (auto intro!: continuous_at_imp_continuous_on DERIV_ln DERIV_isCont
               simp: continuous_isCont[symmetric])
    show "open ({0<..}::real set)" by auto
  qed
  also have "(\<lambda>x. if x \<in> {0<..} then ln x else ln 0) = ln"
    by (simp add: fun_eq_iff not_less ln_imp)
  finally show ?thesis .
qed

lemma borel_measurable_log[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. log (g x) (f x)) \<in> borel_measurable M"
  unfolding log_def by auto

lemma measurable_count_space_eq2_countable:
  fixes f :: "'a => 'c::countable"
  shows "f \<in> measurable M (count_space A) \<longleftrightarrow> (f \<in> space M \<rightarrow> A \<and> (\<forall>a\<in>A. f -` {a} \<inter> space M \<in> sets M))"
proof -
  { fix X assume "X \<subseteq> A" "f \<in> space M \<rightarrow> A"
    then have "f -` X \<inter> space M = (\<Union>a\<in>X. f -` {a} \<inter> space M)"
      by auto
    moreover assume "\<And>a. a\<in>A \<Longrightarrow> f -` {a} \<inter> space M \<in> sets M"
    ultimately have "f -` X \<inter> space M \<in> sets M"
      using `X \<subseteq> A` by (simp add: subset_eq del: UN_simps) }
  then show ?thesis
    unfolding measurable_def by auto
qed

lemma measurable_real_floor[measurable]:
  "(floor :: real \<Rightarrow> int) \<in> measurable borel (count_space UNIV)"
proof -
  have "\<And>a x. \<lfloor>x\<rfloor> = a \<longleftrightarrow> (real a \<le> x \<and> x < real (a + 1))"
    by (auto intro: floor_eq2)
  then show ?thesis
    by (auto simp: vimage_def measurable_count_space_eq2_countable)
qed

lemma measurable_real_natfloor[measurable]:
  "(natfloor :: real \<Rightarrow> nat) \<in> measurable borel (count_space UNIV)"
  by (simp add: natfloor_def[abs_def])

lemma measurable_real_ceiling[measurable]:
  "(ceiling :: real \<Rightarrow> int) \<in> measurable borel (count_space UNIV)"
  unfolding ceiling_def[abs_def] by simp

lemma borel_measurable_real_floor: "(\<lambda>x::real. real \<lfloor>x\<rfloor>) \<in> borel_measurable borel"
  by simp

lemma borel_measurable_real_natfloor:
  "f \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. real (natfloor (f x))) \<in> borel_measurable M"
  by simp

subsection "Borel space on the extended reals"

lemma borel_measurable_ereal[measurable (raw)]:
  assumes f: "f \<in> borel_measurable M" shows "(\<lambda>x. ereal (f x)) \<in> borel_measurable M"
  using continuous_on_ereal f by (rule borel_measurable_continuous_on)

lemma borel_measurable_real_of_ereal[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> ereal" 
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. real (f x)) \<in> borel_measurable M"
proof -
  have "(\<lambda>x. if f x \<in> UNIV - { \<infinity>, - \<infinity> } then real (f x) else 0) \<in> borel_measurable M"
    using continuous_on_real
    by (rule borel_measurable_continuous_on_open[OF _ _ f]) auto
  also have "(\<lambda>x. if f x \<in> UNIV - { \<infinity>, - \<infinity> } then real (f x) else 0) = (\<lambda>x. real (f x))"
    by auto
  finally show ?thesis .
qed

lemma borel_measurable_ereal_cases:
  fixes f :: "'a \<Rightarrow> ereal" 
  assumes f: "f \<in> borel_measurable M"
  assumes H: "(\<lambda>x. H (ereal (real (f x)))) \<in> borel_measurable M"
  shows "(\<lambda>x. H (f x)) \<in> borel_measurable M"
proof -
  let ?F = "\<lambda>x. if f x = \<infinity> then H \<infinity> else if f x = - \<infinity> then H (-\<infinity>) else H (ereal (real (f x)))"
  { fix x have "H (f x) = ?F x" by (cases "f x") auto }
  with f H show ?thesis by simp
qed

lemma
  fixes f :: "'a \<Rightarrow> ereal" assumes f[measurable]: "f \<in> borel_measurable M"
  shows borel_measurable_ereal_abs[measurable(raw)]: "(\<lambda>x. \<bar>f x\<bar>) \<in> borel_measurable M"
    and borel_measurable_ereal_inverse[measurable(raw)]: "(\<lambda>x. inverse (f x) :: ereal) \<in> borel_measurable M"
    and borel_measurable_uminus_ereal[measurable(raw)]: "(\<lambda>x. - f x :: ereal) \<in> borel_measurable M"
  by (auto simp del: abs_real_of_ereal simp: borel_measurable_ereal_cases[OF f] measurable_If)

lemma borel_measurable_uminus_eq_ereal[simp]:
  "(\<lambda>x. - f x :: ereal) \<in> borel_measurable M \<longleftrightarrow> f \<in> borel_measurable M" (is "?l = ?r")
proof
  assume ?l from borel_measurable_uminus_ereal[OF this] show ?r by simp
qed auto

lemma set_Collect_ereal2:
  fixes f g :: "'a \<Rightarrow> ereal" 
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  assumes H: "{x \<in> space M. H (ereal (real (f x))) (ereal (real (g x)))} \<in> sets M"
    "{x \<in> space borel. H (-\<infinity>) (ereal x)} \<in> sets borel"
    "{x \<in> space borel. H (\<infinity>) (ereal x)} \<in> sets borel"
    "{x \<in> space borel. H (ereal x) (-\<infinity>)} \<in> sets borel"
    "{x \<in> space borel. H (ereal x) (\<infinity>)} \<in> sets borel"
  shows "{x \<in> space M. H (f x) (g x)} \<in> sets M"
proof -
  let ?G = "\<lambda>y x. if g x = \<infinity> then H y \<infinity> else if g x = -\<infinity> then H y (-\<infinity>) else H y (ereal (real (g x)))"
  let ?F = "\<lambda>x. if f x = \<infinity> then ?G \<infinity> x else if f x = -\<infinity> then ?G (-\<infinity>) x else ?G (ereal (real (f x))) x"
  { fix x have "H (f x) (g x) = ?F x" by (cases "f x" "g x" rule: ereal2_cases) auto }
  note * = this
  from assms show ?thesis
    by (subst *) (simp del: space_borel split del: split_if)
qed

lemma [measurable]:
  fixes f g :: "'a \<Rightarrow> ereal"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows borel_measurable_ereal_le: "{x \<in> space M. f x \<le> g x} \<in> sets M"
    and borel_measurable_ereal_less: "{x \<in> space M. f x < g x} \<in> sets M"
    and borel_measurable_ereal_eq: "{w \<in> space M. f w = g w} \<in> sets M"
  using f g by (simp_all add: set_Collect_ereal2)

lemma borel_measurable_ereal_neq:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> {w \<in> space M. f w \<noteq> (g w :: ereal)} \<in> sets M"
  by simp

lemma borel_measurable_ereal_iff:
  shows "(\<lambda>x. ereal (f x)) \<in> borel_measurable M \<longleftrightarrow> f \<in> borel_measurable M"
proof
  assume "(\<lambda>x. ereal (f x)) \<in> borel_measurable M"
  from borel_measurable_real_of_ereal[OF this]
  show "f \<in> borel_measurable M" by auto
qed auto

lemma borel_measurable_ereal_iff_real:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "f \<in> borel_measurable M \<longleftrightarrow>
    ((\<lambda>x. real (f x)) \<in> borel_measurable M \<and> f -` {\<infinity>} \<inter> space M \<in> sets M \<and> f -` {-\<infinity>} \<inter> space M \<in> sets M)"
proof safe
  assume *: "(\<lambda>x. real (f x)) \<in> borel_measurable M" "f -` {\<infinity>} \<inter> space M \<in> sets M" "f -` {-\<infinity>} \<inter> space M \<in> sets M"
  have "f -` {\<infinity>} \<inter> space M = {x\<in>space M. f x = \<infinity>}" "f -` {-\<infinity>} \<inter> space M = {x\<in>space M. f x = -\<infinity>}" by auto
  with * have **: "{x\<in>space M. f x = \<infinity>} \<in> sets M" "{x\<in>space M. f x = -\<infinity>} \<in> sets M" by simp_all
  let ?f = "\<lambda>x. if f x = \<infinity> then \<infinity> else if f x = -\<infinity> then -\<infinity> else ereal (real (f x))"
  have "?f \<in> borel_measurable M" using * ** by (intro measurable_If) auto
  also have "?f = f" by (auto simp: fun_eq_iff ereal_real)
  finally show "f \<in> borel_measurable M" .
qed simp_all

lemma borel_measurable_eq_atMost_ereal:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "f \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. f -` {..a} \<inter> space M \<in> sets M)"
proof (intro iffI allI)
  assume pos[rule_format]: "\<forall>a. f -` {..a} \<inter> space M \<in> sets M"
  show "f \<in> borel_measurable M"
    unfolding borel_measurable_ereal_iff_real borel_measurable_iff_le
  proof (intro conjI allI)
    fix a :: real
    { fix x :: ereal assume *: "\<forall>i::nat. real i < x"
      have "x = \<infinity>"
      proof (rule ereal_top)
        fix B from reals_Archimedean2[of B] guess n ..
        then have "ereal B < real n" by auto
        with * show "B \<le> x" by (metis less_trans less_imp_le)
      qed }
    then have "f -` {\<infinity>} \<inter> space M = space M - (\<Union>i::nat. f -` {.. real i} \<inter> space M)"
      by (auto simp: not_le)
    then show "f -` {\<infinity>} \<inter> space M \<in> sets M" using pos
      by (auto simp del: UN_simps)
    moreover
    have "{-\<infinity>::ereal} = {..-\<infinity>}" by auto
    then show "f -` {-\<infinity>} \<inter> space M \<in> sets M" using pos by auto
    moreover have "{x\<in>space M. f x \<le> ereal a} \<in> sets M"
      using pos[of "ereal a"] by (simp add: vimage_def Int_def conj_commute)
    moreover have "{w \<in> space M. real (f w) \<le> a} =
      (if a < 0 then {w \<in> space M. f w \<le> ereal a} - f -` {-\<infinity>} \<inter> space M
      else {w \<in> space M. f w \<le> ereal a} \<union> (f -` {\<infinity>} \<inter> space M) \<union> (f -` {-\<infinity>} \<inter> space M))" (is "?l = ?r")
      proof (intro set_eqI) fix x show "x \<in> ?l \<longleftrightarrow> x \<in> ?r" by (cases "f x") auto qed
    ultimately show "{w \<in> space M. real (f w) \<le> a} \<in> sets M" by auto
  qed
qed (simp add: measurable_sets)

lemma borel_measurable_eq_atLeast_ereal:
  "(f::'a \<Rightarrow> ereal) \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. f -` {a..} \<inter> space M \<in> sets M)"
proof
  assume pos: "\<forall>a. f -` {a..} \<inter> space M \<in> sets M"
  moreover have "\<And>a. (\<lambda>x. - f x) -` {..a} = f -` {-a ..}"
    by (auto simp: ereal_uminus_le_reorder)
  ultimately have "(\<lambda>x. - f x) \<in> borel_measurable M"
    unfolding borel_measurable_eq_atMost_ereal by auto
  then show "f \<in> borel_measurable M" by simp
qed (simp add: measurable_sets)

lemma greater_eq_le_measurable:
  fixes f :: "'a \<Rightarrow> 'c::linorder"
  shows "f -` {..< a} \<inter> space M \<in> sets M \<longleftrightarrow> f -` {a ..} \<inter> space M \<in> sets M"
proof
  assume "f -` {a ..} \<inter> space M \<in> sets M"
  moreover have "f -` {..< a} \<inter> space M = space M - f -` {a ..} \<inter> space M" by auto
  ultimately show "f -` {..< a} \<inter> space M \<in> sets M" by auto
next
  assume "f -` {..< a} \<inter> space M \<in> sets M"
  moreover have "f -` {a ..} \<inter> space M = space M - f -` {..< a} \<inter> space M" by auto
  ultimately show "f -` {a ..} \<inter> space M \<in> sets M" by auto
qed

lemma borel_measurable_ereal_iff_less:
  "(f::'a \<Rightarrow> ereal) \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. f -` {..< a} \<inter> space M \<in> sets M)"
  unfolding borel_measurable_eq_atLeast_ereal greater_eq_le_measurable ..

lemma less_eq_ge_measurable:
  fixes f :: "'a \<Rightarrow> 'c::linorder"
  shows "f -` {a <..} \<inter> space M \<in> sets M \<longleftrightarrow> f -` {..a} \<inter> space M \<in> sets M"
proof
  assume "f -` {a <..} \<inter> space M \<in> sets M"
  moreover have "f -` {..a} \<inter> space M = space M - f -` {a <..} \<inter> space M" by auto
  ultimately show "f -` {..a} \<inter> space M \<in> sets M" by auto
next
  assume "f -` {..a} \<inter> space M \<in> sets M"
  moreover have "f -` {a <..} \<inter> space M = space M - f -` {..a} \<inter> space M" by auto
  ultimately show "f -` {a <..} \<inter> space M \<in> sets M" by auto
qed

lemma borel_measurable_ereal_iff_ge:
  "(f::'a \<Rightarrow> ereal) \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. f -` {a <..} \<inter> space M \<in> sets M)"
  unfolding borel_measurable_eq_atMost_ereal less_eq_ge_measurable ..

lemma borel_measurable_ereal2:
  fixes f g :: "'a \<Rightarrow> ereal" 
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  assumes H: "(\<lambda>x. H (ereal (real (f x))) (ereal (real (g x)))) \<in> borel_measurable M"
    "(\<lambda>x. H (-\<infinity>) (ereal (real (g x)))) \<in> borel_measurable M"
    "(\<lambda>x. H (\<infinity>) (ereal (real (g x)))) \<in> borel_measurable M"
    "(\<lambda>x. H (ereal (real (f x))) (-\<infinity>)) \<in> borel_measurable M"
    "(\<lambda>x. H (ereal (real (f x))) (\<infinity>)) \<in> borel_measurable M"
  shows "(\<lambda>x. H (f x) (g x)) \<in> borel_measurable M"
proof -
  let ?G = "\<lambda>y x. if g x = \<infinity> then H y \<infinity> else if g x = - \<infinity> then H y (-\<infinity>) else H y (ereal (real (g x)))"
  let ?F = "\<lambda>x. if f x = \<infinity> then ?G \<infinity> x else if f x = - \<infinity> then ?G (-\<infinity>) x else ?G (ereal (real (f x))) x"
  { fix x have "H (f x) (g x) = ?F x" by (cases "f x" "g x" rule: ereal2_cases) auto }
  note * = this
  from assms show ?thesis unfolding * by simp
qed

lemma
  fixes f :: "'a \<Rightarrow> ereal" assumes f: "f \<in> borel_measurable M"
  shows borel_measurable_ereal_eq_const: "{x\<in>space M. f x = c} \<in> sets M"
    and borel_measurable_ereal_neq_const: "{x\<in>space M. f x \<noteq> c} \<in> sets M"
  using f by auto

lemma [measurable(raw)]:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows borel_measurable_ereal_add: "(\<lambda>x. f x + g x) \<in> borel_measurable M"
    and borel_measurable_ereal_times: "(\<lambda>x. f x * g x) \<in> borel_measurable M"
    and borel_measurable_ereal_min: "(\<lambda>x. min (g x) (f x)) \<in> borel_measurable M"
    and borel_measurable_ereal_max: "(\<lambda>x. max (g x) (f x)) \<in> borel_measurable M"
  by (simp_all add: borel_measurable_ereal2 min_def max_def)

lemma [measurable(raw)]:
  fixes f g :: "'a \<Rightarrow> ereal"
  assumes "f \<in> borel_measurable M"
  assumes "g \<in> borel_measurable M"
  shows borel_measurable_ereal_diff: "(\<lambda>x. f x - g x) \<in> borel_measurable M"
    and borel_measurable_ereal_divide: "(\<lambda>x. f x / g x) \<in> borel_measurable M"
  using assms by (simp_all add: minus_ereal_def divide_ereal_def)

lemma borel_measurable_ereal_setsum[measurable (raw)]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Sum>i\<in>S. f i x) \<in> borel_measurable M"
proof cases
  assume "finite S"
  thus ?thesis using assms
    by induct auto
qed simp

lemma borel_measurable_ereal_setprod[measurable (raw)]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Prod>i\<in>S. f i x) \<in> borel_measurable M"
proof cases
  assume "finite S"
  thus ?thesis using assms by induct auto
qed simp

lemma borel_measurable_SUP[measurable (raw)]:
  fixes f :: "'d\<Colon>countable \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> A \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. SUP i : A. f i x) \<in> borel_measurable M" (is "?sup \<in> borel_measurable M")
  unfolding borel_measurable_ereal_iff_ge
proof
  fix a
  have "?sup -` {a<..} \<inter> space M = (\<Union>i\<in>A. {x\<in>space M. a < f i x})"
    by (auto simp: less_SUP_iff)
  then show "?sup -` {a<..} \<inter> space M \<in> sets M"
    using assms by auto
qed

lemma borel_measurable_INF[measurable (raw)]:
  fixes f :: "'d :: countable \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> A \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. INF i : A. f i x) \<in> borel_measurable M" (is "?inf \<in> borel_measurable M")
  unfolding borel_measurable_ereal_iff_less
proof
  fix a
  have "?inf -` {..<a} \<inter> space M = (\<Union>i\<in>A. {x\<in>space M. f i x < a})"
    by (auto simp: INF_less_iff)
  then show "?inf -` {..<a} \<inter> space M \<in> sets M"
    using assms by auto
qed

lemma [measurable (raw)]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. f i \<in> borel_measurable M"
  shows borel_measurable_liminf: "(\<lambda>x. liminf (\<lambda>i. f i x)) \<in> borel_measurable M"
    and borel_measurable_limsup: "(\<lambda>x. limsup (\<lambda>i. f i x)) \<in> borel_measurable M"
  unfolding liminf_SUPR_INFI limsup_INFI_SUPR using assms by auto

lemma sets_Collect_eventually_sequentially[measurable]:
  "(\<And>i. {x\<in>space M. P x i} \<in> sets M) \<Longrightarrow> {x\<in>space M. eventually (P x) sequentially} \<in> sets M"
  unfolding eventually_sequentially by simp

lemma sets_Collect_ereal_convergent[measurable]: 
  fixes f :: "nat \<Rightarrow> 'a => ereal"
  assumes f[measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "{x\<in>space M. convergent (\<lambda>i. f i x)} \<in> sets M"
  unfolding convergent_ereal by auto

lemma borel_measurable_extreal_lim[measurable (raw)]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes [measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>x. lim (\<lambda>i. f i x)) \<in> borel_measurable M"
proof -
  have "\<And>x. lim (\<lambda>i. f i x) = (if convergent (\<lambda>i. f i x) then limsup (\<lambda>i. f i x) else (THE i. False))"
    using convergent_ereal_limsup by (simp add: lim_def convergent_def)
  then show ?thesis
    by simp
qed

lemma borel_measurable_ereal_LIMSEQ:
  fixes u :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes u': "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. u i x) ----> u' x"
  and u: "\<And>i. u i \<in> borel_measurable M"
  shows "u' \<in> borel_measurable M"
proof -
  have "\<And>x. x \<in> space M \<Longrightarrow> u' x = liminf (\<lambda>n. u n x)"
    using u' by (simp add: lim_imp_Liminf[symmetric])
  with u show ?thesis by (simp cong: measurable_cong)
qed

lemma borel_measurable_extreal_suminf[measurable (raw)]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes [measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>x. (\<Sum>i. f i x)) \<in> borel_measurable M"
  unfolding suminf_def sums_def[abs_def] lim_def[symmetric] by simp

section "LIMSEQ is borel measurable"

lemma borel_measurable_LIMSEQ:
  fixes u :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes u': "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. u i x) ----> u' x"
  and u: "\<And>i. u i \<in> borel_measurable M"
  shows "u' \<in> borel_measurable M"
proof -
  have "\<And>x. x \<in> space M \<Longrightarrow> liminf (\<lambda>n. ereal (u n x)) = ereal (u' x)"
    using u' by (simp add: lim_imp_Liminf)
  moreover from u have "(\<lambda>x. liminf (\<lambda>n. ereal (u n x))) \<in> borel_measurable M"
    by auto
  ultimately show ?thesis by (simp cong: measurable_cong add: borel_measurable_ereal_iff)
qed

lemma sets_Collect_Cauchy[measurable]: 
  fixes f :: "nat \<Rightarrow> 'a => real"
  assumes f[measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "{x\<in>space M. Cauchy (\<lambda>i. f i x)} \<in> sets M"
  unfolding Cauchy_iff2 using f by auto

lemma borel_measurable_lim[measurable (raw)]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes f[measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>x. lim (\<lambda>i. f i x)) \<in> borel_measurable M"
proof -
  def u' \<equiv> "\<lambda>x. lim (\<lambda>i. if Cauchy (\<lambda>i. f i x) then f i x else 0)"
  then have *: "\<And>x. lim (\<lambda>i. f i x) = (if Cauchy (\<lambda>i. f i x) then u' x else (THE x. False))"
    by (auto simp: lim_def convergent_eq_cauchy[symmetric])
  have "u' \<in> borel_measurable M"
  proof (rule borel_measurable_LIMSEQ)
    fix x
    have "convergent (\<lambda>i. if Cauchy (\<lambda>i. f i x) then f i x else 0)"
      by (cases "Cauchy (\<lambda>i. f i x)")
         (auto simp add: convergent_eq_cauchy[symmetric] convergent_def)
    then show "(\<lambda>i. if Cauchy (\<lambda>i. f i x) then f i x else 0) ----> u' x"
      unfolding u'_def 
      by (rule convergent_LIMSEQ_iff[THEN iffD1])
  qed measurable
  then show ?thesis
    unfolding * by measurable
qed

lemma borel_measurable_suminf[measurable (raw)]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes f[measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>x. suminf (\<lambda>i. f i x)) \<in> borel_measurable M"
  unfolding suminf_def sums_def[abs_def] lim_def[symmetric] by simp

end 
