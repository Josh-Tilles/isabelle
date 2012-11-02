(*  Title:      HOL/Probability/Infinite_Product_Measure.thy
    Author:     Johannes Hölzl, TU München
*)

header {*Infinite Product Measure*}

theory Infinite_Product_Measure
  imports Probability_Measure Caratheodory
begin

lemma extensional_UNIV[simp]: "extensional UNIV = UNIV"
  by (auto simp: extensional_def)

lemma restrict_extensional_sub[intro]: "A \<subseteq> B \<Longrightarrow> restrict f A \<in> extensional B"
  unfolding restrict_def extensional_def by auto

lemma restrict_restrict[simp]: "restrict (restrict f A) B = restrict f (A \<inter> B)"
  unfolding restrict_def by (simp add: fun_eq_iff)

lemma split_merge: "P (merge I J (x,y) i) \<longleftrightarrow> (i \<in> I \<longrightarrow> P (x i)) \<and> (i \<in> J - I \<longrightarrow> P (y i)) \<and> (i \<notin> I \<union> J \<longrightarrow> P undefined)"
  unfolding merge_def by auto

lemma extensional_merge_sub: "I \<union> J \<subseteq> K \<Longrightarrow> merge I J (x, y) \<in> extensional K"
  unfolding merge_def extensional_def by auto

lemma injective_vimage_restrict:
  assumes J: "J \<subseteq> I"
  and sets: "A \<subseteq> (\<Pi>\<^isub>E i\<in>J. S i)" "B \<subseteq> (\<Pi>\<^isub>E i\<in>J. S i)" and ne: "(\<Pi>\<^isub>E i\<in>I. S i) \<noteq> {}"
  and eq: "(\<lambda>x. restrict x J) -` A \<inter> (\<Pi>\<^isub>E i\<in>I. S i) = (\<lambda>x. restrict x J) -` B \<inter> (\<Pi>\<^isub>E i\<in>I. S i)"
  shows "A = B"
proof  (intro set_eqI)
  fix x
  from ne obtain y where y: "\<And>i. i \<in> I \<Longrightarrow> y i \<in> S i" by auto
  have "J \<inter> (I - J) = {}" by auto
  show "x \<in> A \<longleftrightarrow> x \<in> B"
  proof cases
    assume x: "x \<in> (\<Pi>\<^isub>E i\<in>J. S i)"
    have "x \<in> A \<longleftrightarrow> merge J (I - J) (x,y) \<in> (\<lambda>x. restrict x J) -` A \<inter> (\<Pi>\<^isub>E i\<in>I. S i)"
      using y x `J \<subseteq> I` by (auto simp add: Pi_iff extensional_restrict extensional_merge_sub split: split_merge)
    then show "x \<in> A \<longleftrightarrow> x \<in> B"
      using y x `J \<subseteq> I` by (auto simp add: Pi_iff extensional_restrict extensional_merge_sub eq split: split_merge)
  next
    assume "x \<notin> (\<Pi>\<^isub>E i\<in>J. S i)" with sets show "x \<in> A \<longleftrightarrow> x \<in> B" by auto
  qed
qed

lemma prod_algebraI_finite:
  "finite I \<Longrightarrow> (\<forall>i\<in>I. E i \<in> sets (M i)) \<Longrightarrow> (Pi\<^isub>E I E) \<in> prod_algebra I M"
  using prod_algebraI[of I I E M] prod_emb_PiE_same_index[of I E M, OF sets_into_space] by simp

lemma Int_stable_PiE: "Int_stable {Pi\<^isub>E J E | E. \<forall>i\<in>I. E i \<in> sets (M i)}"
proof (safe intro!: Int_stableI)
  fix E F assume "\<forall>i\<in>I. E i \<in> sets (M i)" "\<forall>i\<in>I. F i \<in> sets (M i)"
  then show "\<exists>G. Pi\<^isub>E J E \<inter> Pi\<^isub>E J F = Pi\<^isub>E J G \<and> (\<forall>i\<in>I. G i \<in> sets (M i))"
    by (auto intro!: exI[of _ "\<lambda>i. E i \<inter> F i"])
qed

lemma prod_emb_trans[simp]:
  "J \<subseteq> K \<Longrightarrow> K \<subseteq> L \<Longrightarrow> prod_emb L M K (prod_emb K M J X) = prod_emb L M J X"
  by (auto simp add: Int_absorb1 prod_emb_def)

lemma prod_emb_Pi:
  assumes "X \<in> (\<Pi> j\<in>J. sets (M j))" "J \<subseteq> K"
  shows "prod_emb K M J (Pi\<^isub>E J X) = (\<Pi>\<^isub>E i\<in>K. if i \<in> J then X i else space (M i))"
  using assms space_closed
  by (auto simp: prod_emb_def Pi_iff split: split_if_asm) blast+

lemma prod_emb_id:
  "B \<subseteq> (\<Pi>\<^isub>E i\<in>L. space (M i)) \<Longrightarrow> prod_emb L M L B = B"
  by (auto simp: prod_emb_def Pi_iff subset_eq extensional_restrict)

lemma measurable_prod_emb[intro, simp]:
  "J \<subseteq> L \<Longrightarrow> X \<in> sets (Pi\<^isub>M J M) \<Longrightarrow> prod_emb L M J X \<in> sets (Pi\<^isub>M L M)"
  unfolding prod_emb_def space_PiM[symmetric]
  by (auto intro!: measurable_sets measurable_restrict measurable_component_singleton)

lemma measurable_restrict_subset: "J \<subseteq> L \<Longrightarrow> (\<lambda>f. restrict f J) \<in> measurable (Pi\<^isub>M L M) (Pi\<^isub>M J M)"
  by (intro measurable_restrict measurable_component_singleton) auto

lemma (in product_prob_space) distr_restrict:
  assumes "J \<noteq> {}" "J \<subseteq> K" "finite K"
  shows "(\<Pi>\<^isub>M i\<in>J. M i) = distr (\<Pi>\<^isub>M i\<in>K. M i) (\<Pi>\<^isub>M i\<in>J. M i) (\<lambda>f. restrict f J)" (is "?P = ?D")
proof (rule measure_eqI_generator_eq)
  have "finite J" using `J \<subseteq> K` `finite K` by (auto simp add: finite_subset)
  interpret J: finite_product_prob_space M J proof qed fact
  interpret K: finite_product_prob_space M K proof qed fact

  let ?J = "{Pi\<^isub>E J E | E. \<forall>i\<in>J. E i \<in> sets (M i)}"
  let ?F = "\<lambda>i. \<Pi>\<^isub>E k\<in>J. space (M k)"
  let ?\<Omega> = "(\<Pi>\<^isub>E k\<in>J. space (M k))"
  show "Int_stable ?J"
    by (rule Int_stable_PiE)
  show "range ?F \<subseteq> ?J" "(\<Union>i. ?F i) = ?\<Omega>"
    using `finite J` by (auto intro!: prod_algebraI_finite)
  { fix i show "emeasure ?P (?F i) \<noteq> \<infinity>" by simp }
  show "?J \<subseteq> Pow ?\<Omega>" by (auto simp: Pi_iff dest: sets_into_space)
  show "sets (\<Pi>\<^isub>M i\<in>J. M i) = sigma_sets ?\<Omega> ?J" "sets ?D = sigma_sets ?\<Omega> ?J"
    using `finite J` by (simp_all add: sets_PiM prod_algebra_eq_finite Pi_iff)
  
  fix X assume "X \<in> ?J"
  then obtain E where [simp]: "X = Pi\<^isub>E J E" and E: "\<forall>i\<in>J. E i \<in> sets (M i)" by auto
  with `finite J` have X: "X \<in> sets (Pi\<^isub>M J M)"
    by simp

  have "emeasure ?P X = (\<Prod> i\<in>J. emeasure (M i) (E i))"
    using E by (simp add: J.measure_times)
  also have "\<dots> = (\<Prod> i\<in>J. emeasure (M i) (if i \<in> J then E i else space (M i)))"
    by simp
  also have "\<dots> = (\<Prod> i\<in>K. emeasure (M i) (if i \<in> J then E i else space (M i)))"
    using `finite K` `J \<subseteq> K`
    by (intro setprod_mono_one_left) (auto simp: M.emeasure_space_1)
  also have "\<dots> = emeasure (Pi\<^isub>M K M) (\<Pi>\<^isub>E i\<in>K. if i \<in> J then E i else space (M i))"
    using E by (simp add: K.measure_times)
  also have "(\<Pi>\<^isub>E i\<in>K. if i \<in> J then E i else space (M i)) = (\<lambda>f. restrict f J) -` Pi\<^isub>E J E \<inter> (\<Pi>\<^isub>E i\<in>K. space (M i))"
    using `J \<subseteq> K` sets_into_space E by (force simp:  Pi_iff split: split_if_asm)
  finally show "emeasure (Pi\<^isub>M J M) X = emeasure ?D X"
    using X `J \<subseteq> K` apply (subst emeasure_distr)
    by (auto intro!: measurable_restrict_subset simp: space_PiM)
qed

abbreviation (in product_prob_space)
  "emb L K X \<equiv> prod_emb L M K X"

lemma (in product_prob_space) emeasure_prod_emb[simp]:
  assumes L: "J \<noteq> {}" "J \<subseteq> L" "finite L" and X: "X \<in> sets (Pi\<^isub>M J M)"
  shows "emeasure (Pi\<^isub>M L M) (emb L J X) = emeasure (Pi\<^isub>M J M) X"
  by (subst distr_restrict[OF L])
     (simp add: prod_emb_def space_PiM emeasure_distr measurable_restrict_subset L X)

lemma (in product_prob_space) prod_emb_injective:
  assumes "J \<noteq> {}" "J \<subseteq> L" "finite J" and sets: "X \<in> sets (Pi\<^isub>M J M)" "Y \<in> sets (Pi\<^isub>M J M)"
  assumes "prod_emb L M J X = prod_emb L M J Y"
  shows "X = Y"
proof (rule injective_vimage_restrict)
  show "X \<subseteq> (\<Pi>\<^isub>E i\<in>J. space (M i))" "Y \<subseteq> (\<Pi>\<^isub>E i\<in>J. space (M i))"
    using sets[THEN sets_into_space] by (auto simp: space_PiM)
  have "\<forall>i\<in>L. \<exists>x. x \<in> space (M i)"
      using M.not_empty by auto
  from bchoice[OF this]
  show "(\<Pi>\<^isub>E i\<in>L. space (M i)) \<noteq> {}" by auto
  show "(\<lambda>x. restrict x J) -` X \<inter> (\<Pi>\<^isub>E i\<in>L. space (M i)) = (\<lambda>x. restrict x J) -` Y \<inter> (\<Pi>\<^isub>E i\<in>L. space (M i))"
    using `prod_emb L M J X = prod_emb L M J Y` by (simp add: prod_emb_def)
qed fact

definition (in product_prob_space) generator :: "('i \<Rightarrow> 'a) set set" where
  "generator = (\<Union>J\<in>{J. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I}. emb I J ` sets (Pi\<^isub>M J M))"

lemma (in product_prob_space) generatorI':
  "J \<noteq> {} \<Longrightarrow> finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> X \<in> sets (Pi\<^isub>M J M) \<Longrightarrow> emb I J X \<in> generator"
  unfolding generator_def by auto

lemma (in product_prob_space) algebra_generator:
  assumes "I \<noteq> {}" shows "algebra (\<Pi>\<^isub>E i\<in>I. space (M i)) generator" (is "algebra ?\<Omega> ?G")
  unfolding algebra_def algebra_axioms_def ring_of_sets_iff
proof (intro conjI ballI)
  let ?G = generator
  show "?G \<subseteq> Pow ?\<Omega>"
    by (auto simp: generator_def prod_emb_def)
  from `I \<noteq> {}` obtain i where "i \<in> I" by auto
  then show "{} \<in> ?G"
    by (auto intro!: exI[of _ "{i}"] image_eqI[where x="\<lambda>i. {}"]
             simp: sigma_sets.Empty generator_def prod_emb_def)
  from `i \<in> I` show "?\<Omega> \<in> ?G"
    by (auto intro!: exI[of _ "{i}"] image_eqI[where x="Pi\<^isub>E {i} (\<lambda>i. space (M i))"]
             simp: generator_def prod_emb_def)
  fix A assume "A \<in> ?G"
  then obtain JA XA where XA: "JA \<noteq> {}" "finite JA" "JA \<subseteq> I" "XA \<in> sets (Pi\<^isub>M JA M)" and A: "A = emb I JA XA"
    by (auto simp: generator_def)
  fix B assume "B \<in> ?G"
  then obtain JB XB where XB: "JB \<noteq> {}" "finite JB" "JB \<subseteq> I" "XB \<in> sets (Pi\<^isub>M JB M)" and B: "B = emb I JB XB"
    by (auto simp: generator_def)
  let ?RA = "emb (JA \<union> JB) JA XA"
  let ?RB = "emb (JA \<union> JB) JB XB"
  have *: "A - B = emb I (JA \<union> JB) (?RA - ?RB)" "A \<union> B = emb I (JA \<union> JB) (?RA \<union> ?RB)"
    using XA A XB B by auto
  show "A - B \<in> ?G" "A \<union> B \<in> ?G"
    unfolding * using XA XB by (safe intro!: generatorI') auto
qed

lemma (in product_prob_space) sets_PiM_generator:
  "sets (PiM I M) = sigma_sets (\<Pi>\<^isub>E i\<in>I. space (M i)) generator"
proof cases
  assume "I = {}" then show ?thesis
    unfolding generator_def
    by (auto simp: sets_PiM_empty sigma_sets_empty_eq cong: conj_cong)
next
  assume "I \<noteq> {}"
  show ?thesis
  proof
    show "sets (Pi\<^isub>M I M) \<subseteq> sigma_sets (\<Pi>\<^isub>E i\<in>I. space (M i)) generator"
      unfolding sets_PiM
    proof (safe intro!: sigma_sets_subseteq)
      fix A assume "A \<in> prod_algebra I M" with `I \<noteq> {}` show "A \<in> generator"
        by (auto intro!: generatorI' sets_PiM_I_finite elim!: prod_algebraE)
    qed
  qed (auto simp: generator_def space_PiM[symmetric] intro!: sigma_sets_subset)
qed


lemma (in product_prob_space) generatorI:
  "J \<noteq> {} \<Longrightarrow> finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> X \<in> sets (Pi\<^isub>M J M) \<Longrightarrow> A = emb I J X \<Longrightarrow> A \<in> generator"
  unfolding generator_def by auto

definition (in product_prob_space)
  "\<mu>G A =
    (THE x. \<forall>J. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow> J \<subseteq> I \<longrightarrow> (\<forall>X\<in>sets (Pi\<^isub>M J M). A = emb I J X \<longrightarrow> x = emeasure (Pi\<^isub>M J M) X))"

lemma (in product_prob_space) \<mu>G_spec:
  assumes J: "J \<noteq> {}" "finite J" "J \<subseteq> I" "A = emb I J X" "X \<in> sets (Pi\<^isub>M J M)"
  shows "\<mu>G A = emeasure (Pi\<^isub>M J M) X"
  unfolding \<mu>G_def
proof (intro the_equality allI impI ballI)
  fix K Y assume K: "K \<noteq> {}" "finite K" "K \<subseteq> I" "A = emb I K Y" "Y \<in> sets (Pi\<^isub>M K M)"
  have "emeasure (Pi\<^isub>M K M) Y = emeasure (Pi\<^isub>M (K \<union> J) M) (emb (K \<union> J) K Y)"
    using K J by simp
  also have "emb (K \<union> J) K Y = emb (K \<union> J) J X"
    using K J by (simp add: prod_emb_injective[of "K \<union> J" I])
  also have "emeasure (Pi\<^isub>M (K \<union> J) M) (emb (K \<union> J) J X) = emeasure (Pi\<^isub>M J M) X"
    using K J by simp
  finally show "emeasure (Pi\<^isub>M J M) X = emeasure (Pi\<^isub>M K M) Y" ..
qed (insert J, force)

lemma (in product_prob_space) \<mu>G_eq:
  "J \<noteq> {} \<Longrightarrow> finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> X \<in> sets (Pi\<^isub>M J M) \<Longrightarrow> \<mu>G (emb I J X) = emeasure (Pi\<^isub>M J M) X"
  by (intro \<mu>G_spec) auto

lemma (in product_prob_space) generator_Ex:
  assumes *: "A \<in> generator"
  shows "\<exists>J X. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I \<and> X \<in> sets (Pi\<^isub>M J M) \<and> A = emb I J X \<and> \<mu>G A = emeasure (Pi\<^isub>M J M) X"
proof -
  from * obtain J X where J: "J \<noteq> {}" "finite J" "J \<subseteq> I" "A = emb I J X" "X \<in> sets (Pi\<^isub>M J M)"
    unfolding generator_def by auto
  with \<mu>G_spec[OF this] show ?thesis by auto
qed

lemma (in product_prob_space) generatorE:
  assumes A: "A \<in> generator"
  obtains J X where "J \<noteq> {}" "finite J" "J \<subseteq> I" "X \<in> sets (Pi\<^isub>M J M)" "emb I J X = A" "\<mu>G A = emeasure (Pi\<^isub>M J M) X"
proof -
  from generator_Ex[OF A] obtain X J where "J \<noteq> {}" "finite J" "J \<subseteq> I" "X \<in> sets (Pi\<^isub>M J M)" "emb I J X = A"
    "\<mu>G A = emeasure (Pi\<^isub>M J M) X" by auto
  then show thesis by (intro that) auto
qed

lemma (in product_prob_space) merge_sets:
  "J \<inter> K = {} \<Longrightarrow> A \<in> sets (Pi\<^isub>M (J \<union> K) M) \<Longrightarrow> x \<in> space (Pi\<^isub>M J M) \<Longrightarrow> (\<lambda>y. merge J K (x,y)) -` A \<inter> space (Pi\<^isub>M K M) \<in> sets (Pi\<^isub>M K M)"
  by simp

lemma (in product_prob_space) merge_emb:
  assumes "K \<subseteq> I" "J \<subseteq> I" and y: "y \<in> space (Pi\<^isub>M J M)"
  shows "((\<lambda>x. merge J (I - J) (y, x)) -` emb I K X \<inter> space (Pi\<^isub>M I M)) =
    emb I (K - J) ((\<lambda>x. merge J (K - J) (y, x)) -` emb (J \<union> K) K X \<inter> space (Pi\<^isub>M (K - J) M))"
proof -
  have [simp]: "\<And>x J K L. merge J K (y, restrict x L) = merge J (K \<inter> L) (y, x)"
    by (auto simp: restrict_def merge_def)
  have [simp]: "\<And>x J K L. restrict (merge J K (y, x)) L = merge (J \<inter> L) (K \<inter> L) (y, x)"
    by (auto simp: restrict_def merge_def)
  have [simp]: "(I - J) \<inter> K = K - J" using `K \<subseteq> I` `J \<subseteq> I` by auto
  have [simp]: "(K - J) \<inter> (K \<union> J) = K - J" by auto
  have [simp]: "(K - J) \<inter> K = K - J" by auto
  from y `K \<subseteq> I` `J \<subseteq> I` show ?thesis
    by (simp split: split_merge add: prod_emb_def Pi_iff extensional_merge_sub set_eq_iff space_PiM)
       auto
qed

lemma (in product_prob_space) positive_\<mu>G: 
  assumes "I \<noteq> {}"
  shows "positive generator \<mu>G"
proof -
  interpret G!: algebra "\<Pi>\<^isub>E i\<in>I. space (M i)" generator by (rule algebra_generator) fact
  show ?thesis
  proof (intro positive_def[THEN iffD2] conjI ballI)
    from generatorE[OF G.empty_sets] guess J X . note this[simp]
    interpret J: finite_product_sigma_finite M J by default fact
    have "X = {}"
      by (rule prod_emb_injective[of J I]) simp_all
    then show "\<mu>G {} = 0" by simp
  next
    fix A assume "A \<in> generator"
    from generatorE[OF this] guess J X . note this[simp]
    interpret J: finite_product_sigma_finite M J by default fact
    show "0 \<le> \<mu>G A" by (simp add: emeasure_nonneg)
  qed
qed

lemma (in product_prob_space) additive_\<mu>G: 
  assumes "I \<noteq> {}"
  shows "additive generator \<mu>G"
proof -
  interpret G!: algebra "\<Pi>\<^isub>E i\<in>I. space (M i)" generator by (rule algebra_generator) fact
  show ?thesis
  proof (intro additive_def[THEN iffD2] ballI impI)
    fix A assume "A \<in> generator" with generatorE guess J X . note J = this
    fix B assume "B \<in> generator" with generatorE guess K Y . note K = this
    assume "A \<inter> B = {}"
    have JK: "J \<union> K \<noteq> {}" "J \<union> K \<subseteq> I" "finite (J \<union> K)"
      using J K by auto
    interpret JK: finite_product_sigma_finite M "J \<union> K" by default fact
    have JK_disj: "emb (J \<union> K) J X \<inter> emb (J \<union> K) K Y = {}"
      apply (rule prod_emb_injective[of "J \<union> K" I])
      apply (insert `A \<inter> B = {}` JK J K)
      apply (simp_all add: Int prod_emb_Int)
      done
    have AB: "A = emb I (J \<union> K) (emb (J \<union> K) J X)" "B = emb I (J \<union> K) (emb (J \<union> K) K Y)"
      using J K by simp_all
    then have "\<mu>G (A \<union> B) = \<mu>G (emb I (J \<union> K) (emb (J \<union> K) J X \<union> emb (J \<union> K) K Y))"
      by simp
    also have "\<dots> = emeasure (Pi\<^isub>M (J \<union> K) M) (emb (J \<union> K) J X \<union> emb (J \<union> K) K Y)"
      using JK J(1, 4) K(1, 4) by (simp add: \<mu>G_eq Un del: prod_emb_Un)
    also have "\<dots> = \<mu>G A + \<mu>G B"
      using J K JK_disj by (simp add: plus_emeasure[symmetric])
    finally show "\<mu>G (A \<union> B) = \<mu>G A + \<mu>G B" .
  qed
qed

lemma (in product_prob_space) emeasure_PiM_emb_not_empty:
  assumes X: "J \<noteq> {}" "J \<subseteq> I" "finite J" "\<forall>i\<in>J. X i \<in> sets (M i)"
  shows "emeasure (Pi\<^isub>M I M) (emb I J (Pi\<^isub>E J X)) = emeasure (Pi\<^isub>M J M) (Pi\<^isub>E J X)"
proof cases
  assume "finite I" with X show ?thesis by simp
next
  let ?\<Omega> = "\<Pi>\<^isub>E i\<in>I. space (M i)"
  let ?G = generator
  assume "\<not> finite I"
  then have I_not_empty: "I \<noteq> {}" by auto
  interpret G!: algebra ?\<Omega> generator by (rule algebra_generator) fact
  note \<mu>G_mono =
    G.additive_increasing[OF positive_\<mu>G[OF I_not_empty] additive_\<mu>G[OF I_not_empty], THEN increasingD]

  { fix Z J assume J: "J \<noteq> {}" "finite J" "J \<subseteq> I" and Z: "Z \<in> ?G"

    from `infinite I` `finite J` obtain k where k: "k \<in> I" "k \<notin> J"
      by (metis rev_finite_subset subsetI)
    moreover from Z guess K' X' by (rule generatorE)
    moreover def K \<equiv> "insert k K'"
    moreover def X \<equiv> "emb K K' X'"
    ultimately have K: "K \<noteq> {}" "finite K" "K \<subseteq> I" "X \<in> sets (Pi\<^isub>M K M)" "Z = emb I K X"
      "K - J \<noteq> {}" "K - J \<subseteq> I" "\<mu>G Z = emeasure (Pi\<^isub>M K M) X"
      by (auto simp: subset_insertI)

    let ?M = "\<lambda>y. (\<lambda>x. merge J (K - J) (y, x)) -` emb (J \<union> K) K X \<inter> space (Pi\<^isub>M (K - J) M)"
    { fix y assume y: "y \<in> space (Pi\<^isub>M J M)"
      note * = merge_emb[OF `K \<subseteq> I` `J \<subseteq> I` y, of X]
      moreover
      have **: "?M y \<in> sets (Pi\<^isub>M (K - J) M)"
        using J K y by (intro merge_sets) auto
      ultimately
      have ***: "((\<lambda>x. merge J (I - J) (y, x)) -` Z \<inter> space (Pi\<^isub>M I M)) \<in> ?G"
        using J K by (intro generatorI) auto
      have "\<mu>G ((\<lambda>x. merge J (I - J) (y, x)) -` emb I K X \<inter> space (Pi\<^isub>M I M)) = emeasure (Pi\<^isub>M (K - J) M) (?M y)"
        unfolding * using K J by (subst \<mu>G_eq[OF _ _ _ **]) auto
      note * ** *** this }
    note merge_in_G = this

    have "finite (K - J)" using K by auto

    interpret J: finite_product_prob_space M J by default fact+
    interpret KmJ: finite_product_prob_space M "K - J" by default fact+

    have "\<mu>G Z = emeasure (Pi\<^isub>M (J \<union> (K - J)) M) (emb (J \<union> (K - J)) K X)"
      using K J by simp
    also have "\<dots> = (\<integral>\<^isup>+ x. emeasure (Pi\<^isub>M (K - J) M) (?M x) \<partial>Pi\<^isub>M J M)"
      using K J by (subst emeasure_fold_integral) auto
    also have "\<dots> = (\<integral>\<^isup>+ y. \<mu>G ((\<lambda>x. merge J (I - J) (y, x)) -` Z \<inter> space (Pi\<^isub>M I M)) \<partial>Pi\<^isub>M J M)"
      (is "_ = (\<integral>\<^isup>+x. \<mu>G (?MZ x) \<partial>Pi\<^isub>M J M)")
    proof (intro positive_integral_cong)
      fix x assume x: "x \<in> space (Pi\<^isub>M J M)"
      with K merge_in_G(2)[OF this]
      show "emeasure (Pi\<^isub>M (K - J) M) (?M x) = \<mu>G (?MZ x)"
        unfolding `Z = emb I K X` merge_in_G(1)[OF x] by (subst \<mu>G_eq) auto
    qed
    finally have fold: "\<mu>G Z = (\<integral>\<^isup>+x. \<mu>G (?MZ x) \<partial>Pi\<^isub>M J M)" .

    { fix x assume x: "x \<in> space (Pi\<^isub>M J M)"
      then have "\<mu>G (?MZ x) \<le> 1"
        unfolding merge_in_G(4)[OF x] `Z = emb I K X`
        by (intro KmJ.measure_le_1 merge_in_G(2)[OF x]) }
    note le_1 = this

    let ?q = "\<lambda>y. \<mu>G ((\<lambda>x. merge J (I - J) (y,x)) -` Z \<inter> space (Pi\<^isub>M I M))"
    have "?q \<in> borel_measurable (Pi\<^isub>M J M)"
      unfolding `Z = emb I K X` using J K merge_in_G(3)
      by (simp add: merge_in_G  \<mu>G_eq emeasure_fold_measurable cong: measurable_cong)
    note this fold le_1 merge_in_G(3) }
  note fold = this

  have "\<exists>\<mu>. (\<forall>s\<in>?G. \<mu> s = \<mu>G s) \<and> measure_space ?\<Omega> (sigma_sets ?\<Omega> ?G) \<mu>"
  proof (rule G.caratheodory_empty_continuous[OF positive_\<mu>G additive_\<mu>G])
    fix A assume "A \<in> ?G"
    with generatorE guess J X . note JX = this
    interpret JK: finite_product_prob_space M J by default fact+ 
    from JX show "\<mu>G A \<noteq> \<infinity>" by simp
  next
    fix A assume A: "range A \<subseteq> ?G" "decseq A" "(\<Inter>i. A i) = {}"
    then have "decseq (\<lambda>i. \<mu>G (A i))"
      by (auto intro!: \<mu>G_mono simp: decseq_def)
    moreover
    have "(INF i. \<mu>G (A i)) = 0"
    proof (rule ccontr)
      assume "(INF i. \<mu>G (A i)) \<noteq> 0" (is "?a \<noteq> 0")
      moreover have "0 \<le> ?a"
        using A positive_\<mu>G[OF I_not_empty] by (auto intro!: INF_greatest simp: positive_def)
      ultimately have "0 < ?a" by auto

      have "\<forall>n. \<exists>J X. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I \<and> X \<in> sets (Pi\<^isub>M J M) \<and> A n = emb I J X \<and> \<mu>G (A n) = emeasure (Pi\<^isub>M J M) X"
        using A by (intro allI generator_Ex) auto
      then obtain J' X' where J': "\<And>n. J' n \<noteq> {}" "\<And>n. finite (J' n)" "\<And>n. J' n \<subseteq> I" "\<And>n. X' n \<in> sets (Pi\<^isub>M (J' n) M)"
        and A': "\<And>n. A n = emb I (J' n) (X' n)"
        unfolding choice_iff by blast
      moreover def J \<equiv> "\<lambda>n. (\<Union>i\<le>n. J' i)"
      moreover def X \<equiv> "\<lambda>n. emb (J n) (J' n) (X' n)"
      ultimately have J: "\<And>n. J n \<noteq> {}" "\<And>n. finite (J n)" "\<And>n. J n \<subseteq> I" "\<And>n. X n \<in> sets (Pi\<^isub>M (J n) M)"
        by auto
      with A' have A_eq: "\<And>n. A n = emb I (J n) (X n)" "\<And>n. A n \<in> ?G"
        unfolding J_def X_def by (subst prod_emb_trans) (insert A, auto)

      have J_mono: "\<And>n m. n \<le> m \<Longrightarrow> J n \<subseteq> J m"
        unfolding J_def by force

      interpret J: finite_product_prob_space M "J i" for i by default fact+

      have a_le_1: "?a \<le> 1"
        using \<mu>G_spec[of "J 0" "A 0" "X 0"] J A_eq
        by (auto intro!: INF_lower2[of 0] J.measure_le_1)

      let ?M = "\<lambda>K Z y. (\<lambda>x. merge K (I - K) (y, x)) -` Z \<inter> space (Pi\<^isub>M I M)"

      { fix Z k assume Z: "range Z \<subseteq> ?G" "decseq Z" "\<forall>n. ?a / 2^k \<le> \<mu>G (Z n)"
        then have Z_sets: "\<And>n. Z n \<in> ?G" by auto
        fix J' assume J': "J' \<noteq> {}" "finite J'" "J' \<subseteq> I"
        interpret J': finite_product_prob_space M J' by default fact+

        let ?q = "\<lambda>n y. \<mu>G (?M J' (Z n) y)"
        let ?Q = "\<lambda>n. ?q n -` {?a / 2^(k+1) ..} \<inter> space (Pi\<^isub>M J' M)"
        { fix n
          have "?q n \<in> borel_measurable (Pi\<^isub>M J' M)"
            using Z J' by (intro fold(1)) auto
          then have "?Q n \<in> sets (Pi\<^isub>M J' M)"
            by (rule measurable_sets) auto }
        note Q_sets = this

        have "?a / 2^(k+1) \<le> (INF n. emeasure (Pi\<^isub>M J' M) (?Q n))"
        proof (intro INF_greatest)
          fix n
          have "?a / 2^k \<le> \<mu>G (Z n)" using Z by auto
          also have "\<dots> \<le> (\<integral>\<^isup>+ x. indicator (?Q n) x + ?a / 2^(k+1) \<partial>Pi\<^isub>M J' M)"
            unfolding fold(2)[OF J' `Z n \<in> ?G`]
          proof (intro positive_integral_mono)
            fix x assume x: "x \<in> space (Pi\<^isub>M J' M)"
            then have "?q n x \<le> 1 + 0"
              using J' Z fold(3) Z_sets by auto
            also have "\<dots> \<le> 1 + ?a / 2^(k+1)"
              using `0 < ?a` by (intro add_mono) auto
            finally have "?q n x \<le> 1 + ?a / 2^(k+1)" .
            with x show "?q n x \<le> indicator (?Q n) x + ?a / 2^(k+1)"
              by (auto split: split_indicator simp del: power_Suc)
          qed
          also have "\<dots> = emeasure (Pi\<^isub>M J' M) (?Q n) + ?a / 2^(k+1)"
            using `0 \<le> ?a` Q_sets J'.emeasure_space_1
            by (subst positive_integral_add) auto
          finally show "?a / 2^(k+1) \<le> emeasure (Pi\<^isub>M J' M) (?Q n)" using `?a \<le> 1`
            by (cases rule: ereal2_cases[of ?a "emeasure (Pi\<^isub>M J' M) (?Q n)"])
               (auto simp: field_simps)
        qed
        also have "\<dots> = emeasure (Pi\<^isub>M J' M) (\<Inter>n. ?Q n)"
        proof (intro INF_emeasure_decseq)
          show "range ?Q \<subseteq> sets (Pi\<^isub>M J' M)" using Q_sets by auto
          show "decseq ?Q"
            unfolding decseq_def
          proof (safe intro!: vimageI[OF refl])
            fix m n :: nat assume "m \<le> n"
            fix x assume x: "x \<in> space (Pi\<^isub>M J' M)"
            assume "?a / 2^(k+1) \<le> ?q n x"
            also have "?q n x \<le> ?q m x"
            proof (rule \<mu>G_mono)
              from fold(4)[OF J', OF Z_sets x]
              show "?M J' (Z n) x \<in> ?G" "?M J' (Z m) x \<in> ?G" by auto
              show "?M J' (Z n) x \<subseteq> ?M J' (Z m) x"
                using `decseq Z`[THEN decseqD, OF `m \<le> n`] by auto
            qed
            finally show "?a / 2^(k+1) \<le> ?q m x" .
          qed
        qed simp
        finally have "(\<Inter>n. ?Q n) \<noteq> {}"
          using `0 < ?a` `?a \<le> 1` by (cases ?a) (auto simp: divide_le_0_iff power_le_zero_eq)
        then have "\<exists>w\<in>space (Pi\<^isub>M J' M). \<forall>n. ?a / 2 ^ (k + 1) \<le> ?q n w" by auto }
      note Ex_w = this

      let ?q = "\<lambda>k n y. \<mu>G (?M (J k) (A n) y)"

      have "\<forall>n. ?a / 2 ^ 0 \<le> \<mu>G (A n)" by (auto intro: INF_lower)
      from Ex_w[OF A(1,2) this J(1-3), of 0] guess w0 .. note w0 = this

      let ?P =
        "\<lambda>k wk w. w \<in> space (Pi\<^isub>M (J (Suc k)) M) \<and> restrict w (J k) = wk \<and>
          (\<forall>n. ?a / 2 ^ (Suc k + 1) \<le> ?q (Suc k) n w)"
      def w \<equiv> "nat_rec w0 (\<lambda>k wk. Eps (?P k wk))"

      { fix k have w: "w k \<in> space (Pi\<^isub>M (J k) M) \<and>
          (\<forall>n. ?a / 2 ^ (k + 1) \<le> ?q k n (w k)) \<and> (k \<noteq> 0 \<longrightarrow> restrict (w k) (J (k - 1)) = w (k - 1))"
        proof (induct k)
          case 0 with w0 show ?case
            unfolding w_def nat_rec_0 by auto
        next
          case (Suc k)
          then have wk: "w k \<in> space (Pi\<^isub>M (J k) M)" by auto
          have "\<exists>w'. ?P k (w k) w'"
          proof cases
            assume [simp]: "J k = J (Suc k)"
            show ?thesis
            proof (intro exI[of _ "w k"] conjI allI)
              fix n
              have "?a / 2 ^ (Suc k + 1) \<le> ?a / 2 ^ (k + 1)"
                using `0 < ?a` `?a \<le> 1` by (cases ?a) (auto simp: field_simps)
              also have "\<dots> \<le> ?q k n (w k)" using Suc by auto
              finally show "?a / 2 ^ (Suc k + 1) \<le> ?q (Suc k) n (w k)" by simp
            next
              show "w k \<in> space (Pi\<^isub>M (J (Suc k)) M)"
                using Suc by simp
              then show "restrict (w k) (J k) = w k"
                by (simp add: extensional_restrict space_PiM)
            qed
          next
            assume "J k \<noteq> J (Suc k)"
            with J_mono[of k "Suc k"] have "J (Suc k) - J k \<noteq> {}" (is "?D \<noteq> {}") by auto
            have "range (\<lambda>n. ?M (J k) (A n) (w k)) \<subseteq> ?G"
              "decseq (\<lambda>n. ?M (J k) (A n) (w k))"
              "\<forall>n. ?a / 2 ^ (k + 1) \<le> \<mu>G (?M (J k) (A n) (w k))"
              using `decseq A` fold(4)[OF J(1-3) A_eq(2), of "w k" k] Suc
              by (auto simp: decseq_def)
            from Ex_w[OF this `?D \<noteq> {}`] J[of "Suc k"]
            obtain w' where w': "w' \<in> space (Pi\<^isub>M ?D M)"
              "\<forall>n. ?a / 2 ^ (Suc k + 1) \<le> \<mu>G (?M ?D (?M (J k) (A n) (w k)) w')" by auto
            let ?w = "merge (J k) ?D (w k, w')"
            have [simp]: "\<And>x. merge (J k) (I - J k) (w k, merge ?D (I - ?D) (w', x)) =
              merge (J (Suc k)) (I - (J (Suc k))) (?w, x)"
              using J(3)[of "Suc k"] J(3)[of k] J_mono[of k "Suc k"]
              by (auto intro!: ext split: split_merge)
            have *: "\<And>n. ?M ?D (?M (J k) (A n) (w k)) w' = ?M (J (Suc k)) (A n) ?w"
              using w'(1) J(3)[of "Suc k"]
              by (auto simp: space_PiM split: split_merge intro!: extensional_merge_sub) force+
            show ?thesis
              apply (rule exI[of _ ?w])
              using w' J_mono[of k "Suc k"] wk unfolding *
              apply (auto split: split_merge intro!: extensional_merge_sub ext simp: space_PiM)
              apply (force simp: extensional_def)
              done
          qed
          then have "?P k (w k) (w (Suc k))"
            unfolding w_def nat_rec_Suc unfolding w_def[symmetric]
            by (rule someI_ex)
          then show ?case by auto
        qed
        moreover
        then have "w k \<in> space (Pi\<^isub>M (J k) M)" by auto
        moreover
        from w have "?a / 2 ^ (k + 1) \<le> ?q k k (w k)" by auto
        then have "?M (J k) (A k) (w k) \<noteq> {}"
          using positive_\<mu>G[OF I_not_empty, unfolded positive_def] `0 < ?a` `?a \<le> 1`
          by (cases ?a) (auto simp: divide_le_0_iff power_le_zero_eq)
        then obtain x where "x \<in> ?M (J k) (A k) (w k)" by auto
        then have "merge (J k) (I - J k) (w k, x) \<in> A k" by auto
        then have "\<exists>x\<in>A k. restrict x (J k) = w k"
          using `w k \<in> space (Pi\<^isub>M (J k) M)`
          by (intro rev_bexI) (auto intro!: ext simp: extensional_def space_PiM)
        ultimately have "w k \<in> space (Pi\<^isub>M (J k) M)"
          "\<exists>x\<in>A k. restrict x (J k) = w k"
          "k \<noteq> 0 \<Longrightarrow> restrict (w k) (J (k - 1)) = w (k - 1)"
          by auto }
      note w = this

      { fix k l i assume "k \<le> l" "i \<in> J k"
        { fix l have "w k i = w (k + l) i"
          proof (induct l)
            case (Suc l)
            from `i \<in> J k` J_mono[of k "k + l"] have "i \<in> J (k + l)" by auto
            with w(3)[of "k + Suc l"]
            have "w (k + l) i = w (k + Suc l) i"
              by (auto simp: restrict_def fun_eq_iff split: split_if_asm)
            with Suc show ?case by simp
          qed simp }
        from this[of "l - k"] `k \<le> l` have "w l i = w k i" by simp }
      note w_mono = this

      def w' \<equiv> "\<lambda>i. if i \<in> (\<Union>k. J k) then w (LEAST k. i \<in> J k) i else if i \<in> I then (SOME x. x \<in> space (M i)) else undefined"
      { fix i k assume k: "i \<in> J k"
        have "w k i = w (LEAST k. i \<in> J k) i"
          by (intro w_mono Least_le k LeastI[of _ k])
        then have "w' i = w k i"
          unfolding w'_def using k by auto }
      note w'_eq = this
      have w'_simps1: "\<And>i. i \<notin> I \<Longrightarrow> w' i = undefined"
        using J by (auto simp: w'_def)
      have w'_simps2: "\<And>i. i \<notin> (\<Union>k. J k) \<Longrightarrow> i \<in> I \<Longrightarrow> w' i \<in> space (M i)"
        using J by (auto simp: w'_def intro!: someI_ex[OF M.not_empty[unfolded ex_in_conv[symmetric]]])
      { fix i assume "i \<in> I" then have "w' i \<in> space (M i)"
          using w(1) by (cases "i \<in> (\<Union>k. J k)") (force simp: w'_simps2 w'_eq space_PiM)+ }
      note w'_simps[simp] = w'_eq w'_simps1 w'_simps2 this

      have w': "w' \<in> space (Pi\<^isub>M I M)"
        using w(1) by (auto simp add: Pi_iff extensional_def space_PiM)

      { fix n
        have "restrict w' (J n) = w n" using w(1)
          by (auto simp add: fun_eq_iff restrict_def Pi_iff extensional_def space_PiM)
        with w[of n] obtain x where "x \<in> A n" "restrict x (J n) = restrict w' (J n)" by auto
        then have "w' \<in> A n" unfolding A_eq using w' by (auto simp: prod_emb_def space_PiM) }
      then have "w' \<in> (\<Inter>i. A i)" by auto
      with `(\<Inter>i. A i) = {}` show False by auto
    qed
    ultimately show "(\<lambda>i. \<mu>G (A i)) ----> 0"
      using LIMSEQ_ereal_INFI[of "\<lambda>i. \<mu>G (A i)"] by simp
  qed fact+
  then guess \<mu> .. note \<mu> = this
  show ?thesis
  proof (subst emeasure_extend_measure_Pair[OF PiM_def, of I M \<mu> J X])
    from assms show "(J \<noteq> {} \<or> I = {}) \<and> finite J \<and> J \<subseteq> I \<and> X \<in> (\<Pi> j\<in>J. sets (M j))"
      by (simp add: Pi_iff)
  next
    fix J X assume J: "(J \<noteq> {} \<or> I = {}) \<and> finite J \<and> J \<subseteq> I \<and> X \<in> (\<Pi> j\<in>J. sets (M j))"
    then show "emb I J (Pi\<^isub>E J X) \<in> Pow (\<Pi>\<^isub>E i\<in>I. space (M i))"
      by (auto simp: Pi_iff prod_emb_def dest: sets_into_space)
    have "emb I J (Pi\<^isub>E J X) \<in> generator"
      using J `I \<noteq> {}` by (intro generatorI') (auto simp: Pi_iff)
    then have "\<mu> (emb I J (Pi\<^isub>E J X)) = \<mu>G (emb I J (Pi\<^isub>E J X))"
      using \<mu> by simp
    also have "\<dots> = (\<Prod> j\<in>J. if j \<in> J then emeasure (M j) (X j) else emeasure (M j) (space (M j)))"
      using J  `I \<noteq> {}` by (subst \<mu>G_spec[OF _ _ _ refl]) (auto simp: emeasure_PiM Pi_iff)
    also have "\<dots> = (\<Prod>j\<in>J \<union> {i \<in> I. emeasure (M i) (space (M i)) \<noteq> 1}.
      if j \<in> J then emeasure (M j) (X j) else emeasure (M j) (space (M j)))"
      using J `I \<noteq> {}` by (intro setprod_mono_one_right) (auto simp: M.emeasure_space_1)
    finally show "\<mu> (emb I J (Pi\<^isub>E J X)) = \<dots>" .
  next
    let ?F = "\<lambda>j. if j \<in> J then emeasure (M j) (X j) else emeasure (M j) (space (M j))"
    have "(\<Prod>j\<in>J \<union> {i \<in> I. emeasure (M i) (space (M i)) \<noteq> 1}. ?F j) = (\<Prod>j\<in>J. ?F j)"
      using X `I \<noteq> {}` by (intro setprod_mono_one_right) (auto simp: M.emeasure_space_1)
    then show "(\<Prod>j\<in>J \<union> {i \<in> I. emeasure (M i) (space (M i)) \<noteq> 1}. ?F j) =
      emeasure (Pi\<^isub>M J M) (Pi\<^isub>E J X)"
      using X by (auto simp add: emeasure_PiM) 
  next
    show "positive (sets (Pi\<^isub>M I M)) \<mu>" "countably_additive (sets (Pi\<^isub>M I M)) \<mu>"
      using \<mu> unfolding sets_PiM_generator by (auto simp: measure_space_def)
  qed
qed

sublocale product_prob_space \<subseteq> P: prob_space "Pi\<^isub>M I M"
proof
  show "emeasure (Pi\<^isub>M I M) (space (Pi\<^isub>M I M)) = 1"
  proof cases
    assume "I = {}" then show ?thesis by (simp add: space_PiM_empty)
  next
    assume "I \<noteq> {}"
    then obtain i where "i \<in> I" by auto
    moreover then have "emb I {i} (\<Pi>\<^isub>E i\<in>{i}. space (M i)) = (space (Pi\<^isub>M I M))"
      by (auto simp: prod_emb_def space_PiM)
    ultimately show ?thesis
      using emeasure_PiM_emb_not_empty[of "{i}" "\<lambda>i. space (M i)"]
      by (simp add: emeasure_PiM emeasure_space_1)
  qed
qed

lemma (in product_prob_space) emeasure_PiM_emb:
  assumes X: "J \<subseteq> I" "finite J" "\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)"
  shows "emeasure (Pi\<^isub>M I M) (emb I J (Pi\<^isub>E J X)) = (\<Prod> i\<in>J. emeasure (M i) (X i))"
proof cases
  assume "J = {}"
  moreover have "emb I {} {\<lambda>x. undefined} = space (Pi\<^isub>M I M)"
    by (auto simp: space_PiM prod_emb_def)
  ultimately show ?thesis
    by (simp add: space_PiM_empty P.emeasure_space_1)
next
  assume "J \<noteq> {}" with X show ?thesis
    by (subst emeasure_PiM_emb_not_empty) (auto simp: emeasure_PiM)
qed

lemma (in product_prob_space) emeasure_PiM_Collect:
  assumes X: "J \<subseteq> I" "finite J" "\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)"
  shows "emeasure (Pi\<^isub>M I M) {x\<in>space (Pi\<^isub>M I M). \<forall>i\<in>J. x i \<in> X i} = (\<Prod> i\<in>J. emeasure (M i) (X i))"
proof -
  have "{x\<in>space (Pi\<^isub>M I M). \<forall>i\<in>J. x i \<in> X i} = emb I J (Pi\<^isub>E J X)"
    unfolding prod_emb_def using assms by (auto simp: space_PiM Pi_iff)
  with emeasure_PiM_emb[OF assms] show ?thesis by simp
qed

lemma (in product_prob_space) emeasure_PiM_Collect_single:
  assumes X: "i \<in> I" "A \<in> sets (M i)"
  shows "emeasure (Pi\<^isub>M I M) {x\<in>space (Pi\<^isub>M I M). x i \<in> A} = emeasure (M i) A"
  using emeasure_PiM_Collect[of "{i}" "\<lambda>i. A"] assms
  by simp

lemma (in product_prob_space) measure_PiM_emb:
  assumes "J \<subseteq> I" "finite J" "\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)"
  shows "measure (PiM I M) (emb I J (Pi\<^isub>E J X)) = (\<Prod> i\<in>J. measure (M i) (X i))"
  using emeasure_PiM_emb[OF assms]
  unfolding emeasure_eq_measure M.emeasure_eq_measure by (simp add: setprod_ereal)

lemma sets_Collect_single':
  "i \<in> I \<Longrightarrow> {x\<in>space (M i). P x} \<in> sets (M i) \<Longrightarrow> {x\<in>space (PiM I M). P (x i)} \<in> sets (PiM I M)"
  using sets_Collect_single[of i I "{x\<in>space (M i). P x}" M]
  by (simp add: space_PiM Pi_iff cong: conj_cong)

lemma (in finite_product_prob_space) finite_measure_PiM_emb:
  "(\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i)) \<Longrightarrow> measure (PiM I M) (Pi\<^isub>E I A) = (\<Prod>i\<in>I. measure (M i) (A i))"
  using measure_PiM_emb[of I A] finite_index prod_emb_PiE_same_index[OF sets_into_space, of I A M]
  by auto

lemma (in product_prob_space) PiM_component:
  assumes "i \<in> I"
  shows "distr (PiM I M) (M i) (\<lambda>\<omega>. \<omega> i) = M i"
proof (rule measure_eqI[symmetric])
  fix A assume "A \<in> sets (M i)"
  moreover have "((\<lambda>\<omega>. \<omega> i) -` A \<inter> space (PiM I M)) = {x\<in>space (PiM I M). x i \<in> A}"
    by auto
  ultimately show "emeasure (M i) A = emeasure (distr (PiM I M) (M i) (\<lambda>\<omega>. \<omega> i)) A"
    by (auto simp: `i\<in>I` emeasure_distr measurable_component_singleton emeasure_PiM_Collect_single)
qed simp

lemma (in product_prob_space) PiM_eq:
  assumes "I \<noteq> {}"
  assumes "sets M' = sets (PiM I M)"
  assumes eq: "\<And>J F. finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> (\<And>j. j \<in> J \<Longrightarrow> F j \<in> sets (M j)) \<Longrightarrow>
    emeasure M' (prod_emb I M J (\<Pi>\<^isub>E j\<in>J. F j)) = (\<Prod>j\<in>J. emeasure (M j) (F j))"
  shows "M' = (PiM I M)"
proof (rule measure_eqI_generator_eq[symmetric, OF Int_stable_prod_algebra prod_algebra_sets_into_space])
  show "sets (PiM I M) = sigma_sets (\<Pi>\<^isub>E i\<in>I. space (M i)) (prod_algebra I M)"
    by (rule sets_PiM)
  then show "sets M' = sigma_sets (\<Pi>\<^isub>E i\<in>I. space (M i)) (prod_algebra I M)"
    unfolding `sets M' = sets (PiM I M)` by simp

  def i \<equiv> "SOME i. i \<in> I"
  with `I \<noteq> {}` have i: "i \<in> I"
    by (auto intro: someI_ex)

  def A \<equiv> "\<lambda>n::nat. prod_emb I M {i} (\<Pi>\<^isub>E j\<in>{i}. space (M i))"
  then show "range A \<subseteq> prod_algebra I M"
    by (auto intro!: prod_algebraI i)

  have A_eq: "\<And>i. A i = space (PiM I M)"
    by (auto simp: prod_emb_def space_PiM Pi_iff A_def i)
  show "(\<Union>i. A i) = (\<Pi>\<^isub>E i\<in>I. space (M i))"
    unfolding A_eq by (auto simp: space_PiM)
  show "\<And>i. emeasure (PiM I M) (A i) \<noteq> \<infinity>"
    unfolding A_eq P.emeasure_space_1 by simp
next
  fix X assume X: "X \<in> prod_algebra I M"
  then obtain J E where X: "X = prod_emb I M J (PIE j:J. E j)"
    and J: "finite J" "J \<subseteq> I" "\<And>j. j \<in> J \<Longrightarrow> E j \<in> sets (M j)"
    by (force elim!: prod_algebraE)
  from eq[OF J] have "emeasure M' X = (\<Prod>j\<in>J. emeasure (M j) (E j))"
    by (simp add: X)
  also have "\<dots> = emeasure (PiM I M) X"
    unfolding X using J by (intro emeasure_PiM_emb[symmetric]) auto
  finally show "emeasure (PiM I M) X = emeasure M' X" ..
qed

subsection {* Sequence space *}

lemma measurable_nat_case: "(\<lambda>(x, \<omega>). nat_case x \<omega>) \<in> measurable (M \<Otimes>\<^isub>M (\<Pi>\<^isub>M i\<in>UNIV. M)) (\<Pi>\<^isub>M i\<in>UNIV. M)"
proof (rule measurable_PiM_single)
  show "(\<lambda>(x, \<omega>). nat_case x \<omega>) \<in> space (M \<Otimes>\<^isub>M (\<Pi>\<^isub>M i\<in>UNIV. M)) \<rightarrow> (UNIV \<rightarrow>\<^isub>E space M)"
    by (auto simp: space_pair_measure space_PiM Pi_iff split: nat.split)
  fix i :: nat and A assume A: "A \<in> sets M"
  then have *: "{\<omega> \<in> space (M \<Otimes>\<^isub>M (\<Pi>\<^isub>M i\<in>UNIV. M)). prod_case nat_case \<omega> i \<in> A} =
    (case i of 0 \<Rightarrow> A \<times> space (\<Pi>\<^isub>M i\<in>UNIV. M) | Suc n \<Rightarrow> space M \<times> {\<omega>\<in>space (\<Pi>\<^isub>M i\<in>UNIV. M). \<omega> n \<in> A})"
    by (auto simp: space_PiM space_pair_measure split: nat.split dest: sets_into_space)
  show "{\<omega> \<in> space (M \<Otimes>\<^isub>M (\<Pi>\<^isub>M i\<in>UNIV. M)). prod_case nat_case \<omega> i \<in> A} \<in> sets (M \<Otimes>\<^isub>M (\<Pi>\<^isub>M i\<in>UNIV. M))"
    unfolding * by (auto simp: A split: nat.split intro!: sets_Collect_single)
qed

lemma measurable_nat_case':
  assumes f: "f \<in> measurable N M" and g: "g \<in> measurable N (\<Pi>\<^isub>M i\<in>UNIV. M)"
  shows "(\<lambda>x. nat_case (f x) (g x)) \<in> measurable N (\<Pi>\<^isub>M i\<in>UNIV. M)"
  using measurable_compose[OF measurable_Pair[OF f g] measurable_nat_case] by simp

definition comb_seq :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "comb_seq i \<omega> \<omega>' j = (if j < i then \<omega> j else \<omega>' (j - i))"

lemma split_comb_seq: "P (comb_seq i \<omega> \<omega>' j) \<longleftrightarrow> (j < i \<longrightarrow> P (\<omega> j)) \<and> (\<forall>k. j = i + k \<longrightarrow> P (\<omega>' k))"
  by (auto simp: comb_seq_def not_less)

lemma split_comb_seq_asm: "P (comb_seq i \<omega> \<omega>' j) \<longleftrightarrow> \<not> ((j < i \<and> \<not> P (\<omega> j)) \<or> (\<exists>k. j = i + k \<and> \<not> P (\<omega>' k)))"
  by (auto simp: comb_seq_def)

lemma measurable_comb_seq: "(\<lambda>(\<omega>, \<omega>'). comb_seq i \<omega> \<omega>') \<in> measurable ((\<Pi>\<^isub>M i\<in>UNIV. M) \<Otimes>\<^isub>M (\<Pi>\<^isub>M i\<in>UNIV. M)) (\<Pi>\<^isub>M i\<in>UNIV. M)"
proof (rule measurable_PiM_single)
  show "(\<lambda>(\<omega>, \<omega>'). comb_seq i \<omega> \<omega>') \<in> space ((\<Pi>\<^isub>M i\<in>UNIV. M) \<Otimes>\<^isub>M (\<Pi>\<^isub>M i\<in>UNIV. M)) \<rightarrow> (UNIV \<rightarrow>\<^isub>E space M)"
    by (auto simp: space_pair_measure space_PiM Pi_iff split: split_comb_seq)
  fix j :: nat and A assume A: "A \<in> sets M"
  then have *: "{\<omega> \<in> space ((\<Pi>\<^isub>M i\<in>UNIV. M) \<Otimes>\<^isub>M (\<Pi>\<^isub>M i\<in>UNIV. M)). prod_case (comb_seq i) \<omega> j \<in> A} =
    (if j < i then {\<omega> \<in> space (\<Pi>\<^isub>M i\<in>UNIV. M). \<omega> j \<in> A} \<times> space (\<Pi>\<^isub>M i\<in>UNIV. M)
              else space (\<Pi>\<^isub>M i\<in>UNIV. M) \<times> {\<omega> \<in> space (\<Pi>\<^isub>M i\<in>UNIV. M). \<omega> (j - i) \<in> A})"
    by (auto simp: space_PiM space_pair_measure comb_seq_def dest: sets_into_space)
  show "{\<omega> \<in> space ((\<Pi>\<^isub>M i\<in>UNIV. M) \<Otimes>\<^isub>M (\<Pi>\<^isub>M i\<in>UNIV. M)). prod_case (comb_seq i) \<omega> j \<in> A} \<in> sets ((\<Pi>\<^isub>M i\<in>UNIV. M) \<Otimes>\<^isub>M (\<Pi>\<^isub>M i\<in>UNIV. M))"
    unfolding * by (auto simp: A intro!: sets_Collect_single)
qed

lemma measurable_comb_seq':
  assumes f: "f \<in> measurable N (\<Pi>\<^isub>M i\<in>UNIV. M)" and g: "g \<in> measurable N (\<Pi>\<^isub>M i\<in>UNIV. M)"
  shows "(\<lambda>x. comb_seq i (f x) (g x)) \<in> measurable N (\<Pi>\<^isub>M i\<in>UNIV. M)"
  using measurable_compose[OF measurable_Pair[OF f g] measurable_comb_seq] by simp

locale sequence_space = product_prob_space "\<lambda>i. M" "UNIV :: nat set" for M
begin

abbreviation "S \<equiv> \<Pi>\<^isub>M i\<in>UNIV::nat set. M"

lemma infprod_in_sets[intro]:
  fixes E :: "nat \<Rightarrow> 'a set" assumes E: "\<And>i. E i \<in> sets M"
  shows "Pi UNIV E \<in> sets S"
proof -
  have "Pi UNIV E = (\<Inter>i. emb UNIV {..i} (\<Pi>\<^isub>E j\<in>{..i}. E j))"
    using E E[THEN sets_into_space]
    by (auto simp: prod_emb_def Pi_iff extensional_def) blast
  with E show ?thesis by auto
qed

lemma measure_PiM_countable:
  fixes E :: "nat \<Rightarrow> 'a set" assumes E: "\<And>i. E i \<in> sets M"
  shows "(\<lambda>n. \<Prod>i\<le>n. measure M (E i)) ----> measure S (Pi UNIV E)"
proof -
  let ?E = "\<lambda>n. emb UNIV {..n} (Pi\<^isub>E {.. n} E)"
  have "\<And>n. (\<Prod>i\<le>n. measure M (E i)) = measure S (?E n)"
    using E by (simp add: measure_PiM_emb)
  moreover have "Pi UNIV E = (\<Inter>n. ?E n)"
    using E E[THEN sets_into_space]
    by (auto simp: prod_emb_def extensional_def Pi_iff) blast
  moreover have "range ?E \<subseteq> sets S"
    using E by auto
  moreover have "decseq ?E"
    by (auto simp: prod_emb_def Pi_iff decseq_def)
  ultimately show ?thesis
    by (simp add: finite_Lim_measure_decseq)
qed

lemma nat_eq_diff_eq: 
  fixes a b c :: nat
  shows "c \<le> b \<Longrightarrow> a = b - c \<longleftrightarrow> a + c = b"
  by auto

lemma PiM_comb_seq:
  "distr (S \<Otimes>\<^isub>M S) S (\<lambda>(\<omega>, \<omega>'). comb_seq i \<omega> \<omega>') = S" (is "?D = _")
proof (rule PiM_eq)
  let ?I = "UNIV::nat set" and ?M = "\<lambda>n. M"
  let "distr _ _ ?f" = "?D"

  fix J E assume J: "finite J" "J \<subseteq> ?I" "\<And>j. j \<in> J \<Longrightarrow> E j \<in> sets M"
  let ?X = "prod_emb ?I ?M J (\<Pi>\<^isub>E j\<in>J. E j)"
  have "\<And>j x. j \<in> J \<Longrightarrow> x \<in> E j \<Longrightarrow> x \<in> space M"
    using J(3)[THEN sets_into_space] by (auto simp: space_PiM Pi_iff subset_eq)
  with J have "?f -` ?X \<inter> space (S \<Otimes>\<^isub>M S) =
    (prod_emb ?I ?M (J \<inter> {..<i}) (PIE j:J \<inter> {..<i}. E j)) \<times>
    (prod_emb ?I ?M ((op + i) -` J) (PIE j:(op + i) -` J. E (i + j)))" (is "_ = ?E \<times> ?F")
   by (auto simp: space_pair_measure space_PiM prod_emb_def all_conj_distrib Pi_iff
               split: split_comb_seq split_comb_seq_asm)
  then have "emeasure ?D ?X = emeasure (S \<Otimes>\<^isub>M S) (?E \<times> ?F)"
    by (subst emeasure_distr[OF measurable_comb_seq])
       (auto intro!: sets_PiM_I simp: split_beta' J)
  also have "\<dots> = emeasure S ?E * emeasure S ?F"
    using J by (intro P.emeasure_pair_measure_Times)  (auto intro!: sets_PiM_I finite_vimageI simp: inj_on_def)
  also have "emeasure S ?F = (\<Prod>j\<in>(op + i) -` J. emeasure M (E (i + j)))"
    using J by (intro emeasure_PiM_emb) (simp_all add: finite_vimageI inj_on_def)
  also have "\<dots> = (\<Prod>j\<in>J - (J \<inter> {..<i}). emeasure M (E j))"
    by (rule strong_setprod_reindex_cong[where f="\<lambda>x. x - i"])
       (auto simp: image_iff Bex_def not_less nat_eq_diff_eq ac_simps cong: conj_cong intro!: inj_onI)
  also have "emeasure S ?E = (\<Prod>j\<in>J \<inter> {..<i}. emeasure M (E j))"
    using J by (intro emeasure_PiM_emb) simp_all
  also have "(\<Prod>j\<in>J \<inter> {..<i}. emeasure M (E j)) * (\<Prod>j\<in>J - (J \<inter> {..<i}). emeasure M (E j)) = (\<Prod>j\<in>J. emeasure M (E j))"
    by (subst mult_commute) (auto simp: J setprod_subset_diff[symmetric])
  finally show "emeasure ?D ?X = (\<Prod>j\<in>J. emeasure M (E j))" .
qed simp_all

lemma PiM_iter:
  "distr (M \<Otimes>\<^isub>M S) S (\<lambda>(s, \<omega>). nat_case s \<omega>) = S" (is "?D = _")
proof (rule PiM_eq)
  let ?I = "UNIV::nat set" and ?M = "\<lambda>n. M"
  let "distr _ _ ?f" = "?D"

  fix J E assume J: "finite J" "J \<subseteq> ?I" "\<And>j. j \<in> J \<Longrightarrow> E j \<in> sets M"
  let ?X = "prod_emb ?I ?M J (PIE j:J. E j)"
  have "\<And>j x. j \<in> J \<Longrightarrow> x \<in> E j \<Longrightarrow> x \<in> space M"
    using J(3)[THEN sets_into_space] by (auto simp: space_PiM Pi_iff subset_eq)
  with J have "?f -` ?X \<inter> space (M \<Otimes>\<^isub>M S) = (if 0 \<in> J then E 0 else space M) \<times>
    (prod_emb ?I ?M (Suc -` J) (PIE j:Suc -` J. E (Suc j)))" (is "_ = ?E \<times> ?F")
   by (auto simp: space_pair_measure space_PiM Pi_iff prod_emb_def all_conj_distrib
      split: nat.split nat.split_asm)
  then have "emeasure ?D ?X = emeasure (M \<Otimes>\<^isub>M S) (?E \<times> ?F)"
    by (subst emeasure_distr[OF measurable_nat_case])
       (auto intro!: sets_PiM_I simp: split_beta' J)
  also have "\<dots> = emeasure M ?E * emeasure S ?F"
    using J by (intro P.emeasure_pair_measure_Times) (auto intro!: sets_PiM_I finite_vimageI)
  also have "emeasure S ?F = (\<Prod>j\<in>Suc -` J. emeasure M (E (Suc j)))"
    using J by (intro emeasure_PiM_emb) (simp_all add: finite_vimageI)
  also have "\<dots> = (\<Prod>j\<in>J - {0}. emeasure M (E j))"
    by (rule strong_setprod_reindex_cong[where f="\<lambda>x. x - 1"])
       (auto simp: image_iff Bex_def not_less nat_eq_diff_eq ac_simps cong: conj_cong intro!: inj_onI)
  also have "emeasure M ?E * (\<Prod>j\<in>J - {0}. emeasure M (E j)) = (\<Prod>j\<in>J. emeasure M (E j))"
    by (auto simp: M.emeasure_space_1 setprod.remove J)
  finally show "emeasure ?D ?X = (\<Prod>j\<in>J. emeasure M (E j))" .
qed simp_all

end

end