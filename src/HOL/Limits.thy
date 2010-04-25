(*  Title       : Limits.thy
    Author      : Brian Huffman
*)

header {* Filters and Limits *}

theory Limits
imports RealVector RComplete
begin

subsection {* Nets *}

text {*
  A net is now defined simply as a filter.
  The definition also allows non-proper filters.
*}

locale is_filter =
  fixes net :: "('a \<Rightarrow> bool) \<Rightarrow> bool"
  assumes True: "net (\<lambda>x. True)"
  assumes conj: "net (\<lambda>x. P x) \<Longrightarrow> net (\<lambda>x. Q x) \<Longrightarrow> net (\<lambda>x. P x \<and> Q x)"
  assumes mono: "\<forall>x. P x \<longrightarrow> Q x \<Longrightarrow> net (\<lambda>x. P x) \<Longrightarrow> net (\<lambda>x. Q x)"

typedef (open) 'a net =
  "{net :: ('a \<Rightarrow> bool) \<Rightarrow> bool. is_filter net}"
proof
  show "(\<lambda>x. True) \<in> ?net" by (auto intro: is_filter.intro)
qed

lemma is_filter_Rep_net: "is_filter (Rep_net net)"
using Rep_net [of net] by simp

lemma Abs_net_inverse':
  assumes "is_filter net" shows "Rep_net (Abs_net net) = net"
using assms by (simp add: Abs_net_inverse)


subsection {* Eventually *}

definition
  eventually :: "('a \<Rightarrow> bool) \<Rightarrow> 'a net \<Rightarrow> bool" where
  [code del]: "eventually P net \<longleftrightarrow> Rep_net net P"

lemma eventually_Abs_net:
  assumes "is_filter net" shows "eventually P (Abs_net net) = net P"
unfolding eventually_def using assms by (simp add: Abs_net_inverse)

lemma eventually_True [simp]: "eventually (\<lambda>x. True) net"
unfolding eventually_def
by (rule is_filter.True [OF is_filter_Rep_net])

lemma eventually_mono:
  "(\<forall>x. P x \<longrightarrow> Q x) \<Longrightarrow> eventually P net \<Longrightarrow> eventually Q net"
unfolding eventually_def
by (rule is_filter.mono [OF is_filter_Rep_net])

lemma eventually_conj:
  assumes P: "eventually (\<lambda>x. P x) net"
  assumes Q: "eventually (\<lambda>x. Q x) net"
  shows "eventually (\<lambda>x. P x \<and> Q x) net"
using assms unfolding eventually_def
by (rule is_filter.conj [OF is_filter_Rep_net])

lemma eventually_mp:
  assumes "eventually (\<lambda>x. P x \<longrightarrow> Q x) net"
  assumes "eventually (\<lambda>x. P x) net"
  shows "eventually (\<lambda>x. Q x) net"
proof (rule eventually_mono)
  show "\<forall>x. (P x \<longrightarrow> Q x) \<and> P x \<longrightarrow> Q x" by simp
  show "eventually (\<lambda>x. (P x \<longrightarrow> Q x) \<and> P x) net"
    using assms by (rule eventually_conj)
qed

lemma eventually_rev_mp:
  assumes "eventually (\<lambda>x. P x) net"
  assumes "eventually (\<lambda>x. P x \<longrightarrow> Q x) net"
  shows "eventually (\<lambda>x. Q x) net"
using assms(2) assms(1) by (rule eventually_mp)

lemma eventually_conj_iff:
  "eventually (\<lambda>x. P x \<and> Q x) net \<longleftrightarrow> eventually P net \<and> eventually Q net"
by (auto intro: eventually_conj elim: eventually_rev_mp)

lemma eventually_elim1:
  assumes "eventually (\<lambda>i. P i) net"
  assumes "\<And>i. P i \<Longrightarrow> Q i"
  shows "eventually (\<lambda>i. Q i) net"
using assms by (auto elim!: eventually_rev_mp)

lemma eventually_elim2:
  assumes "eventually (\<lambda>i. P i) net"
  assumes "eventually (\<lambda>i. Q i) net"
  assumes "\<And>i. P i \<Longrightarrow> Q i \<Longrightarrow> R i"
  shows "eventually (\<lambda>i. R i) net"
using assms by (auto elim!: eventually_rev_mp)


subsection {* Standard Nets *}

definition
  sequentially :: "nat net"
where [code del]:
  "sequentially = Abs_net (\<lambda>P. \<exists>k. \<forall>n\<ge>k. P n)"

definition
  within :: "'a net \<Rightarrow> 'a set \<Rightarrow> 'a net" (infixr "within" 70)
where [code del]:
  "net within S = Abs_net (\<lambda>P. eventually (\<lambda>x. x \<in> S \<longrightarrow> P x) net)"

definition
  at :: "'a::topological_space \<Rightarrow> 'a net"
where [code del]:
  "at a = Abs_net (\<lambda>P. \<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. x \<noteq> a \<longrightarrow> P x))"

lemma eventually_sequentially:
  "eventually P sequentially \<longleftrightarrow> (\<exists>N. \<forall>n\<ge>N. P n)"
unfolding sequentially_def
proof (rule eventually_Abs_net, rule is_filter.intro)
  fix P Q :: "nat \<Rightarrow> bool"
  assume "\<exists>i. \<forall>n\<ge>i. P n" and "\<exists>j. \<forall>n\<ge>j. Q n"
  then obtain i j where "\<forall>n\<ge>i. P n" and "\<forall>n\<ge>j. Q n" by auto
  then have "\<forall>n\<ge>max i j. P n \<and> Q n" by simp
  then show "\<exists>k. \<forall>n\<ge>k. P n \<and> Q n" ..
qed auto

lemma eventually_within:
  "eventually P (net within S) = eventually (\<lambda>x. x \<in> S \<longrightarrow> P x) net"
unfolding within_def
by (rule eventually_Abs_net, rule is_filter.intro)
   (auto elim!: eventually_rev_mp)

lemma eventually_at_topological:
  "eventually P (at a) \<longleftrightarrow> (\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. x \<noteq> a \<longrightarrow> P x))"
unfolding at_def
proof (rule eventually_Abs_net, rule is_filter.intro)
  have "open UNIV \<and> a \<in> UNIV \<and> (\<forall>x\<in>UNIV. x \<noteq> a \<longrightarrow> True)" by simp
  thus "\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. x \<noteq> a \<longrightarrow> True)" by - rule
next
  fix P Q
  assume "\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. x \<noteq> a \<longrightarrow> P x)"
     and "\<exists>T. open T \<and> a \<in> T \<and> (\<forall>x\<in>T. x \<noteq> a \<longrightarrow> Q x)"
  then obtain S T where
    "open S \<and> a \<in> S \<and> (\<forall>x\<in>S. x \<noteq> a \<longrightarrow> P x)"
    "open T \<and> a \<in> T \<and> (\<forall>x\<in>T. x \<noteq> a \<longrightarrow> Q x)" by auto
  hence "open (S \<inter> T) \<and> a \<in> S \<inter> T \<and> (\<forall>x\<in>(S \<inter> T). x \<noteq> a \<longrightarrow> P x \<and> Q x)"
    by (simp add: open_Int)
  thus "\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. x \<noteq> a \<longrightarrow> P x \<and> Q x)" by - rule
qed auto

lemma eventually_at:
  fixes a :: "'a::metric_space"
  shows "eventually P (at a) \<longleftrightarrow> (\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> P x)"
unfolding eventually_at_topological open_dist
apply safe
apply fast
apply (rule_tac x="{x. dist x a < d}" in exI, simp)
apply clarsimp
apply (rule_tac x="d - dist x a" in exI, clarsimp)
apply (simp only: less_diff_eq)
apply (erule le_less_trans [OF dist_triangle])
done


subsection {* Boundedness *}

definition
  Bfun :: "('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a net \<Rightarrow> bool" where
  [code del]: "Bfun f net = (\<exists>K>0. eventually (\<lambda>x. norm (f x) \<le> K) net)"

lemma BfunI:
  assumes K: "eventually (\<lambda>x. norm (f x) \<le> K) net" shows "Bfun f net"
unfolding Bfun_def
proof (intro exI conjI allI)
  show "0 < max K 1" by simp
next
  show "eventually (\<lambda>x. norm (f x) \<le> max K 1) net"
    using K by (rule eventually_elim1, simp)
qed

lemma BfunE:
  assumes "Bfun f net"
  obtains B where "0 < B" and "eventually (\<lambda>x. norm (f x) \<le> B) net"
using assms unfolding Bfun_def by fast


subsection {* Convergence to Zero *}

definition
  Zfun :: "('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a net \<Rightarrow> bool" where
  [code del]: "Zfun f net = (\<forall>r>0. eventually (\<lambda>x. norm (f x) < r) net)"

lemma ZfunI:
  "(\<And>r. 0 < r \<Longrightarrow> eventually (\<lambda>x. norm (f x) < r) net) \<Longrightarrow> Zfun f net"
unfolding Zfun_def by simp

lemma ZfunD:
  "\<lbrakk>Zfun f net; 0 < r\<rbrakk> \<Longrightarrow> eventually (\<lambda>x. norm (f x) < r) net"
unfolding Zfun_def by simp

lemma Zfun_ssubst:
  "eventually (\<lambda>x. f x = g x) net \<Longrightarrow> Zfun g net \<Longrightarrow> Zfun f net"
unfolding Zfun_def by (auto elim!: eventually_rev_mp)

lemma Zfun_zero: "Zfun (\<lambda>x. 0) net"
unfolding Zfun_def by simp

lemma Zfun_norm_iff: "Zfun (\<lambda>x. norm (f x)) net = Zfun (\<lambda>x. f x) net"
unfolding Zfun_def by simp

lemma Zfun_imp_Zfun:
  assumes f: "Zfun f net"
  assumes g: "eventually (\<lambda>x. norm (g x) \<le> norm (f x) * K) net"
  shows "Zfun (\<lambda>x. g x) net"
proof (cases)
  assume K: "0 < K"
  show ?thesis
  proof (rule ZfunI)
    fix r::real assume "0 < r"
    hence "0 < r / K"
      using K by (rule divide_pos_pos)
    then have "eventually (\<lambda>x. norm (f x) < r / K) net"
      using ZfunD [OF f] by fast
    with g show "eventually (\<lambda>x. norm (g x) < r) net"
    proof (rule eventually_elim2)
      fix x
      assume *: "norm (g x) \<le> norm (f x) * K"
      assume "norm (f x) < r / K"
      hence "norm (f x) * K < r"
        by (simp add: pos_less_divide_eq K)
      thus "norm (g x) < r"
        by (simp add: order_le_less_trans [OF *])
    qed
  qed
next
  assume "\<not> 0 < K"
  hence K: "K \<le> 0" by (simp only: not_less)
  show ?thesis
  proof (rule ZfunI)
    fix r :: real
    assume "0 < r"
    from g show "eventually (\<lambda>x. norm (g x) < r) net"
    proof (rule eventually_elim1)
      fix x
      assume "norm (g x) \<le> norm (f x) * K"
      also have "\<dots> \<le> norm (f x) * 0"
        using K norm_ge_zero by (rule mult_left_mono)
      finally show "norm (g x) < r"
        using `0 < r` by simp
    qed
  qed
qed

lemma Zfun_le: "\<lbrakk>Zfun g net; \<forall>x. norm (f x) \<le> norm (g x)\<rbrakk> \<Longrightarrow> Zfun f net"
by (erule_tac K="1" in Zfun_imp_Zfun, simp)

lemma Zfun_add:
  assumes f: "Zfun f net" and g: "Zfun g net"
  shows "Zfun (\<lambda>x. f x + g x) net"
proof (rule ZfunI)
  fix r::real assume "0 < r"
  hence r: "0 < r / 2" by simp
  have "eventually (\<lambda>x. norm (f x) < r/2) net"
    using f r by (rule ZfunD)
  moreover
  have "eventually (\<lambda>x. norm (g x) < r/2) net"
    using g r by (rule ZfunD)
  ultimately
  show "eventually (\<lambda>x. norm (f x + g x) < r) net"
  proof (rule eventually_elim2)
    fix x
    assume *: "norm (f x) < r/2" "norm (g x) < r/2"
    have "norm (f x + g x) \<le> norm (f x) + norm (g x)"
      by (rule norm_triangle_ineq)
    also have "\<dots> < r/2 + r/2"
      using * by (rule add_strict_mono)
    finally show "norm (f x + g x) < r"
      by simp
  qed
qed

lemma Zfun_minus: "Zfun f net \<Longrightarrow> Zfun (\<lambda>x. - f x) net"
unfolding Zfun_def by simp

lemma Zfun_diff: "\<lbrakk>Zfun f net; Zfun g net\<rbrakk> \<Longrightarrow> Zfun (\<lambda>x. f x - g x) net"
by (simp only: diff_minus Zfun_add Zfun_minus)

lemma (in bounded_linear) Zfun:
  assumes g: "Zfun g net"
  shows "Zfun (\<lambda>x. f (g x)) net"
proof -
  obtain K where "\<And>x. norm (f x) \<le> norm x * K"
    using bounded by fast
  then have "eventually (\<lambda>x. norm (f (g x)) \<le> norm (g x) * K) net"
    by simp
  with g show ?thesis
    by (rule Zfun_imp_Zfun)
qed

lemma (in bounded_bilinear) Zfun:
  assumes f: "Zfun f net"
  assumes g: "Zfun g net"
  shows "Zfun (\<lambda>x. f x ** g x) net"
proof (rule ZfunI)
  fix r::real assume r: "0 < r"
  obtain K where K: "0 < K"
    and norm_le: "\<And>x y. norm (x ** y) \<le> norm x * norm y * K"
    using pos_bounded by fast
  from K have K': "0 < inverse K"
    by (rule positive_imp_inverse_positive)
  have "eventually (\<lambda>x. norm (f x) < r) net"
    using f r by (rule ZfunD)
  moreover
  have "eventually (\<lambda>x. norm (g x) < inverse K) net"
    using g K' by (rule ZfunD)
  ultimately
  show "eventually (\<lambda>x. norm (f x ** g x) < r) net"
  proof (rule eventually_elim2)
    fix x
    assume *: "norm (f x) < r" "norm (g x) < inverse K"
    have "norm (f x ** g x) \<le> norm (f x) * norm (g x) * K"
      by (rule norm_le)
    also have "norm (f x) * norm (g x) * K < r * inverse K * K"
      by (intro mult_strict_right_mono mult_strict_mono' norm_ge_zero * K)
    also from K have "r * inverse K * K = r"
      by simp
    finally show "norm (f x ** g x) < r" .
  qed
qed

lemma (in bounded_bilinear) Zfun_left:
  "Zfun f net \<Longrightarrow> Zfun (\<lambda>x. f x ** a) net"
by (rule bounded_linear_left [THEN bounded_linear.Zfun])

lemma (in bounded_bilinear) Zfun_right:
  "Zfun f net \<Longrightarrow> Zfun (\<lambda>x. a ** f x) net"
by (rule bounded_linear_right [THEN bounded_linear.Zfun])

lemmas Zfun_mult = mult.Zfun
lemmas Zfun_mult_right = mult.Zfun_right
lemmas Zfun_mult_left = mult.Zfun_left


subsection {* Limits *}

definition
  tendsto :: "('a \<Rightarrow> 'b::topological_space) \<Rightarrow> 'b \<Rightarrow> 'a net \<Rightarrow> bool"
    (infixr "--->" 55)
where [code del]:
  "(f ---> l) net \<longleftrightarrow> (\<forall>S. open S \<longrightarrow> l \<in> S \<longrightarrow> eventually (\<lambda>x. f x \<in> S) net)"

ML {*
structure Tendsto_Intros = Named_Thms
(
  val name = "tendsto_intros"
  val description = "introduction rules for tendsto"
)
*}

setup Tendsto_Intros.setup

lemma topological_tendstoI:
  "(\<And>S. open S \<Longrightarrow> l \<in> S \<Longrightarrow> eventually (\<lambda>x. f x \<in> S) net)
    \<Longrightarrow> (f ---> l) net"
  unfolding tendsto_def by auto

lemma topological_tendstoD:
  "(f ---> l) net \<Longrightarrow> open S \<Longrightarrow> l \<in> S \<Longrightarrow> eventually (\<lambda>x. f x \<in> S) net"
  unfolding tendsto_def by auto

lemma tendstoI:
  assumes "\<And>e. 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) net"
  shows "(f ---> l) net"
apply (rule topological_tendstoI)
apply (simp add: open_dist)
apply (drule (1) bspec, clarify)
apply (drule assms)
apply (erule eventually_elim1, simp)
done

lemma tendstoD:
  "(f ---> l) net \<Longrightarrow> 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) net"
apply (drule_tac S="{x. dist x l < e}" in topological_tendstoD)
apply (clarsimp simp add: open_dist)
apply (rule_tac x="e - dist x l" in exI, clarsimp)
apply (simp only: less_diff_eq)
apply (erule le_less_trans [OF dist_triangle])
apply simp
apply simp
done

lemma tendsto_iff:
  "(f ---> l) net \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist (f x) l < e) net)"
using tendstoI tendstoD by fast

lemma tendsto_Zfun_iff: "(f ---> a) net = Zfun (\<lambda>x. f x - a) net"
by (simp only: tendsto_iff Zfun_def dist_norm)

lemma tendsto_ident_at [tendsto_intros]: "((\<lambda>x. x) ---> a) (at a)"
unfolding tendsto_def eventually_at_topological by auto

lemma tendsto_ident_at_within [tendsto_intros]:
  "a \<in> S \<Longrightarrow> ((\<lambda>x. x) ---> a) (at a within S)"
unfolding tendsto_def eventually_within eventually_at_topological by auto

lemma tendsto_const [tendsto_intros]: "((\<lambda>x. k) ---> k) net"
by (simp add: tendsto_def)

lemma tendsto_dist [tendsto_intros]:
  assumes f: "(f ---> l) net" and g: "(g ---> m) net"
  shows "((\<lambda>x. dist (f x) (g x)) ---> dist l m) net"
proof (rule tendstoI)
  fix e :: real assume "0 < e"
  hence e2: "0 < e/2" by simp
  from tendstoD [OF f e2] tendstoD [OF g e2]
  show "eventually (\<lambda>x. dist (dist (f x) (g x)) (dist l m) < e) net"
  proof (rule eventually_elim2)
    fix x assume "dist (f x) l < e/2" "dist (g x) m < e/2"
    then show "dist (dist (f x) (g x)) (dist l m) < e"
      unfolding dist_real_def
      using dist_triangle2 [of "f x" "g x" "l"]
      using dist_triangle2 [of "g x" "l" "m"]
      using dist_triangle3 [of "l" "m" "f x"]
      using dist_triangle [of "f x" "m" "g x"]
      by arith
  qed
qed

lemma tendsto_norm [tendsto_intros]:
  "(f ---> a) net \<Longrightarrow> ((\<lambda>x. norm (f x)) ---> norm a) net"
apply (simp add: tendsto_iff dist_norm, safe)
apply (drule_tac x="e" in spec, safe)
apply (erule eventually_elim1)
apply (erule order_le_less_trans [OF norm_triangle_ineq3])
done

lemma add_diff_add:
  fixes a b c d :: "'a::ab_group_add"
  shows "(a + c) - (b + d) = (a - b) + (c - d)"
by simp

lemma minus_diff_minus:
  fixes a b :: "'a::ab_group_add"
  shows "(- a) - (- b) = - (a - b)"
by simp

lemma tendsto_add [tendsto_intros]:
  fixes a b :: "'a::real_normed_vector"
  shows "\<lbrakk>(f ---> a) net; (g ---> b) net\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x + g x) ---> a + b) net"
by (simp only: tendsto_Zfun_iff add_diff_add Zfun_add)

lemma tendsto_minus [tendsto_intros]:
  fixes a :: "'a::real_normed_vector"
  shows "(f ---> a) net \<Longrightarrow> ((\<lambda>x. - f x) ---> - a) net"
by (simp only: tendsto_Zfun_iff minus_diff_minus Zfun_minus)

lemma tendsto_minus_cancel:
  fixes a :: "'a::real_normed_vector"
  shows "((\<lambda>x. - f x) ---> - a) net \<Longrightarrow> (f ---> a) net"
by (drule tendsto_minus, simp)

lemma tendsto_diff [tendsto_intros]:
  fixes a b :: "'a::real_normed_vector"
  shows "\<lbrakk>(f ---> a) net; (g ---> b) net\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x - g x) ---> a - b) net"
by (simp add: diff_minus tendsto_add tendsto_minus)

lemma tendsto_setsum [tendsto_intros]:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::real_normed_vector"
  assumes "\<And>i. i \<in> S \<Longrightarrow> (f i ---> a i) net"
  shows "((\<lambda>x. \<Sum>i\<in>S. f i x) ---> (\<Sum>i\<in>S. a i)) net"
proof (cases "finite S")
  assume "finite S" thus ?thesis using assms
  proof (induct set: finite)
    case empty show ?case
      by (simp add: tendsto_const)
  next
    case (insert i F) thus ?case
      by (simp add: tendsto_add)
  qed
next
  assume "\<not> finite S" thus ?thesis
    by (simp add: tendsto_const)
qed

lemma (in bounded_linear) tendsto [tendsto_intros]:
  "(g ---> a) net \<Longrightarrow> ((\<lambda>x. f (g x)) ---> f a) net"
by (simp only: tendsto_Zfun_iff diff [symmetric] Zfun)

lemma (in bounded_bilinear) tendsto [tendsto_intros]:
  "\<lbrakk>(f ---> a) net; (g ---> b) net\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x ** g x) ---> a ** b) net"
by (simp only: tendsto_Zfun_iff prod_diff_prod
               Zfun_add Zfun Zfun_left Zfun_right)


subsection {* Continuity of Inverse *}

lemma (in bounded_bilinear) Zfun_prod_Bfun:
  assumes f: "Zfun f net"
  assumes g: "Bfun g net"
  shows "Zfun (\<lambda>x. f x ** g x) net"
proof -
  obtain K where K: "0 \<le> K"
    and norm_le: "\<And>x y. norm (x ** y) \<le> norm x * norm y * K"
    using nonneg_bounded by fast
  obtain B where B: "0 < B"
    and norm_g: "eventually (\<lambda>x. norm (g x) \<le> B) net"
    using g by (rule BfunE)
  have "eventually (\<lambda>x. norm (f x ** g x) \<le> norm (f x) * (B * K)) net"
  using norm_g proof (rule eventually_elim1)
    fix x
    assume *: "norm (g x) \<le> B"
    have "norm (f x ** g x) \<le> norm (f x) * norm (g x) * K"
      by (rule norm_le)
    also have "\<dots> \<le> norm (f x) * B * K"
      by (intro mult_mono' order_refl norm_g norm_ge_zero
                mult_nonneg_nonneg K *)
    also have "\<dots> = norm (f x) * (B * K)"
      by (rule mult_assoc)
    finally show "norm (f x ** g x) \<le> norm (f x) * (B * K)" .
  qed
  with f show ?thesis
    by (rule Zfun_imp_Zfun)
qed

lemma (in bounded_bilinear) flip:
  "bounded_bilinear (\<lambda>x y. y ** x)"
apply default
apply (rule add_right)
apply (rule add_left)
apply (rule scaleR_right)
apply (rule scaleR_left)
apply (subst mult_commute)
using bounded by fast

lemma (in bounded_bilinear) Bfun_prod_Zfun:
  assumes f: "Bfun f net"
  assumes g: "Zfun g net"
  shows "Zfun (\<lambda>x. f x ** g x) net"
using flip g f by (rule bounded_bilinear.Zfun_prod_Bfun)

lemma inverse_diff_inverse:
  "\<lbrakk>(a::'a::division_ring) \<noteq> 0; b \<noteq> 0\<rbrakk>
   \<Longrightarrow> inverse a - inverse b = - (inverse a * (a - b) * inverse b)"
by (simp add: algebra_simps)

lemma Bfun_inverse_lemma:
  fixes x :: "'a::real_normed_div_algebra"
  shows "\<lbrakk>r \<le> norm x; 0 < r\<rbrakk> \<Longrightarrow> norm (inverse x) \<le> inverse r"
apply (subst nonzero_norm_inverse, clarsimp)
apply (erule (1) le_imp_inverse_le)
done

lemma Bfun_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  assumes f: "(f ---> a) net"
  assumes a: "a \<noteq> 0"
  shows "Bfun (\<lambda>x. inverse (f x)) net"
proof -
  from a have "0 < norm a" by simp
  hence "\<exists>r>0. r < norm a" by (rule dense)
  then obtain r where r1: "0 < r" and r2: "r < norm a" by fast
  have "eventually (\<lambda>x. dist (f x) a < r) net"
    using tendstoD [OF f r1] by fast
  hence "eventually (\<lambda>x. norm (inverse (f x)) \<le> inverse (norm a - r)) net"
  proof (rule eventually_elim1)
    fix x
    assume "dist (f x) a < r"
    hence 1: "norm (f x - a) < r"
      by (simp add: dist_norm)
    hence 2: "f x \<noteq> 0" using r2 by auto
    hence "norm (inverse (f x)) = inverse (norm (f x))"
      by (rule nonzero_norm_inverse)
    also have "\<dots> \<le> inverse (norm a - r)"
    proof (rule le_imp_inverse_le)
      show "0 < norm a - r" using r2 by simp
    next
      have "norm a - norm (f x) \<le> norm (a - f x)"
        by (rule norm_triangle_ineq2)
      also have "\<dots> = norm (f x - a)"
        by (rule norm_minus_commute)
      also have "\<dots> < r" using 1 .
      finally show "norm a - r \<le> norm (f x)" by simp
    qed
    finally show "norm (inverse (f x)) \<le> inverse (norm a - r)" .
  qed
  thus ?thesis by (rule BfunI)
qed

lemma tendsto_inverse_lemma:
  fixes a :: "'a::real_normed_div_algebra"
  shows "\<lbrakk>(f ---> a) net; a \<noteq> 0; eventually (\<lambda>x. f x \<noteq> 0) net\<rbrakk>
         \<Longrightarrow> ((\<lambda>x. inverse (f x)) ---> inverse a) net"
apply (subst tendsto_Zfun_iff)
apply (rule Zfun_ssubst)
apply (erule eventually_elim1)
apply (erule (1) inverse_diff_inverse)
apply (rule Zfun_minus)
apply (rule Zfun_mult_left)
apply (rule mult.Bfun_prod_Zfun)
apply (erule (1) Bfun_inverse)
apply (simp add: tendsto_Zfun_iff)
done

lemma tendsto_inverse [tendsto_intros]:
  fixes a :: "'a::real_normed_div_algebra"
  assumes f: "(f ---> a) net"
  assumes a: "a \<noteq> 0"
  shows "((\<lambda>x. inverse (f x)) ---> inverse a) net"
proof -
  from a have "0 < norm a" by simp
  with f have "eventually (\<lambda>x. dist (f x) a < norm a) net"
    by (rule tendstoD)
  then have "eventually (\<lambda>x. f x \<noteq> 0) net"
    unfolding dist_norm by (auto elim!: eventually_elim1)
  with f a show ?thesis
    by (rule tendsto_inverse_lemma)
qed

lemma tendsto_divide [tendsto_intros]:
  fixes a b :: "'a::real_normed_field"
  shows "\<lbrakk>(f ---> a) net; (g ---> b) net; b \<noteq> 0\<rbrakk>
    \<Longrightarrow> ((\<lambda>x. f x / g x) ---> a / b) net"
by (simp add: mult.tendsto tendsto_inverse divide_inverse)

end
