(*  Title:      HOL/Conditionally_Complete_Lattices.thy
    Author:     Amine Chaieb and L C Paulson, University of Cambridge
    Author:     Johannes Hölzl, TU München
    Author:     Luke S. Serafin, Carnegie Mellon University
*)

header {* Conditionally-complete Lattices *}

theory Conditionally_Complete_Lattices
imports Main Lubs
begin

lemma (in linorder) Sup_fin_eq_Max: "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Sup_fin X = Max X"
  by (induct X rule: finite_ne_induct) (simp_all add: sup_max)

lemma (in linorder) Inf_fin_eq_Min: "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Inf_fin X = Min X"
  by (induct X rule: finite_ne_induct) (simp_all add: inf_min)

context preorder
begin

definition "bdd_above A \<longleftrightarrow> (\<exists>M. \<forall>x \<in> A. x \<le> M)"
definition "bdd_below A \<longleftrightarrow> (\<exists>m. \<forall>x \<in> A. m \<le> x)"

lemma bdd_aboveI[intro]: "(\<And>x. x \<in> A \<Longrightarrow> x \<le> M) \<Longrightarrow> bdd_above A"
  by (auto simp: bdd_above_def)

lemma bdd_belowI[intro]: "(\<And>x. x \<in> A \<Longrightarrow> m \<le> x) \<Longrightarrow> bdd_below A"
  by (auto simp: bdd_below_def)

lemma bdd_above_empty [simp, intro]: "bdd_above {}"
  unfolding bdd_above_def by auto

lemma bdd_below_empty [simp, intro]: "bdd_below {}"
  unfolding bdd_below_def by auto

lemma bdd_above_mono: "bdd_above B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> bdd_above A"
  by (metis (full_types) bdd_above_def order_class.le_neq_trans psubsetD)

lemma bdd_below_mono: "bdd_below B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> bdd_below A"
  by (metis bdd_below_def order_class.le_neq_trans psubsetD)

lemma bdd_above_Int1 [simp]: "bdd_above A \<Longrightarrow> bdd_above (A \<inter> B)"
  using bdd_above_mono by auto

lemma bdd_above_Int2 [simp]: "bdd_above B \<Longrightarrow> bdd_above (A \<inter> B)"
  using bdd_above_mono by auto

lemma bdd_below_Int1 [simp]: "bdd_below A \<Longrightarrow> bdd_below (A \<inter> B)"
  using bdd_below_mono by auto

lemma bdd_below_Int2 [simp]: "bdd_below B \<Longrightarrow> bdd_below (A \<inter> B)"
  using bdd_below_mono by auto

lemma bdd_above_Ioo [simp, intro]: "bdd_above {a <..< b}"
  by (auto simp add: bdd_above_def intro!: exI[of _ b] less_imp_le)

lemma bdd_above_Ico [simp, intro]: "bdd_above {a ..< b}"
  by (auto simp add: bdd_above_def intro!: exI[of _ b] less_imp_le)

lemma bdd_above_Iio [simp, intro]: "bdd_above {..< b}"
  by (auto simp add: bdd_above_def intro: exI[of _ b] less_imp_le)

lemma bdd_above_Ioc [simp, intro]: "bdd_above {a <.. b}"
  by (auto simp add: bdd_above_def intro: exI[of _ b] less_imp_le)

lemma bdd_above_Icc [simp, intro]: "bdd_above {a .. b}"
  by (auto simp add: bdd_above_def intro: exI[of _ b] less_imp_le)

lemma bdd_above_Iic [simp, intro]: "bdd_above {.. b}"
  by (auto simp add: bdd_above_def intro: exI[of _ b] less_imp_le)

lemma bdd_below_Ioo [simp, intro]: "bdd_below {a <..< b}"
  by (auto simp add: bdd_below_def intro!: exI[of _ a] less_imp_le)

lemma bdd_below_Ioc [simp, intro]: "bdd_below {a <.. b}"
  by (auto simp add: bdd_below_def intro!: exI[of _ a] less_imp_le)

lemma bdd_below_Ioi [simp, intro]: "bdd_below {a <..}"
  by (auto simp add: bdd_below_def intro: exI[of _ a] less_imp_le)

lemma bdd_below_Ico [simp, intro]: "bdd_below {a ..< b}"
  by (auto simp add: bdd_below_def intro: exI[of _ a] less_imp_le)

lemma bdd_below_Icc [simp, intro]: "bdd_below {a .. b}"
  by (auto simp add: bdd_below_def intro: exI[of _ a] less_imp_le)

lemma bdd_below_Ici [simp, intro]: "bdd_below {a ..}"
  by (auto simp add: bdd_below_def intro: exI[of _ a] less_imp_le)

end

lemma (in order_top) bdd_above_top[simp, intro!]: "bdd_above A"
  by (rule bdd_aboveI[of _ top]) simp

lemma (in order_bot) bdd_above_bot[simp, intro!]: "bdd_below A"
  by (rule bdd_belowI[of _ bot]) simp

context lattice
begin

lemma bdd_above_insert [simp]: "bdd_above (insert a A) = bdd_above A"
  by (auto simp: bdd_above_def intro: le_supI2 sup_ge1)

lemma bdd_below_insert [simp]: "bdd_below (insert a A) = bdd_below A"
  by (auto simp: bdd_below_def intro: le_infI2 inf_le1)

lemma bdd_finite [simp]:
  assumes "finite A" shows bdd_above_finite: "bdd_above A" and bdd_below_finite: "bdd_below A"
  using assms by (induct rule: finite_induct, auto)

lemma bdd_above_Un [simp]: "bdd_above (A \<union> B) = (bdd_above A \<and> bdd_above B)"
proof
  assume "bdd_above (A \<union> B)"
  thus "bdd_above A \<and> bdd_above B" unfolding bdd_above_def by auto
next
  assume "bdd_above A \<and> bdd_above B"
  then obtain a b where "\<forall>x\<in>A. x \<le> a" "\<forall>x\<in>B. x \<le> b" unfolding bdd_above_def by auto
  hence "\<forall>x \<in> A \<union> B. x \<le> sup a b" by (auto intro: Un_iff le_supI1 le_supI2)
  thus "bdd_above (A \<union> B)" unfolding bdd_above_def ..
qed

lemma bdd_below_Un [simp]: "bdd_below (A \<union> B) = (bdd_below A \<and> bdd_below B)"
proof
  assume "bdd_below (A \<union> B)"
  thus "bdd_below A \<and> bdd_below B" unfolding bdd_below_def by auto
next
  assume "bdd_below A \<and> bdd_below B"
  then obtain a b where "\<forall>x\<in>A. a \<le> x" "\<forall>x\<in>B. b \<le> x" unfolding bdd_below_def by auto
  hence "\<forall>x \<in> A \<union> B. inf a b \<le> x" by (auto intro: Un_iff le_infI1 le_infI2)
  thus "bdd_below (A \<union> B)" unfolding bdd_below_def ..
qed

lemma bdd_above_sup[simp]: "bdd_above ((\<lambda>x. sup (f x) (g x)) ` A) \<longleftrightarrow> bdd_above (f`A) \<and> bdd_above (g`A)"
  by (auto simp: bdd_above_def intro: le_supI1 le_supI2)

lemma bdd_below_inf[simp]: "bdd_below ((\<lambda>x. inf (f x) (g x)) ` A) \<longleftrightarrow> bdd_below (f`A) \<and> bdd_below (g`A)"
  by (auto simp: bdd_below_def intro: le_infI1 le_infI2)

end


text {*

To avoid name classes with the @{class complete_lattice}-class we prefix @{const Sup} and
@{const Inf} in theorem names with c.

*}

class conditionally_complete_lattice = lattice + Sup + Inf +
  assumes cInf_lower: "x \<in> X \<Longrightarrow> bdd_below X \<Longrightarrow> Inf X \<le> x"
    and cInf_greatest: "X \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf X"
  assumes cSup_upper: "x \<in> X \<Longrightarrow> bdd_above X \<Longrightarrow> x \<le> Sup X"
    and cSup_least: "X \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup X \<le> z"
begin

lemma cSup_upper2: "x \<in> X \<Longrightarrow> y \<le> x \<Longrightarrow> bdd_above X \<Longrightarrow> y \<le> Sup X"
  by (metis cSup_upper order_trans)

lemma cInf_lower2: "x \<in> X \<Longrightarrow> x \<le> y \<Longrightarrow> bdd_below X \<Longrightarrow> Inf X \<le> y"
  by (metis cInf_lower order_trans)

lemma cSup_mono: "B \<noteq> {} \<Longrightarrow> bdd_above A \<Longrightarrow> (\<And>b. b \<in> B \<Longrightarrow> \<exists>a\<in>A. b \<le> a) \<Longrightarrow> Sup B \<le> Sup A"
  by (metis cSup_least cSup_upper2)

lemma cInf_mono: "B \<noteq> {} \<Longrightarrow> bdd_below A \<Longrightarrow> (\<And>b. b \<in> B \<Longrightarrow> \<exists>a\<in>A. a \<le> b) \<Longrightarrow> Inf A \<le> Inf B"
  by (metis cInf_greatest cInf_lower2)

lemma cSup_subset_mono: "A \<noteq> {} \<Longrightarrow> bdd_above B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Sup A \<le> Sup B"
  by (metis cSup_least cSup_upper subsetD)

lemma cInf_superset_mono: "A \<noteq> {} \<Longrightarrow> bdd_below B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Inf B \<le> Inf A"
  by (metis cInf_greatest cInf_lower subsetD)

lemma cSup_eq_maximum: "z \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup X = z"
  by (intro antisym cSup_upper[of z X] cSup_least[of X z]) auto

lemma cInf_eq_minimum: "z \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> z \<le> x) \<Longrightarrow> Inf X = z"
  by (intro antisym cInf_lower[of z X] cInf_greatest[of X z]) auto

lemma cSup_le_iff: "S \<noteq> {} \<Longrightarrow> bdd_above S \<Longrightarrow> Sup S \<le> a \<longleftrightarrow> (\<forall>x\<in>S. x \<le> a)"
  by (metis order_trans cSup_upper cSup_least)

lemma le_cInf_iff: "S \<noteq> {} \<Longrightarrow> bdd_below S \<Longrightarrow> a \<le> Inf S \<longleftrightarrow> (\<forall>x\<in>S. a \<le> x)"
  by (metis order_trans cInf_lower cInf_greatest)

lemma cSup_eq_non_empty:
  assumes 1: "X \<noteq> {}"
  assumes 2: "\<And>x. x \<in> X \<Longrightarrow> x \<le> a"
  assumes 3: "\<And>y. (\<And>x. x \<in> X \<Longrightarrow> x \<le> y) \<Longrightarrow> a \<le> y"
  shows "Sup X = a"
  by (intro 3 1 antisym cSup_least) (auto intro: 2 1 cSup_upper)

lemma cInf_eq_non_empty:
  assumes 1: "X \<noteq> {}"
  assumes 2: "\<And>x. x \<in> X \<Longrightarrow> a \<le> x"
  assumes 3: "\<And>y. (\<And>x. x \<in> X \<Longrightarrow> y \<le> x) \<Longrightarrow> y \<le> a"
  shows "Inf X = a"
  by (intro 3 1 antisym cInf_greatest) (auto intro: 2 1 cInf_lower)

lemma cInf_cSup: "S \<noteq> {} \<Longrightarrow> bdd_below S \<Longrightarrow> Inf S = Sup {x. \<forall>s\<in>S. x \<le> s}"
  by (rule cInf_eq_non_empty) (auto intro!: cSup_upper cSup_least simp: bdd_below_def)

lemma cSup_cInf: "S \<noteq> {} \<Longrightarrow> bdd_above S \<Longrightarrow> Sup S = Inf {x. \<forall>s\<in>S. s \<le> x}"
  by (rule cSup_eq_non_empty) (auto intro!: cInf_lower cInf_greatest simp: bdd_above_def)

lemma cSup_insert: "X \<noteq> {} \<Longrightarrow> bdd_above X \<Longrightarrow> Sup (insert a X) = sup a (Sup X)"
  by (intro cSup_eq_non_empty) (auto intro: le_supI2 cSup_upper cSup_least)

lemma cInf_insert: "X \<noteq> {} \<Longrightarrow> bdd_below X \<Longrightarrow> Inf (insert a X) = inf a (Inf X)"
  by (intro cInf_eq_non_empty) (auto intro: le_infI2 cInf_lower cInf_greatest)

lemma cSup_singleton [simp]: "Sup {x} = x"
  by (intro cSup_eq_maximum) auto

lemma cInf_singleton [simp]: "Inf {x} = x"
  by (intro cInf_eq_minimum) auto

lemma cSup_insert_If:  "bdd_above X \<Longrightarrow> Sup (insert a X) = (if X = {} then a else sup a (Sup X))"
  using cSup_insert[of X] by simp

lemma cInf_insert_If: "bdd_below X \<Longrightarrow> Inf (insert a X) = (if X = {} then a else inf a (Inf X))"
  using cInf_insert[of X] by simp

lemma le_cSup_finite: "finite X \<Longrightarrow> x \<in> X \<Longrightarrow> x \<le> Sup X"
proof (induct X arbitrary: x rule: finite_induct)
  case (insert x X y) then show ?case
    by (cases "X = {}") (auto simp: cSup_insert intro: le_supI2)
qed simp

lemma cInf_le_finite: "finite X \<Longrightarrow> x \<in> X \<Longrightarrow> Inf X \<le> x"
proof (induct X arbitrary: x rule: finite_induct)
  case (insert x X y) then show ?case
    by (cases "X = {}") (auto simp: cInf_insert intro: le_infI2)
qed simp

lemma cSup_eq_Sup_fin: "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Sup X = Sup_fin X"
  by (induct X rule: finite_ne_induct) (simp_all add: cSup_insert)

lemma cInf_eq_Inf_fin: "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Inf X = Inf_fin X"
  by (induct X rule: finite_ne_induct) (simp_all add: cInf_insert)

lemma cSup_atMost[simp]: "Sup {..x} = x"
  by (auto intro!: cSup_eq_maximum)

lemma cSup_greaterThanAtMost[simp]: "y < x \<Longrightarrow> Sup {y<..x} = x"
  by (auto intro!: cSup_eq_maximum)

lemma cSup_atLeastAtMost[simp]: "y \<le> x \<Longrightarrow> Sup {y..x} = x"
  by (auto intro!: cSup_eq_maximum)

lemma cInf_atLeast[simp]: "Inf {x..} = x"
  by (auto intro!: cInf_eq_minimum)

lemma cInf_atLeastLessThan[simp]: "y < x \<Longrightarrow> Inf {y..<x} = y"
  by (auto intro!: cInf_eq_minimum)

lemma cInf_atLeastAtMost[simp]: "y \<le> x \<Longrightarrow> Inf {y..x} = y"
  by (auto intro!: cInf_eq_minimum)

lemma cINF_lower: "bdd_below (f ` A) \<Longrightarrow> x \<in> A \<Longrightarrow> INFI A f \<le> f x"
  unfolding INF_def by (rule cInf_lower) auto

lemma cINF_greatest: "A \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> m \<le> f x) \<Longrightarrow> m \<le> INFI A f"
  unfolding INF_def by (rule cInf_greatest) auto

lemma cSUP_upper: "x \<in> A \<Longrightarrow> bdd_above (f ` A) \<Longrightarrow> f x \<le> SUPR A f"
  unfolding SUP_def by (rule cSup_upper) auto

lemma cSUP_least: "A \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<le> M) \<Longrightarrow> SUPR A f \<le> M"
  unfolding SUP_def by (rule cSup_least) auto

lemma cINF_lower2: "bdd_below (f ` A) \<Longrightarrow> x \<in> A \<Longrightarrow> f x \<le> u \<Longrightarrow> INFI A f \<le> u"
  by (auto intro: cINF_lower assms order_trans)

lemma cSUP_upper2: "bdd_above (f ` A) \<Longrightarrow> x \<in> A \<Longrightarrow> u \<le> f x \<Longrightarrow> u \<le> SUPR A f"
  by (auto intro: cSUP_upper assms order_trans)

lemma cSUP_const: "A \<noteq> {} \<Longrightarrow> (SUP x:A. c) = c"
  by (intro antisym cSUP_least) (auto intro: cSUP_upper)

lemma cINF_const: "A \<noteq> {} \<Longrightarrow> (INF x:A. c) = c"
  by (intro antisym cINF_greatest) (auto intro: cINF_lower)

lemma le_cINF_iff: "A \<noteq> {} \<Longrightarrow> bdd_below (f ` A) \<Longrightarrow> u \<le> INFI A f \<longleftrightarrow> (\<forall>x\<in>A. u \<le> f x)"
  by (metis cINF_greatest cINF_lower assms order_trans)

lemma cSUP_le_iff: "A \<noteq> {} \<Longrightarrow> bdd_above (f ` A) \<Longrightarrow> SUPR A f \<le> u \<longleftrightarrow> (\<forall>x\<in>A. f x \<le> u)"
  by (metis cSUP_least cSUP_upper assms order_trans)

lemma cINF_insert: "A \<noteq> {} \<Longrightarrow> bdd_below (f ` A) \<Longrightarrow> INFI (insert a A) f = inf (f a) (INFI A f)"
  by (metis INF_def cInf_insert assms empty_is_image image_insert)

lemma cSUP_insert: "A \<noteq> {} \<Longrightarrow> bdd_above (f ` A) \<Longrightarrow> SUPR (insert a A) f = sup (f a) (SUPR A f)"
  by (metis SUP_def cSup_insert assms empty_is_image image_insert)

lemma cINF_mono: "B \<noteq> {} \<Longrightarrow> bdd_below (f ` A) \<Longrightarrow> (\<And>m. m \<in> B \<Longrightarrow> \<exists>n\<in>A. f n \<le> g m) \<Longrightarrow> INFI A f \<le> INFI B g"
  unfolding INF_def by (auto intro: cInf_mono)

lemma cSUP_mono: "A \<noteq> {} \<Longrightarrow> bdd_above (g ` B) \<Longrightarrow> (\<And>n. n \<in> A \<Longrightarrow> \<exists>m\<in>B. f n \<le> g m) \<Longrightarrow> SUPR A f \<le> SUPR B g"
  unfolding SUP_def by (auto intro: cSup_mono)

lemma cINF_superset_mono: "A \<noteq> {} \<Longrightarrow> bdd_below (g ` B) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> g x \<le> f x) \<Longrightarrow> INFI B g \<le> INFI A f"
  by (rule cINF_mono) auto

lemma cSUP_subset_mono: "A \<noteq> {} \<Longrightarrow> bdd_above (g ` B) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> f x \<le> g x) \<Longrightarrow> SUPR A f \<le> SUPR B g"
  by (rule cSUP_mono) auto

lemma less_eq_cInf_inter: "bdd_below A \<Longrightarrow> bdd_below B \<Longrightarrow> A \<inter> B \<noteq> {} \<Longrightarrow> inf (Inf A) (Inf B) \<le> Inf (A \<inter> B)"
  by (metis cInf_superset_mono lattice_class.inf_sup_ord(1) le_infI1)

lemma cSup_inter_less_eq: "bdd_above A \<Longrightarrow> bdd_above B \<Longrightarrow> A \<inter> B \<noteq> {} \<Longrightarrow> Sup (A \<inter> B) \<le> sup (Sup A) (Sup B) "
  by (metis cSup_subset_mono lattice_class.inf_sup_ord(1) le_supI1)

lemma cInf_union_distrib: "A \<noteq> {} \<Longrightarrow> bdd_below A \<Longrightarrow> B \<noteq> {} \<Longrightarrow> bdd_below B \<Longrightarrow> Inf (A \<union> B) = inf (Inf A) (Inf B)"
  by (intro antisym le_infI cInf_greatest cInf_lower) (auto intro: le_infI1 le_infI2 cInf_lower)

lemma cINF_union: "A \<noteq> {} \<Longrightarrow> bdd_below (f`A) \<Longrightarrow> B \<noteq> {} \<Longrightarrow> bdd_below (f`B) \<Longrightarrow> INFI (A \<union> B) f = inf (INFI A f) (INFI B f)"
  unfolding INF_def using assms by (auto simp add: image_Un intro: cInf_union_distrib)

lemma cSup_union_distrib: "A \<noteq> {} \<Longrightarrow> bdd_above A \<Longrightarrow> B \<noteq> {} \<Longrightarrow> bdd_above B \<Longrightarrow> Sup (A \<union> B) = sup (Sup A) (Sup B)"
  by (intro antisym le_supI cSup_least cSup_upper) (auto intro: le_supI1 le_supI2 cSup_upper)

lemma cSUP_union: "A \<noteq> {} \<Longrightarrow> bdd_above (f`A) \<Longrightarrow> B \<noteq> {} \<Longrightarrow> bdd_above (f`B) \<Longrightarrow> SUPR (A \<union> B) f = sup (SUPR A f) (SUPR B f)"
  unfolding SUP_def by (auto simp add: image_Un intro: cSup_union_distrib)

lemma cINF_inf_distrib: "A \<noteq> {} \<Longrightarrow> bdd_below (f`A) \<Longrightarrow> bdd_below (g`A) \<Longrightarrow> inf (INFI A f) (INFI A g) = (INF a:A. inf (f a) (g a))"
  by (intro antisym le_infI cINF_greatest cINF_lower2)
     (auto intro: le_infI1 le_infI2 cINF_greatest cINF_lower le_infI)

lemma SUP_sup_distrib: "A \<noteq> {} \<Longrightarrow> bdd_above (f`A) \<Longrightarrow> bdd_above (g`A) \<Longrightarrow> sup (SUPR A f) (SUPR A g) = (SUP a:A. sup (f a) (g a))"
  by (intro antisym le_supI cSUP_least cSUP_upper2)
     (auto intro: le_supI1 le_supI2 cSUP_least cSUP_upper le_supI)

end

instance complete_lattice \<subseteq> conditionally_complete_lattice
  by default (auto intro: Sup_upper Sup_least Inf_lower Inf_greatest)

lemma isLub_cSup: 
  "(S::'a :: conditionally_complete_lattice set) \<noteq> {} \<Longrightarrow> (\<exists>b. S *<= b) \<Longrightarrow> isLub UNIV S (Sup S)"
  by  (auto simp add: isLub_def setle_def leastP_def isUb_def
            intro!: setgeI cSup_upper cSup_least)

lemma cSup_eq:
  fixes a :: "'a :: {conditionally_complete_lattice, no_bot}"
  assumes upper: "\<And>x. x \<in> X \<Longrightarrow> x \<le> a"
  assumes least: "\<And>y. (\<And>x. x \<in> X \<Longrightarrow> x \<le> y) \<Longrightarrow> a \<le> y"
  shows "Sup X = a"
proof cases
  assume "X = {}" with lt_ex[of a] least show ?thesis by (auto simp: less_le_not_le)
qed (intro cSup_eq_non_empty assms)

lemma cInf_eq:
  fixes a :: "'a :: {conditionally_complete_lattice, no_top}"
  assumes upper: "\<And>x. x \<in> X \<Longrightarrow> a \<le> x"
  assumes least: "\<And>y. (\<And>x. x \<in> X \<Longrightarrow> y \<le> x) \<Longrightarrow> y \<le> a"
  shows "Inf X = a"
proof cases
  assume "X = {}" with gt_ex[of a] least show ?thesis by (auto simp: less_le_not_le)
qed (intro cInf_eq_non_empty assms)

lemma cSup_le: "(S::'a::conditionally_complete_lattice set) \<noteq> {} \<Longrightarrow> S *<= b \<Longrightarrow> Sup S \<le> b"
  by (metis cSup_least setle_def)

lemma cInf_ge: "(S::'a :: conditionally_complete_lattice set) \<noteq> {} \<Longrightarrow> b <=* S \<Longrightarrow> Inf S \<ge> b"
  by (metis cInf_greatest setge_def)

class conditionally_complete_linorder = conditionally_complete_lattice + linorder
begin

lemma less_cSup_iff : (*REAL_SUP_LE in HOL4*)
  "X \<noteq> {} \<Longrightarrow> bdd_above X \<Longrightarrow> y < Sup X \<longleftrightarrow> (\<exists>x\<in>X. y < x)"
  by (rule iffI) (metis cSup_least not_less, metis cSup_upper less_le_trans)

lemma cInf_less_iff: "X \<noteq> {} \<Longrightarrow> bdd_below X \<Longrightarrow> Inf X < y \<longleftrightarrow> (\<exists>x\<in>X. x < y)"
  by (rule iffI) (metis cInf_greatest not_less, metis cInf_lower le_less_trans)

lemma less_cSupE:
  assumes "y < Sup X" "X \<noteq> {}" obtains x where "x \<in> X" "y < x"
  by (metis cSup_least assms not_le that)

lemma less_cSupD:
  "X \<noteq> {} \<Longrightarrow> z < Sup X \<Longrightarrow> \<exists>x\<in>X. z < x"
  by (metis less_cSup_iff not_leE bdd_above_def)

lemma cInf_lessD:
  "X \<noteq> {} \<Longrightarrow> Inf X < z \<Longrightarrow> \<exists>x\<in>X. x < z"
  by (metis cInf_less_iff not_leE bdd_below_def)

lemma complete_interval:
  assumes "a < b" and "P a" and "\<not> P b"
  shows "\<exists>c. a \<le> c \<and> c \<le> b \<and> (\<forall>x. a \<le> x \<and> x < c \<longrightarrow> P x) \<and>
             (\<forall>d. (\<forall>x. a \<le> x \<and> x < d \<longrightarrow> P x) \<longrightarrow> d \<le> c)"
proof (rule exI [where x = "Sup {d. \<forall>x. a \<le> x & x < d --> P x}"], auto)
  show "a \<le> Sup {d. \<forall>c. a \<le> c \<and> c < d \<longrightarrow> P c}"
    by (rule cSup_upper, auto simp: bdd_above_def)
       (metis `a < b` `\<not> P b` linear less_le)
next
  show "Sup {d. \<forall>c. a \<le> c \<and> c < d \<longrightarrow> P c} \<le> b"
    apply (rule cSup_least) 
    apply auto
    apply (metis less_le_not_le)
    apply (metis `a<b` `~ P b` linear less_le)
    done
next
  fix x
  assume x: "a \<le> x" and lt: "x < Sup {d. \<forall>c. a \<le> c \<and> c < d \<longrightarrow> P c}"
  show "P x"
    apply (rule less_cSupE [OF lt], auto)
    apply (metis less_le_not_le)
    apply (metis x) 
    done
next
  fix d
    assume 0: "\<forall>x. a \<le> x \<and> x < d \<longrightarrow> P x"
    thus "d \<le> Sup {d. \<forall>c. a \<le> c \<and> c < d \<longrightarrow> P c}"
      by (rule_tac cSup_upper, auto simp: bdd_above_def)
         (metis `a<b` `~ P b` linear less_le)
qed

end

lemma cSup_eq_Max: "finite (X::'a::conditionally_complete_linorder set) \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Sup X = Max X"
  using cSup_eq_Sup_fin[of X] Sup_fin_eq_Max[of X] by simp

lemma cInf_eq_Min: "finite (X::'a::conditionally_complete_linorder set) \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Inf X = Min X"
  using cInf_eq_Inf_fin[of X] Inf_fin_eq_Min[of X] by simp

lemma cSup_bounds:
  fixes S :: "'a :: conditionally_complete_lattice set"
  assumes Se: "S \<noteq> {}" and l: "a <=* S" and u: "S *<= b"
  shows "a \<le> Sup S \<and> Sup S \<le> b"
proof-
  from isLub_cSup[OF Se] u have lub: "isLub UNIV S (Sup S)" by blast
  hence b: "Sup S \<le> b" using u 
    by (auto simp add: isLub_def leastP_def setle_def setge_def isUb_def) 
  from Se obtain y where y: "y \<in> S" by blast
  from lub l have "a \<le> Sup S"
    by (auto simp add: isLub_def leastP_def setle_def setge_def isUb_def)
       (metis le_iff_sup le_sup_iff y)
  with b show ?thesis by blast
qed

lemma cSup_unique: "(S::'a :: {conditionally_complete_linorder, no_bot} set) *<= b \<Longrightarrow> (\<forall>b'<b. \<exists>x\<in>S. b' < x) \<Longrightarrow> Sup S = b"
  by (rule cSup_eq) (auto simp: not_le[symmetric] setle_def)

lemma cInf_unique: "b <=* (S::'a :: {conditionally_complete_linorder, no_top} set) \<Longrightarrow> (\<forall>b'>b. \<exists>x\<in>S. b' > x) \<Longrightarrow> Inf S = b"
  by (rule cInf_eq) (auto simp: not_le[symmetric] setge_def)

lemma cSup_lessThan[simp]: "Sup {..<x::'a::{conditionally_complete_linorder, no_bot, dense_linorder}} = x"
  by (auto intro!: cSup_eq_non_empty intro: dense_le)

lemma cSup_greaterThanLessThan[simp]: "y < x \<Longrightarrow> Sup {y<..<x::'a::{conditionally_complete_linorder, no_bot, dense_linorder}} = x"
  by (auto intro!: cSup_eq intro: dense_le_bounded)

lemma cSup_atLeastLessThan[simp]: "y < x \<Longrightarrow> Sup {y..<x::'a::{conditionally_complete_linorder, no_bot, dense_linorder}} = x"
  by (auto intro!: cSup_eq intro: dense_le_bounded)

lemma cInf_greaterThan[simp]: "Inf {x::'a::{conditionally_complete_linorder, no_top, dense_linorder} <..} = x"
  by (auto intro!: cInf_eq intro: dense_ge)

lemma cInf_greaterThanAtMost[simp]: "y < x \<Longrightarrow> Inf {y<..x::'a::{conditionally_complete_linorder, no_top, dense_linorder}} = y"
  by (auto intro!: cInf_eq intro: dense_ge_bounded)

lemma cInf_greaterThanLessThan[simp]: "y < x \<Longrightarrow> Inf {y<..<x::'a::{conditionally_complete_linorder, no_top, dense_linorder}} = y"
  by (auto intro!: cInf_eq intro: dense_ge_bounded)

class linear_continuum = conditionally_complete_linorder + dense_linorder +
  assumes UNIV_not_singleton: "\<exists>a b::'a. a \<noteq> b"
begin

lemma ex_gt_or_lt: "\<exists>b. a < b \<or> b < a"
  by (metis UNIV_not_singleton neq_iff)

end

end
