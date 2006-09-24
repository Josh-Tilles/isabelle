(*  Title       : RealVector.thy
    ID:         $Id$
    Author      : Brian Huffman
*)

header {* Vector Spaces and Algebras over the Reals *}

theory RealVector
imports RealPow
begin

subsection {* Locale for additive functions *}

locale additive =
  fixes f :: "'a::ab_group_add \<Rightarrow> 'b::ab_group_add"
  assumes add: "f (x + y) = f x + f y"

lemma (in additive) zero: "f 0 = 0"
proof -
  have "f 0 = f (0 + 0)" by simp
  also have "\<dots> = f 0 + f 0" by (rule add)
  finally show "f 0 = 0" by simp
qed

lemma (in additive) minus: "f (- x) = - f x"
proof -
  have "f (- x) + f x = f (- x + x)" by (rule add [symmetric])
  also have "\<dots> = - f x + f x" by (simp add: zero)
  finally show "f (- x) = - f x" by (rule add_right_imp_eq)
qed

lemma (in additive) diff: "f (x - y) = f x - f y"
by (simp add: diff_def add minus)


subsection {* Real vector spaces *}

axclass scaleR < type

consts
  scaleR :: "real \<Rightarrow> 'a \<Rightarrow> 'a::scaleR" (infixr "*#" 75)

syntax (xsymbols)
  scaleR :: "real \<Rightarrow> 'a \<Rightarrow> 'a::scaleR" (infixr "*\<^sub>R" 75)

instance real :: scaleR ..

defs (overloaded)
  real_scaleR_def: "a *# x \<equiv> a * x"

axclass real_vector < scaleR, ab_group_add
  scaleR_right_distrib: "a *# (x + y) = a *# x + a *# y"
  scaleR_left_distrib: "(a + b) *# x = a *# x + b *# x"
  scaleR_assoc: "(a * b) *# x = a *# b *# x"
  scaleR_one [simp]: "1 *# x = x"

axclass real_algebra < real_vector, ring
  mult_scaleR_left: "a *# x * y = a *# (x * y)"
  mult_scaleR_right: "x * a *# y = a *# (x * y)"

axclass real_algebra_1 < real_algebra, ring_1

axclass real_div_algebra < real_algebra_1, division_ring

axclass real_field < real_div_algebra, field

instance real :: real_field
apply (intro_classes, unfold real_scaleR_def)
apply (rule right_distrib)
apply (rule left_distrib)
apply (rule mult_assoc)
apply (rule mult_1_left)
apply (rule mult_assoc)
apply (rule mult_left_commute)
done

lemmas scaleR_scaleR = scaleR_assoc [symmetric]

lemma scaleR_left_commute:
  fixes x :: "'a::real_vector"
  shows "a *# b *# x = b *# a *# x"
by (simp add: scaleR_scaleR mult_commute)

lemma additive_scaleR_right: "additive (\<lambda>x. a *# x :: 'a::real_vector)"
by (rule additive.intro, rule scaleR_right_distrib)

lemma additive_scaleR_left: "additive (\<lambda>a. a *# x :: 'a::real_vector)"
by (rule additive.intro, rule scaleR_left_distrib)

lemmas scaleR_zero_left [simp] =
  additive.zero [OF additive_scaleR_left, standard]

lemmas scaleR_zero_right [simp] =
  additive.zero [OF additive_scaleR_right, standard]

lemmas scaleR_minus_left [simp] =
  additive.minus [OF additive_scaleR_left, standard]

lemmas scaleR_minus_right [simp] =
  additive.minus [OF additive_scaleR_right, standard]

lemmas scaleR_left_diff_distrib =
  additive.diff [OF additive_scaleR_left, standard]

lemmas scaleR_right_diff_distrib =
  additive.diff [OF additive_scaleR_right, standard]

lemma scaleR_eq_0_iff:
  fixes x :: "'a::real_vector"
  shows "(a *# x = 0) = (a = 0 \<or> x = 0)"
proof cases
  assume "a = 0" thus ?thesis by simp
next
  assume anz [simp]: "a \<noteq> 0"
  { assume "a *# x = 0"
    hence "inverse a *# a *# x = 0" by simp
    hence "x = 0" by (simp (no_asm_use) add: scaleR_scaleR)}
  thus ?thesis by force
qed

lemma scaleR_left_imp_eq:
  fixes x y :: "'a::real_vector"
  shows "\<lbrakk>a \<noteq> 0; a *# x = a *# y\<rbrakk> \<Longrightarrow> x = y"
proof -
  assume nonzero: "a \<noteq> 0"
  assume "a *# x = a *# y"
  hence "a *# (x - y) = 0"
     by (simp add: scaleR_right_diff_distrib)
  hence "x - y = 0"
     by (simp add: scaleR_eq_0_iff nonzero)
  thus "x = y" by simp
qed

lemma scaleR_right_imp_eq:
  fixes x y :: "'a::real_vector"
  shows "\<lbrakk>x \<noteq> 0; a *# x = b *# x\<rbrakk> \<Longrightarrow> a = b"
proof -
  assume nonzero: "x \<noteq> 0"
  assume "a *# x = b *# x"
  hence "(a - b) *# x = 0"
     by (simp add: scaleR_left_diff_distrib)
  hence "a - b = 0"
     by (simp add: scaleR_eq_0_iff nonzero)
  thus "a = b" by simp
qed

lemma scaleR_cancel_left:
  fixes x y :: "'a::real_vector"
  shows "(a *# x = a *# y) = (x = y \<or> a = 0)"
by (auto intro: scaleR_left_imp_eq)

lemma scaleR_cancel_right:
  fixes x y :: "'a::real_vector"
  shows "(a *# x = b *# x) = (a = b \<or> x = 0)"
by (auto intro: scaleR_right_imp_eq)

lemma nonzero_inverse_scaleR_distrib:
  fixes x :: "'a::real_div_algebra"
  shows "\<lbrakk>a \<noteq> 0; x \<noteq> 0\<rbrakk> \<Longrightarrow> inverse (a *# x) = inverse a *# inverse x"
apply (rule inverse_unique)
apply (simp add: mult_scaleR_left mult_scaleR_right scaleR_scaleR)
done

lemma inverse_scaleR_distrib:
  fixes x :: "'a::{real_div_algebra,division_by_zero}"
  shows "inverse (a *# x) = inverse a *# inverse x"
apply (case_tac "a = 0", simp)
apply (case_tac "x = 0", simp)
apply (erule (1) nonzero_inverse_scaleR_distrib)
done


subsection {* Embedding of the Reals into any @{text real_algebra_1}:
@{term of_real} *}

definition
  of_real :: "real \<Rightarrow> 'a::real_algebra_1"
  "of_real r = r *# 1"

lemma of_real_0 [simp]: "of_real 0 = 0"
by (simp add: of_real_def)

lemma of_real_1 [simp]: "of_real 1 = 1"
by (simp add: of_real_def)

lemma of_real_add [simp]: "of_real (x + y) = of_real x + of_real y"
by (simp add: of_real_def scaleR_left_distrib)

lemma of_real_minus [simp]: "of_real (- x) = - of_real x"
by (simp add: of_real_def)

lemma of_real_diff [simp]: "of_real (x - y) = of_real x - of_real y"
by (simp add: of_real_def scaleR_left_diff_distrib)

lemma of_real_mult [simp]: "of_real (x * y) = of_real x * of_real y"
by (simp add: of_real_def mult_scaleR_left scaleR_scaleR)

lemma nonzero_of_real_inverse:
  "x \<noteq> 0 \<Longrightarrow> of_real (inverse x) =
   inverse (of_real x :: 'a::real_div_algebra)"
by (simp add: of_real_def nonzero_inverse_scaleR_distrib)

lemma of_real_inverse [simp]:
  "of_real (inverse x) =
   inverse (of_real x :: 'a::{real_div_algebra,division_by_zero})"
by (simp add: of_real_def inverse_scaleR_distrib)

lemma nonzero_of_real_divide:
  "y \<noteq> 0 \<Longrightarrow> of_real (x / y) =
   (of_real x / of_real y :: 'a::real_field)"
by (simp add: divide_inverse nonzero_of_real_inverse)
  
lemma of_real_divide:
  "of_real (x / y) =
   (of_real x / of_real y :: 'a::{real_field,division_by_zero})"
by (simp add: divide_inverse)

lemma of_real_eq_iff [simp]: "(of_real x = of_real y) = (x = y)"
by (simp add: of_real_def scaleR_cancel_right)

lemmas of_real_eq_0_iff [simp] = of_real_eq_iff [of _ 0, simplified]

lemma of_real_eq_id [simp]: "of_real = (id :: real \<Rightarrow> real)"
proof
  fix r
  show "of_real r = id r"
    by (simp add: of_real_def real_scaleR_def)
qed

text{*Collapse nested embeddings*}
lemma of_real_of_nat_eq [simp]: "of_real (of_nat n) = of_nat n"
by (induct n, auto)

lemma of_real_of_int_eq [simp]: "of_real (of_int z) = of_int z"
by (cases z rule: int_diff_cases, simp)

lemma of_real_number_of_eq:
  "of_real (number_of w) = (number_of w :: 'a::{number_ring,real_algebra_1})"
by (simp add: number_of_eq)


subsection {* The Set of Real Numbers *}

constdefs
   Reals :: "'a::real_algebra_1 set"
   "Reals \<equiv> range of_real"

const_syntax (xsymbols)
  Reals  ("\<real>")

lemma of_real_in_Reals [simp]: "of_real r \<in> Reals"
by (simp add: Reals_def)

lemma Reals_0 [simp]: "0 \<in> Reals"
apply (unfold Reals_def)
apply (rule range_eqI)
apply (rule of_real_0 [symmetric])
done

lemma Reals_1 [simp]: "1 \<in> Reals"
apply (unfold Reals_def)
apply (rule range_eqI)
apply (rule of_real_1 [symmetric])
done

lemma Reals_add [simp]: "\<lbrakk>a \<in> Reals; b \<in> Reals\<rbrakk> \<Longrightarrow> a + b \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (rule of_real_add [symmetric])
done

lemma Reals_minus [simp]: "a \<in> Reals \<Longrightarrow> - a \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (rule of_real_minus [symmetric])
done

lemma Reals_diff [simp]: "\<lbrakk>a \<in> Reals; b \<in> Reals\<rbrakk> \<Longrightarrow> a - b \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (rule of_real_diff [symmetric])
done

lemma Reals_mult [simp]: "\<lbrakk>a \<in> Reals; b \<in> Reals\<rbrakk> \<Longrightarrow> a * b \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (rule of_real_mult [symmetric])
done

lemma nonzero_Reals_inverse:
  fixes a :: "'a::real_div_algebra"
  shows "\<lbrakk>a \<in> Reals; a \<noteq> 0\<rbrakk> \<Longrightarrow> inverse a \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (erule nonzero_of_real_inverse [symmetric])
done

lemma Reals_inverse [simp]:
  fixes a :: "'a::{real_div_algebra,division_by_zero}"
  shows "a \<in> Reals \<Longrightarrow> inverse a \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (rule of_real_inverse [symmetric])
done

lemma nonzero_Reals_divide:
  fixes a b :: "'a::real_field"
  shows "\<lbrakk>a \<in> Reals; b \<in> Reals; b \<noteq> 0\<rbrakk> \<Longrightarrow> a / b \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (erule nonzero_of_real_divide [symmetric])
done

lemma Reals_divide [simp]:
  fixes a b :: "'a::{real_field,division_by_zero}"
  shows "\<lbrakk>a \<in> Reals; b \<in> Reals\<rbrakk> \<Longrightarrow> a / b \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (rule of_real_divide [symmetric])
done

lemma Reals_cases [cases set: Reals]:
  assumes "q \<in> \<real>"
  obtains (of_real) r where "q = of_real r"
  unfolding Reals_def
proof -
  from `q \<in> \<real>` have "q \<in> range of_real" unfolding Reals_def .
  then obtain r where "q = of_real r" ..
  then show thesis ..
qed

lemma Reals_induct [case_names of_real, induct set: Reals]:
  "q \<in> \<real> \<Longrightarrow> (\<And>r. P (of_real r)) \<Longrightarrow> P q"
  by (rule Reals_cases) auto


subsection {* Real normed vector spaces *}

axclass norm < type
consts norm :: "'a::norm \<Rightarrow> real"

instance real :: norm ..

defs (overloaded)
  real_norm_def [simp]: "norm r \<equiv> \<bar>r\<bar>"

axclass normed < plus, zero, norm
  norm_ge_zero [simp]: "0 \<le> norm x"
  norm_eq_zero [simp]: "(norm x = 0) = (x = 0)"
  norm_triangle_ineq: "norm (x + y) \<le> norm x + norm y"

axclass real_normed_vector < real_vector, normed
  norm_scaleR: "norm (a *# x) = \<bar>a\<bar> * norm x"

axclass real_normed_algebra < real_algebra, real_normed_vector
  norm_mult_ineq: "norm (x * y) \<le> norm x * norm y"

axclass real_normed_div_algebra < real_div_algebra, normed
  norm_of_real: "norm (of_real r) = abs r"
  norm_mult: "norm (x * y) = norm x * norm y"

axclass real_normed_field < real_field, real_normed_div_algebra

instance real_normed_div_algebra < real_normed_algebra
proof
  fix a :: real and x :: 'a
  have "norm (a *# x) = norm (of_real a * x)"
    by (simp add: of_real_def mult_scaleR_left)
  also have "\<dots> = abs a * norm x"
    by (simp add: norm_mult norm_of_real)
  finally show "norm (a *# x) = abs a * norm x" .
next
  fix x y :: 'a
  show "norm (x * y) \<le> norm x * norm y"
    by (simp add: norm_mult)
qed

instance real :: real_normed_field
apply (intro_classes, unfold real_norm_def)
apply (rule abs_ge_zero)
apply (rule abs_eq_0)
apply (rule abs_triangle_ineq)
apply simp
apply (rule abs_mult)
done

lemma norm_zero [simp]: "norm (0::'a::real_normed_vector) = 0"
by simp

lemma zero_less_norm_iff [simp]:
  fixes x :: "'a::real_normed_vector"
  shows "(0 < norm x) = (x \<noteq> 0)"
by (simp add: order_less_le)

lemma norm_minus_cancel [simp]:
  fixes x :: "'a::real_normed_vector"
  shows "norm (- x) = norm x"
proof -
  have "norm (- x) = norm (- 1 *# x)"
    by (simp only: scaleR_minus_left scaleR_one)
  also have "\<dots> = \<bar>- 1\<bar> * norm x"
    by (rule norm_scaleR)
  finally show ?thesis by simp
qed

lemma norm_minus_commute:
  fixes a b :: "'a::real_normed_vector"
  shows "norm (a - b) = norm (b - a)"
proof -
  have "norm (a - b) = norm (- (a - b))"
    by (simp only: norm_minus_cancel)
  also have "\<dots> = norm (b - a)" by simp
  finally show ?thesis .
qed

lemma norm_triangle_ineq2:
  fixes a b :: "'a::real_normed_vector"
  shows "norm a - norm b \<le> norm (a - b)"
proof -
  have "norm (a - b + b) \<le> norm (a - b) + norm b"
    by (rule norm_triangle_ineq)
  also have "(a - b + b) = a"
    by simp
  finally show ?thesis
    by (simp add: compare_rls)
qed

lemma norm_triangle_ineq3:
  fixes a b :: "'a::real_normed_vector"
  shows "\<bar>norm a - norm b\<bar> \<le> norm (a - b)"
apply (subst abs_le_iff)
apply auto
apply (rule norm_triangle_ineq2)
apply (subst norm_minus_commute)
apply (rule norm_triangle_ineq2)
done

lemma norm_triangle_ineq4:
  fixes a b :: "'a::real_normed_vector"
  shows "norm (a - b) \<le> norm a + norm b"
proof -
  have "norm (a - b) = norm (a + - b)"
    by (simp only: diff_minus)
  also have "\<dots> \<le> norm a + norm (- b)"
    by (rule norm_triangle_ineq)
  finally show ?thesis
    by simp
qed

lemma norm_diff_triangle_ineq:
  fixes a b c d :: "'a::real_normed_vector"
  shows "norm ((a + b) - (c + d)) \<le> norm (a - c) + norm (b - d)"
proof -
  have "norm ((a + b) - (c + d)) = norm ((a - c) + (b - d))"
    by (simp add: diff_minus add_ac)
  also have "\<dots> \<le> norm (a - c) + norm (b - d)"
    by (rule norm_triangle_ineq)
  finally show ?thesis .
qed

lemma norm_one [simp]: "norm (1::'a::real_normed_div_algebra) = 1"
proof -
  have "norm (of_real 1 :: 'a) = abs 1"
    by (rule norm_of_real)
  thus ?thesis by simp
qed

lemma nonzero_norm_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  shows "a \<noteq> 0 \<Longrightarrow> norm (inverse a) = inverse (norm a)"
apply (rule inverse_unique [symmetric])
apply (simp add: norm_mult [symmetric])
done

lemma norm_inverse:
  fixes a :: "'a::{real_normed_div_algebra,division_by_zero}"
  shows "norm (inverse a) = inverse (norm a)"
apply (case_tac "a = 0", simp)
apply (erule nonzero_norm_inverse)
done

lemma nonzero_norm_divide:
  fixes a b :: "'a::real_normed_field"
  shows "b \<noteq> 0 \<Longrightarrow> norm (a / b) = norm a / norm b"
by (simp add: divide_inverse norm_mult nonzero_norm_inverse)

lemma norm_divide:
  fixes a b :: "'a::{real_normed_field,division_by_zero}"
  shows "norm (a / b) = norm a / norm b"
by (simp add: divide_inverse norm_mult norm_inverse)

lemma norm_power:
  fixes x :: "'a::{real_normed_div_algebra,recpower}"
  shows "norm (x ^ n) = norm x ^ n"
by (induct n, simp, simp add: power_Suc norm_mult)

end
