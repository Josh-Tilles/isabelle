(*  Title:      HOL/RealVector.thy
    Author:     Brian Huffman
*)

header {* Vector Spaces and Algebras over the Reals *}

theory RealVector
imports Metric_Spaces
begin

subsection {* Locale for additive functions *}

locale additive =
  fixes f :: "'a::ab_group_add \<Rightarrow> 'b::ab_group_add"
  assumes add: "f (x + y) = f x + f y"
begin

lemma zero: "f 0 = 0"
proof -
  have "f 0 = f (0 + 0)" by simp
  also have "\<dots> = f 0 + f 0" by (rule add)
  finally show "f 0 = 0" by simp
qed

lemma minus: "f (- x) = - f x"
proof -
  have "f (- x) + f x = f (- x + x)" by (rule add [symmetric])
  also have "\<dots> = - f x + f x" by (simp add: zero)
  finally show "f (- x) = - f x" by (rule add_right_imp_eq)
qed

lemma diff: "f (x - y) = f x - f y"
by (simp add: add minus diff_minus)

lemma setsum: "f (setsum g A) = (\<Sum>x\<in>A. f (g x))"
apply (cases "finite A")
apply (induct set: finite)
apply (simp add: zero)
apply (simp add: add)
apply (simp add: zero)
done

end

subsection {* Vector spaces *}

locale vector_space =
  fixes scale :: "'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b"
  assumes scale_right_distrib [algebra_simps]:
    "scale a (x + y) = scale a x + scale a y"
  and scale_left_distrib [algebra_simps]:
    "scale (a + b) x = scale a x + scale b x"
  and scale_scale [simp]: "scale a (scale b x) = scale (a * b) x"
  and scale_one [simp]: "scale 1 x = x"
begin

lemma scale_left_commute:
  "scale a (scale b x) = scale b (scale a x)"
by (simp add: mult_commute)

lemma scale_zero_left [simp]: "scale 0 x = 0"
  and scale_minus_left [simp]: "scale (- a) x = - (scale a x)"
  and scale_left_diff_distrib [algebra_simps]:
        "scale (a - b) x = scale a x - scale b x"
  and scale_setsum_left: "scale (setsum f A) x = (\<Sum>a\<in>A. scale (f a) x)"
proof -
  interpret s: additive "\<lambda>a. scale a x"
    proof qed (rule scale_left_distrib)
  show "scale 0 x = 0" by (rule s.zero)
  show "scale (- a) x = - (scale a x)" by (rule s.minus)
  show "scale (a - b) x = scale a x - scale b x" by (rule s.diff)
  show "scale (setsum f A) x = (\<Sum>a\<in>A. scale (f a) x)" by (rule s.setsum)
qed

lemma scale_zero_right [simp]: "scale a 0 = 0"
  and scale_minus_right [simp]: "scale a (- x) = - (scale a x)"
  and scale_right_diff_distrib [algebra_simps]:
        "scale a (x - y) = scale a x - scale a y"
  and scale_setsum_right: "scale a (setsum f A) = (\<Sum>x\<in>A. scale a (f x))"
proof -
  interpret s: additive "\<lambda>x. scale a x"
    proof qed (rule scale_right_distrib)
  show "scale a 0 = 0" by (rule s.zero)
  show "scale a (- x) = - (scale a x)" by (rule s.minus)
  show "scale a (x - y) = scale a x - scale a y" by (rule s.diff)
  show "scale a (setsum f A) = (\<Sum>x\<in>A. scale a (f x))" by (rule s.setsum)
qed

lemma scale_eq_0_iff [simp]:
  "scale a x = 0 \<longleftrightarrow> a = 0 \<or> x = 0"
proof cases
  assume "a = 0" thus ?thesis by simp
next
  assume anz [simp]: "a \<noteq> 0"
  { assume "scale a x = 0"
    hence "scale (inverse a) (scale a x) = 0" by simp
    hence "x = 0" by simp }
  thus ?thesis by force
qed

lemma scale_left_imp_eq:
  "\<lbrakk>a \<noteq> 0; scale a x = scale a y\<rbrakk> \<Longrightarrow> x = y"
proof -
  assume nonzero: "a \<noteq> 0"
  assume "scale a x = scale a y"
  hence "scale a (x - y) = 0"
     by (simp add: scale_right_diff_distrib)
  hence "x - y = 0" by (simp add: nonzero)
  thus "x = y" by (simp only: right_minus_eq)
qed

lemma scale_right_imp_eq:
  "\<lbrakk>x \<noteq> 0; scale a x = scale b x\<rbrakk> \<Longrightarrow> a = b"
proof -
  assume nonzero: "x \<noteq> 0"
  assume "scale a x = scale b x"
  hence "scale (a - b) x = 0"
     by (simp add: scale_left_diff_distrib)
  hence "a - b = 0" by (simp add: nonzero)
  thus "a = b" by (simp only: right_minus_eq)
qed

lemma scale_cancel_left [simp]:
  "scale a x = scale a y \<longleftrightarrow> x = y \<or> a = 0"
by (auto intro: scale_left_imp_eq)

lemma scale_cancel_right [simp]:
  "scale a x = scale b x \<longleftrightarrow> a = b \<or> x = 0"
by (auto intro: scale_right_imp_eq)

end

subsection {* Real vector spaces *}

class scaleR =
  fixes scaleR :: "real \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "*\<^sub>R" 75)
begin

abbreviation
  divideR :: "'a \<Rightarrow> real \<Rightarrow> 'a" (infixl "'/\<^sub>R" 70)
where
  "x /\<^sub>R r == scaleR (inverse r) x"

end

class real_vector = scaleR + ab_group_add +
  assumes scaleR_add_right: "scaleR a (x + y) = scaleR a x + scaleR a y"
  and scaleR_add_left: "scaleR (a + b) x = scaleR a x + scaleR b x"
  and scaleR_scaleR: "scaleR a (scaleR b x) = scaleR (a * b) x"
  and scaleR_one: "scaleR 1 x = x"

interpretation real_vector:
  vector_space "scaleR :: real \<Rightarrow> 'a \<Rightarrow> 'a::real_vector"
apply unfold_locales
apply (rule scaleR_add_right)
apply (rule scaleR_add_left)
apply (rule scaleR_scaleR)
apply (rule scaleR_one)
done

text {* Recover original theorem names *}

lemmas scaleR_left_commute = real_vector.scale_left_commute
lemmas scaleR_zero_left = real_vector.scale_zero_left
lemmas scaleR_minus_left = real_vector.scale_minus_left
lemmas scaleR_diff_left = real_vector.scale_left_diff_distrib
lemmas scaleR_setsum_left = real_vector.scale_setsum_left
lemmas scaleR_zero_right = real_vector.scale_zero_right
lemmas scaleR_minus_right = real_vector.scale_minus_right
lemmas scaleR_diff_right = real_vector.scale_right_diff_distrib
lemmas scaleR_setsum_right = real_vector.scale_setsum_right
lemmas scaleR_eq_0_iff = real_vector.scale_eq_0_iff
lemmas scaleR_left_imp_eq = real_vector.scale_left_imp_eq
lemmas scaleR_right_imp_eq = real_vector.scale_right_imp_eq
lemmas scaleR_cancel_left = real_vector.scale_cancel_left
lemmas scaleR_cancel_right = real_vector.scale_cancel_right

text {* Legacy names *}

lemmas scaleR_left_distrib = scaleR_add_left
lemmas scaleR_right_distrib = scaleR_add_right
lemmas scaleR_left_diff_distrib = scaleR_diff_left
lemmas scaleR_right_diff_distrib = scaleR_diff_right

lemma scaleR_minus1_left [simp]:
  fixes x :: "'a::real_vector"
  shows "scaleR (-1) x = - x"
  using scaleR_minus_left [of 1 x] by simp

class real_algebra = real_vector + ring +
  assumes mult_scaleR_left [simp]: "scaleR a x * y = scaleR a (x * y)"
  and mult_scaleR_right [simp]: "x * scaleR a y = scaleR a (x * y)"

class real_algebra_1 = real_algebra + ring_1

class real_div_algebra = real_algebra_1 + division_ring

class real_field = real_div_algebra + field

instantiation real :: real_field
begin

definition
  real_scaleR_def [simp]: "scaleR a x = a * x"

instance proof
qed (simp_all add: algebra_simps)

end

interpretation scaleR_left: additive "(\<lambda>a. scaleR a x::'a::real_vector)"
proof qed (rule scaleR_left_distrib)

interpretation scaleR_right: additive "(\<lambda>x. scaleR a x::'a::real_vector)"
proof qed (rule scaleR_right_distrib)

lemma nonzero_inverse_scaleR_distrib:
  fixes x :: "'a::real_div_algebra" shows
  "\<lbrakk>a \<noteq> 0; x \<noteq> 0\<rbrakk> \<Longrightarrow> inverse (scaleR a x) = scaleR (inverse a) (inverse x)"
by (rule inverse_unique, simp)

lemma inverse_scaleR_distrib:
  fixes x :: "'a::{real_div_algebra, division_ring_inverse_zero}"
  shows "inverse (scaleR a x) = scaleR (inverse a) (inverse x)"
apply (case_tac "a = 0", simp)
apply (case_tac "x = 0", simp)
apply (erule (1) nonzero_inverse_scaleR_distrib)
done


subsection {* Embedding of the Reals into any @{text real_algebra_1}:
@{term of_real} *}

definition
  of_real :: "real \<Rightarrow> 'a::real_algebra_1" where
  "of_real r = scaleR r 1"

lemma scaleR_conv_of_real: "scaleR r x = of_real r * x"
by (simp add: of_real_def)

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
by (simp add: of_real_def mult_commute)

lemma nonzero_of_real_inverse:
  "x \<noteq> 0 \<Longrightarrow> of_real (inverse x) =
   inverse (of_real x :: 'a::real_div_algebra)"
by (simp add: of_real_def nonzero_inverse_scaleR_distrib)

lemma of_real_inverse [simp]:
  "of_real (inverse x) =
   inverse (of_real x :: 'a::{real_div_algebra, division_ring_inverse_zero})"
by (simp add: of_real_def inverse_scaleR_distrib)

lemma nonzero_of_real_divide:
  "y \<noteq> 0 \<Longrightarrow> of_real (x / y) =
   (of_real x / of_real y :: 'a::real_field)"
by (simp add: divide_inverse nonzero_of_real_inverse)

lemma of_real_divide [simp]:
  "of_real (x / y) =
   (of_real x / of_real y :: 'a::{real_field, field_inverse_zero})"
by (simp add: divide_inverse)

lemma of_real_power [simp]:
  "of_real (x ^ n) = (of_real x :: 'a::{real_algebra_1}) ^ n"
by (induct n) simp_all

lemma of_real_eq_iff [simp]: "(of_real x = of_real y) = (x = y)"
by (simp add: of_real_def)

lemma inj_of_real:
  "inj of_real"
  by (auto intro: injI)

lemmas of_real_eq_0_iff [simp] = of_real_eq_iff [of _ 0, simplified]

lemma of_real_eq_id [simp]: "of_real = (id :: real \<Rightarrow> real)"
proof
  fix r
  show "of_real r = id r"
    by (simp add: of_real_def)
qed

text{*Collapse nested embeddings*}
lemma of_real_of_nat_eq [simp]: "of_real (of_nat n) = of_nat n"
by (induct n) auto

lemma of_real_of_int_eq [simp]: "of_real (of_int z) = of_int z"
by (cases z rule: int_diff_cases, simp)

lemma of_real_numeral: "of_real (numeral w) = numeral w"
using of_real_of_int_eq [of "numeral w"] by simp

lemma of_real_neg_numeral: "of_real (neg_numeral w) = neg_numeral w"
using of_real_of_int_eq [of "neg_numeral w"] by simp

text{*Every real algebra has characteristic zero*}

instance real_algebra_1 < ring_char_0
proof
  from inj_of_real inj_of_nat have "inj (of_real \<circ> of_nat)" by (rule inj_comp)
  then show "inj (of_nat :: nat \<Rightarrow> 'a)" by (simp add: comp_def)
qed

instance real_field < field_char_0 ..


subsection {* The Set of Real Numbers *}

definition Reals :: "'a::real_algebra_1 set" where
  "Reals = range of_real"

notation (xsymbols)
  Reals  ("\<real>")

lemma Reals_of_real [simp]: "of_real r \<in> Reals"
by (simp add: Reals_def)

lemma Reals_of_int [simp]: "of_int z \<in> Reals"
by (subst of_real_of_int_eq [symmetric], rule Reals_of_real)

lemma Reals_of_nat [simp]: "of_nat n \<in> Reals"
by (subst of_real_of_nat_eq [symmetric], rule Reals_of_real)

lemma Reals_numeral [simp]: "numeral w \<in> Reals"
by (subst of_real_numeral [symmetric], rule Reals_of_real)

lemma Reals_neg_numeral [simp]: "neg_numeral w \<in> Reals"
by (subst of_real_neg_numeral [symmetric], rule Reals_of_real)

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
  fixes a :: "'a::{real_div_algebra, division_ring_inverse_zero}"
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
  fixes a b :: "'a::{real_field, field_inverse_zero}"
  shows "\<lbrakk>a \<in> Reals; b \<in> Reals\<rbrakk> \<Longrightarrow> a / b \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (rule of_real_divide [symmetric])
done

lemma Reals_power [simp]:
  fixes a :: "'a::{real_algebra_1}"
  shows "a \<in> Reals \<Longrightarrow> a ^ n \<in> Reals"
apply (auto simp add: Reals_def)
apply (rule range_eqI)
apply (rule of_real_power [symmetric])
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

class norm =
  fixes norm :: "'a \<Rightarrow> real"

class sgn_div_norm = scaleR + norm + sgn +
  assumes sgn_div_norm: "sgn x = x /\<^sub>R norm x"

class dist_norm = dist + norm + minus +
  assumes dist_norm: "dist x y = norm (x - y)"

class real_normed_vector = real_vector + sgn_div_norm + dist_norm + open_dist +
  assumes norm_eq_zero [simp]: "norm x = 0 \<longleftrightarrow> x = 0"
  and norm_triangle_ineq: "norm (x + y) \<le> norm x + norm y"
  and norm_scaleR [simp]: "norm (scaleR a x) = \<bar>a\<bar> * norm x"
begin

lemma norm_ge_zero [simp]: "0 \<le> norm x"
proof -
  have "0 = norm (x + -1 *\<^sub>R x)" 
    using scaleR_add_left[of 1 "-1" x] norm_scaleR[of 0 x] by (simp add: scaleR_one)
  also have "\<dots> \<le> norm x + norm (-1 *\<^sub>R x)" by (rule norm_triangle_ineq)
  finally show ?thesis by simp
qed

end

class real_normed_algebra = real_algebra + real_normed_vector +
  assumes norm_mult_ineq: "norm (x * y) \<le> norm x * norm y"

class real_normed_algebra_1 = real_algebra_1 + real_normed_algebra +
  assumes norm_one [simp]: "norm 1 = 1"

class real_normed_div_algebra = real_div_algebra + real_normed_vector +
  assumes norm_mult: "norm (x * y) = norm x * norm y"

class real_normed_field = real_field + real_normed_div_algebra

instance real_normed_div_algebra < real_normed_algebra_1
proof
  fix x y :: 'a
  show "norm (x * y) \<le> norm x * norm y"
    by (simp add: norm_mult)
next
  have "norm (1 * 1::'a) = norm (1::'a) * norm (1::'a)"
    by (rule norm_mult)
  thus "norm (1::'a) = 1" by simp
qed

lemma norm_zero [simp]: "norm (0::'a::real_normed_vector) = 0"
by simp

lemma zero_less_norm_iff [simp]:
  fixes x :: "'a::real_normed_vector"
  shows "(0 < norm x) = (x \<noteq> 0)"
by (simp add: order_less_le)

lemma norm_not_less_zero [simp]:
  fixes x :: "'a::real_normed_vector"
  shows "\<not> norm x < 0"
by (simp add: linorder_not_less)

lemma norm_le_zero_iff [simp]:
  fixes x :: "'a::real_normed_vector"
  shows "(norm x \<le> 0) = (x = 0)"
by (simp add: order_le_less)

lemma norm_minus_cancel [simp]:
  fixes x :: "'a::real_normed_vector"
  shows "norm (- x) = norm x"
proof -
  have "norm (- x) = norm (scaleR (- 1) x)"
    by (simp only: scaleR_minus_left scaleR_one)
  also have "\<dots> = \<bar>- 1\<bar> * norm x"
    by (rule norm_scaleR)
  finally show ?thesis by simp
qed

lemma norm_minus_commute:
  fixes a b :: "'a::real_normed_vector"
  shows "norm (a - b) = norm (b - a)"
proof -
  have "norm (- (b - a)) = norm (b - a)"
    by (rule norm_minus_cancel)
  thus ?thesis by simp
qed

lemma norm_triangle_ineq2:
  fixes a b :: "'a::real_normed_vector"
  shows "norm a - norm b \<le> norm (a - b)"
proof -
  have "norm (a - b + b) \<le> norm (a - b) + norm b"
    by (rule norm_triangle_ineq)
  thus ?thesis by simp
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
  have "norm (a + - b) \<le> norm a + norm (- b)"
    by (rule norm_triangle_ineq)
  thus ?thesis
    by (simp only: diff_minus norm_minus_cancel)
qed

lemma norm_diff_ineq:
  fixes a b :: "'a::real_normed_vector"
  shows "norm a - norm b \<le> norm (a + b)"
proof -
  have "norm a - norm (- b) \<le> norm (a - - b)"
    by (rule norm_triangle_ineq2)
  thus ?thesis by simp
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

lemma abs_norm_cancel [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "\<bar>norm a\<bar> = norm a"
by (rule abs_of_nonneg [OF norm_ge_zero])

lemma norm_add_less:
  fixes x y :: "'a::real_normed_vector"
  shows "\<lbrakk>norm x < r; norm y < s\<rbrakk> \<Longrightarrow> norm (x + y) < r + s"
by (rule order_le_less_trans [OF norm_triangle_ineq add_strict_mono])

lemma norm_mult_less:
  fixes x y :: "'a::real_normed_algebra"
  shows "\<lbrakk>norm x < r; norm y < s\<rbrakk> \<Longrightarrow> norm (x * y) < r * s"
apply (rule order_le_less_trans [OF norm_mult_ineq])
apply (simp add: mult_strict_mono')
done

lemma norm_of_real [simp]:
  "norm (of_real r :: 'a::real_normed_algebra_1) = \<bar>r\<bar>"
unfolding of_real_def by simp

lemma norm_numeral [simp]:
  "norm (numeral w::'a::real_normed_algebra_1) = numeral w"
by (subst of_real_numeral [symmetric], subst norm_of_real, simp)

lemma norm_neg_numeral [simp]:
  "norm (neg_numeral w::'a::real_normed_algebra_1) = numeral w"
by (subst of_real_neg_numeral [symmetric], subst norm_of_real, simp)

lemma norm_of_int [simp]:
  "norm (of_int z::'a::real_normed_algebra_1) = \<bar>of_int z\<bar>"
by (subst of_real_of_int_eq [symmetric], rule norm_of_real)

lemma norm_of_nat [simp]:
  "norm (of_nat n::'a::real_normed_algebra_1) = of_nat n"
apply (subst of_real_of_nat_eq [symmetric])
apply (subst norm_of_real, simp)
done

lemma nonzero_norm_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  shows "a \<noteq> 0 \<Longrightarrow> norm (inverse a) = inverse (norm a)"
apply (rule inverse_unique [symmetric])
apply (simp add: norm_mult [symmetric])
done

lemma norm_inverse:
  fixes a :: "'a::{real_normed_div_algebra, division_ring_inverse_zero}"
  shows "norm (inverse a) = inverse (norm a)"
apply (case_tac "a = 0", simp)
apply (erule nonzero_norm_inverse)
done

lemma nonzero_norm_divide:
  fixes a b :: "'a::real_normed_field"
  shows "b \<noteq> 0 \<Longrightarrow> norm (a / b) = norm a / norm b"
by (simp add: divide_inverse norm_mult nonzero_norm_inverse)

lemma norm_divide:
  fixes a b :: "'a::{real_normed_field, field_inverse_zero}"
  shows "norm (a / b) = norm a / norm b"
by (simp add: divide_inverse norm_mult norm_inverse)

lemma norm_power_ineq:
  fixes x :: "'a::{real_normed_algebra_1}"
  shows "norm (x ^ n) \<le> norm x ^ n"
proof (induct n)
  case 0 show "norm (x ^ 0) \<le> norm x ^ 0" by simp
next
  case (Suc n)
  have "norm (x * x ^ n) \<le> norm x * norm (x ^ n)"
    by (rule norm_mult_ineq)
  also from Suc have "\<dots> \<le> norm x * norm x ^ n"
    using norm_ge_zero by (rule mult_left_mono)
  finally show "norm (x ^ Suc n) \<le> norm x ^ Suc n"
    by simp
qed

lemma norm_power:
  fixes x :: "'a::{real_normed_div_algebra}"
  shows "norm (x ^ n) = norm x ^ n"
by (induct n) (simp_all add: norm_mult)

text {* Every normed vector space is a metric space. *}

instance real_normed_vector < metric_space
proof
  fix x y :: 'a show "dist x y = 0 \<longleftrightarrow> x = y"
    unfolding dist_norm by simp
next
  fix x y z :: 'a show "dist x y \<le> dist x z + dist y z"
    unfolding dist_norm
    using norm_triangle_ineq4 [of "x - z" "y - z"] by simp
qed

subsection {* Class instances for real numbers *}

instantiation real :: real_normed_field
begin

definition real_norm_def [simp]:
  "norm r = \<bar>r\<bar>"

instance
apply (intro_classes, unfold real_norm_def real_scaleR_def)
apply (rule dist_real_def)
apply (simp add: sgn_real_def)
apply (rule abs_eq_0)
apply (rule abs_triangle_ineq)
apply (rule abs_mult)
apply (rule abs_mult)
done

end

instance real :: linear_continuum_topology ..

subsection {* Extra type constraints *}

text {* Only allow @{term "open"} in class @{text topological_space}. *}

setup {* Sign.add_const_constraint
  (@{const_name "open"}, SOME @{typ "'a::topological_space set \<Rightarrow> bool"}) *}

text {* Only allow @{term dist} in class @{text metric_space}. *}

setup {* Sign.add_const_constraint
  (@{const_name dist}, SOME @{typ "'a::metric_space \<Rightarrow> 'a \<Rightarrow> real"}) *}

text {* Only allow @{term norm} in class @{text real_normed_vector}. *}

setup {* Sign.add_const_constraint
  (@{const_name norm}, SOME @{typ "'a::real_normed_vector \<Rightarrow> real"}) *}

subsection {* Sign function *}

lemma norm_sgn:
  "norm (sgn(x::'a::real_normed_vector)) = (if x = 0 then 0 else 1)"
by (simp add: sgn_div_norm)

lemma sgn_zero [simp]: "sgn(0::'a::real_normed_vector) = 0"
by (simp add: sgn_div_norm)

lemma sgn_zero_iff: "(sgn(x::'a::real_normed_vector) = 0) = (x = 0)"
by (simp add: sgn_div_norm)

lemma sgn_minus: "sgn (- x) = - sgn(x::'a::real_normed_vector)"
by (simp add: sgn_div_norm)

lemma sgn_scaleR:
  "sgn (scaleR r x) = scaleR (sgn r) (sgn(x::'a::real_normed_vector))"
by (simp add: sgn_div_norm mult_ac)

lemma sgn_one [simp]: "sgn (1::'a::real_normed_algebra_1) = 1"
by (simp add: sgn_div_norm)

lemma sgn_of_real:
  "sgn (of_real r::'a::real_normed_algebra_1) = of_real (sgn r)"
unfolding of_real_def by (simp only: sgn_scaleR sgn_one)

lemma sgn_mult:
  fixes x y :: "'a::real_normed_div_algebra"
  shows "sgn (x * y) = sgn x * sgn y"
by (simp add: sgn_div_norm norm_mult mult_commute)

lemma real_sgn_eq: "sgn (x::real) = x / \<bar>x\<bar>"
by (simp add: sgn_div_norm divide_inverse)

lemma real_sgn_pos: "0 < (x::real) \<Longrightarrow> sgn x = 1"
unfolding real_sgn_eq by simp

lemma real_sgn_neg: "(x::real) < 0 \<Longrightarrow> sgn x = -1"
unfolding real_sgn_eq by simp

lemma norm_conv_dist: "norm x = dist x 0"
  unfolding dist_norm by simp

subsection {* Bounded Linear and Bilinear Operators *}

locale bounded_linear = additive f for f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector" +
  assumes scaleR: "f (scaleR r x) = scaleR r (f x)"
  assumes bounded: "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
begin

lemma pos_bounded:
  "\<exists>K>0. \<forall>x. norm (f x) \<le> norm x * K"
proof -
  obtain K where K: "\<And>x. norm (f x) \<le> norm x * K"
    using bounded by fast
  show ?thesis
  proof (intro exI impI conjI allI)
    show "0 < max 1 K"
      by (rule order_less_le_trans [OF zero_less_one le_maxI1])
  next
    fix x
    have "norm (f x) \<le> norm x * K" using K .
    also have "\<dots> \<le> norm x * max 1 K"
      by (rule mult_left_mono [OF le_maxI2 norm_ge_zero])
    finally show "norm (f x) \<le> norm x * max 1 K" .
  qed
qed

lemma nonneg_bounded:
  "\<exists>K\<ge>0. \<forall>x. norm (f x) \<le> norm x * K"
proof -
  from pos_bounded
  show ?thesis by (auto intro: order_less_imp_le)
qed

end

lemma bounded_linear_intro:
  assumes "\<And>x y. f (x + y) = f x + f y"
  assumes "\<And>r x. f (scaleR r x) = scaleR r (f x)"
  assumes "\<And>x. norm (f x) \<le> norm x * K"
  shows "bounded_linear f"
  by default (fast intro: assms)+

locale bounded_bilinear =
  fixes prod :: "['a::real_normed_vector, 'b::real_normed_vector]
                 \<Rightarrow> 'c::real_normed_vector"
    (infixl "**" 70)
  assumes add_left: "prod (a + a') b = prod a b + prod a' b"
  assumes add_right: "prod a (b + b') = prod a b + prod a b'"
  assumes scaleR_left: "prod (scaleR r a) b = scaleR r (prod a b)"
  assumes scaleR_right: "prod a (scaleR r b) = scaleR r (prod a b)"
  assumes bounded: "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
begin

lemma pos_bounded:
  "\<exists>K>0. \<forall>a b. norm (a ** b) \<le> norm a * norm b * K"
apply (cut_tac bounded, erule exE)
apply (rule_tac x="max 1 K" in exI, safe)
apply (rule order_less_le_trans [OF zero_less_one le_maxI1])
apply (drule spec, drule spec, erule order_trans)
apply (rule mult_left_mono [OF le_maxI2])
apply (intro mult_nonneg_nonneg norm_ge_zero)
done

lemma nonneg_bounded:
  "\<exists>K\<ge>0. \<forall>a b. norm (a ** b) \<le> norm a * norm b * K"
proof -
  from pos_bounded
  show ?thesis by (auto intro: order_less_imp_le)
qed

lemma additive_right: "additive (\<lambda>b. prod a b)"
by (rule additive.intro, rule add_right)

lemma additive_left: "additive (\<lambda>a. prod a b)"
by (rule additive.intro, rule add_left)

lemma zero_left: "prod 0 b = 0"
by (rule additive.zero [OF additive_left])

lemma zero_right: "prod a 0 = 0"
by (rule additive.zero [OF additive_right])

lemma minus_left: "prod (- a) b = - prod a b"
by (rule additive.minus [OF additive_left])

lemma minus_right: "prod a (- b) = - prod a b"
by (rule additive.minus [OF additive_right])

lemma diff_left:
  "prod (a - a') b = prod a b - prod a' b"
by (rule additive.diff [OF additive_left])

lemma diff_right:
  "prod a (b - b') = prod a b - prod a b'"
by (rule additive.diff [OF additive_right])

lemma bounded_linear_left:
  "bounded_linear (\<lambda>a. a ** b)"
apply (cut_tac bounded, safe)
apply (rule_tac K="norm b * K" in bounded_linear_intro)
apply (rule add_left)
apply (rule scaleR_left)
apply (simp add: mult_ac)
done

lemma bounded_linear_right:
  "bounded_linear (\<lambda>b. a ** b)"
apply (cut_tac bounded, safe)
apply (rule_tac K="norm a * K" in bounded_linear_intro)
apply (rule add_right)
apply (rule scaleR_right)
apply (simp add: mult_ac)
done

lemma prod_diff_prod:
  "(x ** y - a ** b) = (x - a) ** (y - b) + (x - a) ** b + a ** (y - b)"
by (simp add: diff_left diff_right)

end

lemma bounded_bilinear_mult:
  "bounded_bilinear (op * :: 'a \<Rightarrow> 'a \<Rightarrow> 'a::real_normed_algebra)"
apply (rule bounded_bilinear.intro)
apply (rule distrib_right)
apply (rule distrib_left)
apply (rule mult_scaleR_left)
apply (rule mult_scaleR_right)
apply (rule_tac x="1" in exI)
apply (simp add: norm_mult_ineq)
done

lemma bounded_linear_mult_left:
  "bounded_linear (\<lambda>x::'a::real_normed_algebra. x * y)"
  using bounded_bilinear_mult
  by (rule bounded_bilinear.bounded_linear_left)

lemma bounded_linear_mult_right:
  "bounded_linear (\<lambda>y::'a::real_normed_algebra. x * y)"
  using bounded_bilinear_mult
  by (rule bounded_bilinear.bounded_linear_right)

lemma bounded_linear_divide:
  "bounded_linear (\<lambda>x::'a::real_normed_field. x / y)"
  unfolding divide_inverse by (rule bounded_linear_mult_left)

lemma bounded_bilinear_scaleR: "bounded_bilinear scaleR"
apply (rule bounded_bilinear.intro)
apply (rule scaleR_left_distrib)
apply (rule scaleR_right_distrib)
apply simp
apply (rule scaleR_left_commute)
apply (rule_tac x="1" in exI, simp)
done

lemma bounded_linear_scaleR_left: "bounded_linear (\<lambda>r. scaleR r x)"
  using bounded_bilinear_scaleR
  by (rule bounded_bilinear.bounded_linear_left)

lemma bounded_linear_scaleR_right: "bounded_linear (\<lambda>x. scaleR r x)"
  using bounded_bilinear_scaleR
  by (rule bounded_bilinear.bounded_linear_right)

lemma bounded_linear_of_real: "bounded_linear (\<lambda>r. of_real r)"
  unfolding of_real_def by (rule bounded_linear_scaleR_left)

instance real_normed_algebra_1 \<subseteq> perfect_space
proof
  fix x::'a
  show "\<not> open {x}"
    unfolding open_dist dist_norm
    by (clarsimp, rule_tac x="x + of_real (e/2)" in exI, simp)
qed

end
