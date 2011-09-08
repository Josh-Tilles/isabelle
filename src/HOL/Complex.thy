(*  Title:       HOL/Complex.thy
    Author:      Jacques D. Fleuriot
    Copyright:   2001 University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2003/4
*)

header {* Complex Numbers: Rectangular and Polar Representations *}

theory Complex
imports Transcendental
begin

datatype complex = Complex real real

primrec Re :: "complex \<Rightarrow> real"
  where Re: "Re (Complex x y) = x"

primrec Im :: "complex \<Rightarrow> real"
  where Im: "Im (Complex x y) = y"

lemma complex_surj [simp]: "Complex (Re z) (Im z) = z"
  by (induct z) simp

lemma complex_eqI [intro?]: "\<lbrakk>Re x = Re y; Im x = Im y\<rbrakk> \<Longrightarrow> x = y"
  by (induct x, induct y) simp

lemma complex_eq_iff: "x = y \<longleftrightarrow> Re x = Re y \<and> Im x = Im y"
  by (induct x, induct y) simp


subsection {* Addition and Subtraction *}

instantiation complex :: ab_group_add
begin

definition complex_zero_def:
  "0 = Complex 0 0"

definition complex_add_def:
  "x + y = Complex (Re x + Re y) (Im x + Im y)"

definition complex_minus_def:
  "- x = Complex (- Re x) (- Im x)"

definition complex_diff_def:
  "x - (y\<Colon>complex) = x + - y"

lemma Complex_eq_0 [simp]: "Complex a b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  by (simp add: complex_zero_def)

lemma complex_Re_zero [simp]: "Re 0 = 0"
  by (simp add: complex_zero_def)

lemma complex_Im_zero [simp]: "Im 0 = 0"
  by (simp add: complex_zero_def)

lemma complex_add [simp]:
  "Complex a b + Complex c d = Complex (a + c) (b + d)"
  by (simp add: complex_add_def)

lemma complex_Re_add [simp]: "Re (x + y) = Re x + Re y"
  by (simp add: complex_add_def)

lemma complex_Im_add [simp]: "Im (x + y) = Im x + Im y"
  by (simp add: complex_add_def)

lemma complex_minus [simp]:
  "- (Complex a b) = Complex (- a) (- b)"
  by (simp add: complex_minus_def)

lemma complex_Re_minus [simp]: "Re (- x) = - Re x"
  by (simp add: complex_minus_def)

lemma complex_Im_minus [simp]: "Im (- x) = - Im x"
  by (simp add: complex_minus_def)

lemma complex_diff [simp]:
  "Complex a b - Complex c d = Complex (a - c) (b - d)"
  by (simp add: complex_diff_def)

lemma complex_Re_diff [simp]: "Re (x - y) = Re x - Re y"
  by (simp add: complex_diff_def)

lemma complex_Im_diff [simp]: "Im (x - y) = Im x - Im y"
  by (simp add: complex_diff_def)

instance
  by intro_classes (simp_all add: complex_add_def complex_diff_def)

end


subsection {* Multiplication and Division *}

instantiation complex :: field_inverse_zero
begin

definition complex_one_def:
  "1 = Complex 1 0"

definition complex_mult_def:
  "x * y = Complex (Re x * Re y - Im x * Im y) (Re x * Im y + Im x * Re y)"

definition complex_inverse_def:
  "inverse x =
    Complex (Re x / ((Re x)\<twosuperior> + (Im x)\<twosuperior>)) (- Im x / ((Re x)\<twosuperior> + (Im x)\<twosuperior>))"

definition complex_divide_def:
  "x / (y\<Colon>complex) = x * inverse y"

lemma Complex_eq_1 [simp]: "(Complex a b = 1) = (a = 1 \<and> b = 0)"
  by (simp add: complex_one_def)

lemma complex_Re_one [simp]: "Re 1 = 1"
  by (simp add: complex_one_def)

lemma complex_Im_one [simp]: "Im 1 = 0"
  by (simp add: complex_one_def)

lemma complex_mult [simp]:
  "Complex a b * Complex c d = Complex (a * c - b * d) (a * d + b * c)"
  by (simp add: complex_mult_def)

lemma complex_Re_mult [simp]: "Re (x * y) = Re x * Re y - Im x * Im y"
  by (simp add: complex_mult_def)

lemma complex_Im_mult [simp]: "Im (x * y) = Re x * Im y + Im x * Re y"
  by (simp add: complex_mult_def)

lemma complex_inverse [simp]:
  "inverse (Complex a b) = Complex (a / (a\<twosuperior> + b\<twosuperior>)) (- b / (a\<twosuperior> + b\<twosuperior>))"
  by (simp add: complex_inverse_def)

lemma complex_Re_inverse:
  "Re (inverse x) = Re x / ((Re x)\<twosuperior> + (Im x)\<twosuperior>)"
  by (simp add: complex_inverse_def)

lemma complex_Im_inverse:
  "Im (inverse x) = - Im x / ((Re x)\<twosuperior> + (Im x)\<twosuperior>)"
  by (simp add: complex_inverse_def)

instance
  by intro_classes (simp_all add: complex_mult_def
    right_distrib left_distrib right_diff_distrib left_diff_distrib
    complex_inverse_def complex_divide_def
    power2_eq_square add_divide_distrib [symmetric]
    complex_eq_iff)

end


subsection {* Numerals and Arithmetic *}

instantiation complex :: number_ring
begin

definition complex_number_of_def:
  "number_of w = (of_int w \<Colon> complex)"

instance
  by intro_classes (simp only: complex_number_of_def)

end

lemma complex_Re_of_nat [simp]: "Re (of_nat n) = of_nat n"
  by (induct n) simp_all

lemma complex_Im_of_nat [simp]: "Im (of_nat n) = 0"
  by (induct n) simp_all

lemma complex_Re_of_int [simp]: "Re (of_int z) = of_int z"
  by (cases z rule: int_diff_cases) simp

lemma complex_Im_of_int [simp]: "Im (of_int z) = 0"
  by (cases z rule: int_diff_cases) simp

lemma complex_Re_number_of [simp]: "Re (number_of v) = number_of v"
  unfolding number_of_eq by (rule complex_Re_of_int)

lemma complex_Im_number_of [simp]: "Im (number_of v) = 0"
  unfolding number_of_eq by (rule complex_Im_of_int)

lemma Complex_eq_number_of [simp]:
  "(Complex a b = number_of w) = (a = number_of w \<and> b = 0)"
  by (simp add: complex_eq_iff)


subsection {* Scalar Multiplication *}

instantiation complex :: real_field
begin

definition complex_scaleR_def:
  "scaleR r x = Complex (r * Re x) (r * Im x)"

lemma complex_scaleR [simp]:
  "scaleR r (Complex a b) = Complex (r * a) (r * b)"
  unfolding complex_scaleR_def by simp

lemma complex_Re_scaleR [simp]: "Re (scaleR r x) = r * Re x"
  unfolding complex_scaleR_def by simp

lemma complex_Im_scaleR [simp]: "Im (scaleR r x) = r * Im x"
  unfolding complex_scaleR_def by simp

instance
proof
  fix a b :: real and x y :: complex
  show "scaleR a (x + y) = scaleR a x + scaleR a y"
    by (simp add: complex_eq_iff right_distrib)
  show "scaleR (a + b) x = scaleR a x + scaleR b x"
    by (simp add: complex_eq_iff left_distrib)
  show "scaleR a (scaleR b x) = scaleR (a * b) x"
    by (simp add: complex_eq_iff mult_assoc)
  show "scaleR 1 x = x"
    by (simp add: complex_eq_iff)
  show "scaleR a x * y = scaleR a (x * y)"
    by (simp add: complex_eq_iff algebra_simps)
  show "x * scaleR a y = scaleR a (x * y)"
    by (simp add: complex_eq_iff algebra_simps)
qed

end


subsection{* Properties of Embedding from Reals *}

abbreviation complex_of_real :: "real \<Rightarrow> complex"
  where "complex_of_real \<equiv> of_real"

lemma complex_of_real_def: "complex_of_real r = Complex r 0"
  by (simp add: of_real_def complex_scaleR_def)

lemma Re_complex_of_real [simp]: "Re (complex_of_real z) = z"
  by (simp add: complex_of_real_def)

lemma Im_complex_of_real [simp]: "Im (complex_of_real z) = 0"
  by (simp add: complex_of_real_def)

lemma Complex_add_complex_of_real [simp]:
  shows "Complex x y + complex_of_real r = Complex (x+r) y"
  by (simp add: complex_of_real_def)

lemma complex_of_real_add_Complex [simp]:
  shows "complex_of_real r + Complex x y = Complex (r+x) y"
  by (simp add: complex_of_real_def)

lemma Complex_mult_complex_of_real:
  shows "Complex x y * complex_of_real r = Complex (x*r) (y*r)"
  by (simp add: complex_of_real_def)

lemma complex_of_real_mult_Complex:
  shows "complex_of_real r * Complex x y = Complex (r*x) (r*y)"
  by (simp add: complex_of_real_def)

lemma complex_eq_cancel_iff2 [simp]:
  shows "(Complex x y = complex_of_real xa) = (x = xa & y = 0)"
  by (simp add: complex_of_real_def)

lemma complex_split_polar:
     "\<exists>r a. z = complex_of_real r * (Complex (cos a) (sin a))"
  by (simp add: complex_eq_iff polar_Ex)


subsection {* Vector Norm *}

instantiation complex :: real_normed_field
begin

definition complex_norm_def:
  "norm z = sqrt ((Re z)\<twosuperior> + (Im z)\<twosuperior>)"

abbreviation cmod :: "complex \<Rightarrow> real"
  where "cmod \<equiv> norm"

definition complex_sgn_def:
  "sgn x = x /\<^sub>R cmod x"

definition dist_complex_def:
  "dist x y = cmod (x - y)"

definition open_complex_def:
  "open (S :: complex set) \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"

lemmas cmod_def = complex_norm_def

lemma complex_norm [simp]: "cmod (Complex x y) = sqrt (x\<twosuperior> + y\<twosuperior>)"
  by (simp add: complex_norm_def)

instance proof
  fix r :: real and x y :: complex and S :: "complex set"
  show "0 \<le> norm x"
    by (induct x) simp
  show "(norm x = 0) = (x = 0)"
    by (induct x) simp
  show "norm (x + y) \<le> norm x + norm y"
    by (induct x, induct y)
       (simp add: real_sqrt_sum_squares_triangle_ineq)
  show "norm (scaleR r x) = \<bar>r\<bar> * norm x"
    by (induct x)
       (simp add: power_mult_distrib right_distrib [symmetric] real_sqrt_mult)
  show "norm (x * y) = norm x * norm y"
    by (induct x, induct y)
       (simp add: real_sqrt_mult [symmetric] power2_eq_square algebra_simps)
  show "sgn x = x /\<^sub>R cmod x"
    by (rule complex_sgn_def)
  show "dist x y = cmod (x - y)"
    by (rule dist_complex_def)
  show "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"
    by (rule open_complex_def)
qed

end

lemma cmod_unit_one: "cmod (Complex (cos a) (sin a)) = 1"
  by simp

lemma cmod_complex_polar:
  "cmod (complex_of_real r * Complex (cos a) (sin a)) = abs r"
  by (simp add: norm_mult)

lemma complex_Re_le_cmod: "Re x \<le> cmod x"
  unfolding complex_norm_def
  by (rule real_sqrt_sum_squares_ge1)

lemma complex_mod_minus_le_complex_mod: "- cmod x \<le> cmod x"
  by (rule order_trans [OF _ norm_ge_zero], simp)

lemma complex_mod_triangle_ineq2: "cmod(b + a) - cmod b \<le> cmod a"
  by (rule ord_le_eq_trans [OF norm_triangle_ineq2], simp)

lemma abs_Re_le_cmod: "\<bar>Re x\<bar> \<le> cmod x"
  by (cases x) simp

lemma abs_Im_le_cmod: "\<bar>Im x\<bar> \<le> cmod x"
  by (cases x) simp

text {* Properties of complex signum. *}

lemma sgn_eq: "sgn z = z / complex_of_real (cmod z)"
  by (simp add: sgn_div_norm divide_inverse scaleR_conv_of_real mult_commute)

lemma Re_sgn [simp]: "Re(sgn z) = Re(z)/cmod z"
  by (simp add: complex_sgn_def divide_inverse)

lemma Im_sgn [simp]: "Im(sgn z) = Im(z)/cmod z"
  by (simp add: complex_sgn_def divide_inverse)


subsection {* Completeness of the Complexes *}

lemma bounded_linear_Re: "bounded_linear Re"
  by (rule bounded_linear_intro [where K=1], simp_all add: complex_norm_def)

lemma bounded_linear_Im: "bounded_linear Im"
  by (rule bounded_linear_intro [where K=1], simp_all add: complex_norm_def)

lemmas tendsto_Re [tendsto_intros] =
  bounded_linear.tendsto [OF bounded_linear_Re]

lemmas tendsto_Im [tendsto_intros] =
  bounded_linear.tendsto [OF bounded_linear_Im]

lemmas isCont_Re [simp] = bounded_linear.isCont [OF bounded_linear_Re]
lemmas isCont_Im [simp] = bounded_linear.isCont [OF bounded_linear_Im]
lemmas Cauchy_Re = bounded_linear.Cauchy [OF bounded_linear_Re]
lemmas Cauchy_Im = bounded_linear.Cauchy [OF bounded_linear_Im]

lemma tendsto_Complex [tendsto_intros]:
  assumes "(f ---> a) F" and "(g ---> b) F"
  shows "((\<lambda>x. Complex (f x) (g x)) ---> Complex a b) F"
proof (rule tendstoI)
  fix r :: real assume "0 < r"
  hence "0 < r / sqrt 2" by (simp add: divide_pos_pos)
  have "eventually (\<lambda>x. dist (f x) a < r / sqrt 2) F"
    using `(f ---> a) F` and `0 < r / sqrt 2` by (rule tendstoD)
  moreover
  have "eventually (\<lambda>x. dist (g x) b < r / sqrt 2) F"
    using `(g ---> b) F` and `0 < r / sqrt 2` by (rule tendstoD)
  ultimately
  show "eventually (\<lambda>x. dist (Complex (f x) (g x)) (Complex a b) < r) F"
    by (rule eventually_elim2)
       (simp add: dist_norm real_sqrt_sum_squares_less)
qed

instance complex :: banach
proof
  fix X :: "nat \<Rightarrow> complex"
  assume X: "Cauchy X"
  from Cauchy_Re [OF X] have 1: "(\<lambda>n. Re (X n)) ----> lim (\<lambda>n. Re (X n))"
    by (simp add: Cauchy_convergent_iff convergent_LIMSEQ_iff)
  from Cauchy_Im [OF X] have 2: "(\<lambda>n. Im (X n)) ----> lim (\<lambda>n. Im (X n))"
    by (simp add: Cauchy_convergent_iff convergent_LIMSEQ_iff)
  have "X ----> Complex (lim (\<lambda>n. Re (X n))) (lim (\<lambda>n. Im (X n)))"
    using tendsto_Complex [OF 1 2] by simp
  thus "convergent X"
    by (rule convergentI)
qed


subsection {* The Complex Number $i$ *}

definition "ii" :: complex  ("\<i>")
  where i_def: "ii \<equiv> Complex 0 1"

lemma complex_Re_i [simp]: "Re ii = 0"
  by (simp add: i_def)

lemma complex_Im_i [simp]: "Im ii = 1"
  by (simp add: i_def)

lemma Complex_eq_i [simp]: "(Complex x y = ii) = (x = 0 \<and> y = 1)"
  by (simp add: i_def)

lemma complex_i_not_zero [simp]: "ii \<noteq> 0"
  by (simp add: complex_eq_iff)

lemma complex_i_not_one [simp]: "ii \<noteq> 1"
  by (simp add: complex_eq_iff)

lemma complex_i_not_number_of [simp]: "ii \<noteq> number_of w"
  by (simp add: complex_eq_iff)

lemma i_mult_Complex [simp]: "ii * Complex a b = Complex (- b) a"
  by (simp add: complex_eq_iff)

lemma Complex_mult_i [simp]: "Complex a b * ii = Complex (- b) a"
  by (simp add: complex_eq_iff)

lemma i_complex_of_real [simp]: "ii * complex_of_real r = Complex 0 r"
  by (simp add: i_def complex_of_real_def)

lemma complex_of_real_i [simp]: "complex_of_real r * ii = Complex 0 r"
  by (simp add: i_def complex_of_real_def)

lemma i_squared [simp]: "ii * ii = -1"
  by (simp add: i_def)

lemma power2_i [simp]: "ii\<twosuperior> = -1"
  by (simp add: power2_eq_square)

lemma inverse_i [simp]: "inverse ii = - ii"
  by (rule inverse_unique, simp)

lemma complex_i_mult_minus [simp]: "ii * (ii * x) = - x"
  by (simp add: mult_assoc [symmetric])


subsection {* Complex Conjugation *}

definition cnj :: "complex \<Rightarrow> complex" where
  "cnj z = Complex (Re z) (- Im z)"

lemma complex_cnj [simp]: "cnj (Complex a b) = Complex a (- b)"
  by (simp add: cnj_def)

lemma complex_Re_cnj [simp]: "Re (cnj x) = Re x"
  by (simp add: cnj_def)

lemma complex_Im_cnj [simp]: "Im (cnj x) = - Im x"
  by (simp add: cnj_def)

lemma complex_cnj_cancel_iff [simp]: "(cnj x = cnj y) = (x = y)"
  by (simp add: complex_eq_iff)

lemma complex_cnj_cnj [simp]: "cnj (cnj z) = z"
  by (simp add: cnj_def)

lemma complex_cnj_zero [simp]: "cnj 0 = 0"
  by (simp add: complex_eq_iff)

lemma complex_cnj_zero_iff [iff]: "(cnj z = 0) = (z = 0)"
  by (simp add: complex_eq_iff)

lemma complex_cnj_add: "cnj (x + y) = cnj x + cnj y"
  by (simp add: complex_eq_iff)

lemma complex_cnj_diff: "cnj (x - y) = cnj x - cnj y"
  by (simp add: complex_eq_iff)

lemma complex_cnj_minus: "cnj (- x) = - cnj x"
  by (simp add: complex_eq_iff)

lemma complex_cnj_one [simp]: "cnj 1 = 1"
  by (simp add: complex_eq_iff)

lemma complex_cnj_mult: "cnj (x * y) = cnj x * cnj y"
  by (simp add: complex_eq_iff)

lemma complex_cnj_inverse: "cnj (inverse x) = inverse (cnj x)"
  by (simp add: complex_inverse_def)

lemma complex_cnj_divide: "cnj (x / y) = cnj x / cnj y"
  by (simp add: complex_divide_def complex_cnj_mult complex_cnj_inverse)

lemma complex_cnj_power: "cnj (x ^ n) = cnj x ^ n"
  by (induct n, simp_all add: complex_cnj_mult)

lemma complex_cnj_of_nat [simp]: "cnj (of_nat n) = of_nat n"
  by (simp add: complex_eq_iff)

lemma complex_cnj_of_int [simp]: "cnj (of_int z) = of_int z"
  by (simp add: complex_eq_iff)

lemma complex_cnj_number_of [simp]: "cnj (number_of w) = number_of w"
  by (simp add: complex_eq_iff)

lemma complex_cnj_scaleR: "cnj (scaleR r x) = scaleR r (cnj x)"
  by (simp add: complex_eq_iff)

lemma complex_mod_cnj [simp]: "cmod (cnj z) = cmod z"
  by (simp add: complex_norm_def)

lemma complex_cnj_complex_of_real [simp]: "cnj (of_real x) = of_real x"
  by (simp add: complex_eq_iff)

lemma complex_cnj_i [simp]: "cnj ii = - ii"
  by (simp add: complex_eq_iff)

lemma complex_add_cnj: "z + cnj z = complex_of_real (2 * Re z)"
  by (simp add: complex_eq_iff)

lemma complex_diff_cnj: "z - cnj z = complex_of_real (2 * Im z) * ii"
  by (simp add: complex_eq_iff)

lemma complex_mult_cnj: "z * cnj z = complex_of_real ((Re z)\<twosuperior> + (Im z)\<twosuperior>)"
  by (simp add: complex_eq_iff power2_eq_square)

lemma complex_mod_mult_cnj: "cmod (z * cnj z) = (cmod z)\<twosuperior>"
  by (simp add: norm_mult power2_eq_square)

lemma complex_mod_sqrt_Re_mult_cnj: "cmod z = sqrt (Re (z * cnj z))"
  by (simp add: cmod_def power2_eq_square)

lemma complex_In_mult_cnj_zero [simp]: "Im (z * cnj z) = 0"
  by simp

lemma bounded_linear_cnj: "bounded_linear cnj"
  using complex_cnj_add complex_cnj_scaleR
  by (rule bounded_linear_intro [where K=1], simp)

lemmas tendsto_cnj [tendsto_intros] =
  bounded_linear.tendsto [OF bounded_linear_cnj]

lemmas isCont_cnj [simp] =
  bounded_linear.isCont [OF bounded_linear_cnj]


subsection {* Complex Argument *}

definition arg :: "complex => real" where
  "arg z = (SOME a. Re(sgn z) = cos a & Im(sgn z) = sin a & -pi < a & a \<le> pi)"

(*----------------------------------------------------------------------------*)
(* Many of the theorems below need to be moved elsewhere e.g. Transc. Also *)
(* many of the theorems are not used - so should they be kept?                *)
(*----------------------------------------------------------------------------*)

lemma cos_arg_i_mult_zero_pos:
   "0 < y ==> cos (arg(Complex 0 y)) = 0"
apply (simp add: arg_def abs_if)
apply (rule_tac a = "pi/2" in someI2, auto)
apply (rule order_less_trans [of _ 0], auto)
done

lemma cos_arg_i_mult_zero_neg:
   "y < 0 ==> cos (arg(Complex 0 y)) = 0"
apply (simp add: arg_def abs_if)
apply (rule_tac a = "- pi/2" in someI2, auto)
apply (rule order_trans [of _ 0], auto)
done

lemma cos_arg_i_mult_zero [simp]:
     "y \<noteq> 0 ==> cos (arg(Complex 0 y)) = 0"
by (auto simp add: linorder_neq_iff cos_arg_i_mult_zero_pos cos_arg_i_mult_zero_neg)


subsection{*Finally! Polar Form for Complex Numbers*}

subsubsection {* $\cos \theta + i \sin \theta$ *}

definition cis :: "real \<Rightarrow> complex" where
  "cis a = Complex (cos a) (sin a)"

lemma Re_cis [simp]: "Re (cis a) = cos a"
  by (simp add: cis_def)

lemma Im_cis [simp]: "Im (cis a) = sin a"
  by (simp add: cis_def)

lemma cis_zero [simp]: "cis 0 = 1"
  by (simp add: cis_def)

lemma norm_cis [simp]: "norm (cis a) = 1"
  by (simp add: cis_def)

lemma sgn_cis [simp]: "sgn (cis a) = cis a"
  by (simp add: sgn_div_norm)

lemma cis_neq_zero [simp]: "cis a \<noteq> 0"
  by (metis norm_cis norm_zero zero_neq_one)

lemma cis_mult: "cis a * cis b = cis (a + b)"
  by (simp add: cis_def cos_add sin_add)

lemma DeMoivre: "(cis a) ^ n = cis (real n * a)"
  by (induct n, simp_all add: real_of_nat_Suc algebra_simps cis_mult)

lemma cis_inverse [simp]: "inverse(cis a) = cis (-a)"
  by (simp add: cis_def)

lemma cis_divide: "cis a / cis b = cis (a - b)"
  by (simp add: complex_divide_def cis_mult diff_minus)

lemma cos_n_Re_cis_pow_n: "cos (real n * a) = Re(cis a ^ n)"
  by (auto simp add: DeMoivre)

lemma sin_n_Im_cis_pow_n: "sin (real n * a) = Im(cis a ^ n)"
  by (auto simp add: DeMoivre)

subsubsection {* $r(\cos \theta + i \sin \theta)$ *}

definition rcis :: "[real, real] \<Rightarrow> complex" where
  "rcis r a = complex_of_real r * cis a"

lemma Re_rcis [simp]: "Re(rcis r a) = r * cos a"
  by (simp add: rcis_def)

lemma Im_rcis [simp]: "Im(rcis r a) = r * sin a"
  by (simp add: rcis_def)

lemma rcis_Ex: "\<exists>r a. z = rcis r a"
  by (simp add: complex_eq_iff polar_Ex)

lemma complex_mod_rcis [simp]: "cmod(rcis r a) = abs r"
  by (simp add: rcis_def norm_mult)

lemma cis_rcis_eq: "cis a = rcis 1 a"
  by (simp add: rcis_def)

lemma rcis_mult: "rcis r1 a * rcis r2 b = rcis (r1*r2) (a + b)"
  by (simp add: rcis_def cis_mult)

lemma rcis_zero_mod [simp]: "rcis 0 a = 0"
  by (simp add: rcis_def)

lemma rcis_zero_arg [simp]: "rcis r 0 = complex_of_real r"
  by (simp add: rcis_def)

lemma rcis_eq_zero_iff [simp]: "rcis r a = 0 \<longleftrightarrow> r = 0"
  by (simp add: rcis_def)

lemma DeMoivre2: "(rcis r a) ^ n = rcis (r ^ n) (real n * a)"
  by (simp add: rcis_def power_mult_distrib DeMoivre)

lemma rcis_inverse: "inverse(rcis r a) = rcis (1/r) (-a)"
  by (simp add: divide_inverse rcis_def)

lemma rcis_divide: "rcis r1 a / rcis r2 b = rcis (r1/r2) (a - b)"
  by (simp add: rcis_def cis_divide [symmetric])

subsubsection {* Complex exponential *}

abbreviation expi :: "complex \<Rightarrow> complex"
  where "expi \<equiv> exp"

lemma cis_conv_exp: "cis b = exp (Complex 0 b)"
proof (rule complex_eqI)
  { fix n have "Complex 0 b ^ n =
    real (fact n) *\<^sub>R Complex (cos_coeff n * b ^ n) (sin_coeff n * b ^ n)"
      apply (induct n)
      apply (simp add: cos_coeff_def sin_coeff_def)
      apply (simp add: sin_coeff_Suc cos_coeff_Suc del: mult_Suc)
      done } note * = this
  show "Re (cis b) = Re (exp (Complex 0 b))"
    unfolding exp_def cis_def cos_def
    by (subst bounded_linear.suminf[OF bounded_linear_Re summable_exp_generic],
      simp add: * mult_assoc [symmetric])
  show "Im (cis b) = Im (exp (Complex 0 b))"
    unfolding exp_def cis_def sin_def
    by (subst bounded_linear.suminf[OF bounded_linear_Im summable_exp_generic],
      simp add: * mult_assoc [symmetric])
qed

lemma expi_def: "expi z = complex_of_real (exp (Re z)) * cis (Im z)"
  unfolding cis_conv_exp exp_of_real [symmetric] mult_exp_exp by simp

lemma Re_exp: "Re (exp z) = exp (Re z) * cos (Im z)"
  unfolding expi_def by simp

lemma Im_exp: "Im (exp z) = exp (Re z) * sin (Im z)"
  unfolding expi_def by simp

lemma complex_expi_Ex: "\<exists>a r. z = complex_of_real r * expi a"
apply (insert rcis_Ex [of z])
apply (auto simp add: expi_def rcis_def mult_assoc [symmetric])
apply (rule_tac x = "ii * complex_of_real a" in exI, auto)
done

lemma expi_two_pi_i [simp]: "expi((2::complex) * complex_of_real pi * ii) = 1"
  by (simp add: expi_def cis_def)

text {* Legacy theorem names *}

lemmas expand_complex_eq = complex_eq_iff
lemmas complex_Re_Im_cancel_iff = complex_eq_iff
lemmas complex_equality = complex_eqI

end
