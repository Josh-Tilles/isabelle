(*  Title:       Complex.thy
    ID:      $Id$
    Author:      Jacques D. Fleuriot
    Copyright:   2001 University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2003/4
*)

header {* Complex Numbers: Rectangular and Polar Representations *}

theory Complex
imports "../Hyperreal/HLog"
begin

datatype complex = Complex real real

instance complex :: "{zero, one, plus, times, minus, inverse, power}" ..

consts
  "ii"    :: complex    ("\<i>")

consts Re :: "complex => real"
primrec Re: "Re (Complex x y) = x"

consts Im :: "complex => real"
primrec Im: "Im (Complex x y) = y"

lemma complex_surj [simp]: "Complex (Re z) (Im z) = z"
  by (induct z) simp

defs (overloaded)

  complex_zero_def:
  "0 == Complex 0 0"

  complex_one_def:
  "1 == Complex 1 0"

  i_def: "ii == Complex 0 1"

  complex_minus_def: "- z == Complex (- Re z) (- Im z)"

  complex_inverse_def:
   "inverse z ==
    Complex (Re z / ((Re z)\<twosuperior> + (Im z)\<twosuperior>)) (- Im z / ((Re z)\<twosuperior> + (Im z)\<twosuperior>))"

  complex_add_def:
    "z + w == Complex (Re z + Re w) (Im z + Im w)"

  complex_diff_def:
    "z - w == z + - (w::complex)"

  complex_mult_def:
    "z * w == Complex (Re z * Re w - Im z * Im w) (Re z * Im w + Im z * Re w)"

  complex_divide_def: "w / (z::complex) == w * inverse z"


lemma complex_equality [intro?]: "Re z = Re w ==> Im z = Im w ==> z = w"
  by (induct z, induct w) simp

lemma complex_Re_Im_cancel_iff: "(w=z) = (Re(w) = Re(z) & Im(w) = Im(z))"
by (induct w, induct z, simp)

lemma complex_Re_zero [simp]: "Re 0 = 0"
by (simp add: complex_zero_def)

lemma complex_Im_zero [simp]: "Im 0 = 0"
by (simp add: complex_zero_def)

lemma complex_Re_one [simp]: "Re 1 = 1"
by (simp add: complex_one_def)

lemma complex_Im_one [simp]: "Im 1 = 0"
by (simp add: complex_one_def)

lemma complex_Re_i [simp]: "Re(ii) = 0"
by (simp add: i_def)

lemma complex_Im_i [simp]: "Im(ii) = 1"
by (simp add: i_def)


subsection{*Unary Minus*}

lemma complex_minus [simp]: "- (Complex x y) = Complex (-x) (-y)"
by (simp add: complex_minus_def)

lemma complex_Re_minus [simp]: "Re (-z) = - Re z"
by (simp add: complex_minus_def)

lemma complex_Im_minus [simp]: "Im (-z) = - Im z"
by (simp add: complex_minus_def)


subsection{*Addition*}

lemma complex_add [simp]:
     "Complex x1 y1 + Complex x2 y2 = Complex (x1+x2) (y1+y2)"
by (simp add: complex_add_def)

lemma complex_Re_add [simp]: "Re(x + y) = Re(x) + Re(y)"
by (simp add: complex_add_def)

lemma complex_Im_add [simp]: "Im(x + y) = Im(x) + Im(y)"
by (simp add: complex_add_def)

lemma complex_add_commute: "(u::complex) + v = v + u"
by (simp add: complex_add_def add_commute)

lemma complex_add_assoc: "((u::complex) + v) + w = u + (v + w)"
by (simp add: complex_add_def add_assoc)

lemma complex_add_zero_left: "(0::complex) + z = z"
by (simp add: complex_add_def complex_zero_def)

lemma complex_add_zero_right: "z + (0::complex) = z"
by (simp add: complex_add_def complex_zero_def)

lemma complex_add_minus_left: "-z + z = (0::complex)"
by (simp add: complex_add_def complex_minus_def complex_zero_def)

lemma complex_diff:
      "Complex x1 y1 - Complex x2 y2 = Complex (x1-x2) (y1-y2)"
by (simp add: complex_add_def complex_minus_def complex_diff_def)

lemma complex_Re_diff [simp]: "Re(x - y) = Re(x) - Re(y)"
by (simp add: complex_diff_def)

lemma complex_Im_diff [simp]: "Im(x - y) = Im(x) - Im(y)"
by (simp add: complex_diff_def)


subsection{*Multiplication*}

lemma complex_mult [simp]:
     "Complex x1 y1 * Complex x2 y2 = Complex (x1*x2 - y1*y2) (x1*y2 + y1*x2)"
by (simp add: complex_mult_def)

lemma complex_mult_commute: "(w::complex) * z = z * w"
by (simp add: complex_mult_def mult_commute add_commute)

lemma complex_mult_assoc: "((u::complex) * v) * w = u * (v * w)"
by (simp add: complex_mult_def mult_ac add_ac
              right_diff_distrib right_distrib left_diff_distrib left_distrib)

lemma complex_mult_one_left: "(1::complex) * z = z"
by (simp add: complex_mult_def complex_one_def)

lemma complex_mult_one_right: "z * (1::complex) = z"
by (simp add: complex_mult_def complex_one_def)


subsection{*Inverse*}

lemma complex_inverse [simp]:
     "inverse (Complex x y) = Complex (x/(x ^ 2 + y ^ 2)) (-y/(x ^ 2 + y ^ 2))"
by (simp add: complex_inverse_def)

lemma complex_mult_inv_left: "z \<noteq> (0::complex) ==> inverse(z) * z = 1"
apply (induct z)
apply (rename_tac x y)
apply (auto simp add: times_divide_eq complex_mult complex_inverse 
             complex_one_def complex_zero_def add_divide_distrib [symmetric] 
             power2_eq_square mult_ac)
apply (simp_all add: real_sum_squares_not_zero real_sum_squares_not_zero2) 
done


subsection {* The field of complex numbers *}

instance complex :: field
proof
  fix z u v w :: complex
  show "(u + v) + w = u + (v + w)"
    by (rule complex_add_assoc)
  show "z + w = w + z"
    by (rule complex_add_commute)
  show "0 + z = z"
    by (rule complex_add_zero_left)
  show "-z + z = 0"
    by (rule complex_add_minus_left)
  show "z - w = z + -w"
    by (simp add: complex_diff_def)
  show "(u * v) * w = u * (v * w)"
    by (rule complex_mult_assoc)
  show "z * w = w * z"
    by (rule complex_mult_commute)
  show "1 * z = z"
    by (rule complex_mult_one_left)
  show "0 \<noteq> (1::complex)"
    by (simp add: complex_zero_def complex_one_def)
  show "(u + v) * w = u * w + v * w"
    by (simp add: complex_mult_def complex_add_def left_distrib 
                  diff_minus add_ac)
  show "z / w = z * inverse w"
    by (simp add: complex_divide_def)
  assume "w \<noteq> 0"
  thus "inverse w * w = 1"
    by (simp add: complex_mult_inv_left)
qed

instance complex :: division_by_zero
proof
  show "inverse 0 = (0::complex)"
    by (simp add: complex_inverse_def complex_zero_def)
qed


subsection{*The real algebra of complex numbers*}

instance complex :: scaleR ..

defs (overloaded)
  complex_scaleR_def: "r *# x == Complex r 0 * x"

instance complex :: real_algebra_1
proof
  fix a b :: real
  fix x y :: complex
  show "a *# (x + y) = a *# x + a *# y"
    by (simp add: complex_scaleR_def right_distrib)
  show "(a + b) *# x = a *# x + b *# x"
    by (simp add: complex_scaleR_def left_distrib [symmetric])
  show "(a * b) *# x = a *# b *# x"
    by (simp add: complex_scaleR_def mult_assoc [symmetric])
  show "1 *# x = x"
    by (simp add: complex_scaleR_def complex_one_def [symmetric])
  show "a *# x * y = a *# (x * y)"
    by (simp add: complex_scaleR_def mult_assoc)
  show "x * a *# y = a *# (x * y)"
    by (simp add: complex_scaleR_def mult_left_commute)
qed


subsection{*Embedding Properties for @{term complex_of_real} Map*}

abbreviation
  complex_of_real :: "real => complex"
  "complex_of_real == of_real"

lemma complex_of_real_def: "complex_of_real r = Complex r 0"
by (simp add: of_real_def complex_scaleR_def)

lemma Re_complex_of_real [simp]: "Re (complex_of_real z) = z"
by (simp add: complex_of_real_def)

lemma Im_complex_of_real [simp]: "Im (complex_of_real z) = 0"
by (simp add: complex_of_real_def)

lemma Complex_add_complex_of_real [simp]:
     "Complex x y + complex_of_real r = Complex (x+r) y"
by (simp add: complex_of_real_def)

lemma complex_of_real_add_Complex [simp]:
     "complex_of_real r + Complex x y = Complex (r+x) y"
by (simp add: i_def complex_of_real_def)

lemma Complex_mult_complex_of_real:
     "Complex x y * complex_of_real r = Complex (x*r) (y*r)"
by (simp add: complex_of_real_def)

lemma complex_of_real_mult_Complex:
     "complex_of_real r * Complex x y = Complex (r*x) (r*y)"
by (simp add: i_def complex_of_real_def)

lemma i_complex_of_real [simp]: "ii * complex_of_real r = Complex 0 r"
by (simp add: i_def complex_of_real_def)

lemma complex_of_real_i [simp]: "complex_of_real r * ii = Complex 0 r"
by (simp add: i_def complex_of_real_def)

(* TODO: generalize and move to Real/RealVector.thy *)
lemma complex_of_real_inverse [simp]:
     "complex_of_real(inverse x) = inverse(complex_of_real x)"
apply (case_tac "x=0", simp)
apply (simp add: complex_of_real_def divide_inverse power2_eq_square)
done

(* TODO: generalize and move to Real/RealVector.thy *)
lemma complex_of_real_divide [simp]:
      "complex_of_real(x/y) = complex_of_real x / complex_of_real y"
apply (simp add: complex_divide_def)
apply (case_tac "y=0", simp)
apply (simp add: divide_inverse)
done


subsection{*The Functions @{term Re} and @{term Im}*}

lemma complex_Re_mult_eq: "Re (w * z) = Re w * Re z - Im w * Im z"
by (induct z, induct w, simp add: complex_mult)

lemma complex_Im_mult_eq: "Im (w * z) = Re w * Im z + Im w * Re z"
by (induct z, induct w, simp add: complex_mult)

lemma Re_i_times [simp]: "Re(ii * z) = - Im z"
by (simp add: complex_Re_mult_eq) 

lemma Re_times_i [simp]: "Re(z * ii) = - Im z"
by (simp add: complex_Re_mult_eq) 

lemma Im_i_times [simp]: "Im(ii * z) = Re z"
by (simp add: complex_Im_mult_eq) 

lemma Im_times_i [simp]: "Im(z * ii) = Re z"
by (simp add: complex_Im_mult_eq) 

lemma complex_Re_mult: "[| Im w = 0; Im z = 0 |] ==> Re(w * z) = Re(w) * Re(z)"
by (simp add: complex_Re_mult_eq)

lemma complex_Re_mult_complex_of_real [simp]:
     "Re (z * complex_of_real c) = Re(z) * c"
by (simp add: complex_Re_mult_eq)

lemma complex_Im_mult_complex_of_real [simp]:
     "Im (z * complex_of_real c) = Im(z) * c"
by (simp add: complex_Im_mult_eq)

lemma complex_Re_mult_complex_of_real2 [simp]:
     "Re (complex_of_real c * z) = c * Re(z)"
by (simp add: complex_Re_mult_eq)

lemma complex_Im_mult_complex_of_real2 [simp]:
     "Im (complex_of_real c * z) = c * Im(z)"
by (simp add: complex_Im_mult_eq)


subsection{*Conjugation is an Automorphism*}

definition
  cnj :: "complex => complex"
  "cnj z = Complex (Re z) (-Im z)"

lemma complex_cnj: "cnj (Complex x y) = Complex x (-y)"
by (simp add: cnj_def)

lemma complex_cnj_cancel_iff [simp]: "(cnj x = cnj y) = (x = y)"
by (simp add: cnj_def complex_Re_Im_cancel_iff)

lemma complex_cnj_cnj [simp]: "cnj (cnj z) = z"
by (simp add: cnj_def)

lemma complex_cnj_complex_of_real [simp]:
     "cnj (complex_of_real x) = complex_of_real x"
by (simp add: complex_of_real_def complex_cnj)

lemma complex_cnj_minus: "cnj (-z) = - cnj z"
by (simp add: cnj_def complex_minus complex_Re_minus complex_Im_minus)

lemma complex_cnj_inverse: "cnj(inverse z) = inverse(cnj z)"
by (induct z, simp add: complex_cnj complex_inverse power2_eq_square)

lemma complex_cnj_add: "cnj(w + z) = cnj(w) + cnj(z)"
by (induct w, induct z, simp add: complex_cnj complex_add)

lemma complex_cnj_diff: "cnj(w - z) = cnj(w) - cnj(z)"
by (simp add: diff_minus complex_cnj_add complex_cnj_minus)

lemma complex_cnj_mult: "cnj(w * z) = cnj(w) * cnj(z)"
by (induct w, induct z, simp add: complex_cnj complex_mult)

lemma complex_cnj_divide: "cnj(w / z) = (cnj w)/(cnj z)"
by (simp add: complex_divide_def complex_cnj_mult complex_cnj_inverse)

lemma complex_cnj_one [simp]: "cnj 1 = 1"
by (simp add: cnj_def complex_one_def)

lemma complex_add_cnj: "z + cnj z = complex_of_real (2 * Re(z))"
by (induct z, simp add: complex_add complex_cnj complex_of_real_def)

lemma complex_diff_cnj: "z - cnj z = complex_of_real (2 * Im(z)) * ii"
apply (induct z)
apply (simp add: complex_add complex_cnj complex_of_real_def diff_minus
                 complex_minus i_def complex_mult)
done

lemma complex_cnj_zero [simp]: "cnj 0 = 0"
by (simp add: cnj_def complex_zero_def)

lemma complex_cnj_zero_iff [iff]: "(cnj z = 0) = (z = 0)"
by (induct z, simp add: complex_zero_def complex_cnj)

lemma complex_mult_cnj: "z * cnj z = complex_of_real (Re(z) ^ 2 + Im(z) ^ 2)"
by (induct z,
    simp add: complex_cnj complex_mult complex_of_real_def power2_eq_square)


subsection{*Modulus*}

instance complex :: norm ..

defs (overloaded)
  complex_norm_def: "norm z == sqrt(Re(z) ^ 2 + Im(z) ^ 2)"

abbreviation
  cmod :: "complex => real"
  "cmod == norm"

lemmas cmod_def = complex_norm_def

lemma complex_mod [simp]: "cmod (Complex x y) = sqrt(x ^ 2 + y ^ 2)"
by (simp add: cmod_def)

lemma complex_mod_zero [simp]: "cmod(0) = 0"
by (simp add: cmod_def)

lemma complex_mod_one [simp]: "cmod(1) = 1"
by (simp add: cmod_def power2_eq_square)

lemma complex_mod_complex_of_real [simp]: "cmod(complex_of_real x) = abs x"
by (simp add: complex_of_real_def power2_eq_square complex_mod)

lemma complex_of_real_abs:
     "complex_of_real (abs x) = complex_of_real(cmod(complex_of_real x))"
by simp

lemma complex_mod_eq_zero_cancel [simp]: "(cmod x = 0) = (x = 0)"
apply (induct x)
apply (auto iff: real_0_le_add_iff 
            intro: real_sum_squares_cancel real_sum_squares_cancel2
            simp add: complex_mod complex_zero_def power2_eq_square)
done

lemma complex_mod_complex_of_real_of_nat [simp]:
     "cmod (complex_of_real(real (n::nat))) = real n"
by simp

lemma complex_mod_minus [simp]: "cmod (-x) = cmod(x)"
by (induct x, simp add: complex_mod complex_minus power2_eq_square)

lemma complex_mod_cnj [simp]: "cmod (cnj z) = cmod z"
by (induct z, simp add: complex_cnj complex_mod power2_eq_square)

lemma complex_mod_mult_cnj: "cmod(z * cnj(z)) = cmod(z) ^ 2"
apply (induct z, simp add: complex_mod complex_cnj complex_mult)
apply (simp add: power2_eq_square abs_if linorder_not_less real_0_le_add_iff)
done

lemma complex_mod_squared: "cmod(Complex x y) ^ 2 = x ^ 2 + y ^ 2"
by (simp add: cmod_def)

lemma complex_mod_ge_zero [simp]: "0 \<le> cmod x"
by (simp add: cmod_def)

lemma abs_cmod_cancel [simp]: "abs(cmod x) = cmod x"
by (simp add: abs_if linorder_not_less)

lemma complex_mod_mult: "cmod(x*y) = cmod(x) * cmod(y)"
apply (induct x, induct y)
apply (auto simp add: complex_mult complex_mod real_sqrt_mult_distrib2[symmetric])
apply (rule_tac n = 1 in power_inject_base)
apply (auto simp add: power2_eq_square [symmetric] simp del: realpow_Suc)
apply (auto simp add: real_diff_def power2_eq_square right_distrib left_distrib 
                      add_ac mult_ac)
done

lemma cmod_unit_one [simp]: "cmod (Complex (cos a) (sin a)) = 1"
by (simp add: cmod_def) 

lemma cmod_complex_polar [simp]:
     "cmod (complex_of_real r * Complex (cos a) (sin a)) = abs r"
by (simp only: cmod_unit_one complex_mod_mult, simp) 

lemma complex_mod_add_squared_eq:
     "cmod(x + y) ^ 2 = cmod(x) ^ 2 + cmod(y) ^ 2 + 2 * Re(x * cnj y)"
apply (induct x, induct y)
apply (auto simp add: complex_add complex_mod_squared complex_mult complex_cnj real_diff_def simp del: realpow_Suc)
apply (auto simp add: right_distrib left_distrib power2_eq_square mult_ac add_ac)
done

lemma complex_Re_mult_cnj_le_cmod [simp]: "Re(x * cnj y) \<le> cmod(x * cnj y)"
apply (induct x, induct y)
apply (auto simp add: complex_mod complex_mult complex_cnj real_diff_def simp del: realpow_Suc)
done

lemma complex_Re_mult_cnj_le_cmod2 [simp]: "Re(x * cnj y) \<le> cmod(x * y)"
by (insert complex_Re_mult_cnj_le_cmod [of x y], simp add: complex_mod_mult)

lemma real_sum_squared_expand:
     "((x::real) + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y"
by (simp add: left_distrib right_distrib power2_eq_square)

lemma complex_mod_triangle_squared [simp]:
     "cmod (x + y) ^ 2 \<le> (cmod(x) + cmod(y)) ^ 2"
by (simp add: real_sum_squared_expand complex_mod_add_squared_eq real_mult_assoc complex_mod_mult [symmetric])

lemma complex_mod_minus_le_complex_mod [simp]: "- cmod x \<le> cmod x"
by (rule order_trans [OF _ complex_mod_ge_zero], simp)

lemma complex_mod_triangle_ineq [simp]: "cmod (x + y) \<le> cmod(x) + cmod(y)"
apply (rule_tac n = 1 in realpow_increasing)
apply (auto intro:  order_trans [OF _ complex_mod_ge_zero]
            simp add: add_increasing power2_eq_square [symmetric])
done

instance complex :: real_normed_div_algebra
proof
  fix r :: real
  fix x y :: complex
  show "0 \<le> cmod x"
    by (rule complex_mod_ge_zero)
  show "(cmod x = 0) = (x = 0)"
    by (rule complex_mod_eq_zero_cancel)
  show "cmod (x + y) \<le> cmod x + cmod y"
    by (rule complex_mod_triangle_ineq)
  show "cmod (of_real r) = abs r"
    by (rule complex_mod_complex_of_real)
  show "cmod (x * y) = cmod x * cmod y"
    by (rule complex_mod_mult)
  show "cmod 1 = 1"
    by (rule complex_mod_one)
qed

lemma complex_mod_triangle_ineq2 [simp]: "cmod(b + a) - cmod b \<le> cmod a"
by (insert complex_mod_triangle_ineq [THEN add_right_mono, of b a"-cmod b"], simp)

lemma complex_mod_diff_commute: "cmod (x - y) = cmod (y - x)"
by (rule norm_minus_commute)

lemma complex_mod_add_less:
     "[| cmod x < r; cmod y < s |] ==> cmod (x + y) < r + s"
by (auto intro: order_le_less_trans complex_mod_triangle_ineq)

lemma complex_mod_mult_less:
     "[| cmod x < r; cmod y < s |] ==> cmod (x * y) < r * s"
by (auto intro: real_mult_less_mono' simp add: complex_mod_mult)

lemma complex_mod_diff_ineq [simp]: "cmod(a) - cmod(b) \<le> cmod(a + b)"
apply (rule linorder_cases [of "cmod(a)" "cmod (b)"])
apply auto
apply (rule order_trans [of _ 0], rule order_less_imp_le)
apply (simp add: compare_rls, simp)
apply (simp add: compare_rls)
apply (rule complex_mod_minus [THEN subst])
apply (rule order_trans)
apply (rule_tac [2] complex_mod_triangle_ineq)
apply (auto simp add: add_ac)
done

lemma complex_Re_le_cmod [simp]: "Re z \<le> cmod z"
by (induct z, simp add: complex_mod del: realpow_Suc)

lemma complex_mod_gt_zero: "z \<noteq> 0 ==> 0 < cmod z"
by (rule zero_less_norm_iff [THEN iffD2])

lemma complex_mod_inverse: "cmod(inverse x) = inverse(cmod x)"
by (rule norm_inverse)

lemma complex_mod_divide: "cmod(x/y) = cmod(x)/(cmod y)"
by (simp add: divide_inverse norm_mult norm_inverse)


subsection{*Exponentiation*}

primrec
     complexpow_0:   "z ^ 0       = 1"
     complexpow_Suc: "z ^ (Suc n) = (z::complex) * (z ^ n)"


instance complex :: recpower
proof
  fix z :: complex
  fix n :: nat
  show "z^0 = 1" by simp
  show "z^(Suc n) = z * (z^n)" by simp
qed


lemma complex_of_real_pow: "complex_of_real (x ^ n) = (complex_of_real x) ^ n"
apply (induct_tac "n")
apply (auto simp add: of_real_mult [symmetric])
done

lemma complex_cnj_pow: "cnj(z ^ n) = cnj(z) ^ n"
apply (induct_tac "n")
apply (auto simp add: complex_cnj_mult)
done

lemma complex_mod_complexpow: "cmod(x ^ n) = cmod(x) ^ n"
apply (induct_tac "n")
apply (auto simp add: complex_mod_mult)
done

lemma complexpow_i_squared [simp]: "ii ^ 2 = -(1::complex)"
by (simp add: i_def complex_mult complex_one_def complex_minus numeral_2_eq_2)

lemma complex_i_not_zero [simp]: "ii \<noteq> 0"
by (simp add: i_def complex_zero_def)


subsection{*The Function @{term sgn}*}

definition
  (*------------ Argand -------------*)

  sgn :: "complex => complex"
  "sgn z = z / complex_of_real(cmod z)"

  arg :: "complex => real"
  "arg z = (SOME a. Re(sgn z) = cos a & Im(sgn z) = sin a & -pi < a & a \<le> pi)"

lemma sgn_zero [simp]: "sgn 0 = 0"
by (simp add: sgn_def)

lemma sgn_one [simp]: "sgn 1 = 1"
by (simp add: sgn_def)

lemma sgn_minus: "sgn (-z) = - sgn(z)"
by (simp add: sgn_def)

lemma sgn_eq: "sgn z = z / complex_of_real (cmod z)"
by (simp add: sgn_def)

lemma i_mult_eq: "ii * ii = complex_of_real (-1)"
by (simp add: i_def complex_of_real_def complex_mult complex_add)

lemma i_mult_eq2 [simp]: "ii * ii = -(1::complex)"
by (simp add: i_def complex_one_def complex_mult complex_minus)

lemma complex_eq_cancel_iff2 [simp]:
     "(Complex x y = complex_of_real xa) = (x = xa & y = 0)"
by (simp add: complex_of_real_def) 

lemma complex_eq_cancel_iff2a [simp]:
     "(Complex x y = complex_of_real xa) = (x = xa & y = 0)"
by (simp add: complex_of_real_def)

lemma Complex_eq_0 [simp]: "(Complex x y = 0) = (x = 0 & y = 0)"
by (simp add: complex_zero_def)

lemma Complex_eq_1 [simp]: "(Complex x y = 1) = (x = 1 & y = 0)"
by (simp add: complex_one_def)

lemma Complex_eq_i [simp]: "(Complex x y = ii) = (x = 0 & y = 1)"
by (simp add: i_def)



lemma Re_sgn [simp]: "Re(sgn z) = Re(z)/cmod z"
proof (induct z)
  case (Complex x y)
    have "sqrt (x\<twosuperior> + y\<twosuperior>) * inverse (x\<twosuperior> + y\<twosuperior>) = inverse (sqrt (x\<twosuperior> + y\<twosuperior>))"
      by (simp add: divide_inverse [symmetric] sqrt_divide_self_eq)
    thus "Re (sgn (Complex x y)) = Re (Complex x y) /cmod (Complex x y)"
       by (simp add: sgn_def complex_of_real_def divide_inverse)
qed


lemma Im_sgn [simp]: "Im(sgn z) = Im(z)/cmod z"
proof (induct z)
  case (Complex x y)
    have "sqrt (x\<twosuperior> + y\<twosuperior>) * inverse (x\<twosuperior> + y\<twosuperior>) = inverse (sqrt (x\<twosuperior> + y\<twosuperior>))"
      by (simp add: divide_inverse [symmetric] sqrt_divide_self_eq)
    thus "Im (sgn (Complex x y)) = Im (Complex x y) /cmod (Complex x y)"
       by (simp add: sgn_def complex_of_real_def divide_inverse)
qed

lemma complex_inverse_complex_split:
     "inverse(complex_of_real x + ii * complex_of_real y) =
      complex_of_real(x/(x ^ 2 + y ^ 2)) -
      ii * complex_of_real(y/(x ^ 2 + y ^ 2))"
by (simp add: complex_of_real_def i_def complex_mult complex_add
         diff_minus complex_minus complex_inverse divide_inverse)

(*----------------------------------------------------------------------------*)
(* Many of the theorems below need to be moved elsewhere e.g. Transc. Also *)
(* many of the theorems are not used - so should they be kept?                *)
(*----------------------------------------------------------------------------*)

lemma complex_of_real_zero_iff [simp]: "(complex_of_real y = 0) = (y = 0)"
by (auto simp add: complex_zero_def complex_of_real_def)

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

definition

  (* abbreviation for (cos a + i sin a) *)
  cis :: "real => complex"
  "cis a = Complex (cos a) (sin a)"

  (* abbreviation for r*(cos a + i sin a) *)
  rcis :: "[real, real] => complex"
  "rcis r a = complex_of_real r * cis a"

  (* e ^ (x + iy) *)
  expi :: "complex => complex"
  "expi z = complex_of_real(exp (Re z)) * cis (Im z)"

lemma complex_split_polar:
     "\<exists>r a. z = complex_of_real r * (Complex (cos a) (sin a))"
apply (induct z) 
apply (auto simp add: polar_Ex complex_of_real_mult_Complex)
done

lemma rcis_Ex: "\<exists>r a. z = rcis r a"
apply (induct z) 
apply (simp add: rcis_def cis_def polar_Ex complex_of_real_mult_Complex)
done

lemma Re_rcis [simp]: "Re(rcis r a) = r * cos a"
by (simp add: rcis_def cis_def)

lemma Im_rcis [simp]: "Im(rcis r a) = r * sin a"
by (simp add: rcis_def cis_def)

lemma sin_cos_squared_add2_mult: "(r * cos a)\<twosuperior> + (r * sin a)\<twosuperior> = r\<twosuperior>"
proof -
  have "(r * cos a)\<twosuperior> + (r * sin a)\<twosuperior> = r\<twosuperior> * ((cos a)\<twosuperior> + (sin a)\<twosuperior>)"
    by (simp only: power_mult_distrib right_distrib) 
  thus ?thesis by simp
qed

lemma complex_mod_rcis [simp]: "cmod(rcis r a) = abs r"
by (simp add: rcis_def cis_def sin_cos_squared_add2_mult)

lemma complex_mod_sqrt_Re_mult_cnj: "cmod z = sqrt (Re (z * cnj z))"
apply (simp add: cmod_def)
apply (rule real_sqrt_eq_iff [THEN iffD2])
apply (auto simp add: complex_mult_cnj)
done

lemma complex_Re_cnj [simp]: "Re(cnj z) = Re z"
by (induct z, simp add: complex_cnj)

lemma complex_Im_cnj [simp]: "Im(cnj z) = - Im z"
by (induct z, simp add: complex_cnj)

lemma complex_In_mult_cnj_zero [simp]: "Im (z * cnj z) = 0"
by (induct z, simp add: complex_cnj complex_mult)


(*---------------------------------------------------------------------------*)
(*  (r1 * cis a) * (r2 * cis b) = r1 * r2 * cis (a + b)                      *)
(*---------------------------------------------------------------------------*)

lemma cis_rcis_eq: "cis a = rcis 1 a"
by (simp add: rcis_def)

lemma rcis_mult: "rcis r1 a * rcis r2 b = rcis (r1*r2) (a + b)"
by (simp add: rcis_def cis_def cos_add sin_add right_distrib right_diff_distrib
              complex_of_real_def)

lemma cis_mult: "cis a * cis b = cis (a + b)"
by (simp add: cis_rcis_eq rcis_mult)

lemma cis_zero [simp]: "cis 0 = 1"
by (simp add: cis_def complex_one_def)

lemma rcis_zero_mod [simp]: "rcis 0 a = 0"
by (simp add: rcis_def)

lemma rcis_zero_arg [simp]: "rcis r 0 = complex_of_real r"
by (simp add: rcis_def)

lemma complex_of_real_minus_one:
   "complex_of_real (-(1::real)) = -(1::complex)"
by (simp add: complex_of_real_def complex_one_def complex_minus)

lemma complex_i_mult_minus [simp]: "ii * (ii * x) = - x"
by (simp add: complex_mult_assoc [symmetric])


lemma cis_real_of_nat_Suc_mult:
   "cis (real (Suc n) * a) = cis a * cis (real n * a)"
by (simp add: cis_def real_of_nat_Suc left_distrib cos_add sin_add right_distrib)

lemma DeMoivre: "(cis a) ^ n = cis (real n * a)"
apply (induct_tac "n")
apply (auto simp add: cis_real_of_nat_Suc_mult)
done

lemma DeMoivre2: "(rcis r a) ^ n = rcis (r ^ n) (real n * a)"
by (simp add: rcis_def power_mult_distrib DeMoivre complex_of_real_pow)

lemma cis_inverse [simp]: "inverse(cis a) = cis (-a)"
by (simp add: cis_def complex_inverse_complex_split of_real_minus 
              diff_minus)

lemma rcis_inverse: "inverse(rcis r a) = rcis (1/r) (-a)"
by (simp add: divide_inverse rcis_def complex_of_real_inverse)

lemma cis_divide: "cis a / cis b = cis (a - b)"
by (simp add: complex_divide_def cis_mult real_diff_def)

lemma rcis_divide: "rcis r1 a / rcis r2 b = rcis (r1/r2) (a - b)"
apply (simp add: complex_divide_def)
apply (case_tac "r2=0", simp)
apply (simp add: rcis_inverse rcis_mult real_diff_def)
done

lemma Re_cis [simp]: "Re(cis a) = cos a"
by (simp add: cis_def)

lemma Im_cis [simp]: "Im(cis a) = sin a"
by (simp add: cis_def)

lemma cos_n_Re_cis_pow_n: "cos (real n * a) = Re(cis a ^ n)"
by (auto simp add: DeMoivre)

lemma sin_n_Im_cis_pow_n: "sin (real n * a) = Im(cis a ^ n)"
by (auto simp add: DeMoivre)

lemma expi_add: "expi(a + b) = expi(a) * expi(b)"
by (simp add: expi_def complex_Re_add exp_add complex_Im_add 
              cis_mult [symmetric] of_real_mult mult_ac)

lemma expi_zero [simp]: "expi (0::complex) = 1"
by (simp add: expi_def)

lemma complex_expi_Ex: "\<exists>a r. z = complex_of_real r * expi a"
apply (insert rcis_Ex [of z])
apply (auto simp add: expi_def rcis_def complex_mult_assoc [symmetric] of_real_mult)
apply (rule_tac x = "ii * complex_of_real a" in exI, auto)
done


subsection{*Numerals and Arithmetic*}

instance complex :: number ..

defs (overloaded)
  complex_number_of_def: "(number_of w :: complex) == of_int w"
    --{*the type constraint is essential!*}

instance complex :: number_ring
by (intro_classes, simp add: complex_number_of_def) 


text{*Collapse applications of @{term complex_of_real} to @{term number_of}*}
lemma complex_number_of [simp]: "complex_of_real (number_of w) = number_of w"
by (rule of_real_number_of_eq)

text{*This theorem is necessary because theorems such as
   @{text iszero_number_of_0} only hold for ordered rings. They cannot
   be generalized to fields in general because they fail for finite fields.
   They work for type complex because the reals can be embedded in them.*}
(* TODO: generalize and move to Real/RealVector.thy *)
lemma iszero_complex_number_of [simp]:
     "iszero (number_of w :: complex) = iszero (number_of w :: real)"
by (simp only: complex_of_real_zero_iff complex_number_of [symmetric] 
               iszero_def)  

lemma complex_number_of_cnj [simp]: "cnj(number_of v :: complex) = number_of v"
by (simp only: complex_number_of [symmetric] complex_cnj_complex_of_real)

lemma complex_number_of_cmod: 
      "cmod(number_of v :: complex) = abs (number_of v :: real)"
by (simp only: complex_number_of [symmetric] complex_mod_complex_of_real)

lemma complex_number_of_Re [simp]: "Re(number_of v :: complex) = number_of v"
by (simp only: complex_number_of [symmetric] Re_complex_of_real)

lemma complex_number_of_Im [simp]: "Im(number_of v :: complex) = 0"
by (simp only: complex_number_of [symmetric] Im_complex_of_real)

lemma expi_two_pi_i [simp]: "expi((2::complex) * complex_of_real pi * ii) = 1"
by (simp add: expi_def complex_Re_mult_eq complex_Im_mult_eq cis_def)


(*examples:
print_depth 22
set timing;
set trace_simp;
fun test s = (Goal s, by (Simp_tac 1)); 

test "23 * ii + 45 * ii= (x::complex)";

test "5 * ii + 12 - 45 * ii= (x::complex)";
test "5 * ii + 40 - 12 * ii + 9 = (x::complex) + 89 * ii";
test "5 * ii + 40 - 12 * ii + 9 - 78 = (x::complex) + 89 * ii";

test "l + 10 * ii + 90 + 3*l +  9 + 45 * ii= (x::complex)";
test "87 + 10 * ii + 90 + 3*7 +  9 + 45 * ii= (x::complex)";


fun test s = (Goal s; by (Asm_simp_tac 1)); 

test "x*k = k*(y::complex)";
test "k = k*(y::complex)"; 
test "a*(b*c) = (b::complex)";
test "a*(b*c) = d*(b::complex)*(x*a)";


test "(x*k) / (k*(y::complex)) = (uu::complex)";
test "(k) / (k*(y::complex)) = (uu::complex)"; 
test "(a*(b*c)) / ((b::complex)) = (uu::complex)";
test "(a*(b*c)) / (d*(b::complex)*(x*a)) = (uu::complex)";

FIXME: what do we do about this?
test "a*(b*c)/(y*z) = d*(b::complex)*(x*a)/z";
*)

end


