(*  Title       : HyperPow.thy
    Author      : Jacques D. Fleuriot  
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2003/4
*)

header{*Exponentials on the Hyperreals*}

theory HyperPow
imports HyperArith HyperNat Parity
begin

(* consts hpowr :: "[hypreal,nat] => hypreal" *)

lemma hpowr_0 [simp]:   "r ^ 0       = (1::hypreal)"
by (rule power_0)

lemma hpowr_Suc [simp]: "r ^ (Suc n) = (r::hypreal) * (r ^ n)"
by (rule power_Suc)

definition
  (* hypernatural powers of hyperreals *)
  pow :: "['a::power star, nat star] \<Rightarrow> 'a star" (infixr "pow" 80) where
  hyperpow_def [transfer_unfold]:
  "R pow N = ( *f2* op ^) R N"

lemma hrealpow_two: "(r::hypreal) ^ Suc (Suc 0) = r * r"
by simp

lemma hrealpow_two_le [simp]: "(0::hypreal) \<le> r ^ Suc (Suc 0)"
by (auto simp add: zero_le_mult_iff)

lemma hrealpow_two_le_add_order [simp]:
     "(0::hypreal) \<le> u ^ Suc (Suc 0) + v ^ Suc (Suc 0)"
by (simp only: hrealpow_two_le add_nonneg_nonneg)

lemma hrealpow_two_le_add_order2 [simp]:
     "(0::hypreal) \<le> u ^ Suc (Suc 0) + v ^ Suc (Suc 0) + w ^ Suc (Suc 0)"
by (simp only: hrealpow_two_le add_nonneg_nonneg)

lemma hypreal_add_nonneg_eq_0_iff:
     "[| 0 \<le> x; 0 \<le> y |] ==> (x+y = 0) = (x = 0 & y = (0::hypreal))"
by arith


text{*FIXME: DELETE THESE*}
lemma hypreal_three_squares_add_zero_iff:
     "(x*x + y*y + z*z = 0) = (x = 0 & y = 0 & z = (0::hypreal))"
apply (simp only: zero_le_square add_nonneg_nonneg hypreal_add_nonneg_eq_0_iff, auto)
done

lemma hrealpow_three_squares_add_zero_iff [simp]:
     "(x ^ Suc (Suc 0) + y ^ Suc (Suc 0) + z ^ Suc (Suc 0) = (0::hypreal)) = 
      (x = 0 & y = 0 & z = 0)"
by (simp only: hypreal_three_squares_add_zero_iff hrealpow_two)

(*FIXME: This and RealPow.abs_realpow_two should be replaced by an abstract
  result proved in Ring_and_Field*)
lemma hrabs_hrealpow_two [simp]:
     "abs(x ^ Suc (Suc 0)) = (x::hypreal) ^ Suc (Suc 0)"
by (simp add: abs_mult)

lemma two_hrealpow_ge_one [simp]: "(1::hypreal) \<le> 2 ^ n"
by (insert power_increasing [of 0 n "2::hypreal"], simp)

lemma two_hrealpow_gt [simp]: "hypreal_of_nat n < 2 ^ n"
apply (induct_tac "n")
apply (auto simp add: left_distrib)
apply (cut_tac n = n in two_hrealpow_ge_one, arith)
done

lemma hrealpow:
    "star_n X ^ m = star_n (%n. (X n::real) ^ m)"
apply (induct_tac "m")
apply (auto simp add: star_n_one_num star_n_mult power_0)
done

lemma hrealpow_sum_square_expand:
     "(x + (y::hypreal)) ^ Suc (Suc 0) =
      x ^ Suc (Suc 0) + y ^ Suc (Suc 0) + (hypreal_of_nat (Suc (Suc 0)))*x*y"
by (simp add: right_distrib left_distrib)


subsection{*Literal Arithmetic Involving Powers and Type @{typ hypreal}*}

lemma power_hypreal_of_real_number_of:
     "(number_of v :: hypreal) ^ n = hypreal_of_real ((number_of v) ^ n)"
by simp
declare power_hypreal_of_real_number_of [of _ "number_of w", standard, simp]

lemma hrealpow_HFinite:
  fixes x :: "'a::{real_normed_algebra,recpower} star"
  shows "x \<in> HFinite ==> x ^ n \<in> HFinite"
apply (induct_tac "n")
apply (auto simp add: power_Suc intro: HFinite_mult)
done


subsection{*Powers with Hypernatural Exponents*}

lemma hyperpow: "star_n X pow star_n Y = star_n (%n. X n ^ Y n)"
by (simp add: hyperpow_def starfun2_star_n)

lemma hyperpow_zero [simp]:
  "\<And>n. (0::'a::{recpower,semiring_0} star) pow (n + (1::hypnat)) = 0"
by transfer simp

lemma hyperpow_not_zero:
  "\<And>r n. r \<noteq> (0::'a::{recpower,field} star) ==> r pow n \<noteq> 0"
by transfer (rule field_power_not_zero)

lemma hyperpow_inverse:
  "\<And>r n. r \<noteq> (0::'a::{recpower,division_by_zero,field} star)
   \<Longrightarrow> inverse (r pow n) = (inverse r) pow n"
by transfer (rule power_inverse)

lemma hyperpow_hrabs:
  "\<And>r n. abs (r::'a::{recpower,ordered_idom} star) pow n = abs (r pow n)"
by transfer (rule power_abs [symmetric])

lemma hyperpow_add:
  "\<And>r n m. (r::'a::recpower star) pow (n + m) = (r pow n) * (r pow m)"
by transfer (rule power_add)

lemma hyperpow_one [simp]:
  "\<And>r. (r::'a::recpower star) pow (1::hypnat) = r"
by transfer (rule power_one_right)

lemma hyperpow_two:
  "\<And>r. (r::'a::recpower star) pow ((1::hypnat) + (1::hypnat)) = r * r"
by transfer (simp add: power_Suc)

lemma hyperpow_gt_zero:
  "\<And>r n. (0::'a::{recpower,ordered_semidom} star) < r \<Longrightarrow> 0 < r pow n"
by transfer (rule zero_less_power)

lemma hyperpow_ge_zero:
  "\<And>r n. (0::'a::{recpower,ordered_semidom} star) \<le> r \<Longrightarrow> 0 \<le> r pow n"
by transfer (rule zero_le_power)

lemma hyperpow_le:
  "\<And>x y n. \<lbrakk>(0::'a::{recpower,ordered_semidom} star) < x; x \<le> y\<rbrakk>
   \<Longrightarrow> x pow n \<le> y pow n"
by transfer (rule power_mono [OF _ order_less_imp_le])

lemma hyperpow_eq_one [simp]:
  "\<And>n. 1 pow n = (1::'a::recpower star)"
by transfer (rule power_one)

lemma hrabs_hyperpow_minus_one [simp]:
  "\<And>n. abs(-1 pow n) = (1::'a::{number_ring,recpower,ordered_idom} star)"
by transfer (rule abs_power_minus_one)

lemma hyperpow_mult:
  "\<And>r s n. (r * s::'a::{comm_monoid_mult,recpower} star) pow n
   = (r pow n) * (s pow n)"
by transfer (rule power_mult_distrib)

lemma hyperpow_two_le [simp]:
  "(0::'a::{recpower,ordered_ring_strict} star) \<le> r pow (1 + 1)"
by (auto simp add: hyperpow_two zero_le_mult_iff)

lemma hrabs_hyperpow_two [simp]:
  "abs(x pow (1 + 1)) =
   (x::'a::{recpower,ordered_ring_strict} star) pow (1 + 1)"
by (simp only: abs_of_nonneg hyperpow_two_le)

lemma hyperpow_two_hrabs [simp]:
  "abs(x::'a::{recpower,ordered_idom} star) pow (1 + 1)  = x pow (1 + 1)"
by (simp add: hyperpow_hrabs)

text{*The precondition could be weakened to @{term "0\<le>x"}*}
lemma hypreal_mult_less_mono:
     "[| u<v;  x<y;  (0::hypreal) < v;  0 < x |] ==> u*x < v* y"
 by (simp add: Ring_and_Field.mult_strict_mono order_less_imp_le)

lemma hyperpow_two_gt_one:
  "\<And>r::'a::{recpower,ordered_semidom} star. 1 < r \<Longrightarrow> 1 < r pow (1 + 1)"
by transfer (simp add: power_gt1)

lemma hyperpow_two_ge_one:
  "\<And>r::'a::{recpower,ordered_semidom} star. 1 \<le> r \<Longrightarrow> 1 \<le> r pow (1 + 1)"
by transfer (simp add: one_le_power)

lemma two_hyperpow_ge_one [simp]: "(1::hypreal) \<le> 2 pow n"
apply (rule_tac y = "1 pow n" in order_trans)
apply (rule_tac [2] hyperpow_le, auto)
done

lemma hyperpow_minus_one2 [simp]:
     "!!n. -1 pow ((1 + 1)*n) = (1::hypreal)"
by transfer (simp)

lemma hyperpow_less_le:
     "!!r n N. [|(0::hypreal) \<le> r; r \<le> 1; n < N|] ==> r pow N \<le> r pow n"
by transfer (rule power_decreasing [OF order_less_imp_le])

lemma hyperpow_SHNat_le:
     "[| 0 \<le> r;  r \<le> (1::hypreal);  N \<in> HNatInfinite |]
      ==> ALL n: Nats. r pow N \<le> r pow n"
by (auto intro!: hyperpow_less_le simp add: HNatInfinite_iff)

lemma hyperpow_realpow:
      "(hypreal_of_real r) pow (hypnat_of_nat n) = hypreal_of_real (r ^ n)"
by transfer (rule refl)

lemma hyperpow_SReal [simp]:
     "(hypreal_of_real r) pow (hypnat_of_nat n) \<in> Reals"
by (simp del: star_of_power add: hyperpow_realpow SReal_def)


lemma hyperpow_zero_HNatInfinite [simp]:
     "N \<in> HNatInfinite ==> (0::hypreal) pow N = 0"
by (drule HNatInfinite_is_Suc, auto)

lemma hyperpow_le_le:
     "[| (0::hypreal) \<le> r; r \<le> 1; n \<le> N |] ==> r pow N \<le> r pow n"
apply (drule order_le_less [of n, THEN iffD1])
apply (auto intro: hyperpow_less_le)
done

lemma hyperpow_Suc_le_self2:
     "[| (0::hypreal) \<le> r; r < 1 |] ==> r pow (n + (1::hypnat)) \<le> r"
apply (drule_tac n = " (1::hypnat) " in hyperpow_le_le)
apply auto
done

lemma lemma_Infinitesimal_hyperpow:
     "[| (x::hypreal) \<in> Infinitesimal; 0 < N |] ==> abs (x pow N) \<le> abs x"
apply (unfold Infinitesimal_def)
apply (auto intro!: hyperpow_Suc_le_self2 
          simp add: hyperpow_hrabs [symmetric] hypnat_gt_zero_iff2 abs_ge_zero)
done

lemma Infinitesimal_hyperpow:
     "[| (x::hypreal) \<in> Infinitesimal; 0 < N |] ==> x pow N \<in> Infinitesimal"
apply (rule hrabs_le_Infinitesimal)
apply (rule_tac [2] lemma_Infinitesimal_hyperpow, auto)
done

lemma hyperpow_hypnat_of_nat: "\<And>x. x pow hypnat_of_nat n = x ^ n"
by transfer (rule refl)

lemma hrealpow_hyperpow_Infinitesimal_iff:
     "(x ^ n \<in> Infinitesimal) = (x pow (hypnat_of_nat n) \<in> Infinitesimal)"
by (simp only: hyperpow_hypnat_of_nat)

lemma Infinitesimal_hrealpow:
     "[| (x::hypreal) \<in> Infinitesimal; 0 < n |] ==> x ^ n \<in> Infinitesimal"
by (simp add: hrealpow_hyperpow_Infinitesimal_iff Infinitesimal_hyperpow)

end
