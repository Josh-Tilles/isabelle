(*  Title       : HOL/RealPow.thy
    Author      : Jacques D. Fleuriot  
    Copyright   : 1998  University of Cambridge
*)

header {* Natural powers theory *}

theory RealPow
imports RealDef
begin

declare abs_mult_self [simp]

lemma two_realpow_ge_one [simp]: "(1::real) \<le> 2 ^ n"
by simp

lemma two_realpow_gt [simp]: "real (n::nat) < 2 ^ n"
apply (induct "n")
apply (auto simp add: real_of_nat_Suc)
apply (subst mult_2)
apply (erule add_less_le_mono)
apply (rule two_realpow_ge_one)
done

lemma realpow_Suc_le_self: "[| 0 \<le> r; r \<le> (1::real) |] ==> r ^ Suc n \<le> r"
by (insert power_decreasing [of 1 "Suc n" r], simp)

lemma realpow_minus_mult [rule_format]:
     "0 < n --> (x::real) ^ (n - 1) * x = x ^ n"
apply (simp split add: nat_diff_split)
done

lemma realpow_two_mult_inverse [simp]:
     "r \<noteq> 0 ==> r * inverse r ^Suc (Suc 0) = inverse (r::real)"
by (simp add:  real_mult_assoc [symmetric])

lemma realpow_two_minus [simp]: "(-x)^Suc (Suc 0) = (x::real)^Suc (Suc 0)"
by simp

lemma realpow_two_diff:
     "(x::real)^Suc (Suc 0) - y^Suc (Suc 0) = (x - y) * (x + y)"
apply (unfold real_diff_def)
apply (simp add: algebra_simps)
done

lemma realpow_two_disj:
     "((x::real)^Suc (Suc 0) = y^Suc (Suc 0)) = (x = y | x = -y)"
apply (cut_tac x = x and y = y in realpow_two_diff)
apply auto
done

lemma realpow_real_of_nat_two_pos [simp] : "0 < real (Suc (Suc 0) ^ n)"
apply (induct "n")
apply (auto simp add: zero_less_mult_iff)
done

(* used by AFP Integration theory *)
lemma realpow_increasing:
     "[|(0::real) \<le> x; 0 \<le> y; x ^ Suc n \<le> y ^ Suc n|] ==> x \<le> y"
  by (rule power_le_imp_le_base)


subsection{* Squares of Reals *}

lemma real_two_squares_add_zero_iff [simp]:
  "(x * x + y * y = 0) = ((x::real) = 0 \<and> y = 0)"
by (rule sum_squares_eq_zero_iff)

lemma real_sum_squares_cancel: "x * x + y * y = 0 ==> x = (0::real)"
by simp

lemma real_sum_squares_cancel2: "x * x + y * y = 0 ==> y = (0::real)"
by simp

lemma real_mult_self_sum_ge_zero: "(0::real) \<le> x*x + y*y"
by (rule sum_squares_ge_zero)

lemma real_sum_squares_cancel_a: "x * x = -(y * y) ==> x = (0::real) & y=0"
by (simp add: real_add_eq_0_iff [symmetric])

lemma real_squared_diff_one_factored: "x*x - (1::real) = (x + 1)*(x - 1)"
by (simp add: left_distrib right_diff_distrib)

lemma real_mult_is_one [simp]: "(x*x = (1::real)) = (x = 1 | x = - 1)"
apply auto
apply (drule right_minus_eq [THEN iffD2]) 
apply (auto simp add: real_squared_diff_one_factored)
done

lemma real_sum_squares_not_zero: "x ~= 0 ==> x * x + y * y ~= (0::real)"
by simp

lemma real_sum_squares_not_zero2: "y ~= 0 ==> x * x + y * y ~= (0::real)"
by simp

lemma realpow_two_sum_zero_iff [simp]:
     "(x ^ 2 + y ^ 2 = (0::real)) = (x = 0 & y = 0)"
by (rule sum_power2_eq_zero_iff)

lemma realpow_two_le_add_order [simp]: "(0::real) \<le> u ^ 2 + v ^ 2"
by (rule sum_power2_ge_zero)

lemma realpow_two_le_add_order2 [simp]: "(0::real) \<le> u ^ 2 + v ^ 2 + w ^ 2"
by (intro add_nonneg_nonneg zero_le_power2)

lemma real_sum_square_gt_zero: "x ~= 0 ==> (0::real) < x * x + y * y"
by (simp add: sum_squares_gt_zero_iff)

lemma real_sum_square_gt_zero2: "y ~= 0 ==> (0::real) < x * x + y * y"
by (simp add: sum_squares_gt_zero_iff)

lemma real_minus_mult_self_le [simp]: "-(u * u) \<le> (x * (x::real))"
by (rule_tac j = 0 in real_le_trans, auto)

lemma realpow_square_minus_le [simp]: "-(u ^ 2) \<le> (x::real) ^ 2"
by (auto simp add: power2_eq_square)

(* The following theorem is by Benjamin Porter *)
lemma real_sq_order:
  fixes x::real
  assumes xgt0: "0 \<le> x" and ygt0: "0 \<le> y" and sq: "x^2 \<le> y^2"
  shows "x \<le> y"
proof -
  from sq have "x ^ Suc (Suc 0) \<le> y ^ Suc (Suc 0)"
    by (simp only: numeral_2_eq_2)
  thus "x \<le> y" using ygt0
    by (rule power_le_imp_le_base)
qed


subsection {*Various Other Theorems*}

lemma real_le_add_half_cancel: "(x + y/2 \<le> (y::real)) = (x \<le> y /2)"
by auto

lemma real_minus_half_eq [simp]: "(x::real) - x/2 = x/2"
by auto

lemma real_mult_inverse_cancel:
     "[|(0::real) < x; 0 < x1; x1 * y < x * u |] 
      ==> inverse x * y < inverse x1 * u"
apply (rule_tac c=x in mult_less_imp_less_left) 
apply (auto simp add: real_mult_assoc [symmetric])
apply (simp (no_asm) add: mult_ac)
apply (rule_tac c=x1 in mult_less_imp_less_right) 
apply (auto simp add: mult_ac)
done

lemma real_mult_inverse_cancel2:
     "[|(0::real) < x;0 < x1; x1 * y < x * u |] ==> y * inverse x < u * inverse x1"
apply (auto dest: real_mult_inverse_cancel simp add: mult_ac)
done

lemma inverse_real_of_nat_gt_zero [simp]: "0 < inverse (real (Suc n))"
by simp

lemma inverse_real_of_nat_ge_zero [simp]: "0 \<le> inverse (real (Suc n))"
by simp

lemma realpow_num_eq_if: "(m::real) ^ n = (if n=0 then 1 else m * m ^ (n - 1))"
by (case_tac "n", auto)

end
