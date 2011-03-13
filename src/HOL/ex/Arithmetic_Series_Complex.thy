(*  Title:      HOL/ex/Arithmetic_Series_Complex.thy
    Author:     Benjamin Porter, 2006
*)


header {* Arithmetic Series for Reals *}

theory Arithmetic_Series_Complex
imports Complex_Main 
begin

lemma arith_series_real:
  "(2::real) * (\<Sum>i\<in>{..<n}. a + of_nat i * d) =
  of_nat n * (a + (a + of_nat(n - 1)*d))"
proof -
  have
    "((1::real) + 1) * (\<Sum>i\<in>{..<n}. a + of_nat(i)*d) =
    of_nat(n) * (a + (a + of_nat(n - 1)*d))"
    by (rule arith_series_general)
  thus ?thesis by simp
qed

end
