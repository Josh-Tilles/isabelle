(*  Title:      HOL/HyperArith.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

header{*Binary arithmetic and Simplification for the Hyperreals*}

theory HyperArith
imports HyperDef
uses ("hypreal_arith.ML")
begin

subsection{*Absolute Value Function for the Hyperreals*}

lemma hrabs_add_less:
     "[| abs x < r; abs y < s |] ==> abs(x+y) < r + (s::hypreal)"
by (simp add: abs_if split: split_if_asm)

lemma hrabs_less_gt_zero: "abs x < r ==> (0::hypreal) < r"
by (blast intro!: order_le_less_trans abs_ge_zero)

lemma hrabs_disj: "abs x = (x::hypreal) | abs x = -x"
by (simp add: abs_if)

lemma hrabs_add_lemma_disj: "(y::hypreal) + - x + (y + - z) = abs (x + - z) ==> y = z | x = y"
by (simp add: abs_if split add: split_if_asm)

lemma hypreal_of_real_hrabs:
    "abs (hypreal_of_real r) = hypreal_of_real (abs r)"
by (rule star_of_abs [symmetric])


subsection{*Embedding the Naturals into the Hyperreals*}

definition
  hypreal_of_nat   :: "nat => hypreal"
  "hypreal_of_nat m = of_nat m"

lemma SNat_eq: "Nats = {n. \<exists>N. n = hypreal_of_nat N}"
by (force simp add: hypreal_of_nat_def Nats_def) 

lemma hypreal_of_nat_add [simp]:
     "hypreal_of_nat (m + n) = hypreal_of_nat m + hypreal_of_nat n"
by (simp add: hypreal_of_nat_def)

lemma hypreal_of_nat_mult: "hypreal_of_nat (m * n) = hypreal_of_nat m * hypreal_of_nat n"
by (simp add: hypreal_of_nat_def)
declare hypreal_of_nat_mult [simp]

lemma hypreal_of_nat_less_iff:
      "(n < m) = (hypreal_of_nat n < hypreal_of_nat m)"
apply (simp add: hypreal_of_nat_def)
done
declare hypreal_of_nat_less_iff [symmetric, simp]

(*------------------------------------------------------------*)
(* naturals embedded in hyperreals                            *)
(* is a hyperreal c.f. NS extension                           *)
(*------------------------------------------------------------*)

lemma hypreal_of_nat_eq:
     "hypreal_of_nat (n::nat) = hypreal_of_real (real n)"
apply (induct n) 
apply (simp_all add: hypreal_of_nat_def real_of_nat_def)
done

lemma hypreal_of_nat:
     "hypreal_of_nat m = star_n (%n. real m)"
apply (fold star_of_def)
apply (induct m)
apply (simp_all add: hypreal_of_nat_def real_of_nat_def star_n_add)
done

lemma hypreal_of_nat_Suc:
     "hypreal_of_nat (Suc n) = hypreal_of_nat n + (1::hypreal)"
by (simp add: hypreal_of_nat_def)

(*"neg" is used in rewrite rules for binary comparisons*)
lemma hypreal_of_nat_number_of [simp]:
     "hypreal_of_nat (number_of v :: nat) =
         (if neg (number_of v :: int) then 0
          else (number_of v :: hypreal))"
by (simp add: hypreal_of_nat_eq)

lemma hypreal_of_nat_zero [simp]: "hypreal_of_nat 0 = 0"
by (simp add: hypreal_of_nat_def) 

lemma hypreal_of_nat_one [simp]: "hypreal_of_nat 1 = 1"
by (simp add: hypreal_of_nat_def) 

lemma hypreal_of_nat_le_iff [simp]:
     "(hypreal_of_nat n \<le> hypreal_of_nat m) = (n \<le> m)"
by (simp add: hypreal_of_nat_def) 

lemma hypreal_of_nat_ge_zero [simp]: "0 \<le> hypreal_of_nat n"
by (simp add: hypreal_of_nat_def) 


(*
FIXME: we should declare this, as for type int, but many proofs would break.
It replaces x+-y by x-y.
Addsimps [symmetric hypreal_diff_def]
*)


use "hypreal_arith.ML"

setup hypreal_arith_setup

end
