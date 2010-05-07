(*  Title:      HOL/Groebner_Basis.thy
    Author:     Amine Chaieb, TU Muenchen
*)

header {* Groebner bases *}

theory Groebner_Basis
imports Semiring_Normalization
uses
  ("Tools/Groebner_Basis/groebner.ML")
begin

subsection {* Groebner Bases *}

lemmas bool_simps = simp_thms(1-34)

lemma dnf:
    "(P & (Q | R)) = ((P&Q) | (P&R))" "((Q | R) & P) = ((Q&P) | (R&P))"
    "(P \<and> Q) = (Q \<and> P)" "(P \<or> Q) = (Q \<or> P)"
  by blast+

lemmas weak_dnf_simps = dnf bool_simps

lemma nnf_simps:
    "(\<not>(P \<and> Q)) = (\<not>P \<or> \<not>Q)" "(\<not>(P \<or> Q)) = (\<not>P \<and> \<not>Q)" "(P \<longrightarrow> Q) = (\<not>P \<or> Q)"
    "(P = Q) = ((P \<and> Q) \<or> (\<not>P \<and> \<not> Q))" "(\<not> \<not>(P)) = P"
  by blast+

lemma PFalse:
    "P \<equiv> False \<Longrightarrow> \<not> P"
    "\<not> P \<Longrightarrow> (P \<equiv> False)"
  by auto

ML {*
structure Algebra_Simplification = Named_Thms(
  val name = "algebra"
  val description = "pre-simplification rules for algebraic methods"
)
*}

setup Algebra_Simplification.setup

use "Tools/Groebner_Basis/groebner.ML"

method_setup algebra = Groebner.algebra_method
  "solve polynomial equations over (semi)rings and ideal membership problems using Groebner bases"

declare dvd_def[algebra]
declare dvd_eq_mod_eq_0[symmetric, algebra]
declare mod_div_trivial[algebra]
declare mod_mod_trivial[algebra]
declare conjunct1[OF DIVISION_BY_ZERO, algebra]
declare conjunct2[OF DIVISION_BY_ZERO, algebra]
declare zmod_zdiv_equality[symmetric,algebra]
declare zdiv_zmod_equality[symmetric, algebra]
declare zdiv_zminus_zminus[algebra]
declare zmod_zminus_zminus[algebra]
declare zdiv_zminus2[algebra]
declare zmod_zminus2[algebra]
declare zdiv_zero[algebra]
declare zmod_zero[algebra]
declare mod_by_1[algebra]
declare div_by_1[algebra]
declare zmod_minus1_right[algebra]
declare zdiv_minus1_right[algebra]
declare mod_div_trivial[algebra]
declare mod_mod_trivial[algebra]
declare mod_mult_self2_is_0[algebra]
declare mod_mult_self1_is_0[algebra]
declare zmod_eq_0_iff[algebra]
declare dvd_0_left_iff[algebra]
declare zdvd1_eq[algebra]
declare zmod_eq_dvd_iff[algebra]
declare nat_mod_eq_iff[algebra]

end
