(*  Title:      HOL/Library/ExecutableRat.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Executable implementation of rational numbers in HOL *}

theory ExecutableRat
imports "~~/src/HOL/Real/Rational" "~~/src/HOL/NumberTheory/IntPrimes"
begin

text {*
  Actually nothing is proved about the implementation.
*}


section {* HOL definitions *}

datatype erat = Rat bool int int

instance erat :: zero ..
instance erat :: one ..
instance erat :: plus ..
instance erat :: minus ..
instance erat :: times ..
instance erat :: inverse ..
instance erat :: ord ..

definition
  norm :: "erat \<Rightarrow> erat"
  norm_def: "norm r = (case r of (Rat a p q) \<Rightarrow>
     if p = 0 then Rat True 0 1
     else
       let
         absp = abs p
       in let
         m = zgcd (absp, q)
       in Rat (a = (0 <= p)) (absp div m) (q div m))"
  common :: "(int * int) * (int * int) \<Rightarrow> (int * int) * int"
  common_def: "common r = (case r of ((p1, q1), (p2, q2)) \<Rightarrow>
       let q' = q1 * q2 div int (gcd (nat q1, nat q2))
       in ((p1 * (q' div q1), p2 * (q' div q2)), q'))"
  of_quotient :: "int * int \<Rightarrow> erat"
  of_quotient_def: "of_quotient r = (case r of (a, b) \<Rightarrow>
       norm (Rat True a b))"
  of_rat :: "rat \<Rightarrow> erat"
  of_rat_def: "of_rat r = of_quotient (SOME s. s : Rep_Rat r)"
  to_rat :: "erat \<Rightarrow> rat"
  to_rat_def: "to_rat r = (case r of (Rat a p q) \<Rightarrow>
       if a then Fract p q else Fract (uminus p) q)"
  eq_rat :: "erat \<Rightarrow> erat \<Rightarrow> bool"
  "eq_rat r s = (norm r = norm s)"

defs (overloaded)
  zero_rat_def: "0 == Rat True 0 1"
  one_rat_def: "1 == Rat True 1 1"
  add_rat_def: "r + s == case r of Rat a1 p1 q1 \<Rightarrow> case s of Rat a2 p2 q2 \<Rightarrow>
        let
          ((r1, r2), den) = common ((p1, q1), (p2, q2))
        in let
          num = (if a1 then r1 else -r1) + (if a2 then r2 else -r2)
        in norm (Rat True num den)"
  uminus_rat_def: "- r == case r of Rat a p q \<Rightarrow>
        if p = 0 then Rat a p q
        else Rat (\<not> a) p q"
  times_rat_def: "r * s == case r of Rat a1 p1 q1 \<Rightarrow> case s of Rat a2 p2 q2 \<Rightarrow>
        norm (Rat (a1 = a2) (p1 * p2) (q1 * q2))"
  inverse_rat_def: "inverse r == case r of Rat a p q \<Rightarrow>
        if p = 0 then arbitrary
        else Rat a q p"
  le_rat_def: "r <= s == case r of Rat a1 p1 q1 \<Rightarrow> case s of Rat a2 p2 q2 \<Rightarrow>
        (\<not> a1 \<and> a2) \<or>
        (\<not> (a1 \<and> \<not> a2) \<and>
          (let
            ((r1, r2), dummy) = common ((p1, q1), (p2, q2))
          in if a1 then r1 <= r2 else r2 <= r1))"


section {* type serializations *}

types_code
  rat ("{*erat*}")

code_gen Rat
  (SML) (Haskell)

code_type rat
  (SML "{*erat*}")
  (Haskell "{*erat*}")


section {* const serializations *}

consts_code
  arbitrary :: erat ("raise/ (Fail/ \"non-defined rational number\")")
  Fract ("{*of_quotient*}")
  0 :: rat ("{*0::erat*}")
  1 :: rat ("{*1::erat*}")
  HOL.plus :: "rat \<Rightarrow> rat \<Rightarrow> rat" ("{*op + :: erat \<Rightarrow> erat \<Rightarrow> erat*}")
  uminus :: "rat \<Rightarrow> rat" ("{*uminus :: erat \<Rightarrow> erat*}")
  HOL.times :: "rat \<Rightarrow> rat \<Rightarrow> rat" ("{*op * :: erat \<Rightarrow> erat \<Rightarrow> erat*}")
  inverse :: "rat \<Rightarrow> rat" ("{*inverse :: erat \<Rightarrow> erat*}")
  divide :: "rat \<Rightarrow> rat \<Rightarrow> rat" ("{*op * :: erat \<Rightarrow> erat \<Rightarrow> erat*}/ _/ ({*inverse :: erat \<Rightarrow> erat*}/ _)")
  Orderings.less_eq :: "rat \<Rightarrow> rat \<Rightarrow> bool" ("{*op <= :: erat \<Rightarrow> erat \<Rightarrow> bool*}")
  "op =" :: "rat \<Rightarrow> rat \<Rightarrow> bool" ("{*eq_rat*}")

code_const "arbitrary :: erat"
  (SML "raise/ (Fail/ \"non-defined rational number\")")
  (Haskell "error/ \"non-defined rational number\"")

code_gen
  of_quotient
  "0::erat"
  "1::erat"
  "op + :: erat \<Rightarrow> erat \<Rightarrow> erat"
  "uminus :: erat \<Rightarrow> erat"
  "op * :: erat \<Rightarrow> erat \<Rightarrow> erat"
  "inverse :: erat \<Rightarrow> erat"
  "op <= :: erat \<Rightarrow> erat \<Rightarrow> bool"
  eq_rat
  (SML) (Haskell)

code_const Fract
  (SML "{*of_quotient*}")
  (Haskell "{*of_quotient*}")

code_const "0 :: rat"
  (SML "{*0::erat*}")
  (Haskell "{*1::erat*}")

code_const "1 :: rat"
  (SML "{*1::erat*}")
  (Haskell "{*1::erat*}")

code_const "op + :: rat \<Rightarrow> rat \<Rightarrow> rat"
  (SML "{*op + :: erat \<Rightarrow> erat \<Rightarrow> erat*}")
  (Haskell "{*op + :: erat \<Rightarrow> erat \<Rightarrow> erat*}")

code_const "uminus :: rat \<Rightarrow> rat"
  (SML "{*uminus :: erat \<Rightarrow> erat*}")
  (Haskell "{*uminus :: erat \<Rightarrow> erat*}")

code_const "op * :: rat \<Rightarrow> rat \<Rightarrow> rat"
  (SML "{*op * :: erat \<Rightarrow> erat \<Rightarrow> erat*}")
  (Haskell "{*op * :: erat \<Rightarrow> erat \<Rightarrow> erat*}")

code_const "inverse :: rat \<Rightarrow> rat"
  (SML "{*inverse :: erat \<Rightarrow> erat*}")
  (Haskell "{*inverse :: erat \<Rightarrow> erat*}")

code_const "divide :: rat \<Rightarrow> rat \<Rightarrow> rat"
  (SML "{*op * :: erat \<Rightarrow> erat \<Rightarrow> erat*}/ _/ ({*inverse :: erat \<Rightarrow> erat*}/ _)")
  (Haskell "{*op * :: erat \<Rightarrow> erat \<Rightarrow> erat*}/ _/ ({*inverse :: erat \<Rightarrow> erat*}/ _)")

code_const "op <= :: rat \<Rightarrow> rat \<Rightarrow> bool"
  (SML "{*op <= :: erat \<Rightarrow> erat \<Rightarrow> bool*}")
  (Haskell "{*op <= :: erat \<Rightarrow> erat \<Rightarrow> bool*}")

code_const "op = :: rat \<Rightarrow> rat \<Rightarrow> bool"
  (SML "{*eq_rat*}")
  (Haskell "{*eq_rat*}")

end
