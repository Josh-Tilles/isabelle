(*  Title:      HOL/IntDiv.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

The division operators div, mod and the divides relation "dvd"

Here is the division algorithm in ML:

    fun posDivAlg (a,b) =
      if a<b then (0,a)
      else let val (q,r) = posDivAlg(a, 2*b)
	       in  if 0\<le>r-b then (2*q+1, r-b) else (2*q, r)
	   end

    fun negDivAlg (a,b) =
      if 0\<le>a+b then (~1,a+b)
      else let val (q,r) = negDivAlg(a, 2*b)
	       in  if 0\<le>r-b then (2*q+1, r-b) else (2*q, r)
	   end;

    fun negateSnd (q,r:int) = (q,~r);

    fun divAlg (a,b) = if 0\<le>a then 
			  if b>0 then posDivAlg (a,b) 
			   else if a=0 then (0,0)
				else negateSnd (negDivAlg (~a,~b))
		       else 
			  if 0<b then negDivAlg (a,b)
			  else        negateSnd (posDivAlg (~a,~b));
*)


theory IntDiv
imports IntArith Recdef
files ("IntDiv_setup.ML")
begin

declare zless_nat_conj [simp]

constdefs
  quorem :: "(int*int) * (int*int) => bool"
    "quorem == %((a,b), (q,r)).
                      a = b*q + r &
                      (if 0 < b then 0\<le>r & r<b else b<r & r \<le> 0)"

  adjust :: "[int, int*int] => int*int"
    "adjust b == %(q,r). if 0 \<le> r-b then (2*q + 1, r-b)
                         else (2*q, r)"

(** the division algorithm **)

(*for the case a>=0, b>0*)
consts posDivAlg :: "int*int => int*int"
recdef posDivAlg "inv_image less_than (%(a,b). nat(a - b + 1))"
    "posDivAlg (a,b) =
       (if (a<b | b\<le>0) then (0,a)
        else adjust b (posDivAlg(a, 2*b)))"

(*for the case a<0, b>0*)
consts negDivAlg :: "int*int => int*int"
recdef negDivAlg "inv_image less_than (%(a,b). nat(- a - b))"
    "negDivAlg (a,b) =
       (if (0\<le>a+b | b\<le>0) then (-1,a+b)
        else adjust b (negDivAlg(a, 2*b)))"

(*for the general case b~=0*)

constdefs
  negateSnd :: "int*int => int*int"
    "negateSnd == %(q,r). (q,-r)"

  (*The full division algorithm considers all possible signs for a, b
    including the special case a=0, b<0, because negDivAlg requires a<0*)
  divAlg :: "int*int => int*int"
    "divAlg ==
       %(a,b). if 0\<le>a then
                  if 0\<le>b then posDivAlg (a,b)
                  else if a=0 then (0,0)
                       else negateSnd (negDivAlg (-a,-b))
               else 
                  if 0<b then negDivAlg (a,b)
                  else         negateSnd (posDivAlg (-a,-b))"

instance
  int :: "Divides.div" ..       (*avoid clash with 'div' token*)

defs
  div_def:   "a div b == fst (divAlg (a,b))"
  mod_def:   "a mod b == snd (divAlg (a,b))"



subsection{*Uniqueness and Monotonicity of Quotients and Remainders*}

lemma unique_quotient_lemma:
     "[| b*q' + r'  \<le> b*q + r;  0 \<le> r';  0 < b;  r < b |]  
      ==> q' \<le> (q::int)"
apply (subgoal_tac "r' + b * (q'-q) \<le> r")
 prefer 2 apply (simp add: right_diff_distrib)
apply (subgoal_tac "0 < b * (1 + q - q') ")
apply (erule_tac [2] order_le_less_trans)
 prefer 2 apply (simp add: right_diff_distrib right_distrib)
apply (subgoal_tac "b * q' < b * (1 + q) ")
 prefer 2 apply (simp add: right_diff_distrib right_distrib)
apply (simp add: mult_less_cancel_left)
done

lemma unique_quotient_lemma_neg:
     "[| b*q' + r' \<le> b*q + r;  r \<le> 0;  b < 0;  b < r' |]  
      ==> q \<le> (q'::int)"
by (rule_tac b = "-b" and r = "-r'" and r' = "-r" in unique_quotient_lemma, 
    auto)

lemma unique_quotient:
     "[| quorem ((a,b), (q,r));  quorem ((a,b), (q',r'));  b ~= 0 |]  
      ==> q = q'"
apply (simp add: quorem_def linorder_neq_iff split: split_if_asm)
apply (blast intro: order_antisym
             dest: order_eq_refl [THEN unique_quotient_lemma] 
             order_eq_refl [THEN unique_quotient_lemma_neg] sym)+
done


lemma unique_remainder:
     "[| quorem ((a,b), (q,r));  quorem ((a,b), (q',r'));  b ~= 0 |]  
      ==> r = r'"
apply (subgoal_tac "q = q'")
 apply (simp add: quorem_def)
apply (blast intro: unique_quotient)
done


subsection{*Correctness of posDivAlg, the Algorithm for Non-Negative Dividends*}

text{*And positive divisors*}

lemma adjust_eq [simp]:
     "adjust b (q,r) = 
      (let diff = r-b in  
	if 0 \<le> diff then (2*q + 1, diff)   
                     else (2*q, r))"
by (simp add: Let_def adjust_def)

declare posDivAlg.simps [simp del]

(**use with a simproc to avoid repeatedly proving the premise*)
lemma posDivAlg_eqn:
     "0 < b ==>  
      posDivAlg (a,b) = (if a<b then (0,a) else adjust b (posDivAlg(a, 2*b)))"
by (rule posDivAlg.simps [THEN trans], simp)

(*Correctness of posDivAlg: it computes quotients correctly*)
lemma posDivAlg_correct [rule_format]:
     "0 \<le> a --> 0 < b --> quorem ((a, b), posDivAlg (a, b))"
apply (induct_tac a b rule: posDivAlg.induct, auto)
 apply (simp_all add: quorem_def)
 (*base case: a<b*)
 apply (simp add: posDivAlg_eqn)
(*main argument*)
apply (subst posDivAlg_eqn, simp_all)
apply (erule splitE)
apply (auto simp add: right_distrib Let_def)
done


subsection{*Correctness of negDivAlg, the Algorithm for Negative Dividends*}

text{*And positive divisors*}

declare negDivAlg.simps [simp del]

(**use with a simproc to avoid repeatedly proving the premise*)
lemma negDivAlg_eqn:
     "0 < b ==>  
      negDivAlg (a,b) =       
       (if 0\<le>a+b then (-1,a+b) else adjust b (negDivAlg(a, 2*b)))"
by (rule negDivAlg.simps [THEN trans], simp)

(*Correctness of negDivAlg: it computes quotients correctly
  It doesn't work if a=0 because the 0/b equals 0, not -1*)
lemma negDivAlg_correct [rule_format]:
     "a < 0 --> 0 < b --> quorem ((a, b), negDivAlg (a, b))"
apply (induct_tac a b rule: negDivAlg.induct, auto)
 apply (simp_all add: quorem_def)
 (*base case: 0\<le>a+b*)
 apply (simp add: negDivAlg_eqn)
(*main argument*)
apply (subst negDivAlg_eqn, assumption)
apply (erule splitE)
apply (auto simp add: right_distrib Let_def)
done


subsection{*Existence Shown by Proving the Division Algorithm to be Correct*}

(*the case a=0*)
lemma quorem_0: "b ~= 0 ==> quorem ((0,b), (0,0))"
by (auto simp add: quorem_def linorder_neq_iff)

lemma posDivAlg_0 [simp]: "posDivAlg (0, b) = (0, 0)"
by (subst posDivAlg.simps, auto)

lemma negDivAlg_minus1 [simp]: "negDivAlg (-1, b) = (-1, b - 1)"
by (subst negDivAlg.simps, auto)

lemma negateSnd_eq [simp]: "negateSnd(q,r) = (q,-r)"
by (unfold negateSnd_def, auto)

lemma quorem_neg: "quorem ((-a,-b), qr) ==> quorem ((a,b), negateSnd qr)"
by (auto simp add: split_ifs quorem_def)

lemma divAlg_correct: "b ~= 0 ==> quorem ((a,b), divAlg(a,b))"
by (force simp add: linorder_neq_iff quorem_0 divAlg_def quorem_neg
                    posDivAlg_correct negDivAlg_correct)

(** Arbitrary definitions for division by zero.  Useful to simplify 
    certain equations **)

lemma DIVISION_BY_ZERO [simp]: "a div (0::int) = 0 & a mod (0::int) = a"
by (simp add: div_def mod_def divAlg_def posDivAlg.simps)  

(** Basic laws about division and remainder **)

lemma zmod_zdiv_equality: "(a::int) = b * (a div b) + (a mod b)"
apply (case_tac "b = 0", simp)
apply (cut_tac a = a and b = b in divAlg_correct)
apply (auto simp add: quorem_def div_def mod_def)
done

lemma zdiv_zmod_equality: "(b * (a div b) + (a mod b)) + k = (a::int)+k"
by(simp add: zmod_zdiv_equality[symmetric])

lemma zdiv_zmod_equality2: "((a div b) * b + (a mod b)) + k = (a::int)+k"
by(simp add: zmult_commute zmod_zdiv_equality[symmetric])

use "IntDiv_setup.ML"

lemma pos_mod_conj : "(0::int) < b ==> 0 \<le> a mod b & a mod b < b"
apply (cut_tac a = a and b = b in divAlg_correct)
apply (auto simp add: quorem_def mod_def)
done

lemmas pos_mod_sign[simp]  = pos_mod_conj [THEN conjunct1, standard]
   and pos_mod_bound[simp] = pos_mod_conj [THEN conjunct2, standard]

lemma neg_mod_conj : "b < (0::int) ==> a mod b \<le> 0 & b < a mod b"
apply (cut_tac a = a and b = b in divAlg_correct)
apply (auto simp add: quorem_def div_def mod_def)
done

lemmas neg_mod_sign[simp]  = neg_mod_conj [THEN conjunct1, standard]
   and neg_mod_bound[simp] = neg_mod_conj [THEN conjunct2, standard]



(** proving general properties of div and mod **)

lemma quorem_div_mod: "b ~= 0 ==> quorem ((a, b), (a div b, a mod b))"
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (force simp add: quorem_def linorder_neq_iff)
done

lemma quorem_div: "[| quorem((a,b),(q,r));  b ~= 0 |] ==> a div b = q"
by (simp add: quorem_div_mod [THEN unique_quotient])

lemma quorem_mod: "[| quorem((a,b),(q,r));  b ~= 0 |] ==> a mod b = r"
by (simp add: quorem_div_mod [THEN unique_remainder])

lemma div_pos_pos_trivial: "[| (0::int) \<le> a;  a < b |] ==> a div b = 0"
apply (rule quorem_div)
apply (auto simp add: quorem_def)
done

lemma div_neg_neg_trivial: "[| a \<le> (0::int);  b < a |] ==> a div b = 0"
apply (rule quorem_div)
apply (auto simp add: quorem_def)
done

lemma div_pos_neg_trivial: "[| (0::int) < a;  a+b \<le> 0 |] ==> a div b = -1"
apply (rule quorem_div)
apply (auto simp add: quorem_def)
done

(*There is no div_neg_pos_trivial because  0 div b = 0 would supersede it*)

lemma mod_pos_pos_trivial: "[| (0::int) \<le> a;  a < b |] ==> a mod b = a"
apply (rule_tac q = 0 in quorem_mod)
apply (auto simp add: quorem_def)
done

lemma mod_neg_neg_trivial: "[| a \<le> (0::int);  b < a |] ==> a mod b = a"
apply (rule_tac q = 0 in quorem_mod)
apply (auto simp add: quorem_def)
done

lemma mod_pos_neg_trivial: "[| (0::int) < a;  a+b \<le> 0 |] ==> a mod b = a+b"
apply (rule_tac q = "-1" in quorem_mod)
apply (auto simp add: quorem_def)
done

(*There is no mod_neg_pos_trivial...*)


(*Simpler laws such as -a div b = -(a div b) FAIL, but see just below*)
lemma zdiv_zminus_zminus [simp]: "(-a) div (-b) = a div (b::int)"
apply (case_tac "b = 0", simp)
apply (simp add: quorem_div_mod [THEN quorem_neg, simplified, 
                                 THEN quorem_div, THEN sym])

done

(*Simpler laws such as -a mod b = -(a mod b) FAIL, but see just below*)
lemma zmod_zminus_zminus [simp]: "(-a) mod (-b) = - (a mod (b::int))"
apply (case_tac "b = 0", simp)
apply (subst quorem_div_mod [THEN quorem_neg, simplified, THEN quorem_mod],
       auto)
done

subsection{*div, mod and unary minus*}

lemma zminus1_lemma:
     "quorem((a,b),(q,r))  
      ==> quorem ((-a,b), (if r=0 then -q else -q - 1),  
                          (if r=0 then 0 else b-r))"
by (force simp add: split_ifs quorem_def linorder_neq_iff right_diff_distrib)


lemma zdiv_zminus1_eq_if:
     "b ~= (0::int)  
      ==> (-a) div b =  
          (if a mod b = 0 then - (a div b) else  - (a div b) - 1)"
by (blast intro: quorem_div_mod [THEN zminus1_lemma, THEN quorem_div])

lemma zmod_zminus1_eq_if:
     "(-a::int) mod b = (if a mod b = 0 then 0 else  b - (a mod b))"
apply (case_tac "b = 0", simp)
apply (blast intro: quorem_div_mod [THEN zminus1_lemma, THEN quorem_mod])
done

lemma zdiv_zminus2: "a div (-b) = (-a::int) div b"
by (cut_tac a = "-a" in zdiv_zminus_zminus, auto)

lemma zmod_zminus2: "a mod (-b) = - ((-a::int) mod b)"
by (cut_tac a = "-a" and b = b in zmod_zminus_zminus, auto)

lemma zdiv_zminus2_eq_if:
     "b ~= (0::int)  
      ==> a div (-b) =  
          (if a mod b = 0 then - (a div b) else  - (a div b) - 1)"
by (simp add: zdiv_zminus1_eq_if zdiv_zminus2)

lemma zmod_zminus2_eq_if:
     "a mod (-b::int) = (if a mod b = 0 then 0 else  (a mod b) - b)"
by (simp add: zmod_zminus1_eq_if zmod_zminus2)


subsection{*Division of a Number by Itself*}

lemma self_quotient_aux1: "[| (0::int) < a; a = r + a*q; r < a |] ==> 1 \<le> q"
apply (subgoal_tac "0 < a*q")
 apply (simp add: zero_less_mult_iff, arith)
done

lemma self_quotient_aux2: "[| (0::int) < a; a = r + a*q; 0 \<le> r |] ==> q \<le> 1"
apply (subgoal_tac "0 \<le> a* (1-q) ")
 apply (simp add: zero_le_mult_iff)
apply (simp add: right_diff_distrib)
done

lemma self_quotient: "[| quorem((a,a),(q,r));  a ~= (0::int) |] ==> q = 1"
apply (simp add: split_ifs quorem_def linorder_neq_iff)
apply (rule order_antisym, safe, simp_all (no_asm_use))
apply (rule_tac [3] a = "-a" and r = "-r" in self_quotient_aux1)
apply (rule_tac a = "-a" and r = "-r" in self_quotient_aux2)
apply (force intro: self_quotient_aux1 self_quotient_aux2 simp only: zadd_commute zmult_zminus)+
done

lemma self_remainder: "[| quorem((a,a),(q,r));  a ~= (0::int) |] ==> r = 0"
apply (frule self_quotient, assumption)
apply (simp add: quorem_def)
done

lemma zdiv_self [simp]: "a ~= 0 ==> a div a = (1::int)"
by (simp add: quorem_div_mod [THEN self_quotient])

(*Here we have 0 mod 0 = 0, also assumed by Knuth (who puts m mod 0 = 0) *)
lemma zmod_self [simp]: "a mod a = (0::int)"
apply (case_tac "a = 0", simp)
apply (simp add: quorem_div_mod [THEN self_remainder])
done


subsection{*Computation of Division and Remainder*}

lemma zdiv_zero [simp]: "(0::int) div b = 0"
by (simp add: div_def divAlg_def)

lemma div_eq_minus1: "(0::int) < b ==> -1 div b = -1"
by (simp add: div_def divAlg_def)

lemma zmod_zero [simp]: "(0::int) mod b = 0"
by (simp add: mod_def divAlg_def)

lemma zdiv_minus1: "(0::int) < b ==> -1 div b = -1"
by (simp add: div_def divAlg_def)

lemma zmod_minus1: "(0::int) < b ==> -1 mod b = b - 1"
by (simp add: mod_def divAlg_def)

(** a positive, b positive **)

lemma div_pos_pos: "[| 0 < a;  0 \<le> b |] ==> a div b = fst (posDivAlg(a,b))"
by (simp add: div_def divAlg_def)

lemma mod_pos_pos: "[| 0 < a;  0 \<le> b |] ==> a mod b = snd (posDivAlg(a,b))"
by (simp add: mod_def divAlg_def)

(** a negative, b positive **)

lemma div_neg_pos: "[| a < 0;  0 < b |] ==> a div b = fst (negDivAlg(a,b))"
by (simp add: div_def divAlg_def)

lemma mod_neg_pos: "[| a < 0;  0 < b |] ==> a mod b = snd (negDivAlg(a,b))"
by (simp add: mod_def divAlg_def)

(** a positive, b negative **)

lemma div_pos_neg:
     "[| 0 < a;  b < 0 |] ==> a div b = fst (negateSnd(negDivAlg(-a,-b)))"
by (simp add: div_def divAlg_def)

lemma mod_pos_neg:
     "[| 0 < a;  b < 0 |] ==> a mod b = snd (negateSnd(negDivAlg(-a,-b)))"
by (simp add: mod_def divAlg_def)

(** a negative, b negative **)

lemma div_neg_neg:
     "[| a < 0;  b \<le> 0 |] ==> a div b = fst (negateSnd(posDivAlg(-a,-b)))"
by (simp add: div_def divAlg_def)

lemma mod_neg_neg:
     "[| a < 0;  b \<le> 0 |] ==> a mod b = snd (negateSnd(posDivAlg(-a,-b)))"
by (simp add: mod_def divAlg_def)

text {*Simplify expresions in which div and mod combine numerical constants*}

declare div_pos_pos [of "number_of v" "number_of w", standard, simp]
declare div_neg_pos [of "number_of v" "number_of w", standard, simp]
declare div_pos_neg [of "number_of v" "number_of w", standard, simp]
declare div_neg_neg [of "number_of v" "number_of w", standard, simp]

declare mod_pos_pos [of "number_of v" "number_of w", standard, simp]
declare mod_neg_pos [of "number_of v" "number_of w", standard, simp]
declare mod_pos_neg [of "number_of v" "number_of w", standard, simp]
declare mod_neg_neg [of "number_of v" "number_of w", standard, simp]

declare posDivAlg_eqn [of "number_of v" "number_of w", standard, simp]
declare negDivAlg_eqn [of "number_of v" "number_of w", standard, simp]


(** Special-case simplification **)

lemma zmod_1 [simp]: "a mod (1::int) = 0"
apply (cut_tac a = a and b = 1 in pos_mod_sign)
apply (cut_tac [2] a = a and b = 1 in pos_mod_bound)
apply (auto simp del:pos_mod_bound pos_mod_sign)
done

lemma zdiv_1 [simp]: "a div (1::int) = a"
by (cut_tac a = a and b = 1 in zmod_zdiv_equality, auto)

lemma zmod_minus1_right [simp]: "a mod (-1::int) = 0"
apply (cut_tac a = a and b = "-1" in neg_mod_sign)
apply (cut_tac [2] a = a and b = "-1" in neg_mod_bound)
apply (auto simp del: neg_mod_sign neg_mod_bound)
done

lemma zdiv_minus1_right [simp]: "a div (-1::int) = -a"
by (cut_tac a = a and b = "-1" in zmod_zdiv_equality, auto)

(** The last remaining special cases for constant arithmetic:
    1 div z and 1 mod z **)

declare div_pos_pos [OF int_0_less_1, of "number_of w", standard, simp]
declare div_pos_neg [OF int_0_less_1, of "number_of w", standard, simp]
declare mod_pos_pos [OF int_0_less_1, of "number_of w", standard, simp]
declare mod_pos_neg [OF int_0_less_1, of "number_of w", standard, simp]

declare posDivAlg_eqn [of concl: 1 "number_of w", standard, simp]
declare negDivAlg_eqn [of concl: 1 "number_of w", standard, simp]


subsection{*Monotonicity in the First Argument (Dividend)*}

lemma zdiv_mono1: "[| a \<le> a';  0 < (b::int) |] ==> a div b \<le> a' div b"
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (cut_tac a = a' and b = b in zmod_zdiv_equality)
apply (rule unique_quotient_lemma)
apply (erule subst)
apply (erule subst)
apply (simp_all)
done

lemma zdiv_mono1_neg: "[| a \<le> a';  (b::int) < 0 |] ==> a' div b \<le> a div b"
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (cut_tac a = a' and b = b in zmod_zdiv_equality)
apply (rule unique_quotient_lemma_neg)
apply (erule subst)
apply (erule subst)
apply (simp_all)
done


subsection{*Monotonicity in the Second Argument (Divisor)*}

lemma q_pos_lemma:
     "[| 0 \<le> b'*q' + r'; r' < b';  0 < b' |] ==> 0 \<le> (q'::int)"
apply (subgoal_tac "0 < b'* (q' + 1) ")
 apply (simp add: zero_less_mult_iff)
apply (simp add: right_distrib)
done

lemma zdiv_mono2_lemma:
     "[| b*q + r = b'*q' + r';  0 \<le> b'*q' + r';   
         r' < b';  0 \<le> r;  0 < b';  b' \<le> b |]   
      ==> q \<le> (q'::int)"
apply (frule q_pos_lemma, assumption+) 
apply (subgoal_tac "b*q < b* (q' + 1) ")
 apply (simp add: mult_less_cancel_left)
apply (subgoal_tac "b*q = r' - r + b'*q'")
 prefer 2 apply simp
apply (simp (no_asm_simp) add: right_distrib)
apply (subst zadd_commute, rule zadd_zless_mono, arith)
apply (rule mult_right_mono, auto)
done

lemma zdiv_mono2:
     "[| (0::int) \<le> a;  0 < b';  b' \<le> b |] ==> a div b \<le> a div b'"
apply (subgoal_tac "b ~= 0")
 prefer 2 apply arith
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (cut_tac a = a and b = b' in zmod_zdiv_equality)
apply (rule zdiv_mono2_lemma)
apply (erule subst)
apply (erule subst)
apply (simp_all)
done

lemma q_neg_lemma:
     "[| b'*q' + r' < 0;  0 \<le> r';  0 < b' |] ==> q' \<le> (0::int)"
apply (subgoal_tac "b'*q' < 0")
 apply (simp add: mult_less_0_iff, arith)
done

lemma zdiv_mono2_neg_lemma:
     "[| b*q + r = b'*q' + r';  b'*q' + r' < 0;   
         r < b;  0 \<le> r';  0 < b';  b' \<le> b |]   
      ==> q' \<le> (q::int)"
apply (frule q_neg_lemma, assumption+) 
apply (subgoal_tac "b*q' < b* (q + 1) ")
 apply (simp add: mult_less_cancel_left)
apply (simp add: right_distrib)
apply (subgoal_tac "b*q' \<le> b'*q'")
 prefer 2 apply (simp add: mult_right_mono_neg)
apply (subgoal_tac "b'*q' < b + b*q")
 apply arith
apply simp 
done

lemma zdiv_mono2_neg:
     "[| a < (0::int);  0 < b';  b' \<le> b |] ==> a div b' \<le> a div b"
apply (cut_tac a = a and b = b in zmod_zdiv_equality)
apply (cut_tac a = a and b = b' in zmod_zdiv_equality)
apply (rule zdiv_mono2_neg_lemma)
apply (erule subst)
apply (erule subst)
apply (simp_all)
done


subsection{*More Algebraic Laws for div and mod*}

(** proving (a*b) div c = a * (b div c) + a * (b mod c) **)

lemma zmult1_lemma:
     "[| quorem((b,c),(q,r));  c ~= 0 |]  
      ==> quorem ((a*b, c), (a*q + a*r div c, a*r mod c))"
by (force simp add: split_ifs quorem_def linorder_neq_iff right_distrib)

lemma zdiv_zmult1_eq: "(a*b) div c = a*(b div c) + a*(b mod c) div (c::int)"
apply (case_tac "c = 0", simp)
apply (blast intro: quorem_div_mod [THEN zmult1_lemma, THEN quorem_div])
done

lemma zmod_zmult1_eq: "(a*b) mod c = a*(b mod c) mod (c::int)"
apply (case_tac "c = 0", simp)
apply (blast intro: quorem_div_mod [THEN zmult1_lemma, THEN quorem_mod])
done

lemma zmod_zmult1_eq': "(a*b) mod (c::int) = ((a mod c) * b) mod c"
apply (rule trans)
apply (rule_tac s = "b*a mod c" in trans)
apply (rule_tac [2] zmod_zmult1_eq)
apply (simp_all add: zmult_commute)
done

lemma zmod_zmult_distrib: "(a*b) mod (c::int) = ((a mod c) * (b mod c)) mod c"
apply (rule zmod_zmult1_eq' [THEN trans])
apply (rule zmod_zmult1_eq)
done

lemma zdiv_zmult_self1 [simp]: "b ~= (0::int) ==> (a*b) div b = a"
by (simp add: zdiv_zmult1_eq)

lemma zdiv_zmult_self2 [simp]: "b ~= (0::int) ==> (b*a) div b = a"
by (subst zmult_commute, erule zdiv_zmult_self1)

lemma zmod_zmult_self1 [simp]: "(a*b) mod b = (0::int)"
by (simp add: zmod_zmult1_eq)

lemma zmod_zmult_self2 [simp]: "(b*a) mod b = (0::int)"
by (simp add: zmult_commute zmod_zmult1_eq)

lemma zmod_eq_0_iff: "(m mod d = 0) = (EX q::int. m = d*q)"
proof
  assume "m mod d = 0"
  with zmod_zdiv_equality[of m d] show "EX q::int. m = d*q" by auto
next
  assume "EX q::int. m = d*q"
  thus "m mod d = 0" by auto
qed

declare zmod_eq_0_iff [THEN iffD1, dest!]

(** proving (a+b) div c = a div c + b div c + ((a mod c + b mod c) div c) **)

lemma zadd1_lemma:
     "[| quorem((a,c),(aq,ar));  quorem((b,c),(bq,br));  c ~= 0 |]  
      ==> quorem ((a+b, c), (aq + bq + (ar+br) div c, (ar+br) mod c))"
by (force simp add: split_ifs quorem_def linorder_neq_iff right_distrib)

(*NOT suitable for rewriting: the RHS has an instance of the LHS*)
lemma zdiv_zadd1_eq:
     "(a+b) div (c::int) = a div c + b div c + ((a mod c + b mod c) div c)"
apply (case_tac "c = 0", simp)
apply (blast intro: zadd1_lemma [OF quorem_div_mod quorem_div_mod] quorem_div)
done

lemma zmod_zadd1_eq: "(a+b) mod (c::int) = (a mod c + b mod c) mod c"
apply (case_tac "c = 0", simp)
apply (blast intro: zadd1_lemma [OF quorem_div_mod quorem_div_mod] quorem_mod)
done

lemma mod_div_trivial [simp]: "(a mod b) div b = (0::int)"
apply (case_tac "b = 0", simp)
apply (auto simp add: linorder_neq_iff div_pos_pos_trivial div_neg_neg_trivial)
done

lemma mod_mod_trivial [simp]: "(a mod b) mod b = a mod (b::int)"
apply (case_tac "b = 0", simp)
apply (force simp add: linorder_neq_iff mod_pos_pos_trivial mod_neg_neg_trivial)
done

lemma zmod_zadd_left_eq: "(a+b) mod (c::int) = ((a mod c) + b) mod c"
apply (rule trans [symmetric])
apply (rule zmod_zadd1_eq, simp)
apply (rule zmod_zadd1_eq [symmetric])
done

lemma zmod_zadd_right_eq: "(a+b) mod (c::int) = (a + (b mod c)) mod c"
apply (rule trans [symmetric])
apply (rule zmod_zadd1_eq, simp)
apply (rule zmod_zadd1_eq [symmetric])
done

lemma zdiv_zadd_self1[simp]: "a ~= (0::int) ==> (a+b) div a = b div a + 1"
by (simp add: zdiv_zadd1_eq)

lemma zdiv_zadd_self2[simp]: "a ~= (0::int) ==> (b+a) div a = b div a + 1"
by (simp add: zdiv_zadd1_eq)

lemma zmod_zadd_self1[simp]: "(a+b) mod a = b mod (a::int)"
apply (case_tac "a = 0", simp)
apply (simp add: zmod_zadd1_eq)
done

lemma zmod_zadd_self2[simp]: "(b+a) mod a = b mod (a::int)"
apply (case_tac "a = 0", simp)
apply (simp add: zmod_zadd1_eq)
done


subsection{*Proving  @{term "a div (b*c) = (a div b) div c"} *}

(*The condition c>0 seems necessary.  Consider that 7 div ~6 = ~2 but
  7 div 2 div ~3 = 3 div ~3 = ~1.  The subcase (a div b) mod c = 0 seems
  to cause particular problems.*)

(** first, four lemmas to bound the remainder for the cases b<0 and b>0 **)

lemma zmult2_lemma_aux1: "[| (0::int) < c;  b < r;  r \<le> 0 |] ==> b*c < b*(q mod c) + r"
apply (subgoal_tac "b * (c - q mod c) < r * 1")
apply (simp add: right_diff_distrib)
apply (rule order_le_less_trans)
apply (erule_tac [2] mult_strict_right_mono)
apply (rule mult_left_mono_neg)
apply (auto simp add: compare_rls zadd_commute [of 1]
                      add1_zle_eq pos_mod_bound)
done

lemma zmult2_lemma_aux2: "[| (0::int) < c;   b < r;  r \<le> 0 |] ==> b * (q mod c) + r \<le> 0"
apply (subgoal_tac "b * (q mod c) \<le> 0")
 apply arith
apply (simp add: mult_le_0_iff)
done

lemma zmult2_lemma_aux3: "[| (0::int) < c;  0 \<le> r;  r < b |] ==> 0 \<le> b * (q mod c) + r"
apply (subgoal_tac "0 \<le> b * (q mod c) ")
apply arith
apply (simp add: zero_le_mult_iff)
done

lemma zmult2_lemma_aux4: "[| (0::int) < c; 0 \<le> r; r < b |] ==> b * (q mod c) + r < b * c"
apply (subgoal_tac "r * 1 < b * (c - q mod c) ")
apply (simp add: right_diff_distrib)
apply (rule order_less_le_trans)
apply (erule mult_strict_right_mono)
apply (rule_tac [2] mult_left_mono)
apply (auto simp add: compare_rls zadd_commute [of 1]
                      add1_zle_eq pos_mod_bound)
done

lemma zmult2_lemma: "[| quorem ((a,b), (q,r));  b ~= 0;  0 < c |]  
      ==> quorem ((a, b*c), (q div c, b*(q mod c) + r))"
by (auto simp add: mult_ac quorem_def linorder_neq_iff
                   zero_less_mult_iff right_distrib [symmetric] 
                   zmult2_lemma_aux1 zmult2_lemma_aux2 zmult2_lemma_aux3 zmult2_lemma_aux4)

lemma zdiv_zmult2_eq: "(0::int) < c ==> a div (b*c) = (a div b) div c"
apply (case_tac "b = 0", simp)
apply (force simp add: quorem_div_mod [THEN zmult2_lemma, THEN quorem_div])
done

lemma zmod_zmult2_eq:
     "(0::int) < c ==> a mod (b*c) = b*(a div b mod c) + a mod b"
apply (case_tac "b = 0", simp)
apply (force simp add: quorem_div_mod [THEN zmult2_lemma, THEN quorem_mod])
done


subsection{*Cancellation of Common Factors in div*}

lemma zdiv_zmult_zmult1_aux1: "[| (0::int) < b;  c ~= 0 |] ==> (c*a) div (c*b) = a div b"
by (subst zdiv_zmult2_eq, auto)

lemma zdiv_zmult_zmult1_aux2: "[| b < (0::int);  c ~= 0 |] ==> (c*a) div (c*b) = a div b"
apply (subgoal_tac " (c * (-a)) div (c * (-b)) = (-a) div (-b) ")
apply (rule_tac [2] zdiv_zmult_zmult1_aux1, auto)
done

lemma zdiv_zmult_zmult1: "c ~= (0::int) ==> (c*a) div (c*b) = a div b"
apply (case_tac "b = 0", simp)
apply (auto simp add: linorder_neq_iff zdiv_zmult_zmult1_aux1 zdiv_zmult_zmult1_aux2)
done

lemma zdiv_zmult_zmult2: "c ~= (0::int) ==> (a*c) div (b*c) = a div b"
apply (drule zdiv_zmult_zmult1)
apply (auto simp add: zmult_commute)
done



subsection{*Distribution of Factors over mod*}

lemma zmod_zmult_zmult1_aux1: "[| (0::int) < b;  c ~= 0 |] ==> (c*a) mod (c*b) = c * (a mod b)"
by (subst zmod_zmult2_eq, auto)

lemma zmod_zmult_zmult1_aux2: "[| b < (0::int);  c ~= 0 |] ==> (c*a) mod (c*b) = c * (a mod b)"
apply (subgoal_tac " (c * (-a)) mod (c * (-b)) = c * ((-a) mod (-b))")
apply (rule_tac [2] zmod_zmult_zmult1_aux1, auto)
done

lemma zmod_zmult_zmult1: "(c*a) mod (c*b) = (c::int) * (a mod b)"
apply (case_tac "b = 0", simp)
apply (case_tac "c = 0", simp)
apply (auto simp add: linorder_neq_iff zmod_zmult_zmult1_aux1 zmod_zmult_zmult1_aux2)
done

lemma zmod_zmult_zmult2: "(a*c) mod (b*c) = (a mod b) * (c::int)"
apply (cut_tac c = c in zmod_zmult_zmult1)
apply (auto simp add: zmult_commute)
done


subsection {*Splitting Rules for div and mod*}

text{*The proofs of the two lemmas below are essentially identical*}

lemma split_pos_lemma:
 "0<k ==> 
    P(n div k :: int)(n mod k) = (\<forall>i j. 0\<le>j & j<k & n = k*i + j --> P i j)"
apply (rule iffI)
 apply clarify
 apply (erule_tac P="P ?x ?y" in rev_mp)  
 apply (subst zmod_zadd1_eq) 
 apply (subst zdiv_zadd1_eq) 
 apply (simp add: div_pos_pos_trivial mod_pos_pos_trivial)  
txt{*converse direction*}
apply (drule_tac x = "n div k" in spec) 
apply (drule_tac x = "n mod k" in spec) 
apply (simp)
done

lemma split_neg_lemma:
 "k<0 ==>
    P(n div k :: int)(n mod k) = (\<forall>i j. k<j & j\<le>0 & n = k*i + j --> P i j)"
apply (rule iffI)
 apply clarify
 apply (erule_tac P="P ?x ?y" in rev_mp)  
 apply (subst zmod_zadd1_eq) 
 apply (subst zdiv_zadd1_eq) 
 apply (simp add: div_neg_neg_trivial mod_neg_neg_trivial)  
txt{*converse direction*}
apply (drule_tac x = "n div k" in spec) 
apply (drule_tac x = "n mod k" in spec) 
apply (simp)
done

lemma split_zdiv:
 "P(n div k :: int) =
  ((k = 0 --> P 0) & 
   (0<k --> (\<forall>i j. 0\<le>j & j<k & n = k*i + j --> P i)) & 
   (k<0 --> (\<forall>i j. k<j & j\<le>0 & n = k*i + j --> P i)))"
apply (case_tac "k=0")
 apply (simp)
apply (simp only: linorder_neq_iff)
apply (erule disjE) 
 apply (simp_all add: split_pos_lemma [of concl: "%x y. P x"] 
                      split_neg_lemma [of concl: "%x y. P x"])
done

lemma split_zmod:
 "P(n mod k :: int) =
  ((k = 0 --> P n) & 
   (0<k --> (\<forall>i j. 0\<le>j & j<k & n = k*i + j --> P j)) & 
   (k<0 --> (\<forall>i j. k<j & j\<le>0 & n = k*i + j --> P j)))"
apply (case_tac "k=0")
 apply (simp)
apply (simp only: linorder_neq_iff)
apply (erule disjE) 
 apply (simp_all add: split_pos_lemma [of concl: "%x y. P y"] 
                      split_neg_lemma [of concl: "%x y. P y"])
done

(* Enable arith to deal with div 2 and mod 2: *)
declare split_zdiv [of _ _ "number_of k", simplified, standard, arith_split]
declare split_zmod [of _ _ "number_of k", simplified, standard, arith_split]


subsection{*Speeding up the Division Algorithm with Shifting*}

(** computing div by shifting **)

lemma pos_zdiv_mult_2: "(0::int) \<le> a ==> (1 + 2*b) div (2*a) = b div a"
proof cases
  assume "a=0"
    thus ?thesis by simp
next
  assume "a\<noteq>0" and le_a: "0\<le>a"   
  hence a_pos: "1 \<le> a" by arith
  hence one_less_a2: "1 < 2*a" by arith
  hence le_2a: "2 * (1 + b mod a) \<le> 2 * a"
    by (simp add: mult_le_cancel_left zadd_commute [of 1] add1_zle_eq)
  with a_pos have "0 \<le> b mod a" by simp
  hence le_addm: "0 \<le> 1 mod (2*a) + 2*(b mod a)"
    by (simp add: mod_pos_pos_trivial one_less_a2)
  with  le_2a
  have "(1 mod (2*a) + 2*(b mod a)) div (2*a) = 0"
    by (simp add: div_pos_pos_trivial le_addm mod_pos_pos_trivial one_less_a2
                  right_distrib) 
  thus ?thesis
    by (subst zdiv_zadd1_eq,
        simp add: zdiv_zmult_zmult1 zmod_zmult_zmult1 one_less_a2
                  div_pos_pos_trivial)
qed

lemma neg_zdiv_mult_2: "a \<le> (0::int) ==> (1 + 2*b) div (2*a) = (b+1) div a"
apply (subgoal_tac " (1 + 2* (-b - 1)) div (2 * (-a)) = (-b - 1) div (-a) ")
apply (rule_tac [2] pos_zdiv_mult_2)
apply (auto simp add: minus_mult_right [symmetric] right_diff_distrib)
apply (subgoal_tac " (-1 - (2 * b)) = - (1 + (2 * b))")
apply (simp only: zdiv_zminus_zminus diff_minus minus_add_distrib [symmetric],
       simp) 
done


(*Not clear why this must be proved separately; probably number_of causes
  simplification problems*)
lemma not_0_le_lemma: "~ 0 \<le> x ==> x \<le> (0::int)"
by auto

lemma zdiv_number_of_BIT[simp]:
     "number_of (v BIT b) div number_of (w BIT False) =  
          (if ~b | (0::int) \<le> number_of w                    
           then number_of v div (number_of w)     
           else (number_of v + (1::int)) div (number_of w))"
apply (simp only: number_of_eq Bin_simps UNIV_I split: split_if) 
apply (simp add: zdiv_zmult_zmult1 pos_zdiv_mult_2 neg_zdiv_mult_2 add_ac)
done


subsection{*Computing mod by Shifting (proofs resemble those for div)*}

lemma pos_zmod_mult_2:
     "(0::int) \<le> a ==> (1 + 2*b) mod (2*a) = 1 + 2 * (b mod a)"
apply (case_tac "a = 0", simp)
apply (subgoal_tac "1 \<le> a")
 prefer 2 apply arith
apply (subgoal_tac "1 < a * 2")
 prefer 2 apply arith
apply (subgoal_tac "2* (1 + b mod a) \<le> 2*a")
 apply (rule_tac [2] mult_left_mono)
apply (auto simp add: zadd_commute [of 1] zmult_commute add1_zle_eq 
                      pos_mod_bound)
apply (subst zmod_zadd1_eq)
apply (simp add: zmod_zmult_zmult2 mod_pos_pos_trivial)
apply (rule mod_pos_pos_trivial)
apply (auto simp add: mod_pos_pos_trivial left_distrib)
apply (subgoal_tac "0 \<le> b mod a", arith)
apply (simp)
done

lemma neg_zmod_mult_2:
     "a \<le> (0::int) ==> (1 + 2*b) mod (2*a) = 2 * ((b+1) mod a) - 1"
apply (subgoal_tac "(1 + 2* (-b - 1)) mod (2* (-a)) = 
                    1 + 2* ((-b - 1) mod (-a))")
apply (rule_tac [2] pos_zmod_mult_2)
apply (auto simp add: minus_mult_right [symmetric] right_diff_distrib)
apply (subgoal_tac " (-1 - (2 * b)) = - (1 + (2 * b))")
 prefer 2 apply simp 
apply (simp only: zmod_zminus_zminus diff_minus minus_add_distrib [symmetric])
done

lemma zmod_number_of_BIT [simp]:
     "number_of (v BIT b) mod number_of (w BIT False) =  
          (if b then  
                if (0::int) \<le> number_of w  
                then 2 * (number_of v mod number_of w) + 1     
                else 2 * ((number_of v + (1::int)) mod number_of w) - 1   
           else 2 * (number_of v mod number_of w))"
apply (simp only: number_of_eq Bin_simps UNIV_I split: split_if) 
apply (simp add: zmod_zmult_zmult1 pos_zmod_mult_2 
                 not_0_le_lemma neg_zmod_mult_2 add_ac)
done



subsection{*Quotients of Signs*}

lemma div_neg_pos_less0: "[| a < (0::int);  0 < b |] ==> a div b < 0"
apply (subgoal_tac "a div b \<le> -1", force)
apply (rule order_trans)
apply (rule_tac a' = "-1" in zdiv_mono1)
apply (auto simp add: zdiv_minus1)
done

lemma div_nonneg_neg_le0: "[| (0::int) \<le> a;  b < 0 |] ==> a div b \<le> 0"
by (drule zdiv_mono1_neg, auto)

lemma pos_imp_zdiv_nonneg_iff: "(0::int) < b ==> (0 \<le> a div b) = (0 \<le> a)"
apply auto
apply (drule_tac [2] zdiv_mono1)
apply (auto simp add: linorder_neq_iff)
apply (simp (no_asm_use) add: linorder_not_less [symmetric])
apply (blast intro: div_neg_pos_less0)
done

lemma neg_imp_zdiv_nonneg_iff:
     "b < (0::int) ==> (0 \<le> a div b) = (a \<le> (0::int))"
apply (subst zdiv_zminus_zminus [symmetric])
apply (subst pos_imp_zdiv_nonneg_iff, auto)
done

(*But not (a div b \<le> 0 iff a\<le>0); consider a=1, b=2 when a div b = 0.*)
lemma pos_imp_zdiv_neg_iff: "(0::int) < b ==> (a div b < 0) = (a < 0)"
by (simp add: linorder_not_le [symmetric] pos_imp_zdiv_nonneg_iff)

(*Again the law fails for \<le>: consider a = -1, b = -2 when a div b = 0*)
lemma neg_imp_zdiv_neg_iff: "b < (0::int) ==> (a div b < 0) = (0 < a)"
by (simp add: linorder_not_le [symmetric] neg_imp_zdiv_nonneg_iff)


subsection {* The Divides Relation *}

lemma zdvd_iff_zmod_eq_0: "(m dvd n) = (n mod m = (0::int))"
by(simp add:dvd_def zmod_eq_0_iff)

lemma zdvd_0_right [iff]: "(m::int) dvd 0"
  apply (unfold dvd_def)
  apply (blast intro: mult_zero_right [symmetric])
  done

lemma zdvd_0_left [iff]: "(0 dvd (m::int)) = (m = 0)"
  by (unfold dvd_def, auto)

lemma zdvd_1_left [iff]: "1 dvd (m::int)"
  by (unfold dvd_def, simp)

lemma zdvd_refl [simp]: "m dvd (m::int)"
  apply (unfold dvd_def)
  apply (blast intro: zmult_1_right [symmetric])
  done

lemma zdvd_trans: "m dvd n ==> n dvd k ==> m dvd (k::int)"
  apply (unfold dvd_def)
  apply (blast intro: zmult_assoc)
  done

lemma zdvd_zminus_iff: "(m dvd -n) = (m dvd (n::int))"
  apply (unfold dvd_def, auto)
   apply (rule_tac [!] x = "-k" in exI, auto)
  done

lemma zdvd_zminus2_iff: "(-m dvd n) = (m dvd (n::int))"
  apply (unfold dvd_def, auto)
   apply (rule_tac [!] x = "-k" in exI, auto)
  done

lemma zdvd_anti_sym:
    "0 < m ==> 0 < n ==> m dvd n ==> n dvd m ==> m = (n::int)"
  apply (unfold dvd_def, auto)
  apply (simp add: zmult_assoc zmult_eq_self_iff zero_less_mult_iff zmult_eq_1_iff)
  done

lemma zdvd_zadd: "k dvd m ==> k dvd n ==> k dvd (m + n :: int)"
  apply (unfold dvd_def)
  apply (blast intro: right_distrib [symmetric])
  done

lemma zdvd_zdiff: "k dvd m ==> k dvd n ==> k dvd (m - n :: int)"
  apply (unfold dvd_def)
  apply (blast intro: right_diff_distrib [symmetric])
  done

lemma zdvd_zdiffD: "k dvd m - n ==> k dvd n ==> k dvd (m::int)"
  apply (subgoal_tac "m = n + (m - n)")
   apply (erule ssubst)
   apply (blast intro: zdvd_zadd, simp)
  done

lemma zdvd_zmult: "k dvd (n::int) ==> k dvd m * n"
  apply (unfold dvd_def)
  apply (blast intro: mult_left_commute)
  done

lemma zdvd_zmult2: "k dvd (m::int) ==> k dvd m * n"
  apply (subst zmult_commute)
  apply (erule zdvd_zmult)
  done

lemma [iff]: "(k::int) dvd m * k"
  apply (rule zdvd_zmult)
  apply (rule zdvd_refl)
  done

lemma [iff]: "(k::int) dvd k * m"
  apply (rule zdvd_zmult2)
  apply (rule zdvd_refl)
  done

lemma zdvd_zmultD2: "j * k dvd n ==> j dvd (n::int)"
  apply (unfold dvd_def)
  apply (simp add: zmult_assoc, blast)
  done

lemma zdvd_zmultD: "j * k dvd n ==> k dvd (n::int)"
  apply (rule zdvd_zmultD2)
  apply (subst zmult_commute, assumption)
  done

lemma zdvd_zmult_mono: "i dvd m ==> j dvd (n::int) ==> i * j dvd m * n"
  apply (unfold dvd_def, clarify)
  apply (rule_tac x = "k * ka" in exI)
  apply (simp add: mult_ac)
  done

lemma zdvd_reduce: "(k dvd n + k * m) = (k dvd (n::int))"
  apply (rule iffI)
   apply (erule_tac [2] zdvd_zadd)
   apply (subgoal_tac "n = (n + k * m) - k * m")
    apply (erule ssubst)
    apply (erule zdvd_zdiff, simp_all)
  done

lemma zdvd_zmod: "f dvd m ==> f dvd (n::int) ==> f dvd m mod n"
  apply (unfold dvd_def)
  apply (auto simp add: zmod_zmult_zmult1)
  done

lemma zdvd_zmod_imp_zdvd: "k dvd m mod n ==> k dvd n ==> k dvd (m::int)"
  apply (subgoal_tac "k dvd n * (m div n) + m mod n")
   apply (simp add: zmod_zdiv_equality [symmetric])
  apply (simp only: zdvd_zadd zdvd_zmult2)
  done

lemma zdvd_not_zless: "0 < m ==> m < n ==> \<not> n dvd (m::int)"
  apply (unfold dvd_def, auto)
  apply (subgoal_tac "0 < n")
   prefer 2
   apply (blast intro: order_less_trans)
  apply (simp add: zero_less_mult_iff)
  apply (subgoal_tac "n * k < n * 1")
   apply (drule mult_less_cancel_left [THEN iffD1], auto)
  done

lemma int_dvd_iff: "(int m dvd z) = (m dvd nat (abs z))"
  apply (auto simp add: dvd_def nat_abs_mult_distrib)
  apply (auto simp add: nat_eq_iff abs_if split add: split_if_asm)
   apply (rule_tac x = "-(int k)" in exI)
  apply (auto simp add: zmult_int [symmetric])
  done

lemma dvd_int_iff: "(z dvd int m) = (nat (abs z) dvd m)"
  apply (auto simp add: dvd_def abs_if zmult_int [symmetric])
    apply (rule_tac [3] x = "nat k" in exI)
    apply (rule_tac [2] x = "-(int k)" in exI)
    apply (rule_tac x = "nat (-k)" in exI)
    apply (cut_tac [3] k = m in int_less_0_conv)
    apply (cut_tac k = m in int_less_0_conv)
    apply (auto simp add: zero_le_mult_iff mult_less_0_iff
      nat_mult_distrib [symmetric] nat_eq_iff2)
  done

lemma nat_dvd_iff: "(nat z dvd m) = (if 0 \<le> z then (z dvd int m) else m = 0)"
  apply (auto simp add: dvd_def zmult_int [symmetric])
  apply (rule_tac x = "nat k" in exI)
  apply (cut_tac k = m in int_less_0_conv)
  apply (auto simp add: zero_le_mult_iff mult_less_0_iff
    nat_mult_distrib [symmetric] nat_eq_iff2)
  done

lemma zminus_dvd_iff [iff]: "(-z dvd w) = (z dvd (w::int))"
  apply (auto simp add: dvd_def)
   apply (rule_tac [!] x = "-k" in exI, auto)
  done

lemma dvd_zminus_iff [iff]: "(z dvd -w) = (z dvd (w::int))"
  apply (auto simp add: dvd_def)
   apply (drule minus_equation_iff [THEN iffD1])
   apply (rule_tac [!] x = "-k" in exI, auto)
  done

lemma zdvd_imp_le: "[| z dvd n; 0 < n |] ==> z \<le> (n::int)"
  apply (rule_tac z=n in int_cases)
  apply (auto simp add: dvd_int_iff) 
  apply (rule_tac z=z in int_cases) 
  apply (auto simp add: dvd_imp_le) 
  done


subsection{*Integer Powers*} 

instance int :: power ..

primrec
  "p ^ 0 = 1"
  "p ^ (Suc n) = (p::int) * (p ^ n)"


instance int :: recpower
proof
  fix z :: int
  fix n :: nat
  show "z^0 = 1" by simp
  show "z^(Suc n) = z * (z^n)" by simp
qed


lemma zpower_zmod: "((x::int) mod m)^y mod m = x^y mod m"
apply (induct_tac "y", auto)
apply (rule zmod_zmult1_eq [THEN trans])
apply (simp (no_asm_simp))
apply (rule zmod_zmult_distrib [symmetric])
done

lemma zpower_zadd_distrib: "x^(y+z) = ((x^y)*(x^z)::int)"
  by (rule Power.power_add)

lemma zpower_zpower: "(x^y)^z = (x^(y*z)::int)"
  by (rule Power.power_mult [symmetric])

lemma zero_less_zpower_abs_iff [simp]:
     "(0 < (abs x)^n) = (x \<noteq> (0::int) | n=0)"
apply (induct_tac "n")
apply (auto simp add: zero_less_mult_iff)
done

lemma zero_le_zpower_abs [simp]: "(0::int) <= (abs x)^n"
apply (induct_tac "n")
apply (auto simp add: zero_le_mult_iff)
done

lemma zdiv_int: "int (a div b) = (int a) div (int b)"
apply (subst split_div, auto)
apply (subst split_zdiv, auto)
apply (rule_tac a="int (b * i) + int j" and b="int b" and r="int j" and r'=ja in IntDiv.unique_quotient)
apply (auto simp add: IntDiv.quorem_def int_eq_of_nat)
done

lemma zmod_int: "int (a mod b) = (int a) mod (int b)"
apply (subst split_mod, auto)
apply (subst split_zmod, auto)
apply (rule_tac a="int (b * i) + int j" and b="int b" and q="int i" and q'=ia in IntDiv.unique_remainder)
apply (auto simp add: IntDiv.quorem_def int_eq_of_nat)
done

ML
{*
val quorem_def = thm "quorem_def";

val unique_quotient = thm "unique_quotient";
val unique_remainder = thm "unique_remainder";
val adjust_eq = thm "adjust_eq";
val posDivAlg_eqn = thm "posDivAlg_eqn";
val posDivAlg_correct = thm "posDivAlg_correct";
val negDivAlg_eqn = thm "negDivAlg_eqn";
val negDivAlg_correct = thm "negDivAlg_correct";
val quorem_0 = thm "quorem_0";
val posDivAlg_0 = thm "posDivAlg_0";
val negDivAlg_minus1 = thm "negDivAlg_minus1";
val negateSnd_eq = thm "negateSnd_eq";
val quorem_neg = thm "quorem_neg";
val divAlg_correct = thm "divAlg_correct";
val DIVISION_BY_ZERO = thm "DIVISION_BY_ZERO";
val zmod_zdiv_equality = thm "zmod_zdiv_equality";
val pos_mod_conj = thm "pos_mod_conj";
val pos_mod_sign = thm "pos_mod_sign";
val neg_mod_conj = thm "neg_mod_conj";
val neg_mod_sign = thm "neg_mod_sign";
val quorem_div_mod = thm "quorem_div_mod";
val quorem_div = thm "quorem_div";
val quorem_mod = thm "quorem_mod";
val div_pos_pos_trivial = thm "div_pos_pos_trivial";
val div_neg_neg_trivial = thm "div_neg_neg_trivial";
val div_pos_neg_trivial = thm "div_pos_neg_trivial";
val mod_pos_pos_trivial = thm "mod_pos_pos_trivial";
val mod_neg_neg_trivial = thm "mod_neg_neg_trivial";
val mod_pos_neg_trivial = thm "mod_pos_neg_trivial";
val zdiv_zminus_zminus = thm "zdiv_zminus_zminus";
val zmod_zminus_zminus = thm "zmod_zminus_zminus";
val zdiv_zminus1_eq_if = thm "zdiv_zminus1_eq_if";
val zmod_zminus1_eq_if = thm "zmod_zminus1_eq_if";
val zdiv_zminus2 = thm "zdiv_zminus2";
val zmod_zminus2 = thm "zmod_zminus2";
val zdiv_zminus2_eq_if = thm "zdiv_zminus2_eq_if";
val zmod_zminus2_eq_if = thm "zmod_zminus2_eq_if";
val self_quotient = thm "self_quotient";
val self_remainder = thm "self_remainder";
val zdiv_self = thm "zdiv_self";
val zmod_self = thm "zmod_self";
val zdiv_zero = thm "zdiv_zero";
val div_eq_minus1 = thm "div_eq_minus1";
val zmod_zero = thm "zmod_zero";
val zdiv_minus1 = thm "zdiv_minus1";
val zmod_minus1 = thm "zmod_minus1";
val div_pos_pos = thm "div_pos_pos";
val mod_pos_pos = thm "mod_pos_pos";
val div_neg_pos = thm "div_neg_pos";
val mod_neg_pos = thm "mod_neg_pos";
val div_pos_neg = thm "div_pos_neg";
val mod_pos_neg = thm "mod_pos_neg";
val div_neg_neg = thm "div_neg_neg";
val mod_neg_neg = thm "mod_neg_neg";
val zmod_1 = thm "zmod_1";
val zdiv_1 = thm "zdiv_1";
val zmod_minus1_right = thm "zmod_minus1_right";
val zdiv_minus1_right = thm "zdiv_minus1_right";
val zdiv_mono1 = thm "zdiv_mono1";
val zdiv_mono1_neg = thm "zdiv_mono1_neg";
val zdiv_mono2 = thm "zdiv_mono2";
val zdiv_mono2_neg = thm "zdiv_mono2_neg";
val zdiv_zmult1_eq = thm "zdiv_zmult1_eq";
val zmod_zmult1_eq = thm "zmod_zmult1_eq";
val zmod_zmult1_eq' = thm "zmod_zmult1_eq'";
val zmod_zmult_distrib = thm "zmod_zmult_distrib";
val zdiv_zmult_self1 = thm "zdiv_zmult_self1";
val zdiv_zmult_self2 = thm "zdiv_zmult_self2";
val zmod_zmult_self1 = thm "zmod_zmult_self1";
val zmod_zmult_self2 = thm "zmod_zmult_self2";
val zmod_eq_0_iff = thm "zmod_eq_0_iff";
val zdiv_zadd1_eq = thm "zdiv_zadd1_eq";
val zmod_zadd1_eq = thm "zmod_zadd1_eq";
val mod_div_trivial = thm "mod_div_trivial";
val mod_mod_trivial = thm "mod_mod_trivial";
val zmod_zadd_left_eq = thm "zmod_zadd_left_eq";
val zmod_zadd_right_eq = thm "zmod_zadd_right_eq";
val zdiv_zadd_self1 = thm "zdiv_zadd_self1";
val zdiv_zadd_self2 = thm "zdiv_zadd_self2";
val zmod_zadd_self1 = thm "zmod_zadd_self1";
val zmod_zadd_self2 = thm "zmod_zadd_self2";
val zdiv_zmult2_eq = thm "zdiv_zmult2_eq";
val zmod_zmult2_eq = thm "zmod_zmult2_eq";
val zdiv_zmult_zmult1 = thm "zdiv_zmult_zmult1";
val zdiv_zmult_zmult2 = thm "zdiv_zmult_zmult2";
val zmod_zmult_zmult1 = thm "zmod_zmult_zmult1";
val zmod_zmult_zmult2 = thm "zmod_zmult_zmult2";
val pos_zdiv_mult_2 = thm "pos_zdiv_mult_2";
val neg_zdiv_mult_2 = thm "neg_zdiv_mult_2";
val zdiv_number_of_BIT = thm "zdiv_number_of_BIT";
val pos_zmod_mult_2 = thm "pos_zmod_mult_2";
val neg_zmod_mult_2 = thm "neg_zmod_mult_2";
val zmod_number_of_BIT = thm "zmod_number_of_BIT";
val div_neg_pos_less0 = thm "div_neg_pos_less0";
val div_nonneg_neg_le0 = thm "div_nonneg_neg_le0";
val pos_imp_zdiv_nonneg_iff = thm "pos_imp_zdiv_nonneg_iff";
val neg_imp_zdiv_nonneg_iff = thm "neg_imp_zdiv_nonneg_iff";
val pos_imp_zdiv_neg_iff = thm "pos_imp_zdiv_neg_iff";
val neg_imp_zdiv_neg_iff = thm "neg_imp_zdiv_neg_iff";

val zpower_zmod = thm "zpower_zmod";
val zpower_zadd_distrib = thm "zpower_zadd_distrib";
val zpower_zpower = thm "zpower_zpower";
val zero_less_zpower_abs_iff = thm "zero_less_zpower_abs_iff";
val zero_le_zpower_abs = thm "zero_le_zpower_abs";
*}

end
