(*
  Title:     The algebraic hierarchy of rings as axiomatic classes
  Id:        $Id$
  Author:    Clemens Ballarin, started 9 December 1996
  Copyright: Clemens Ballarin
*)

header {* The algebraic hierarchy of rings as axiomatic classes *}

theory Ring2 imports Main
begin

section {* Constants *}

text {* Most constants are already declared by HOL. *}

consts
  assoc         :: "['a::times, 'a] => bool"              (infixl 50)
  irred         :: "'a::{zero, one, times} => bool"
  prime         :: "'a::{zero, one, times} => bool"

section {* Axioms *}

subsection {* Ring axioms *}

axclass ring < zero, one, plus, minus, times, inverse, power

  a_assoc:      "(a + b) + c = a + (b + c)"
  l_zero:       "0 + a = a"
  l_neg:        "(-a) + a = 0"
  a_comm:       "a + b = b + a"

  m_assoc:      "(a * b) * c = a * (b * c)"
  l_one:        "1 * a = a"

  l_distr:      "(a + b) * c = a * c + b * c"

  m_comm:       "a * b = b * a"

  -- {* Definition of derived operations *}

  minus_def:    "a - b = a + (-b)"
  inverse_def:  "inverse a = (if a dvd 1 then THE x. a*x = 1 else 0)"
  divide_def:   "a / b = a * inverse b"
  power_def:    "a ^ n = nat_rec 1 (%u b. b * a) n"

defs
  assoc_def:    "a assoc b == a dvd b & b dvd a"
  irred_def:    "irred a == a ~= 0 & ~ a dvd 1
                          & (ALL d. d dvd a --> d dvd 1 | a dvd d)"
  prime_def:    "prime p == p ~= 0 & ~ p dvd 1
                          & (ALL a b. p dvd (a*b) --> p dvd a | p dvd b)"

subsection {* Integral domains *}

axclass
  "domain" < ring

  one_not_zero: "1 ~= 0"
  integral:     "a * b = 0 ==> a = 0 | b = 0"

subsection {* Factorial domains *}

axclass
  factorial < "domain"

(*
  Proper definition using divisor chain condition currently not supported.
  factorial_divisor:    "wf {(a, b). a dvd b & ~ (b dvd a)}"
*)
  factorial_divisor:	"True"
  factorial_prime:      "irred a ==> prime a"

subsection {* Euclidean domains *}

(*
axclass
  euclidean < "domain"

  euclidean_ax:  "b ~= 0 ==> Ex (% (q, r, e_size::('a::ringS)=>nat).
                   a = b * q + r & e_size r < e_size b)"

  Nothing has been proved about Euclidean domains, yet.
  Design question:
    Fix quo, rem and e_size as constants that are axiomatised with
    euclidean_ax?
    - advantage: more pragmatic and easier to use
    - disadvantage: for every type, one definition of quo and rem will
        be fixed, users may want to use differing ones;
        also, it seems not possible to prove that fields are euclidean
        domains, because that would require generic (type-independent)
        definitions of quo and rem.
*)

subsection {* Fields *}

axclass
  field < ring

  field_one_not_zero:    "1 ~= 0"
                (* Avoid a common superclass as the first thing we will
                   prove about fields is that they are domains. *)
  field_ax:        "a ~= 0 ==> a dvd 1"


section {* Basic facts *}

subsection {* Normaliser for rings *}

(* derived rewrite rules *)

lemma a_lcomm: "(a::'a::ring)+(b+c) = b+(a+c)"
  apply (rule a_comm [THEN trans])
  apply (rule a_assoc [THEN trans])
  apply (rule a_comm [THEN arg_cong])
  done

lemma r_zero: "(a::'a::ring) + 0 = a"
  apply (rule a_comm [THEN trans])
  apply (rule l_zero)
  done

lemma r_neg: "(a::'a::ring) + (-a) = 0"
  apply (rule a_comm [THEN trans])
  apply (rule l_neg)
  done

lemma r_neg2: "(a::'a::ring) + (-a + b) = b"
  apply (rule a_assoc [symmetric, THEN trans])
  apply (simp add: r_neg l_zero)
  done

lemma r_neg1: "-(a::'a::ring) + (a + b) = b"
  apply (rule a_assoc [symmetric, THEN trans])
  apply (simp add: l_neg l_zero)
  done


(* auxiliary *)

lemma a_lcancel: "!! a::'a::ring. a + b = a + c ==> b = c"
  apply (rule box_equals)
  prefer 2
  apply (rule l_zero)
  prefer 2
  apply (rule l_zero)
  apply (rule_tac a1 = a in l_neg [THEN subst])
  apply (simp add: a_assoc)
  done

lemma minus_add: "-((a::'a::ring) + b) = (-a) + (-b)"
  apply (rule_tac a = "a + b" in a_lcancel)
  apply (simp add: r_neg l_neg l_zero a_assoc a_comm a_lcomm)
  done

lemma minus_minus: "-(-(a::'a::ring)) = a"
  apply (rule a_lcancel)
  apply (rule r_neg [THEN trans])
  apply (rule l_neg [symmetric])
  done

lemma minus0: "- 0 = (0::'a::ring)"
  apply (rule a_lcancel)
  apply (rule r_neg [THEN trans])
  apply (rule l_zero [symmetric])
  done


(* derived rules for multiplication *)

lemma m_lcomm: "(a::'a::ring)*(b*c) = b*(a*c)"
  apply (rule m_comm [THEN trans])
  apply (rule m_assoc [THEN trans])
  apply (rule m_comm [THEN arg_cong])
  done

lemma r_one: "(a::'a::ring) * 1 = a"
  apply (rule m_comm [THEN trans])
  apply (rule l_one)
  done

lemma r_distr: "(a::'a::ring) * (b + c) = a * b + a * c"
  apply (rule m_comm [THEN trans])
  apply (rule l_distr [THEN trans])
  apply (simp add: m_comm)
  done


(* the following proof is from Jacobson, Basic Algebra I, pp. 88-89 *)
lemma l_null: "0 * (a::'a::ring) = 0"
  apply (rule a_lcancel)
  apply (rule l_distr [symmetric, THEN trans])
  apply (simp add: r_zero)
  done

lemma r_null: "(a::'a::ring) * 0 = 0"
  apply (rule m_comm [THEN trans])
  apply (rule l_null)
  done

lemma l_minus: "(-(a::'a::ring)) * b = - (a * b)"
  apply (rule a_lcancel)
  apply (rule r_neg [symmetric, THEN [2] trans])
  apply (rule l_distr [symmetric, THEN trans])
  apply (simp add: l_null r_neg)
  done

lemma r_minus: "(a::'a::ring) * (-b) = - (a * b)"
  apply (rule a_lcancel)
  apply (rule r_neg [symmetric, THEN [2] trans])
  apply (rule r_distr [symmetric, THEN trans])
  apply (simp add: r_null r_neg)
  done

(*** Term order for commutative rings ***)

ML {*
fun ring_ord (Const (a, _)) =
    find_index (fn a' => a = a')
      ["HOL.zero", "HOL.plus", "HOL.uminus", "HOL.minus", "HOL.one", "HOL.times"]
  | ring_ord _ = ~1;

fun termless_ring (a, b) = (Term.term_lpo ring_ord (a, b) = LESS);

val ring_ss = HOL_basic_ss settermless termless_ring addsimps
  [thm "a_assoc", thm "l_zero", thm "l_neg", thm "a_comm", thm "m_assoc",
   thm "l_one", thm "l_distr", thm "m_comm", thm "minus_def",
   thm "r_zero", thm "r_neg", thm "r_neg2", thm "r_neg1", thm "minus_add",
   thm "minus_minus", thm "minus0", thm "a_lcomm", thm "m_lcomm", (*thm "r_one",*)
   thm "r_distr", thm "l_null", thm "r_null", thm "l_minus", thm "r_minus"];
*}   (* Note: r_one is not necessary in ring_ss *)

method_setup ring =
  {* Method.no_args (Method.SIMPLE_METHOD' (full_simp_tac ring_ss)) *}
  {* computes distributive normal form in rings *}

lemmas ring_simps =
  l_zero r_zero l_neg r_neg minus_minus minus0
  l_one r_one l_null r_null l_minus r_minus


subsection {* Rings and the summation operator *}

(* Basic facts --- move to HOL!!! *)

(* needed because natsum_cong (below) disables atMost_0 *)
lemma natsum_0 [simp]: "setsum f {..(0::nat)} = (f 0::'a::comm_monoid_add)"
by simp
(*
lemma natsum_Suc [simp]:
  "setsum f {..Suc n} = (f (Suc n) + setsum f {..n}::'a::comm_monoid_add)"
by (simp add: atMost_Suc)
*)
lemma natsum_Suc2:
  "setsum f {..Suc n} = (f 0::'a::comm_monoid_add) + (setsum (%i. f (Suc i)) {..n})"
proof (induct n)
  case 0 show ?case by simp
next
  case Suc thus ?case by (simp add: add_assoc) 
qed

lemma natsum_cong [cong]:
  "!!k. [| j = k; !!i::nat. i <= k ==> f i = (g i::'a::comm_monoid_add) |] ==>
        setsum f {..j} = setsum g {..k}"
by (induct j) auto

lemma natsum_zero [simp]: "setsum (%i. 0) {..n::nat} = (0::'a::comm_monoid_add)"
by (induct n) simp_all

lemma natsum_add [simp]:
  "!!f::nat=>'a::comm_monoid_add.
   setsum (%i. f i + g i) {..n::nat} = setsum f {..n} + setsum g {..n}"
by (induct n) (simp_all add: add_ac)

(* Facts specific to rings *)

instance ring < comm_monoid_add
proof
  fix x y z
  show "(x::'a::ring) + y = y + x" by (rule a_comm)
  show "((x::'a::ring) + y) + z = x + (y + z)" by (rule a_assoc)
  show "0 + (x::'a::ring) = x" by (rule l_zero)
qed

ML {*
  local
    val lhss = 
        ["t + u::'a::ring",
	 "t - u::'a::ring",
	 "t * u::'a::ring",
	 "- t::'a::ring"];
    fun proc ss t = 
      let val rew = Goal.prove (Simplifier.the_context ss) [] []
            (HOLogic.mk_Trueprop
              (HOLogic.mk_eq (t, Var (("x", Term.maxidx_of_term t + 1), fastype_of t))))
                (fn _ => simp_tac (Simplifier.inherit_context ss ring_ss) 1)
            |> mk_meta_eq;
          val (t', u) = Logic.dest_equals (Thm.prop_of rew);
      in if t' aconv u 
        then NONE
        else SOME rew 
    end;
  in
    val ring_simproc = Simplifier.simproc (the_context ()) "ring" lhss (K proc);
  end;
*}

ML_setup {* Addsimprocs [ring_simproc] *}

lemma natsum_ldistr:
  "!!a::'a::ring. setsum f {..n::nat} * a = setsum (%i. f i * a) {..n}"
by (induct n) simp_all

lemma natsum_rdistr:
  "!!a::'a::ring. a * setsum f {..n::nat} = setsum (%i. a * f i) {..n}"
by (induct n) simp_all

subsection {* Integral Domains *}

declare one_not_zero [simp]

lemma zero_not_one [simp]:
  "0 ~= (1::'a::domain)" 
by (rule not_sym) simp

lemma integral_iff: (* not by default a simp rule! *)
  "(a * b = (0::'a::domain)) = (a = 0 | b = 0)"
proof
  assume "a * b = 0" then show "a = 0 | b = 0" by (simp add: integral)
next
  assume "a = 0 | b = 0" then show "a * b = 0" by auto
qed

(*
lemma "(a::'a::ring) - (a - b) = b" apply simp
 simproc seems to fail on this example (fixed with new term order)
*)
(*
lemma bug: "(b::'a::ring) - (b - a) = a" by simp
   simproc for rings cannot prove "(a::'a::ring) - (a - b) = b" 
*)
lemma m_lcancel:
  assumes prem: "(a::'a::domain) ~= 0" shows conc: "(a * b = a * c) = (b = c)"
proof
  assume eq: "a * b = a * c"
  then have "a * (b - c) = 0" by simp
  then have "a = 0 | (b - c) = 0" by (simp only: integral_iff)
  with prem have "b - c = 0" by auto 
  then have "b = b - (b - c)" by simp 
  also have "b - (b - c) = c" by simp
  finally show "b = c" .
next
  assume "b = c" then show "a * b = a * c" by simp
qed

lemma m_rcancel:
  "(a::'a::domain) ~= 0 ==> (b * a = c * a) = (b = c)"
by (simp add: m_lcancel)

lemma power_0 [simp]:
  "(a::'a::ring) ^ 0 = 1" unfolding power_def by simp

lemma power_Suc [simp]:
  "(a::'a::ring) ^ Suc n = a ^ n * a" unfolding power_def by simp

lemma power_one [simp]:
  "1 ^ n = (1::'a::ring)" by (induct n) simp_all

lemma power_zero [simp]:
  "n \<noteq> 0 \<Longrightarrow> 0 ^ n = (0::'a::ring)" by (induct n) simp_all

lemma power_mult [simp]:
  "(a::'a::ring) ^ m * a ^ n = a ^ (m + n)"
  by (induct m) simp_all


section "Divisibility"

lemma dvd_zero_right [simp]:
  "(a::'a::ring) dvd 0"
proof
  show "0 = a * 0" by simp
qed

lemma dvd_zero_left:
  "0 dvd (a::'a::ring) \<Longrightarrow> a = 0" unfolding dvd_def by simp

lemma dvd_refl_ring [simp]:
  "(a::'a::ring) dvd a"
proof
  show "a = a * 1" by simp
qed

lemma dvd_trans_ring:
  fixes a b c :: "'a::ring"
  assumes a_dvd_b: "a dvd b"
  and b_dvd_c: "b dvd c"
  shows "a dvd c"
proof -
  from a_dvd_b obtain l where "b = a * l" using dvd_def by blast
  moreover from b_dvd_c obtain j where "c = b * j" using dvd_def by blast
  ultimately have "c = a * (l * j)" by simp
  then have "\<exists>k. c = a * k" ..
  then show ?thesis using dvd_def by blast
qed


lemma unit_mult: 
  "!!a::'a::ring. [| a dvd 1; b dvd 1 |] ==> a * b dvd 1"
  apply (unfold dvd_def)
  apply clarify
  apply (rule_tac x = "k * ka" in exI)
  apply simp
  done

lemma unit_power: "!!a::'a::ring. a dvd 1 ==> a^n dvd 1"
  apply (induct_tac n)
   apply simp
  apply (simp add: unit_mult)
  done

lemma dvd_add_right [simp]:
  "!! a::'a::ring. [| a dvd b; a dvd c |] ==> a dvd b + c"
  apply (unfold dvd_def)
  apply clarify
  apply (rule_tac x = "k + ka" in exI)
  apply (simp add: r_distr)
  done

lemma dvd_uminus_right [simp]:
  "!! a::'a::ring. a dvd b ==> a dvd -b"
  apply (unfold dvd_def)
  apply clarify
  apply (rule_tac x = "-k" in exI)
  apply (simp add: r_minus)
  done

lemma dvd_l_mult_right [simp]:
  "!! a::'a::ring. a dvd b ==> a dvd c*b"
  apply (unfold dvd_def)
  apply clarify
  apply (rule_tac x = "c * k" in exI)
  apply simp
  done

lemma dvd_r_mult_right [simp]:
  "!! a::'a::ring. a dvd b ==> a dvd b*c"
  apply (unfold dvd_def)
  apply clarify
  apply (rule_tac x = "k * c" in exI)
  apply simp
  done


(* Inverse of multiplication *)

section "inverse"

lemma inverse_unique: "!! a::'a::ring. [| a * x = 1; a * y = 1 |] ==> x = y"
  apply (rule_tac a = "(a*y) * x" and b = "y * (a*x)" in box_equals)
    apply (simp (no_asm))
  apply auto
  done

lemma r_inverse_ring: "!! a::'a::ring. a dvd 1 ==> a * inverse a = 1"
  apply (unfold inverse_def dvd_def)
  apply (tactic {* asm_full_simp_tac (simpset () delsimprocs [ring_simproc]) 1 *})
  apply clarify
  apply (rule theI)
   apply assumption
  apply (rule inverse_unique)
   apply assumption
  apply assumption
  done

lemma l_inverse_ring: "!! a::'a::ring. a dvd 1 ==> inverse a * a = 1"
  by (simp add: r_inverse_ring)


(* Fields *)

section "Fields"

lemma field_unit [simp]: "!! a::'a::field. (a dvd 1) = (a ~= 0)"
  by (auto dest: field_ax dvd_zero_left simp add: field_one_not_zero)

lemma r_inverse [simp]: "!! a::'a::field. a ~= 0 ==> a * inverse a = 1"
  by (simp add: r_inverse_ring)

lemma l_inverse [simp]: "!! a::'a::field. a ~= 0 ==> inverse a * a= 1"
  by (simp add: l_inverse_ring)


(* fields are integral domains *)

lemma field_integral: "!! a::'a::field. a * b = 0 ==> a = 0 | b = 0"
  apply (tactic "Step_tac 1")
  apply (rule_tac a = " (a*b) * inverse b" in box_equals)
    apply (rule_tac [3] refl)
   prefer 2
   apply (simp (no_asm))
   apply auto
  done


(* fields are factorial domains *)

lemma field_fact_prime: "!! a::'a::field. irred a ==> prime a"
  unfolding prime_def irred_def by (blast intro: field_ax)

end
