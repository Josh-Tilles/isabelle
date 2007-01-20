(*  Title:      HOL/ex/Binary.thy
    ID:         $Id$
    Author:     Makarius
*)

header {* Simple and efficient binary numerals *}

theory Binary
imports Main
begin

subsection {* Binary representation of natural numbers *}

definition
  bit :: "nat \<Rightarrow> bool \<Rightarrow> nat" where
  "bit n b = (if b then 2 * n + 1 else 2 * n)"

lemma bit_simps:
    "bit n False = 2 * n"
    "bit n True = 2 * n + 1"
  unfolding bit_def by simp_all


subsection {* Direct operations -- plain normalization *}

lemma binary_norm:
    "bit 0 False = 0"
    "bit 0 True = 1"
  unfolding bit_def by simp_all

lemma binary_add:
    "n + 0 = n"
    "0 + n = n"
    "1 + 1 = bit 1 False"
    "bit n False + 1 = bit n True"
    "bit n True + 1 = bit (n + 1) False"
    "1 + bit n False = bit n True"
    "1 + bit n True = bit (n + 1) False"
    "bit m False + bit n False = bit (m + n) False"
    "bit m False + bit n True = bit (m + n) True"
    "bit m True + bit n False = bit (m + n) True"
    "bit m True + bit n True = bit ((m + n) + 1) False"
  by (simp_all add: bit_simps)

lemma binary_mult:
    "n * 0 = 0"
    "0 * n = 0"
    "n * 1 = n"
    "1 * n = n"
    "bit m True * n = bit (m * n) False + n"
    "bit m False * n = bit (m * n) False"
    "n * bit m True = bit (m * n) False + n"
    "n * bit m False = bit (m * n) False"
  by (simp_all add: bit_simps)

lemmas binary_simps = binary_norm binary_add binary_mult


subsection {* Indirect operations -- ML will produce witnesses *}

lemma binary_less_eq:
  fixes n :: nat
  shows "n \<equiv> m + k \<Longrightarrow> (m \<le> n) \<equiv> True"
    and "m \<equiv> n + k + 1 \<Longrightarrow> (m \<le> n) \<equiv> False"
  by simp_all
  
lemma binary_less:
  fixes n :: nat
  shows "m \<equiv> n + k \<Longrightarrow> (m < n) \<equiv> False"
    and "n \<equiv> m + k + 1 \<Longrightarrow> (m < n) \<equiv> True"
  by simp_all

lemma binary_diff:
  fixes n :: nat
  shows "m \<equiv> n + k \<Longrightarrow> m - n \<equiv> k"
    and "n \<equiv> m + k \<Longrightarrow> m - n \<equiv> 0"
  by simp_all

lemma binary_divmod:
  fixes n :: nat
  assumes "m \<equiv> n * k + l" and "0 < n" and "l < n"
  shows "m div n \<equiv> k"
    and "m mod n \<equiv> l"
proof -
  from `m \<equiv> n * k + l` have "m = l + k * n" by simp
  with `0 < n` and `l < n` show "m div n \<equiv> k" and "m mod n \<equiv> l" by simp_all
qed

ML {*
  fun dest_bit (Const ("False", _)) = 0
    | dest_bit (Const ("True", _)) = 1
    | dest_bit t = raise TERM ("dest_bit", [t]);

  fun dest_binary (Const ("HOL.zero", Type ("nat", _))) = 0
    | dest_binary (Const ("HOL.one", Type ("nat", _))) = 1
    | dest_binary (Const ("Binary.bit", _) $ bs $ b) =
        2 * dest_binary bs + IntInf.fromInt (dest_bit b)
    | dest_binary t = raise TERM ("dest_binary", [t]);

  val bit_const = Const ("Binary.bit", HOLogic.natT --> HOLogic.boolT --> HOLogic.natT);

  fun mk_bit 0 = HOLogic.false_const
    | mk_bit 1 = HOLogic.true_const
    | mk_bit _ = raise TERM ("mk_bit", []);

  fun mk_binary 0 = Const ("HOL.zero", HOLogic.natT)
    | mk_binary 1 = Const ("HOL.one", HOLogic.natT)
    | mk_binary n =
        if n < 0 then raise TERM ("mk_binary", [])
        else
          let val (q, r) = IntInf.divMod (n, 2)
          in bit_const $ mk_binary q $ mk_bit (IntInf.toInt r) end;
*}

ML {*
local
  val binary_ss = HOL_basic_ss addsimps @{thms binary_simps};
  val [binary_less_eq1, binary_less_eq2] = @{thms binary_less_eq};
  val [binary_less1, binary_less2] = @{thms binary_less}
  val [binary_diff1, binary_diff2] = @{thms binary_diff}
  val [binary_div, binary_mod] = @{thms binary_divmod}

  infix ==;
  val op == = Logic.mk_equals;

  fun nat_op c t u = Const (c, HOLogic.natT --> HOLogic.natT --> HOLogic.natT) $ t $ u;
  val plus = nat_op "HOL.plus";
  val mult = nat_op "HOL.times";

  fun prove ctxt prop =  (* FIXME avoid re-certification *)
    Goal.prove ctxt [] [] prop (fn _ => ALLGOALS (full_simp_tac binary_ss));


  exception FAIL;
  fun the_arg t = (t, dest_binary t handle TERM _ => raise FAIL);

  val read =
    let val thy = the_context () in Thm.cterm_of thy o Sign.read_term thy end;
  fun mk_proc name pat proc = Simplifier.mk_simproc' name [read pat]
    (fn ss => fn ct =>
      (case Thm.term_of ct of
        _ $ t $ u =>
          (SOME (proc (Simplifier.the_context ss) (the_arg t) (the_arg u)) handle FAIL => NONE)
      | _ => NONE));


  val less_eq_simproc = mk_proc "binary_nat_less_eq" "?m <= (?n::nat)"
    (fn ctxt => fn (t, m) => fn (u, n) =>
      let val k = n - m in
        if k >= 0 then binary_less_eq1 OF [prove ctxt (u == plus t (mk_binary k))]
        else binary_less_eq2 OF
          [prove ctxt (t == plus (plus u (mk_binary (~ k - 1))) (mk_binary 1))]
      end);

  val less_simproc = mk_proc "binary_nat_less" "?m < (?n::nat)"
    (fn ctxt => fn (t, m) => fn (u, n) =>
      let val k = m - n in
        if k >= 0 then binary_less1 OF [prove ctxt (t == plus u (mk_binary k))]
        else binary_less2 OF [prove ctxt (u == plus (plus t (mk_binary (~ k - 1))) (mk_binary 1))]
      end);

  val diff_simproc = mk_proc "binary_nat_diff" "?m - (?n::nat)"
    (fn ctxt => fn (t, m) => fn (u, n) =>
      let val k = m - n in
        if k >= 0 then binary_diff1 OF [prove ctxt (t == plus u (mk_binary k))]
        else binary_diff2 OF [prove ctxt (u == plus t (mk_binary (~ k)))]
      end);

  fun divmod_proc rule ctxt (t, m) (u, n) =
    if n = 0 then raise FAIL
    else
      let val (k, l) = IntInf.divMod (m, n)
      in rule OF [prove ctxt (t == plus (mult u (mk_binary k)) (mk_binary l))] end;

  val div_simproc = mk_proc "binary_nat_div" "?m div (?n::nat)" (divmod_proc binary_div);
  val mod_simproc = mk_proc "binary_nat_mod" "?m mod (?n::nat)" (divmod_proc binary_mod);

in
  val binary_nat_simprocs =
    [less_eq_simproc, less_simproc, diff_simproc, div_simproc, mod_simproc];
end
*}


subsection {* Concrete syntax *}

syntax
  "_Binary" :: "num_const \<Rightarrow> 'a"    ("$_")

parse_translation {*
let

val syntax_consts = map_aterms (fn Const (c, T) => Const (Syntax.constN ^ c, T) | a => a);

fun binary_tr [t as Const (num, _)] =
      let
        val {leading_zeros = z, value = n, ...} = Syntax.read_xnum num;
        val _ = z = 0 andalso n >= 0 orelse error ("Bad binary number: " ^ num);
      in syntax_consts (mk_binary n) end
  | binary_tr ts = raise TERM ("binary_tr", ts);

in [("_Binary", binary_tr)] end
*}


subsection {* Examples *}

method_setup binary_simp = {*
  Method.no_args (Method.SIMPLE_METHOD'
    (full_simp_tac (HOL_basic_ss addsimps @{thms binary_simps} addsimprocs binary_nat_simprocs)))
*} "binary simplification"


lemma "$6 = 6"
  by (simp add: bit_simps)

lemma "bit (bit (bit 0 False) False) True = 1"
  by (simp add: bit_simps)

lemma "bit (bit (bit 0 False) False) True = bit 0 True"
  by (simp add: bit_simps)

lemma "$5 + $3 = $8"
  by binary_simp

lemma "$5 * $3 = $15"
  by binary_simp

lemma "$5 - $3 = $2"
  by binary_simp

lemma "$3 - $5 = 0"
  by binary_simp

lemma "$123456789 - $123 = $123456666"
  by binary_simp

lemma "$1111111111222222222233333333334444444444 - $998877665544332211 =
  $1111111111222222222232334455668900112233"
  by binary_simp

lemma "(1111111111222222222233333333334444444444::nat) - 998877665544332211 =
  1111111111222222222232334455668900112233"
  by simp

lemma "(1111111111222222222233333333334444444444::int) - 998877665544332211 =
  1111111111222222222232334455668900112233"
  by simp

lemma "$1111111111222222222233333333334444444444 * $998877665544332211 =
    $1109864072938022197293802219729380221972383090160869185684"
  by binary_simp

lemma "$1111111111222222222233333333334444444444 * $998877665544332211 -
      $5555555555666666666677777777778888888888 =
    $1109864072938022191738246664062713555294605312381980296796"
  by binary_simp

lemma "$42 < $4 = False"
  by binary_simp

lemma "$4 < $42 = True"
  by binary_simp

lemma "$42 <= $4 = False"
  by binary_simp

lemma "$4 <= $42 = True"
  by binary_simp

lemma "$1111111111222222222233333333334444444444 < $998877665544332211 = False"
  by binary_simp

lemma "$998877665544332211 < $1111111111222222222233333333334444444444 = True"
  by binary_simp

lemma "$1111111111222222222233333333334444444444 <= $998877665544332211 = False"
  by binary_simp

lemma "$998877665544332211 <= $1111111111222222222233333333334444444444 = True"
  by binary_simp

lemma "$1234 div $23 = $53"
  by binary_simp

lemma "$1234 mod $23 = $15"
  by binary_simp

lemma "$1111111111222222222233333333334444444444 div $998877665544332211 =
    $1112359550673033707875"
  by binary_simp

lemma "(1111111111222222222233333333334444444444::int) div 998877665544332211 =
    1112359550673033707875"
  by simp  -- {* existing numerals: slower by factor 30 *}

lemma "$1111111111222222222233333333334444444444 mod $998877665544332211 =
    $42245174317582819"
  by binary_simp

lemma "(1111111111222222222233333333334444444444::int) mod 998877665544332211 =
    42245174317582819"
  by simp  -- {* existing numerals: slower by factor 30 *}

end
