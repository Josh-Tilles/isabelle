(* Author: Lukas Bulwahn, TU Muenchen *)

header {* Counterexample generator performing narrowing-based testing *}

theory Quickcheck_Narrowing
imports Quickcheck_Exhaustive
uses
  ("Tools/Quickcheck/PNF_Narrowing_Engine.hs")
  ("Tools/Quickcheck/Narrowing_Engine.hs")
  ("Tools/Quickcheck/narrowing_generators.ML")
begin

subsection {* Counterexample generator *}

text {* We create a new target for the necessary code generation setup. *}

setup {* Code_Target.extend_target ("Haskell_Quickcheck", (Code_Haskell.target, K I)) *}

subsubsection {* Code generation setup *}

code_type typerep
  (Haskell_Quickcheck "Typerep")

code_const Typerep.Typerep
  (Haskell_Quickcheck "Typerep")

code_reserved Haskell_Quickcheck Typerep

subsubsection {* Type @{text "code_int"} for Haskell Quickcheck's Int type *}

typedef (open) code_int = "UNIV \<Colon> int set"
  morphisms int_of of_int by rule

lemma of_int_int_of [simp]:
  "of_int (int_of k) = k"
  by (rule int_of_inverse)

lemma int_of_of_int [simp]:
  "int_of (of_int n) = n"
  by (rule of_int_inverse) (rule UNIV_I)

lemma code_int:
  "(\<And>n\<Colon>code_int. PROP P n) \<equiv> (\<And>n\<Colon>int. PROP P (of_int n))"
proof
  fix n :: int
  assume "\<And>n\<Colon>code_int. PROP P n"
  then show "PROP P (of_int n)" .
next
  fix n :: code_int
  assume "\<And>n\<Colon>int. PROP P (of_int n)"
  then have "PROP P (of_int (int_of n))" .
  then show "PROP P n" by simp
qed


lemma int_of_inject [simp]:
  "int_of k = int_of l \<longleftrightarrow> k = l"
  by (rule int_of_inject)

lemma of_int_inject [simp]:
  "of_int n = of_int m \<longleftrightarrow> n = m"
  by (rule of_int_inject) (rule UNIV_I)+

instantiation code_int :: equal
begin

definition
  "HOL.equal k l \<longleftrightarrow> HOL.equal (int_of k) (int_of l)"

instance proof
qed (auto simp add: equal_code_int_def equal_int_def eq_int_refl)

end

instantiation code_int :: number
begin

definition
  "number_of = of_int"

instance ..

end

lemma int_of_number [simp]:
  "int_of (number_of k) = number_of k"
  by (simp add: number_of_code_int_def number_of_is_id)


definition nat_of :: "code_int => nat"
where
  "nat_of i = nat (int_of i)"


code_datatype "number_of \<Colon> int \<Rightarrow> code_int"
  
  
instantiation code_int :: "{minus, linordered_semidom, semiring_div, linorder}"
begin

definition [simp, code del]:
  "0 = of_int 0"

definition [simp, code del]:
  "1 = of_int 1"

definition [simp, code del]:
  "n + m = of_int (int_of n + int_of m)"

definition [simp, code del]:
  "n - m = of_int (int_of n - int_of m)"

definition [simp, code del]:
  "n * m = of_int (int_of n * int_of m)"

definition [simp, code del]:
  "n div m = of_int (int_of n div int_of m)"

definition [simp, code del]:
  "n mod m = of_int (int_of n mod int_of m)"

definition [simp, code del]:
  "n \<le> m \<longleftrightarrow> int_of n \<le> int_of m"

definition [simp, code del]:
  "n < m \<longleftrightarrow> int_of n < int_of m"


instance proof
qed (auto simp add: code_int left_distrib zmult_zless_mono2)

end

lemma zero_code_int_code [code, code_unfold]:
  "(0\<Colon>code_int) = Numeral0"
  by (simp add: number_of_code_int_def Pls_def)
lemma [code_post]: "Numeral0 = (0\<Colon>code_int)"
  using zero_code_int_code ..

lemma one_code_int_code [code, code_unfold]:
  "(1\<Colon>code_int) = Numeral1"
  by (simp add: number_of_code_int_def Pls_def Bit1_def)
lemma [code_post]: "Numeral1 = (1\<Colon>code_int)"
  using one_code_int_code ..


definition div_mod_code_int :: "code_int \<Rightarrow> code_int \<Rightarrow> code_int \<times> code_int" where
  [code del]: "div_mod_code_int n m = (n div m, n mod m)"

lemma [code]:
  "div_mod_code_int n m = (if m = 0 then (0, n) else (n div m, n mod m))"
  unfolding div_mod_code_int_def by auto

lemma [code]:
  "n div m = fst (div_mod_code_int n m)"
  unfolding div_mod_code_int_def by simp

lemma [code]:
  "n mod m = snd (div_mod_code_int n m)"
  unfolding div_mod_code_int_def by simp

lemma int_of_code [code]:
  "int_of k = (if k = 0 then 0
    else (if k mod 2 = 0 then 2 * int_of (k div 2) else 2 * int_of (k div 2) + 1))"
proof -
  have 1: "(int_of k div 2) * 2 + int_of k mod 2 = int_of k" 
    by (rule mod_div_equality)
  have "int_of k mod 2 = 0 \<or> int_of k mod 2 = 1" by auto
  from this show ?thesis
    apply auto
    apply (insert 1) by (auto simp add: mult_ac)
qed


code_instance code_numeral :: equal
  (Haskell_Quickcheck -)

setup {* fold (Numeral.add_code @{const_name number_code_int_inst.number_of_code_int}
  false Code_Printer.literal_numeral) ["Haskell_Quickcheck"]  *}

code_const "0 \<Colon> code_int"
  (Haskell_Quickcheck "0")

code_const "1 \<Colon> code_int"
  (Haskell_Quickcheck "1")

code_const "minus \<Colon> code_int \<Rightarrow> code_int \<Rightarrow> code_int"
  (Haskell_Quickcheck "(_/ -/ _)")

code_const div_mod_code_int
  (Haskell_Quickcheck "divMod")

code_const "HOL.equal \<Colon> code_int \<Rightarrow> code_int \<Rightarrow> bool"
  (Haskell_Quickcheck infix 4 "==")

code_const "op \<le> \<Colon> code_int \<Rightarrow> code_int \<Rightarrow> bool"
  (Haskell_Quickcheck infix 4 "<=")

code_const "op < \<Colon> code_int \<Rightarrow> code_int \<Rightarrow> bool"
  (Haskell_Quickcheck infix 4 "<")

code_type code_int
  (Haskell_Quickcheck "Int")

code_abort of_int

subsubsection {* Narrowing's deep representation of types and terms *}

datatype narrowing_type = SumOfProd "narrowing_type list list"
datatype narrowing_term = Var "code_int list" narrowing_type | Ctr code_int "narrowing_term list"
datatype 'a cons = C narrowing_type "(narrowing_term list => 'a) list"

primrec map_cons :: "('a => 'b) => 'a cons => 'b cons"
where
  "map_cons f (C ty cs) = C ty (map (%c. f o c) cs)"

subsubsection {* From narrowing's deep representation of terms to @{theory Code_Evaluation}'s terms *}

class partial_term_of = typerep +
  fixes partial_term_of :: "'a itself => narrowing_term => Code_Evaluation.term"

lemma partial_term_of_anything: "partial_term_of x nt \<equiv> t"
  by (rule eq_reflection) (cases "partial_term_of x nt", cases t, simp)
 
subsubsection {* Auxilary functions for Narrowing *}

consts nth :: "'a list => code_int => 'a"

code_const nth (Haskell_Quickcheck infixl 9  "!!")

consts error :: "char list => 'a"

code_const error (Haskell_Quickcheck "error")

consts toEnum :: "code_int => char"

code_const toEnum (Haskell_Quickcheck "toEnum")

consts marker :: "char"

code_const marker (Haskell_Quickcheck "''\\0'")

subsubsection {* Narrowing's basic operations *}

type_synonym 'a narrowing = "code_int => 'a cons"

definition empty :: "'a narrowing"
where
  "empty d = C (SumOfProd []) []"
  
definition cons :: "'a => 'a narrowing"
where
  "cons a d = (C (SumOfProd [[]]) [(%_. a)])"

fun conv :: "(narrowing_term list => 'a) list => narrowing_term => 'a"
where
  "conv cs (Var p _) = error (marker # map toEnum p)"
| "conv cs (Ctr i xs) = (nth cs i) xs"

fun nonEmpty :: "narrowing_type => bool"
where
  "nonEmpty (SumOfProd ps) = (\<not> (List.null ps))"

definition "apply" :: "('a => 'b) narrowing => 'a narrowing => 'b narrowing"
where
  "apply f a d =
     (case f d of C (SumOfProd ps) cfs =>
       case a (d - 1) of C ta cas =>
       let
         shallow = (d > 0 \<and> nonEmpty ta);
         cs = [(%xs'. (case xs' of [] => undefined | x # xs => cf xs (conv cas x))). shallow, cf <- cfs]
       in C (SumOfProd [ta # p. shallow, p <- ps]) cs)"

definition sum :: "'a narrowing => 'a narrowing => 'a narrowing"
where
  "sum a b d =
    (case a d of C (SumOfProd ssa) ca => 
      case b d of C (SumOfProd ssb) cb =>
      C (SumOfProd (ssa @ ssb)) (ca @ cb))"

lemma [fundef_cong]:
  assumes "a d = a' d" "b d = b' d" "d = d'"
  shows "sum a b d = sum a' b' d'"
using assms unfolding sum_def by (auto split: cons.split narrowing_type.split)

lemma [fundef_cong]:
  assumes "f d = f' d" "(\<And>d'. 0 <= d' & d' < d ==> a d' = a' d')"
  assumes "d = d'"
  shows "apply f a d = apply f' a' d'"
proof -
  note assms moreover
  have "int_of (of_int 0) < int_of d' ==> int_of (of_int 0) <= int_of (of_int (int_of d' - int_of (of_int 1)))"
    by (simp add: of_int_inverse)
  moreover
  have "int_of (of_int (int_of d' - int_of (of_int 1))) < int_of d'"
    by (simp add: of_int_inverse)
  ultimately show ?thesis
    unfolding apply_def by (auto split: cons.split narrowing_type.split simp add: Let_def)
qed

subsubsection {* Narrowing generator type class *}

class narrowing =
  fixes narrowing :: "code_int => 'a cons"

datatype property = Universal narrowing_type "(narrowing_term => property)" "narrowing_term => Code_Evaluation.term" | Existential narrowing_type "(narrowing_term => property)" "narrowing_term => Code_Evaluation.term" | Property bool

(* FIXME: hard-wired maximal depth of 100 here *)
definition exists :: "('a :: {narrowing, partial_term_of} => property) => property"
where
  "exists f = (case narrowing (100 :: code_int) of C ty cs => Existential ty (\<lambda> t. f (conv cs t)) (partial_term_of (TYPE('a))))"

definition "all" :: "('a :: {narrowing, partial_term_of} => property) => property"
where
  "all f = (case narrowing (100 :: code_int) of C ty cs => Universal ty (\<lambda>t. f (conv cs t)) (partial_term_of (TYPE('a))))"

subsubsection {* class @{text is_testable} *}

text {* The class @{text is_testable} ensures that all necessary type instances are generated. *}

class is_testable

instance bool :: is_testable ..

instance "fun" :: ("{term_of, narrowing, partial_term_of}", is_testable) is_testable ..

definition ensure_testable :: "'a :: is_testable => 'a :: is_testable"
where
  "ensure_testable f = f"


subsubsection {* Defining a simple datatype to represent functions in an incomplete and redundant way *}

datatype ('a, 'b) ffun = Constant 'b | Update 'a 'b "('a, 'b) ffun"

primrec eval_ffun :: "('a, 'b) ffun => 'a => 'b"
where
  "eval_ffun (Constant c) x = c"
| "eval_ffun (Update x' y f) x = (if x = x' then y else eval_ffun f x)"

hide_type (open) ffun
hide_const (open) Constant Update eval_ffun

datatype 'b cfun = Constant 'b

primrec eval_cfun :: "'b cfun => 'a => 'b"
where
  "eval_cfun (Constant c) y = c"

hide_type (open) cfun
hide_const (open) Constant eval_cfun

subsubsection {* Setting up the counterexample generator *}

use "Tools/Quickcheck/narrowing_generators.ML"

setup {* Narrowing_Generators.setup *}

subsection {* Narrowing for integers *}


definition drawn_from :: "'a list => 'a cons"
where "drawn_from xs = C (SumOfProd (map (%_. []) xs)) (map (%x y. x) xs)"

function around_zero :: "int => int list"
where
  "around_zero i = (if i < 0 then [] else (if i = 0 then [0] else around_zero (i - 1) @ [i, -i]))"
by pat_completeness auto
termination by (relation "measure nat") auto

declare around_zero.simps[simp del]

lemma length_around_zero:
  assumes "i >= 0" 
  shows "length (around_zero i) = 2 * nat i + 1"
proof (induct rule: int_ge_induct[OF assms])
  case 1
  from 1 show ?case by (simp add: around_zero.simps)
next
  case (2 i)
  from 2 show ?case
    by (simp add: around_zero.simps[of "i + 1"])
qed

instantiation int :: narrowing
begin

definition
  "narrowing_int d = (let (u :: _ => _ => unit) = conv; i = Quickcheck_Narrowing.int_of d in drawn_from (around_zero i))"

instance ..

end

lemma [code, code del]: "partial_term_of (ty :: int itself) t == undefined"
by (rule partial_term_of_anything)+

lemma [code]:
  "partial_term_of (ty :: int itself) (Var p t) == Code_Evaluation.Free (STR ''_'') (Typerep.Typerep (STR ''Int.int'') [])"
  "partial_term_of (ty :: int itself) (Ctr i []) == (if i mod 2 = 0 then
     Code_Evaluation.term_of (- (int_of i) div 2) else Code_Evaluation.term_of ((int_of i + 1) div 2))"
by (rule partial_term_of_anything)+

text {* Defining integers by positive and negative copy of naturals *}
(*
datatype simple_int = Positive nat | Negative nat

primrec int_of_simple_int :: "simple_int => int"
where
  "int_of_simple_int (Positive n) = int n"
| "int_of_simple_int (Negative n) = (-1 - int n)"

instantiation int :: narrowing
begin

definition narrowing_int :: "code_int => int cons"
where
  "narrowing_int d = map_cons int_of_simple_int ((narrowing :: simple_int narrowing) d)"

instance ..

end

text {* printing the partial terms *}

lemma [code]:
  "partial_term_of (ty :: int itself) t == Code_Evaluation.App (Code_Evaluation.Const (STR ''Quickcheck_Narrowing.int_of_simple_int'')
     (Typerep.Typerep (STR ''fun'') [Typerep.Typerep (STR ''Quickcheck_Narrowing.simple_int'') [], Typerep.Typerep (STR ''Int.int'') []])) (partial_term_of (TYPE(simple_int)) t)"
by (rule partial_term_of_anything)

*)

hide_type code_int narrowing_type narrowing_term cons property
hide_const int_of of_int nth error toEnum marker empty
  C cons conv nonEmpty "apply" sum ensure_testable all exists 
hide_const (open) Var Ctr
hide_fact empty_def cons_def conv.simps nonEmpty.simps apply_def sum_def ensure_testable_def all_def exists_def


end