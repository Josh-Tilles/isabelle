(* Author: Florian Haftmann, TU Muenchen *)

header {* Type of target language numerals *}

theory Code_Numeral
imports Nat_Numeral
begin

text {*
  Code numerals are isomorphic to HOL @{typ nat} but
  mapped to target-language builtin numerals.
*}

subsection {* Datatype of target language numerals *}

typedef (open) code_numeral = "UNIV \<Colon> nat set"
  morphisms nat_of of_nat by rule

lemma of_nat_nat_of [simp]:
  "of_nat (nat_of k) = k"
  by (rule nat_of_inverse)

lemma nat_of_of_nat [simp]:
  "nat_of (of_nat n) = n"
  by (rule of_nat_inverse) (rule UNIV_I)

lemma [measure_function]:
  "is_measure nat_of" by (rule is_measure_trivial)

lemma code_numeral:
  "(\<And>n\<Colon>code_numeral. PROP P n) \<equiv> (\<And>n\<Colon>nat. PROP P (of_nat n))"
proof
  fix n :: nat
  assume "\<And>n\<Colon>code_numeral. PROP P n"
  then show "PROP P (of_nat n)" .
next
  fix n :: code_numeral
  assume "\<And>n\<Colon>nat. PROP P (of_nat n)"
  then have "PROP P (of_nat (nat_of n))" .
  then show "PROP P n" by simp
qed

lemma code_numeral_case:
  assumes "\<And>n. k = of_nat n \<Longrightarrow> P"
  shows P
  by (rule assms [of "nat_of k"]) simp

lemma code_numeral_induct_raw:
  assumes "\<And>n. P (of_nat n)"
  shows "P k"
proof -
  from assms have "P (of_nat (nat_of k))" .
  then show ?thesis by simp
qed

lemma nat_of_inject [simp]:
  "nat_of k = nat_of l \<longleftrightarrow> k = l"
  by (rule nat_of_inject)

lemma of_nat_inject [simp]:
  "of_nat n = of_nat m \<longleftrightarrow> n = m"
  by (rule of_nat_inject) (rule UNIV_I)+

instantiation code_numeral :: zero
begin

definition [simp, code del]:
  "0 = of_nat 0"

instance ..

end

definition [simp]:
  "Suc_code_numeral k = of_nat (Suc (nat_of k))"

rep_datatype "0 \<Colon> code_numeral" Suc_code_numeral
proof -
  fix P :: "code_numeral \<Rightarrow> bool"
  fix k :: code_numeral
  assume "P 0" then have init: "P (of_nat 0)" by simp
  assume "\<And>k. P k \<Longrightarrow> P (Suc_code_numeral k)"
    then have "\<And>n. P (of_nat n) \<Longrightarrow> P (Suc_code_numeral (of_nat n))" .
    then have step: "\<And>n. P (of_nat n) \<Longrightarrow> P (of_nat (Suc n))" by simp
  from init step have "P (of_nat (nat_of k))"
    by (induct "nat_of k") simp_all
  then show "P k" by simp
qed simp_all

declare code_numeral_case [case_names nat, cases type: code_numeral]
declare code_numeral.induct [case_names nat, induct type: code_numeral]

lemma code_numeral_decr [termination_simp]:
  "k \<noteq> of_nat 0 \<Longrightarrow> nat_of k - Suc 0 < nat_of k"
  by (cases k) simp

lemma [simp, code]:
  "code_numeral_size = nat_of"
proof (rule ext)
  fix k
  have "code_numeral_size k = nat_size (nat_of k)"
    by (induct k rule: code_numeral.induct) (simp_all del: zero_code_numeral_def Suc_code_numeral_def, simp_all)
  also have "nat_size (nat_of k) = nat_of k" by (induct "nat_of k") simp_all
  finally show "code_numeral_size k = nat_of k" .
qed

lemma [simp, code]:
  "size = nat_of"
proof (rule ext)
  fix k
  show "size k = nat_of k"
  by (induct k) (simp_all del: zero_code_numeral_def Suc_code_numeral_def, simp_all)
qed

lemmas [code del] = code_numeral.recs code_numeral.cases

lemma [code]:
  "eq_class.eq k l \<longleftrightarrow> eq_class.eq (nat_of k) (nat_of l)"
  by (cases k, cases l) (simp add: eq)

lemma [code nbe]:
  "eq_class.eq (k::code_numeral) k \<longleftrightarrow> True"
  by (rule HOL.eq_refl)


subsection {* Indices as datatype of ints *}

instantiation code_numeral :: number
begin

definition
  "number_of = of_nat o nat"

instance ..

end

lemma nat_of_number [simp]:
  "nat_of (number_of k) = number_of k"
  by (simp add: number_of_code_numeral_def nat_number_of_def number_of_is_id)

code_datatype "number_of \<Colon> int \<Rightarrow> code_numeral"


subsection {* Basic arithmetic *}

instantiation code_numeral :: "{minus, ordered_semidom, semiring_div, linorder}"
begin

definition [simp, code del]:
  "(1\<Colon>code_numeral) = of_nat 1"

definition [simp, code del]:
  "n + m = of_nat (nat_of n + nat_of m)"

definition [simp, code del]:
  "n - m = of_nat (nat_of n - nat_of m)"

definition [simp, code del]:
  "n * m = of_nat (nat_of n * nat_of m)"

definition [simp, code del]:
  "n div m = of_nat (nat_of n div nat_of m)"

definition [simp, code del]:
  "n mod m = of_nat (nat_of n mod nat_of m)"

definition [simp, code del]:
  "n \<le> m \<longleftrightarrow> nat_of n \<le> nat_of m"

definition [simp, code del]:
  "n < m \<longleftrightarrow> nat_of n < nat_of m"

instance proof
qed (auto simp add: code_numeral left_distrib div_mult_self1)

end

lemma zero_code_numeral_code [code inline, code]:
  "(0\<Colon>code_numeral) = Numeral0"
  by (simp add: number_of_code_numeral_def Pls_def)
lemma [code post]: "Numeral0 = (0\<Colon>code_numeral)"
  using zero_code_numeral_code ..

lemma one_code_numeral_code [code inline, code]:
  "(1\<Colon>code_numeral) = Numeral1"
  by (simp add: number_of_code_numeral_def Pls_def Bit1_def)
lemma [code post]: "Numeral1 = (1\<Colon>code_numeral)"
  using one_code_numeral_code ..

lemma plus_code_numeral_code [code nbe]:
  "of_nat n + of_nat m = of_nat (n + m)"
  by simp

definition subtract_code_numeral :: "code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral" where
  [simp, code del]: "subtract_code_numeral = op -"

lemma subtract_code_numeral_code [code nbe]:
  "subtract_code_numeral (of_nat n) (of_nat m) = of_nat (n - m)"
  by simp

lemma minus_code_numeral_code [code]:
  "n - m = subtract_code_numeral n m"
  by simp

lemma times_code_numeral_code [code nbe]:
  "of_nat n * of_nat m = of_nat (n * m)"
  by simp

lemma less_eq_code_numeral_code [code nbe]:
  "of_nat n \<le> of_nat m \<longleftrightarrow> n \<le> m"
  by simp

lemma less_code_numeral_code [code nbe]:
  "of_nat n < of_nat m \<longleftrightarrow> n < m"
  by simp

lemma Suc_code_numeral_minus_one: "Suc_code_numeral n - 1 = n" by simp

lemma of_nat_code [code]:
  "of_nat = Nat.of_nat"
proof
  fix n :: nat
  have "Nat.of_nat n = of_nat n"
    by (induct n) simp_all
  then show "of_nat n = Nat.of_nat n"
    by (rule sym)
qed

lemma code_numeral_not_eq_zero: "i \<noteq> of_nat 0 \<longleftrightarrow> i \<ge> 1"
  by (cases i) auto

definition nat_of_aux :: "code_numeral \<Rightarrow> nat \<Rightarrow> nat" where
  "nat_of_aux i n = nat_of i + n"

lemma nat_of_aux_code [code]:
  "nat_of_aux i n = (if i = 0 then n else nat_of_aux (i - 1) (Suc n))"
  by (auto simp add: nat_of_aux_def code_numeral_not_eq_zero)

lemma nat_of_code [code]:
  "nat_of i = nat_of_aux i 0"
  by (simp add: nat_of_aux_def)

definition div_mod_code_numeral ::  "code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral \<times> code_numeral" where
  [code del]: "div_mod_code_numeral n m = (n div m, n mod m)"

lemma [code]:
  "div_mod_code_numeral n m = (if m = 0 then (0, n) else (n div m, n mod m))"
  unfolding div_mod_code_numeral_def by auto

lemma [code]:
  "n div m = fst (div_mod_code_numeral n m)"
  unfolding div_mod_code_numeral_def by simp

lemma [code]:
  "n mod m = snd (div_mod_code_numeral n m)"
  unfolding div_mod_code_numeral_def by simp

definition int_of :: "code_numeral \<Rightarrow> int" where
  "int_of = Nat.of_nat o nat_of"

lemma int_of_code [code]:
  "int_of k = (if k = 0 then 0
    else (if k mod 2 = 0 then 2 * int_of (k div 2) else 2 * int_of (k div 2) + 1))"
  by (auto simp add: int_of_def mod_div_equality')

hide (open) const of_nat nat_of int_of


subsection {* Code generator setup *}

text {* Implementation of indices by bounded integers *}

code_type code_numeral
  (SML "int")
  (OCaml "int")
  (Haskell "Int")

code_instance code_numeral :: eq
  (Haskell -)

setup {*
  fold (Numeral.add_code @{const_name number_code_numeral_inst.number_of_code_numeral}
    false false) ["SML", "OCaml", "Haskell"]
*}

code_reserved SML Int int
code_reserved OCaml Pervasives int

code_const "op + \<Colon> code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral"
  (SML "Int.+/ ((_),/ (_))")
  (OCaml "Pervasives.( + )")
  (Haskell infixl 6 "+")

code_const "subtract_code_numeral \<Colon> code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral"
  (SML "Int.max/ (_/ -/ _,/ 0 : int)")
  (OCaml "Pervasives.max/ (_/ -/ _)/ (0 : int) ")
  (Haskell "max/ (_/ -/ _)/ (0 :: Int)")

code_const "op * \<Colon> code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral"
  (SML "Int.*/ ((_),/ (_))")
  (OCaml "Pervasives.( * )")
  (Haskell infixl 7 "*")

code_const div_mod_code_numeral
  (SML "(fn n => fn m =>/ if m = 0/ then (0, n) else/ (n div m, n mod m))")
  (OCaml "(fun n -> fun m ->/ if m = 0/ then (0, n) else/ (n '/ m, n mod m))")
  (Haskell "divMod")

code_const "eq_class.eq \<Colon> code_numeral \<Rightarrow> code_numeral \<Rightarrow> bool"
  (SML "!((_ : Int.int) = _)")
  (OCaml "!((_ : int) = _)")
  (Haskell infixl 4 "==")

code_const "op \<le> \<Colon> code_numeral \<Rightarrow> code_numeral \<Rightarrow> bool"
  (SML "Int.<=/ ((_),/ (_))")
  (OCaml "!((_ : int) <= _)")
  (Haskell infix 4 "<=")

code_const "op < \<Colon> code_numeral \<Rightarrow> code_numeral \<Rightarrow> bool"
  (SML "Int.</ ((_),/ (_))")
  (OCaml "!((_ : int) < _)")
  (Haskell infix 4 "<")

end
