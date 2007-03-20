(*  Title:      HOL/Library/Char_ord.thy
    ID:         $Id$
    Author:     Norbert Voelker
*)

header {* Order on characters *}

theory Char_ord
imports Product_ord
begin

text {* Conversions between nibbles and integers in [0..15]. *}

fun
  nibble_to_int:: "nibble \<Rightarrow> int" where
  "nibble_to_int Nibble0 = 0"
  | "nibble_to_int Nibble1 = 1"
  | "nibble_to_int Nibble2 = 2"
  | "nibble_to_int Nibble3 = 3"
  | "nibble_to_int Nibble4 = 4"
  | "nibble_to_int Nibble5 = 5"
  | "nibble_to_int Nibble6 = 6"
  | "nibble_to_int Nibble7 = 7"
  | "nibble_to_int Nibble8 = 8"
  | "nibble_to_int Nibble9 = 9"
  | "nibble_to_int NibbleA = 10"
  | "nibble_to_int NibbleB = 11"
  | "nibble_to_int NibbleC = 12"
  | "nibble_to_int NibbleD = 13"
  | "nibble_to_int NibbleE = 14"
  | "nibble_to_int NibbleF = 15"

definition
  int_to_nibble :: "int \<Rightarrow> nibble" where
  "int_to_nibble x = (let y = x mod 16 in
    if y = 0 then Nibble0 else
    if y = 1 then Nibble1 else
    if y = 2 then Nibble2 else
    if y = 3 then Nibble3 else
    if y = 4 then Nibble4 else
    if y = 5 then Nibble5 else
    if y = 6 then Nibble6 else
    if y = 7 then Nibble7 else
    if y = 8 then Nibble8 else
    if y = 9 then Nibble9 else
    if y = 10 then NibbleA else
    if y = 11 then NibbleB else
    if y = 12 then NibbleC else
    if y = 13 then NibbleD else
    if y = 14 then NibbleE else
    NibbleF)"

lemma int_to_nibble_nibble_to_int: "int_to_nibble (nibble_to_int x) = x"
  by (cases x) (auto simp: int_to_nibble_def Let_def)

lemma inj_nibble_to_int: "inj nibble_to_int"
  by (rule inj_on_inverseI) (rule int_to_nibble_nibble_to_int)

lemmas nibble_to_int_eq = inj_nibble_to_int [THEN inj_eq]

lemma nibble_to_int_ge_0: "0 \<le> nibble_to_int x"
  by (cases x) auto

lemma nibble_to_int_less_16: "nibble_to_int x < 16"
  by (cases x) auto

text {* Conversion between chars and int pairs. *}

fun
  char_to_int_pair :: "char \<Rightarrow> int \<times> int" where
  "char_to_int_pair (Char a b) = (nibble_to_int a, nibble_to_int b)"

lemma inj_char_to_int_pair: "inj char_to_int_pair"
  apply (rule inj_onI)
  apply (case_tac x, case_tac y)
  apply (auto simp: nibble_to_int_eq)
  done

lemmas char_to_int_pair_eq = inj_char_to_int_pair [THEN inj_eq]


text {* Instantiation of order classes *}

instance char :: ord
  char_le_def: "c \<le> d \<equiv> (char_to_int_pair c \<le> char_to_int_pair d)"
  char_less_def: "c < d \<equiv> (char_to_int_pair c < char_to_int_pair d)"  ..

lemmas char_ord_defs = char_less_def char_le_def

instance char :: order
  by default (auto simp: char_ord_defs char_to_int_pair_eq order_less_le)

instance char :: linorder
  by default (auto simp: char_le_def)

instance char :: distrib_lattice
  "inf \<equiv> min"
  "sup \<equiv> max"
  by intro_classes
    (auto simp add: inf_char_def sup_char_def min_max.sup_inf_distrib1)


text {* code generator setup *}

code_const char_to_int_pair
  (SML "raise/ Fail/ \"char'_to'_int'_pair\"")
  (OCaml "failwith \"char'_to'_int'_pair\"")
  (Haskell "error/ \"char'_to'_int'_pair\"")

end
