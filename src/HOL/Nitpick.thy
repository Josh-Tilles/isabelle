(*  Title:      HOL/Nitpick.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009

Nitpick: Yet another counterexample generator for Isabelle/HOL.
*)

header {* Nitpick: Yet Another Counterexample Generator for Isabelle/HOL *}

theory Nitpick
imports Map SAT
uses ("Tools/Nitpick/kodkod.ML")
     ("Tools/Nitpick/kodkod_sat.ML")
     ("Tools/Nitpick/nitpick_util.ML")
     ("Tools/Nitpick/nitpick_hol.ML")
     ("Tools/Nitpick/nitpick_mono.ML")
     ("Tools/Nitpick/nitpick_scope.ML")
     ("Tools/Nitpick/nitpick_peephole.ML")
     ("Tools/Nitpick/nitpick_rep.ML")
     ("Tools/Nitpick/nitpick_nut.ML")
     ("Tools/Nitpick/nitpick_kodkod.ML")
     ("Tools/Nitpick/nitpick_model.ML")
     ("Tools/Nitpick/nitpick.ML")
     ("Tools/Nitpick/nitpick_isar.ML")
     ("Tools/Nitpick/nitpick_tests.ML")
     ("Tools/Nitpick/minipick.ML")
begin

typedecl bisim_iterator

axiomatization unknown :: 'a
           and undefined_fast_The :: 'a
           and undefined_fast_Eps :: 'a
           and bisim :: "bisim_iterator \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
           and bisim_iterator_max :: bisim_iterator
           and Tha :: "('a \<Rightarrow> bool) \<Rightarrow> 'a"

datatype ('a, 'b) pair_box = PairBox 'a 'b
datatype ('a, 'b) fun_box = FunBox "'a \<Rightarrow> 'b"

text {*
Alternative definitions.
*}

lemma If_def [nitpick_def]:
"(if P then Q else R) \<equiv> (P \<longrightarrow> Q) \<and> (\<not> P \<longrightarrow> R)"
by (rule eq_reflection) (rule if_bool_eq_conj)

lemma Ex1_def [nitpick_def]:
"Ex1 P \<equiv> \<exists>x. P = {x}"
apply (rule eq_reflection)
apply (simp add: Ex1_def expand_set_eq)
apply (rule iffI)
 apply (erule exE)
 apply (erule conjE)
 apply (rule_tac x = x in exI)
 apply (rule allI)
 apply (rename_tac y)
 apply (erule_tac x = y in allE)
by (auto simp: mem_def)

lemma rtrancl_def [nitpick_def]: "r\<^sup>* \<equiv> (r\<^sup>+)\<^sup>="
by simp

lemma rtranclp_def [nitpick_def]:
"rtranclp r a b \<equiv> (a = b \<or> tranclp r a b)"
by (rule eq_reflection) (auto dest: rtranclpD)

lemma tranclp_def [nitpick_def]:
"tranclp r a b \<equiv> trancl (split r) (a, b)"
by (simp add: trancl_def Collect_def mem_def)

definition refl' :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"refl' r \<equiv> \<forall>x. (x, x) \<in> r"

definition wf' :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"wf' r \<equiv> acyclic r \<and> (finite r \<or> unknown)"

axiomatization wf_wfrec :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"

definition wf_wfrec' :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
[nitpick_simp]: "wf_wfrec' R F x = F (Recdef.cut (wf_wfrec R F) R x) x"

definition wfrec' ::  "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
"wfrec' R F x \<equiv> if wf R then wf_wfrec' R F x
                else THE y. wfrec_rel R (%f x. F (Recdef.cut f R x) x) x y"

definition card' :: "('a \<Rightarrow> bool) \<Rightarrow> nat" where
"card' X \<equiv> length (SOME xs. set xs = X \<and> distinct xs)"

definition setsum' :: "('a \<Rightarrow> 'b\<Colon>comm_monoid_add) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b" where
"setsum' f A \<equiv> if finite A then listsum (map f (SOME xs. set xs = A \<and> distinct xs)) else 0"

inductive fold_graph' :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> bool" where
"fold_graph' f z {} z" |
"\<lbrakk>x \<in> A; fold_graph' f z (A - {x}) y\<rbrakk> \<Longrightarrow> fold_graph' f z A (f x y)"

text {*
The following lemmas are not strictly necessary but they help the
\textit{special\_level} optimization.
*}

lemma The_psimp [nitpick_psimp]:
"P = {x} \<Longrightarrow> The P = x"
by (subgoal_tac "{x} = (\<lambda>y. y = x)") (auto simp: mem_def)

lemma Eps_psimp [nitpick_psimp]:
"\<lbrakk>P x; \<not> P y; Eps P = y\<rbrakk> \<Longrightarrow> Eps P = x"
apply (case_tac "P (Eps P)")
 apply auto
apply (erule contrapos_np)
by (rule someI)

lemma unit_case_def [nitpick_def]:
"unit_case x u \<equiv> x"
apply (subgoal_tac "u = ()")
 apply (simp only: unit.cases)
by simp

lemma nat_case_def [nitpick_def]:
"nat_case x f n \<equiv> if n = 0 then x else f (n - 1)"
apply (rule eq_reflection)
by (case_tac n) auto

lemmas dvd_def = dvd_eq_mod_eq_0 [THEN eq_reflection, nitpick_def]

lemma list_size_simp [nitpick_simp]:
"list_size f xs = (if xs = [] then 0
                   else Suc (f (hd xs) + list_size f (tl xs)))"
"size xs = (if xs = [] then 0 else Suc (size (tl xs)))"
by (case_tac xs) auto

text {*
Auxiliary definitions used to provide an alternative representation for
@{text rat} and @{text real}.
*}

function nat_gcd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
[simp del]: "nat_gcd x y = (if y = 0 then x else nat_gcd y (x mod y))"
by auto
termination
apply (relation "measure (\<lambda>(x, y). x + y + (if y > x then 1 else 0))")
 apply auto
 apply (metis mod_less_divisor xt1(9))
by (metis mod_mod_trivial mod_self nat_neq_iff xt1(10))

definition nat_lcm :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"nat_lcm x y = x * y div (nat_gcd x y)"

definition int_gcd :: "int \<Rightarrow> int \<Rightarrow> int" where
"int_gcd x y = int (nat_gcd (nat (abs x)) (nat (abs y)))"

definition int_lcm :: "int \<Rightarrow> int \<Rightarrow> int" where
"int_lcm x y = int (nat_lcm (nat (abs x)) (nat (abs y)))"

definition Frac :: "int \<times> int \<Rightarrow> bool" where
"Frac \<equiv> \<lambda>(a, b). b > 0 \<and> int_gcd a b = 1"

axiomatization Abs_Frac :: "int \<times> int \<Rightarrow> 'a"
           and Rep_Frac :: "'a \<Rightarrow> int \<times> int"

definition zero_frac :: 'a where
"zero_frac \<equiv> Abs_Frac (0, 1)"

definition one_frac :: 'a where
"one_frac \<equiv> Abs_Frac (1, 1)"

definition num :: "'a \<Rightarrow> int" where
"num \<equiv> fst o Rep_Frac"

definition denom :: "'a \<Rightarrow> int" where
"denom \<equiv> snd o Rep_Frac"

function norm_frac :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" where
[simp del]: "norm_frac a b = (if b < 0 then norm_frac (- a) (- b)
                              else if a = 0 \<or> b = 0 then (0, 1)
                              else let c = int_gcd a b in (a div c, b div c))"
by pat_completeness auto
termination by (relation "measure (\<lambda>(_, b). if b < 0 then 1 else 0)") auto

definition frac :: "int \<Rightarrow> int \<Rightarrow> 'a" where
"frac a b \<equiv> Abs_Frac (norm_frac a b)"

definition plus_frac :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
[nitpick_simp]:
"plus_frac q r = (let d = int_lcm (denom q) (denom r) in
                    frac (num q * (d div denom q) + num r * (d div denom r)) d)"

definition times_frac :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
[nitpick_simp]:
"times_frac q r = frac (num q * num r) (denom q * denom r)"

definition uminus_frac :: "'a \<Rightarrow> 'a" where
"uminus_frac q \<equiv> Abs_Frac (- num q, denom q)"

definition number_of_frac :: "int \<Rightarrow> 'a" where
"number_of_frac n \<equiv> Abs_Frac (n, 1)"

definition inverse_frac :: "'a \<Rightarrow> 'a" where
"inverse_frac q \<equiv> frac (denom q) (num q)"

definition less_eq_frac :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
[nitpick_simp]:
"less_eq_frac q r \<longleftrightarrow> num (plus_frac q (uminus_frac r)) \<le> 0"

definition of_frac :: "'a \<Rightarrow> 'b\<Colon>{inverse,ring_1}" where
"of_frac q \<equiv> of_int (num q) / of_int (denom q)"

use "Tools/Nitpick/kodkod.ML"
use "Tools/Nitpick/kodkod_sat.ML"
use "Tools/Nitpick/nitpick_util.ML"
use "Tools/Nitpick/nitpick_hol.ML"
use "Tools/Nitpick/nitpick_mono.ML"
use "Tools/Nitpick/nitpick_scope.ML"
use "Tools/Nitpick/nitpick_peephole.ML"
use "Tools/Nitpick/nitpick_rep.ML"
use "Tools/Nitpick/nitpick_nut.ML"
use "Tools/Nitpick/nitpick_kodkod.ML"
use "Tools/Nitpick/nitpick_model.ML"
use "Tools/Nitpick/nitpick.ML"
use "Tools/Nitpick/nitpick_isar.ML"
use "Tools/Nitpick/nitpick_tests.ML"
use "Tools/Nitpick/minipick.ML"

hide (open) const unknown undefined_fast_The undefined_fast_Eps bisim 
    bisim_iterator_max Tha refl' wf' wf_wfrec wf_wfrec' wfrec' card' setsum'
    fold_graph' nat_gcd nat_lcm int_gcd int_lcm Frac Abs_Frac Rep_Frac zero_frac
    one_frac num denom norm_frac frac plus_frac times_frac uminus_frac
    number_of_frac inverse_frac less_eq_frac of_frac
hide (open) type bisim_iterator pair_box fun_box
hide (open) fact If_def Ex1_def rtrancl_def rtranclp_def tranclp_def refl'_def
    wf'_def wf_wfrec'_def wfrec'_def card'_def setsum'_def fold_graph'_def
    The_psimp Eps_psimp unit_case_def nat_case_def dvd_def list_size_simp
    nat_gcd_def nat_lcm_def int_gcd_def int_lcm_def Frac_def zero_frac_def
    one_frac_def num_def denom_def norm_frac_def frac_def plus_frac_def
    times_frac_def uminus_frac_def number_of_frac_def inverse_frac_def
    less_eq_frac_def of_frac_def

end
