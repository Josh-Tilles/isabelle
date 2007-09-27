(*  Title:      HOL/ex/Primrec.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Primitive Recursive Functions.  Demonstrates recursive definitions,
the TFL package.
*)

header {* Primitive Recursive Functions *}

theory Primrec imports Main begin

text {*
  Proof adopted from

  Nora Szasz, A Machine Checked Proof that Ackermann's Function is not
  Primitive Recursive, In: Huet \& Plotkin, eds., Logical Environments
  (CUP, 1993), 317-338.

  See also E. Mendelson, Introduction to Mathematical Logic.  (Van
  Nostrand, 1964), page 250, exercise 11.
  \medskip
*}

consts ack :: "nat * nat => nat"
recdef ack  "less_than <*lex*> less_than"
  "ack (0, n) =  Suc n"
  "ack (Suc m, 0) = ack (m, 1)"
  "ack (Suc m, Suc n) = ack (m, ack (Suc m, n))"

consts list_add :: "nat list => nat"
primrec
  "list_add [] = 0"
  "list_add (m # ms) = m + list_add ms"

consts zeroHd :: "nat list => nat"
primrec
  "zeroHd [] = 0"
  "zeroHd (m # ms) = m"


text {* The set of primitive recursive functions of type @{typ "nat list => nat"}. *}

definition
  SC :: "nat list => nat" where
  "SC l = Suc (zeroHd l)"

definition
  CONSTANT :: "nat => nat list => nat" where
  "CONSTANT k l = k"

definition
  PROJ :: "nat => nat list => nat" where
  "PROJ i l = zeroHd (drop i l)"

definition
  COMP :: "(nat list => nat) => (nat list => nat) list => nat list => nat" where
  "COMP g fs l = g (map (\<lambda>f. f l) fs)"

definition
  PREC :: "(nat list => nat) => (nat list => nat) => nat list => nat" where
  "PREC f g l =
    (case l of
      [] => 0
    | x # l' => nat_rec (f l') (\<lambda>y r. g (r # y # l')) x)"
  -- {* Note that @{term g} is applied first to @{term "PREC f g y"} and then to @{term y}! *}

inductive PRIMREC :: "(nat list => nat) => bool"
  where
    SC: "PRIMREC SC"
  | CONSTANT: "PRIMREC (CONSTANT k)"
  | PROJ: "PRIMREC (PROJ i)"
  | COMP: "PRIMREC g ==> \<forall>f \<in> set fs. PRIMREC f ==> PRIMREC (COMP g fs)"
  | PREC: "PRIMREC f ==> PRIMREC g ==> PRIMREC (PREC f g)"


text {* Useful special cases of evaluation *}

lemma SC [simp]: "SC (x # l) = Suc x"
  apply (simp add: SC_def)
  done

lemma CONSTANT [simp]: "CONSTANT k l = k"
  apply (simp add: CONSTANT_def)
  done

lemma PROJ_0 [simp]: "PROJ 0 (x # l) = x"
  apply (simp add: PROJ_def)
  done

lemma COMP_1 [simp]: "COMP g [f] l = g [f l]"
  apply (simp add: COMP_def)
  done

lemma PREC_0 [simp]: "PREC f g (0 # l) = f l"
  apply (simp add: PREC_def)
  done

lemma PREC_Suc [simp]: "PREC f g (Suc x # l) = g (PREC f g (x # l) # x # l)"
  apply (simp add: PREC_def)
  done


text {* PROPERTY A 4 *}

lemma less_ack2 [iff]: "j < ack (i, j)"
  apply (induct i j rule: ack.induct)
    apply simp_all
  done


text {* PROPERTY A 5-, the single-step lemma *}

lemma ack_less_ack_Suc2 [iff]: "ack(i, j) < ack (i, Suc j)"
  apply (induct i j rule: ack.induct)
    apply simp_all
  done


text {* PROPERTY A 5, monotonicity for @{text "<"} *}

lemma ack_less_mono2: "j < k ==> ack (i, j) < ack (i, k)"
  apply (induct i k rule: ack.induct)
    apply simp_all
  apply (blast elim!: less_SucE intro: less_trans)
  done


text {* PROPERTY A 5', monotonicity for @{text \<le>} *}

lemma ack_le_mono2: "j \<le> k ==> ack (i, j) \<le> ack (i, k)"
  apply (simp add: order_le_less)
  apply (blast intro: ack_less_mono2)
  done


text {* PROPERTY A 6 *}

lemma ack2_le_ack1 [iff]: "ack (i, Suc j) \<le> ack (Suc i, j)"
  apply (induct j)
   apply simp_all
  apply (blast intro: ack_le_mono2 less_ack2 [THEN Suc_leI] le_trans)
  done


text {* PROPERTY A 7-, the single-step lemma *}

lemma ack_less_ack_Suc1 [iff]: "ack (i, j) < ack (Suc i, j)"
  apply (blast intro: ack_less_mono2 less_le_trans)
  done


text {* PROPERTY A 4'? Extra lemma needed for @{term CONSTANT} case, constant functions *}

lemma less_ack1 [iff]: "i < ack (i, j)"
  apply (induct i)
   apply simp_all
  apply (blast intro: Suc_leI le_less_trans)
  done


text {* PROPERTY A 8 *}

lemma ack_1 [simp]: "ack (Suc 0, j) = j + 2"
  apply (induct j)
   apply simp_all
  done


text {* PROPERTY A 9.  The unary @{text 1} and @{text 2} in @{term
  ack} is essential for the rewriting. *}

lemma ack_2 [simp]: "ack (Suc (Suc 0), j) = 2 * j + 3"
  apply (induct j)
   apply simp_all
  done


text {* PROPERTY A 7, monotonicity for @{text "<"} [not clear why
  @{thm [source] ack_1} is now needed first!] *}

lemma ack_less_mono1_aux: "ack (i, k) < ack (Suc (i +i'), k)"
  apply (induct i k rule: ack.induct)
    apply simp_all
   prefer 2
   apply (blast intro: less_trans ack_less_mono2)
  apply (induct_tac i' n rule: ack.induct)
    apply simp_all
  apply (blast intro: Suc_leI [THEN le_less_trans] ack_less_mono2)
  done

lemma ack_less_mono1: "i < j ==> ack (i, k) < ack (j, k)"
  apply (drule less_imp_Suc_add)
  apply (blast intro!: ack_less_mono1_aux)
  done


text {* PROPERTY A 7', monotonicity for @{text "\<le>"} *}

lemma ack_le_mono1: "i \<le> j ==> ack (i, k) \<le> ack (j, k)"
  apply (simp add: order_le_less)
  apply (blast intro: ack_less_mono1)
  done


text {* PROPERTY A 10 *}

lemma ack_nest_bound: "ack(i1, ack (i2, j)) < ack (2 + (i1 + i2), j)"
  apply (simp add: numerals)
  apply (rule ack2_le_ack1 [THEN [2] less_le_trans])
  apply simp
  apply (rule le_add1 [THEN ack_le_mono1, THEN le_less_trans])
  apply (rule ack_less_mono1 [THEN ack_less_mono2])
  apply (simp add: le_imp_less_Suc le_add2)
  done


text {* PROPERTY A 11 *}

lemma ack_add_bound: "ack (i1, j) + ack (i2, j) < ack (4 + (i1 + i2), j)"
  apply (rule less_trans [of _ "ack (Suc (Suc 0), ack (i1 + i2, j))" _])
   prefer 2
   apply (rule ack_nest_bound [THEN less_le_trans])
   apply (simp add: Suc3_eq_add_3)
  apply simp
  apply (cut_tac i = i1 and m1 = i2 and k = j in le_add1 [THEN ack_le_mono1])
  apply (cut_tac i = "i2" and m1 = i1 and k = j in le_add2 [THEN ack_le_mono1])
  apply auto
  done


text {* PROPERTY A 12.  Article uses existential quantifier but the ALF proof
  used @{text "k + 4"}.  Quantified version must be nested @{text
  "\<exists>k'. \<forall>i j. ..."} *}

lemma ack_add_bound2: "i < ack (k, j) ==> i + j < ack (4 + k, j)"
  apply (rule less_trans [of _ "ack (k, j) + ack (0, j)" _])
   apply (blast intro: add_less_mono less_ack2) 
   apply (rule ack_add_bound [THEN less_le_trans])
   apply simp
  done



text {* Inductive definition of the @{term PR} functions *}

text {* MAIN RESULT *}

lemma SC_case: "SC l < ack (1, list_add l)"
  apply (unfold SC_def)
  apply (induct l)
  apply (simp_all add: le_add1 le_imp_less_Suc)
  done

lemma CONSTANT_case: "CONSTANT k l < ack (k, list_add l)"
  by simp

lemma PROJ_case [rule_format]: "\<forall>i. PROJ i l < ack (0, list_add l)"
  apply (simp add: PROJ_def)
  apply (induct l)
   apply (auto simp add: drop_Cons split: nat.split) 
  apply (blast intro: less_le_trans le_add2)
  done


text {* @{term COMP} case *}

lemma COMP_map_aux: "\<forall>f \<in> set fs. PRIMREC f \<and> (\<exists>kf. \<forall>l. f l < ack (kf, list_add l))
  ==> \<exists>k. \<forall>l. list_add (map (\<lambda>f. f l) fs) < ack (k, list_add l)"
  apply (induct fs)
  apply (rule_tac x = 0 in exI) 
   apply simp
  apply simp
  apply (blast intro: add_less_mono ack_add_bound less_trans)
  done

lemma COMP_case:
  "\<forall>l. g l < ack (kg, list_add l) ==>
  \<forall>f \<in> set fs. PRIMREC f \<and> (\<exists>kf. \<forall>l. f l < ack(kf, list_add l))
  ==> \<exists>k. \<forall>l. COMP g fs  l < ack(k, list_add l)"
  apply (unfold COMP_def)
    --{*Now, if meson tolerated map, we could finish with
  @{text "(drule COMP_map_aux, meson ack_less_mono2 ack_nest_bound less_trans)"} *}
  apply (erule COMP_map_aux [THEN exE])
  apply (rule exI)
  apply (rule allI)
  apply (drule spec)+
  apply (erule less_trans)
  apply (blast intro: ack_less_mono2 ack_nest_bound less_trans)
  done


text {* @{term PREC} case *}

lemma PREC_case_aux:
  "\<forall>l. f l + list_add l < ack (kf, list_add l) ==>
    \<forall>l. g l + list_add l < ack (kg, list_add l) ==>
    PREC f g l + list_add l < ack (Suc (kf + kg), list_add l)"
  apply (unfold PREC_def)
  apply (case_tac l)
   apply simp_all
   apply (blast intro: less_trans)
  apply (erule ssubst) -- {* get rid of the needless assumption *}
  apply (induct_tac a)
   apply simp_all
   txt {* base case *}
   apply (blast intro: le_add1 [THEN le_imp_less_Suc, THEN ack_less_mono1] less_trans)
  txt {* induction step *}
  apply (rule Suc_leI [THEN le_less_trans])
   apply (rule le_refl [THEN add_le_mono, THEN le_less_trans])
    prefer 2
    apply (erule spec)
   apply (simp add: le_add2)
  txt {* final part of the simplification *}
  apply simp
  apply (rule le_add2 [THEN ack_le_mono1, THEN le_less_trans])
  apply (erule ack_less_mono2)
  done

lemma PREC_case:
  "\<forall>l. f l < ack (kf, list_add l) ==>
    \<forall>l. g l < ack (kg, list_add l) ==>
    \<exists>k. \<forall>l. PREC f g l < ack (k, list_add l)"
  by (metis le_less_trans [OF le_add1 PREC_case_aux] ack_add_bound2) 

lemma ack_bounds_PRIMREC: "PRIMREC f ==> \<exists>k. \<forall>l. f l < ack (k, list_add l)"
  apply (erule PRIMREC.induct)
      apply (blast intro: SC_case CONSTANT_case PROJ_case COMP_case PREC_case)+
  done

lemma ack_not_PRIMREC: "\<not> PRIMREC (\<lambda>l. case l of [] => 0 | x # l' => ack (x, x))"
  apply (rule notI)
  apply (erule ack_bounds_PRIMREC [THEN exE])
  apply (rule Nat.less_irrefl)
  apply (drule_tac x = "[x]" in spec)
  apply simp
  done

end
