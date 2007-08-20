(* 
  ID:     $Id$
  Author: Jeremy Dawson and Gerwin Klein, NICTA

  definition and basic theorems for bit-wise logical operations 
  for integers expressed using Pls, Min, BIT,
  and converting them to and from lists of bools
*) 

header {* Bitwise Operations on Binary Integers *}

theory BinOperations imports BinGeneral BitSyntax

begin

subsection {* Logical operations *}

text "bit-wise logical operations on the int type"

instance int :: bit
  int_not_def: "bitNOT \<equiv> bin_rec Numeral.Min Numeral.Pls 
    (\<lambda>w b s. s BIT (NOT b))"
  int_and_def: "bitAND \<equiv> bin_rec (\<lambda>x. Numeral.Pls) (\<lambda>y. y) 
    (\<lambda>w b s y. s (bin_rest y) BIT (b AND bin_last y))"
  int_or_def: "bitOR \<equiv> bin_rec (\<lambda>x. x) (\<lambda>y. Numeral.Min) 
    (\<lambda>w b s y. s (bin_rest y) BIT (b OR bin_last y))"
  int_xor_def: "bitXOR \<equiv> bin_rec (\<lambda>x. x) bitNOT 
    (\<lambda>w b s y. s (bin_rest y) BIT (b XOR bin_last y))"
  ..

lemma int_not_simps [simp]:
  "NOT Numeral.Pls = Numeral.Min"
  "NOT Numeral.Min = Numeral.Pls"
  "NOT (w BIT b) = (NOT w) BIT (NOT b)"
  by (unfold int_not_def) (auto intro: bin_rec_simps)

lemma bit_extra_simps [simp]: 
  "x AND bit.B0 = bit.B0"
  "x AND bit.B1 = x"
  "x OR bit.B1 = bit.B1"
  "x OR bit.B0 = x"
  "x XOR bit.B1 = NOT x"
  "x XOR bit.B0 = x"
  by (cases x, auto)+

lemma bit_ops_comm: 
  "(x::bit) AND y = y AND x"
  "(x::bit) OR y = y OR x"
  "(x::bit) XOR y = y XOR x"
  by (cases y, auto)+

lemma bit_ops_same [simp]: 
  "(x::bit) AND x = x"
  "(x::bit) OR x = x"
  "(x::bit) XOR x = bit.B0"
  by (cases x, auto)+

lemma bit_not_not [simp]: "NOT (NOT (x::bit)) = x"
  by (cases x) auto

lemma int_xor_Pls [simp]: 
  "Numeral.Pls XOR x = x"
  unfolding int_xor_def by (simp add: bin_rec_PM)

lemma int_xor_Min [simp]: 
  "Numeral.Min XOR x = NOT x"
  unfolding int_xor_def by (simp add: bin_rec_PM)

lemma int_xor_Bits [simp]: 
  "(x BIT b) XOR (y BIT c) = (x XOR y) BIT (b XOR c)"
  apply (unfold int_xor_def)
  apply (rule bin_rec_simps (1) [THEN fun_cong, THEN trans])
    apply (rule ext, simp)
   prefer 2
   apply simp
  apply (rule ext)
  apply (simp add: int_not_simps [symmetric])
  done

lemma int_xor_x_simps':
  "w XOR (Numeral.Pls BIT bit.B0) = w"
  "w XOR (Numeral.Min BIT bit.B1) = NOT w"
  apply (induct w rule: bin_induct)
       apply simp_all[4]
   apply (unfold int_xor_Bits)
   apply clarsimp+
  done

lemmas int_xor_extra_simps [simp] = int_xor_x_simps' [simplified arith_simps]

lemma int_or_Pls [simp]: 
  "Numeral.Pls OR x = x"
  by (unfold int_or_def) (simp add: bin_rec_PM)
  
lemma int_or_Min [simp]:
  "Numeral.Min OR x = Numeral.Min"
  by (unfold int_or_def) (simp add: bin_rec_PM)

lemma int_or_Bits [simp]: 
  "(x BIT b) OR (y BIT c) = (x OR y) BIT (b OR c)"
  unfolding int_or_def by (simp add: bin_rec_simps)

lemma int_or_x_simps': 
  "w OR (Numeral.Pls BIT bit.B0) = w"
  "w OR (Numeral.Min BIT bit.B1) = Numeral.Min"
  apply (induct w rule: bin_induct)
       apply simp_all[4]
   apply (unfold int_or_Bits)
   apply clarsimp+
  done

lemmas int_or_extra_simps [simp] = int_or_x_simps' [simplified arith_simps]


lemma int_and_Pls [simp]:
  "Numeral.Pls AND x = Numeral.Pls"
  unfolding int_and_def by (simp add: bin_rec_PM)

lemma int_and_Min [simp]:
  "Numeral.Min AND x = x"
  unfolding int_and_def by (simp add: bin_rec_PM)

lemma int_and_Bits [simp]: 
  "(x BIT b) AND (y BIT c) = (x AND y) BIT (b AND c)" 
  unfolding int_and_def by (simp add: bin_rec_simps)

lemma int_and_x_simps': 
  "w AND (Numeral.Pls BIT bit.B0) = Numeral.Pls"
  "w AND (Numeral.Min BIT bit.B1) = w"
  apply (induct w rule: bin_induct)
       apply simp_all[4]
   apply (unfold int_and_Bits)
   apply clarsimp+
  done

lemmas int_and_extra_simps [simp] = int_and_x_simps' [simplified arith_simps]

(* commutativity of the above *)
lemma bin_ops_comm:
  shows
  int_and_comm: "!!y::int. x AND y = y AND x" and
  int_or_comm:  "!!y::int. x OR y = y OR x" and
  int_xor_comm: "!!y::int. x XOR y = y XOR x"
  apply (induct x rule: bin_induct)
          apply simp_all[6]
    apply (case_tac y rule: bin_exhaust, simp add: bit_ops_comm)+
  done

lemma bin_ops_same [simp]:
  "(x::int) AND x = x" 
  "(x::int) OR x = x" 
  "(x::int) XOR x = Numeral.Pls"
  by (induct x rule: bin_induct) auto

lemma int_not_not [simp]: "NOT (NOT (x::int)) = x"
  by (induct x rule: bin_induct) auto

lemmas bin_log_esimps = 
  int_and_extra_simps  int_or_extra_simps  int_xor_extra_simps
  int_and_Pls int_and_Min  int_or_Pls int_or_Min  int_xor_Pls int_xor_Min

(* basic properties of logical (bit-wise) operations *)

lemma bbw_ao_absorb: 
  "!!y::int. x AND (y OR x) = x & x OR (y AND x) = x"
  apply (induct x rule: bin_induct)
    apply auto 
   apply (case_tac [!] y rule: bin_exhaust)
   apply auto
   apply (case_tac [!] bit)
     apply auto
  done

lemma bbw_ao_absorbs_other:
  "x AND (x OR y) = x \<and> (y AND x) OR x = (x::int)"
  "(y OR x) AND x = x \<and> x OR (x AND y) = (x::int)"
  "(x OR y) AND x = x \<and> (x AND y) OR x = (x::int)"
  apply (auto simp: bbw_ao_absorb int_or_comm)  
      apply (subst int_or_comm)
    apply (simp add: bbw_ao_absorb)
   apply (subst int_and_comm)
   apply (subst int_or_comm)
   apply (simp add: bbw_ao_absorb)
  apply (subst int_and_comm)
  apply (simp add: bbw_ao_absorb)
  done

lemmas bbw_ao_absorbs [simp] = bbw_ao_absorb bbw_ao_absorbs_other

lemma int_xor_not:
  "!!y::int. (NOT x) XOR y = NOT (x XOR y) & 
        x XOR (NOT y) = NOT (x XOR y)"
  apply (induct x rule: bin_induct)
    apply auto
   apply (case_tac y rule: bin_exhaust, auto, 
          case_tac b, auto)+
  done

lemma bbw_assocs': 
  "!!y z::int. (x AND y) AND z = x AND (y AND z) & 
          (x OR y) OR z = x OR (y OR z) & 
          (x XOR y) XOR z = x XOR (y XOR z)"
  apply (induct x rule: bin_induct)
    apply (auto simp: int_xor_not)
    apply (case_tac [!] y rule: bin_exhaust)
    apply (case_tac [!] z rule: bin_exhaust)
    apply (case_tac [!] bit)
       apply (case_tac [!] b)
             apply auto
  done

lemma int_and_assoc:
  "(x AND y) AND (z::int) = x AND (y AND z)"
  by (simp add: bbw_assocs')

lemma int_or_assoc:
  "(x OR y) OR (z::int) = x OR (y OR z)"
  by (simp add: bbw_assocs')

lemma int_xor_assoc:
  "(x XOR y) XOR (z::int) = x XOR (y XOR z)"
  by (simp add: bbw_assocs')

lemmas bbw_assocs = int_and_assoc int_or_assoc int_xor_assoc

lemma bbw_lcs [simp]: 
  "(y::int) AND (x AND z) = x AND (y AND z)"
  "(y::int) OR (x OR z) = x OR (y OR z)"
  "(y::int) XOR (x XOR z) = x XOR (y XOR z)" 
  apply (auto simp: bbw_assocs [symmetric])
  apply (auto simp: bin_ops_comm)
  done

lemma bbw_not_dist: 
  "!!y::int. NOT (x OR y) = (NOT x) AND (NOT y)" 
  "!!y::int. NOT (x AND y) = (NOT x) OR (NOT y)"
  apply (induct x rule: bin_induct)
       apply auto
   apply (case_tac [!] y rule: bin_exhaust)
   apply (case_tac [!] bit, auto)
  done

lemma bbw_oa_dist: 
  "!!y z::int. (x AND y) OR z = 
          (x OR z) AND (y OR z)"
  apply (induct x rule: bin_induct)
    apply auto
  apply (case_tac y rule: bin_exhaust)
  apply (case_tac z rule: bin_exhaust)
  apply (case_tac ba, auto)
  done

lemma bbw_ao_dist: 
  "!!y z::int. (x OR y) AND z = 
          (x AND z) OR (y AND z)"
   apply (induct x rule: bin_induct)
    apply auto
  apply (case_tac y rule: bin_exhaust)
  apply (case_tac z rule: bin_exhaust)
  apply (case_tac ba, auto)
  done

declare bin_ops_comm [simp] bbw_assocs [simp] 

lemma plus_and_or [rule_format]:
  "ALL y::int. (x AND y) + (x OR y) = x + y"
  apply (induct x rule: bin_induct)
    apply clarsimp
   apply clarsimp
  apply clarsimp
  apply (case_tac y rule: bin_exhaust)
  apply clarsimp
  apply (unfold Bit_def)
  apply clarsimp
  apply (erule_tac x = "x" in allE)
  apply (simp split: bit.split)
  done

lemma le_int_or:
  "!!x.  bin_sign y = Numeral.Pls ==> x <= x OR y"
  apply (induct y rule: bin_induct)
    apply clarsimp
   apply clarsimp
  apply (case_tac x rule: bin_exhaust)
  apply (case_tac b)
   apply (case_tac [!] bit)
     apply (auto simp: less_eq_numeral_code)
  done

lemmas int_and_le =
  xtr3 [OF bbw_ao_absorbs (2) [THEN conjunct2, symmetric] le_int_or] ;

lemma bin_nth_ops:
  "!!x y. bin_nth (x AND y) n = (bin_nth x n & bin_nth y n)" 
  "!!x y. bin_nth (x OR y) n = (bin_nth x n | bin_nth y n)"
  "!!x y. bin_nth (x XOR y) n = (bin_nth x n ~= bin_nth y n)" 
  "!!x. bin_nth (NOT x) n = (~ bin_nth x n)"
  apply (induct n)
         apply safe
                         apply (case_tac [!] x rule: bin_exhaust)
                         apply simp_all
                      apply (case_tac [!] y rule: bin_exhaust)
                      apply simp_all
        apply (auto dest: not_B1_is_B0 intro: B1_ass_B0)
  done

(* interaction between bit-wise and arithmetic *)
(* good example of bin_induction *)
lemma bin_add_not: "x + NOT x = Numeral.Min"
  apply (induct x rule: bin_induct)
    apply clarsimp
   apply clarsimp
  apply (case_tac bit, auto)
  done

(* truncating results of bit-wise operations *)
lemma bin_trunc_ao: 
  "!!x y. (bintrunc n x) AND (bintrunc n y) = bintrunc n (x AND y)" 
  "!!x y. (bintrunc n x) OR (bintrunc n y) = bintrunc n (x OR y)"
  apply (induct n)
      apply auto
      apply (case_tac [!] x rule: bin_exhaust)
      apply (case_tac [!] y rule: bin_exhaust)
      apply auto
  done

lemma bin_trunc_xor: 
  "!!x y. bintrunc n (bintrunc n x XOR bintrunc n y) = 
          bintrunc n (x XOR y)"
  apply (induct n)
   apply auto
   apply (case_tac [!] x rule: bin_exhaust)
   apply (case_tac [!] y rule: bin_exhaust)
   apply auto
  done

lemma bin_trunc_not: 
  "!!x. bintrunc n (NOT (bintrunc n x)) = bintrunc n (NOT x)"
  apply (induct n)
   apply auto
   apply (case_tac [!] x rule: bin_exhaust)
   apply auto
  done

(* want theorems of the form of bin_trunc_xor *)
lemma bintr_bintr_i:
  "x = bintrunc n y ==> bintrunc n x = bintrunc n y"
  by auto

lemmas bin_trunc_and = bin_trunc_ao(1) [THEN bintr_bintr_i]
lemmas bin_trunc_or = bin_trunc_ao(2) [THEN bintr_bintr_i]

subsection {* Setting and clearing bits *}

consts
  bin_sc :: "nat => bit => int => int"

primrec
  Z : "bin_sc 0 b w = bin_rest w BIT b"
  Suc :
    "bin_sc (Suc n) b w = bin_sc n b (bin_rest w) BIT bin_last w"

(** nth bit, set/clear **)

lemma bin_nth_sc [simp]: 
  "!!w. bin_nth (bin_sc n b w) n = (b = bit.B1)"
  by (induct n)  auto

lemma bin_sc_sc_same [simp]: 
  "!!w. bin_sc n c (bin_sc n b w) = bin_sc n c w"
  by (induct n) auto

lemma bin_sc_sc_diff:
  "!!w m. m ~= n ==> 
    bin_sc m c (bin_sc n b w) = bin_sc n b (bin_sc m c w)"
  apply (induct n)
   apply safe
   apply (case_tac [!] m)
     apply auto
  done

lemma bin_nth_sc_gen: 
  "!!w m. bin_nth (bin_sc n b w) m = (if m = n then b = bit.B1 else bin_nth w m)"
  by (induct n) (case_tac [!] m, auto)
  
lemma bin_sc_nth [simp]:
  "!!w. (bin_sc n (If (bin_nth w n) bit.B1 bit.B0) w) = w"
  by (induct n) auto

lemma bin_sign_sc [simp]:
  "!!w. bin_sign (bin_sc n b w) = bin_sign w"
  by (induct n) auto
  
lemma bin_sc_bintr [simp]: 
  "!!w m. bintrunc m (bin_sc n x (bintrunc m (w))) = bintrunc m (bin_sc n x w)"
  apply (induct n)
   apply (case_tac [!] w rule: bin_exhaust)
   apply (case_tac [!] m, auto)
  done

lemma bin_clr_le:
  "!!w. bin_sc n bit.B0 w <= w"
  apply (induct n) 
   apply (case_tac [!] w rule: bin_exhaust)
   apply auto
   apply (unfold Bit_def)
   apply (simp_all split: bit.split)
  done

lemma bin_set_ge:
  "!!w. bin_sc n bit.B1 w >= w"
  apply (induct n) 
   apply (case_tac [!] w rule: bin_exhaust)
   apply auto
   apply (unfold Bit_def)
   apply (simp_all split: bit.split)
  done

lemma bintr_bin_clr_le:
  "!!w m. bintrunc n (bin_sc m bit.B0 w) <= bintrunc n w"
  apply (induct n)
   apply simp
  apply (case_tac w rule: bin_exhaust)
  apply (case_tac m)
   apply auto
   apply (unfold Bit_def)
   apply (simp_all split: bit.split)
  done

lemma bintr_bin_set_ge:
  "!!w m. bintrunc n (bin_sc m bit.B1 w) >= bintrunc n w"
  apply (induct n)
   apply simp
  apply (case_tac w rule: bin_exhaust)
  apply (case_tac m)
   apply auto
   apply (unfold Bit_def)
   apply (simp_all split: bit.split)
  done

lemma bin_sc_FP [simp]: "bin_sc n bit.B0 Numeral.Pls = Numeral.Pls"
  by (induct n) auto

lemma bin_sc_TM [simp]: "bin_sc n bit.B1 Numeral.Min = Numeral.Min"
  by (induct n) auto
  
lemmas bin_sc_simps = bin_sc.Z bin_sc.Suc bin_sc_TM bin_sc_FP

lemma bin_sc_minus:
  "0 < n ==> bin_sc (Suc (n - 1)) b w = bin_sc n b w"
  by auto

lemmas bin_sc_Suc_minus = 
  trans [OF bin_sc_minus [symmetric] bin_sc.Suc, standard]

lemmas bin_sc_Suc_pred [simp] = 
  bin_sc_Suc_minus [of "number_of bin", simplified nobm1, standard]

subsection {* Operations on lists of booleans *}

consts
  bin_to_bl :: "nat => int => bool list"
  bin_to_bl_aux :: "nat => int => bool list => bool list"
  bl_to_bin :: "bool list => int"
  bl_to_bin_aux :: "int => bool list => int"

  bl_of_nth :: "nat => (nat => bool) => bool list"

primrec
  Nil : "bl_to_bin_aux w [] = w"
  Cons : "bl_to_bin_aux w (b # bs) = 
      bl_to_bin_aux (w BIT (if b then bit.B1 else bit.B0)) bs"

primrec
  Z : "bin_to_bl_aux 0 w bl = bl"
  Suc : "bin_to_bl_aux (Suc n) w bl =
    bin_to_bl_aux n (bin_rest w) ((bin_last w = bit.B1) # bl)"

defs
  bin_to_bl_def : "bin_to_bl n w == bin_to_bl_aux n w []"
  bl_to_bin_def : "bl_to_bin bs == bl_to_bin_aux Numeral.Pls bs"

primrec
  Suc : "bl_of_nth (Suc n) f = f n # bl_of_nth n f"
  Z : "bl_of_nth 0 f = []"

consts
  takefill :: "'a => nat => 'a list => 'a list"
  app2 :: "('a => 'b => 'c) => 'a list => 'b list => 'c list"

-- "takefill - like take but if argument list too short,"
-- "extends result to get requested length"
primrec
  Z : "takefill fill 0 xs = []"
  Suc : "takefill fill (Suc n) xs = (
    case xs of [] => fill # takefill fill n xs
      | y # ys => y # takefill fill n ys)"

defs
  app2_def : "app2 f as bs == map (split f) (zip as bs)"

subsection {* Splitting and concatenation *}

-- "rcat and rsplit"
consts
  bin_rcat :: "nat => int list => int"
  bin_rsplit_aux :: "nat * int list * nat * int => int list"
  bin_rsplit :: "nat => (nat * int) => int list"
  bin_rsplitl_aux :: "nat * int list * nat * int => int list"
  bin_rsplitl :: "nat => (nat * int) => int list"
  
recdef bin_rsplit_aux "measure (fst o snd o snd)"
  "bin_rsplit_aux (n, bs, (m, c)) =
    (if m = 0 | n = 0 then bs else
      let (a, b) = bin_split n c 
      in bin_rsplit_aux (n, b # bs, (m - n, a)))"

recdef bin_rsplitl_aux "measure (fst o snd o snd)"
  "bin_rsplitl_aux (n, bs, (m, c)) =
    (if m = 0 | n = 0 then bs else
      let (a, b) = bin_split (min m n) c 
      in bin_rsplitl_aux (n, b # bs, (m - n, a)))"

defs
  bin_rcat_def : "bin_rcat n bs == foldl (%u v. bin_cat u n v) Numeral.Pls bs"
  bin_rsplit_def : "bin_rsplit n w == bin_rsplit_aux (n, [], w)"
  bin_rsplitl_def : "bin_rsplitl n w == bin_rsplitl_aux (n, [], w)"
     
 
(* potential for looping *)
declare bin_rsplit_aux.simps [simp del]
declare bin_rsplitl_aux.simps [simp del]

lemma bin_sign_cat: 
  "!!y. bin_sign (bin_cat x n y) = bin_sign x"
  by (induct n) auto

lemma bin_cat_Suc_Bit:
  "bin_cat w (Suc n) (v BIT b) = bin_cat w n v BIT b"
  by auto

lemma bin_nth_cat: 
  "!!n y. bin_nth (bin_cat x k y) n = 
    (if n < k then bin_nth y n else bin_nth x (n - k))"
  apply (induct k)
   apply clarsimp
  apply (case_tac n, auto)
  done

lemma bin_nth_split:
  "!!b c. bin_split n c = (a, b) ==> 
    (ALL k. bin_nth a k = bin_nth c (n + k)) & 
    (ALL k. bin_nth b k = (k < n & bin_nth c k))"
  apply (induct n)
   apply clarsimp
  apply (clarsimp simp: Let_def split: ls_splits)
  apply (case_tac k)
  apply auto
  done

lemma bin_cat_assoc: 
  "!!z. bin_cat (bin_cat x m y) n z = bin_cat x (m + n) (bin_cat y n z)" 
  by (induct n) auto

lemma bin_cat_assoc_sym: "!!z m. 
  bin_cat x m (bin_cat y n z) = bin_cat (bin_cat x (m - n) y) (min m n) z"
  apply (induct n, clarsimp)
  apply (case_tac m, auto)
  done

lemma bin_cat_Pls [simp]: 
  "!!w. bin_cat Numeral.Pls n w = bintrunc n w"
  by (induct n) auto

lemma bintr_cat1: 
  "!!b. bintrunc (k + n) (bin_cat a n b) = bin_cat (bintrunc k a) n b"
  by (induct n) auto
    
lemma bintr_cat: "bintrunc m (bin_cat a n b) = 
    bin_cat (bintrunc (m - n) a) n (bintrunc (min m n) b)"
  by (rule bin_eqI) (auto simp: bin_nth_cat nth_bintr)
    
lemma bintr_cat_same [simp]: 
  "bintrunc n (bin_cat a n b) = bintrunc n b"
  by (auto simp add : bintr_cat)

lemma cat_bintr [simp]: 
  "!!b. bin_cat a n (bintrunc n b) = bin_cat a n b"
  by (induct n) auto

lemma split_bintrunc: 
  "!!b c. bin_split n c = (a, b) ==> b = bintrunc n c"
  by (induct n) (auto simp: Let_def split: ls_splits)

lemma bin_cat_split:
  "!!v w. bin_split n w = (u, v) ==> w = bin_cat u n v"
  by (induct n) (auto simp: Let_def split: ls_splits)

lemma bin_split_cat:
  "!!w. bin_split n (bin_cat v n w) = (v, bintrunc n w)"
  by (induct n) auto

lemma bin_split_Pls [simp]:
  "bin_split n Numeral.Pls = (Numeral.Pls, Numeral.Pls)"
  by (induct n) (auto simp: Let_def split: ls_splits)

lemma bin_split_Min [simp]:
  "bin_split n Numeral.Min = (Numeral.Min, bintrunc n Numeral.Min)"
  by (induct n) (auto simp: Let_def split: ls_splits)

lemma bin_split_trunc:
  "!!m b c. bin_split (min m n) c = (a, b) ==> 
    bin_split n (bintrunc m c) = (bintrunc (m - n) a, b)"
  apply (induct n, clarsimp)
  apply (simp add: bin_rest_trunc Let_def split: ls_splits)
  apply (case_tac m)
   apply (auto simp: Let_def split: ls_splits)
  done

lemma bin_split_trunc1:
  "!!m b c. bin_split n c = (a, b) ==> 
    bin_split n (bintrunc m c) = (bintrunc (m - n) a, bintrunc m b)"
  apply (induct n, clarsimp)
  apply (simp add: bin_rest_trunc Let_def split: ls_splits)
  apply (case_tac m)
   apply (auto simp: Let_def split: ls_splits)
  done

lemma bin_cat_num:
  "!!b. bin_cat a n b = a * 2 ^ n + bintrunc n b"
  apply (induct n, clarsimp)
  apply (simp add: Bit_def cong: number_of_False_cong)
  done

lemma bin_split_num:
  "!!b. bin_split n b = (b div 2 ^ n, b mod 2 ^ n)"
  apply (induct n, clarsimp)
  apply (simp add: bin_rest_div zdiv_zmult2_eq)
  apply (case_tac b rule: bin_exhaust)
  apply simp
  apply (simp add: Bit_def zmod_zmult_zmult1 p1mod22k
              split: bit.split 
              cong: number_of_False_cong)
  done 

subsection {* Miscellaneous lemmas *}

lemma nth_2p_bin: 
  "!!m. bin_nth (2 ^ n) m = (m = n)"
  apply (induct n)
   apply clarsimp
   apply safe
     apply (case_tac m) 
      apply (auto simp: trans [OF numeral_1_eq_1 [symmetric] number_of_eq])
   apply (case_tac m) 
    apply (auto simp: Bit_B0_2t [symmetric])
  done

(* for use when simplifying with bin_nth_Bit *)

lemma ex_eq_or:
  "(EX m. n = Suc m & (m = k | P m)) = (n = Suc k | (EX m. n = Suc m & P m))"
  by auto

end

