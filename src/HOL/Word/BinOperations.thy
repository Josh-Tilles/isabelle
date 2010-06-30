(* 
  Author: Jeremy Dawson and Gerwin Klein, NICTA

  definition and basic theorems for bit-wise logical operations 
  for integers expressed using Pls, Min, BIT,
  and converting them to and from lists of bools
*) 

header {* Bitwise Operations on Binary Integers *}

theory BinOperations
imports Bit_Operations BinGeneral
begin

subsection {* Logical operations *}

text "bit-wise logical operations on the int type"

instantiation int :: bit
begin

definition
  int_not_def [code del]: "bitNOT = bin_rec Int.Min Int.Pls 
    (\<lambda>w b s. s BIT (NOT b))"

definition
  int_and_def [code del]: "bitAND = bin_rec (\<lambda>x. Int.Pls) (\<lambda>y. y) 
    (\<lambda>w b s y. s (bin_rest y) BIT (b AND bin_last y))"

definition
  int_or_def [code del]: "bitOR = bin_rec (\<lambda>x. x) (\<lambda>y. Int.Min) 
    (\<lambda>w b s y. s (bin_rest y) BIT (b OR bin_last y))"

definition
  int_xor_def [code del]: "bitXOR = bin_rec (\<lambda>x. x) bitNOT 
    (\<lambda>w b s y. s (bin_rest y) BIT (b XOR bin_last y))"

instance ..

end

lemma int_not_simps [simp]:
  "NOT Int.Pls = Int.Min"
  "NOT Int.Min = Int.Pls"
  "NOT (Int.Bit0 w) = Int.Bit1 (NOT w)"
  "NOT (Int.Bit1 w) = Int.Bit0 (NOT w)"
  "NOT (w BIT b) = (NOT w) BIT (NOT b)"
  unfolding int_not_def by (simp_all add: bin_rec_simps)

declare int_not_simps(1-4) [code]

lemma int_xor_Pls [simp, code]: 
  "Int.Pls XOR x = x"
  unfolding int_xor_def by (simp add: bin_rec_PM)

lemma int_xor_Min [simp, code]: 
  "Int.Min XOR x = NOT x"
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

lemma int_xor_Bits2 [simp, code]: 
  "(Int.Bit0 x) XOR (Int.Bit0 y) = Int.Bit0 (x XOR y)"
  "(Int.Bit0 x) XOR (Int.Bit1 y) = Int.Bit1 (x XOR y)"
  "(Int.Bit1 x) XOR (Int.Bit0 y) = Int.Bit1 (x XOR y)"
  "(Int.Bit1 x) XOR (Int.Bit1 y) = Int.Bit0 (x XOR y)"
  unfolding BIT_simps [symmetric] int_xor_Bits by simp_all

lemma int_xor_x_simps':
  "w XOR (Int.Pls BIT 0) = w"
  "w XOR (Int.Min BIT 1) = NOT w"
  apply (induct w rule: bin_induct)
       apply simp_all[4]
   apply (unfold int_xor_Bits)
   apply clarsimp+
  done

lemma int_xor_extra_simps [simp, code]:
  "w XOR Int.Pls = w"
  "w XOR Int.Min = NOT w"
  using int_xor_x_simps' by simp_all

lemma int_or_Pls [simp, code]: 
  "Int.Pls OR x = x"
  by (unfold int_or_def) (simp add: bin_rec_PM)
  
lemma int_or_Min [simp, code]:
  "Int.Min OR x = Int.Min"
  by (unfold int_or_def) (simp add: bin_rec_PM)

lemma int_or_Bits [simp]: 
  "(x BIT b) OR (y BIT c) = (x OR y) BIT (b OR c)"
  unfolding int_or_def by (simp add: bin_rec_simps)

lemma int_or_Bits2 [simp, code]: 
  "(Int.Bit0 x) OR (Int.Bit0 y) = Int.Bit0 (x OR y)"
  "(Int.Bit0 x) OR (Int.Bit1 y) = Int.Bit1 (x OR y)"
  "(Int.Bit1 x) OR (Int.Bit0 y) = Int.Bit1 (x OR y)"
  "(Int.Bit1 x) OR (Int.Bit1 y) = Int.Bit1 (x OR y)"
  unfolding BIT_simps [symmetric] int_or_Bits by simp_all

lemma int_or_x_simps': 
  "w OR (Int.Pls BIT 0) = w"
  "w OR (Int.Min BIT 1) = Int.Min"
  apply (induct w rule: bin_induct)
       apply simp_all[4]
   apply (unfold int_or_Bits)
   apply clarsimp+
  done

lemma int_or_extra_simps [simp, code]:
  "w OR Int.Pls = w"
  "w OR Int.Min = Int.Min"
  using int_or_x_simps' by simp_all

lemma int_and_Pls [simp, code]:
  "Int.Pls AND x = Int.Pls"
  unfolding int_and_def by (simp add: bin_rec_PM)

lemma int_and_Min [simp, code]:
  "Int.Min AND x = x"
  unfolding int_and_def by (simp add: bin_rec_PM)

lemma int_and_Bits [simp]: 
  "(x BIT b) AND (y BIT c) = (x AND y) BIT (b AND c)" 
  unfolding int_and_def by (simp add: bin_rec_simps)

lemma int_and_Bits2 [simp, code]: 
  "(Int.Bit0 x) AND (Int.Bit0 y) = Int.Bit0 (x AND y)"
  "(Int.Bit0 x) AND (Int.Bit1 y) = Int.Bit0 (x AND y)"
  "(Int.Bit1 x) AND (Int.Bit0 y) = Int.Bit0 (x AND y)"
  "(Int.Bit1 x) AND (Int.Bit1 y) = Int.Bit1 (x AND y)"
  unfolding BIT_simps [symmetric] int_and_Bits by simp_all

lemma int_and_x_simps': 
  "w AND (Int.Pls BIT 0) = Int.Pls"
  "w AND (Int.Min BIT 1) = w"
  apply (induct w rule: bin_induct)
       apply simp_all[4]
   apply (unfold int_and_Bits)
   apply clarsimp+
  done

lemma int_and_extra_simps [simp, code]:
  "w AND Int.Pls = Int.Pls"
  "w AND Int.Min = w"
  using int_and_x_simps' by simp_all

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
  "(x::int) XOR x = Int.Pls"
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
             apply (auto simp del: BIT_simps)
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
   apply (case_tac [!] bit, auto simp del: BIT_simps)
  done

lemma bbw_oa_dist: 
  "!!y z::int. (x AND y) OR z = 
          (x OR z) AND (y OR z)"
  apply (induct x rule: bin_induct)
    apply auto
  apply (case_tac y rule: bin_exhaust)
  apply (case_tac z rule: bin_exhaust)
  apply (case_tac ba, auto simp del: BIT_simps)
  done

lemma bbw_ao_dist: 
  "!!y z::int. (x OR y) AND z = 
          (x AND z) OR (y AND z)"
   apply (induct x rule: bin_induct)
    apply auto
  apply (case_tac y rule: bin_exhaust)
  apply (case_tac z rule: bin_exhaust)
  apply (case_tac ba, auto simp del: BIT_simps)
  done

(*
Why were these declared simp???
declare bin_ops_comm [simp] bbw_assocs [simp] 
*)

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
  "!!x.  bin_sign y = Int.Pls ==> x <= x OR y"
  apply (induct y rule: bin_induct)
    apply clarsimp
   apply clarsimp
  apply (case_tac x rule: bin_exhaust)
  apply (case_tac b)
   apply (case_tac [!] bit)
     apply (auto simp: less_eq_int_code)
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
                         apply (simp_all del: BIT_simps)
                      apply (case_tac [!] y rule: bin_exhaust)
                      apply (simp_all del: BIT_simps)
        apply (auto dest: not_B1_is_B0 intro: B1_ass_B0)
  done

(* interaction between bit-wise and arithmetic *)
(* good example of bin_induction *)
lemma bin_add_not: "x + NOT x = Int.Min"
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

primrec
  bin_sc :: "nat => bit => int => int"
where
  Z: "bin_sc 0 b w = bin_rest w BIT b"
  | Suc: "bin_sc (Suc n) b w = bin_sc n b (bin_rest w) BIT bin_last w"

(** nth bit, set/clear **)

lemma bin_nth_sc [simp]: 
  "!!w. bin_nth (bin_sc n b w) n = (b = 1)"
  by (induct n)  auto

lemma bin_sc_sc_same [simp]: 
  "!!w. bin_sc n c (bin_sc n b w) = bin_sc n c w"
  by (induct n) auto

lemma bin_sc_sc_diff:
  "!!w m. m ~= n ==> 
    bin_sc m c (bin_sc n b w) = bin_sc n b (bin_sc m c w)"
  apply (induct n)
   apply (case_tac [!] m)
     apply auto
  done

lemma bin_nth_sc_gen: 
  "!!w m. bin_nth (bin_sc n b w) m = (if m = n then b = 1 else bin_nth w m)"
  by (induct n) (case_tac [!] m, auto)
  
lemma bin_sc_nth [simp]:
  "!!w. (bin_sc n (If (bin_nth w n) 1 0) w) = w"
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
  "!!w. bin_sc n 0 w <= w"
  apply (induct n) 
   apply (case_tac [!] w rule: bin_exhaust)
   apply (auto simp del: BIT_simps)
   apply (unfold Bit_def)
   apply (simp_all split: bit.split)
  done

lemma bin_set_ge:
  "!!w. bin_sc n 1 w >= w"
  apply (induct n) 
   apply (case_tac [!] w rule: bin_exhaust)
   apply (auto simp del: BIT_simps)
   apply (unfold Bit_def)
   apply (simp_all split: bit.split)
  done

lemma bintr_bin_clr_le:
  "!!w m. bintrunc n (bin_sc m 0 w) <= bintrunc n w"
  apply (induct n)
   apply simp
  apply (case_tac w rule: bin_exhaust)
  apply (case_tac m)
   apply (auto simp del: BIT_simps)
   apply (unfold Bit_def)
   apply (simp_all split: bit.split)
  done

lemma bintr_bin_set_ge:
  "!!w m. bintrunc n (bin_sc m 1 w) >= bintrunc n w"
  apply (induct n)
   apply simp
  apply (case_tac w rule: bin_exhaust)
  apply (case_tac m)
   apply (auto simp del: BIT_simps)
   apply (unfold Bit_def)
   apply (simp_all split: bit.split)
  done

lemma bin_sc_FP [simp]: "bin_sc n 0 Int.Pls = Int.Pls"
  by (induct n) auto

lemma bin_sc_TM [simp]: "bin_sc n 1 Int.Min = Int.Min"
  by (induct n) auto
  
lemmas bin_sc_simps = bin_sc.Z bin_sc.Suc bin_sc_TM bin_sc_FP

lemma bin_sc_minus:
  "0 < n ==> bin_sc (Suc (n - 1)) b w = bin_sc n b w"
  by auto

lemmas bin_sc_Suc_minus = 
  trans [OF bin_sc_minus [symmetric] bin_sc.Suc, standard]

lemmas bin_sc_Suc_pred [simp] = 
  bin_sc_Suc_minus [of "number_of bin", simplified nobm1, standard]


subsection {* Splitting and concatenation *}

definition bin_rcat :: "nat \<Rightarrow> int list \<Rightarrow> int" where
  "bin_rcat n = foldl (%u v. bin_cat u n v) Int.Pls"

fun bin_rsplit_aux :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list" where
  "bin_rsplit_aux n m c bs =
    (if m = 0 | n = 0 then bs else
      let (a, b) = bin_split n c 
      in bin_rsplit_aux n (m - n) a (b # bs))"

definition bin_rsplit :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> int list" where
  "bin_rsplit n w = bin_rsplit_aux n (fst w) (snd w) []"

fun bin_rsplitl_aux :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list" where
  "bin_rsplitl_aux n m c bs =
    (if m = 0 | n = 0 then bs else
      let (a, b) = bin_split (min m n) c 
      in bin_rsplitl_aux n (m - n) a (b # bs))"

definition bin_rsplitl :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> int list" where
  "bin_rsplitl n w = bin_rsplitl_aux n (fst w) (snd w) []"

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
  "!!w. bin_cat Int.Pls n w = bintrunc n w"
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
  "bin_split n Int.Pls = (Int.Pls, Int.Pls)"
  by (induct n) (auto simp: Let_def split: ls_splits)

lemma bin_split_Min [simp]:
  "bin_split n Int.Min = (Int.Min, bintrunc n Int.Min)"
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
  apply (simp add: Bit_def mod_mult_mult1 p1mod22k
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

