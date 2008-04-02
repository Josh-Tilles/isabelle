(* 
  ID:      $Id$
  Author:  Jeremy Dawson, NICTA
*) 

header {* Useful Numerical Lemmas *}

theory Num_Lemmas
imports Main Parity
begin

datatype bit = B0 | B1

definition
  Bit :: "int \<Rightarrow> bit \<Rightarrow> int" (infixl "BIT" 90) where
  "k BIT b = (case b of B0 \<Rightarrow> 0 | B1 \<Rightarrow> 1) + k + k"

lemma BIT_B0_eq_Bit0 [simp]: "w BIT B0 = Int.Bit0 w"
  unfolding Bit_def Bit0_def by simp

lemma BIT_B1_eq_Bit1 [simp]: "w BIT B1 = Int.Bit1 w"
  unfolding Bit_def Bit1_def by simp

lemmas BIT_simps = BIT_B0_eq_Bit0 BIT_B1_eq_Bit1

hide (open) const B0 B1

lemma contentsI: "y = {x} ==> contents y = x" 
  unfolding contents_def by auto

lemma prod_case_split: "prod_case = split"
  by (rule ext)+ auto
 
lemmas split_split = prod.split [unfolded prod_case_split] 
lemmas split_split_asm = prod.split_asm [unfolded prod_case_split]
lemmas "split.splits" = split_split split_split_asm 

lemmas funpow_0 = funpow.simps(1)
lemmas funpow_Suc = funpow.simps(2)

lemma nonemptyE: "S ~= {} ==> (!!x. x : S ==> R) ==> R"
  apply (erule contrapos_np)
  apply (rule equals0I)
  apply auto
  done

lemma gt_or_eq_0: "0 < y \<or> 0 = (y::nat)" by auto

constdefs
  -- "alternative way of defining @{text bin_last}, @{text bin_rest}"
  bin_rl :: "int => int * bit" 
  "bin_rl w == SOME (r, l). w = r BIT l"

declare iszero_0 [iff]

lemmas xtr1 = xtrans(1)
lemmas xtr2 = xtrans(2)
lemmas xtr3 = xtrans(3)
lemmas xtr4 = xtrans(4)
lemmas xtr5 = xtrans(5)
lemmas xtr6 = xtrans(6)
lemmas xtr7 = xtrans(7)
lemmas xtr8 = xtrans(8)

lemma Min_ne_Pls [iff]:  
  "Int.Min ~= Int.Pls"
  unfolding Min_def Pls_def by auto

lemmas Pls_ne_Min [iff] = Min_ne_Pls [symmetric]

lemmas PlsMin_defs [intro!] = 
  Pls_def Min_def Pls_def [symmetric] Min_def [symmetric]

lemmas PlsMin_simps [simp] = PlsMin_defs [THEN Eq_TrueI]

lemma number_of_False_cong: 
  "False \<Longrightarrow> number_of x = number_of y"
  by (rule FalseE)

lemmas nat_simps = diff_add_inverse2 diff_add_inverse
lemmas nat_iffs = le_add1 le_add2

lemma sum_imp_diff: "j = k + i ==> j - i = (k :: nat)"
  by (clarsimp simp add: nat_simps)

lemma nobm1:
  "0 < (number_of w :: nat) ==> 
   number_of w - (1 :: nat) = number_of (Int.pred w)"
  apply (unfold nat_number_of_def One_nat_def nat_1 [symmetric] pred_def)
  apply (simp add: number_of_eq nat_diff_distrib [symmetric])
  done

lemma of_int_power:
  "of_int (a ^ n) = (of_int a ^ n :: 'a :: {recpower, comm_ring_1})" 
  by (induct n) (auto simp add: power_Suc)

lemma zless2: "0 < (2 :: int)" 
  by auto

lemmas zless2p [simp] = zless2 [THEN zero_less_power]
lemmas zle2p [simp] = zless2p [THEN order_less_imp_le]

lemmas pos_mod_sign2 = zless2 [THEN pos_mod_sign [where b = "2::int"]]
lemmas pos_mod_bound2 = zless2 [THEN pos_mod_bound [where b = "2::int"]]

-- "the inverse(s) of @{text number_of}"
lemma nmod2: "n mod (2::int) = 0 | n mod 2 = 1"
  by (cases "n mod 2 = 0", simp_all)

lemma emep1:
  "even n ==> even d ==> 0 <= d ==> (n + 1) mod (d :: int) = (n mod d) + 1"
  apply (simp add: add_commute)
  apply (safe dest!: even_equiv_def [THEN iffD1])
  apply (subst pos_zmod_mult_2)
   apply arith
  apply (simp add: zmod_zmult_zmult1)
 done

lemmas eme1p = emep1 [simplified add_commute]

lemma le_diff_eq': "(a \<le> c - b) = (b + a \<le> (c::int))"
  by (simp add: le_diff_eq add_commute)

lemma less_diff_eq': "(a < c - b) = (b + a < (c::int))"
  by (simp add: less_diff_eq add_commute)

lemma diff_le_eq': "(a - b \<le> c) = (a \<le> b + (c::int))"
  by (simp add: diff_le_eq add_commute)

lemma diff_less_eq': "(a - b < c) = (a < b + (c::int))"
  by (simp add: diff_less_eq add_commute)


lemmas m1mod2k = zless2p [THEN zmod_minus1]
lemmas m1mod22k = mult_pos_pos [OF zless2 zless2p, THEN zmod_minus1]
lemmas p1mod22k' = zless2p [THEN order_less_imp_le, THEN pos_zmod_mult_2]
lemmas z1pmod2' = zero_le_one [THEN pos_zmod_mult_2, simplified]
lemmas z1pdiv2' = zero_le_one [THEN pos_zdiv_mult_2, simplified]

lemma p1mod22k:
  "(2 * b + 1) mod (2 * 2 ^ n) = 2 * (b mod 2 ^ n) + (1::int)"
  by (simp add: p1mod22k' add_commute)

lemma z1pmod2:
  "(2 * b + 1) mod 2 = (1::int)"
  by (simp add: z1pmod2' add_commute)
  
lemma z1pdiv2:
  "(2 * b + 1) div 2 = (b::int)"
  by (simp add: z1pdiv2' add_commute)

lemmas zdiv_le_dividend = xtr3 [OF zdiv_1 [symmetric] zdiv_mono2,
  simplified int_one_le_iff_zero_less, simplified, standard]
  
(** ways in which type Bin resembles a datatype **)

lemma BIT_eq: "u BIT b = v BIT c ==> u = v & b = c"
  apply (unfold Bit_def)
  apply (simp (no_asm_use) split: bit.split_asm)
     apply simp_all
   apply (drule_tac f=even in arg_cong, clarsimp)+
  done
     
lemmas BIT_eqE [elim!] = BIT_eq [THEN conjE, standard]

lemma BIT_eq_iff [simp]: 
  "(u BIT b = v BIT c) = (u = v \<and> b = c)"
  by (rule iffI) auto

lemmas BIT_eqI [intro!] = conjI [THEN BIT_eq_iff [THEN iffD2]]

lemma less_Bits: 
  "(v BIT b < w BIT c) = (v < w | v <= w & b = bit.B0 & c = bit.B1)"
  unfolding Bit_def by (auto split: bit.split)

lemma le_Bits: 
  "(v BIT b <= w BIT c) = (v < w | v <= w & (b ~= bit.B1 | c ~= bit.B0))" 
  unfolding Bit_def by (auto split: bit.split)

lemma neB1E [elim!]:
  assumes ne: "y \<noteq> bit.B1"
  assumes y: "y = bit.B0 \<Longrightarrow> P"
  shows "P"
  apply (rule y)
  apply (cases y rule: bit.exhaust, simp)
  apply (simp add: ne)
  done

lemma bin_ex_rl: "EX w b. w BIT b = bin"
  apply (unfold Bit_def)
  apply (cases "even bin")
   apply (clarsimp simp: even_equiv_def)
   apply (auto simp: odd_equiv_def split: bit.split)
  done

lemma bin_exhaust:
  assumes Q: "\<And>x b. bin = x BIT b \<Longrightarrow> Q"
  shows "Q"
  apply (insert bin_ex_rl [of bin])  
  apply (erule exE)+
  apply (rule Q)
  apply force
  done

lemma bin_rl_char: "(bin_rl w = (r, l)) = (r BIT l = w)"
  apply (unfold bin_rl_def)
  apply safe
   apply (cases w rule: bin_exhaust)
   apply auto
  done

lemma bin_rl_simps [simp]:
  "bin_rl Int.Pls = (Int.Pls, bit.B0)"
  "bin_rl Int.Min = (Int.Min, bit.B1)"
  "bin_rl (r BIT b) = (r, b)"
  "bin_rl (Int.Bit0 r) = (r, bit.B0)"
  "bin_rl (Int.Bit1 r) = (r, bit.B1)"
  unfolding bin_rl_char by simp_all

lemma bin_abs_lem:
  "bin = (w BIT b) ==> ~ bin = Int.Min --> ~ bin = Int.Pls -->
    nat (abs w) < nat (abs bin)"
  apply (clarsimp simp add: bin_rl_char)
  apply (unfold Pls_def Min_def Bit_def)
  apply (cases b)
   apply (clarsimp, arith)
  apply (clarsimp, arith)
  done

lemma bin_induct:
  assumes PPls: "P Int.Pls"
    and PMin: "P Int.Min"
    and PBit: "!!bin bit. P bin ==> P (bin BIT bit)"
  shows "P bin"
  apply (rule_tac P=P and a=bin and f1="nat o abs" 
                  in wf_measure [THEN wf_induct])
  apply (simp add: measure_def inv_image_def)
  apply (case_tac x rule: bin_exhaust)
  apply (frule bin_abs_lem)
  apply (auto simp add : PPls PMin PBit)
  done

lemma numeral_induct:
  assumes Pls: "P Int.Pls"
  assumes Min: "P Int.Min"
  assumes Bit0: "\<And>w. \<lbrakk>P w; w \<noteq> Int.Pls\<rbrakk> \<Longrightarrow> P (Int.Bit0 w)"
  assumes Bit1: "\<And>w. \<lbrakk>P w; w \<noteq> Int.Min\<rbrakk> \<Longrightarrow> P (Int.Bit1 w)"
  shows "P x"
  apply (induct x rule: bin_induct)
    apply (rule Pls)
   apply (rule Min)
  apply (case_tac bit)
   apply (case_tac "bin = Int.Pls")
    apply simp
   apply (simp add: Bit0)
  apply (case_tac "bin = Int.Min")
   apply simp
  apply (simp add: Bit1)
  done

lemma no_no [simp]: "number_of (number_of i) = i"
  unfolding number_of_eq by simp

lemma Bit_B0:
  "k BIT bit.B0 = k + k"
   by (unfold Bit_def) simp

lemma Bit_B1:
  "k BIT bit.B1 = k + k + 1"
   by (unfold Bit_def) simp
  
lemma Bit_B0_2t: "k BIT bit.B0 = 2 * k"
  by (rule trans, rule Bit_B0) simp

lemma Bit_B1_2t: "k BIT bit.B1 = 2 * k + 1"
  by (rule trans, rule Bit_B1) simp

lemma B_mod_2': 
  "X = 2 ==> (w BIT bit.B1) mod X = 1 & (w BIT bit.B0) mod X = 0"
  apply (simp (no_asm) only: Bit_B0 Bit_B1)
  apply (simp add: z1pmod2)
  done

lemma B1_mod_2 [simp]: "(Int.Bit1 w) mod 2 = 1"
  unfolding numeral_simps number_of_is_id by (simp add: z1pmod2)

lemma B0_mod_2 [simp]: "(Int.Bit0 w) mod 2 = 0"
  unfolding numeral_simps number_of_is_id by simp

lemma axxbyy:
  "a + m + m = b + n + n ==> (a = 0 | a = 1) ==> (b = 0 | b = 1) ==>  
   a = b & m = (n :: int)"
  apply auto
   apply (drule_tac f="%n. n mod 2" in arg_cong)
   apply (clarsimp simp: z1pmod2)
  apply (drule_tac f="%n. n mod 2" in arg_cong)
  apply (clarsimp simp: z1pmod2)
  done

lemma axxmod2:
  "(1 + x + x) mod 2 = (1 :: int) & (0 + x + x) mod 2 = (0 :: int)" 
  by simp (rule z1pmod2)

lemma axxdiv2:
  "(1 + x + x) div 2 = (x :: int) & (0 + x + x) div 2 = (x :: int)" 
  by simp (rule z1pdiv2)

lemmas iszero_minus = trans [THEN trans,
  OF iszero_def neg_equal_0_iff_equal iszero_def [symmetric], standard]

lemmas zadd_diff_inverse = trans [OF diff_add_cancel [symmetric] add_commute,
  standard]

lemmas add_diff_cancel2 = add_commute [THEN diff_eq_eq [THEN iffD2], standard]

lemma zmod_uminus: "- ((a :: int) mod b) mod b = -a mod b"
  by (simp add : zmod_zminus1_eq_if)

lemma zmod_zsub_distrib: "((a::int) - b) mod c = (a mod c - b mod c) mod c"
  apply (unfold diff_int_def)
  apply (rule trans [OF _ zmod_zadd1_eq [symmetric]])
  apply (simp add: zmod_uminus zmod_zadd1_eq [symmetric])
  done

lemma zmod_zsub_right_eq: "((a::int) - b) mod c = (a - b mod c) mod c"
  apply (unfold diff_int_def)
  apply (rule trans [OF _ zmod_zadd_right_eq [symmetric]])
  apply (simp add : zmod_uminus zmod_zadd_right_eq [symmetric])
  done

lemma zmod_zsub_left_eq: "((a::int) - b) mod c = (a mod c - b) mod c"
  by (rule zmod_zadd_left_eq [where b = "- b", simplified diff_int_def [symmetric]])

lemma zmod_zsub_self [simp]: 
  "((b :: int) - a) mod a = b mod a"
  by (simp add: zmod_zsub_right_eq)

lemma zmod_zmult1_eq_rev:
  "b * a mod c = b mod c * a mod (c::int)"
  apply (simp add: mult_commute)
  apply (subst zmod_zmult1_eq)
  apply simp
  done

lemmas rdmods [symmetric] = zmod_uminus [symmetric]
  zmod_zsub_left_eq zmod_zsub_right_eq zmod_zadd_left_eq
  zmod_zadd_right_eq zmod_zmult1_eq zmod_zmult1_eq_rev

lemma mod_plus_right:
  "((a + x) mod m = (b + x) mod m) = (a mod m = b mod (m :: nat))"
  apply (induct x)
   apply (simp_all add: mod_Suc)
  apply arith
  done

lemma nat_minus_mod: "(n - n mod m) mod m = (0 :: nat)"
  by (induct n) (simp_all add : mod_Suc)

lemmas nat_minus_mod_plus_right = trans [OF nat_minus_mod mod_0 [symmetric],
  THEN mod_plus_right [THEN iffD2], standard, simplified]

lemmas push_mods' = zmod_zadd1_eq [standard]
  zmod_zmult_distrib [standard] zmod_zsub_distrib [standard]
  zmod_uminus [symmetric, standard]

lemmas push_mods = push_mods' [THEN eq_reflection, standard]
lemmas pull_mods = push_mods [symmetric] rdmods [THEN eq_reflection, standard]
lemmas mod_simps = 
  zmod_zmult_self1 [THEN eq_reflection] zmod_zmult_self2 [THEN eq_reflection]
  mod_mod_trivial [THEN eq_reflection]

lemma nat_mod_eq:
  "!!b. b < n ==> a mod n = b mod n ==> a mod n = (b :: nat)" 
  by (induct a) auto

lemmas nat_mod_eq' = refl [THEN [2] nat_mod_eq]

lemma nat_mod_lem: 
  "(0 :: nat) < n ==> b < n = (b mod n = b)"
  apply safe
   apply (erule nat_mod_eq')
  apply (erule subst)
  apply (erule mod_less_divisor)
  done

lemma mod_nat_add: 
  "(x :: nat) < z ==> y < z ==> 
   (x + y) mod z = (if x + y < z then x + y else x + y - z)"
  apply (rule nat_mod_eq)
   apply auto
  apply (rule trans)
   apply (rule le_mod_geq)
   apply simp
  apply (rule nat_mod_eq')
  apply arith
  done

lemma mod_nat_sub: 
  "(x :: nat) < z ==> (x - y) mod z = x - y"
  by (rule nat_mod_eq') arith

lemma int_mod_lem: 
  "(0 :: int) < n ==> (0 <= b & b < n) = (b mod n = b)"
  apply safe
    apply (erule (1) mod_pos_pos_trivial)
   apply (erule_tac [!] subst)
   apply auto
  done

lemma int_mod_eq:
  "(0 :: int) <= b ==> b < n ==> a mod n = b mod n ==> a mod n = b"
  by clarsimp (rule mod_pos_pos_trivial)

lemmas int_mod_eq' = refl [THEN [3] int_mod_eq]

lemma int_mod_le: "0 <= a ==> 0 < (n :: int) ==> a mod n <= a"
  apply (cases "a < n")
   apply (auto dest: mod_pos_pos_trivial pos_mod_bound [where a=a])
  done

lemma int_mod_le': "0 <= b - n ==> 0 < (n :: int) ==> b mod n <= b - n"
  by (rule int_mod_le [where a = "b - n" and n = n, simplified])

lemma int_mod_ge: "a < n ==> 0 < (n :: int) ==> a <= a mod n"
  apply (cases "0 <= a")
   apply (drule (1) mod_pos_pos_trivial)
   apply simp
  apply (rule order_trans [OF _ pos_mod_sign])
   apply simp
  apply assumption
  done

lemma int_mod_ge': "b < 0 ==> 0 < (n :: int) ==> b + n <= b mod n"
  by (rule int_mod_ge [where a = "b + n" and n = n, simplified])

lemma mod_add_if_z:
  "(x :: int) < z ==> y < z ==> 0 <= y ==> 0 <= x ==> 0 <= z ==> 
   (x + y) mod z = (if x + y < z then x + y else x + y - z)"
  by (auto intro: int_mod_eq)

lemma mod_sub_if_z:
  "(x :: int) < z ==> y < z ==> 0 <= y ==> 0 <= x ==> 0 <= z ==> 
   (x - y) mod z = (if y <= x then x - y else x - y + z)"
  by (auto intro: int_mod_eq)

lemmas zmde = zmod_zdiv_equality [THEN diff_eq_eq [THEN iffD2], symmetric]
lemmas mcl = mult_cancel_left [THEN iffD1, THEN make_pos_rule]

(* already have this for naturals, div_mult_self1/2, but not for ints *)
lemma zdiv_mult_self: "m ~= (0 :: int) ==> (a + m * n) div m = a div m + n"
  apply (rule mcl)
   prefer 2
   apply (erule asm_rl)
  apply (simp add: zmde ring_distribs)
  apply (simp add: push_mods)
  done

(** Rep_Integ **)
lemma eqne: "equiv A r ==> X : A // r ==> X ~= {}"
  unfolding equiv_def refl_def quotient_def Image_def by auto

lemmas Rep_Integ_ne = Integ.Rep_Integ 
  [THEN equiv_intrel [THEN eqne, simplified Integ_def [symmetric]], standard]

lemmas riq = Integ.Rep_Integ [simplified Integ_def]
lemmas intrel_refl = refl [THEN equiv_intrel_iff [THEN iffD1], standard]
lemmas Rep_Integ_equiv = quotient_eq_iff
  [OF equiv_intrel riq riq, simplified Integ.Rep_Integ_inject, standard]
lemmas Rep_Integ_same = 
  Rep_Integ_equiv [THEN intrel_refl [THEN rev_iffD2], standard]

lemma RI_int: "(a, 0) : Rep_Integ (int a)"
  unfolding int_def by auto

lemmas RI_intrel [simp] = UNIV_I [THEN quotientI,
  THEN Integ.Abs_Integ_inverse [simplified Integ_def], standard]

lemma RI_minus: "(a, b) : Rep_Integ x ==> (b, a) : Rep_Integ (- x)"
  apply (rule_tac z=x in eq_Abs_Integ)
  apply (clarsimp simp: minus)
  done

lemma RI_add: 
  "(a, b) : Rep_Integ x ==> (c, d) : Rep_Integ y ==> 
   (a + c, b + d) : Rep_Integ (x + y)"
  apply (rule_tac z=x in eq_Abs_Integ)
  apply (rule_tac z=y in eq_Abs_Integ) 
  apply (clarsimp simp: add)
  done

lemma mem_same: "a : S ==> a = b ==> b : S"
  by fast

(* two alternative proofs of this *)
lemma RI_eq_diff': "(a, b) : Rep_Integ (int a - int b)"
  apply (unfold diff_def)
  apply (rule mem_same)
   apply (rule RI_minus RI_add RI_int)+
  apply simp
  done

lemma RI_eq_diff: "((a, b) : Rep_Integ x) = (int a - int b = x)"
  apply safe
   apply (rule Rep_Integ_same)
    prefer 2
    apply (erule asm_rl)
   apply (rule RI_eq_diff')+
  done

lemma mod_power_lem:
  "a > 1 ==> a ^ n mod a ^ m = (if m <= n then 0 else (a :: int) ^ n)"
  apply clarsimp
  apply safe
   apply (simp add: zdvd_iff_zmod_eq_0 [symmetric])
   apply (drule le_iff_add [THEN iffD1])
   apply (force simp: zpower_zadd_distrib)
  apply (rule mod_pos_pos_trivial)
   apply (simp)
  apply (rule power_strict_increasing)
   apply auto
  done

lemma min_pm [simp]: "min a b + (a - b) = (a :: nat)"
  by arith
  
lemmas min_pm1 [simp] = trans [OF add_commute min_pm]

lemma rev_min_pm [simp]: "min b a + (a - b) = (a::nat)"
  by simp

lemmas rev_min_pm1 [simp] = trans [OF add_commute rev_min_pm]

lemma pl_pl_rels: 
  "a + b = c + d ==> 
   a >= c & b <= d | a <= c & b >= (d :: nat)"
  apply (cut_tac n=a and m=c in nat_le_linear)
  apply (safe dest!: le_iff_add [THEN iffD1])
         apply arith+
  done

lemmas pl_pl_rels' = add_commute [THEN [2] trans, THEN pl_pl_rels]

lemma minus_eq: "(m - k = m) = (k = 0 | m = (0 :: nat))"
  by arith

lemma pl_pl_mm: "(a :: nat) + b = c + d ==> a - c = d - b"
  by arith

lemmas pl_pl_mm' = add_commute [THEN [2] trans, THEN pl_pl_mm]
 
lemma min_minus [simp] : "min m (m - k) = (m - k :: nat)"
  by arith
  
lemmas min_minus' [simp] = trans [OF min_max.inf_commute min_minus]

lemma nat_no_eq_iff: 
  "(number_of b :: int) >= 0 ==> (number_of c :: int) >= 0 ==> 
   (number_of b = (number_of c :: nat)) = (b = c)"
  apply (unfold nat_number_of_def)
  apply safe
  apply (drule (2) eq_nat_nat_iff [THEN iffD1])
  apply (simp add: number_of_eq)
  done

lemmas dme = box_equals [OF div_mod_equality add_0_right add_0_right]
lemmas dtle = xtr3 [OF dme [symmetric] le_add1]
lemmas th2 = order_trans [OF order_refl [THEN [2] mult_le_mono] dtle]

lemma td_gal: 
  "0 < c ==> (a >= b * c) = (a div c >= (b :: nat))"
  apply safe
   apply (erule (1) xtr4 [OF div_le_mono div_mult_self_is_m])
  apply (erule th2)
  done
  
lemmas td_gal_lt = td_gal [simplified not_less [symmetric], simplified]

lemma div_mult_le: "(a :: nat) div b * b <= a"
  apply (cases b)
   prefer 2
   apply (rule order_refl [THEN th2])
  apply auto
  done

lemmas sdl = split_div_lemma [THEN iffD1, symmetric]

lemma given_quot: "f > (0 :: nat) ==> (f * l + (f - 1)) div f = l"
  by (rule sdl, assumption) (simp (no_asm))

lemma given_quot_alt: "f > (0 :: nat) ==> (l * f + f - Suc 0) div f = l"
  apply (frule given_quot)
  apply (rule trans)
   prefer 2
   apply (erule asm_rl)
  apply (rule_tac f="%n. n div f" in arg_cong)
  apply (simp add : mult_ac)
  done
    
lemma diff_mod_le: "(a::nat) < d ==> b dvd d ==> a - a mod b <= d - b"
  apply (unfold dvd_def)
  apply clarify
  apply (case_tac k)
   apply clarsimp
  apply clarify
  apply (cases "b > 0")
   apply (drule mult_commute [THEN xtr1])
   apply (frule (1) td_gal_lt [THEN iffD1])
   apply (clarsimp simp: le_simps)
   apply (rule mult_div_cancel [THEN [2] xtr4])
   apply (rule mult_mono)
      apply auto
  done

lemma less_le_mult':
  "w * c < b * c ==> 0 \<le> c ==> (w + 1) * c \<le> b * (c::int)"
  apply (rule mult_right_mono)
   apply (rule zless_imp_add1_zle)
   apply (erule (1) mult_right_less_imp_less)
  apply assumption
  done

lemmas less_le_mult = less_le_mult' [simplified left_distrib, simplified]

lemmas less_le_mult_minus = iffD2 [OF le_diff_eq less_le_mult, 
  simplified left_diff_distrib, standard]

lemma lrlem':
  assumes d: "(i::nat) \<le> j \<or> m < j'"
  assumes R1: "i * k \<le> j * k \<Longrightarrow> R"
  assumes R2: "Suc m * k' \<le> j' * k' \<Longrightarrow> R"
  shows "R" using d
  apply safe
   apply (rule R1, erule mult_le_mono1)
  apply (rule R2, erule Suc_le_eq [THEN iffD2 [THEN mult_le_mono1]])
  done

lemma lrlem: "(0::nat) < sc ==>
    (sc - n + (n + lb * n) <= m * n) = (sc + lb * n <= m * n)"
  apply safe
   apply arith
  apply (case_tac "sc >= n")
   apply arith
  apply (insert linorder_le_less_linear [of m lb])
  apply (erule_tac k=n and k'=n in lrlem')
   apply arith
  apply simp
  done

lemma gen_minus: "0 < n ==> f n = f (Suc (n - 1))"
  by auto

lemma mpl_lem: "j <= (i :: nat) ==> k < j ==> i - j + k < i"
  apply (induct i, clarsimp)
  apply (cases j, clarsimp)
  apply arith
  done

lemma nonneg_mod_div:
  "0 <= a ==> 0 <= b ==> 0 <= (a mod b :: int) & 0 <= a div b"
  apply (cases "b = 0", clarsimp)
  apply (auto intro: pos_imp_zdiv_nonneg_iff [THEN iffD2])
  done

end
