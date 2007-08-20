(* 
  ID:     $Id$
  Author: Jeremy Dawson, NICTA

  contains theorems to do with integers, expressed using Pls, Min, BIT,
  theorems linking them to lists of booleans, and repeated splitting 
  and concatenation.
*) 

header "Bool lists and integers"

theory BinBoolList imports BinOperations begin

section "Arithmetic in terms of bool lists"

consts (* arithmetic operations in terms of the reversed bool list,
  assuming input list(s) the same length, and don't extend them *)
  rbl_succ :: "bool list => bool list"
  rbl_pred :: "bool list => bool list"
  rbl_add :: "bool list => bool list => bool list"
  rbl_mult :: "bool list => bool list => bool list"

primrec 
  Nil: "rbl_succ Nil = Nil"
  Cons: "rbl_succ (x # xs) = (if x then False # rbl_succ xs else True # xs)"

primrec 
  Nil : "rbl_pred Nil = Nil"
  Cons : "rbl_pred (x # xs) = (if x then False # xs else True # rbl_pred xs)"

primrec (* result is length of first arg, second arg may be longer *)
  Nil : "rbl_add Nil x = Nil"
  Cons : "rbl_add (y # ys) x = (let ws = rbl_add ys (tl x) in 
    (y ~= hd x) # (if hd x & y then rbl_succ ws else ws))"

primrec (* result is length of first arg, second arg may be longer *)
  Nil : "rbl_mult Nil x = Nil"
  Cons : "rbl_mult (y # ys) x = (let ws = False # rbl_mult ys x in 
    if y then rbl_add ws x else ws)"

lemma tl_take: "tl (take n l) = take (n - 1) (tl l)"
  apply (cases n, clarsimp)
  apply (cases l, auto)
  done

lemma take_butlast [rule_format] :
  "ALL n. n < length l --> take n (butlast l) = take n l"
  apply (induct l, clarsimp)
  apply clarsimp
  apply (case_tac n)
  apply auto
  done

lemma butlast_take [rule_format] :
  "ALL n. n <= length l --> butlast (take n l) = take (n - 1) l"
  apply (induct l, clarsimp)
  apply clarsimp
  apply (case_tac "n")
   apply safe
   apply simp_all
  apply (case_tac "nat")
   apply auto
  done

lemma butlast_drop [rule_format] :
  "ALL n. butlast (drop n l) = drop n (butlast l)"
  apply (induct l)
   apply clarsimp
  apply clarsimp
  apply safe
   apply ((case_tac n, auto)[1])+
  done

lemma butlast_power:
  "(butlast ^ n) bl = take (length bl - n) bl"
  by (induct n) (auto simp: butlast_take)

lemma bin_to_bl_aux_Pls_minus_simp:
  "0 < n ==> bin_to_bl_aux n Numeral.Pls bl = 
    bin_to_bl_aux (n - 1) Numeral.Pls (False # bl)"
  by (cases n) auto

lemma bin_to_bl_aux_Min_minus_simp:
  "0 < n ==> bin_to_bl_aux n Numeral.Min bl = 
    bin_to_bl_aux (n - 1) Numeral.Min (True # bl)"
  by (cases n) auto

lemma bin_to_bl_aux_Bit_minus_simp:
  "0 < n ==> bin_to_bl_aux n (w BIT b) bl = 
    bin_to_bl_aux (n - 1) w ((b = bit.B1) # bl)"
  by (cases n) auto

declare bin_to_bl_aux_Pls_minus_simp [simp]
  bin_to_bl_aux_Min_minus_simp [simp]
  bin_to_bl_aux_Bit_minus_simp [simp]

(** link between bin and bool list **)

lemma bl_to_bin_aux_append [rule_format] : 
  "ALL w. bl_to_bin_aux w (bs @ cs) = bl_to_bin_aux (bl_to_bin_aux w bs) cs"
  by (induct bs) auto

lemma bin_to_bl_aux_append [rule_format] : 
  "ALL w bs. bin_to_bl_aux n w bs @ cs = bin_to_bl_aux n w (bs @ cs)"
  by (induct n) auto

lemma bl_to_bin_append: 
  "bl_to_bin (bs @ cs) = bl_to_bin_aux (bl_to_bin bs) cs"
  unfolding bl_to_bin_def by (rule bl_to_bin_aux_append)

lemma bin_to_bl_aux_alt: 
  "bin_to_bl_aux n w bs = bin_to_bl n w @ bs" 
  unfolding bin_to_bl_def by (simp add : bin_to_bl_aux_append)

lemma bin_to_bl_0: "bin_to_bl 0 bs = []"
  unfolding bin_to_bl_def by auto

lemma size_bin_to_bl_aux [rule_format] : 
  "ALL w bs. size (bin_to_bl_aux n w bs) = n + length bs"
  by (induct n) auto

lemma size_bin_to_bl: "size (bin_to_bl n w) = n" 
  unfolding bin_to_bl_def by (simp add : size_bin_to_bl_aux)

lemma bin_bl_bin' [rule_format] : 
  "ALL w bs. bl_to_bin (bin_to_bl_aux n w bs) = 
    bl_to_bin_aux (bintrunc n w) bs"
  by (induct n) (auto simp add : bl_to_bin_def)

lemma bin_bl_bin: "bl_to_bin (bin_to_bl n w) = bintrunc n w"
  unfolding bin_to_bl_def bin_bl_bin' by auto

lemma bl_bin_bl' [rule_format] :
  "ALL w n. bin_to_bl (n + length bs) (bl_to_bin_aux w bs) = 
    bin_to_bl_aux n w bs"
  apply (induct "bs")
   apply auto
    apply (simp_all only : add_Suc [symmetric])
    apply (auto simp add : bin_to_bl_def)
  done

lemma bl_bin_bl: "bin_to_bl (length bs) (bl_to_bin bs) = bs"
  unfolding bl_to_bin_def
  apply (rule box_equals)
    apply (rule bl_bin_bl')
   prefer 2
   apply (rule bin_to_bl_aux.Z)
  apply simp
  done
  
declare 
  bin_to_bl_0 [simp] 
  size_bin_to_bl [simp] 
  bin_bl_bin [simp] 
  bl_bin_bl [simp]

lemma bl_to_bin_inj:
  "bl_to_bin bs = bl_to_bin cs ==> length bs = length cs ==> bs = cs"
  apply (rule_tac box_equals)
    defer
    apply (rule bl_bin_bl)
   apply (rule bl_bin_bl)
  apply simp
  done

lemma bl_to_bin_False: "bl_to_bin (False # bl) = bl_to_bin bl"
  unfolding bl_to_bin_def by auto
  
lemma bl_to_bin_Nil: "bl_to_bin [] = Numeral.Pls"
  unfolding bl_to_bin_def by auto

lemma bin_to_bl_Pls_aux [rule_format] : 
  "ALL bl. bin_to_bl_aux n Numeral.Pls bl = replicate n False @ bl"
  by (induct n) (auto simp: replicate_app_Cons_same)

lemma bin_to_bl_Pls: "bin_to_bl n Numeral.Pls = replicate n False"
  unfolding bin_to_bl_def by (simp add : bin_to_bl_Pls_aux)

lemma bin_to_bl_Min_aux [rule_format] : 
  "ALL bl. bin_to_bl_aux n Numeral.Min bl = replicate n True @ bl"
  by (induct n) (auto simp: replicate_app_Cons_same)

lemma bin_to_bl_Min: "bin_to_bl n Numeral.Min = replicate n True"
  unfolding bin_to_bl_def by (simp add : bin_to_bl_Min_aux)

lemma bl_to_bin_rep_F: 
  "bl_to_bin (replicate n False @ bl) = bl_to_bin bl"
  apply (simp add: bin_to_bl_Pls_aux [symmetric] bin_bl_bin')
  apply (simp add: bl_to_bin_def)
  done

lemma bin_to_bl_trunc:
  "n <= m ==> bin_to_bl n (bintrunc m w) = bin_to_bl n w"
  by (auto intro: bl_to_bin_inj)

declare 
  bin_to_bl_trunc [simp] 
  bl_to_bin_False [simp] 
  bl_to_bin_Nil [simp]

lemma bin_to_bl_aux_bintr [rule_format] :
  "ALL m bin bl. bin_to_bl_aux n (bintrunc m bin) bl = 
    replicate (n - m) False @ bin_to_bl_aux (min n m) bin bl"
  apply (induct_tac "n")
   apply clarsimp
  apply clarsimp
  apply (case_tac "m")
   apply (clarsimp simp: bin_to_bl_Pls_aux) 
   apply (erule thin_rl)
   apply (induct_tac n)   
    apply auto
  done

lemmas bin_to_bl_bintr = 
  bin_to_bl_aux_bintr [where bl = "[]", folded bin_to_bl_def]

lemma bl_to_bin_rep_False: "bl_to_bin (replicate n False) = Numeral.Pls"
  by (induct n) auto

lemma len_bin_to_bl_aux [rule_format] : 
  "ALL w bs. length (bin_to_bl_aux n w bs) = n + length bs"
  by (induct "n") auto

lemma len_bin_to_bl [simp]: "length (bin_to_bl n w) = n"
  unfolding bin_to_bl_def len_bin_to_bl_aux by auto
  
lemma sign_bl_bin' [rule_format] : 
  "ALL w. bin_sign (bl_to_bin_aux w bs) = bin_sign w"
  by (induct bs) auto
  
lemma sign_bl_bin: "bin_sign (bl_to_bin bs) = Numeral.Pls"
  unfolding bl_to_bin_def by (simp add : sign_bl_bin')
  
lemma bl_sbin_sign_aux [rule_format] : 
  "ALL w bs. hd (bin_to_bl_aux (Suc n) w bs) = 
    (bin_sign (sbintrunc n w) = Numeral.Min)"
  apply (induct "n")
   apply clarsimp
   apply (case_tac w rule: bin_exhaust)
   apply (simp split add : bit.split)
  apply clarsimp
  done
    
lemma bl_sbin_sign: 
  "hd (bin_to_bl (Suc n) w) = (bin_sign (sbintrunc n w) = Numeral.Min)"
  unfolding bin_to_bl_def by (rule bl_sbin_sign_aux)

lemma bin_nth_of_bl_aux [rule_format] : 
  "ALL w. bin_nth (bl_to_bin_aux w bl) n = 
    (n < size bl & rev bl ! n | n >= length bl & bin_nth w (n - size bl))"
  apply (induct_tac bl)
   apply clarsimp
  apply clarsimp
  apply (cut_tac x=n and y="size list" in linorder_less_linear)
  apply (erule disjE, simp add: nth_append)+
  apply (simp add: nth_append)
  done

lemma bin_nth_of_bl: "bin_nth (bl_to_bin bl) n = (n < length bl & rev bl ! n)";
  unfolding bl_to_bin_def by (simp add : bin_nth_of_bl_aux)

lemma bin_nth_bl [rule_format] : "ALL m w. n < m --> 
    bin_nth w n = nth (rev (bin_to_bl m w)) n"
  apply (induct n)
   apply clarsimp
   apply (case_tac m, clarsimp)
   apply (clarsimp simp: bin_to_bl_def)
   apply (simp add: bin_to_bl_aux_alt)
  apply clarsimp
  apply (case_tac m, clarsimp)
  apply (clarsimp simp: bin_to_bl_def)
  apply (simp add: bin_to_bl_aux_alt)
  done

lemma nth_rev [rule_format] : 
  "n < length xs --> rev xs ! n = xs ! (length xs - 1 - n)"
  apply (induct_tac "xs")
   apply simp
  apply (clarsimp simp add : nth_append nth.simps split add : nat.split)
  apply (rule_tac f = "%n. list ! n" in arg_cong) 
  apply arith
  done

lemmas nth_rev_alt = nth_rev [where xs = "rev ?ys", simplified]

lemma nth_bin_to_bl_aux [rule_format] : 
  "ALL w n bl. n < m + length bl --> (bin_to_bl_aux m w bl) ! n = 
    (if n < m then bin_nth w (m - 1 - n) else bl ! (n - m))"
  apply (induct_tac "m")
   apply clarsimp
  apply clarsimp
  apply (case_tac w rule: bin_exhaust)
  apply clarsimp
  apply (case_tac "na - n")
   apply arith
  apply simp
  apply (rule_tac f = "%n. bl ! n" in arg_cong) 
  apply arith
  done
  
lemma nth_bin_to_bl: "n < m ==> (bin_to_bl m w) ! n = bin_nth w (m - Suc n)"
  unfolding bin_to_bl_def by (simp add : nth_bin_to_bl_aux)

lemma bl_to_bin_lt2p_aux [rule_format] : 
  "ALL w. bl_to_bin_aux w bs < (w + 1) * (2 ^ length bs)"
  apply (induct "bs")
   apply clarsimp
  apply clarsimp
  apply safe
   apply (erule allE, erule xtr8 [rotated],
          simp add: Bit_def ring_simps cong add : number_of_False_cong)+
  done

lemma bl_to_bin_lt2p: "bl_to_bin bs < (2 ^ length bs)"
  apply (unfold bl_to_bin_def)
  apply (rule xtr1)
   prefer 2
   apply (rule bl_to_bin_lt2p_aux)
  apply simp
  done

lemma bl_to_bin_ge2p_aux [rule_format] : 
  "ALL w. bl_to_bin_aux w bs >= w * (2 ^ length bs)"
  apply (induct bs)
   apply clarsimp
  apply clarsimp
  apply safe
   apply (erule allE, erule less_eq_less.order_trans [rotated],
          simp add: Bit_def ring_simps cong add : number_of_False_cong)+
  done

lemma bl_to_bin_ge0: "bl_to_bin bs >= 0"
  apply (unfold bl_to_bin_def)
  apply (rule xtr4)
   apply (rule bl_to_bin_ge2p_aux)
  apply simp
  done

lemma butlast_rest_bin: 
  "butlast (bin_to_bl n w) = bin_to_bl (n - 1) (bin_rest w)"
  apply (unfold bin_to_bl_def)
  apply (cases w rule: bin_exhaust)
  apply (cases n, clarsimp)
  apply clarsimp
  apply (auto simp add: bin_to_bl_aux_alt)
  done

lemmas butlast_bin_rest = butlast_rest_bin
  [where w="bl_to_bin ?bl" and n="length ?bl", simplified]

lemma butlast_rest_bl2bin_aux [rule_format] :
  "ALL w. bl ~= [] --> 
    bl_to_bin_aux w (butlast bl) = bin_rest (bl_to_bin_aux w bl)"
  by (induct bl) auto
  
lemma butlast_rest_bl2bin: 
  "bl_to_bin (butlast bl) = bin_rest (bl_to_bin bl)"
  apply (unfold bl_to_bin_def)
  apply (cases bl)
   apply (auto simp add: butlast_rest_bl2bin_aux)
  done

lemma trunc_bl2bin_aux [rule_format] : 
  "ALL w. bintrunc m (bl_to_bin_aux w bl) = 
    bl_to_bin_aux (bintrunc (m - length bl) w) (drop (length bl - m) bl)"
  apply (induct_tac bl)
   apply clarsimp
  apply clarsimp
  apply safe
   apply (case_tac "m - size list")
    apply (simp add : diff_is_0_eq [THEN iffD1, THEN Suc_diff_le])
   apply simp
   apply (rule_tac f = "%nat. bl_to_bin_aux (bintrunc nat w BIT bit.B1) list" 
                   in arg_cong) 
   apply simp
  apply (case_tac "m - size list")
   apply (simp add: diff_is_0_eq [THEN iffD1, THEN Suc_diff_le])
  apply simp
  apply (rule_tac f = "%nat. bl_to_bin_aux (bintrunc nat w BIT bit.B0) list" 
                  in arg_cong) 
  apply simp
  done

lemma trunc_bl2bin: 
  "bintrunc m (bl_to_bin bl) = bl_to_bin (drop (length bl - m) bl)"
  unfolding bl_to_bin_def by (simp add : trunc_bl2bin_aux)
  
lemmas trunc_bl2bin_len [simp] =
  trunc_bl2bin [of "length bl" bl, simplified, standard]  

lemma bl2bin_drop: 
  "bl_to_bin (drop k bl) = bintrunc (length bl - k) (bl_to_bin bl)"
  apply (rule trans)
   prefer 2
   apply (rule trunc_bl2bin [symmetric])
  apply (cases "k <= length bl")
   apply auto
  done

lemma nth_rest_power_bin [rule_format] :
  "ALL n. bin_nth ((bin_rest ^ k) w) n = bin_nth w (n + k)"
  apply (induct k, clarsimp)
  apply clarsimp
  apply (simp only: bin_nth.Suc [symmetric] add_Suc)
  done

lemma take_rest_power_bin:
  "m <= n ==> take m (bin_to_bl n w) = bin_to_bl m ((bin_rest ^ (n - m)) w)" 
  apply (rule nth_equalityI)
   apply simp
  apply (clarsimp simp add: nth_bin_to_bl nth_rest_power_bin)
  done

lemma hd_butlast: "size xs > 1 ==> hd (butlast xs) = hd xs"
  by (cases xs) auto

lemma last_bin_last' [rule_format] : 
  "ALL w. size xs > 0 --> last xs = (bin_last (bl_to_bin_aux w xs) = bit.B1)" 
  by (induct xs) auto

lemma last_bin_last: 
  "size xs > 0 ==> last xs = (bin_last (bl_to_bin xs) = bit.B1)" 
  unfolding bl_to_bin_def by (erule last_bin_last')
  
lemma bin_last_last: 
  "bin_last w = (if last (bin_to_bl (Suc n) w) then bit.B1 else bit.B0)" 
  apply (unfold bin_to_bl_def)
  apply simp
  apply (auto simp add: bin_to_bl_aux_alt)
  done

(** links between bit-wise operations and operations on bool lists **)
    
lemma app2_Nil [simp]: "app2 f [] ys = []"
  unfolding app2_def by auto

lemma app2_Cons [simp]:
  "app2 f (x # xs) (y # ys) = f x y # app2 f xs ys"
  unfolding app2_def by auto

lemma bl_xor_aux_bin [rule_format] : "ALL v w bs cs. 
    app2 (%x y. x ~= y) (bin_to_bl_aux n v bs) (bin_to_bl_aux n w cs) = 
    bin_to_bl_aux n (int_xor v w) (app2 (%x y. x ~= y) bs cs)"
  apply (induct_tac n)
   apply safe
   apply simp
  apply (case_tac v rule: bin_exhaust)
  apply (case_tac w rule: bin_exhaust)
  apply clarsimp
  apply (case_tac b)
  apply (case_tac ba, safe, simp_all)+
  done
    
lemma bl_or_aux_bin [rule_format] : "ALL v w bs cs. 
    app2 (op | ) (bin_to_bl_aux n v bs) (bin_to_bl_aux n w cs) = 
    bin_to_bl_aux n (int_or v w) (app2 (op | ) bs cs)" 
  apply (induct_tac n)
   apply safe
   apply simp
  apply (case_tac v rule: bin_exhaust)
  apply (case_tac w rule: bin_exhaust)
  apply clarsimp
  apply (case_tac b)
  apply (case_tac ba, safe, simp_all)+
  done
    
lemma bl_and_aux_bin [rule_format] : "ALL v w bs cs. 
    app2 (op & ) (bin_to_bl_aux n v bs) (bin_to_bl_aux n w cs) = 
    bin_to_bl_aux n (int_and v w) (app2 (op & ) bs cs)" 
  apply (induct_tac n)
   apply safe
   apply simp
  apply (case_tac v rule: bin_exhaust)
  apply (case_tac w rule: bin_exhaust)
  apply clarsimp
  apply (case_tac b)
  apply (case_tac ba, safe, simp_all)+
  done
    
lemma bl_not_aux_bin [rule_format] : 
  "ALL w cs. map Not (bin_to_bl_aux n w cs) = 
    bin_to_bl_aux n (int_not w) (map Not cs)"
  apply (induct n)
   apply clarsimp
  apply clarsimp
  apply (case_tac w rule: bin_exhaust)
  apply (case_tac b)
   apply auto
  done

lemmas bl_not_bin = bl_not_aux_bin
  [where cs = "[]", unfolded bin_to_bl_def [symmetric] map.simps]

lemmas bl_and_bin = bl_and_aux_bin [where bs="[]" and cs="[]", 
                                    unfolded app2_Nil, folded bin_to_bl_def]

lemmas bl_or_bin = bl_or_aux_bin [where bs="[]" and cs="[]", 
                                  unfolded app2_Nil, folded bin_to_bl_def]

lemmas bl_xor_bin = bl_xor_aux_bin [where bs="[]" and cs="[]", 
                                    unfolded app2_Nil, folded bin_to_bl_def]

lemma drop_bin2bl_aux [rule_format] : 
  "ALL m bin bs. drop m (bin_to_bl_aux n bin bs) = 
    bin_to_bl_aux (n - m) bin (drop (m - n) bs)"
  apply (induct n, clarsimp)
  apply clarsimp
  apply (case_tac bin rule: bin_exhaust)
  apply (case_tac "m <= n", simp)
  apply (case_tac "m - n", simp)
  apply simp
  apply (rule_tac f = "%nat. drop nat bs" in arg_cong) 
  apply simp
  done

lemma drop_bin2bl: "drop m (bin_to_bl n bin) = bin_to_bl (n - m) bin"
  unfolding bin_to_bl_def by (simp add : drop_bin2bl_aux)

lemma take_bin2bl_lem1 [rule_format] : 
  "ALL w bs. take m (bin_to_bl_aux m w bs) = bin_to_bl m w"
  apply (induct m, clarsimp)
  apply clarsimp
  apply (simp add: bin_to_bl_aux_alt)
  apply (simp add: bin_to_bl_def)
  apply (simp add: bin_to_bl_aux_alt)
  done

lemma take_bin2bl_lem [rule_format] : 
  "ALL w bs. take m (bin_to_bl_aux (m + n) w bs) = 
    take m (bin_to_bl (m + n) w)"
  apply (induct n)
   apply clarify
   apply (simp_all (no_asm) add: bin_to_bl_def take_bin2bl_lem1)
  apply simp
  done

lemma bin_split_take [rule_format] : 
  "ALL b c. bin_split n c = (a, b) --> 
    bin_to_bl m a = take m (bin_to_bl (m + n) c)"
  apply (induct n)
   apply clarsimp
  apply (clarsimp simp: Let_def split: ls_splits)
  apply (simp add: bin_to_bl_def)
  apply (simp add: take_bin2bl_lem)
  done

lemma bin_split_take1: 
  "k = m + n ==> bin_split n c = (a, b) ==> 
    bin_to_bl m a = take m (bin_to_bl k c)"
  by (auto elim: bin_split_take)
  
lemma nth_takefill [rule_format] : "ALL m l. m < n --> 
    takefill fill n l ! m = (if m < length l then l ! m else fill)"
  apply (induct n, clarsimp)
  apply clarsimp
  apply (case_tac m)
   apply (simp split: list.split)
  apply clarsimp
  apply (erule allE)+
  apply (erule (1) impE)
  apply (simp split: list.split)
  done

lemma takefill_alt [rule_format] :
  "ALL l. takefill fill n l = take n l @ replicate (n - length l) fill"
  by (induct n) (auto split: list.split)

lemma takefill_replicate [simp]:
  "takefill fill n (replicate m fill) = replicate n fill"
  by (simp add : takefill_alt replicate_add [symmetric])

lemma takefill_le' [rule_format] :
  "ALL l n. n = m + k --> takefill x m (takefill x n l) = takefill x m l"
  by (induct m) (auto split: list.split)

lemma length_takefill [simp]: "length (takefill fill n l) = n"
  by (simp add : takefill_alt)

lemma take_takefill':
  "!!w n.  n = k + m ==> take k (takefill fill n w) = takefill fill k w"
  by (induct k) (auto split add : list.split) 

lemma drop_takefill:
  "!!w. drop k (takefill fill (m + k) w) = takefill fill m (drop k w)"
  by (induct k) (auto split add : list.split) 

lemma takefill_le [simp]:
  "m \<le> n \<Longrightarrow> takefill x m (takefill x n l) = takefill x m l"
  by (auto simp: le_iff_add takefill_le')

lemma take_takefill [simp]:
  "m \<le> n \<Longrightarrow> take m (takefill fill n w) = takefill fill m w"
  by (auto simp: le_iff_add take_takefill')
 
lemma takefill_append:
  "takefill fill (m + length xs) (xs @ w) = xs @ (takefill fill m w)"
  by (induct xs) auto

lemma takefill_same': 
  "l = length xs ==> takefill fill l xs = xs"
  by clarify (induct xs, auto)
 
lemmas takefill_same [simp] = takefill_same' [OF refl]

lemma takefill_bintrunc:
  "takefill False n bl = rev (bin_to_bl n (bl_to_bin (rev bl)))"
  apply (rule nth_equalityI)
   apply simp
  apply (clarsimp simp: nth_takefill nth_rev nth_bin_to_bl bin_nth_of_bl)
  done

lemma bl_bin_bl_rtf:
  "bin_to_bl n (bl_to_bin bl) = rev (takefill False n (rev bl))"
  by (simp add : takefill_bintrunc)
  
lemmas bl_bin_bl_rep_drop = 
  bl_bin_bl_rtf [simplified takefill_alt,
                 simplified, simplified rev_take, simplified]

lemma tf_rev:
  "n + k = m + length bl ==> takefill x m (rev (takefill y n bl)) = 
    rev (takefill y m (rev (takefill x k (rev bl))))"
  apply (rule nth_equalityI)
   apply (auto simp add: nth_takefill nth_rev)
  apply (rule_tac f = "%n. bl ! n" in arg_cong) 
  apply arith 
  done

lemma takefill_minus:
  "0 < n ==> takefill fill (Suc (n - 1)) w = takefill fill n w"
  by auto

lemmas takefill_Suc_cases = 
  list.cases [THEN takefill.Suc [THEN trans], standard]

lemmas takefill_Suc_Nil = takefill_Suc_cases (1)
lemmas takefill_Suc_Cons = takefill_Suc_cases (2)

lemmas takefill_minus_simps = takefill_Suc_cases [THEN [2] 
  takefill_minus [symmetric, THEN trans], standard]

lemmas takefill_pred_simps [simp] =
  takefill_minus_simps [where n="number_of bin", simplified nobm1, standard]

(* links with function bl_to_bin *)

lemma bl_to_bin_aux_cat: 
  "!!nv v. bl_to_bin_aux (bin_cat w nv v) bs = 
    bin_cat w (nv + length bs) (bl_to_bin_aux v bs)"
  apply (induct bs)
   apply simp
  apply (simp add: bin_cat_Suc_Bit [symmetric] del: bin_cat.simps)
  done

lemma bin_to_bl_aux_cat: 
  "!!w bs. bin_to_bl_aux (nv + nw) (bin_cat v nw w) bs = 
    bin_to_bl_aux nv v (bin_to_bl_aux nw w bs)"
  by (induct nw) auto 

lemmas bl_to_bin_aux_alt = 
  bl_to_bin_aux_cat [where nv = "0" and v = "Numeral.Pls", 
    simplified bl_to_bin_def [symmetric], simplified]

lemmas bin_to_bl_cat =
  bin_to_bl_aux_cat [where bs = "[]", folded bin_to_bl_def]

lemmas bl_to_bin_aux_app_cat = 
  trans [OF bl_to_bin_aux_append bl_to_bin_aux_alt]

lemmas bin_to_bl_aux_cat_app =
  trans [OF bin_to_bl_aux_cat bin_to_bl_aux_alt]

lemmas bl_to_bin_app_cat = bl_to_bin_aux_app_cat
  [where w = "Numeral.Pls", folded bl_to_bin_def]

lemmas bin_to_bl_cat_app = bin_to_bl_aux_cat_app
  [where bs = "[]", folded bin_to_bl_def]

(* bl_to_bin_app_cat_alt and bl_to_bin_app_cat are easily interderivable *)
lemma bl_to_bin_app_cat_alt: 
  "bin_cat (bl_to_bin cs) n w = bl_to_bin (cs @ bin_to_bl n w)"
  by (simp add : bl_to_bin_app_cat)

lemma mask_lem: "(bl_to_bin (True # replicate n False)) = 
    Numeral.succ (bl_to_bin (replicate n True))"
  apply (unfold bl_to_bin_def)
  apply (induct n)
   apply simp
  apply (simp only: Suc_eq_add_numeral_1 replicate_add
                    append_Cons [symmetric] bl_to_bin_aux_append)
  apply simp
  done

(* function bl_of_nth *)
lemma length_bl_of_nth [simp]: "length (bl_of_nth n f) = n"
  by (induct n)  auto

lemma nth_bl_of_nth [simp]:
  "m < n \<Longrightarrow> rev (bl_of_nth n f) ! m = f m"
  apply (induct n)
   apply simp
  apply (clarsimp simp add : nth_append)
  apply (rule_tac f = "f" in arg_cong) 
  apply simp
  done

lemma bl_of_nth_inj: 
  "(!!k. k < n ==> f k = g k) ==> bl_of_nth n f = bl_of_nth n g"
  by (induct n)  auto

lemma bl_of_nth_nth_le [rule_format] : "ALL xs. 
    length xs >= n --> bl_of_nth n (nth (rev xs)) = drop (length xs - n) xs";
  apply (induct n, clarsimp)
  apply clarsimp
  apply (rule trans [OF _ hd_Cons_tl])
   apply (frule Suc_le_lessD)
   apply (simp add: nth_rev trans [OF drop_Suc drop_tl, symmetric])
   apply (subst hd_drop_conv_nth)
     apply force
    apply simp_all
  apply (rule_tac f = "%n. drop n xs" in arg_cong) 
  apply simp
  done

lemmas bl_of_nth_nth [simp] = order_refl [THEN bl_of_nth_nth_le, simplified]

lemma size_rbl_pred: "length (rbl_pred bl) = length bl"
  by (induct bl) auto

lemma size_rbl_succ: "length (rbl_succ bl) = length bl"
  by (induct bl) auto

lemma size_rbl_add:
  "!!cl. length (rbl_add bl cl) = length bl"
  by (induct bl) (auto simp: Let_def size_rbl_succ)

lemma size_rbl_mult: 
  "!!cl. length (rbl_mult bl cl) = length bl"
  by (induct bl) (auto simp add : Let_def size_rbl_add)

lemmas rbl_sizes [simp] = 
  size_rbl_pred size_rbl_succ size_rbl_add size_rbl_mult

lemmas rbl_Nils =
  rbl_pred.Nil rbl_succ.Nil rbl_add.Nil rbl_mult.Nil

lemma rbl_pred: 
  "!!bin. rbl_pred (rev (bin_to_bl n bin)) = rev (bin_to_bl n (Numeral.pred bin))"
  apply (induct n, simp)
  apply (unfold bin_to_bl_def)
  apply clarsimp
  apply (case_tac bin rule: bin_exhaust)
  apply (case_tac b)
   apply (clarsimp simp: bin_to_bl_aux_alt)+
  done

lemma rbl_succ: 
  "!!bin. rbl_succ (rev (bin_to_bl n bin)) = rev (bin_to_bl n (Numeral.succ bin))"
  apply (induct n, simp)
  apply (unfold bin_to_bl_def)
  apply clarsimp
  apply (case_tac bin rule: bin_exhaust)
  apply (case_tac b)
   apply (clarsimp simp: bin_to_bl_aux_alt)+
  done

lemma rbl_add: 
  "!!bina binb. rbl_add (rev (bin_to_bl n bina)) (rev (bin_to_bl n binb)) = 
    rev (bin_to_bl n (bina + binb))"
  apply (induct n, simp)
  apply (unfold bin_to_bl_def)
  apply clarsimp
  apply (case_tac bina rule: bin_exhaust)
  apply (case_tac binb rule: bin_exhaust)
  apply (case_tac b)
   apply (case_tac [!] "ba")
     apply (auto simp: rbl_succ succ_def bin_to_bl_aux_alt Let_def add_ac)
  done

lemma rbl_add_app2: 
  "!!blb. length blb >= length bla ==> 
    rbl_add bla (blb @ blc) = rbl_add bla blb"
  apply (induct bla, simp)
  apply clarsimp
  apply (case_tac blb, clarsimp)
  apply (clarsimp simp: Let_def)
  done

lemma rbl_add_take2: 
  "!!blb. length blb >= length bla ==> 
    rbl_add bla (take (length bla) blb) = rbl_add bla blb"
  apply (induct bla, simp)
  apply clarsimp
  apply (case_tac blb, clarsimp)
  apply (clarsimp simp: Let_def)
  done

lemma rbl_add_long: 
  "m >= n ==> rbl_add (rev (bin_to_bl n bina)) (rev (bin_to_bl m binb)) = 
    rev (bin_to_bl n (bina + binb))"
  apply (rule box_equals [OF _ rbl_add_take2 rbl_add])
   apply (rule_tac f = "rbl_add (rev (bin_to_bl n bina))" in arg_cong) 
   apply (rule rev_swap [THEN iffD1])
   apply (simp add: rev_take drop_bin2bl)
  apply simp
  done

lemma rbl_mult_app2:
  "!!blb. length blb >= length bla ==> 
    rbl_mult bla (blb @ blc) = rbl_mult bla blb"
  apply (induct bla, simp)
  apply clarsimp
  apply (case_tac blb, clarsimp)
  apply (clarsimp simp: Let_def rbl_add_app2)
  done

lemma rbl_mult_take2: 
  "length blb >= length bla ==> 
    rbl_mult bla (take (length bla) blb) = rbl_mult bla blb"
  apply (rule trans)
   apply (rule rbl_mult_app2 [symmetric])
   apply simp
  apply (rule_tac f = "rbl_mult bla" in arg_cong) 
  apply (rule append_take_drop_id)
  done
    
lemma rbl_mult_gt1: 
  "m >= length bl ==> rbl_mult bl (rev (bin_to_bl m binb)) = 
    rbl_mult bl (rev (bin_to_bl (length bl) binb))"
  apply (rule trans)
   apply (rule rbl_mult_take2 [symmetric])
   apply simp_all
  apply (rule_tac f = "rbl_mult bl" in arg_cong) 
  apply (rule rev_swap [THEN iffD1])
  apply (simp add: rev_take drop_bin2bl)
  done
    
lemma rbl_mult_gt: 
  "m > n ==> rbl_mult (rev (bin_to_bl n bina)) (rev (bin_to_bl m binb)) = 
    rbl_mult (rev (bin_to_bl n bina)) (rev (bin_to_bl n binb))"
  by (auto intro: trans [OF rbl_mult_gt1])
  
lemmas rbl_mult_Suc = lessI [THEN rbl_mult_gt]

lemma rbbl_Cons: 
  "b # rev (bin_to_bl n x) = rev (bin_to_bl (Suc n) (x BIT If b bit.B1 bit.B0))"
  apply (unfold bin_to_bl_def)
  apply simp
  apply (simp add: bin_to_bl_aux_alt)
  done
  
lemma rbl_mult: "!!bina binb. 
    rbl_mult (rev (bin_to_bl n bina)) (rev (bin_to_bl n binb)) = 
    rev (bin_to_bl n (bina * binb))"
  apply (induct n)
   apply simp
  apply (unfold bin_to_bl_def)
  apply clarsimp
  apply (case_tac bina rule: bin_exhaust)
  apply (case_tac binb rule: bin_exhaust)
  apply (case_tac b)
   apply (case_tac [!] "ba")
     apply (auto simp: bin_to_bl_aux_alt Let_def)
     apply (auto simp: rbbl_Cons rbl_mult_Suc rbl_add)
  done

lemma rbl_add_split: 
  "P (rbl_add (y # ys) (x # xs)) = 
    (ALL ws. length ws = length ys --> ws = rbl_add ys xs --> 
    (y --> ((x --> P (False # rbl_succ ws)) & (~ x -->  P (True # ws)))) & \ 
    (~ y --> P (x # ws)))"
  apply (auto simp add: Let_def)
   apply (case_tac [!] "y")
     apply auto
  done

lemma rbl_mult_split: 
  "P (rbl_mult (y # ys) xs) = 
    (ALL ws. length ws = Suc (length ys) --> ws = False # rbl_mult ys xs --> 
    (y --> P (rbl_add ws xs)) & (~ y -->  P ws))"
  by (clarsimp simp add : Let_def)
  
lemma and_len: "xs = ys ==> xs = ys & length xs = length ys"
  by auto

lemma size_if: "size (if p then xs else ys) = (if p then size xs else size ys)"
  by auto

lemma tl_if: "tl (if p then xs else ys) = (if p then tl xs else tl ys)"
  by auto

lemma hd_if: "hd (if p then xs else ys) = (if p then hd xs else hd ys)"
  by auto

lemma if_Not_x: "(if p then ~ x else x) = (p = (~ x))"
  by auto

lemma if_x_Not: "(if p then x else ~ x) = (p = x)"
  by auto

lemma if_same_and: "(If p x y & If p u v) = (if p then x & u else y & v)"
  by auto

lemma if_same_eq: "(If p x y  = (If p u v)) = (if p then x = (u) else y = (v))"
  by auto

lemma if_same_eq_not:
  "(If p x y  = (~ If p u v)) = (if p then x = (~u) else y = (~v))"
  by auto

(* note - if_Cons can cause blowup in the size, if p is complex,
  so make a simproc *)
lemma if_Cons: "(if p then x # xs else y # ys) = If p x y # If p xs ys"
  by auto

lemma if_single:
  "(if xc then [xab] else [an]) = [if xc then xab else an]"
  by auto

lemma if_bool_simps:
  "If p True y = (p | y) & If p False y = (~p & y) & 
    If p y True = (p --> y) & If p y False = (p & y)"
  by auto

lemmas if_simps = if_x_Not if_Not_x if_cancel if_True if_False if_bool_simps

lemmas seqr = eq_reflection [where x = "size ?w"]

lemmas tl_Nil = tl.simps (1)
lemmas tl_Cons = tl.simps (2)


section "Repeated splitting or concatenation"

lemma sclem:
  "size (concat (map (bin_to_bl n) xs)) = length xs * n"
  by (induct xs) auto

lemma bin_cat_foldl_lem [rule_format] :
  "ALL x. foldl (%u. bin_cat u n) x xs = 
    bin_cat x (size xs * n) (foldl (%u. bin_cat u n) y xs)"
  apply (induct xs)
   apply simp
  apply clarify
  apply (simp (no_asm))
  apply (frule asm_rl)
  apply (drule spec)
  apply (erule trans)
  apply (drule_tac x = "bin_cat y n a" in spec) 
  apply (simp add : bin_cat_assoc_sym min_def)
  done

lemma bin_rcat_bl:
  "(bin_rcat n wl) = bl_to_bin (concat (map (bin_to_bl n) wl))"
  apply (unfold bin_rcat_def)
  apply (rule sym)
  apply (induct wl)
   apply (auto simp add : bl_to_bin_append)
  apply (simp add : bl_to_bin_aux_alt sclem)
  apply (simp add : bin_cat_foldl_lem [symmetric])
  done

lemmas bin_rsplit_aux_simps = bin_rsplit_aux.simps bin_rsplitl_aux.simps
lemmas rsplit_aux_simps = bin_rsplit_aux_simps

lemmas th_if_simp1 = split_if [where P = "op = ?l",
  THEN iffD1, THEN conjunct1, THEN mp, standard]
lemmas th_if_simp2 = split_if [where P = "op = ?l",
  THEN iffD1, THEN conjunct2, THEN mp, standard]

lemmas rsplit_aux_simp1s = rsplit_aux_simps [THEN th_if_simp1]

lemmas rsplit_aux_simp2ls = rsplit_aux_simps [THEN th_if_simp2]
(* these safe to [simp add] as require calculating m - n *)
lemmas bin_rsplit_aux_simp2s [simp] = rsplit_aux_simp2ls [unfolded Let_def]
lemmas rbscl = bin_rsplit_aux_simp2s (2)

lemmas rsplit_aux_0_simps [simp] = 
  rsplit_aux_simp1s [OF disjI1] rsplit_aux_simp1s [OF disjI2]

lemma bin_rsplit_aux_append:
  "bin_rsplit_aux (n, bs @ cs, m, c) = bin_rsplit_aux (n, bs, m, c) @ cs"
  apply (rule_tac u=n and v=bs and w=m and x=c in bin_rsplit_aux.induct)
  apply (subst bin_rsplit_aux.simps)
  apply (subst bin_rsplit_aux.simps)
  apply (clarsimp split: ls_splits)
  done

lemma bin_rsplitl_aux_append:
  "bin_rsplitl_aux (n, bs @ cs, m, c) = bin_rsplitl_aux (n, bs, m, c) @ cs"
  apply (rule_tac u=n and v=bs and w=m and x=c in bin_rsplitl_aux.induct)
  apply (subst bin_rsplitl_aux.simps)
  apply (subst bin_rsplitl_aux.simps)
  apply (clarsimp split: ls_splits)
  done

lemmas rsplit_aux_apps [where bs = "[]"] =
  bin_rsplit_aux_append bin_rsplitl_aux_append

lemmas rsplit_def_auxs = bin_rsplit_def bin_rsplitl_def

lemmas rsplit_aux_alts = rsplit_aux_apps 
  [unfolded append_Nil rsplit_def_auxs [symmetric]]

lemma bin_split_minus: "0 < n ==> bin_split (Suc (n - 1)) w = bin_split n w"
  by auto

lemmas bin_split_minus_simp =
  bin_split.Suc [THEN [2] bin_split_minus [symmetric, THEN trans], standard]

lemma bin_split_pred_simp [simp]: 
  "(0::nat) < number_of bin \<Longrightarrow>
  bin_split (number_of bin) w =
  (let (w1, w2) = bin_split (number_of (Numeral.pred bin)) (bin_rest w)
   in (w1, w2 BIT bin_last w))" 
  by (simp only: nobm1 bin_split_minus_simp)

declare bin_split_pred_simp [simp]

lemma bin_rsplit_aux_simp_alt:
  "bin_rsplit_aux (n, bs, m, c) =
   (if m = 0 \<or> n = 0 
   then bs
   else let (a, b) = bin_split n c in bin_rsplit n (m - n, a) @ b # bs)"
  apply (rule trans)
   apply (subst bin_rsplit_aux.simps, rule refl)
  apply (simp add: rsplit_aux_alts)
  done

lemmas bin_rsplit_simp_alt = 
  trans [OF bin_rsplit_def [THEN meta_eq_to_obj_eq]
            bin_rsplit_aux_simp_alt, standard]

lemmas bthrs = bin_rsplit_simp_alt [THEN [2] trans]

lemma bin_rsplit_size_sign' [rule_format] : 
  "n > 0 ==> (ALL nw w. rev sw = bin_rsplit n (nw, w) --> 
    (ALL v: set sw. bintrunc n v = v))"
  apply (induct sw)
   apply clarsimp
  apply clarsimp
  apply (drule bthrs)
  apply (simp (no_asm_use) add: Let_def split: ls_splits)
  apply clarify
  apply (erule impE, rule exI, erule exI)
  apply (drule split_bintrunc)
  apply simp
  done

lemmas bin_rsplit_size_sign = bin_rsplit_size_sign' [OF asm_rl 
  rev_rev_ident [THEN trans] set_rev [THEN equalityD2 [THEN subsetD]],
  standard]

lemma bin_nth_rsplit [rule_format] :
  "n > 0 ==> m < n ==> (ALL w k nw. rev sw = bin_rsplit n (nw, w) --> 
       k < size sw --> bin_nth (sw ! k) m = bin_nth w (k * n + m))"
  apply (induct sw)
   apply clarsimp
  apply clarsimp
  apply (drule bthrs)
  apply (simp (no_asm_use) add: Let_def split: ls_splits)
  apply clarify
  apply (erule allE, erule impE, erule exI)
  apply (case_tac k)
   apply clarsimp   
   prefer 2
   apply clarsimp
   apply (erule allE)
   apply (erule (1) impE)
   apply (drule bin_nth_split, erule conjE, erule allE,
          erule trans, simp add : add_ac)+
  done

lemma bin_rsplit_all:
  "0 < nw ==> nw <= n ==> bin_rsplit n (nw, w) = [bintrunc n w]"
  unfolding bin_rsplit_def
  by (clarsimp dest!: split_bintrunc simp: rsplit_aux_simp2ls split: ls_splits)

lemma bin_rsplit_l [rule_format] :
  "ALL bin. bin_rsplitl n (m, bin) = bin_rsplit n (m, bintrunc m bin)"
  apply (rule_tac a = "m" in wf_less_than [THEN wf_induct])
  apply (simp (no_asm) add : bin_rsplitl_def bin_rsplit_def)
  apply (rule allI)
  apply (subst bin_rsplitl_aux.simps)
  apply (subst bin_rsplit_aux.simps)
  apply (clarsimp simp: rsplit_aux_alts Let_def split: ls_splits)
  apply (drule bin_split_trunc)
  apply (drule sym [THEN trans], assumption)
  apply fast
  done
    
lemma bin_rsplit_rcat [rule_format] :
  "n > 0 --> bin_rsplit n (n * size ws, bin_rcat n ws) = map (bintrunc n) ws"
  apply (unfold bin_rsplit_def bin_rcat_def)
  apply (rule_tac xs = "ws" in rev_induct)
   apply clarsimp
  apply clarsimp
  apply (clarsimp simp add: bin_split_cat rsplit_aux_alts)
  done

lemma bin_rsplit_aux_len_le [rule_format] :
  "ALL ws m. n > 0 --> ws = bin_rsplit_aux (n, bs, nw, w) --> 
    (length ws <= m) = (nw + length bs * n <= m * n)"
  apply (rule_tac u=n and v=bs and w=nw and x=w in bin_rsplit_aux.induct)
  apply (subst bin_rsplit_aux.simps)
  apply (clarsimp simp: Let_def split: ls_splits)
  apply (erule lrlem)
  done

lemma bin_rsplit_len_le: 
  "n > 0 --> ws = bin_rsplit n (nw, w) --> (length ws <= m) = (nw <= m * n)"
  unfolding bin_rsplit_def by (clarsimp simp add : bin_rsplit_aux_len_le)
 
lemma bin_rsplit_aux_len [rule_format] :
  "0 < n --> length (bin_rsplit_aux (n, cs, nw, w)) = 
    (nw + n - 1) div n + length cs"
  apply (rule_tac u=n and v=cs and w=nw and x=w in bin_rsplit_aux.induct)
  apply (subst bin_rsplit_aux.simps)
  apply (clarsimp simp: Let_def split: ls_splits)
  apply (erule thin_rl)
  apply (case_tac "m <= n")
   prefer 2
   apply (simp add: div_add_self2 [symmetric])
  apply (case_tac m, clarsimp)
  apply (simp add: div_add_self2)
  done

lemma bin_rsplit_len: 
  "0 < n ==> length (bin_rsplit n (nw, w)) = (nw + n - 1) div n"
  unfolding bin_rsplit_def by (clarsimp simp add : bin_rsplit_aux_len)

lemma bin_rsplit_aux_len_indep [rule_format] :
  "0 < n ==> (ALL v bs. length bs = length cs --> 
    length (bin_rsplit_aux (n, bs, nw, v)) = 
    length (bin_rsplit_aux (n, cs, nw, w)))"
  apply (rule_tac u=n and v=cs and w=nw and x=w in bin_rsplit_aux.induct)
  apply clarsimp
  apply (simp (no_asm_simp) add: bin_rsplit_aux_simp_alt Let_def 
                            split: ls_splits)
  apply clarify 
  apply (erule allE)+
  apply (erule impE)
   apply (fast elim!: sym)
  apply (simp (no_asm_use) add: rsplit_aux_alts)
  apply (erule impE)
  apply (rule_tac x="ba # bs" in exI)
  apply auto
  done

lemma bin_rsplit_len_indep: 
  "0 < n ==> length (bin_rsplit n (nw, v)) = length (bin_rsplit n (nw, w))"
  apply (unfold bin_rsplit_def)
  apply (erule bin_rsplit_aux_len_indep)
  apply (rule refl)
  done

end

