(*  Title:      HOL/BNF/Examples/Misc_Data.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012, 2013

Miscellaneous datatype declarations.
*)

header {* Miscellaneous Datatype Declarations *}

theory Misc_Data
imports "../BNF"
begin

datatype_new simple = X1 | X2 | X3 | X4

datatype_new simple' = X1' unit | X2' unit | X3' unit | X4' unit

datatype_new simple'' = X1'' nat int | X2''

datatype_new 'a mylist = MyNil | MyCons 'a "'a mylist"

datatype_new ('b, 'c, 'd, 'e) some_passive =
  SP1 "('b, 'c, 'd, 'e) some_passive" | SP2 'b | SP3 'c | SP4 'd | SP5 'e

datatype_new hfset = HFset "hfset fset"

datatype_new lambda =
  Var string |
  App lambda lambda |
  Abs string lambda |
  Let "(string \<times> lambda) fset" lambda

datatype_new 'a par_lambda =
  PVar 'a |
  PApp "'a par_lambda" "'a par_lambda" |
  PAbs 'a "'a par_lambda" |
  PLet "('a \<times> 'a par_lambda) fset" "'a par_lambda"

(*
  ('a, 'b1, 'b2) F1 = 'a * 'b1 + 'a * 'b2
  ('a, 'b1, 'b2) F2 = unit + 'b1 * 'b2
*)

datatype_new 'a I1 = I11 'a "'a I1" | I12 'a "'a I2"
and 'a I2 = I21 | I22 "'a I1" "'a I2"

datatype_new 'a tree = TEmpty | TNode 'a "'a forest"
and 'a forest = FNil | FCons "'a tree" "'a forest"

datatype_new 'a tree' = TEmpty' | TNode' "'a branch" "'a branch"
and 'a branch = Branch 'a "'a tree'"

datatype_new ('a, 'b) exp = Term "('a, 'b) trm" | Sum "('a, 'b) trm" "('a, 'b) exp"
and ('a, 'b) trm = Factor "('a, 'b) factor" | Prod "('a, 'b) factor" "('a, 'b) trm"
and ('a, 'b) factor = C 'a | V 'b | Paren "('a, 'b) exp"

datatype_new ('a, 'b, 'c) some_killing =
  SK "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) some_killing + ('a, 'b, 'c) in_here"
and ('a, 'b, 'c) in_here =
  IH1 'b 'a | IH2 'c

datatype_new 'b nofail1 = NF11 "'b nofail1" 'b | NF12 'b
datatype_new 'b nofail2 = NF2 "('b nofail2 \<times> 'b \<times> 'b nofail2 \<times> 'b) list"
datatype_new 'b nofail3 = NF3 'b "('b nofail3 \<times> 'b \<times> 'b nofail3 \<times> 'b) fset"
datatype_new 'b nofail4 = NF4 "('b nofail4 \<times> ('b nofail4 \<times> 'b \<times> 'b nofail4 \<times> 'b) fset) list"

(*
datatype_new 'b fail = F "'b fail" 'b "'b fail" "'b list"
datatype_new 'b fail = F "'b fail" 'b "'b fail" 'b
datatype_new 'b fail = F1 "'b fail" 'b | F2 "'b fail"
datatype_new 'b fail = F "'b fail" 'b
*)

datatype_new l1 = L1 "l2 list"
and l2 = L21 "l1 fset" | L22 l2

datatype_new kk1 = KK1 kk2
and kk2 = KK2 kk3
and kk3 = KK3 "kk1 list"

datatype_new t1 = T11 t3 | T12 t2
and t2 = T2 t1
and t3 = T3

datatype_new t1' = T11' t2' | T12' t3'
and t2' = T2' t1'
and t3' = T3'

(*
datatype_new fail1 = F1 fail2
and fail2 = F2 fail3
and fail3 = F3 fail1

datatype_new fail1 = F1 "fail2 list" fail2
and fail2 = F2 "fail2 fset" fail3
and fail3 = F3 fail1

datatype_new fail1 = F1 "fail2 list" fail2
and fail2 = F2 "fail1 fset" fail1
*)

(* SLOW
datatype_new ('a, 'c) D1 = A1 "('a, 'c) D2" | B1 "'a list"
and ('a, 'c) D2 = A2 "('a, 'c) D3" | B2 "'c list"
and ('a, 'c) D3 = A3 "('a, 'c) D3" | B3 "('a, 'c) D4" | C3 "('a, 'c) D4" "('a, 'c) D5"
and ('a, 'c) D4 = A4 "('a, 'c) D5" | B4 "'a list list list"
and ('a, 'c) D5 = A5 "('a, 'c) D6"
and ('a, 'c) D6 = A6 "('a, 'c) D7"
and ('a, 'c) D7 = A7 "('a, 'c) D8"
and ('a, 'c) D8 = A8 "('a, 'c) D1 list"

(*time comparison*)
datatype ('a, 'c) D1' = A1' "('a, 'c) D2'" | B1' "'a list"
     and ('a, 'c) D2' = A2' "('a, 'c) D3'" | B2' "'c list"
     and ('a, 'c) D3' = A3' "('a, 'c) D3'" | B3' "('a, 'c) D4'" | C3' "('a, 'c) D4'" "('a, 'c) D5'"
     and ('a, 'c) D4' = A4' "('a, 'c) D5'" | B4' "'a list list list"
     and ('a, 'c) D5' = A5' "('a, 'c) D6'"
     and ('a, 'c) D6' = A6' "('a, 'c) D7'"
     and ('a, 'c) D7' = A7' "('a, 'c) D8'"
     and ('a, 'c) D8' = A8' "('a, 'c) D1' list"
*)

(* fail:
datatype_new tt1 = TT11 tt2 tt3 | TT12 tt2 tt4
and tt2 = TT2
and tt3 = TT3 tt4
and tt4 = TT4 tt1
*)

datatype_new k1 = K11 k2 k3 | K12 k2 k4
and k2 = K2
and k3 = K3 k4
and k4 = K4

datatype_new tt1 = TT11 tt3 tt2 | TT12 tt2 tt4
and tt2 = TT2
and tt3 = TT3 tt1
and tt4 = TT4

(* SLOW
datatype_new s1 = S11 s2 s3 s4 | S12 s3 | S13 s2 s6 | S14 s4 s2 | S15 s2 s2
and s2 = S21 s7 s5 | S22 s5 s4 s6
and s3 = S31 s1 s7 s2 | S32 s3 s3 | S33 s4 s5
and s4 = S4 s5
and s5 = S5
and s6 = S61 s6 | S62 s1 s2 | S63 s6
and s7 = S71 s8 | S72 s5
and s8 = S8 nat
*)

datatype_new 'a deadbar = DeadBar "'a \<Rightarrow> 'a"
datatype_new 'a deadbar_option = DeadBarOption "'a option \<Rightarrow> 'a option"
datatype_new ('a, 'b) bar = Bar "'b \<Rightarrow> 'a"
datatype_new ('a, 'b, 'c, 'd) foo = Foo "'d + 'b \<Rightarrow> 'c + 'a"

datatype_new 'a dead_foo = A
datatype_new ('a, 'b) use_dead_foo = Y "'a" "'b dead_foo"

datatype_new d1 = D
datatype_new d1' = is_D: D

datatype_new d2 = D nat
datatype_new d2' = is_D: D nat

datatype_new d3 = D | E
datatype_new d3' = D | is_E: E
datatype_new d3'' = is_D: D | E
datatype_new d3''' = is_D: D | is_E: E

datatype_new d4 = D nat | E
datatype_new d4' = D nat | is_E: E
datatype_new d4'' = is_D: D nat | E
datatype_new d4''' = is_D: D nat | is_E: E

datatype_new d5 = D nat | E int
datatype_new d5' = D nat | is_E: E int
datatype_new d5'' = is_D: D nat | E int
datatype_new d5''' = is_D: D nat | is_E: E int

end
