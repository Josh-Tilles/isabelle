(* AUTOMATICALLY GENERATED, DO NOT EDIT! *)

theory HOL4Base imports "../HOL4Compat" "../HOL4Syntax" begin

;setup_theory bool

definition ARB :: "'a" where 
  "ARB == SOME x::'a::type. True"

lemma ARB_DEF: "ARB = (SOME x::'a::type. True)"
  by (import bool ARB_DEF)

definition IN :: "'a => ('a => bool) => bool" where 
  "IN == %(x::'a::type) f::'a::type => bool. f x"

lemma IN_DEF: "IN = (%(x::'a::type) f::'a::type => bool. f x)"
  by (import bool IN_DEF)

definition RES_FORALL :: "('a => bool) => ('a => bool) => bool" where 
  "RES_FORALL ==
%(p::'a::type => bool) m::'a::type => bool. ALL x::'a::type. IN x p --> m x"

lemma RES_FORALL_DEF: "RES_FORALL =
(%(p::'a::type => bool) m::'a::type => bool.
    ALL x::'a::type. IN x p --> m x)"
  by (import bool RES_FORALL_DEF)

definition RES_EXISTS :: "('a => bool) => ('a => bool) => bool" where 
  "RES_EXISTS ==
%(p::'a::type => bool) m::'a::type => bool. EX x::'a::type. IN x p & m x"

lemma RES_EXISTS_DEF: "RES_EXISTS =
(%(p::'a::type => bool) m::'a::type => bool. EX x::'a::type. IN x p & m x)"
  by (import bool RES_EXISTS_DEF)

definition RES_EXISTS_UNIQUE :: "('a => bool) => ('a => bool) => bool" where 
  "RES_EXISTS_UNIQUE ==
%(p::'a::type => bool) m::'a::type => bool.
   RES_EXISTS p m &
   RES_FORALL p
    (%x::'a::type. RES_FORALL p (%y::'a::type. m x & m y --> x = y))"

lemma RES_EXISTS_UNIQUE_DEF: "RES_EXISTS_UNIQUE =
(%(p::'a::type => bool) m::'a::type => bool.
    RES_EXISTS p m &
    RES_FORALL p
     (%x::'a::type. RES_FORALL p (%y::'a::type. m x & m y --> x = y)))"
  by (import bool RES_EXISTS_UNIQUE_DEF)

definition RES_SELECT :: "('a => bool) => ('a => bool) => 'a" where 
  "RES_SELECT ==
%(p::'a::type => bool) m::'a::type => bool. SOME x::'a::type. IN x p & m x"

lemma RES_SELECT_DEF: "RES_SELECT =
(%(p::'a::type => bool) m::'a::type => bool. SOME x::'a::type. IN x p & m x)"
  by (import bool RES_SELECT_DEF)

lemma EXCLUDED_MIDDLE: "ALL t::bool. t | ~ t"
  by (import bool EXCLUDED_MIDDLE)

lemma FORALL_THM: "All (f::'a::type => bool) = All f"
  by (import bool FORALL_THM)

lemma EXISTS_THM: "Ex (f::'a::type => bool) = Ex f"
  by (import bool EXISTS_THM)

lemma F_IMP: "ALL t::bool. ~ t --> t --> False"
  by (import bool F_IMP)

lemma NOT_AND: "~ ((t::bool) & ~ t)"
  by (import bool NOT_AND)

lemma AND_CLAUSES: "ALL t::bool.
   (True & t) = t &
   (t & True) = t & (False & t) = False & (t & False) = False & (t & t) = t"
  by (import bool AND_CLAUSES)

lemma OR_CLAUSES: "ALL t::bool.
   (True | t) = True &
   (t | True) = True & (False | t) = t & (t | False) = t & (t | t) = t"
  by (import bool OR_CLAUSES)

lemma IMP_CLAUSES: "ALL t::bool.
   (True --> t) = t &
   (t --> True) = True &
   (False --> t) = True & (t --> t) = True & (t --> False) = (~ t)"
  by (import bool IMP_CLAUSES)

lemma NOT_CLAUSES: "(ALL t::bool. (~ ~ t) = t) & (~ True) = False & (~ False) = True"
  by (import bool NOT_CLAUSES)

lemma BOOL_EQ_DISTINCT: "True ~= False & False ~= True"
  by (import bool BOOL_EQ_DISTINCT)

lemma EQ_CLAUSES: "ALL t::bool.
   (True = t) = t &
   (t = True) = t & (False = t) = (~ t) & (t = False) = (~ t)"
  by (import bool EQ_CLAUSES)

lemma COND_CLAUSES: "ALL (t1::'a::type) t2::'a::type.
   (if True then t1 else t2) = t1 & (if False then t1 else t2) = t2"
  by (import bool COND_CLAUSES)

lemma SELECT_UNIQUE: "ALL (P::'a::type => bool) x::'a::type.
   (ALL y::'a::type. P y = (y = x)) --> Eps P = x"
  by (import bool SELECT_UNIQUE)

lemma BOTH_EXISTS_AND_THM: "ALL (P::bool) Q::bool.
   (EX x::'a::type. P & Q) = ((EX x::'a::type. P) & (EX x::'a::type. Q))"
  by (import bool BOTH_EXISTS_AND_THM)

lemma BOTH_FORALL_OR_THM: "ALL (P::bool) Q::bool.
   (ALL x::'a::type. P | Q) = ((ALL x::'a::type. P) | (ALL x::'a::type. Q))"
  by (import bool BOTH_FORALL_OR_THM)

lemma BOTH_FORALL_IMP_THM: "ALL (P::bool) Q::bool.
   (ALL x::'a::type. P --> Q) =
   ((EX x::'a::type. P) --> (ALL x::'a::type. Q))"
  by (import bool BOTH_FORALL_IMP_THM)

lemma BOTH_EXISTS_IMP_THM: "ALL (P::bool) Q::bool.
   (EX x::'a::type. P --> Q) =
   ((ALL x::'a::type. P) --> (EX x::'a::type. Q))"
  by (import bool BOTH_EXISTS_IMP_THM)

lemma OR_IMP_THM: "ALL (A::bool) B::bool. (A = (B | A)) = (B --> A)"
  by (import bool OR_IMP_THM)

lemma DE_MORGAN_THM: "ALL (A::bool) B::bool. (~ (A & B)) = (~ A | ~ B) & (~ (A | B)) = (~ A & ~ B)"
  by (import bool DE_MORGAN_THM)

lemma IMP_F_EQ_F: "ALL t::bool. (t --> False) = (t = False)"
  by (import bool IMP_F_EQ_F)

lemma EQ_EXPAND: "ALL (t1::bool) t2::bool. (t1 = t2) = (t1 & t2 | ~ t1 & ~ t2)"
  by (import bool EQ_EXPAND)

lemma COND_RATOR: "ALL (b::bool) (f::'a::type => 'b::type) (g::'a::type => 'b::type)
   x::'a::type. (if b then f else g) x = (if b then f x else g x)"
  by (import bool COND_RATOR)

lemma COND_ABS: "ALL (b::bool) (f::'a::type => 'b::type) g::'a::type => 'b::type.
   (%x::'a::type. if b then f x else g x) = (if b then f else g)"
  by (import bool COND_ABS)

lemma COND_EXPAND: "ALL (b::bool) (t1::bool) t2::bool.
   (if b then t1 else t2) = ((~ b | t1) & (b | t2))"
  by (import bool COND_EXPAND)

lemma ONE_ONE_THM: "ALL f::'a::type => 'b::type.
   inj f = (ALL (x1::'a::type) x2::'a::type. f x1 = f x2 --> x1 = x2)"
  by (import bool ONE_ONE_THM)

lemma ABS_REP_THM: "(All::(('a::type => bool) => bool) => bool)
 (%P::'a::type => bool.
     (op -->::bool => bool => bool)
      ((Ex::(('b::type => 'a::type) => bool) => bool)
        ((TYPE_DEFINITION::('a::type => bool)
                           => ('b::type => 'a::type) => bool)
          P))
      ((Ex::(('b::type => 'a::type) => bool) => bool)
        (%x::'b::type => 'a::type.
            (Ex::(('a::type => 'b::type) => bool) => bool)
             (%abs::'a::type => 'b::type.
                 (op &::bool => bool => bool)
                  ((All::('b::type => bool) => bool)
                    (%a::'b::type.
                        (op =::'b::type => 'b::type => bool) (abs (x a)) a))
                  ((All::('a::type => bool) => bool)
                    (%r::'a::type.
                        (op =::bool => bool => bool) (P r)
                         ((op =::'a::type => 'a::type => bool) (x (abs r))
                           r)))))))"
  by (import bool ABS_REP_THM)

lemma LET_RAND: "(P::'b::type => bool) (Let (M::'a::type) (N::'a::type => 'b::type)) =
(let x::'a::type = M in P (N x))"
  by (import bool LET_RAND)

lemma LET_RATOR: "Let (M::'a::type) (N::'a::type => 'b::type => 'c::type) (b::'b::type) =
(let x::'a::type = M in N x b)"
  by (import bool LET_RATOR)

lemma SWAP_FORALL_THM: "ALL P::'a::type => 'b::type => bool.
   (ALL x::'a::type. All (P x)) = (ALL (y::'b::type) x::'a::type. P x y)"
  by (import bool SWAP_FORALL_THM)

lemma SWAP_EXISTS_THM: "ALL P::'a::type => 'b::type => bool.
   (EX x::'a::type. Ex (P x)) = (EX (y::'b::type) x::'a::type. P x y)"
  by (import bool SWAP_EXISTS_THM)

lemma AND_CONG: "ALL (P::bool) (P'::bool) (Q::bool) Q'::bool.
   (Q --> P = P') & (P' --> Q = Q') --> (P & Q) = (P' & Q')"
  by (import bool AND_CONG)

lemma OR_CONG: "ALL (P::bool) (P'::bool) (Q::bool) Q'::bool.
   (~ Q --> P = P') & (~ P' --> Q = Q') --> (P | Q) = (P' | Q')"
  by (import bool OR_CONG)

lemma COND_CONG: "ALL (P::bool) (Q::bool) (x::'a::type) (x'::'a::type) (y::'a::type)
   y'::'a::type.
   P = Q & (Q --> x = x') & (~ Q --> y = y') -->
   (if P then x else y) = (if Q then x' else y')"
  by (import bool COND_CONG)

lemma MONO_COND: "((x::bool) --> (y::bool)) -->
((z::bool) --> (w::bool)) -->
(if b::bool then x else z) --> (if b then y else w)"
  by (import bool MONO_COND)

lemma SKOLEM_THM: "ALL P::'a::type => 'b::type => bool.
   (ALL x::'a::type. Ex (P x)) =
   (EX f::'a::type => 'b::type. ALL x::'a::type. P x (f x))"
  by (import bool SKOLEM_THM)

lemma bool_case_thm: "(ALL (e0::'a::type) e1::'a::type.
    (case True of True => e0 | False => e1) = e0) &
(ALL (e0::'a::type) e1::'a::type.
    (case False of True => e0 | False => e1) = e1)"
  by (import bool bool_case_thm)

lemma bool_case_ID: "ALL (x::'a::type) b::bool. (case b of True => x | _ => x) = x"
  by (import bool bool_case_ID)

lemma boolAxiom: "ALL (e0::'a::type) e1::'a::type.
   EX x::bool => 'a::type. x True = e0 & x False = e1"
  by (import bool boolAxiom)

lemma UEXISTS_OR_THM: "ALL (P::'a::type => bool) Q::'a::type => bool.
   (EX! x::'a::type. P x | Q x) --> Ex1 P | Ex1 Q"
  by (import bool UEXISTS_OR_THM)

lemma UEXISTS_SIMP: "(EX! x::'a::type. (t::bool)) = (t & (ALL x::'a::type. All (op = x)))"
  by (import bool UEXISTS_SIMP)

consts
  RES_ABSTRACT :: "('a => bool) => ('a => 'b) => 'a => 'b" 

specification (RES_ABSTRACT) RES_ABSTRACT_DEF: "(ALL (p::'a::type => bool) (m::'a::type => 'b::type) x::'a::type.
    IN x p --> RES_ABSTRACT p m x = m x) &
(ALL (p::'a::type => bool) (m1::'a::type => 'b::type)
    m2::'a::type => 'b::type.
    (ALL x::'a::type. IN x p --> m1 x = m2 x) -->
    RES_ABSTRACT p m1 = RES_ABSTRACT p m2)"
  by (import bool RES_ABSTRACT_DEF)

lemma BOOL_FUN_CASES_THM: "ALL f::bool => bool.
   f = (%b::bool. True) |
   f = (%b::bool. False) | f = (%b::bool. b) | f = Not"
  by (import bool BOOL_FUN_CASES_THM)

lemma BOOL_FUN_INDUCT: "ALL P::(bool => bool) => bool.
   P (%b::bool. True) & P (%b::bool. False) & P (%b::bool. b) & P Not -->
   All P"
  by (import bool BOOL_FUN_INDUCT)

;end_setup

;setup_theory combin

definition K :: "'a => 'b => 'a" where 
  "K == %(x::'a::type) y::'b::type. x"

lemma K_DEF: "K = (%(x::'a::type) y::'b::type. x)"
  by (import combin K_DEF)

definition S :: "('a => 'b => 'c) => ('a => 'b) => 'a => 'c" where 
  "S ==
%(f::'a::type => 'b::type => 'c::type) (g::'a::type => 'b::type)
   x::'a::type. f x (g x)"

lemma S_DEF: "S =
(%(f::'a::type => 'b::type => 'c::type) (g::'a::type => 'b::type)
    x::'a::type. f x (g x))"
  by (import combin S_DEF)

definition I :: "'a => 'a" where 
  "(op ==::('a::type => 'a::type) => ('a::type => 'a::type) => prop)
 (I::'a::type => 'a::type)
 ((S::('a::type => ('a::type => 'a::type) => 'a::type)
      => ('a::type => 'a::type => 'a::type) => 'a::type => 'a::type)
   (K::'a::type => ('a::type => 'a::type) => 'a::type)
   (K::'a::type => 'a::type => 'a::type))"

lemma I_DEF: "(op =::('a::type => 'a::type) => ('a::type => 'a::type) => bool)
 (I::'a::type => 'a::type)
 ((S::('a::type => ('a::type => 'a::type) => 'a::type)
      => ('a::type => 'a::type => 'a::type) => 'a::type => 'a::type)
   (K::'a::type => ('a::type => 'a::type) => 'a::type)
   (K::'a::type => 'a::type => 'a::type))"
  by (import combin I_DEF)

definition C :: "('a => 'b => 'c) => 'b => 'a => 'c" where 
  "C == %(f::'a::type => 'b::type => 'c::type) (x::'b::type) y::'a::type. f y x"

lemma C_DEF: "C =
(%(f::'a::type => 'b::type => 'c::type) (x::'b::type) y::'a::type. f y x)"
  by (import combin C_DEF)

definition W :: "('a => 'a => 'b) => 'a => 'b" where 
  "W == %(f::'a::type => 'a::type => 'b::type) x::'a::type. f x x"

lemma W_DEF: "W = (%(f::'a::type => 'a::type => 'b::type) x::'a::type. f x x)"
  by (import combin W_DEF)

lemma I_THM: "ALL x::'a::type. I x = x"
  by (import combin I_THM)

lemma I_o_ID: "ALL f::'a::type => 'b::type. I o f = f & f o I = f"
  by (import combin I_o_ID)

;end_setup

;setup_theory sum

lemma ISL_OR_ISR: "ALL x::'a::type + 'b::type. ISL x | ISR x"
  by (import sum ISL_OR_ISR)

lemma INL: "ALL x::'a::type + 'b::type. ISL x --> Inl (OUTL x) = x"
  by (import sum INL)

lemma INR: "ALL x::'a::type + 'b::type. ISR x --> Inr (OUTR x) = x"
  by (import sum INR)

lemma sum_case_cong: "ALL (M::'b::type + 'c::type) (M'::'b::type + 'c::type)
   (f::'b::type => 'a::type) g::'c::type => 'a::type.
   M = M' &
   (ALL x::'b::type. M' = Inl x --> f x = (f'::'b::type => 'a::type) x) &
   (ALL y::'c::type. M' = Inr y --> g y = (g'::'c::type => 'a::type) y) -->
   sum_case f g M = sum_case f' g' M'"
  by (import sum sum_case_cong)

;end_setup

;setup_theory one

;end_setup

;setup_theory option

lemma option_CLAUSES: "(op &::bool => bool => bool)
 ((All::('a::type => bool) => bool)
   (%x::'a::type.
       (All::('a::type => bool) => bool)
        (%y::'a::type.
            (op =::bool => bool => bool)
             ((op =::'a::type option => 'a::type option => bool)
               ((Some::'a::type ~=> 'a::type) x)
               ((Some::'a::type ~=> 'a::type) y))
             ((op =::'a::type => 'a::type => bool) x y))))
 ((op &::bool => bool => bool)
   ((All::('a::type => bool) => bool)
     (%x::'a::type.
         (op =::'a::type => 'a::type => bool)
          ((the::'a::type option => 'a::type)
            ((Some::'a::type ~=> 'a::type) x))
          x))
   ((op &::bool => bool => bool)
     ((All::('a::type => bool) => bool)
       (%x::'a::type.
           (Not::bool => bool)
            ((op =::'a::type option => 'a::type option => bool)
              (None::'a::type option) ((Some::'a::type ~=> 'a::type) x))))
     ((op &::bool => bool => bool)
       ((All::('a::type => bool) => bool)
         (%x::'a::type.
             (Not::bool => bool)
              ((op =::'a::type option => 'a::type option => bool)
                ((Some::'a::type ~=> 'a::type) x) (None::'a::type option))))
       ((op &::bool => bool => bool)
         ((All::('a::type => bool) => bool)
           (%x::'a::type.
               (op =::bool => bool => bool)
                ((IS_SOME::'a::type option => bool)
                  ((Some::'a::type ~=> 'a::type) x))
                (True::bool)))
         ((op &::bool => bool => bool)
           ((op =::bool => bool => bool)
             ((IS_SOME::'a::type option => bool) (None::'a::type option))
             (False::bool))
           ((op &::bool => bool => bool)
             ((All::('a::type option => bool) => bool)
               (%x::'a::type option.
                   (op =::bool => bool => bool)
                    ((IS_NONE::'a::type option => bool) x)
                    ((op =::'a::type option => 'a::type option => bool) x
                      (None::'a::type option))))
             ((op &::bool => bool => bool)
               ((All::('a::type option => bool) => bool)
                 (%x::'a::type option.
                     (op =::bool => bool => bool)
                      ((Not::bool => bool)
                        ((IS_SOME::'a::type option => bool) x))
                      ((op =::'a::type option => 'a::type option => bool) x
                        (None::'a::type option))))
               ((op &::bool => bool => bool)
                 ((All::('a::type option => bool) => bool)
                   (%x::'a::type option.
                       (op -->::bool => bool => bool)
                        ((IS_SOME::'a::type option => bool) x)
                        ((op =::'a::type option => 'a::type option => bool)
                          ((Some::'a::type ~=> 'a::type)
                            ((the::'a::type option => 'a::type) x))
                          x)))
                 ((op &::bool => bool => bool)
                   ((All::('a::type option => bool) => bool)
                     (%x::'a::type option.
                         (op =::'a::type option => 'a::type option => bool)
                          ((option_case::'a::type option
   => ('a::type ~=> 'a::type) => 'a::type option ~=> 'a::type)
                            (None::'a::type option)
                            (Some::'a::type ~=> 'a::type) x)
                          x))
                   ((op &::bool => bool => bool)
                     ((All::('a::type option => bool) => bool)
                       (%x::'a::type option.
                           (op =::'a::type option
                                  => 'a::type option => bool)
                            ((option_case::'a::type option
     => ('a::type ~=> 'a::type) => 'a::type option ~=> 'a::type)
                              x (Some::'a::type ~=> 'a::type) x)
                            x))
                     ((op &::bool => bool => bool)
                       ((All::('a::type option => bool) => bool)
                         (%x::'a::type option.
                             (op -->::bool => bool => bool)
                              ((IS_NONE::'a::type option => bool) x)
                              ((op =::'b::type => 'b::type => bool)
                                ((option_case::'b::type
         => ('a::type => 'b::type) => 'a::type option => 'b::type)
                                  (e::'b::type) (f::'a::type => 'b::type) x)
                                e)))
                       ((op &::bool => bool => bool)
                         ((All::('a::type option => bool) => bool)
                           (%x::'a::type option.
                               (op -->::bool => bool => bool)
                                ((IS_SOME::'a::type option => bool) x)
                                ((op =::'b::type => 'b::type => bool)
                                  ((option_case::'b::type
           => ('a::type => 'b::type) => 'a::type option => 'b::type)
                                    e f x)
                                  (f ((the::'a::type option => 'a::type)
 x)))))
                         ((op &::bool => bool => bool)
                           ((All::('a::type option => bool) => bool)
                             (%x::'a::type option.
                                 (op -->::bool => bool => bool)
                                  ((IS_SOME::'a::type option => bool) x)
                                  ((op =::'a::type option
    => 'a::type option => bool)
                                    ((option_case::'a::type option
             => ('a::type ~=> 'a::type) => 'a::type option ~=> 'a::type)
(ea::'a::type option) (Some::'a::type ~=> 'a::type) x)
                                    x)))
                           ((op &::bool => bool => bool)
                             ((All::('b::type => bool) => bool)
                               (%u::'b::type.
                                   (All::(('a::type => 'b::type) => bool)
   => bool)
                                    (%f::'a::type => 'b::type.
  (op =::'b::type => 'b::type => bool)
   ((option_case::'b::type
                  => ('a::type => 'b::type) => 'a::type option => 'b::type)
     u f (None::'a::type option))
   u)))
                             ((op &::bool => bool => bool)
                               ((All::('b::type => bool) => bool)
                                 (%u::'b::type.
                                     (All::(('a::type => 'b::type) => bool)
     => bool)
(%f::'a::type => 'b::type.
    (All::('a::type => bool) => bool)
     (%x::'a::type.
         (op =::'b::type => 'b::type => bool)
          ((option_case::'b::type
                         => ('a::type => 'b::type)
                            => 'a::type option => 'b::type)
            u f ((Some::'a::type ~=> 'a::type) x))
          (f x)))))
                               ((op &::bool => bool => bool)
                                 ((All::(('a::type => 'b::type) => bool)
  => bool)
                                   (%f::'a::type => 'b::type.
 (All::('a::type => bool) => bool)
  (%x::'a::type.
      (op =::'b::type option => 'b::type option => bool)
       ((option_map::('a::type => 'b::type) => 'a::type option ~=> 'b::type)
         f ((Some::'a::type ~=> 'a::type) x))
       ((Some::'b::type ~=> 'b::type) (f x)))))
                                 ((op &::bool => bool => bool)
                                   ((All::(('a::type => 'b::type) => bool)
    => bool)
                                     (%f::'a::type => 'b::type.
   (op =::'b::type option => 'b::type option => bool)
    ((option_map::('a::type => 'b::type) => 'a::type option ~=> 'b::type) f
      (None::'a::type option))
    (None::'b::type option)))
                                   ((op &::bool => bool => bool)
                                     ((op =::'a::type option
       => 'a::type option => bool)
 ((OPTION_JOIN::'a::type option option ~=> 'a::type)
   (None::'a::type option option))
 (None::'a::type option))
                                     ((All::('a::type option => bool)
      => bool)
 (%x::'a::type option.
     (op =::'a::type option => 'a::type option => bool)
      ((OPTION_JOIN::'a::type option option ~=> 'a::type)
        ((Some::'a::type option ~=> 'a::type option) x))
      x))))))))))))))))))))"
  by (import option option_CLAUSES)

lemma option_case_compute: "option_case (e::'b::type) (f::'a::type => 'b::type) (x::'a::type option) =
(if IS_SOME x then f (the x) else e)"
  by (import option option_case_compute)

lemma OPTION_MAP_EQ_SOME: "ALL (f::'a::type => 'b::type) (x::'a::type option) y::'b::type.
   (option_map f x = Some y) = (EX z::'a::type. x = Some z & y = f z)"
  by (import option OPTION_MAP_EQ_SOME)

lemma OPTION_JOIN_EQ_SOME: "ALL (x::'a::type option option) xa::'a::type.
   (OPTION_JOIN x = Some xa) = (x = Some (Some xa))"
  by (import option OPTION_JOIN_EQ_SOME)

lemma option_case_cong: "ALL (M::'a::type option) (M'::'a::type option) (u::'b::type)
   f::'a::type => 'b::type.
   M = M' &
   (M' = None --> u = (u'::'b::type)) &
   (ALL x::'a::type. M' = Some x --> f x = (f'::'a::type => 'b::type) x) -->
   option_case u f M = option_case u' f' M'"
  by (import option option_case_cong)

;end_setup

;setup_theory marker

consts
  stmarker :: "'a => 'a" 

defs
  stmarker_primdef: "stmarker == %x::'a::type. x"

lemma stmarker_def: "ALL x::'a::type. stmarker x = x"
  by (import marker stmarker_def)

lemma move_left_conj: "ALL (x::bool) (xa::bool) xb::bool.
   (x & stmarker xb) = (stmarker xb & x) &
   ((stmarker xb & x) & xa) = (stmarker xb & x & xa) &
   (x & stmarker xb & xa) = (stmarker xb & x & xa)"
  by (import marker move_left_conj)

lemma move_right_conj: "ALL (x::bool) (xa::bool) xb::bool.
   (stmarker xb & x) = (x & stmarker xb) &
   (x & xa & stmarker xb) = ((x & xa) & stmarker xb) &
   ((x & stmarker xb) & xa) = ((x & xa) & stmarker xb)"
  by (import marker move_right_conj)

lemma move_left_disj: "ALL (x::bool) (xa::bool) xb::bool.
   (x | stmarker xb) = (stmarker xb | x) &
   ((stmarker xb | x) | xa) = (stmarker xb | x | xa) &
   (x | stmarker xb | xa) = (stmarker xb | x | xa)"
  by (import marker move_left_disj)

lemma move_right_disj: "ALL (x::bool) (xa::bool) xb::bool.
   (stmarker xb | x) = (x | stmarker xb) &
   (x | xa | stmarker xb) = ((x | xa) | stmarker xb) &
   ((x | stmarker xb) | xa) = ((x | xa) | stmarker xb)"
  by (import marker move_right_disj)

;end_setup

;setup_theory relation

definition TC :: "('a => 'a => bool) => 'a => 'a => bool" where 
  "TC ==
%(R::'a::type => 'a::type => bool) (a::'a::type) b::'a::type.
   ALL P::'a::type => 'a::type => bool.
      (ALL (x::'a::type) y::'a::type. R x y --> P x y) &
      (ALL (x::'a::type) (y::'a::type) z::'a::type.
          P x y & P y z --> P x z) -->
      P a b"

lemma TC_DEF: "ALL (R::'a::type => 'a::type => bool) (a::'a::type) b::'a::type.
   TC R a b =
   (ALL P::'a::type => 'a::type => bool.
       (ALL (x::'a::type) y::'a::type. R x y --> P x y) &
       (ALL (x::'a::type) (y::'a::type) z::'a::type.
           P x y & P y z --> P x z) -->
       P a b)"
  by (import relation TC_DEF)

definition RTC :: "('a => 'a => bool) => 'a => 'a => bool" where 
  "RTC ==
%(R::'a::type => 'a::type => bool) (a::'a::type) b::'a::type.
   ALL P::'a::type => 'a::type => bool.
      (ALL x::'a::type. P x x) &
      (ALL (x::'a::type) (y::'a::type) z::'a::type.
          R x y & P y z --> P x z) -->
      P a b"

lemma RTC_DEF: "ALL (R::'a::type => 'a::type => bool) (a::'a::type) b::'a::type.
   RTC R a b =
   (ALL P::'a::type => 'a::type => bool.
       (ALL x::'a::type. P x x) &
       (ALL (x::'a::type) (y::'a::type) z::'a::type.
           R x y & P y z --> P x z) -->
       P a b)"
  by (import relation RTC_DEF)

consts
  RC :: "('a => 'a => bool) => 'a => 'a => bool" 

defs
  RC_primdef: "RC ==
%(R::'a::type => 'a::type => bool) (x::'a::type) y::'a::type. x = y | R x y"

lemma RC_def: "ALL (R::'a::type => 'a::type => bool) (x::'a::type) y::'a::type.
   RC R x y = (x = y | R x y)"
  by (import relation RC_def)

consts
  transitive :: "('a => 'a => bool) => bool" 

defs
  transitive_primdef: "transitive ==
%R::'a::type => 'a::type => bool.
   ALL (x::'a::type) (y::'a::type) z::'a::type. R x y & R y z --> R x z"

lemma transitive_def: "ALL R::'a::type => 'a::type => bool.
   transitive R =
   (ALL (x::'a::type) (y::'a::type) z::'a::type. R x y & R y z --> R x z)"
  by (import relation transitive_def)

definition pred_reflexive :: "('a => 'a => bool) => bool" where 
  "pred_reflexive == %R::'a::type => 'a::type => bool. ALL x::'a::type. R x x"

lemma reflexive_def: "ALL R::'a::type => 'a::type => bool.
   pred_reflexive R = (ALL x::'a::type. R x x)"
  by (import relation reflexive_def)

lemma TC_TRANSITIVE: "ALL x::'a::type => 'a::type => bool. transitive (TC x)"
  by (import relation TC_TRANSITIVE)

lemma RTC_INDUCT: "ALL (x::'a::type => 'a::type => bool) xa::'a::type => 'a::type => bool.
   (ALL x::'a::type. xa x x) &
   (ALL (xb::'a::type) (y::'a::type) z::'a::type.
       x xb y & xa y z --> xa xb z) -->
   (ALL (xb::'a::type) xc::'a::type. RTC x xb xc --> xa xb xc)"
  by (import relation RTC_INDUCT)

lemma TC_RULES: "ALL x::'a::type => 'a::type => bool.
   (ALL (xa::'a::type) xb::'a::type. x xa xb --> TC x xa xb) &
   (ALL (xa::'a::type) (xb::'a::type) xc::'a::type.
       TC x xa xb & TC x xb xc --> TC x xa xc)"
  by (import relation TC_RULES)

lemma RTC_RULES: "ALL x::'a::type => 'a::type => bool.
   (ALL xa::'a::type. RTC x xa xa) &
   (ALL (xa::'a::type) (xb::'a::type) xc::'a::type.
       x xa xb & RTC x xb xc --> RTC x xa xc)"
  by (import relation RTC_RULES)

lemma RTC_STRONG_INDUCT: "ALL (R::'a::type => 'a::type => bool) P::'a::type => 'a::type => bool.
   (ALL x::'a::type. P x x) &
   (ALL (x::'a::type) (y::'a::type) z::'a::type.
       R x y & RTC R y z & P y z --> P x z) -->
   (ALL (x::'a::type) y::'a::type. RTC R x y --> P x y)"
  by (import relation RTC_STRONG_INDUCT)

lemma RTC_RTC: "ALL (R::'a::type => 'a::type => bool) (x::'a::type) y::'a::type.
   RTC R x y --> (ALL z::'a::type. RTC R y z --> RTC R x z)"
  by (import relation RTC_RTC)

lemma RTC_TRANSITIVE: "ALL x::'a::type => 'a::type => bool. transitive (RTC x)"
  by (import relation RTC_TRANSITIVE)

lemma RTC_REFLEXIVE: "ALL R::'a::type => 'a::type => bool. pred_reflexive (RTC R)"
  by (import relation RTC_REFLEXIVE)

lemma RC_REFLEXIVE: "ALL R::'a::type => 'a::type => bool. pred_reflexive (RC R)"
  by (import relation RC_REFLEXIVE)

lemma TC_SUBSET: "ALL (x::'a::type => 'a::type => bool) (xa::'a::type) xb::'a::type.
   x xa xb --> TC x xa xb"
  by (import relation TC_SUBSET)

lemma RTC_SUBSET: "ALL (R::'a::type => 'a::type => bool) (x::'a::type) y::'a::type.
   R x y --> RTC R x y"
  by (import relation RTC_SUBSET)

lemma RC_SUBSET: "ALL (R::'a::type => 'a::type => bool) (x::'a::type) y::'a::type.
   R x y --> RC R x y"
  by (import relation RC_SUBSET)

lemma RC_RTC: "ALL (R::'a::type => 'a::type => bool) (x::'a::type) y::'a::type.
   RC R x y --> RTC R x y"
  by (import relation RC_RTC)

lemma TC_INDUCT: "ALL (x::'a::type => 'a::type => bool) xa::'a::type => 'a::type => bool.
   (ALL (xb::'a::type) y::'a::type. x xb y --> xa xb y) &
   (ALL (x::'a::type) (y::'a::type) z::'a::type.
       xa x y & xa y z --> xa x z) -->
   (ALL (xb::'a::type) xc::'a::type. TC x xb xc --> xa xb xc)"
  by (import relation TC_INDUCT)

lemma TC_INDUCT_LEFT1: "ALL (x::'a::type => 'a::type => bool) xa::'a::type => 'a::type => bool.
   (ALL (xb::'a::type) y::'a::type. x xb y --> xa xb y) &
   (ALL (xb::'a::type) (y::'a::type) z::'a::type.
       x xb y & xa y z --> xa xb z) -->
   (ALL (xb::'a::type) xc::'a::type. TC x xb xc --> xa xb xc)"
  by (import relation TC_INDUCT_LEFT1)

lemma TC_STRONG_INDUCT: "ALL (R::'a::type => 'a::type => bool) P::'a::type => 'a::type => bool.
   (ALL (x::'a::type) y::'a::type. R x y --> P x y) &
   (ALL (x::'a::type) (y::'a::type) z::'a::type.
       P x y & P y z & TC R x y & TC R y z --> P x z) -->
   (ALL (u::'a::type) v::'a::type. TC R u v --> P u v)"
  by (import relation TC_STRONG_INDUCT)

lemma TC_STRONG_INDUCT_LEFT1: "ALL (R::'a::type => 'a::type => bool) P::'a::type => 'a::type => bool.
   (ALL (x::'a::type) y::'a::type. R x y --> P x y) &
   (ALL (x::'a::type) (y::'a::type) z::'a::type.
       R x y & P y z & TC R y z --> P x z) -->
   (ALL (u::'a::type) v::'a::type. TC R u v --> P u v)"
  by (import relation TC_STRONG_INDUCT_LEFT1)

lemma TC_RTC: "ALL (R::'a::type => 'a::type => bool) (x::'a::type) y::'a::type.
   TC R x y --> RTC R x y"
  by (import relation TC_RTC)

lemma RTC_TC_RC: "ALL (R::'a::type => 'a::type => bool) (x::'a::type) y::'a::type.
   RTC R x y --> RC R x y | TC R x y"
  by (import relation RTC_TC_RC)

lemma TC_RC_EQNS: "ALL R::'a::type => 'a::type => bool. RC (TC R) = RTC R & TC (RC R) = RTC R"
  by (import relation TC_RC_EQNS)

lemma RC_IDEM: "ALL R::'a::type => 'a::type => bool. RC (RC R) = RC R"
  by (import relation RC_IDEM)

lemma TC_IDEM: "ALL R::'a::type => 'a::type => bool. TC (TC R) = TC R"
  by (import relation TC_IDEM)

lemma RTC_IDEM: "ALL R::'a::type => 'a::type => bool. RTC (RTC R) = RTC R"
  by (import relation RTC_IDEM)

lemma RTC_CASES1: "ALL (x::'a::type => 'a::type => bool) (xa::'a::type) xb::'a::type.
   RTC x xa xb = (xa = xb | (EX u::'a::type. x xa u & RTC x u xb))"
  by (import relation RTC_CASES1)

lemma RTC_CASES2: "ALL (x::'a::type => 'a::type => bool) (xa::'a::type) xb::'a::type.
   RTC x xa xb = (xa = xb | (EX u::'a::type. RTC x xa u & x u xb))"
  by (import relation RTC_CASES2)

lemma RTC_CASES_RTC_TWICE: "ALL (x::'a::type => 'a::type => bool) (xa::'a::type) xb::'a::type.
   RTC x xa xb = (EX u::'a::type. RTC x xa u & RTC x u xb)"
  by (import relation RTC_CASES_RTC_TWICE)

lemma TC_CASES1: "ALL (R::'a::type => 'a::type => bool) (x::'a::type) z::'a::type.
   TC R x z --> R x z | (EX y::'a::type. R x y & TC R y z)"
  by (import relation TC_CASES1)

lemma TC_CASES2: "ALL (R::'a::type => 'a::type => bool) (x::'a::type) z::'a::type.
   TC R x z --> R x z | (EX y::'a::type. TC R x y & R y z)"
  by (import relation TC_CASES2)

lemma TC_MONOTONE: "ALL (R::'a::type => 'a::type => bool) Q::'a::type => 'a::type => bool.
   (ALL (x::'a::type) y::'a::type. R x y --> Q x y) -->
   (ALL (x::'a::type) y::'a::type. TC R x y --> TC Q x y)"
  by (import relation TC_MONOTONE)

lemma RTC_MONOTONE: "ALL (R::'a::type => 'a::type => bool) Q::'a::type => 'a::type => bool.
   (ALL (x::'a::type) y::'a::type. R x y --> Q x y) -->
   (ALL (x::'a::type) y::'a::type. RTC R x y --> RTC Q x y)"
  by (import relation RTC_MONOTONE)

definition WF :: "('a => 'a => bool) => bool" where 
  "WF ==
%R::'a::type => 'a::type => bool.
   ALL B::'a::type => bool.
      Ex B -->
      (EX min::'a::type. B min & (ALL b::'a::type. R b min --> ~ B b))"

lemma WF_DEF: "ALL R::'a::type => 'a::type => bool.
   WF R =
   (ALL B::'a::type => bool.
       Ex B -->
       (EX min::'a::type. B min & (ALL b::'a::type. R b min --> ~ B b)))"
  by (import relation WF_DEF)

lemma WF_INDUCTION_THM: "ALL R::'a::type => 'a::type => bool.
   WF R -->
   (ALL P::'a::type => bool.
       (ALL x::'a::type. (ALL y::'a::type. R y x --> P y) --> P x) -->
       All P)"
  by (import relation WF_INDUCTION_THM)

lemma WF_NOT_REFL: "ALL (x::'a::type => 'a::type => bool) (xa::'a::type) xb::'a::type.
   WF x --> x xa xb --> xa ~= xb"
  by (import relation WF_NOT_REFL)

definition EMPTY_REL :: "'a => 'a => bool" where 
  "EMPTY_REL == %(x::'a::type) y::'a::type. False"

lemma EMPTY_REL_DEF: "ALL (x::'a::type) y::'a::type. EMPTY_REL x y = False"
  by (import relation EMPTY_REL_DEF)

lemma WF_EMPTY_REL: "WF EMPTY_REL"
  by (import relation WF_EMPTY_REL)

lemma WF_SUBSET: "ALL (x::'a::type => 'a::type => bool) xa::'a::type => 'a::type => bool.
   WF x & (ALL (xb::'a::type) y::'a::type. xa xb y --> x xb y) --> WF xa"
  by (import relation WF_SUBSET)

lemma WF_TC: "ALL R::'a::type => 'a::type => bool. WF R --> WF (TC R)"
  by (import relation WF_TC)

consts
  inv_image :: "('b => 'b => bool) => ('a => 'b) => 'a => 'a => bool" 

defs
  inv_image_primdef: "relation.inv_image ==
%(R::'b::type => 'b::type => bool) (f::'a::type => 'b::type) (x::'a::type)
   y::'a::type. R (f x) (f y)"

lemma inv_image_def: "ALL (R::'b::type => 'b::type => bool) f::'a::type => 'b::type.
   relation.inv_image R f = (%(x::'a::type) y::'a::type. R (f x) (f y))"
  by (import relation inv_image_def)

lemma WF_inv_image: "ALL (R::'b::type => 'b::type => bool) f::'a::type => 'b::type.
   WF R --> WF (relation.inv_image R f)"
  by (import relation WF_inv_image)

definition RESTRICT :: "('a => 'b) => ('a => 'a => bool) => 'a => 'a => 'b" where 
  "RESTRICT ==
%(f::'a::type => 'b::type) (R::'a::type => 'a::type => bool) (x::'a::type)
   y::'a::type. if R y x then f y else ARB"

lemma RESTRICT_DEF: "ALL (f::'a::type => 'b::type) (R::'a::type => 'a::type => bool) x::'a::type.
   RESTRICT f R x = (%y::'a::type. if R y x then f y else ARB)"
  by (import relation RESTRICT_DEF)

lemma RESTRICT_LEMMA: "ALL (x::'a::type => 'b::type) (xa::'a::type => 'a::type => bool)
   (xb::'a::type) xc::'a::type. xa xb xc --> RESTRICT x xa xc xb = x xb"
  by (import relation RESTRICT_LEMMA)

consts
  approx :: "('a => 'a => bool) => (('a => 'b) => 'a => 'b) => 'a => ('a => 'b) => bool" 

defs
  approx_primdef: "approx ==
%(R::'a::type => 'a::type => bool)
   (M::('a::type => 'b::type) => 'a::type => 'b::type) (x::'a::type)
   f::'a::type => 'b::type.
   f = RESTRICT (%y::'a::type. M (RESTRICT f R y) y) R x"

lemma approx_def: "ALL (R::'a::type => 'a::type => bool)
   (M::('a::type => 'b::type) => 'a::type => 'b::type) (x::'a::type)
   f::'a::type => 'b::type.
   approx R M x f = (f = RESTRICT (%y::'a::type. M (RESTRICT f R y) y) R x)"
  by (import relation approx_def)

consts
  the_fun :: "('a => 'a => bool) => (('a => 'b) => 'a => 'b) => 'a => 'a => 'b" 

defs
  the_fun_primdef: "the_fun ==
%(R::'a::type => 'a::type => bool)
   (M::('a::type => 'b::type) => 'a::type => 'b::type) x::'a::type.
   Eps (approx R M x)"

lemma the_fun_def: "ALL (R::'a::type => 'a::type => bool)
   (M::('a::type => 'b::type) => 'a::type => 'b::type) x::'a::type.
   the_fun R M x = Eps (approx R M x)"
  by (import relation the_fun_def)

definition WFREC :: "('a => 'a => bool) => (('a => 'b) => 'a => 'b) => 'a => 'b" where 
  "WFREC ==
%(R::'a::type => 'a::type => bool)
   (M::('a::type => 'b::type) => 'a::type => 'b::type) x::'a::type.
   M (RESTRICT
       (the_fun (TC R)
         (%(f::'a::type => 'b::type) v::'a::type. M (RESTRICT f R v) v) x)
       R x)
    x"

lemma WFREC_DEF: "ALL (R::'a::type => 'a::type => bool)
   M::('a::type => 'b::type) => 'a::type => 'b::type.
   WFREC R M =
   (%x::'a::type.
       M (RESTRICT
           (the_fun (TC R)
             (%(f::'a::type => 'b::type) v::'a::type. M (RESTRICT f R v) v)
             x)
           R x)
        x)"
  by (import relation WFREC_DEF)

lemma WFREC_THM: "ALL (R::'a::type => 'a::type => bool)
   M::('a::type => 'b::type) => 'a::type => 'b::type.
   WF R --> (ALL x::'a::type. WFREC R M x = M (RESTRICT (WFREC R M) R x) x)"
  by (import relation WFREC_THM)

lemma WFREC_COROLLARY: "ALL (M::('a::type => 'b::type) => 'a::type => 'b::type)
   (R::'a::type => 'a::type => bool) f::'a::type => 'b::type.
   f = WFREC R M --> WF R --> (ALL x::'a::type. f x = M (RESTRICT f R x) x)"
  by (import relation WFREC_COROLLARY)

lemma WF_RECURSION_THM: "ALL R::'a::type => 'a::type => bool.
   WF R -->
   (ALL M::('a::type => 'b::type) => 'a::type => 'b::type.
       EX! f::'a::type => 'b::type.
          ALL x::'a::type. f x = M (RESTRICT f R x) x)"
  by (import relation WF_RECURSION_THM)

;end_setup

;setup_theory pair

lemma CURRY_ONE_ONE_THM: "(curry (f::'a::type * 'b::type => 'c::type) =
 curry (g::'a::type * 'b::type => 'c::type)) =
(f = g)"
  by (import pair CURRY_ONE_ONE_THM)

lemma UNCURRY_ONE_ONE_THM: "(op =::bool => bool => bool)
 ((op =::('a::type * 'b::type => 'c::type)
         => ('a::type * 'b::type => 'c::type) => bool)
   ((split::('a::type => 'b::type => 'c::type)
            => 'a::type * 'b::type => 'c::type)
     (f::'a::type => 'b::type => 'c::type))
   ((split::('a::type => 'b::type => 'c::type)
            => 'a::type * 'b::type => 'c::type)
     (g::'a::type => 'b::type => 'c::type)))
 ((op =::('a::type => 'b::type => 'c::type)
         => ('a::type => 'b::type => 'c::type) => bool)
   f g)"
  by (import pair UNCURRY_ONE_ONE_THM)

lemma pair_Axiom: "ALL f::'a::type => 'b::type => 'c::type.
   EX x::'a::type * 'b::type => 'c::type.
      ALL (xa::'a::type) y::'b::type. x (xa, y) = f xa y"
  by (import pair pair_Axiom)

lemma UNCURRY_CONG: "ALL (M::'a::type * 'b::type) (M'::'a::type * 'b::type)
   f::'a::type => 'b::type => 'c::type.
   M = M' &
   (ALL (x::'a::type) y::'b::type.
       M' = (x, y) -->
       f x y = (f'::'a::type => 'b::type => 'c::type) x y) -->
   split f M = split f' M'"
  by (import pair UNCURRY_CONG)

lemma ELIM_PEXISTS: "(EX p::'a::type * 'b::type.
    (P::'a::type => 'b::type => bool) (fst p) (snd p)) =
(EX p1::'a::type. Ex (P p1))"
  by (import pair ELIM_PEXISTS)

lemma ELIM_PFORALL: "(ALL p::'a::type * 'b::type.
    (P::'a::type => 'b::type => bool) (fst p) (snd p)) =
(ALL p1::'a::type. All (P p1))"
  by (import pair ELIM_PFORALL)

lemma PFORALL_THM: "(All::(('a::type => 'b::type => bool) => bool) => bool)
 (%x::'a::type => 'b::type => bool.
     (op =::bool => bool => bool)
      ((All::('a::type => bool) => bool)
        (%xa::'a::type. (All::('b::type => bool) => bool) (x xa)))
      ((All::('a::type * 'b::type => bool) => bool)
        ((split::('a::type => 'b::type => bool)
                 => 'a::type * 'b::type => bool)
          x)))"
  by (import pair PFORALL_THM)

lemma PEXISTS_THM: "(All::(('a::type => 'b::type => bool) => bool) => bool)
 (%x::'a::type => 'b::type => bool.
     (op =::bool => bool => bool)
      ((Ex::('a::type => bool) => bool)
        (%xa::'a::type. (Ex::('b::type => bool) => bool) (x xa)))
      ((Ex::('a::type * 'b::type => bool) => bool)
        ((split::('a::type => 'b::type => bool)
                 => 'a::type * 'b::type => bool)
          x)))"
  by (import pair PEXISTS_THM)

lemma LET2_RAND: "(All::(('c::type => 'd::type) => bool) => bool)
 (%x::'c::type => 'd::type.
     (All::('a::type * 'b::type => bool) => bool)
      (%xa::'a::type * 'b::type.
          (All::(('a::type => 'b::type => 'c::type) => bool) => bool)
           (%xb::'a::type => 'b::type => 'c::type.
               (op =::'d::type => 'd::type => bool)
                (x ((Let::'a::type * 'b::type
                          => ('a::type * 'b::type => 'c::type) => 'c::type)
                     xa ((split::('a::type => 'b::type => 'c::type)
                                 => 'a::type * 'b::type => 'c::type)
                          xb)))
                ((Let::'a::type * 'b::type
                       => ('a::type * 'b::type => 'd::type) => 'd::type)
                  xa ((split::('a::type => 'b::type => 'd::type)
                              => 'a::type * 'b::type => 'd::type)
                       (%(xa::'a::type) y::'b::type. x (xb xa y)))))))"
  by (import pair LET2_RAND)

lemma LET2_RATOR: "(All::('a1::type * 'a2::type => bool) => bool)
 (%x::'a1::type * 'a2::type.
     (All::(('a1::type => 'a2::type => 'b::type => 'c::type) => bool)
           => bool)
      (%xa::'a1::type => 'a2::type => 'b::type => 'c::type.
          (All::('b::type => bool) => bool)
           (%xb::'b::type.
               (op =::'c::type => 'c::type => bool)
                ((Let::'a1::type * 'a2::type
                       => ('a1::type * 'a2::type => 'b::type => 'c::type)
                          => 'b::type => 'c::type)
                  x ((split::('a1::type
                              => 'a2::type => 'b::type => 'c::type)
                             => 'a1::type * 'a2::type
                                => 'b::type => 'c::type)
                      xa)
                  xb)
                ((Let::'a1::type * 'a2::type
                       => ('a1::type * 'a2::type => 'c::type) => 'c::type)
                  x ((split::('a1::type => 'a2::type => 'c::type)
                             => 'a1::type * 'a2::type => 'c::type)
                      (%(x::'a1::type) y::'a2::type. xa x y xb))))))"
  by (import pair LET2_RATOR)

lemma pair_case_cong: "ALL (x::'a::type * 'b::type) (xa::'a::type * 'b::type)
   xb::'a::type => 'b::type => 'c::type.
   x = xa &
   (ALL (x::'a::type) y::'b::type.
       xa = (x, y) -->
       xb x y = (f'::'a::type => 'b::type => 'c::type) x y) -->
   split xb x = split f' xa"
  by (import pair pair_case_cong)

definition LEX :: "('a => 'a => bool) => ('b => 'b => bool) => 'a * 'b => 'a * 'b => bool" where 
  "LEX ==
%(R1::'a::type => 'a::type => bool) (R2::'b::type => 'b::type => bool)
   (s::'a::type, t::'b::type) (u::'a::type, v::'b::type).
   R1 s u | s = u & R2 t v"

lemma LEX_DEF: "ALL (R1::'a::type => 'a::type => bool) R2::'b::type => 'b::type => bool.
   LEX R1 R2 =
   (%(s::'a::type, t::'b::type) (u::'a::type, v::'b::type).
       R1 s u | s = u & R2 t v)"
  by (import pair LEX_DEF)

lemma WF_LEX: "ALL (x::'a::type => 'a::type => bool) xa::'b::type => 'b::type => bool.
   WF x & WF xa --> WF (LEX x xa)"
  by (import pair WF_LEX)

definition RPROD :: "('a => 'a => bool) => ('b => 'b => bool) => 'a * 'b => 'a * 'b => bool" where 
  "RPROD ==
%(R1::'a::type => 'a::type => bool) (R2::'b::type => 'b::type => bool)
   (s::'a::type, t::'b::type) (u::'a::type, v::'b::type). R1 s u & R2 t v"

lemma RPROD_DEF: "ALL (R1::'a::type => 'a::type => bool) R2::'b::type => 'b::type => bool.
   RPROD R1 R2 =
   (%(s::'a::type, t::'b::type) (u::'a::type, v::'b::type). R1 s u & R2 t v)"
  by (import pair RPROD_DEF)

lemma WF_RPROD: "ALL (R::'a::type => 'a::type => bool) Q::'b::type => 'b::type => bool.
   WF R & WF Q --> WF (RPROD R Q)"
  by (import pair WF_RPROD)

;end_setup

;setup_theory num

;end_setup

;setup_theory prim_rec

lemma LESS_0_0: "0 < Suc 0"
  by (import prim_rec LESS_0_0)

lemma LESS_LEMMA1: "ALL (x::nat) xa::nat. x < Suc xa --> x = xa | x < xa"
  by (import prim_rec LESS_LEMMA1)

lemma LESS_LEMMA2: "ALL (m::nat) n::nat. m = n | m < n --> m < Suc n"
  by (import prim_rec LESS_LEMMA2)

lemma LESS_THM: "ALL (m::nat) n::nat. (m < Suc n) = (m = n | m < n)"
  by (import prim_rec LESS_THM)

lemma LESS_SUC_IMP: "ALL (x::nat) xa::nat. x < Suc xa --> x ~= xa --> x < xa"
  by (import prim_rec LESS_SUC_IMP)

lemma EQ_LESS: "ALL n::nat. Suc (m::nat) = n --> m < n"
  by (import prim_rec EQ_LESS)

lemma NOT_LESS_EQ: "ALL (m::nat) n::nat. m = n --> ~ m < n"
  by (import prim_rec NOT_LESS_EQ)

definition SIMP_REC_REL :: "(nat => 'a) => 'a => ('a => 'a) => nat => bool" where 
  "(op ==::((nat => 'a::type)
         => 'a::type => ('a::type => 'a::type) => nat => bool)
        => ((nat => 'a::type)
            => 'a::type => ('a::type => 'a::type) => nat => bool)
           => prop)
 (SIMP_REC_REL::(nat => 'a::type)
                => 'a::type => ('a::type => 'a::type) => nat => bool)
 (%(fun::nat => 'a::type) (x::'a::type) (f::'a::type => 'a::type) n::nat.
     (op &::bool => bool => bool)
      ((op =::'a::type => 'a::type => bool) (fun (0::nat)) x)
      ((All::(nat => bool) => bool)
        (%m::nat.
            (op -->::bool => bool => bool) ((op <::nat => nat => bool) m n)
             ((op =::'a::type => 'a::type => bool)
               (fun ((Suc::nat => nat) m)) (f (fun m))))))"

lemma SIMP_REC_REL: "(All::((nat => 'a::type) => bool) => bool)
 (%fun::nat => 'a::type.
     (All::('a::type => bool) => bool)
      (%x::'a::type.
          (All::(('a::type => 'a::type) => bool) => bool)
           (%f::'a::type => 'a::type.
               (All::(nat => bool) => bool)
                (%n::nat.
                    (op =::bool => bool => bool)
                     ((SIMP_REC_REL::(nat => 'a::type)
                                     => 'a::type
  => ('a::type => 'a::type) => nat => bool)
                       fun x f n)
                     ((op &::bool => bool => bool)
                       ((op =::'a::type => 'a::type => bool) (fun (0::nat))
                         x)
                       ((All::(nat => bool) => bool)
                         (%m::nat.
                             (op -->::bool => bool => bool)
                              ((op <::nat => nat => bool) m n)
                              ((op =::'a::type => 'a::type => bool)
                                (fun ((Suc::nat => nat) m))
                                (f (fun m))))))))))"
  by (import prim_rec SIMP_REC_REL)

lemma SIMP_REC_EXISTS: "ALL (x::'a::type) (f::'a::type => 'a::type) n::nat.
   EX fun::nat => 'a::type. SIMP_REC_REL fun x f n"
  by (import prim_rec SIMP_REC_EXISTS)

lemma SIMP_REC_REL_UNIQUE: "ALL (x::'a::type) (xa::'a::type => 'a::type) (xb::nat => 'a::type)
   (xc::nat => 'a::type) (xd::nat) xe::nat.
   SIMP_REC_REL xb x xa xd & SIMP_REC_REL xc x xa xe -->
   (ALL n::nat. n < xd & n < xe --> xb n = xc n)"
  by (import prim_rec SIMP_REC_REL_UNIQUE)

lemma SIMP_REC_REL_UNIQUE_RESULT: "ALL (x::'a::type) (f::'a::type => 'a::type) n::nat.
   EX! y::'a::type.
      EX g::nat => 'a::type. SIMP_REC_REL g x f (Suc n) & y = g n"
  by (import prim_rec SIMP_REC_REL_UNIQUE_RESULT)

consts
  SIMP_REC :: "'a => ('a => 'a) => nat => 'a" 

specification (SIMP_REC) SIMP_REC: "ALL (x::'a::type) (f'::'a::type => 'a::type) n::nat.
   EX g::nat => 'a::type.
      SIMP_REC_REL g x f' (Suc n) & SIMP_REC x f' n = g n"
  by (import prim_rec SIMP_REC)

lemma LESS_SUC_SUC: "ALL m::nat. m < Suc m & m < Suc (Suc m)"
  by (import prim_rec LESS_SUC_SUC)

lemma SIMP_REC_THM: "ALL (x::'a::type) f::'a::type => 'a::type.
   SIMP_REC x f 0 = x &
   (ALL m::nat. SIMP_REC x f (Suc m) = f (SIMP_REC x f m))"
  by (import prim_rec SIMP_REC_THM)

definition PRE :: "nat => nat" where 
  "PRE == %m::nat. if m = 0 then 0 else SOME n::nat. m = Suc n"

lemma PRE_DEF: "ALL m::nat. PRE m = (if m = 0 then 0 else SOME n::nat. m = Suc n)"
  by (import prim_rec PRE_DEF)

lemma PRE: "PRE 0 = 0 & (ALL m::nat. PRE (Suc m) = m)"
  by (import prim_rec PRE)

definition PRIM_REC_FUN :: "'a => ('a => nat => 'a) => nat => nat => 'a" where 
  "PRIM_REC_FUN ==
%(x::'a::type) f::'a::type => nat => 'a::type.
   SIMP_REC (%n::nat. x) (%(fun::nat => 'a::type) n::nat. f (fun (PRE n)) n)"

lemma PRIM_REC_FUN: "ALL (x::'a::type) f::'a::type => nat => 'a::type.
   PRIM_REC_FUN x f =
   SIMP_REC (%n::nat. x) (%(fun::nat => 'a::type) n::nat. f (fun (PRE n)) n)"
  by (import prim_rec PRIM_REC_FUN)

lemma PRIM_REC_EQN: "ALL (x::'a::type) f::'a::type => nat => 'a::type.
   (ALL n::nat. PRIM_REC_FUN x f 0 n = x) &
   (ALL (m::nat) n::nat.
       PRIM_REC_FUN x f (Suc m) n = f (PRIM_REC_FUN x f m (PRE n)) n)"
  by (import prim_rec PRIM_REC_EQN)

definition PRIM_REC :: "'a => ('a => nat => 'a) => nat => 'a" where 
  "PRIM_REC ==
%(x::'a::type) (f::'a::type => nat => 'a::type) m::nat.
   PRIM_REC_FUN x f m (PRE m)"

lemma PRIM_REC: "ALL (x::'a::type) (f::'a::type => nat => 'a::type) m::nat.
   PRIM_REC x f m = PRIM_REC_FUN x f m (PRE m)"
  by (import prim_rec PRIM_REC)

lemma PRIM_REC_THM: "ALL (x::'a::type) f::'a::type => nat => 'a::type.
   PRIM_REC x f 0 = x &
   (ALL m::nat. PRIM_REC x f (Suc m) = f (PRIM_REC x f m) m)"
  by (import prim_rec PRIM_REC_THM)

lemma DC: "ALL (P::'a::type => bool) (R::'a::type => 'a::type => bool) a::'a::type.
   P a & (ALL x::'a::type. P x --> (EX y::'a::type. P y & R x y)) -->
   (EX x::nat => 'a::type.
       x 0 = a & (ALL n::nat. P (x n) & R (x n) (x (Suc n))))"
  by (import prim_rec DC)

lemma num_Axiom_old: "ALL (e::'a::type) f::'a::type => nat => 'a::type.
   EX! fn1::nat => 'a::type.
      fn1 0 = e & (ALL n::nat. fn1 (Suc n) = f (fn1 n) n)"
  by (import prim_rec num_Axiom_old)

lemma num_Axiom: "ALL (e::'a::type) f::nat => 'a::type => 'a::type.
   EX x::nat => 'a::type. x 0 = e & (ALL n::nat. x (Suc n) = f n (x n))"
  by (import prim_rec num_Axiom)

consts
  wellfounded :: "('a => 'a => bool) => bool" 

defs
  wellfounded_primdef: "wellfounded ==
%R::'a::type => 'a::type => bool.
   ~ (EX f::nat => 'a::type. ALL n::nat. R (f (Suc n)) (f n))"

lemma wellfounded_def: "ALL R::'a::type => 'a::type => bool.
   wellfounded R =
   (~ (EX f::nat => 'a::type. ALL n::nat. R (f (Suc n)) (f n)))"
  by (import prim_rec wellfounded_def)

lemma WF_IFF_WELLFOUNDED: "ALL R::'a::type => 'a::type => bool. WF R = wellfounded R"
  by (import prim_rec WF_IFF_WELLFOUNDED)

lemma WF_PRED: "WF (%(x::nat) y::nat. y = Suc x)"
  by (import prim_rec WF_PRED)

lemma WF_LESS: "(WF::(nat => nat => bool) => bool) (op <::nat => nat => bool)"
  by (import prim_rec WF_LESS)

consts
  measure :: "('a => nat) => 'a => 'a => bool" 

defs
  measure_primdef: "prim_rec.measure == relation.inv_image op <"

lemma measure_def: "prim_rec.measure = relation.inv_image op <"
  by (import prim_rec measure_def)

lemma WF_measure: "ALL x::'a::type => nat. WF (prim_rec.measure x)"
  by (import prim_rec WF_measure)

lemma measure_thm: "ALL (x::'a::type => nat) (xa::'a::type) xb::'a::type.
   prim_rec.measure x xa xb = (x xa < x xb)"
  by (import prim_rec measure_thm)

;end_setup

;setup_theory arithmetic

definition nat_elim__magic :: "nat => nat" where 
  "nat_elim__magic == %n::nat. n"

lemma nat_elim__magic: "ALL n::nat. nat_elim__magic n = n"
  by (import arithmetic nat_elim__magic)

consts
  EVEN :: "nat => bool" 

specification (EVEN) EVEN: "EVEN 0 = True & (ALL n::nat. EVEN (Suc n) = (~ EVEN n))"
  by (import arithmetic EVEN)

consts
  ODD :: "nat => bool" 

specification (ODD) ODD: "ODD 0 = False & (ALL n::nat. ODD (Suc n) = (~ ODD n))"
  by (import arithmetic ODD)

lemma TWO: "2 = Suc 1"
  by (import arithmetic TWO)

lemma NORM_0: "(op =::nat => nat => bool) (0::nat) (0::nat)"
  by (import arithmetic NORM_0)

lemma num_case_compute: "ALL n::nat.
   nat_case (f::'a::type) (g::nat => 'a::type) n =
   (if n = 0 then f else g (PRE n))"
  by (import arithmetic num_case_compute)

lemma ADD_CLAUSES: "0 + (m::nat) = m &
m + 0 = m & Suc m + (n::nat) = Suc (m + n) & m + Suc n = Suc (m + n)"
  by (import arithmetic ADD_CLAUSES)

lemma LESS_ADD: "ALL (m::nat) n::nat. n < m --> (EX p::nat. p + n = m)"
  by (import arithmetic LESS_ADD)

lemma LESS_ANTISYM: "ALL (m::nat) n::nat. ~ (m < n & n < m)"
  by (import arithmetic LESS_ANTISYM)

lemma LESS_LESS_SUC: "ALL (x::nat) xa::nat. ~ (x < xa & xa < Suc x)"
  by (import arithmetic LESS_LESS_SUC)

lemma FUN_EQ_LEMMA: "ALL (f::'a::type => bool) (x1::'a::type) x2::'a::type.
   f x1 & ~ f x2 --> x1 ~= x2"
  by (import arithmetic FUN_EQ_LEMMA)

lemma LESS_NOT_SUC: "ALL (m::nat) n::nat. m < n & n ~= Suc m --> Suc m < n"
  by (import arithmetic LESS_NOT_SUC)

lemma LESS_0_CASES: "ALL m::nat. 0 = m | 0 < m"
  by (import arithmetic LESS_0_CASES)

lemma LESS_CASES_IMP: "ALL (m::nat) n::nat. ~ m < n & m ~= n --> n < m"
  by (import arithmetic LESS_CASES_IMP)

lemma LESS_CASES: "ALL (m::nat) n::nat. m < n | n <= m"
  by (import arithmetic LESS_CASES)

lemma LESS_EQ_SUC_REFL: "ALL m::nat. m <= Suc m"
  by (import arithmetic LESS_EQ_SUC_REFL)

lemma LESS_ADD_NONZERO: "ALL (m::nat) n::nat. n ~= 0 --> m < m + n"
  by (import arithmetic LESS_ADD_NONZERO)

lemma LESS_EQ_ANTISYM: "ALL (x::nat) xa::nat. ~ (x < xa & xa <= x)"
  by (import arithmetic LESS_EQ_ANTISYM)

lemma SUB_0: "ALL m::nat. 0 - m = 0 & m - 0 = m"
  by (import arithmetic SUB_0)

lemma SUC_SUB1: "ALL m::nat. Suc m - 1 = m"
  by (import arithmetic SUC_SUB1)

lemma PRE_SUB1: "ALL m::nat. PRE m = m - 1"
  by (import arithmetic PRE_SUB1)

lemma MULT_CLAUSES: "ALL (x::nat) xa::nat.
   0 * x = 0 &
   x * 0 = 0 &
   1 * x = x &
   x * 1 = x & Suc x * xa = x * xa + xa & x * Suc xa = x + x * xa"
  by (import arithmetic MULT_CLAUSES)

lemma PRE_SUB: "ALL (m::nat) n::nat. PRE (m - n) = PRE m - n"
  by (import arithmetic PRE_SUB)

lemma ADD_EQ_1: "ALL (m::nat) n::nat. (m + n = 1) = (m = 1 & n = 0 | m = 0 & n = 1)"
  by (import arithmetic ADD_EQ_1)

lemma ADD_INV_0_EQ: "ALL (m::nat) n::nat. (m + n = m) = (n = 0)"
  by (import arithmetic ADD_INV_0_EQ)

lemma PRE_SUC_EQ: "ALL (m::nat) n::nat. 0 < n --> (m = PRE n) = (Suc m = n)"
  by (import arithmetic PRE_SUC_EQ)

lemma INV_PRE_EQ: "ALL (m::nat) n::nat. 0 < m & 0 < n --> (PRE m = PRE n) = (m = n)"
  by (import arithmetic INV_PRE_EQ)

lemma LESS_SUC_NOT: "ALL (m::nat) n::nat. m < n --> ~ n < Suc m"
  by (import arithmetic LESS_SUC_NOT)

lemma ADD_EQ_SUB: "ALL (m::nat) (n::nat) p::nat. n <= p --> (m + n = p) = (m = p - n)"
  by (import arithmetic ADD_EQ_SUB)

lemma LESS_ADD_1: "ALL (x::nat) xa::nat. xa < x --> (EX xb::nat. x = xa + (xb + 1))"
  by (import arithmetic LESS_ADD_1)

lemma NOT_ODD_EQ_EVEN: "ALL (n::nat) m::nat. Suc (n + n) ~= m + m"
  by (import arithmetic NOT_ODD_EQ_EVEN)

lemma MULT_SUC_EQ: "ALL (p::nat) (m::nat) n::nat. (n * Suc p = m * Suc p) = (n = m)"
  by (import arithmetic MULT_SUC_EQ)

lemma MULT_EXP_MONO: "ALL (p::nat) (q::nat) (n::nat) m::nat.
   (n * Suc q ^ p = m * Suc q ^ p) = (n = m)"
  by (import arithmetic MULT_EXP_MONO)

lemma LESS_ADD_SUC: "ALL (m::nat) n::nat. m < m + Suc n"
  by (import arithmetic LESS_ADD_SUC)

lemma LESS_OR_EQ_ADD: "ALL (n::nat) m::nat. n < m | (EX p::nat. n = p + m)"
  by (import arithmetic LESS_OR_EQ_ADD)

lemma WOP: "(All::((nat => bool) => bool) => bool)
 (%P::nat => bool.
     (op -->::bool => bool => bool) ((Ex::(nat => bool) => bool) P)
      ((Ex::(nat => bool) => bool)
        (%n::nat.
            (op &::bool => bool => bool) (P n)
             ((All::(nat => bool) => bool)
               (%m::nat.
                   (op -->::bool => bool => bool)
                    ((op <::nat => nat => bool) m n)
                    ((Not::bool => bool) (P m)))))))"
  by (import arithmetic WOP)

lemma INV_PRE_LESS: "ALL m>0. ALL n::nat. (PRE m < PRE n) = (m < n)"
  by (import arithmetic INV_PRE_LESS)

lemma INV_PRE_LESS_EQ: "ALL n>0. ALL m::nat. (PRE m <= PRE n) = (m <= n)"
  by (import arithmetic INV_PRE_LESS_EQ)

lemma SUB_EQ_EQ_0: "ALL (m::nat) n::nat. (m - n = m) = (m = 0 | n = 0)"
  by (import arithmetic SUB_EQ_EQ_0)

lemma SUB_LESS_OR: "ALL (m::nat) n::nat. n < m --> n <= m - 1"
  by (import arithmetic SUB_LESS_OR)

lemma LESS_SUB_ADD_LESS: "ALL (n::nat) (m::nat) i::nat. i < n - m --> i + m < n"
  by (import arithmetic LESS_SUB_ADD_LESS)

lemma LESS_EQ_SUB_LESS: "ALL (x::nat) xa::nat. xa <= x --> (ALL c::nat. (x - xa < c) = (x < xa + c))"
  by (import arithmetic LESS_EQ_SUB_LESS)

lemma NOT_SUC_LESS_EQ: "ALL (x::nat) xa::nat. (~ Suc x <= xa) = (xa <= x)"
  by (import arithmetic NOT_SUC_LESS_EQ)

lemma SUB_LESS_EQ_ADD: "ALL (m::nat) p::nat. m <= p --> (ALL n::nat. (p - m <= n) = (p <= m + n))"
  by (import arithmetic SUB_LESS_EQ_ADD)

lemma SUB_CANCEL: "ALL (x::nat) (xa::nat) xb::nat.
   xa <= x & xb <= x --> (x - xa = x - xb) = (xa = xb)"
  by (import arithmetic SUB_CANCEL)

lemma NOT_EXP_0: "ALL (m::nat) n::nat. Suc n ^ m ~= 0"
  by (import arithmetic NOT_EXP_0)

lemma ZERO_LESS_EXP: "ALL (m::nat) n::nat. 0 < Suc n ^ m"
  by (import arithmetic ZERO_LESS_EXP)

lemma ODD_OR_EVEN: "ALL x::nat. EX xa::nat. x = Suc (Suc 0) * xa | x = Suc (Suc 0) * xa + 1"
  by (import arithmetic ODD_OR_EVEN)

lemma LESS_EXP_SUC_MONO: "ALL (n::nat) m::nat. Suc (Suc m) ^ n < Suc (Suc m) ^ Suc n"
  by (import arithmetic LESS_EXP_SUC_MONO)

lemma LESS_LESS_CASES: "ALL (m::nat) n::nat. m = n | m < n | n < m"
  by (import arithmetic LESS_LESS_CASES)

lemma LESS_EQUAL_ADD: "ALL (m::nat) n::nat. m <= n --> (EX p::nat. n = m + p)"
  by (import arithmetic LESS_EQUAL_ADD)

lemma MULT_EQ_1: "ALL (x::nat) y::nat. (x * y = 1) = (x = 1 & y = 1)"
  by (import arithmetic MULT_EQ_1)

consts
  FACT :: "nat => nat" 

specification (FACT) FACT: "FACT 0 = 1 & (ALL n::nat. FACT (Suc n) = Suc n * FACT n)"
  by (import arithmetic FACT)

lemma FACT_LESS: "ALL n::nat. 0 < FACT n"
  by (import arithmetic FACT_LESS)

lemma EVEN_ODD: "ALL n::nat. EVEN n = (~ ODD n)"
  by (import arithmetic EVEN_ODD)

lemma ODD_EVEN: "ALL x::nat. ODD x = (~ EVEN x)"
  by (import arithmetic ODD_EVEN)

lemma EVEN_OR_ODD: "ALL x::nat. EVEN x | ODD x"
  by (import arithmetic EVEN_OR_ODD)

lemma EVEN_AND_ODD: "ALL x::nat. ~ (EVEN x & ODD x)"
  by (import arithmetic EVEN_AND_ODD)

lemma EVEN_ADD: "ALL (m::nat) n::nat. EVEN (m + n) = (EVEN m = EVEN n)"
  by (import arithmetic EVEN_ADD)

lemma EVEN_MULT: "ALL (m::nat) n::nat. EVEN (m * n) = (EVEN m | EVEN n)"
  by (import arithmetic EVEN_MULT)

lemma ODD_ADD: "ALL (m::nat) n::nat. ODD (m + n) = (ODD m ~= ODD n)"
  by (import arithmetic ODD_ADD)

lemma ODD_MULT: "ALL (m::nat) n::nat. ODD (m * n) = (ODD m & ODD n)"
  by (import arithmetic ODD_MULT)

lemma EVEN_DOUBLE: "ALL n::nat. EVEN (2 * n)"
  by (import arithmetic EVEN_DOUBLE)

lemma ODD_DOUBLE: "ALL x::nat. ODD (Suc (2 * x))"
  by (import arithmetic ODD_DOUBLE)

lemma EVEN_ODD_EXISTS: "ALL x::nat.
   (EVEN x --> (EX m::nat. x = 2 * m)) &
   (ODD x --> (EX m::nat. x = Suc (2 * m)))"
  by (import arithmetic EVEN_ODD_EXISTS)

lemma EVEN_EXISTS: "ALL n::nat. EVEN n = (EX m::nat. n = 2 * m)"
  by (import arithmetic EVEN_EXISTS)

lemma ODD_EXISTS: "ALL n::nat. ODD n = (EX m::nat. n = Suc (2 * m))"
  by (import arithmetic ODD_EXISTS)

lemma NOT_SUC_LESS_EQ_0: "ALL x::nat. ~ Suc x <= 0"
  by (import arithmetic NOT_SUC_LESS_EQ_0)

lemma NOT_LEQ: "ALL (x::nat) xa::nat. (~ x <= xa) = (Suc xa <= x)"
  by (import arithmetic NOT_LEQ)

lemma NOT_NUM_EQ: "ALL (x::nat) xa::nat. (x ~= xa) = (Suc x <= xa | Suc xa <= x)"
  by (import arithmetic NOT_NUM_EQ)

lemma NOT_GREATER_EQ: "ALL (x::nat) xa::nat. (~ xa <= x) = (Suc x <= xa)"
  by (import arithmetic NOT_GREATER_EQ)

lemma SUC_ADD_SYM: "ALL (m::nat) n::nat. Suc (m + n) = Suc n + m"
  by (import arithmetic SUC_ADD_SYM)

lemma NOT_SUC_ADD_LESS_EQ: "ALL (m::nat) n::nat. ~ Suc (m + n) <= m"
  by (import arithmetic NOT_SUC_ADD_LESS_EQ)

lemma SUB_LEFT_ADD: "ALL (m::nat) (n::nat) p::nat.
   m + (n - p) = (if n <= p then m else m + n - p)"
  by (import arithmetic SUB_LEFT_ADD)

lemma SUB_RIGHT_ADD: "ALL (m::nat) (n::nat) p::nat. m - n + p = (if m <= n then p else m + p - n)"
  by (import arithmetic SUB_RIGHT_ADD)

lemma SUB_LEFT_SUB: "ALL (m::nat) (n::nat) p::nat.
   m - (n - p) = (if n <= p then m else m + p - n)"
  by (import arithmetic SUB_LEFT_SUB)

lemma SUB_LEFT_SUC: "ALL (m::nat) n::nat. Suc (m - n) = (if m <= n then Suc 0 else Suc m - n)"
  by (import arithmetic SUB_LEFT_SUC)

lemma SUB_LEFT_LESS_EQ: "ALL (m::nat) (n::nat) p::nat. (m <= n - p) = (m + p <= n | m <= 0)"
  by (import arithmetic SUB_LEFT_LESS_EQ)

lemma SUB_RIGHT_LESS_EQ: "ALL (m::nat) (n::nat) p::nat. (m - n <= p) = (m <= n + p)"
  by (import arithmetic SUB_RIGHT_LESS_EQ)

lemma SUB_RIGHT_LESS: "ALL (m::nat) (n::nat) p::nat. (m - n < p) = (m < n + p & 0 < p)"
  by (import arithmetic SUB_RIGHT_LESS)

lemma SUB_RIGHT_GREATER_EQ: "ALL (m::nat) (n::nat) p::nat. (p <= m - n) = (n + p <= m | p <= 0)"
  by (import arithmetic SUB_RIGHT_GREATER_EQ)

lemma SUB_LEFT_GREATER: "ALL (m::nat) (n::nat) p::nat. (n - p < m) = (n < m + p & 0 < m)"
  by (import arithmetic SUB_LEFT_GREATER)

lemma SUB_RIGHT_GREATER: "ALL (m::nat) (n::nat) p::nat. (p < m - n) = (n + p < m)"
  by (import arithmetic SUB_RIGHT_GREATER)

lemma SUB_LEFT_EQ: "ALL (m::nat) (n::nat) p::nat. (m = n - p) = (m + p = n | m <= 0 & n <= p)"
  by (import arithmetic SUB_LEFT_EQ)

lemma SUB_RIGHT_EQ: "ALL (m::nat) (n::nat) p::nat. (m - n = p) = (m = n + p | m <= n & p <= 0)"
  by (import arithmetic SUB_RIGHT_EQ)

lemma LE: "(ALL n::nat. (n <= 0) = (n = 0)) &
(ALL (m::nat) n::nat. (m <= Suc n) = (m = Suc n | m <= n))"
  by (import arithmetic LE)

lemma DA: "ALL (k::nat) n::nat. 0 < n --> (EX (x::nat) q::nat. k = q * n + x & x < n)"
  by (import arithmetic DA)

lemma DIV_LESS_EQ: "ALL n>0. ALL k::nat. k div n <= k"
  by (import arithmetic DIV_LESS_EQ)

lemma DIV_UNIQUE: "ALL (n::nat) (k::nat) q::nat.
   (EX r::nat. k = q * n + r & r < n) --> k div n = q"
  by (import arithmetic DIV_UNIQUE)

lemma MOD_UNIQUE: "ALL (n::nat) (k::nat) r::nat.
   (EX q::nat. k = q * n + r & r < n) --> k mod n = r"
  by (import arithmetic MOD_UNIQUE)

lemma DIV_MULT: "ALL (n::nat) r::nat. r < n --> (ALL q::nat. (q * n + r) div n = q)"
  by (import arithmetic DIV_MULT)

lemma MOD_EQ_0: "ALL n>0. ALL k::nat. k * n mod n = 0"
  by (import arithmetic MOD_EQ_0)

lemma ZERO_MOD: "(All::(nat => bool) => bool)
 (%n::nat.
     (op -->::bool => bool => bool) ((op <::nat => nat => bool) (0::nat) n)
      ((op =::nat => nat => bool) ((op mod::nat => nat => nat) (0::nat) n)
        (0::nat)))"
  by (import arithmetic ZERO_MOD)

lemma ZERO_DIV: "(All::(nat => bool) => bool)
 (%n::nat.
     (op -->::bool => bool => bool) ((op <::nat => nat => bool) (0::nat) n)
      ((op =::nat => nat => bool) ((op div::nat => nat => nat) (0::nat) n)
        (0::nat)))"
  by (import arithmetic ZERO_DIV)

lemma MOD_MULT: "ALL (n::nat) r::nat. r < n --> (ALL q::nat. (q * n + r) mod n = r)"
  by (import arithmetic MOD_MULT)

lemma MOD_TIMES: "ALL n>0. ALL (q::nat) r::nat. (q * n + r) mod n = r mod n"
  by (import arithmetic MOD_TIMES)

lemma MOD_PLUS: "ALL n>0. ALL (j::nat) k::nat. (j mod n + k mod n) mod n = (j + k) mod n"
  by (import arithmetic MOD_PLUS)

lemma MOD_MOD: "ALL n>0. ALL k::nat. k mod n mod n = k mod n"
  by (import arithmetic MOD_MOD)

lemma ADD_DIV_ADD_DIV: "ALL x>0. ALL (xa::nat) r::nat. (xa * x + r) div x = xa + r div x"
  by (import arithmetic ADD_DIV_ADD_DIV)

lemma MOD_MULT_MOD: "ALL (m::nat) n::nat.
   0 < n & 0 < m --> (ALL x::nat. x mod (n * m) mod n = x mod n)"
  by (import arithmetic MOD_MULT_MOD)

lemma DIVMOD_ID: "(All::(nat => bool) => bool)
 (%n::nat.
     (op -->::bool => bool => bool) ((op <::nat => nat => bool) (0::nat) n)
      ((op &::bool => bool => bool)
        ((op =::nat => nat => bool) ((op div::nat => nat => nat) n n)
          (1::nat))
        ((op =::nat => nat => bool) ((op mod::nat => nat => nat) n n)
          (0::nat))))"
  by (import arithmetic DIVMOD_ID)

lemma DIV_DIV_DIV_MULT: "ALL (x::nat) xa::nat.
   0 < x & 0 < xa --> (ALL xb::nat. xb div x div xa = xb div (x * xa))"
  by (import arithmetic DIV_DIV_DIV_MULT)

lemma DIV_P: "ALL (P::nat => bool) (p::nat) q::nat.
   0 < q --> P (p div q) = (EX (k::nat) r::nat. p = k * q + r & r < q & P k)"
  by (import arithmetic DIV_P)

lemma MOD_P: "ALL (P::nat => bool) (p::nat) q::nat.
   0 < q --> P (p mod q) = (EX (k::nat) r::nat. p = k * q + r & r < q & P r)"
  by (import arithmetic MOD_P)

lemma MOD_TIMES2: "ALL n>0. ALL (j::nat) k::nat. j mod n * (k mod n) mod n = j * k mod n"
  by (import arithmetic MOD_TIMES2)

lemma MOD_COMMON_FACTOR: "ALL (n::nat) (p::nat) q::nat.
   0 < n & 0 < q --> n * (p mod q) = n * p mod (n * q)"
  by (import arithmetic MOD_COMMON_FACTOR)

lemma num_case_cong: "ALL (M::nat) (M'::nat) (b::'a::type) f::nat => 'a::type.
   M = M' &
   (M' = 0 --> b = (b'::'a::type)) &
   (ALL n::nat. M' = Suc n --> f n = (f'::nat => 'a::type) n) -->
   nat_case b f M = nat_case b' f' M'"
  by (import arithmetic num_case_cong)

lemma SUC_ELIM_THM: "ALL P::nat => nat => bool.
   (ALL n::nat. P (Suc n) n) = (ALL n>0. P n (n - 1))"
  by (import arithmetic SUC_ELIM_THM)

lemma SUB_ELIM_THM: "(P::nat => bool) ((a::nat) - (b::nat)) =
(ALL x::nat. (b = a + x --> P 0) & (a = b + x --> P x))"
  by (import arithmetic SUB_ELIM_THM)

lemma PRE_ELIM_THM: "(P::nat => bool) (PRE (n::nat)) =
(ALL m::nat. (n = 0 --> P 0) & (n = Suc m --> P m))"
  by (import arithmetic PRE_ELIM_THM)

lemma MULT_INCREASES: "ALL (m::nat) n::nat. 1 < m & 0 < n --> Suc n <= m * n"
  by (import arithmetic MULT_INCREASES)

lemma EXP_ALWAYS_BIG_ENOUGH: "ALL b>1. ALL n::nat. EX m::nat. n <= b ^ m"
  by (import arithmetic EXP_ALWAYS_BIG_ENOUGH)

lemma EXP_EQ_0: "ALL (n::nat) m::nat. (n ^ m = 0) = (n = 0 & 0 < m)"
  by (import arithmetic EXP_EQ_0)

lemma EXP_1: "(All::(nat => bool) => bool)
 (%x::nat.
     (op &::bool => bool => bool)
      ((op =::nat => nat => bool) ((op ^::nat => nat => nat) (1::nat) x)
        (1::nat))
      ((op =::nat => nat => bool) ((op ^::nat => nat => nat) x (1::nat)) x))"
  by (import arithmetic EXP_1)

lemma EXP_EQ_1: "ALL (n::nat) m::nat. (n ^ m = 1) = (n = 1 | m = 0)"
  by (import arithmetic EXP_EQ_1)

lemma MIN_MAX_EQ: "ALL (x::nat) xa::nat. (min x xa = max x xa) = (x = xa)"
  by (import arithmetic MIN_MAX_EQ)

lemma MIN_MAX_LT: "ALL (x::nat) xa::nat. (min x xa < max x xa) = (x ~= xa)"
  by (import arithmetic MIN_MAX_LT)

lemma MIN_MAX_PRED: "ALL (P::nat => bool) (m::nat) n::nat.
   P m & P n --> P (min m n) & P (max m n)"
  by (import arithmetic MIN_MAX_PRED)

lemma MIN_LT: "ALL (x::nat) xa::nat.
   (min xa x < xa) = (xa ~= x & min xa x = x) &
   (min xa x < x) = (xa ~= x & min xa x = xa) &
   (xa < min xa x) = False & (x < min xa x) = False"
  by (import arithmetic MIN_LT)

lemma MAX_LT: "ALL (x::nat) xa::nat.
   (xa < max xa x) = (xa ~= x & max xa x = x) &
   (x < max xa x) = (xa ~= x & max xa x = xa) &
   (max xa x < xa) = False & (max xa x < x) = False"
  by (import arithmetic MAX_LT)

lemma MIN_LE: "ALL (x::nat) xa::nat. min xa x <= xa & min xa x <= x"
  by (import arithmetic MIN_LE)

lemma MAX_LE: "ALL (x::nat) xa::nat. xa <= max xa x & x <= max xa x"
  by (import arithmetic MAX_LE)

lemma MIN_0: "ALL x::nat. min x 0 = 0 & min 0 x = 0"
  by (import arithmetic MIN_0)

lemma MAX_0: "ALL x::nat. max x 0 = x & max 0 x = x"
  by (import arithmetic MAX_0)

lemma EXISTS_GREATEST: "ALL P::nat => bool.
   (Ex P & (EX x::nat. ALL y::nat. x < y --> ~ P y)) =
   (EX x::nat. P x & (ALL y::nat. x < y --> ~ P y))"
  by (import arithmetic EXISTS_GREATEST)

;end_setup

;setup_theory hrat

definition trat_1 :: "nat * nat" where 
  "trat_1 == (0, 0)"

lemma trat_1: "trat_1 = (0, 0)"
  by (import hrat trat_1)

definition trat_inv :: "nat * nat => nat * nat" where 
  "trat_inv == %(x::nat, y::nat). (y, x)"

lemma trat_inv: "ALL (x::nat) y::nat. trat_inv (x, y) = (y, x)"
  by (import hrat trat_inv)

definition trat_add :: "nat * nat => nat * nat => nat * nat" where 
  "trat_add ==
%(x::nat, y::nat) (x'::nat, y'::nat).
   (PRE (Suc x * Suc y' + Suc x' * Suc y), PRE (Suc y * Suc y'))"

lemma trat_add: "ALL (x::nat) (y::nat) (x'::nat) y'::nat.
   trat_add (x, y) (x', y') =
   (PRE (Suc x * Suc y' + Suc x' * Suc y), PRE (Suc y * Suc y'))"
  by (import hrat trat_add)

definition trat_mul :: "nat * nat => nat * nat => nat * nat" where 
  "trat_mul ==
%(x::nat, y::nat) (x'::nat, y'::nat).
   (PRE (Suc x * Suc x'), PRE (Suc y * Suc y'))"

lemma trat_mul: "ALL (x::nat) (y::nat) (x'::nat) y'::nat.
   trat_mul (x, y) (x', y') = (PRE (Suc x * Suc x'), PRE (Suc y * Suc y'))"
  by (import hrat trat_mul)

consts
  trat_sucint :: "nat => nat * nat" 

specification (trat_sucint) trat_sucint: "trat_sucint 0 = trat_1 &
(ALL n::nat. trat_sucint (Suc n) = trat_add (trat_sucint n) trat_1)"
  by (import hrat trat_sucint)

definition trat_eq :: "nat * nat => nat * nat => bool" where 
  "trat_eq ==
%(x::nat, y::nat) (x'::nat, y'::nat). Suc x * Suc y' = Suc x' * Suc y"

lemma trat_eq: "ALL (x::nat) (y::nat) (x'::nat) y'::nat.
   trat_eq (x, y) (x', y') = (Suc x * Suc y' = Suc x' * Suc y)"
  by (import hrat trat_eq)

lemma TRAT_EQ_REFL: "ALL p::nat * nat. trat_eq p p"
  by (import hrat TRAT_EQ_REFL)

lemma TRAT_EQ_SYM: "ALL (p::nat * nat) q::nat * nat. trat_eq p q = trat_eq q p"
  by (import hrat TRAT_EQ_SYM)

lemma TRAT_EQ_TRANS: "ALL (p::nat * nat) (q::nat * nat) r::nat * nat.
   trat_eq p q & trat_eq q r --> trat_eq p r"
  by (import hrat TRAT_EQ_TRANS)

lemma TRAT_EQ_AP: "ALL (p::nat * nat) q::nat * nat. p = q --> trat_eq p q"
  by (import hrat TRAT_EQ_AP)

lemma TRAT_ADD_SYM_EQ: "ALL (h::nat * nat) i::nat * nat. trat_add h i = trat_add i h"
  by (import hrat TRAT_ADD_SYM_EQ)

lemma TRAT_MUL_SYM_EQ: "ALL (h::nat * nat) i::nat * nat. trat_mul h i = trat_mul i h"
  by (import hrat TRAT_MUL_SYM_EQ)

lemma TRAT_INV_WELLDEFINED: "ALL (p::nat * nat) q::nat * nat.
   trat_eq p q --> trat_eq (trat_inv p) (trat_inv q)"
  by (import hrat TRAT_INV_WELLDEFINED)

lemma TRAT_ADD_WELLDEFINED: "ALL (p::nat * nat) (q::nat * nat) r::nat * nat.
   trat_eq p q --> trat_eq (trat_add p r) (trat_add q r)"
  by (import hrat TRAT_ADD_WELLDEFINED)

lemma TRAT_ADD_WELLDEFINED2: "ALL (p1::nat * nat) (p2::nat * nat) (q1::nat * nat) q2::nat * nat.
   trat_eq p1 p2 & trat_eq q1 q2 -->
   trat_eq (trat_add p1 q1) (trat_add p2 q2)"
  by (import hrat TRAT_ADD_WELLDEFINED2)

lemma TRAT_MUL_WELLDEFINED: "ALL (p::nat * nat) (q::nat * nat) r::nat * nat.
   trat_eq p q --> trat_eq (trat_mul p r) (trat_mul q r)"
  by (import hrat TRAT_MUL_WELLDEFINED)

lemma TRAT_MUL_WELLDEFINED2: "ALL (p1::nat * nat) (p2::nat * nat) (q1::nat * nat) q2::nat * nat.
   trat_eq p1 p2 & trat_eq q1 q2 -->
   trat_eq (trat_mul p1 q1) (trat_mul p2 q2)"
  by (import hrat TRAT_MUL_WELLDEFINED2)

lemma TRAT_ADD_SYM: "ALL (h::nat * nat) i::nat * nat. trat_eq (trat_add h i) (trat_add i h)"
  by (import hrat TRAT_ADD_SYM)

lemma TRAT_ADD_ASSOC: "ALL (h::nat * nat) (i::nat * nat) j::nat * nat.
   trat_eq (trat_add h (trat_add i j)) (trat_add (trat_add h i) j)"
  by (import hrat TRAT_ADD_ASSOC)

lemma TRAT_MUL_SYM: "ALL (h::nat * nat) i::nat * nat. trat_eq (trat_mul h i) (trat_mul i h)"
  by (import hrat TRAT_MUL_SYM)

lemma TRAT_MUL_ASSOC: "ALL (h::nat * nat) (i::nat * nat) j::nat * nat.
   trat_eq (trat_mul h (trat_mul i j)) (trat_mul (trat_mul h i) j)"
  by (import hrat TRAT_MUL_ASSOC)

lemma TRAT_LDISTRIB: "ALL (h::nat * nat) (i::nat * nat) j::nat * nat.
   trat_eq (trat_mul h (trat_add i j))
    (trat_add (trat_mul h i) (trat_mul h j))"
  by (import hrat TRAT_LDISTRIB)

lemma TRAT_MUL_LID: "ALL h::nat * nat. trat_eq (trat_mul trat_1 h) h"
  by (import hrat TRAT_MUL_LID)

lemma TRAT_MUL_LINV: "ALL h::nat * nat. trat_eq (trat_mul (trat_inv h) h) trat_1"
  by (import hrat TRAT_MUL_LINV)

lemma TRAT_NOZERO: "ALL (h::nat * nat) i::nat * nat. ~ trat_eq (trat_add h i) h"
  by (import hrat TRAT_NOZERO)

lemma TRAT_ADD_TOTAL: "ALL (h::nat * nat) i::nat * nat.
   trat_eq h i |
   (EX d::nat * nat. trat_eq h (trat_add i d)) |
   (EX d::nat * nat. trat_eq i (trat_add h d))"
  by (import hrat TRAT_ADD_TOTAL)

lemma TRAT_SUCINT_0: "ALL n::nat. trat_eq (trat_sucint n) (n, 0)"
  by (import hrat TRAT_SUCINT_0)

lemma TRAT_ARCH: "ALL h::nat * nat.
   EX (n::nat) d::nat * nat. trat_eq (trat_sucint n) (trat_add h d)"
  by (import hrat TRAT_ARCH)

lemma TRAT_SUCINT: "trat_eq (trat_sucint 0) trat_1 &
(ALL n::nat.
    trat_eq (trat_sucint (Suc n)) (trat_add (trat_sucint n) trat_1))"
  by (import hrat TRAT_SUCINT)

lemma TRAT_EQ_EQUIV: "ALL (p::nat * nat) q::nat * nat. trat_eq p q = (trat_eq p = trat_eq q)"
  by (import hrat TRAT_EQ_EQUIV)

typedef (open) hrat = "{x::nat * nat => bool. EX xa::nat * nat. x = trat_eq xa}" 
  by (rule typedef_helper,import hrat hrat_TY_DEF)

lemmas hrat_TY_DEF = typedef_hol2hol4 [OF type_definition_hrat]

consts
  mk_hrat :: "(nat * nat => bool) => hrat" 
  dest_hrat :: "hrat => nat * nat => bool" 

specification (dest_hrat mk_hrat) hrat_tybij: "(ALL a::hrat. mk_hrat (dest_hrat a) = a) &
(ALL r::nat * nat => bool.
    (EX x::nat * nat. r = trat_eq x) = (dest_hrat (mk_hrat r) = r))"
  by (import hrat hrat_tybij)

definition hrat_1 :: "hrat" where 
  "hrat_1 == mk_hrat (trat_eq trat_1)"

lemma hrat_1: "hrat_1 = mk_hrat (trat_eq trat_1)"
  by (import hrat hrat_1)

definition hrat_inv :: "hrat => hrat" where 
  "hrat_inv == %T1::hrat. mk_hrat (trat_eq (trat_inv (Eps (dest_hrat T1))))"

lemma hrat_inv: "ALL T1::hrat.
   hrat_inv T1 = mk_hrat (trat_eq (trat_inv (Eps (dest_hrat T1))))"
  by (import hrat hrat_inv)

definition hrat_add :: "hrat => hrat => hrat" where 
  "hrat_add ==
%(T1::hrat) T2::hrat.
   mk_hrat (trat_eq (trat_add (Eps (dest_hrat T1)) (Eps (dest_hrat T2))))"

lemma hrat_add: "ALL (T1::hrat) T2::hrat.
   hrat_add T1 T2 =
   mk_hrat (trat_eq (trat_add (Eps (dest_hrat T1)) (Eps (dest_hrat T2))))"
  by (import hrat hrat_add)

definition hrat_mul :: "hrat => hrat => hrat" where 
  "hrat_mul ==
%(T1::hrat) T2::hrat.
   mk_hrat (trat_eq (trat_mul (Eps (dest_hrat T1)) (Eps (dest_hrat T2))))"

lemma hrat_mul: "ALL (T1::hrat) T2::hrat.
   hrat_mul T1 T2 =
   mk_hrat (trat_eq (trat_mul (Eps (dest_hrat T1)) (Eps (dest_hrat T2))))"
  by (import hrat hrat_mul)

definition hrat_sucint :: "nat => hrat" where 
  "hrat_sucint == %T1::nat. mk_hrat (trat_eq (trat_sucint T1))"

lemma hrat_sucint: "ALL T1::nat. hrat_sucint T1 = mk_hrat (trat_eq (trat_sucint T1))"
  by (import hrat hrat_sucint)

lemma HRAT_ADD_SYM: "ALL (h::hrat) i::hrat. hrat_add h i = hrat_add i h"
  by (import hrat HRAT_ADD_SYM)

lemma HRAT_ADD_ASSOC: "ALL (h::hrat) (i::hrat) j::hrat.
   hrat_add h (hrat_add i j) = hrat_add (hrat_add h i) j"
  by (import hrat HRAT_ADD_ASSOC)

lemma HRAT_MUL_SYM: "ALL (h::hrat) i::hrat. hrat_mul h i = hrat_mul i h"
  by (import hrat HRAT_MUL_SYM)

lemma HRAT_MUL_ASSOC: "ALL (h::hrat) (i::hrat) j::hrat.
   hrat_mul h (hrat_mul i j) = hrat_mul (hrat_mul h i) j"
  by (import hrat HRAT_MUL_ASSOC)

lemma HRAT_LDISTRIB: "ALL (h::hrat) (i::hrat) j::hrat.
   hrat_mul h (hrat_add i j) = hrat_add (hrat_mul h i) (hrat_mul h j)"
  by (import hrat HRAT_LDISTRIB)

lemma HRAT_MUL_LID: "ALL h::hrat. hrat_mul hrat_1 h = h"
  by (import hrat HRAT_MUL_LID)

lemma HRAT_MUL_LINV: "ALL h::hrat. hrat_mul (hrat_inv h) h = hrat_1"
  by (import hrat HRAT_MUL_LINV)

lemma HRAT_NOZERO: "ALL (h::hrat) i::hrat. hrat_add h i ~= h"
  by (import hrat HRAT_NOZERO)

lemma HRAT_ADD_TOTAL: "ALL (h::hrat) i::hrat.
   h = i | (EX x::hrat. h = hrat_add i x) | (EX x::hrat. i = hrat_add h x)"
  by (import hrat HRAT_ADD_TOTAL)

lemma HRAT_ARCH: "ALL h::hrat. EX (x::nat) xa::hrat. hrat_sucint x = hrat_add h xa"
  by (import hrat HRAT_ARCH)

lemma HRAT_SUCINT: "hrat_sucint 0 = hrat_1 &
(ALL x::nat. hrat_sucint (Suc x) = hrat_add (hrat_sucint x) hrat_1)"
  by (import hrat HRAT_SUCINT)

;end_setup

;setup_theory hreal

definition hrat_lt :: "hrat => hrat => bool" where 
  "hrat_lt == %(x::hrat) y::hrat. EX d::hrat. y = hrat_add x d"

lemma hrat_lt: "ALL (x::hrat) y::hrat. hrat_lt x y = (EX d::hrat. y = hrat_add x d)"
  by (import hreal hrat_lt)

lemma HRAT_LT_REFL: "ALL x::hrat. ~ hrat_lt x x"
  by (import hreal HRAT_LT_REFL)

lemma HRAT_LT_TRANS: "ALL (x::hrat) (y::hrat) z::hrat. hrat_lt x y & hrat_lt y z --> hrat_lt x z"
  by (import hreal HRAT_LT_TRANS)

lemma HRAT_LT_ANTISYM: "ALL (x::hrat) y::hrat. ~ (hrat_lt x y & hrat_lt y x)"
  by (import hreal HRAT_LT_ANTISYM)

lemma HRAT_LT_TOTAL: "ALL (x::hrat) y::hrat. x = y | hrat_lt x y | hrat_lt y x"
  by (import hreal HRAT_LT_TOTAL)

lemma HRAT_MUL_RID: "ALL x::hrat. hrat_mul x hrat_1 = x"
  by (import hreal HRAT_MUL_RID)

lemma HRAT_MUL_RINV: "ALL x::hrat. hrat_mul x (hrat_inv x) = hrat_1"
  by (import hreal HRAT_MUL_RINV)

lemma HRAT_RDISTRIB: "ALL (x::hrat) (y::hrat) z::hrat.
   hrat_mul (hrat_add x y) z = hrat_add (hrat_mul x z) (hrat_mul y z)"
  by (import hreal HRAT_RDISTRIB)

lemma HRAT_LT_ADDL: "ALL (x::hrat) y::hrat. hrat_lt x (hrat_add x y)"
  by (import hreal HRAT_LT_ADDL)

lemma HRAT_LT_ADDR: "ALL (x::hrat) xa::hrat. hrat_lt xa (hrat_add x xa)"
  by (import hreal HRAT_LT_ADDR)

lemma HRAT_LT_GT: "ALL (x::hrat) y::hrat. hrat_lt x y --> ~ hrat_lt y x"
  by (import hreal HRAT_LT_GT)

lemma HRAT_LT_NE: "ALL (x::hrat) y::hrat. hrat_lt x y --> x ~= y"
  by (import hreal HRAT_LT_NE)

lemma HRAT_EQ_LADD: "ALL (x::hrat) (y::hrat) z::hrat. (hrat_add x y = hrat_add x z) = (y = z)"
  by (import hreal HRAT_EQ_LADD)

lemma HRAT_EQ_LMUL: "ALL (x::hrat) (y::hrat) z::hrat. (hrat_mul x y = hrat_mul x z) = (y = z)"
  by (import hreal HRAT_EQ_LMUL)

lemma HRAT_LT_ADD2: "ALL (u::hrat) (v::hrat) (x::hrat) y::hrat.
   hrat_lt u x & hrat_lt v y --> hrat_lt (hrat_add u v) (hrat_add x y)"
  by (import hreal HRAT_LT_ADD2)

lemma HRAT_LT_LADD: "ALL (x::hrat) (y::hrat) z::hrat.
   hrat_lt (hrat_add z x) (hrat_add z y) = hrat_lt x y"
  by (import hreal HRAT_LT_LADD)

lemma HRAT_LT_RADD: "ALL (x::hrat) (y::hrat) z::hrat.
   hrat_lt (hrat_add x z) (hrat_add y z) = hrat_lt x y"
  by (import hreal HRAT_LT_RADD)

lemma HRAT_LT_MUL2: "ALL (u::hrat) (v::hrat) (x::hrat) y::hrat.
   hrat_lt u x & hrat_lt v y --> hrat_lt (hrat_mul u v) (hrat_mul x y)"
  by (import hreal HRAT_LT_MUL2)

lemma HRAT_LT_LMUL: "ALL (x::hrat) (y::hrat) z::hrat.
   hrat_lt (hrat_mul z x) (hrat_mul z y) = hrat_lt x y"
  by (import hreal HRAT_LT_LMUL)

lemma HRAT_LT_RMUL: "ALL (x::hrat) (y::hrat) z::hrat.
   hrat_lt (hrat_mul x z) (hrat_mul y z) = hrat_lt x y"
  by (import hreal HRAT_LT_RMUL)

lemma HRAT_LT_LMUL1: "ALL (x::hrat) y::hrat. hrat_lt (hrat_mul x y) y = hrat_lt x hrat_1"
  by (import hreal HRAT_LT_LMUL1)

lemma HRAT_LT_RMUL1: "ALL (x::hrat) y::hrat. hrat_lt (hrat_mul x y) x = hrat_lt y hrat_1"
  by (import hreal HRAT_LT_RMUL1)

lemma HRAT_GT_LMUL1: "ALL (x::hrat) y::hrat. hrat_lt y (hrat_mul x y) = hrat_lt hrat_1 x"
  by (import hreal HRAT_GT_LMUL1)

lemma HRAT_LT_L1: "ALL (x::hrat) y::hrat.
   hrat_lt (hrat_mul (hrat_inv x) y) hrat_1 = hrat_lt y x"
  by (import hreal HRAT_LT_L1)

lemma HRAT_LT_R1: "ALL (x::hrat) y::hrat.
   hrat_lt (hrat_mul x (hrat_inv y)) hrat_1 = hrat_lt x y"
  by (import hreal HRAT_LT_R1)

lemma HRAT_GT_L1: "ALL (x::hrat) y::hrat.
   hrat_lt hrat_1 (hrat_mul (hrat_inv x) y) = hrat_lt x y"
  by (import hreal HRAT_GT_L1)

lemma HRAT_INV_MUL: "ALL (x::hrat) y::hrat.
   hrat_inv (hrat_mul x y) = hrat_mul (hrat_inv x) (hrat_inv y)"
  by (import hreal HRAT_INV_MUL)

lemma HRAT_UP: "ALL x::hrat. Ex (hrat_lt x)"
  by (import hreal HRAT_UP)

lemma HRAT_DOWN: "ALL x::hrat. EX xa::hrat. hrat_lt xa x"
  by (import hreal HRAT_DOWN)

lemma HRAT_DOWN2: "ALL (x::hrat) y::hrat. EX xa::hrat. hrat_lt xa x & hrat_lt xa y"
  by (import hreal HRAT_DOWN2)

lemma HRAT_MEAN: "ALL (x::hrat) y::hrat.
   hrat_lt x y --> (EX xa::hrat. hrat_lt x xa & hrat_lt xa y)"
  by (import hreal HRAT_MEAN)

definition isacut :: "(hrat => bool) => bool" where 
  "isacut ==
%C::hrat => bool.
   Ex C &
   (EX x::hrat. ~ C x) &
   (ALL (x::hrat) y::hrat. C x & hrat_lt y x --> C y) &
   (ALL x::hrat. C x --> (EX y::hrat. C y & hrat_lt x y))"

lemma isacut: "ALL C::hrat => bool.
   isacut C =
   (Ex C &
    (EX x::hrat. ~ C x) &
    (ALL (x::hrat) y::hrat. C x & hrat_lt y x --> C y) &
    (ALL x::hrat. C x --> (EX y::hrat. C y & hrat_lt x y)))"
  by (import hreal isacut)

definition cut_of_hrat :: "hrat => hrat => bool" where 
  "cut_of_hrat == %(x::hrat) y::hrat. hrat_lt y x"

lemma cut_of_hrat: "ALL x::hrat. cut_of_hrat x = (%y::hrat. hrat_lt y x)"
  by (import hreal cut_of_hrat)

lemma ISACUT_HRAT: "ALL h::hrat. isacut (cut_of_hrat h)"
  by (import hreal ISACUT_HRAT)

typedef (open) hreal = "Collect isacut" 
  by (rule typedef_helper,import hreal hreal_TY_DEF)

lemmas hreal_TY_DEF = typedef_hol2hol4 [OF type_definition_hreal]

consts
  hreal :: "(hrat => bool) => hreal" 
  cut :: "hreal => hrat => bool" 

specification (cut hreal) hreal_tybij: "(ALL a::hreal. hreal (hreal.cut a) = a) &
(ALL r::hrat => bool. isacut r = (hreal.cut (hreal r) = r))"
  by (import hreal hreal_tybij)

lemma EQUAL_CUTS: "ALL (X::hreal) Y::hreal. hreal.cut X = hreal.cut Y --> X = Y"
  by (import hreal EQUAL_CUTS)

lemma CUT_ISACUT: "ALL x::hreal. isacut (hreal.cut x)"
  by (import hreal CUT_ISACUT)

lemma CUT_NONEMPTY: "ALL x::hreal. Ex (hreal.cut x)"
  by (import hreal CUT_NONEMPTY)

lemma CUT_BOUNDED: "ALL x::hreal. EX xa::hrat. ~ hreal.cut x xa"
  by (import hreal CUT_BOUNDED)

lemma CUT_DOWN: "ALL (x::hreal) (xa::hrat) xb::hrat.
   hreal.cut x xa & hrat_lt xb xa --> hreal.cut x xb"
  by (import hreal CUT_DOWN)

lemma CUT_UP: "ALL (x::hreal) xa::hrat.
   hreal.cut x xa --> (EX y::hrat. hreal.cut x y & hrat_lt xa y)"
  by (import hreal CUT_UP)

lemma CUT_UBOUND: "ALL (x::hreal) (xa::hrat) xb::hrat.
   ~ hreal.cut x xa & hrat_lt xa xb --> ~ hreal.cut x xb"
  by (import hreal CUT_UBOUND)

lemma CUT_STRADDLE: "ALL (X::hreal) (x::hrat) y::hrat.
   hreal.cut X x & ~ hreal.cut X y --> hrat_lt x y"
  by (import hreal CUT_STRADDLE)

lemma CUT_NEARTOP_ADD: "ALL (X::hreal) e::hrat.
   EX x::hrat. hreal.cut X x & ~ hreal.cut X (hrat_add x e)"
  by (import hreal CUT_NEARTOP_ADD)

lemma CUT_NEARTOP_MUL: "ALL (X::hreal) u::hrat.
   hrat_lt hrat_1 u -->
   (EX x::hrat. hreal.cut X x & ~ hreal.cut X (hrat_mul u x))"
  by (import hreal CUT_NEARTOP_MUL)

definition hreal_1 :: "hreal" where 
  "hreal_1 == hreal (cut_of_hrat hrat_1)"

lemma hreal_1: "hreal_1 = hreal (cut_of_hrat hrat_1)"
  by (import hreal hreal_1)

definition hreal_add :: "hreal => hreal => hreal" where 
  "hreal_add ==
%(X::hreal) Y::hreal.
   hreal
    (%w::hrat.
        EX (x::hrat) y::hrat.
           w = hrat_add x y & hreal.cut X x & hreal.cut Y y)"

lemma hreal_add: "ALL (X::hreal) Y::hreal.
   hreal_add X Y =
   hreal
    (%w::hrat.
        EX (x::hrat) y::hrat.
           w = hrat_add x y & hreal.cut X x & hreal.cut Y y)"
  by (import hreal hreal_add)

definition hreal_mul :: "hreal => hreal => hreal" where 
  "hreal_mul ==
%(X::hreal) Y::hreal.
   hreal
    (%w::hrat.
        EX (x::hrat) y::hrat.
           w = hrat_mul x y & hreal.cut X x & hreal.cut Y y)"

lemma hreal_mul: "ALL (X::hreal) Y::hreal.
   hreal_mul X Y =
   hreal
    (%w::hrat.
        EX (x::hrat) y::hrat.
           w = hrat_mul x y & hreal.cut X x & hreal.cut Y y)"
  by (import hreal hreal_mul)

definition hreal_inv :: "hreal => hreal" where 
  "hreal_inv ==
%X::hreal.
   hreal
    (%w::hrat.
        EX d::hrat.
           hrat_lt d hrat_1 &
           (ALL x::hrat. hreal.cut X x --> hrat_lt (hrat_mul w x) d))"

lemma hreal_inv: "ALL X::hreal.
   hreal_inv X =
   hreal
    (%w::hrat.
        EX d::hrat.
           hrat_lt d hrat_1 &
           (ALL x::hrat. hreal.cut X x --> hrat_lt (hrat_mul w x) d))"
  by (import hreal hreal_inv)

definition hreal_sup :: "(hreal => bool) => hreal" where 
  "hreal_sup ==
%P::hreal => bool. hreal (%w::hrat. EX X::hreal. P X & hreal.cut X w)"

lemma hreal_sup: "ALL P::hreal => bool.
   hreal_sup P = hreal (%w::hrat. EX X::hreal. P X & hreal.cut X w)"
  by (import hreal hreal_sup)

definition hreal_lt :: "hreal => hreal => bool" where 
  "hreal_lt ==
%(X::hreal) Y::hreal.
   X ~= Y & (ALL x::hrat. hreal.cut X x --> hreal.cut Y x)"

lemma hreal_lt: "ALL (X::hreal) Y::hreal.
   hreal_lt X Y = (X ~= Y & (ALL x::hrat. hreal.cut X x --> hreal.cut Y x))"
  by (import hreal hreal_lt)

lemma HREAL_INV_ISACUT: "ALL X::hreal.
   isacut
    (%w::hrat.
        EX d::hrat.
           hrat_lt d hrat_1 &
           (ALL x::hrat. hreal.cut X x --> hrat_lt (hrat_mul w x) d))"
  by (import hreal HREAL_INV_ISACUT)

lemma HREAL_ADD_ISACUT: "ALL (X::hreal) Y::hreal.
   isacut
    (%w::hrat.
        EX (x::hrat) y::hrat.
           w = hrat_add x y & hreal.cut X x & hreal.cut Y y)"
  by (import hreal HREAL_ADD_ISACUT)

lemma HREAL_MUL_ISACUT: "ALL (X::hreal) Y::hreal.
   isacut
    (%w::hrat.
        EX (x::hrat) y::hrat.
           w = hrat_mul x y & hreal.cut X x & hreal.cut Y y)"
  by (import hreal HREAL_MUL_ISACUT)

lemma HREAL_ADD_SYM: "ALL (X::hreal) Y::hreal. hreal_add X Y = hreal_add Y X"
  by (import hreal HREAL_ADD_SYM)

lemma HREAL_MUL_SYM: "ALL (X::hreal) Y::hreal. hreal_mul X Y = hreal_mul Y X"
  by (import hreal HREAL_MUL_SYM)

lemma HREAL_ADD_ASSOC: "ALL (X::hreal) (Y::hreal) Z::hreal.
   hreal_add X (hreal_add Y Z) = hreal_add (hreal_add X Y) Z"
  by (import hreal HREAL_ADD_ASSOC)

lemma HREAL_MUL_ASSOC: "ALL (X::hreal) (Y::hreal) Z::hreal.
   hreal_mul X (hreal_mul Y Z) = hreal_mul (hreal_mul X Y) Z"
  by (import hreal HREAL_MUL_ASSOC)

lemma HREAL_LDISTRIB: "ALL (X::hreal) (Y::hreal) Z::hreal.
   hreal_mul X (hreal_add Y Z) = hreal_add (hreal_mul X Y) (hreal_mul X Z)"
  by (import hreal HREAL_LDISTRIB)

lemma HREAL_MUL_LID: "ALL X::hreal. hreal_mul hreal_1 X = X"
  by (import hreal HREAL_MUL_LID)

lemma HREAL_MUL_LINV: "ALL X::hreal. hreal_mul (hreal_inv X) X = hreal_1"
  by (import hreal HREAL_MUL_LINV)

lemma HREAL_NOZERO: "ALL (X::hreal) Y::hreal. hreal_add X Y ~= X"
  by (import hreal HREAL_NOZERO)

definition hreal_sub :: "hreal => hreal => hreal" where 
  "hreal_sub ==
%(Y::hreal) X::hreal.
   hreal
    (%w::hrat. EX x::hrat. ~ hreal.cut X x & hreal.cut Y (hrat_add x w))"

lemma hreal_sub: "ALL (Y::hreal) X::hreal.
   hreal_sub Y X =
   hreal
    (%w::hrat. EX x::hrat. ~ hreal.cut X x & hreal.cut Y (hrat_add x w))"
  by (import hreal hreal_sub)

lemma HREAL_LT_LEMMA: "ALL (X::hreal) Y::hreal.
   hreal_lt X Y --> (EX x::hrat. ~ hreal.cut X x & hreal.cut Y x)"
  by (import hreal HREAL_LT_LEMMA)

lemma HREAL_SUB_ISACUT: "ALL (X::hreal) Y::hreal.
   hreal_lt X Y -->
   isacut
    (%w::hrat. EX x::hrat. ~ hreal.cut X x & hreal.cut Y (hrat_add x w))"
  by (import hreal HREAL_SUB_ISACUT)

lemma HREAL_SUB_ADD: "ALL (X::hreal) Y::hreal. hreal_lt X Y --> hreal_add (hreal_sub Y X) X = Y"
  by (import hreal HREAL_SUB_ADD)

lemma HREAL_LT_TOTAL: "ALL (X::hreal) Y::hreal. X = Y | hreal_lt X Y | hreal_lt Y X"
  by (import hreal HREAL_LT_TOTAL)

lemma HREAL_LT: "ALL (X::hreal) Y::hreal. hreal_lt X Y = (EX D::hreal. Y = hreal_add X D)"
  by (import hreal HREAL_LT)

lemma HREAL_ADD_TOTAL: "ALL (X::hreal) Y::hreal.
   X = Y |
   (EX D::hreal. Y = hreal_add X D) | (EX D::hreal. X = hreal_add Y D)"
  by (import hreal HREAL_ADD_TOTAL)

lemma HREAL_SUP_ISACUT: "ALL P::hreal => bool.
   Ex P & (EX Y::hreal. ALL X::hreal. P X --> hreal_lt X Y) -->
   isacut (%w::hrat. EX X::hreal. P X & hreal.cut X w)"
  by (import hreal HREAL_SUP_ISACUT)

lemma HREAL_SUP: "ALL P::hreal => bool.
   Ex P & (EX Y::hreal. ALL X::hreal. P X --> hreal_lt X Y) -->
   (ALL Y::hreal.
       (EX X::hreal. P X & hreal_lt Y X) = hreal_lt Y (hreal_sup P))"
  by (import hreal HREAL_SUP)

;end_setup

;setup_theory numeral

lemma numeral_suc: "Suc ALT_ZERO = NUMERAL_BIT1 ALT_ZERO &
(ALL x::nat. Suc (NUMERAL_BIT1 x) = NUMERAL_BIT2 x) &
(ALL x::nat. Suc (NUMERAL_BIT2 x) = NUMERAL_BIT1 (Suc x))"
  by (import numeral numeral_suc)

definition iZ :: "nat => nat" where 
  "iZ == %x::nat. x"

lemma iZ: "ALL x::nat. iZ x = x"
  by (import numeral iZ)

definition iiSUC :: "nat => nat" where 
  "iiSUC == %n::nat. Suc (Suc n)"

lemma iiSUC: "ALL n::nat. iiSUC n = Suc (Suc n)"
  by (import numeral iiSUC)

lemma numeral_distrib: "(op &::bool => bool => bool)
 ((All::(nat => bool) => bool)
   (%x::nat.
       (op =::nat => nat => bool) ((op +::nat => nat => nat) (0::nat) x) x))
 ((op &::bool => bool => bool)
   ((All::(nat => bool) => bool)
     (%x::nat.
         (op =::nat => nat => bool) ((op +::nat => nat => nat) x (0::nat))
          x))
   ((op &::bool => bool => bool)
     ((All::(nat => bool) => bool)
       (%x::nat.
           (All::(nat => bool) => bool)
            (%xa::nat.
                (op =::nat => nat => bool)
                 ((op +::nat => nat => nat) ((NUMERAL::nat => nat) x)
                   ((NUMERAL::nat => nat) xa))
                 ((NUMERAL::nat => nat)
                   ((iZ::nat => nat) ((op +::nat => nat => nat) x xa))))))
     ((op &::bool => bool => bool)
       ((All::(nat => bool) => bool)
         (%x::nat.
             (op =::nat => nat => bool)
              ((op *::nat => nat => nat) (0::nat) x) (0::nat)))
       ((op &::bool => bool => bool)
         ((All::(nat => bool) => bool)
           (%x::nat.
               (op =::nat => nat => bool)
                ((op *::nat => nat => nat) x (0::nat)) (0::nat)))
         ((op &::bool => bool => bool)
           ((All::(nat => bool) => bool)
             (%x::nat.
                 (All::(nat => bool) => bool)
                  (%xa::nat.
                      (op =::nat => nat => bool)
                       ((op *::nat => nat => nat) ((NUMERAL::nat => nat) x)
                         ((NUMERAL::nat => nat) xa))
                       ((NUMERAL::nat => nat)
                         ((op *::nat => nat => nat) x xa)))))
           ((op &::bool => bool => bool)
             ((All::(nat => bool) => bool)
               (%x::nat.
                   (op =::nat => nat => bool)
                    ((op -::nat => nat => nat) (0::nat) x) (0::nat)))
             ((op &::bool => bool => bool)
               ((All::(nat => bool) => bool)
                 (%x::nat.
                     (op =::nat => nat => bool)
                      ((op -::nat => nat => nat) x (0::nat)) x))
               ((op &::bool => bool => bool)
                 ((All::(nat => bool) => bool)
                   (%x::nat.
                       (All::(nat => bool) => bool)
                        (%xa::nat.
                            (op =::nat => nat => bool)
                             ((op -::nat => nat => nat)
                               ((NUMERAL::nat => nat) x)
                               ((NUMERAL::nat => nat) xa))
                             ((NUMERAL::nat => nat)
                               ((op -::nat => nat => nat) x xa)))))
                 ((op &::bool => bool => bool)
                   ((All::(nat => bool) => bool)
                     (%x::nat.
                         (op =::nat => nat => bool)
                          ((op ^::nat => nat => nat) (0::nat)
                            ((NUMERAL::nat => nat)
                              ((NUMERAL_BIT1::nat => nat) x)))
                          (0::nat)))
                   ((op &::bool => bool => bool)
                     ((All::(nat => bool) => bool)
                       (%x::nat.
                           (op =::nat => nat => bool)
                            ((op ^::nat => nat => nat) (0::nat)
                              ((NUMERAL::nat => nat)
                                ((NUMERAL_BIT2::nat => nat) x)))
                            (0::nat)))
                     ((op &::bool => bool => bool)
                       ((All::(nat => bool) => bool)
                         (%x::nat.
                             (op =::nat => nat => bool)
                              ((op ^::nat => nat => nat) x (0::nat))
                              (1::nat)))
                       ((op &::bool => bool => bool)
                         ((All::(nat => bool) => bool)
                           (%x::nat.
                               (All::(nat => bool) => bool)
                                (%xa::nat.
                                    (op =::nat => nat => bool)
                                     ((op ^::nat => nat => nat)
 ((NUMERAL::nat => nat) x) ((NUMERAL::nat => nat) xa))
                                     ((NUMERAL::nat => nat)
 ((op ^::nat => nat => nat) x xa)))))
                         ((op &::bool => bool => bool)
                           ((op =::nat => nat => bool)
                             ((Suc::nat => nat) (0::nat)) (1::nat))
                           ((op &::bool => bool => bool)
                             ((All::(nat => bool) => bool)
                               (%x::nat.
                                   (op =::nat => nat => bool)
                                    ((Suc::nat => nat)
((NUMERAL::nat => nat) x))
                                    ((NUMERAL::nat => nat)
((Suc::nat => nat) x))))
                             ((op &::bool => bool => bool)
                               ((op =::nat => nat => bool)
                                 ((PRE::nat => nat) (0::nat)) (0::nat))
                               ((op &::bool => bool => bool)
                                 ((All::(nat => bool) => bool)
                                   (%x::nat.
 (op =::nat => nat => bool) ((PRE::nat => nat) ((NUMERAL::nat => nat) x))
  ((NUMERAL::nat => nat) ((PRE::nat => nat) x))))
                                 ((op &::bool => bool => bool)
                                   ((All::(nat => bool) => bool)
                                     (%x::nat.
   (op =::bool => bool => bool)
    ((op =::nat => nat => bool) ((NUMERAL::nat => nat) x) (0::nat))
    ((op =::nat => nat => bool) x (ALT_ZERO::nat))))
                                   ((op &::bool => bool => bool)
                                     ((All::(nat => bool) => bool)
 (%x::nat.
     (op =::bool => bool => bool)
      ((op =::nat => nat => bool) (0::nat) ((NUMERAL::nat => nat) x))
      ((op =::nat => nat => bool) x (ALT_ZERO::nat))))
                                     ((op &::bool => bool => bool)
 ((All::(nat => bool) => bool)
   (%x::nat.
       (All::(nat => bool) => bool)
        (%xa::nat.
            (op =::bool => bool => bool)
             ((op =::nat => nat => bool) ((NUMERAL::nat => nat) x)
               ((NUMERAL::nat => nat) xa))
             ((op =::nat => nat => bool) x xa))))
 ((op &::bool => bool => bool)
   ((All::(nat => bool) => bool)
     (%x::nat.
         (op =::bool => bool => bool)
          ((op <::nat => nat => bool) x (0::nat)) (False::bool)))
   ((op &::bool => bool => bool)
     ((All::(nat => bool) => bool)
       (%x::nat.
           (op =::bool => bool => bool)
            ((op <::nat => nat => bool) (0::nat) ((NUMERAL::nat => nat) x))
            ((op <::nat => nat => bool) (ALT_ZERO::nat) x)))
     ((op &::bool => bool => bool)
       ((All::(nat => bool) => bool)
         (%x::nat.
             (All::(nat => bool) => bool)
              (%xa::nat.
                  (op =::bool => bool => bool)
                   ((op <::nat => nat => bool) ((NUMERAL::nat => nat) x)
                     ((NUMERAL::nat => nat) xa))
                   ((op <::nat => nat => bool) x xa))))
       ((op &::bool => bool => bool)
         ((All::(nat => bool) => bool)
           (%x::nat.
               (op =::bool => bool => bool)
                ((op <::nat => nat => bool) x (0::nat)) (False::bool)))
         ((op &::bool => bool => bool)
           ((All::(nat => bool) => bool)
             (%x::nat.
                 (op =::bool => bool => bool)
                  ((op <::nat => nat => bool) (0::nat)
                    ((NUMERAL::nat => nat) x))
                  ((op <::nat => nat => bool) (ALT_ZERO::nat) x)))
           ((op &::bool => bool => bool)
             ((All::(nat => bool) => bool)
               (%x::nat.
                   (All::(nat => bool) => bool)
                    (%xa::nat.
                        (op =::bool => bool => bool)
                         ((op <::nat => nat => bool)
                           ((NUMERAL::nat => nat) xa)
                           ((NUMERAL::nat => nat) x))
                         ((op <::nat => nat => bool) xa x))))
             ((op &::bool => bool => bool)
               ((All::(nat => bool) => bool)
                 (%x::nat.
                     (op =::bool => bool => bool)
                      ((op <=::nat => nat => bool) (0::nat) x)
                      (True::bool)))
               ((op &::bool => bool => bool)
                 ((All::(nat => bool) => bool)
                   (%x::nat.
                       (op =::bool => bool => bool)
                        ((op <=::nat => nat => bool)
                          ((NUMERAL::nat => nat) x) (0::nat))
                        ((op <=::nat => nat => bool) x (ALT_ZERO::nat))))
                 ((op &::bool => bool => bool)
                   ((All::(nat => bool) => bool)
                     (%x::nat.
                         (All::(nat => bool) => bool)
                          (%xa::nat.
                              (op =::bool => bool => bool)
                               ((op <=::nat => nat => bool)
                                 ((NUMERAL::nat => nat) x)
                                 ((NUMERAL::nat => nat) xa))
                               ((op <=::nat => nat => bool) x xa))))
                   ((op &::bool => bool => bool)
                     ((All::(nat => bool) => bool)
                       (%x::nat.
                           (op =::bool => bool => bool)
                            ((op <=::nat => nat => bool) (0::nat) x)
                            (True::bool)))
                     ((op &::bool => bool => bool)
                       ((All::(nat => bool) => bool)
                         (%x::nat.
                             (op =::bool => bool => bool)
                              ((op <=::nat => nat => bool) x (0::nat))
                              ((op =::nat => nat => bool) x (0::nat))))
                       ((op &::bool => bool => bool)
                         ((All::(nat => bool) => bool)
                           (%x::nat.
                               (All::(nat => bool) => bool)
                                (%xa::nat.
                                    (op =::bool => bool => bool)
                                     ((op <=::nat => nat => bool)
 ((NUMERAL::nat => nat) xa) ((NUMERAL::nat => nat) x))
                                     ((op <=::nat => nat => bool) xa x))))
                         ((op &::bool => bool => bool)
                           ((All::(nat => bool) => bool)
                             (%x::nat.
                                 (op =::bool => bool => bool)
                                  ((ODD::nat => bool)
                                    ((NUMERAL::nat => nat) x))
                                  ((ODD::nat => bool) x)))
                           ((op &::bool => bool => bool)
                             ((All::(nat => bool) => bool)
                               (%x::nat.
                                   (op =::bool => bool => bool)
                                    ((EVEN::nat => bool)
((NUMERAL::nat => nat) x))
                                    ((EVEN::nat => bool) x)))
                             ((op &::bool => bool => bool)
                               ((Not::bool => bool)
                                 ((ODD::nat => bool) (0::nat)))
                               ((EVEN::nat => bool)
                                 (0::nat))))))))))))))))))))))))))))))))))))"
  by (import numeral numeral_distrib)

lemma numeral_iisuc: "iiSUC ALT_ZERO = NUMERAL_BIT2 ALT_ZERO &
iiSUC (NUMERAL_BIT1 (n::nat)) = NUMERAL_BIT1 (Suc n) &
iiSUC (NUMERAL_BIT2 n) = NUMERAL_BIT2 (Suc n)"
  by (import numeral numeral_iisuc)

lemma numeral_add: "ALL (x::nat) xa::nat.
   iZ (ALT_ZERO + x) = x &
   iZ (x + ALT_ZERO) = x &
   iZ (NUMERAL_BIT1 x + NUMERAL_BIT1 xa) = NUMERAL_BIT2 (iZ (x + xa)) &
   iZ (NUMERAL_BIT1 x + NUMERAL_BIT2 xa) = NUMERAL_BIT1 (Suc (x + xa)) &
   iZ (NUMERAL_BIT2 x + NUMERAL_BIT1 xa) = NUMERAL_BIT1 (Suc (x + xa)) &
   iZ (NUMERAL_BIT2 x + NUMERAL_BIT2 xa) = NUMERAL_BIT2 (Suc (x + xa)) &
   Suc (ALT_ZERO + x) = Suc x &
   Suc (x + ALT_ZERO) = Suc x &
   Suc (NUMERAL_BIT1 x + NUMERAL_BIT1 xa) = NUMERAL_BIT1 (Suc (x + xa)) &
   Suc (NUMERAL_BIT1 x + NUMERAL_BIT2 xa) = NUMERAL_BIT2 (Suc (x + xa)) &
   Suc (NUMERAL_BIT2 x + NUMERAL_BIT1 xa) = NUMERAL_BIT2 (Suc (x + xa)) &
   Suc (NUMERAL_BIT2 x + NUMERAL_BIT2 xa) = NUMERAL_BIT1 (iiSUC (x + xa)) &
   iiSUC (ALT_ZERO + x) = iiSUC x &
   iiSUC (x + ALT_ZERO) = iiSUC x &
   iiSUC (NUMERAL_BIT1 x + NUMERAL_BIT1 xa) = NUMERAL_BIT2 (Suc (x + xa)) &
   iiSUC (NUMERAL_BIT1 x + NUMERAL_BIT2 xa) =
   NUMERAL_BIT1 (iiSUC (x + xa)) &
   iiSUC (NUMERAL_BIT2 x + NUMERAL_BIT1 xa) =
   NUMERAL_BIT1 (iiSUC (x + xa)) &
   iiSUC (NUMERAL_BIT2 x + NUMERAL_BIT2 xa) = NUMERAL_BIT2 (iiSUC (x + xa))"
  by (import numeral numeral_add)

lemma numeral_eq: "ALL (x::nat) xa::nat.
   (ALT_ZERO = NUMERAL_BIT1 x) = False &
   (NUMERAL_BIT1 x = ALT_ZERO) = False &
   (ALT_ZERO = NUMERAL_BIT2 x) = False &
   (NUMERAL_BIT2 x = ALT_ZERO) = False &
   (NUMERAL_BIT1 x = NUMERAL_BIT2 xa) = False &
   (NUMERAL_BIT2 x = NUMERAL_BIT1 xa) = False &
   (NUMERAL_BIT1 x = NUMERAL_BIT1 xa) = (x = xa) &
   (NUMERAL_BIT2 x = NUMERAL_BIT2 xa) = (x = xa)"
  by (import numeral numeral_eq)

lemma numeral_lt: "ALL (x::nat) xa::nat.
   (ALT_ZERO < NUMERAL_BIT1 x) = True &
   (ALT_ZERO < NUMERAL_BIT2 x) = True &
   (x < ALT_ZERO) = False &
   (NUMERAL_BIT1 x < NUMERAL_BIT1 xa) = (x < xa) &
   (NUMERAL_BIT2 x < NUMERAL_BIT2 xa) = (x < xa) &
   (NUMERAL_BIT1 x < NUMERAL_BIT2 xa) = (~ xa < x) &
   (NUMERAL_BIT2 x < NUMERAL_BIT1 xa) = (x < xa)"
  by (import numeral numeral_lt)

lemma numeral_lte: "ALL (x::nat) xa::nat.
   (ALT_ZERO <= x) = True &
   (NUMERAL_BIT1 x <= ALT_ZERO) = False &
   (NUMERAL_BIT2 x <= ALT_ZERO) = False &
   (NUMERAL_BIT1 x <= NUMERAL_BIT1 xa) = (x <= xa) &
   (NUMERAL_BIT1 x <= NUMERAL_BIT2 xa) = (x <= xa) &
   (NUMERAL_BIT2 x <= NUMERAL_BIT1 xa) = (~ xa <= x) &
   (NUMERAL_BIT2 x <= NUMERAL_BIT2 xa) = (x <= xa)"
  by (import numeral numeral_lte)

lemma numeral_pre: "PRE ALT_ZERO = ALT_ZERO &
PRE (NUMERAL_BIT1 ALT_ZERO) = ALT_ZERO &
(ALL x::nat.
    PRE (NUMERAL_BIT1 (NUMERAL_BIT1 x)) =
    NUMERAL_BIT2 (PRE (NUMERAL_BIT1 x))) &
(ALL x::nat.
    PRE (NUMERAL_BIT1 (NUMERAL_BIT2 x)) = NUMERAL_BIT2 (NUMERAL_BIT1 x)) &
(ALL x::nat. PRE (NUMERAL_BIT2 x) = NUMERAL_BIT1 x)"
  by (import numeral numeral_pre)

lemma bit_initiality: "ALL (zf::'a::type) (b1f::nat => 'a::type => 'a::type)
   b2f::nat => 'a::type => 'a::type.
   EX x::nat => 'a::type.
      x ALT_ZERO = zf &
      (ALL n::nat. x (NUMERAL_BIT1 n) = b1f n (x n)) &
      (ALL n::nat. x (NUMERAL_BIT2 n) = b2f n (x n))"
  by (import numeral bit_initiality)

consts
  iBIT_cases :: "nat => 'a => (nat => 'a) => (nat => 'a) => 'a" 

specification (iBIT_cases) iBIT_cases: "(ALL (zf::'a::type) (bf1::nat => 'a::type) bf2::nat => 'a::type.
    iBIT_cases ALT_ZERO zf bf1 bf2 = zf) &
(ALL (n::nat) (zf::'a::type) (bf1::nat => 'a::type) bf2::nat => 'a::type.
    iBIT_cases (NUMERAL_BIT1 n) zf bf1 bf2 = bf1 n) &
(ALL (n::nat) (zf::'a::type) (bf1::nat => 'a::type) bf2::nat => 'a::type.
    iBIT_cases (NUMERAL_BIT2 n) zf bf1 bf2 = bf2 n)"
  by (import numeral iBIT_cases)

definition iDUB :: "nat => nat" where 
  "iDUB == %x::nat. x + x"

lemma iDUB: "ALL x::nat. iDUB x = x + x"
  by (import numeral iDUB)

consts
  iSUB :: "bool => nat => nat => nat" 

specification (iSUB) iSUB_DEF: "(ALL (b::bool) x::nat. iSUB b ALT_ZERO x = ALT_ZERO) &
(ALL (b::bool) (n::nat) x::nat.
    iSUB b (NUMERAL_BIT1 n) x =
    (if b
     then iBIT_cases x (NUMERAL_BIT1 n) (%m::nat. iDUB (iSUB True n m))
           (%m::nat. NUMERAL_BIT1 (iSUB False n m))
     else iBIT_cases x (iDUB n) (%m::nat. NUMERAL_BIT1 (iSUB False n m))
           (%m::nat. iDUB (iSUB False n m)))) &
(ALL (b::bool) (n::nat) x::nat.
    iSUB b (NUMERAL_BIT2 n) x =
    (if b
     then iBIT_cases x (NUMERAL_BIT2 n)
           (%m::nat. NUMERAL_BIT1 (iSUB True n m))
           (%m::nat. iDUB (iSUB True n m))
     else iBIT_cases x (NUMERAL_BIT1 n) (%m::nat. iDUB (iSUB True n m))
           (%m::nat. NUMERAL_BIT1 (iSUB False n m))))"
  by (import numeral iSUB_DEF)

lemma bit_induction: "ALL P::nat => bool.
   P ALT_ZERO &
   (ALL n::nat. P n --> P (NUMERAL_BIT1 n)) &
   (ALL n::nat. P n --> P (NUMERAL_BIT2 n)) -->
   All P"
  by (import numeral bit_induction)

lemma iSUB_THM: "ALL (xa::bool) (xb::nat) xc::nat.
   iSUB xa ALT_ZERO (x::nat) = ALT_ZERO &
   iSUB True xb ALT_ZERO = xb &
   iSUB False (NUMERAL_BIT1 xb) ALT_ZERO = iDUB xb &
   iSUB True (NUMERAL_BIT1 xb) (NUMERAL_BIT1 xc) = iDUB (iSUB True xb xc) &
   iSUB False (NUMERAL_BIT1 xb) (NUMERAL_BIT1 xc) =
   NUMERAL_BIT1 (iSUB False xb xc) &
   iSUB True (NUMERAL_BIT1 xb) (NUMERAL_BIT2 xc) =
   NUMERAL_BIT1 (iSUB False xb xc) &
   iSUB False (NUMERAL_BIT1 xb) (NUMERAL_BIT2 xc) =
   iDUB (iSUB False xb xc) &
   iSUB False (NUMERAL_BIT2 xb) ALT_ZERO = NUMERAL_BIT1 xb &
   iSUB True (NUMERAL_BIT2 xb) (NUMERAL_BIT1 xc) =
   NUMERAL_BIT1 (iSUB True xb xc) &
   iSUB False (NUMERAL_BIT2 xb) (NUMERAL_BIT1 xc) = iDUB (iSUB True xb xc) &
   iSUB True (NUMERAL_BIT2 xb) (NUMERAL_BIT2 xc) = iDUB (iSUB True xb xc) &
   iSUB False (NUMERAL_BIT2 xb) (NUMERAL_BIT2 xc) =
   NUMERAL_BIT1 (iSUB False xb xc)"
  by (import numeral iSUB_THM)

lemma numeral_sub: "ALL (x::nat) xa::nat.
   NUMERAL (x - xa) = (if xa < x then NUMERAL (iSUB True x xa) else 0)"
  by (import numeral numeral_sub)

lemma iDUB_removal: "ALL x::nat.
   iDUB (NUMERAL_BIT1 x) = NUMERAL_BIT2 (iDUB x) &
   iDUB (NUMERAL_BIT2 x) = NUMERAL_BIT2 (NUMERAL_BIT1 x) &
   iDUB ALT_ZERO = ALT_ZERO"
  by (import numeral iDUB_removal)

lemma numeral_mult: "ALL (x::nat) xa::nat.
   ALT_ZERO * x = ALT_ZERO &
   x * ALT_ZERO = ALT_ZERO &
   NUMERAL_BIT1 x * xa = iZ (iDUB (x * xa) + xa) &
   NUMERAL_BIT2 x * xa = iDUB (iZ (x * xa + xa))"
  by (import numeral numeral_mult)

definition iSQR :: "nat => nat" where 
  "iSQR == %x::nat. x * x"

lemma iSQR: "ALL x::nat. iSQR x = x * x"
  by (import numeral iSQR)

lemma numeral_exp: "(ALL x::nat. x ^ ALT_ZERO = NUMERAL_BIT1 ALT_ZERO) &
(ALL (x::nat) xa::nat. x ^ NUMERAL_BIT1 xa = x * iSQR (x ^ xa)) &
(ALL (x::nat) xa::nat. x ^ NUMERAL_BIT2 xa = iSQR x * iSQR (x ^ xa))"
  by (import numeral numeral_exp)

lemma numeral_evenodd: "ALL x::nat.
   EVEN ALT_ZERO &
   EVEN (NUMERAL_BIT2 x) &
   ~ EVEN (NUMERAL_BIT1 x) &
   ~ ODD ALT_ZERO & ~ ODD (NUMERAL_BIT2 x) & ODD (NUMERAL_BIT1 x)"
  by (import numeral numeral_evenodd)

lemma numeral_fact: "ALL n::nat. FACT n = (if n = 0 then 1 else n * FACT (PRE n))"
  by (import numeral numeral_fact)

lemma numeral_funpow: "ALL n::nat.
   ((f::'a::type => 'a::type) ^^ n) (x::'a::type) =
   (if n = 0 then x else (f ^^ (n - 1)) (f x))"
  by (import numeral numeral_funpow)

;end_setup

;setup_theory ind_type

lemma INJ_INVERSE2: "ALL P::'A::type => 'B::type => 'C::type.
   (ALL (x1::'A::type) (y1::'B::type) (x2::'A::type) y2::'B::type.
       (P x1 y1 = P x2 y2) = (x1 = x2 & y1 = y2)) -->
   (EX (x::'C::type => 'A::type) Y::'C::type => 'B::type.
       ALL (xa::'A::type) y::'B::type. x (P xa y) = xa & Y (P xa y) = y)"
  by (import ind_type INJ_INVERSE2)

definition NUMPAIR :: "nat => nat => nat" where 
  "NUMPAIR == %(x::nat) y::nat. 2 ^ x * (2 * y + 1)"

lemma NUMPAIR: "ALL (x::nat) y::nat. NUMPAIR x y = 2 ^ x * (2 * y + 1)"
  by (import ind_type NUMPAIR)

lemma NUMPAIR_INJ_LEMMA: "ALL (x::nat) (xa::nat) (xb::nat) xc::nat.
   NUMPAIR x xa = NUMPAIR xb xc --> x = xb"
  by (import ind_type NUMPAIR_INJ_LEMMA)

lemma NUMPAIR_INJ: "ALL (x1::nat) (y1::nat) (x2::nat) y2::nat.
   (NUMPAIR x1 y1 = NUMPAIR x2 y2) = (x1 = x2 & y1 = y2)"
  by (import ind_type NUMPAIR_INJ)

consts
  NUMSND :: "nat => nat" 
  NUMFST :: "nat => nat" 

specification (NUMFST NUMSND) NUMPAIR_DEST: "ALL (x::nat) y::nat. NUMFST (NUMPAIR x y) = x & NUMSND (NUMPAIR x y) = y"
  by (import ind_type NUMPAIR_DEST)

definition NUMSUM :: "bool => nat => nat" where 
  "NUMSUM == %(b::bool) x::nat. if b then Suc (2 * x) else 2 * x"

lemma NUMSUM: "ALL (b::bool) x::nat. NUMSUM b x = (if b then Suc (2 * x) else 2 * x)"
  by (import ind_type NUMSUM)

lemma NUMSUM_INJ: "ALL (b1::bool) (x1::nat) (b2::bool) x2::nat.
   (NUMSUM b1 x1 = NUMSUM b2 x2) = (b1 = b2 & x1 = x2)"
  by (import ind_type NUMSUM_INJ)

consts
  NUMRIGHT :: "nat => nat" 
  NUMLEFT :: "nat => bool" 

specification (NUMLEFT NUMRIGHT) NUMSUM_DEST: "ALL (x::bool) y::nat. NUMLEFT (NUMSUM x y) = x & NUMRIGHT (NUMSUM x y) = y"
  by (import ind_type NUMSUM_DEST)

definition INJN :: "nat => nat => 'a => bool" where 
  "INJN == %(m::nat) (n::nat) a::'a::type. n = m"

lemma INJN: "ALL m::nat. INJN m = (%(n::nat) a::'a::type. n = m)"
  by (import ind_type INJN)

lemma INJN_INJ: "ALL (n1::nat) n2::nat. (INJN n1 = INJN n2) = (n1 = n2)"
  by (import ind_type INJN_INJ)

definition INJA :: "'a => nat => 'a => bool" where 
  "INJA == %(a::'a::type) (n::nat) b::'a::type. b = a"

lemma INJA: "ALL a::'a::type. INJA a = (%(n::nat) b::'a::type. b = a)"
  by (import ind_type INJA)

lemma INJA_INJ: "ALL (a1::'a::type) a2::'a::type. (INJA a1 = INJA a2) = (a1 = a2)"
  by (import ind_type INJA_INJ)

definition INJF :: "(nat => nat => 'a => bool) => nat => 'a => bool" where 
  "INJF == %(f::nat => nat => 'a::type => bool) n::nat. f (NUMFST n) (NUMSND n)"

lemma INJF: "ALL f::nat => nat => 'a::type => bool.
   INJF f = (%n::nat. f (NUMFST n) (NUMSND n))"
  by (import ind_type INJF)

lemma INJF_INJ: "ALL (f1::nat => nat => 'a::type => bool) f2::nat => nat => 'a::type => bool.
   (INJF f1 = INJF f2) = (f1 = f2)"
  by (import ind_type INJF_INJ)

definition INJP :: "(nat => 'a => bool) => (nat => 'a => bool) => nat => 'a => bool" where 
  "INJP ==
%(f1::nat => 'a::type => bool) (f2::nat => 'a::type => bool) (n::nat)
   a::'a::type. if NUMLEFT n then f1 (NUMRIGHT n) a else f2 (NUMRIGHT n) a"

lemma INJP: "ALL (f1::nat => 'a::type => bool) f2::nat => 'a::type => bool.
   INJP f1 f2 =
   (%(n::nat) a::'a::type.
       if NUMLEFT n then f1 (NUMRIGHT n) a else f2 (NUMRIGHT n) a)"
  by (import ind_type INJP)

lemma INJP_INJ: "ALL (f1::nat => 'a::type => bool) (f1'::nat => 'a::type => bool)
   (f2::nat => 'a::type => bool) f2'::nat => 'a::type => bool.
   (INJP f1 f2 = INJP f1' f2') = (f1 = f1' & f2 = f2')"
  by (import ind_type INJP_INJ)

definition ZCONSTR :: "nat => 'a => (nat => nat => 'a => bool) => nat => 'a => bool" where 
  "ZCONSTR ==
%(c::nat) (i::'a::type) r::nat => nat => 'a::type => bool.
   INJP (INJN (Suc c)) (INJP (INJA i) (INJF r))"

lemma ZCONSTR: "ALL (c::nat) (i::'a::type) r::nat => nat => 'a::type => bool.
   ZCONSTR c i r = INJP (INJN (Suc c)) (INJP (INJA i) (INJF r))"
  by (import ind_type ZCONSTR)

definition ZBOT :: "nat => 'a => bool" where 
  "ZBOT == INJP (INJN 0) (SOME z::nat => 'a::type => bool. True)"

lemma ZBOT: "ZBOT = INJP (INJN 0) (SOME z::nat => 'a::type => bool. True)"
  by (import ind_type ZBOT)

lemma ZCONSTR_ZBOT: "ALL (x::nat) (xa::'a::type) xb::nat => nat => 'a::type => bool.
   ZCONSTR x xa xb ~= ZBOT"
  by (import ind_type ZCONSTR_ZBOT)

definition ZRECSPACE :: "(nat => 'a => bool) => bool" where 
  "ZRECSPACE ==
%a0::nat => 'a::type => bool.
   ALL ZRECSPACE'::(nat => 'a::type => bool) => bool.
      (ALL a0::nat => 'a::type => bool.
          a0 = ZBOT |
          (EX (c::nat) (i::'a::type) r::nat => nat => 'a::type => bool.
              a0 = ZCONSTR c i r & (ALL n::nat. ZRECSPACE' (r n))) -->
          ZRECSPACE' a0) -->
      ZRECSPACE' a0"

lemma ZRECSPACE: "ZRECSPACE =
(%a0::nat => 'a::type => bool.
    ALL ZRECSPACE'::(nat => 'a::type => bool) => bool.
       (ALL a0::nat => 'a::type => bool.
           a0 = ZBOT |
           (EX (c::nat) (i::'a::type) r::nat => nat => 'a::type => bool.
               a0 = ZCONSTR c i r & (ALL n::nat. ZRECSPACE' (r n))) -->
           ZRECSPACE' a0) -->
       ZRECSPACE' a0)"
  by (import ind_type ZRECSPACE)

lemma ZRECSPACE_rules: "(op &::bool => bool => bool)
 ((ZRECSPACE::(nat => 'a::type => bool) => bool)
   (ZBOT::nat => 'a::type => bool))
 ((All::(nat => bool) => bool)
   (%c::nat.
       (All::('a::type => bool) => bool)
        (%i::'a::type.
            (All::((nat => nat => 'a::type => bool) => bool) => bool)
             (%r::nat => nat => 'a::type => bool.
                 (op -->::bool => bool => bool)
                  ((All::(nat => bool) => bool)
                    (%n::nat.
                        (ZRECSPACE::(nat => 'a::type => bool) => bool)
                         (r n)))
                  ((ZRECSPACE::(nat => 'a::type => bool) => bool)
                    ((ZCONSTR::nat
                               => 'a::type
                                  => (nat => nat => 'a::type => bool)
                                     => nat => 'a::type => bool)
                      c i r))))))"
  by (import ind_type ZRECSPACE_rules)

lemma ZRECSPACE_ind: "ALL x::(nat => 'a::type => bool) => bool.
   x ZBOT &
   (ALL (c::nat) (i::'a::type) r::nat => nat => 'a::type => bool.
       (ALL n::nat. x (r n)) --> x (ZCONSTR c i r)) -->
   (ALL a0::nat => 'a::type => bool. ZRECSPACE a0 --> x a0)"
  by (import ind_type ZRECSPACE_ind)

lemma ZRECSPACE_cases: "ALL a0::nat => 'a::type => bool.
   ZRECSPACE a0 =
   (a0 = ZBOT |
    (EX (c::nat) (i::'a::type) r::nat => nat => 'a::type => bool.
        a0 = ZCONSTR c i r & (ALL n::nat. ZRECSPACE (r n))))"
  by (import ind_type ZRECSPACE_cases)

typedef (open) ('a) recspace = "(Collect::((nat => 'a::type => bool) => bool)
          => (nat => 'a::type => bool) set)
 (ZRECSPACE::(nat => 'a::type => bool) => bool)" 
  by (rule typedef_helper,import ind_type recspace_TY_DEF)

lemmas recspace_TY_DEF = typedef_hol2hol4 [OF type_definition_recspace]

consts
  mk_rec :: "(nat => 'a => bool) => 'a recspace" 
  dest_rec :: "'a recspace => nat => 'a => bool" 

specification (dest_rec mk_rec) recspace_repfns: "(ALL a::'a::type recspace. mk_rec (dest_rec a) = a) &
(ALL r::nat => 'a::type => bool. ZRECSPACE r = (dest_rec (mk_rec r) = r))"
  by (import ind_type recspace_repfns)

definition BOTTOM :: "'a recspace" where 
  "BOTTOM == mk_rec ZBOT"

lemma BOTTOM: "BOTTOM = mk_rec ZBOT"
  by (import ind_type BOTTOM)

definition CONSTR :: "nat => 'a => (nat => 'a recspace) => 'a recspace" where 
  "CONSTR ==
%(c::nat) (i::'a::type) r::nat => 'a::type recspace.
   mk_rec (ZCONSTR c i (%n::nat. dest_rec (r n)))"

lemma CONSTR: "ALL (c::nat) (i::'a::type) r::nat => 'a::type recspace.
   CONSTR c i r = mk_rec (ZCONSTR c i (%n::nat. dest_rec (r n)))"
  by (import ind_type CONSTR)

lemma MK_REC_INJ: "ALL (x::nat => 'a::type => bool) y::nat => 'a::type => bool.
   mk_rec x = mk_rec y --> ZRECSPACE x & ZRECSPACE y --> x = y"
  by (import ind_type MK_REC_INJ)

lemma DEST_REC_INJ: "ALL (x::'a::type recspace) y::'a::type recspace.
   (dest_rec x = dest_rec y) = (x = y)"
  by (import ind_type DEST_REC_INJ)

lemma CONSTR_BOT: "ALL (c::nat) (i::'a::type) r::nat => 'a::type recspace.
   CONSTR c i r ~= BOTTOM"
  by (import ind_type CONSTR_BOT)

lemma CONSTR_INJ: "ALL (c1::nat) (i1::'a::type) (r1::nat => 'a::type recspace) (c2::nat)
   (i2::'a::type) r2::nat => 'a::type recspace.
   (CONSTR c1 i1 r1 = CONSTR c2 i2 r2) = (c1 = c2 & i1 = i2 & r1 = r2)"
  by (import ind_type CONSTR_INJ)

lemma CONSTR_IND: "ALL P::'a::type recspace => bool.
   P BOTTOM &
   (ALL (c::nat) (i::'a::type) r::nat => 'a::type recspace.
       (ALL n::nat. P (r n)) --> P (CONSTR c i r)) -->
   All P"
  by (import ind_type CONSTR_IND)

lemma CONSTR_REC: "ALL Fn::nat
        => 'a::type
           => (nat => 'a::type recspace) => (nat => 'b::type) => 'b::type.
   EX f::'a::type recspace => 'b::type.
      ALL (c::nat) (i::'a::type) r::nat => 'a::type recspace.
         f (CONSTR c i r) = Fn c i r (%n::nat. f (r n))"
  by (import ind_type CONSTR_REC)

consts
  FCONS :: "'a => (nat => 'a) => nat => 'a" 

specification (FCONS) FCONS: "(ALL (a::'a::type) f::nat => 'a::type. FCONS a f 0 = a) &
(ALL (a::'a::type) (f::nat => 'a::type) n::nat. FCONS a f (Suc n) = f n)"
  by (import ind_type FCONS)

definition FNIL :: "nat => 'a" where 
  "FNIL == %n::nat. SOME x::'a::type. True"

lemma FNIL: "ALL n::nat. FNIL n = (SOME x::'a::type. True)"
  by (import ind_type FNIL)

definition ISO :: "('a => 'b) => ('b => 'a) => bool" where 
  "ISO ==
%(f::'a::type => 'b::type) g::'b::type => 'a::type.
   (ALL x::'b::type. f (g x) = x) & (ALL y::'a::type. g (f y) = y)"

lemma ISO: "ALL (f::'a::type => 'b::type) g::'b::type => 'a::type.
   ISO f g =
   ((ALL x::'b::type. f (g x) = x) & (ALL y::'a::type. g (f y) = y))"
  by (import ind_type ISO)

lemma ISO_REFL: "ISO (%x::'a::type. x) (%x::'a::type. x)"
  by (import ind_type ISO_REFL)

lemma ISO_FUN: "ISO (f::'a::type => 'c::type) (f'::'c::type => 'a::type) &
ISO (g::'b::type => 'd::type) (g'::'d::type => 'b::type) -->
ISO (%(h::'a::type => 'b::type) a'::'c::type. g (h (f' a')))
 (%(h::'c::type => 'd::type) a::'a::type. g' (h (f a)))"
  by (import ind_type ISO_FUN)

lemma ISO_USAGE: "ISO (f::'a::type => 'b::type) (g::'b::type => 'a::type) -->
(ALL P::'a::type => bool. All P = (ALL x::'b::type. P (g x))) &
(ALL P::'a::type => bool. Ex P = (EX x::'b::type. P (g x))) &
(ALL (a::'a::type) b::'b::type. (a = g b) = (f a = b))"
  by (import ind_type ISO_USAGE)

;end_setup

;setup_theory divides

lemma ONE_DIVIDES_ALL: "(All::(nat => bool) => bool) ((op dvd::nat => nat => bool) (1::nat))"
  by (import divides ONE_DIVIDES_ALL)

lemma DIVIDES_ADD_2: "ALL (a::nat) (b::nat) c::nat. a dvd b & a dvd b + c --> a dvd c"
  by (import divides DIVIDES_ADD_2)

lemma DIVIDES_FACT: "ALL b>0. b dvd FACT b"
  by (import divides DIVIDES_FACT)

lemma DIVIDES_MULT_LEFT: "ALL (x::nat) xa::nat. (x * xa dvd xa) = (xa = 0 | x = 1)"
  by (import divides DIVIDES_MULT_LEFT)

;end_setup

;setup_theory prime

consts
  prime :: "nat => bool" 

defs
  prime_primdef: "prime.prime == %a::nat. a ~= 1 & (ALL b::nat. b dvd a --> b = a | b = 1)"

lemma prime_def: "ALL a::nat.
   prime.prime a = (a ~= 1 & (ALL b::nat. b dvd a --> b = a | b = 1))"
  by (import prime prime_def)

lemma NOT_PRIME_0: "~ prime.prime 0"
  by (import prime NOT_PRIME_0)

lemma NOT_PRIME_1: "~ prime.prime 1"
  by (import prime NOT_PRIME_1)

;end_setup

;setup_theory list

consts
  EL :: "nat => 'a list => 'a" 

specification (EL) EL: "(ALL l::'a::type list. EL 0 l = hd l) &
(ALL (l::'a::type list) n::nat. EL (Suc n) l = EL n (tl l))"
  by (import list EL)

lemma NULL: "(op &::bool => bool => bool)
 ((null::'a::type list => bool) ([]::'a::type list))
 ((All::('a::type => bool) => bool)
   (%x::'a::type.
       (All::('a::type list => bool) => bool)
        (%xa::'a::type list.
            (Not::bool => bool)
             ((null::'a::type list => bool)
               ((op #::'a::type => 'a::type list => 'a::type list) x xa)))))"
  by (import list NULL)

lemma list_case_compute: "ALL l::'a::type list.
   list_case (b::'b::type) (f::'a::type => 'a::type list => 'b::type) l =
   (if null l then b else f (hd l) (tl l))"
  by (import list list_case_compute)

lemma LIST_NOT_EQ: "ALL (l1::'a::type list) l2::'a::type list.
   l1 ~= l2 --> (ALL (x::'a::type) xa::'a::type. x # l1 ~= xa # l2)"
  by (import list LIST_NOT_EQ)

lemma NOT_EQ_LIST: "ALL (h1::'a::type) h2::'a::type.
   h1 ~= h2 -->
   (ALL (x::'a::type list) xa::'a::type list. h1 # x ~= h2 # xa)"
  by (import list NOT_EQ_LIST)

lemma EQ_LIST: "ALL (h1::'a::type) h2::'a::type.
   h1 = h2 -->
   (ALL (l1::'a::type list) l2::'a::type list.
       l1 = l2 --> h1 # l1 = h2 # l2)"
  by (import list EQ_LIST)

lemma CONS: "ALL l::'a::type list. ~ null l --> hd l # tl l = l"
  by (import list CONS)

lemma MAP_EQ_NIL: "ALL (l::'a::type list) f::'a::type => 'b::type.
   (map f l = []) = (l = []) & ([] = map f l) = (l = [])"
  by (import list MAP_EQ_NIL)

lemma EVERY_EL: "(All::('a::type list => bool) => bool)
 (%l::'a::type list.
     (All::(('a::type => bool) => bool) => bool)
      (%P::'a::type => bool.
          (op =::bool => bool => bool)
           ((list_all::('a::type => bool) => 'a::type list => bool) P l)
           ((All::(nat => bool) => bool)
             (%n::nat.
                 (op -->::bool => bool => bool)
                  ((op <::nat => nat => bool) n
                    ((size::'a::type list => nat) l))
                  (P ((EL::nat => 'a::type list => 'a::type) n l))))))"
  by (import list EVERY_EL)

lemma EVERY_CONJ: "ALL l::'a::type list.
   list_all
    (%x::'a::type. (P::'a::type => bool) x & (Q::'a::type => bool) x) l =
   (list_all P l & list_all Q l)"
  by (import list EVERY_CONJ)

lemma EVERY_MEM: "ALL (P::'a::type => bool) l::'a::type list.
   list_all P l = (ALL e::'a::type. e mem l --> P e)"
  by (import list EVERY_MEM)

lemma EXISTS_MEM: "ALL (P::'a::type => bool) l::'a::type list.
   list_ex P l = (EX e::'a::type. e mem l & P e)"
  by (import list EXISTS_MEM)

lemma MEM_APPEND: "ALL (e::'a::type) (l1::'a::type list) l2::'a::type list.
   e mem l1 @ l2 = (e mem l1 | e mem l2)"
  by (import list MEM_APPEND)

lemma EXISTS_APPEND: "ALL (P::'a::type => bool) (l1::'a::type list) l2::'a::type list.
   list_ex P (l1 @ l2) = (list_ex P l1 | list_ex P l2)"
  by (import list EXISTS_APPEND)

lemma NOT_EVERY: "ALL (P::'a::type => bool) l::'a::type list.
   (~ list_all P l) = list_ex (Not o P) l"
  by (import list NOT_EVERY)

lemma NOT_EXISTS: "ALL (P::'a::type => bool) l::'a::type list.
   (~ list_ex P l) = list_all (Not o P) l"
  by (import list NOT_EXISTS)

lemma MEM_MAP: "ALL (l::'a::type list) (f::'a::type => 'b::type) x::'b::type.
   x mem map f l = (EX y::'a::type. x = f y & y mem l)"
  by (import list MEM_MAP)

lemma LENGTH_CONS: "ALL (l::'a::type list) n::nat.
   (length l = Suc n) =
   (EX (h::'a::type) l'::'a::type list. length l' = n & l = h # l')"
  by (import list LENGTH_CONS)

lemma LENGTH_EQ_CONS: "ALL (P::'a::type list => bool) n::nat.
   (ALL l::'a::type list. length l = Suc n --> P l) =
   (ALL l::'a::type list. length l = n --> (ALL x::'a::type. P (x # l)))"
  by (import list LENGTH_EQ_CONS)

lemma LENGTH_EQ_NIL: "ALL P::'a::type list => bool.
   (ALL l::'a::type list. length l = 0 --> P l) = P []"
  by (import list LENGTH_EQ_NIL)

lemma CONS_ACYCLIC: "ALL (l::'a::type list) x::'a::type. l ~= x # l & x # l ~= l"
  by (import list CONS_ACYCLIC)

lemma APPEND_eq_NIL: "(ALL (l1::'a::type list) l2::'a::type list.
    ([] = l1 @ l2) = (l1 = [] & l2 = [])) &
(ALL (l1::'a::type list) l2::'a::type list.
    (l1 @ l2 = []) = (l1 = [] & l2 = []))"
  by (import list APPEND_eq_NIL)

lemma APPEND_11: "(ALL (l1::'a::type list) (l2::'a::type list) l3::'a::type list.
    (l1 @ l2 = l1 @ l3) = (l2 = l3)) &
(ALL (l1::'a::type list) (l2::'a::type list) l3::'a::type list.
    (l2 @ l1 = l3 @ l1) = (l2 = l3))"
  by (import list APPEND_11)

lemma EL_compute: "ALL n::nat.
   EL n (l::'a::type list) = (if n = 0 then hd l else EL (PRE n) (tl l))"
  by (import list EL_compute)

lemma WF_LIST_PRED: "WF (%(L1::'a::type list) L2::'a::type list. EX h::'a::type. L2 = h # L1)"
  by (import list WF_LIST_PRED)

lemma list_size_cong: "ALL (M::'a::type list) (N::'a::type list) (f::'a::type => nat)
   f'::'a::type => nat.
   M = N & (ALL x::'a::type. x mem N --> f x = f' x) -->
   list_size f M = list_size f' N"
  by (import list list_size_cong)

lemma FOLDR_CONG: "ALL (l::'a::type list) (l'::'a::type list) (b::'b::type) (b'::'b::type)
   (f::'a::type => 'b::type => 'b::type)
   f'::'a::type => 'b::type => 'b::type.
   l = l' &
   b = b' & (ALL (x::'a::type) a::'b::type. x mem l' --> f x a = f' x a) -->
   foldr f l b = foldr f' l' b'"
  by (import list FOLDR_CONG)

lemma FOLDL_CONG: "ALL (l::'a::type list) (l'::'a::type list) (b::'b::type) (b'::'b::type)
   (f::'b::type => 'a::type => 'b::type)
   f'::'b::type => 'a::type => 'b::type.
   l = l' &
   b = b' & (ALL (x::'a::type) a::'b::type. x mem l' --> f a x = f' a x) -->
   foldl f b l = foldl f' b' l'"
  by (import list FOLDL_CONG)

lemma MAP_CONG: "ALL (l1::'a::type list) (l2::'a::type list) (f::'a::type => 'b::type)
   f'::'a::type => 'b::type.
   l1 = l2 & (ALL x::'a::type. x mem l2 --> f x = f' x) -->
   map f l1 = map f' l2"
  by (import list MAP_CONG)

lemma EXISTS_CONG: "ALL (l1::'a::type list) (l2::'a::type list) (P::'a::type => bool)
   P'::'a::type => bool.
   l1 = l2 & (ALL x::'a::type. x mem l2 --> P x = P' x) -->
   list_ex P l1 = list_ex P' l2"
  by (import list EXISTS_CONG)

lemma EVERY_CONG: "ALL (l1::'a::type list) (l2::'a::type list) (P::'a::type => bool)
   P'::'a::type => bool.
   l1 = l2 & (ALL x::'a::type. x mem l2 --> P x = P' x) -->
   list_all P l1 = list_all P' l2"
  by (import list EVERY_CONG)

lemma EVERY_MONOTONIC: "ALL (P::'a::type => bool) Q::'a::type => bool.
   (ALL x::'a::type. P x --> Q x) -->
   (ALL l::'a::type list. list_all P l --> list_all Q l)"
  by (import list EVERY_MONOTONIC)

lemma LENGTH_ZIP: "ALL (l1::'a::type list) l2::'b::type list.
   length l1 = length l2 -->
   length (zip l1 l2) = length l1 & length (zip l1 l2) = length l2"
  by (import list LENGTH_ZIP)

lemma LENGTH_UNZIP: "ALL pl::('a::type * 'b::type) list.
   length (fst (unzip pl)) = length pl & length (snd (unzip pl)) = length pl"
  by (import list LENGTH_UNZIP)

lemma ZIP_UNZIP: "ALL l::('a::type * 'b::type) list. ZIP (unzip l) = l"
  by (import list ZIP_UNZIP)

lemma UNZIP_ZIP: "ALL (l1::'a::type list) l2::'b::type list.
   length l1 = length l2 --> unzip (zip l1 l2) = (l1, l2)"
  by (import list UNZIP_ZIP)

lemma ZIP_MAP: "ALL (l1::'a::type list) (l2::'b::type list) (f1::'a::type => 'c::type)
   f2::'b::type => 'd::type.
   length l1 = length l2 -->
   zip (map f1 l1) l2 =
   map (%p::'a::type * 'b::type. (f1 (fst p), snd p)) (zip l1 l2) &
   zip l1 (map f2 l2) =
   map (%p::'a::type * 'b::type. (fst p, f2 (snd p))) (zip l1 l2)"
  by (import list ZIP_MAP)

lemma MEM_ZIP: "(All::('a::type list => bool) => bool)
 (%l1::'a::type list.
     (All::('b::type list => bool) => bool)
      (%l2::'b::type list.
          (All::('a::type * 'b::type => bool) => bool)
           (%p::'a::type * 'b::type.
               (op -->::bool => bool => bool)
                ((op =::nat => nat => bool)
                  ((size::'a::type list => nat) l1)
                  ((size::'b::type list => nat) l2))
                ((op =::bool => bool => bool)
                  ((op mem::'a::type * 'b::type
                            => ('a::type * 'b::type) list => bool)
                    p ((zip::'a::type list
                             => 'b::type list => ('a::type * 'b::type) list)
                        l1 l2))
                  ((Ex::(nat => bool) => bool)
                    (%n::nat.
                        (op &::bool => bool => bool)
                         ((op <::nat => nat => bool) n
                           ((size::'a::type list => nat) l1))
                         ((op =::'a::type * 'b::type
                                 => 'a::type * 'b::type => bool)
                           p ((Pair::'a::type
                                     => 'b::type => 'a::type * 'b::type)
                               ((EL::nat => 'a::type list => 'a::type) n l1)
                               ((EL::nat => 'b::type list => 'b::type) n
                                 l2)))))))))"
  by (import list MEM_ZIP)

lemma EL_ZIP: "ALL (l1::'a::type list) (l2::'b::type list) n::nat.
   length l1 = length l2 & n < length l1 -->
   EL n (zip l1 l2) = (EL n l1, EL n l2)"
  by (import list EL_ZIP)

lemma MAP2_ZIP: "(All::('a::type list => bool) => bool)
 (%l1::'a::type list.
     (All::('b::type list => bool) => bool)
      (%l2::'b::type list.
          (op -->::bool => bool => bool)
           ((op =::nat => nat => bool) ((size::'a::type list => nat) l1)
             ((size::'b::type list => nat) l2))
           ((All::(('a::type => 'b::type => 'c::type) => bool) => bool)
             (%f::'a::type => 'b::type => 'c::type.
                 (op =::'c::type list => 'c::type list => bool)
                  ((map2::('a::type => 'b::type => 'c::type)
                          => 'a::type list
                             => 'b::type list => 'c::type list)
                    f l1 l2)
                  ((map::('a::type * 'b::type => 'c::type)
                         => ('a::type * 'b::type) list => 'c::type list)
                    ((split::('a::type => 'b::type => 'c::type)
                             => 'a::type * 'b::type => 'c::type)
                      f)
                    ((zip::'a::type list
                           => 'b::type list => ('a::type * 'b::type) list)
                      l1 l2))))))"
  by (import list MAP2_ZIP)

lemma MEM_EL: "(All::('a::type list => bool) => bool)
 (%l::'a::type list.
     (All::('a::type => bool) => bool)
      (%x::'a::type.
          (op =::bool => bool => bool)
           ((op mem::'a::type => 'a::type list => bool) x l)
           ((Ex::(nat => bool) => bool)
             (%n::nat.
                 (op &::bool => bool => bool)
                  ((op <::nat => nat => bool) n
                    ((size::'a::type list => nat) l))
                  ((op =::'a::type => 'a::type => bool) x
                    ((EL::nat => 'a::type list => 'a::type) n l))))))"
  by (import list MEM_EL)

lemma LAST_CONS: "(ALL x::'a::type. last [x] = x) &
(ALL (x::'a::type) (xa::'a::type) xb::'a::type list.
    last (x # xa # xb) = last (xa # xb))"
  by (import list LAST_CONS)

lemma FRONT_CONS: "(ALL x::'a::type. butlast [x] = []) &
(ALL (x::'a::type) (xa::'a::type) xb::'a::type list.
    butlast (x # xa # xb) = x # butlast (xa # xb))"
  by (import list FRONT_CONS)

;end_setup

;setup_theory pred_set

lemma EXTENSION: "ALL (s::'a::type => bool) t::'a::type => bool.
   (s = t) = (ALL x::'a::type. IN x s = IN x t)"
  by (import pred_set EXTENSION)

lemma NOT_EQUAL_SETS: "ALL (x::'a::type => bool) xa::'a::type => bool.
   (x ~= xa) = (EX xb::'a::type. IN xb xa = (~ IN xb x))"
  by (import pred_set NOT_EQUAL_SETS)

lemma NUM_SET_WOP: "ALL s::nat => bool.
   (EX n::nat. IN n s) =
   (EX n::nat. IN n s & (ALL m::nat. IN m s --> n <= m))"
  by (import pred_set NUM_SET_WOP)

consts
  GSPEC :: "('b => 'a * bool) => 'a => bool" 

specification (GSPEC) GSPECIFICATION: "ALL (f::'b::type => 'a::type * bool) v::'a::type.
   IN v (GSPEC f) = (EX x::'b::type. (v, True) = f x)"
  by (import pred_set GSPECIFICATION)

lemma SET_MINIMUM: "ALL (s::'a::type => bool) M::'a::type => nat.
   (EX x::'a::type. IN x s) =
   (EX x::'a::type. IN x s & (ALL y::'a::type. IN y s --> M x <= M y))"
  by (import pred_set SET_MINIMUM)

definition EMPTY :: "'a => bool" where 
  "EMPTY == %x::'a::type. False"

lemma EMPTY_DEF: "EMPTY = (%x::'a::type. False)"
  by (import pred_set EMPTY_DEF)

lemma NOT_IN_EMPTY: "ALL x::'a::type. ~ IN x EMPTY"
  by (import pred_set NOT_IN_EMPTY)

lemma MEMBER_NOT_EMPTY: "ALL x::'a::type => bool. (EX xa::'a::type. IN xa x) = (x ~= EMPTY)"
  by (import pred_set MEMBER_NOT_EMPTY)

consts
  UNIV :: "'a => bool" 

defs
  UNIV_def: "pred_set.UNIV == %x::'a::type. True"

lemma UNIV_DEF: "pred_set.UNIV = (%x::'a::type. True)"
  by (import pred_set UNIV_DEF)

lemma IN_UNIV: "ALL x::'a::type. IN x pred_set.UNIV"
  by (import pred_set IN_UNIV)

lemma UNIV_NOT_EMPTY: "pred_set.UNIV ~= EMPTY"
  by (import pred_set UNIV_NOT_EMPTY)

lemma EMPTY_NOT_UNIV: "EMPTY ~= pred_set.UNIV"
  by (import pred_set EMPTY_NOT_UNIV)

lemma EQ_UNIV: "(ALL x::'a::type. IN x (s::'a::type => bool)) = (s = pred_set.UNIV)"
  by (import pred_set EQ_UNIV)

definition SUBSET :: "('a => bool) => ('a => bool) => bool" where 
  "SUBSET ==
%(s::'a::type => bool) t::'a::type => bool.
   ALL x::'a::type. IN x s --> IN x t"

lemma SUBSET_DEF: "ALL (s::'a::type => bool) t::'a::type => bool.
   SUBSET s t = (ALL x::'a::type. IN x s --> IN x t)"
  by (import pred_set SUBSET_DEF)

lemma SUBSET_TRANS: "ALL (x::'a::type => bool) (xa::'a::type => bool) xb::'a::type => bool.
   SUBSET x xa & SUBSET xa xb --> SUBSET x xb"
  by (import pred_set SUBSET_TRANS)

lemma SUBSET_REFL: "ALL x::'a::type => bool. SUBSET x x"
  by (import pred_set SUBSET_REFL)

lemma SUBSET_ANTISYM: "ALL (x::'a::type => bool) xa::'a::type => bool.
   SUBSET x xa & SUBSET xa x --> x = xa"
  by (import pred_set SUBSET_ANTISYM)

lemma EMPTY_SUBSET: "All (SUBSET EMPTY)"
  by (import pred_set EMPTY_SUBSET)

lemma SUBSET_EMPTY: "ALL x::'a::type => bool. SUBSET x EMPTY = (x = EMPTY)"
  by (import pred_set SUBSET_EMPTY)

lemma SUBSET_UNIV: "ALL x::'a::type => bool. SUBSET x pred_set.UNIV"
  by (import pred_set SUBSET_UNIV)

lemma UNIV_SUBSET: "ALL x::'a::type => bool. SUBSET pred_set.UNIV x = (x = pred_set.UNIV)"
  by (import pred_set UNIV_SUBSET)

definition PSUBSET :: "('a => bool) => ('a => bool) => bool" where 
  "PSUBSET == %(s::'a::type => bool) t::'a::type => bool. SUBSET s t & s ~= t"

lemma PSUBSET_DEF: "ALL (s::'a::type => bool) t::'a::type => bool.
   PSUBSET s t = (SUBSET s t & s ~= t)"
  by (import pred_set PSUBSET_DEF)

lemma PSUBSET_TRANS: "ALL (x::'a::type => bool) (xa::'a::type => bool) xb::'a::type => bool.
   PSUBSET x xa & PSUBSET xa xb --> PSUBSET x xb"
  by (import pred_set PSUBSET_TRANS)

lemma PSUBSET_IRREFL: "ALL x::'a::type => bool. ~ PSUBSET x x"
  by (import pred_set PSUBSET_IRREFL)

lemma NOT_PSUBSET_EMPTY: "ALL x::'a::type => bool. ~ PSUBSET x EMPTY"
  by (import pred_set NOT_PSUBSET_EMPTY)

lemma NOT_UNIV_PSUBSET: "ALL x::'a::type => bool. ~ PSUBSET pred_set.UNIV x"
  by (import pred_set NOT_UNIV_PSUBSET)

lemma PSUBSET_UNIV: "ALL x::'a::type => bool.
   PSUBSET x pred_set.UNIV = (EX xa::'a::type. ~ IN xa x)"
  by (import pred_set PSUBSET_UNIV)

consts
  UNION :: "('a => bool) => ('a => bool) => 'a => bool" 

defs
  UNION_def: "pred_set.UNION ==
%(s::'a::type => bool) t::'a::type => bool.
   GSPEC (%x::'a::type. (x, IN x s | IN x t))"

lemma UNION_DEF: "ALL (s::'a::type => bool) t::'a::type => bool.
   pred_set.UNION s t = GSPEC (%x::'a::type. (x, IN x s | IN x t))"
  by (import pred_set UNION_DEF)

lemma IN_UNION: "ALL (x::'a::type => bool) (xa::'a::type => bool) xb::'a::type.
   IN xb (pred_set.UNION x xa) = (IN xb x | IN xb xa)"
  by (import pred_set IN_UNION)

lemma UNION_ASSOC: "ALL (x::'a::type => bool) (xa::'a::type => bool) xb::'a::type => bool.
   pred_set.UNION x (pred_set.UNION xa xb) =
   pred_set.UNION (pred_set.UNION x xa) xb"
  by (import pred_set UNION_ASSOC)

lemma UNION_IDEMPOT: "ALL x::'a::type => bool. pred_set.UNION x x = x"
  by (import pred_set UNION_IDEMPOT)

lemma UNION_COMM: "ALL (x::'a::type => bool) xa::'a::type => bool.
   pred_set.UNION x xa = pred_set.UNION xa x"
  by (import pred_set UNION_COMM)

lemma SUBSET_UNION: "(ALL (x::'a::type => bool) xa::'a::type => bool.
    SUBSET x (pred_set.UNION x xa)) &
(ALL (x::'a::type => bool) xa::'a::type => bool.
    SUBSET x (pred_set.UNION xa x))"
  by (import pred_set SUBSET_UNION)

lemma UNION_SUBSET: "ALL (s::'a::type => bool) (t::'a::type => bool) u::'a::type => bool.
   SUBSET (pred_set.UNION s t) u = (SUBSET s u & SUBSET t u)"
  by (import pred_set UNION_SUBSET)

lemma SUBSET_UNION_ABSORPTION: "ALL (x::'a::type => bool) xa::'a::type => bool.
   SUBSET x xa = (pred_set.UNION x xa = xa)"
  by (import pred_set SUBSET_UNION_ABSORPTION)

lemma UNION_EMPTY: "(ALL x::'a::type => bool. pred_set.UNION EMPTY x = x) &
(ALL x::'a::type => bool. pred_set.UNION x EMPTY = x)"
  by (import pred_set UNION_EMPTY)

lemma UNION_UNIV: "(ALL x::'a::type => bool. pred_set.UNION pred_set.UNIV x = pred_set.UNIV) &
(ALL x::'a::type => bool. pred_set.UNION x pred_set.UNIV = pred_set.UNIV)"
  by (import pred_set UNION_UNIV)

lemma EMPTY_UNION: "ALL (x::'a::type => bool) xa::'a::type => bool.
   (pred_set.UNION x xa = EMPTY) = (x = EMPTY & xa = EMPTY)"
  by (import pred_set EMPTY_UNION)

consts
  INTER :: "('a => bool) => ('a => bool) => 'a => bool" 

defs
  INTER_def: "pred_set.INTER ==
%(s::'a::type => bool) t::'a::type => bool.
   GSPEC (%x::'a::type. (x, IN x s & IN x t))"

lemma INTER_DEF: "ALL (s::'a::type => bool) t::'a::type => bool.
   pred_set.INTER s t = GSPEC (%x::'a::type. (x, IN x s & IN x t))"
  by (import pred_set INTER_DEF)

lemma IN_INTER: "ALL (x::'a::type => bool) (xa::'a::type => bool) xb::'a::type.
   IN xb (pred_set.INTER x xa) = (IN xb x & IN xb xa)"
  by (import pred_set IN_INTER)

lemma INTER_ASSOC: "ALL (x::'a::type => bool) (xa::'a::type => bool) xb::'a::type => bool.
   pred_set.INTER x (pred_set.INTER xa xb) =
   pred_set.INTER (pred_set.INTER x xa) xb"
  by (import pred_set INTER_ASSOC)

lemma INTER_IDEMPOT: "ALL x::'a::type => bool. pred_set.INTER x x = x"
  by (import pred_set INTER_IDEMPOT)

lemma INTER_COMM: "ALL (x::'a::type => bool) xa::'a::type => bool.
   pred_set.INTER x xa = pred_set.INTER xa x"
  by (import pred_set INTER_COMM)

lemma INTER_SUBSET: "(ALL (x::'a::type => bool) xa::'a::type => bool.
    SUBSET (pred_set.INTER x xa) x) &
(ALL (x::'a::type => bool) xa::'a::type => bool.
    SUBSET (pred_set.INTER xa x) x)"
  by (import pred_set INTER_SUBSET)

lemma SUBSET_INTER: "ALL (s::'a::type => bool) (t::'a::type => bool) u::'a::type => bool.
   SUBSET s (pred_set.INTER t u) = (SUBSET s t & SUBSET s u)"
  by (import pred_set SUBSET_INTER)

lemma SUBSET_INTER_ABSORPTION: "ALL (x::'a::type => bool) xa::'a::type => bool.
   SUBSET x xa = (pred_set.INTER x xa = x)"
  by (import pred_set SUBSET_INTER_ABSORPTION)

lemma INTER_EMPTY: "(ALL x::'a::type => bool. pred_set.INTER EMPTY x = EMPTY) &
(ALL x::'a::type => bool. pred_set.INTER x EMPTY = EMPTY)"
  by (import pred_set INTER_EMPTY)

lemma INTER_UNIV: "(ALL x::'a::type => bool. pred_set.INTER pred_set.UNIV x = x) &
(ALL x::'a::type => bool. pred_set.INTER x pred_set.UNIV = x)"
  by (import pred_set INTER_UNIV)

lemma UNION_OVER_INTER: "ALL (x::'a::type => bool) (xa::'a::type => bool) xb::'a::type => bool.
   pred_set.INTER x (pred_set.UNION xa xb) =
   pred_set.UNION (pred_set.INTER x xa) (pred_set.INTER x xb)"
  by (import pred_set UNION_OVER_INTER)

lemma INTER_OVER_UNION: "ALL (x::'a::type => bool) (xa::'a::type => bool) xb::'a::type => bool.
   pred_set.UNION x (pred_set.INTER xa xb) =
   pred_set.INTER (pred_set.UNION x xa) (pred_set.UNION x xb)"
  by (import pred_set INTER_OVER_UNION)

definition DISJOINT :: "('a => bool) => ('a => bool) => bool" where 
  "DISJOINT ==
%(s::'a::type => bool) t::'a::type => bool. pred_set.INTER s t = EMPTY"

lemma DISJOINT_DEF: "ALL (s::'a::type => bool) t::'a::type => bool.
   DISJOINT s t = (pred_set.INTER s t = EMPTY)"
  by (import pred_set DISJOINT_DEF)

lemma IN_DISJOINT: "ALL (x::'a::type => bool) xa::'a::type => bool.
   DISJOINT x xa = (~ (EX xb::'a::type. IN xb x & IN xb xa))"
  by (import pred_set IN_DISJOINT)

lemma DISJOINT_SYM: "ALL (x::'a::type => bool) xa::'a::type => bool.
   DISJOINT x xa = DISJOINT xa x"
  by (import pred_set DISJOINT_SYM)

lemma DISJOINT_EMPTY: "ALL x::'a::type => bool. DISJOINT EMPTY x & DISJOINT x EMPTY"
  by (import pred_set DISJOINT_EMPTY)

lemma DISJOINT_EMPTY_REFL: "ALL x::'a::type => bool. (x = EMPTY) = DISJOINT x x"
  by (import pred_set DISJOINT_EMPTY_REFL)

lemma DISJOINT_UNION: "ALL (x::'a::type => bool) (xa::'a::type => bool) xb::'a::type => bool.
   DISJOINT (pred_set.UNION x xa) xb = (DISJOINT x xb & DISJOINT xa xb)"
  by (import pred_set DISJOINT_UNION)

lemma DISJOINT_UNION_BOTH: "ALL (s::'a::type => bool) (t::'a::type => bool) u::'a::type => bool.
   DISJOINT (pred_set.UNION s t) u = (DISJOINT s u & DISJOINT t u) &
   DISJOINT u (pred_set.UNION s t) = (DISJOINT s u & DISJOINT t u)"
  by (import pred_set DISJOINT_UNION_BOTH)

definition DIFF :: "('a => bool) => ('a => bool) => 'a => bool" where 
  "DIFF ==
%(s::'a::type => bool) t::'a::type => bool.
   GSPEC (%x::'a::type. (x, IN x s & ~ IN x t))"

lemma DIFF_DEF: "ALL (s::'a::type => bool) t::'a::type => bool.
   DIFF s t = GSPEC (%x::'a::type. (x, IN x s & ~ IN x t))"
  by (import pred_set DIFF_DEF)

lemma IN_DIFF: "ALL (s::'a::type => bool) (t::'a::type => bool) x::'a::type.
   IN x (DIFF s t) = (IN x s & ~ IN x t)"
  by (import pred_set IN_DIFF)

lemma DIFF_EMPTY: "ALL s::'a::type => bool. DIFF s EMPTY = s"
  by (import pred_set DIFF_EMPTY)

lemma EMPTY_DIFF: "ALL s::'a::type => bool. DIFF EMPTY s = EMPTY"
  by (import pred_set EMPTY_DIFF)

lemma DIFF_UNIV: "ALL s::'a::type => bool. DIFF s pred_set.UNIV = EMPTY"
  by (import pred_set DIFF_UNIV)

lemma DIFF_DIFF: "ALL (x::'a::type => bool) xa::'a::type => bool.
   DIFF (DIFF x xa) xa = DIFF x xa"
  by (import pred_set DIFF_DIFF)

lemma DIFF_EQ_EMPTY: "ALL x::'a::type => bool. DIFF x x = EMPTY"
  by (import pred_set DIFF_EQ_EMPTY)

definition INSERT :: "'a => ('a => bool) => 'a => bool" where 
  "INSERT ==
%(x::'a::type) s::'a::type => bool.
   GSPEC (%y::'a::type. (y, y = x | IN y s))"

lemma INSERT_DEF: "ALL (x::'a::type) s::'a::type => bool.
   INSERT x s = GSPEC (%y::'a::type. (y, y = x | IN y s))"
  by (import pred_set INSERT_DEF)

lemma IN_INSERT: "ALL (x::'a::type) (xa::'a::type) xb::'a::type => bool.
   IN x (INSERT xa xb) = (x = xa | IN x xb)"
  by (import pred_set IN_INSERT)

lemma COMPONENT: "ALL (x::'a::type) xa::'a::type => bool. IN x (INSERT x xa)"
  by (import pred_set COMPONENT)

lemma SET_CASES: "ALL x::'a::type => bool.
   x = EMPTY |
   (EX (xa::'a::type) xb::'a::type => bool. x = INSERT xa xb & ~ IN xa xb)"
  by (import pred_set SET_CASES)

lemma DECOMPOSITION: "ALL (s::'a::type => bool) x::'a::type.
   IN x s = (EX t::'a::type => bool. s = INSERT x t & ~ IN x t)"
  by (import pred_set DECOMPOSITION)

lemma ABSORPTION: "ALL (x::'a::type) xa::'a::type => bool. IN x xa = (INSERT x xa = xa)"
  by (import pred_set ABSORPTION)

lemma INSERT_INSERT: "ALL (x::'a::type) xa::'a::type => bool. INSERT x (INSERT x xa) = INSERT x xa"
  by (import pred_set INSERT_INSERT)

lemma INSERT_COMM: "ALL (x::'a::type) (xa::'a::type) xb::'a::type => bool.
   INSERT x (INSERT xa xb) = INSERT xa (INSERT x xb)"
  by (import pred_set INSERT_COMM)

lemma INSERT_UNIV: "ALL x::'a::type. INSERT x pred_set.UNIV = pred_set.UNIV"
  by (import pred_set INSERT_UNIV)

lemma NOT_INSERT_EMPTY: "ALL (x::'a::type) xa::'a::type => bool. INSERT x xa ~= EMPTY"
  by (import pred_set NOT_INSERT_EMPTY)

lemma NOT_EMPTY_INSERT: "ALL (x::'a::type) xa::'a::type => bool. EMPTY ~= INSERT x xa"
  by (import pred_set NOT_EMPTY_INSERT)

lemma INSERT_UNION: "ALL (x::'a::type) (s::'a::type => bool) t::'a::type => bool.
   pred_set.UNION (INSERT x s) t =
   (if IN x t then pred_set.UNION s t else INSERT x (pred_set.UNION s t))"
  by (import pred_set INSERT_UNION)

lemma INSERT_UNION_EQ: "ALL (x::'a::type) (s::'a::type => bool) t::'a::type => bool.
   pred_set.UNION (INSERT x s) t = INSERT x (pred_set.UNION s t)"
  by (import pred_set INSERT_UNION_EQ)

lemma INSERT_INTER: "ALL (x::'a::type) (s::'a::type => bool) t::'a::type => bool.
   pred_set.INTER (INSERT x s) t =
   (if IN x t then INSERT x (pred_set.INTER s t) else pred_set.INTER s t)"
  by (import pred_set INSERT_INTER)

lemma DISJOINT_INSERT: "ALL (x::'a::type) (xa::'a::type => bool) xb::'a::type => bool.
   DISJOINT (INSERT x xa) xb = (DISJOINT xa xb & ~ IN x xb)"
  by (import pred_set DISJOINT_INSERT)

lemma INSERT_SUBSET: "ALL (x::'a::type) (xa::'a::type => bool) xb::'a::type => bool.
   SUBSET (INSERT x xa) xb = (IN x xb & SUBSET xa xb)"
  by (import pred_set INSERT_SUBSET)

lemma SUBSET_INSERT: "ALL (x::'a::type) xa::'a::type => bool.
   ~ IN x xa -->
   (ALL xb::'a::type => bool. SUBSET xa (INSERT x xb) = SUBSET xa xb)"
  by (import pred_set SUBSET_INSERT)

lemma INSERT_DIFF: "ALL (s::'a::type => bool) (t::'a::type => bool) x::'a::type.
   DIFF (INSERT x s) t = (if IN x t then DIFF s t else INSERT x (DIFF s t))"
  by (import pred_set INSERT_DIFF)

definition DELETE :: "('a => bool) => 'a => 'a => bool" where 
  "DELETE == %(s::'a::type => bool) x::'a::type. DIFF s (INSERT x EMPTY)"

lemma DELETE_DEF: "ALL (s::'a::type => bool) x::'a::type. DELETE s x = DIFF s (INSERT x EMPTY)"
  by (import pred_set DELETE_DEF)

lemma IN_DELETE: "ALL (x::'a::type => bool) (xa::'a::type) xb::'a::type.
   IN xa (DELETE x xb) = (IN xa x & xa ~= xb)"
  by (import pred_set IN_DELETE)

lemma DELETE_NON_ELEMENT: "ALL (x::'a::type) xa::'a::type => bool. (~ IN x xa) = (DELETE xa x = xa)"
  by (import pred_set DELETE_NON_ELEMENT)

lemma IN_DELETE_EQ: "ALL (s::'a::type => bool) (x::'a::type) x'::'a::type.
   (IN x s = IN x' s) = (IN x (DELETE s x') = IN x' (DELETE s x))"
  by (import pred_set IN_DELETE_EQ)

lemma EMPTY_DELETE: "ALL x::'a::type. DELETE EMPTY x = EMPTY"
  by (import pred_set EMPTY_DELETE)

lemma DELETE_DELETE: "ALL (x::'a::type) xa::'a::type => bool. DELETE (DELETE xa x) x = DELETE xa x"
  by (import pred_set DELETE_DELETE)

lemma DELETE_COMM: "ALL (x::'a::type) (xa::'a::type) xb::'a::type => bool.
   DELETE (DELETE xb x) xa = DELETE (DELETE xb xa) x"
  by (import pred_set DELETE_COMM)

lemma DELETE_SUBSET: "ALL (x::'a::type) xa::'a::type => bool. SUBSET (DELETE xa x) xa"
  by (import pred_set DELETE_SUBSET)

lemma SUBSET_DELETE: "ALL (x::'a::type) (xa::'a::type => bool) xb::'a::type => bool.
   SUBSET xa (DELETE xb x) = (~ IN x xa & SUBSET xa xb)"
  by (import pred_set SUBSET_DELETE)

lemma SUBSET_INSERT_DELETE: "ALL (x::'a::type) (s::'a::type => bool) t::'a::type => bool.
   SUBSET s (INSERT x t) = SUBSET (DELETE s x) t"
  by (import pred_set SUBSET_INSERT_DELETE)

lemma DIFF_INSERT: "ALL (x::'a::type => bool) (xa::'a::type => bool) xb::'a::type.
   DIFF x (INSERT xb xa) = DIFF (DELETE x xb) xa"
  by (import pred_set DIFF_INSERT)

lemma PSUBSET_INSERT_SUBSET: "ALL (x::'a::type => bool) xa::'a::type => bool.
   PSUBSET x xa = (EX xb::'a::type. ~ IN xb x & SUBSET (INSERT xb x) xa)"
  by (import pred_set PSUBSET_INSERT_SUBSET)

lemma PSUBSET_MEMBER: "ALL (s::'a::type => bool) t::'a::type => bool.
   PSUBSET s t = (SUBSET s t & (EX y::'a::type. IN y t & ~ IN y s))"
  by (import pred_set PSUBSET_MEMBER)

lemma DELETE_INSERT: "ALL (x::'a::type) (xa::'a::type) xb::'a::type => bool.
   DELETE (INSERT x xb) xa =
   (if x = xa then DELETE xb xa else INSERT x (DELETE xb xa))"
  by (import pred_set DELETE_INSERT)

lemma INSERT_DELETE: "ALL (x::'a::type) xa::'a::type => bool.
   IN x xa --> INSERT x (DELETE xa x) = xa"
  by (import pred_set INSERT_DELETE)

lemma DELETE_INTER: "ALL (x::'a::type => bool) (xa::'a::type => bool) xb::'a::type.
   pred_set.INTER (DELETE x xb) xa = DELETE (pred_set.INTER x xa) xb"
  by (import pred_set DELETE_INTER)

lemma DISJOINT_DELETE_SYM: "ALL (x::'a::type => bool) (xa::'a::type => bool) xb::'a::type.
   DISJOINT (DELETE x xb) xa = DISJOINT (DELETE xa xb) x"
  by (import pred_set DISJOINT_DELETE_SYM)

consts
  CHOICE :: "('a => bool) => 'a" 

specification (CHOICE) CHOICE_DEF: "ALL x::'a::type => bool. x ~= EMPTY --> IN (CHOICE x) x"
  by (import pred_set CHOICE_DEF)

definition REST :: "('a => bool) => 'a => bool" where 
  "REST == %s::'a::type => bool. DELETE s (CHOICE s)"

lemma REST_DEF: "ALL s::'a::type => bool. REST s = DELETE s (CHOICE s)"
  by (import pred_set REST_DEF)

lemma CHOICE_NOT_IN_REST: "ALL x::'a::type => bool. ~ IN (CHOICE x) (REST x)"
  by (import pred_set CHOICE_NOT_IN_REST)

lemma CHOICE_INSERT_REST: "ALL s::'a::type => bool. s ~= EMPTY --> INSERT (CHOICE s) (REST s) = s"
  by (import pred_set CHOICE_INSERT_REST)

lemma REST_SUBSET: "ALL x::'a::type => bool. SUBSET (REST x) x"
  by (import pred_set REST_SUBSET)

lemma REST_PSUBSET: "ALL x::'a::type => bool. x ~= EMPTY --> PSUBSET (REST x) x"
  by (import pred_set REST_PSUBSET)

definition SING :: "('a => bool) => bool" where 
  "SING == %s::'a::type => bool. EX x::'a::type. s = INSERT x EMPTY"

lemma SING_DEF: "ALL s::'a::type => bool. SING s = (EX x::'a::type. s = INSERT x EMPTY)"
  by (import pred_set SING_DEF)

lemma SING: "ALL x::'a::type. SING (INSERT x EMPTY)"
  by (import pred_set SING)

lemma IN_SING: "ALL (x::'a::type) xa::'a::type. IN x (INSERT xa EMPTY) = (x = xa)"
  by (import pred_set IN_SING)

lemma NOT_SING_EMPTY: "ALL x::'a::type. INSERT x EMPTY ~= EMPTY"
  by (import pred_set NOT_SING_EMPTY)

lemma NOT_EMPTY_SING: "ALL x::'a::type. EMPTY ~= INSERT x EMPTY"
  by (import pred_set NOT_EMPTY_SING)

lemma EQUAL_SING: "ALL (x::'a::type) xa::'a::type.
   (INSERT x EMPTY = INSERT xa EMPTY) = (x = xa)"
  by (import pred_set EQUAL_SING)

lemma DISJOINT_SING_EMPTY: "ALL x::'a::type. DISJOINT (INSERT x EMPTY) EMPTY"
  by (import pred_set DISJOINT_SING_EMPTY)

lemma INSERT_SING_UNION: "ALL (x::'a::type => bool) xa::'a::type.
   INSERT xa x = pred_set.UNION (INSERT xa EMPTY) x"
  by (import pred_set INSERT_SING_UNION)

lemma SING_DELETE: "ALL x::'a::type. DELETE (INSERT x EMPTY) x = EMPTY"
  by (import pred_set SING_DELETE)

lemma DELETE_EQ_SING: "ALL (x::'a::type => bool) xa::'a::type.
   IN xa x --> (DELETE x xa = EMPTY) = (x = INSERT xa EMPTY)"
  by (import pred_set DELETE_EQ_SING)

lemma CHOICE_SING: "ALL x::'a::type. CHOICE (INSERT x EMPTY) = x"
  by (import pred_set CHOICE_SING)

lemma REST_SING: "ALL x::'a::type. REST (INSERT x EMPTY) = EMPTY"
  by (import pred_set REST_SING)

lemma SING_IFF_EMPTY_REST: "ALL x::'a::type => bool. SING x = (x ~= EMPTY & REST x = EMPTY)"
  by (import pred_set SING_IFF_EMPTY_REST)

definition IMAGE :: "('a => 'b) => ('a => bool) => 'b => bool" where 
  "IMAGE ==
%(f::'a::type => 'b::type) s::'a::type => bool.
   GSPEC (%x::'a::type. (f x, IN x s))"

lemma IMAGE_DEF: "ALL (f::'a::type => 'b::type) s::'a::type => bool.
   IMAGE f s = GSPEC (%x::'a::type. (f x, IN x s))"
  by (import pred_set IMAGE_DEF)

lemma IN_IMAGE: "ALL (x::'b::type) (xa::'a::type => bool) xb::'a::type => 'b::type.
   IN x (IMAGE xb xa) = (EX xc::'a::type. x = xb xc & IN xc xa)"
  by (import pred_set IN_IMAGE)

lemma IMAGE_IN: "ALL (x::'a::type) xa::'a::type => bool.
   IN x xa --> (ALL xb::'a::type => 'b::type. IN (xb x) (IMAGE xb xa))"
  by (import pred_set IMAGE_IN)

lemma IMAGE_EMPTY: "ALL x::'a::type => 'b::type. IMAGE x EMPTY = EMPTY"
  by (import pred_set IMAGE_EMPTY)

lemma IMAGE_ID: "ALL x::'a::type => bool. IMAGE (%x::'a::type. x) x = x"
  by (import pred_set IMAGE_ID)

lemma IMAGE_COMPOSE: "ALL (x::'b::type => 'c::type) (xa::'a::type => 'b::type)
   xb::'a::type => bool. IMAGE (x o xa) xb = IMAGE x (IMAGE xa xb)"
  by (import pred_set IMAGE_COMPOSE)

lemma IMAGE_INSERT: "ALL (x::'a::type => 'b::type) (xa::'a::type) xb::'a::type => bool.
   IMAGE x (INSERT xa xb) = INSERT (x xa) (IMAGE x xb)"
  by (import pred_set IMAGE_INSERT)

lemma IMAGE_EQ_EMPTY: "ALL (s::'a::type => bool) x::'a::type => 'b::type.
   (IMAGE x s = EMPTY) = (s = EMPTY)"
  by (import pred_set IMAGE_EQ_EMPTY)

lemma IMAGE_DELETE: "ALL (f::'a::type => 'b::type) (x::'a::type) s::'a::type => bool.
   ~ IN x s --> IMAGE f (DELETE s x) = IMAGE f s"
  by (import pred_set IMAGE_DELETE)

lemma IMAGE_UNION: "ALL (x::'a::type => 'b::type) (xa::'a::type => bool) xb::'a::type => bool.
   IMAGE x (pred_set.UNION xa xb) = pred_set.UNION (IMAGE x xa) (IMAGE x xb)"
  by (import pred_set IMAGE_UNION)

lemma IMAGE_SUBSET: "ALL (x::'a::type => bool) xa::'a::type => bool.
   SUBSET x xa -->
   (ALL xb::'a::type => 'b::type. SUBSET (IMAGE xb x) (IMAGE xb xa))"
  by (import pred_set IMAGE_SUBSET)

lemma IMAGE_INTER: "ALL (f::'a::type => 'b::type) (s::'a::type => bool) t::'a::type => bool.
   SUBSET (IMAGE f (pred_set.INTER s t))
    (pred_set.INTER (IMAGE f s) (IMAGE f t))"
  by (import pred_set IMAGE_INTER)

definition INJ :: "('a => 'b) => ('a => bool) => ('b => bool) => bool" where 
  "INJ ==
%(f::'a::type => 'b::type) (s::'a::type => bool) t::'b::type => bool.
   (ALL x::'a::type. IN x s --> IN (f x) t) &
   (ALL (x::'a::type) y::'a::type. IN x s & IN y s --> f x = f y --> x = y)"

lemma INJ_DEF: "ALL (f::'a::type => 'b::type) (s::'a::type => bool) t::'b::type => bool.
   INJ f s t =
   ((ALL x::'a::type. IN x s --> IN (f x) t) &
    (ALL (x::'a::type) y::'a::type.
        IN x s & IN y s --> f x = f y --> x = y))"
  by (import pred_set INJ_DEF)

lemma INJ_ID: "ALL x::'a::type => bool. INJ (%x::'a::type. x) x x"
  by (import pred_set INJ_ID)

lemma INJ_COMPOSE: "ALL (x::'a::type => 'b::type) (xa::'b::type => 'c::type)
   (xb::'a::type => bool) (xc::'b::type => bool) xd::'c::type => bool.
   INJ x xb xc & INJ xa xc xd --> INJ (xa o x) xb xd"
  by (import pred_set INJ_COMPOSE)

lemma INJ_EMPTY: "ALL x::'a::type => 'b::type.
   All (INJ x EMPTY) &
   (ALL xa::'a::type => bool. INJ x xa EMPTY = (xa = EMPTY))"
  by (import pred_set INJ_EMPTY)

definition SURJ :: "('a => 'b) => ('a => bool) => ('b => bool) => bool" where 
  "SURJ ==
%(f::'a::type => 'b::type) (s::'a::type => bool) t::'b::type => bool.
   (ALL x::'a::type. IN x s --> IN (f x) t) &
   (ALL x::'b::type. IN x t --> (EX y::'a::type. IN y s & f y = x))"

lemma SURJ_DEF: "ALL (f::'a::type => 'b::type) (s::'a::type => bool) t::'b::type => bool.
   SURJ f s t =
   ((ALL x::'a::type. IN x s --> IN (f x) t) &
    (ALL x::'b::type. IN x t --> (EX y::'a::type. IN y s & f y = x)))"
  by (import pred_set SURJ_DEF)

lemma SURJ_ID: "ALL x::'a::type => bool. SURJ (%x::'a::type. x) x x"
  by (import pred_set SURJ_ID)

lemma SURJ_COMPOSE: "ALL (x::'a::type => 'b::type) (xa::'b::type => 'c::type)
   (xb::'a::type => bool) (xc::'b::type => bool) xd::'c::type => bool.
   SURJ x xb xc & SURJ xa xc xd --> SURJ (xa o x) xb xd"
  by (import pred_set SURJ_COMPOSE)

lemma SURJ_EMPTY: "ALL x::'a::type => 'b::type.
   (ALL xa::'b::type => bool. SURJ x EMPTY xa = (xa = EMPTY)) &
   (ALL xa::'a::type => bool. SURJ x xa EMPTY = (xa = EMPTY))"
  by (import pred_set SURJ_EMPTY)

lemma IMAGE_SURJ: "ALL (x::'a::type => 'b::type) (xa::'a::type => bool) xb::'b::type => bool.
   SURJ x xa xb = (IMAGE x xa = xb)"
  by (import pred_set IMAGE_SURJ)

definition BIJ :: "('a => 'b) => ('a => bool) => ('b => bool) => bool" where 
  "BIJ ==
%(f::'a::type => 'b::type) (s::'a::type => bool) t::'b::type => bool.
   INJ f s t & SURJ f s t"

lemma BIJ_DEF: "ALL (f::'a::type => 'b::type) (s::'a::type => bool) t::'b::type => bool.
   BIJ f s t = (INJ f s t & SURJ f s t)"
  by (import pred_set BIJ_DEF)

lemma BIJ_ID: "ALL x::'a::type => bool. BIJ (%x::'a::type. x) x x"
  by (import pred_set BIJ_ID)

lemma BIJ_EMPTY: "ALL x::'a::type => 'b::type.
   (ALL xa::'b::type => bool. BIJ x EMPTY xa = (xa = EMPTY)) &
   (ALL xa::'a::type => bool. BIJ x xa EMPTY = (xa = EMPTY))"
  by (import pred_set BIJ_EMPTY)

lemma BIJ_COMPOSE: "ALL (x::'a::type => 'b::type) (xa::'b::type => 'c::type)
   (xb::'a::type => bool) (xc::'b::type => bool) xd::'c::type => bool.
   BIJ x xb xc & BIJ xa xc xd --> BIJ (xa o x) xb xd"
  by (import pred_set BIJ_COMPOSE)

consts
  LINV :: "('a => 'b) => ('a => bool) => 'b => 'a" 

specification (LINV) LINV_DEF: "ALL (f::'a::type => 'b::type) (s::'a::type => bool) t::'b::type => bool.
   INJ f s t --> (ALL x::'a::type. IN x s --> LINV f s (f x) = x)"
  by (import pred_set LINV_DEF)

consts
  RINV :: "('a => 'b) => ('a => bool) => 'b => 'a" 

specification (RINV) RINV_DEF: "ALL (f::'a::type => 'b::type) (s::'a::type => bool) t::'b::type => bool.
   SURJ f s t --> (ALL x::'b::type. IN x t --> f (RINV f s x) = x)"
  by (import pred_set RINV_DEF)

definition FINITE :: "('a => bool) => bool" where 
  "FINITE ==
%s::'a::type => bool.
   ALL P::('a::type => bool) => bool.
      P EMPTY &
      (ALL s::'a::type => bool.
          P s --> (ALL e::'a::type. P (INSERT e s))) -->
      P s"

lemma FINITE_DEF: "ALL s::'a::type => bool.
   FINITE s =
   (ALL P::('a::type => bool) => bool.
       P EMPTY &
       (ALL s::'a::type => bool.
           P s --> (ALL e::'a::type. P (INSERT e s))) -->
       P s)"
  by (import pred_set FINITE_DEF)

lemma FINITE_EMPTY: "FINITE EMPTY"
  by (import pred_set FINITE_EMPTY)

lemma FINITE_INDUCT: "ALL P::('a::type => bool) => bool.
   P EMPTY &
   (ALL s::'a::type => bool.
       FINITE s & P s -->
       (ALL e::'a::type. ~ IN e s --> P (INSERT e s))) -->
   (ALL s::'a::type => bool. FINITE s --> P s)"
  by (import pred_set FINITE_INDUCT)

lemma FINITE_INSERT: "ALL (x::'a::type) s::'a::type => bool. FINITE (INSERT x s) = FINITE s"
  by (import pred_set FINITE_INSERT)

lemma FINITE_DELETE: "ALL (x::'a::type) s::'a::type => bool. FINITE (DELETE s x) = FINITE s"
  by (import pred_set FINITE_DELETE)

lemma FINITE_UNION: "ALL (s::'a::type => bool) t::'a::type => bool.
   FINITE (pred_set.UNION s t) = (FINITE s & FINITE t)"
  by (import pred_set FINITE_UNION)

lemma INTER_FINITE: "ALL s::'a::type => bool.
   FINITE s --> (ALL t::'a::type => bool. FINITE (pred_set.INTER s t))"
  by (import pred_set INTER_FINITE)

lemma SUBSET_FINITE: "ALL s::'a::type => bool.
   FINITE s --> (ALL t::'a::type => bool. SUBSET t s --> FINITE t)"
  by (import pred_set SUBSET_FINITE)

lemma PSUBSET_FINITE: "ALL x::'a::type => bool.
   FINITE x --> (ALL xa::'a::type => bool. PSUBSET xa x --> FINITE xa)"
  by (import pred_set PSUBSET_FINITE)

lemma FINITE_DIFF: "ALL s::'a::type => bool.
   FINITE s --> (ALL t::'a::type => bool. FINITE (DIFF s t))"
  by (import pred_set FINITE_DIFF)

lemma FINITE_SING: "ALL x::'a::type. FINITE (INSERT x EMPTY)"
  by (import pred_set FINITE_SING)

lemma SING_FINITE: "ALL x::'a::type => bool. SING x --> FINITE x"
  by (import pred_set SING_FINITE)

lemma IMAGE_FINITE: "ALL s::'a::type => bool.
   FINITE s --> (ALL f::'a::type => 'b::type. FINITE (IMAGE f s))"
  by (import pred_set IMAGE_FINITE)

consts
  CARD :: "('a => bool) => nat" 

specification (CARD) CARD_DEF: "(op &::bool => bool => bool)
 ((op =::nat => nat => bool)
   ((CARD::('a::type => bool) => nat) (EMPTY::'a::type => bool)) (0::nat))
 ((All::(('a::type => bool) => bool) => bool)
   (%s::'a::type => bool.
       (op -->::bool => bool => bool)
        ((FINITE::('a::type => bool) => bool) s)
        ((All::('a::type => bool) => bool)
          (%x::'a::type.
              (op =::nat => nat => bool)
               ((CARD::('a::type => bool) => nat)
                 ((INSERT::'a::type
                           => ('a::type => bool) => 'a::type => bool)
                   x s))
               ((If::bool => nat => nat => nat)
                 ((IN::'a::type => ('a::type => bool) => bool) x s)
                 ((CARD::('a::type => bool) => nat) s)
                 ((Suc::nat => nat)
                   ((CARD::('a::type => bool) => nat) s)))))))"
  by (import pred_set CARD_DEF)

lemma CARD_EMPTY: "CARD EMPTY = 0"
  by (import pred_set CARD_EMPTY)

lemma CARD_INSERT: "ALL s::'a::type => bool.
   FINITE s -->
   (ALL x::'a::type.
       CARD (INSERT x s) = (if IN x s then CARD s else Suc (CARD s)))"
  by (import pred_set CARD_INSERT)

lemma CARD_EQ_0: "ALL s::'a::type => bool. FINITE s --> (CARD s = 0) = (s = EMPTY)"
  by (import pred_set CARD_EQ_0)

lemma CARD_DELETE: "ALL s::'a::type => bool.
   FINITE s -->
   (ALL x::'a::type.
       CARD (DELETE s x) = (if IN x s then CARD s - 1 else CARD s))"
  by (import pred_set CARD_DELETE)

lemma CARD_INTER_LESS_EQ: "ALL s::'a::type => bool.
   FINITE s -->
   (ALL t::'a::type => bool. CARD (pred_set.INTER s t) <= CARD s)"
  by (import pred_set CARD_INTER_LESS_EQ)

lemma CARD_UNION: "ALL s::'a::type => bool.
   FINITE s -->
   (ALL t::'a::type => bool.
       FINITE t -->
       CARD (pred_set.UNION s t) + CARD (pred_set.INTER s t) =
       CARD s + CARD t)"
  by (import pred_set CARD_UNION)

lemma CARD_SUBSET: "ALL s::'a::type => bool.
   FINITE s --> (ALL t::'a::type => bool. SUBSET t s --> CARD t <= CARD s)"
  by (import pred_set CARD_SUBSET)

lemma CARD_PSUBSET: "ALL s::'a::type => bool.
   FINITE s --> (ALL t::'a::type => bool. PSUBSET t s --> CARD t < CARD s)"
  by (import pred_set CARD_PSUBSET)

lemma CARD_SING: "ALL x::'a::type. CARD (INSERT x EMPTY) = 1"
  by (import pred_set CARD_SING)

lemma SING_IFF_CARD1: "ALL x::'a::type => bool. SING x = (CARD x = 1 & FINITE x)"
  by (import pred_set SING_IFF_CARD1)

lemma CARD_DIFF: "ALL t::'a::type => bool.
   FINITE t -->
   (ALL s::'a::type => bool.
       FINITE s --> CARD (DIFF s t) = CARD s - CARD (pred_set.INTER s t))"
  by (import pred_set CARD_DIFF)

lemma LESS_CARD_DIFF: "ALL t::'a::type => bool.
   FINITE t -->
   (ALL s::'a::type => bool.
       FINITE s --> CARD t < CARD s --> 0 < CARD (DIFF s t))"
  by (import pred_set LESS_CARD_DIFF)

lemma FINITE_COMPLETE_INDUCTION: "ALL P::('a::type => bool) => bool.
   (ALL x::'a::type => bool.
       (ALL y::'a::type => bool. PSUBSET y x --> P y) -->
       FINITE x --> P x) -->
   (ALL x::'a::type => bool. FINITE x --> P x)"
  by (import pred_set FINITE_COMPLETE_INDUCTION)

definition INFINITE :: "('a => bool) => bool" where 
  "INFINITE == %s::'a::type => bool. ~ FINITE s"

lemma INFINITE_DEF: "ALL s::'a::type => bool. INFINITE s = (~ FINITE s)"
  by (import pred_set INFINITE_DEF)

lemma NOT_IN_FINITE: "(op =::bool => bool => bool)
 ((INFINITE::('a::type => bool) => bool) (pred_set.UNIV::'a::type => bool))
 ((All::(('a::type => bool) => bool) => bool)
   (%s::'a::type => bool.
       (op -->::bool => bool => bool)
        ((FINITE::('a::type => bool) => bool) s)
        ((Ex::('a::type => bool) => bool)
          (%x::'a::type.
              (Not::bool => bool)
               ((IN::'a::type => ('a::type => bool) => bool) x s)))))"
  by (import pred_set NOT_IN_FINITE)

lemma INFINITE_INHAB: "ALL x::'a::type => bool. INFINITE x --> (EX xa::'a::type. IN xa x)"
  by (import pred_set INFINITE_INHAB)

lemma IMAGE_11_INFINITE: "ALL f::'a::type => 'b::type.
   (ALL (x::'a::type) y::'a::type. f x = f y --> x = y) -->
   (ALL s::'a::type => bool. INFINITE s --> INFINITE (IMAGE f s))"
  by (import pred_set IMAGE_11_INFINITE)

lemma INFINITE_SUBSET: "ALL x::'a::type => bool.
   INFINITE x --> (ALL xa::'a::type => bool. SUBSET x xa --> INFINITE xa)"
  by (import pred_set INFINITE_SUBSET)

lemma IN_INFINITE_NOT_FINITE: "ALL (x::'a::type => bool) xa::'a::type => bool.
   INFINITE x & FINITE xa --> (EX xb::'a::type. IN xb x & ~ IN xb xa)"
  by (import pred_set IN_INFINITE_NOT_FINITE)

lemma INFINITE_UNIV: "(op =::bool => bool => bool)
 ((INFINITE::('a::type => bool) => bool) (pred_set.UNIV::'a::type => bool))
 ((Ex::(('a::type => 'a::type) => bool) => bool)
   (%f::'a::type => 'a::type.
       (op &::bool => bool => bool)
        ((All::('a::type => bool) => bool)
          (%x::'a::type.
              (All::('a::type => bool) => bool)
               (%y::'a::type.
                   (op -->::bool => bool => bool)
                    ((op =::'a::type => 'a::type => bool) (f x) (f y))
                    ((op =::'a::type => 'a::type => bool) x y))))
        ((Ex::('a::type => bool) => bool)
          (%y::'a::type.
              (All::('a::type => bool) => bool)
               (%x::'a::type.
                   (Not::bool => bool)
                    ((op =::'a::type => 'a::type => bool) (f x) y))))))"
  by (import pred_set INFINITE_UNIV)

lemma FINITE_PSUBSET_INFINITE: "ALL x::'a::type => bool.
   INFINITE x =
   (ALL xa::'a::type => bool. FINITE xa --> SUBSET xa x --> PSUBSET xa x)"
  by (import pred_set FINITE_PSUBSET_INFINITE)

lemma FINITE_PSUBSET_UNIV: "(op =::bool => bool => bool)
 ((INFINITE::('a::type => bool) => bool) (pred_set.UNIV::'a::type => bool))
 ((All::(('a::type => bool) => bool) => bool)
   (%s::'a::type => bool.
       (op -->::bool => bool => bool)
        ((FINITE::('a::type => bool) => bool) s)
        ((PSUBSET::('a::type => bool) => ('a::type => bool) => bool) s
          (pred_set.UNIV::'a::type => bool))))"
  by (import pred_set FINITE_PSUBSET_UNIV)

lemma INFINITE_DIFF_FINITE: "ALL (s::'a::type => bool) t::'a::type => bool.
   INFINITE s & FINITE t --> DIFF s t ~= EMPTY"
  by (import pred_set INFINITE_DIFF_FINITE)

lemma FINITE_ISO_NUM: "ALL s::'a::type => bool.
   FINITE s -->
   (EX f::nat => 'a::type.
       (ALL (n::nat) m::nat.
           n < CARD s & m < CARD s --> f n = f m --> n = m) &
       s = GSPEC (%n::nat. (f n, n < CARD s)))"
  by (import pred_set FINITE_ISO_NUM)

lemma FINITE_WEAK_ENUMERATE: "(All::(('a::type => bool) => bool) => bool)
 (%x::'a::type => bool.
     (op =::bool => bool => bool) ((FINITE::('a::type => bool) => bool) x)
      ((Ex::((nat => 'a::type) => bool) => bool)
        (%f::nat => 'a::type.
            (Ex::(nat => bool) => bool)
             (%b::nat.
                 (All::('a::type => bool) => bool)
                  (%e::'a::type.
                      (op =::bool => bool => bool)
                       ((IN::'a::type => ('a::type => bool) => bool) e x)
                       ((Ex::(nat => bool) => bool)
                         (%n::nat.
                             (op &::bool => bool => bool)
                              ((op <::nat => nat => bool) n b)
                              ((op =::'a::type => 'a::type => bool) e
                                (f n)))))))))"
  by (import pred_set FINITE_WEAK_ENUMERATE)

definition BIGUNION :: "(('a => bool) => bool) => 'a => bool" where 
  "BIGUNION ==
%P::('a::type => bool) => bool.
   GSPEC (%x::'a::type. (x, EX p::'a::type => bool. IN p P & IN x p))"

lemma BIGUNION: "ALL P::('a::type => bool) => bool.
   BIGUNION P =
   GSPEC (%x::'a::type. (x, EX p::'a::type => bool. IN p P & IN x p))"
  by (import pred_set BIGUNION)

lemma IN_BIGUNION: "ALL (x::'a::type) xa::('a::type => bool) => bool.
   IN x (BIGUNION xa) = (EX s::'a::type => bool. IN x s & IN s xa)"
  by (import pred_set IN_BIGUNION)

lemma BIGUNION_EMPTY: "BIGUNION EMPTY = EMPTY"
  by (import pred_set BIGUNION_EMPTY)

lemma BIGUNION_SING: "ALL x::'a::type => bool. BIGUNION (INSERT x EMPTY) = x"
  by (import pred_set BIGUNION_SING)

lemma BIGUNION_UNION: "ALL (x::('a::type => bool) => bool) xa::('a::type => bool) => bool.
   BIGUNION (pred_set.UNION x xa) =
   pred_set.UNION (BIGUNION x) (BIGUNION xa)"
  by (import pred_set BIGUNION_UNION)

lemma DISJOINT_BIGUNION: "(ALL (s::('a::type => bool) => bool) t::'a::type => bool.
    DISJOINT (BIGUNION s) t =
    (ALL s'::'a::type => bool. IN s' s --> DISJOINT s' t)) &
(ALL (x::('a::type => bool) => bool) xa::'a::type => bool.
    DISJOINT xa (BIGUNION x) =
    (ALL xb::'a::type => bool. IN xb x --> DISJOINT xa xb))"
  by (import pred_set DISJOINT_BIGUNION)

lemma BIGUNION_INSERT: "ALL (x::'a::type => bool) xa::('a::type => bool) => bool.
   BIGUNION (INSERT x xa) = pred_set.UNION x (BIGUNION xa)"
  by (import pred_set BIGUNION_INSERT)

lemma BIGUNION_SUBSET: "ALL (X::'a::type => bool) P::('a::type => bool) => bool.
   SUBSET (BIGUNION P) X = (ALL Y::'a::type => bool. IN Y P --> SUBSET Y X)"
  by (import pred_set BIGUNION_SUBSET)

lemma FINITE_BIGUNION: "ALL x::('a::type => bool) => bool.
   FINITE x & (ALL s::'a::type => bool. IN s x --> FINITE s) -->
   FINITE (BIGUNION x)"
  by (import pred_set FINITE_BIGUNION)

definition BIGINTER :: "(('a => bool) => bool) => 'a => bool" where 
  "BIGINTER ==
%B::('a::type => bool) => bool.
   GSPEC (%x::'a::type. (x, ALL P::'a::type => bool. IN P B --> IN x P))"

lemma BIGINTER: "ALL B::('a::type => bool) => bool.
   BIGINTER B =
   GSPEC (%x::'a::type. (x, ALL P::'a::type => bool. IN P B --> IN x P))"
  by (import pred_set BIGINTER)

lemma IN_BIGINTER: "IN (x::'a::type) (BIGINTER (B::('a::type => bool) => bool)) =
(ALL P::'a::type => bool. IN P B --> IN x P)"
  by (import pred_set IN_BIGINTER)

lemma BIGINTER_INSERT: "ALL (P::'a::type => bool) B::('a::type => bool) => bool.
   BIGINTER (INSERT P B) = pred_set.INTER P (BIGINTER B)"
  by (import pred_set BIGINTER_INSERT)

lemma BIGINTER_EMPTY: "BIGINTER EMPTY = pred_set.UNIV"
  by (import pred_set BIGINTER_EMPTY)

lemma BIGINTER_INTER: "ALL (x::'a::type => bool) xa::'a::type => bool.
   BIGINTER (INSERT x (INSERT xa EMPTY)) = pred_set.INTER x xa"
  by (import pred_set BIGINTER_INTER)

lemma BIGINTER_SING: "ALL x::'a::type => bool. BIGINTER (INSERT x EMPTY) = x"
  by (import pred_set BIGINTER_SING)

lemma SUBSET_BIGINTER: "ALL (X::'a::type => bool) P::('a::type => bool) => bool.
   SUBSET X (BIGINTER P) = (ALL x::'a::type => bool. IN x P --> SUBSET X x)"
  by (import pred_set SUBSET_BIGINTER)

lemma DISJOINT_BIGINTER: "ALL (x::'a::type => bool) (xa::'a::type => bool)
   xb::('a::type => bool) => bool.
   IN xa xb & DISJOINT xa x -->
   DISJOINT x (BIGINTER xb) & DISJOINT (BIGINTER xb) x"
  by (import pred_set DISJOINT_BIGINTER)

definition CROSS :: "('a => bool) => ('b => bool) => 'a * 'b => bool" where 
  "CROSS ==
%(P::'a::type => bool) Q::'b::type => bool.
   GSPEC (%p::'a::type * 'b::type. (p, IN (fst p) P & IN (snd p) Q))"

lemma CROSS_DEF: "ALL (P::'a::type => bool) Q::'b::type => bool.
   CROSS P Q =
   GSPEC (%p::'a::type * 'b::type. (p, IN (fst p) P & IN (snd p) Q))"
  by (import pred_set CROSS_DEF)

lemma IN_CROSS: "ALL (x::'a::type => bool) (xa::'b::type => bool) xb::'a::type * 'b::type.
   IN xb (CROSS x xa) = (IN (fst xb) x & IN (snd xb) xa)"
  by (import pred_set IN_CROSS)

lemma CROSS_EMPTY: "ALL x::'a::type => bool. CROSS x EMPTY = EMPTY & CROSS EMPTY x = EMPTY"
  by (import pred_set CROSS_EMPTY)

lemma CROSS_INSERT_LEFT: "ALL (x::'a::type => bool) (xa::'b::type => bool) xb::'a::type.
   CROSS (INSERT xb x) xa =
   pred_set.UNION (CROSS (INSERT xb EMPTY) xa) (CROSS x xa)"
  by (import pred_set CROSS_INSERT_LEFT)

lemma CROSS_INSERT_RIGHT: "ALL (x::'a::type => bool) (xa::'b::type => bool) xb::'b::type.
   CROSS x (INSERT xb xa) =
   pred_set.UNION (CROSS x (INSERT xb EMPTY)) (CROSS x xa)"
  by (import pred_set CROSS_INSERT_RIGHT)

lemma FINITE_CROSS: "ALL (x::'a::type => bool) xa::'b::type => bool.
   FINITE x & FINITE xa --> FINITE (CROSS x xa)"
  by (import pred_set FINITE_CROSS)

lemma CROSS_SINGS: "ALL (x::'a::type) xa::'b::type.
   CROSS (INSERT x EMPTY) (INSERT xa EMPTY) = INSERT (x, xa) EMPTY"
  by (import pred_set CROSS_SINGS)

lemma CARD_SING_CROSS: "ALL (x::'a::type) s::'b::type => bool.
   FINITE s --> CARD (CROSS (INSERT x EMPTY) s) = CARD s"
  by (import pred_set CARD_SING_CROSS)

lemma CARD_CROSS: "ALL (x::'a::type => bool) xa::'b::type => bool.
   FINITE x & FINITE xa --> CARD (CROSS x xa) = CARD x * CARD xa"
  by (import pred_set CARD_CROSS)

lemma CROSS_SUBSET: "ALL (x::'a::type => bool) (xa::'b::type => bool) (xb::'a::type => bool)
   xc::'b::type => bool.
   SUBSET (CROSS xb xc) (CROSS x xa) =
   (xb = EMPTY | xc = EMPTY | SUBSET xb x & SUBSET xc xa)"
  by (import pred_set CROSS_SUBSET)

lemma FINITE_CROSS_EQ: "ALL (P::'a::type => bool) Q::'b::type => bool.
   FINITE (CROSS P Q) = (P = EMPTY | Q = EMPTY | FINITE P & FINITE Q)"
  by (import pred_set FINITE_CROSS_EQ)

definition COMPL :: "('a => bool) => 'a => bool" where 
  "COMPL == DIFF pred_set.UNIV"

lemma COMPL_DEF: "ALL P::'a::type => bool. COMPL P = DIFF pred_set.UNIV P"
  by (import pred_set COMPL_DEF)

lemma IN_COMPL: "ALL (x::'a::type) xa::'a::type => bool. IN x (COMPL xa) = (~ IN x xa)"
  by (import pred_set IN_COMPL)

lemma COMPL_COMPL: "ALL x::'a::type => bool. COMPL (COMPL x) = x"
  by (import pred_set COMPL_COMPL)

lemma COMPL_CLAUSES: "ALL x::'a::type => bool.
   pred_set.INTER (COMPL x) x = EMPTY &
   pred_set.UNION (COMPL x) x = pred_set.UNIV"
  by (import pred_set COMPL_CLAUSES)

lemma COMPL_SPLITS: "ALL (x::'a::type => bool) xa::'a::type => bool.
   pred_set.UNION (pred_set.INTER x xa) (pred_set.INTER (COMPL x) xa) = xa"
  by (import pred_set COMPL_SPLITS)

lemma INTER_UNION_COMPL: "ALL (x::'a::type => bool) xa::'a::type => bool.
   pred_set.INTER x xa = COMPL (pred_set.UNION (COMPL x) (COMPL xa))"
  by (import pred_set INTER_UNION_COMPL)

lemma COMPL_EMPTY: "COMPL EMPTY = pred_set.UNIV"
  by (import pred_set COMPL_EMPTY)

consts
  count :: "nat => nat => bool" 

defs
  count_primdef: "count == %n::nat. GSPEC (%m::nat. (m, m < n))"

lemma count_def: "ALL n::nat. count n = GSPEC (%m::nat. (m, m < n))"
  by (import pred_set count_def)

lemma IN_COUNT: "ALL (m::nat) n::nat. IN m (count n) = (m < n)"
  by (import pred_set IN_COUNT)

lemma COUNT_ZERO: "count 0 = EMPTY"
  by (import pred_set COUNT_ZERO)

lemma COUNT_SUC: "ALL n::nat. count (Suc n) = INSERT n (count n)"
  by (import pred_set COUNT_SUC)

lemma FINITE_COUNT: "ALL n::nat. FINITE (count n)"
  by (import pred_set FINITE_COUNT)

lemma CARD_COUNT: "ALL n::nat. CARD (count n) = n"
  by (import pred_set CARD_COUNT)

definition ITSET_tupled :: "('a => 'b => 'b) => ('a => bool) * 'b => 'b" where 
  "ITSET_tupled ==
%f::'a::type => 'b::type => 'b::type.
   WFREC
    (SOME R::('a::type => bool) * 'b::type
             => ('a::type => bool) * 'b::type => bool.
        WF R &
        (ALL (b::'b::type) s::'a::type => bool.
            FINITE s & s ~= EMPTY --> R (REST s, f (CHOICE s) b) (s, b)))
    (%(ITSET_tupled::('a::type => bool) * 'b::type => 'b::type)
        (v::'a::type => bool, v1::'b::type).
        if FINITE v
        then if v = EMPTY then v1
             else ITSET_tupled (REST v, f (CHOICE v) v1)
        else ARB)"

lemma ITSET_tupled_primitive_def: "ALL f::'a::type => 'b::type => 'b::type.
   ITSET_tupled f =
   WFREC
    (SOME R::('a::type => bool) * 'b::type
             => ('a::type => bool) * 'b::type => bool.
        WF R &
        (ALL (b::'b::type) s::'a::type => bool.
            FINITE s & s ~= EMPTY --> R (REST s, f (CHOICE s) b) (s, b)))
    (%(ITSET_tupled::('a::type => bool) * 'b::type => 'b::type)
        (v::'a::type => bool, v1::'b::type).
        if FINITE v
        then if v = EMPTY then v1
             else ITSET_tupled (REST v, f (CHOICE v) v1)
        else ARB)"
  by (import pred_set ITSET_tupled_primitive_def)

definition ITSET :: "('a => 'b => 'b) => ('a => bool) => 'b => 'b" where 
  "ITSET ==
%(f::'a::type => 'b::type => 'b::type) (x::'a::type => bool) x1::'b::type.
   ITSET_tupled f (x, x1)"

lemma ITSET_curried_def: "ALL (f::'a::type => 'b::type => 'b::type) (x::'a::type => bool)
   x1::'b::type. ITSET f x x1 = ITSET_tupled f (x, x1)"
  by (import pred_set ITSET_curried_def)

lemma ITSET_IND: "ALL P::('a::type => bool) => 'b::type => bool.
   (ALL (s::'a::type => bool) b::'b::type.
       (FINITE s & s ~= EMPTY -->
        P (REST s) ((f::'a::type => 'b::type => 'b::type) (CHOICE s) b)) -->
       P s b) -->
   (ALL v::'a::type => bool. All (P v))"
  by (import pred_set ITSET_IND)

lemma ITSET_THM: "ALL (s::'a::type => bool) (f::'a::type => 'b::type => 'b::type) b::'b::type.
   FINITE s -->
   ITSET f s b =
   (if s = EMPTY then b else ITSET f (REST s) (f (CHOICE s) b))"
  by (import pred_set ITSET_THM)

lemma ITSET_EMPTY: "ALL (x::'a::type => 'b::type => 'b::type) xa::'b::type.
   ITSET x EMPTY xa = xa"
  by (import pred_set ITSET_EMPTY)

;end_setup

;setup_theory operator

definition ASSOC :: "('a => 'a => 'a) => bool" where 
  "ASSOC ==
%f::'a::type => 'a::type => 'a::type.
   ALL (x::'a::type) (y::'a::type) z::'a::type. f x (f y z) = f (f x y) z"

lemma ASSOC_DEF: "ALL f::'a::type => 'a::type => 'a::type.
   ASSOC f =
   (ALL (x::'a::type) (y::'a::type) z::'a::type. f x (f y z) = f (f x y) z)"
  by (import operator ASSOC_DEF)

definition COMM :: "('a => 'a => 'b) => bool" where 
  "COMM ==
%f::'a::type => 'a::type => 'b::type.
   ALL (x::'a::type) y::'a::type. f x y = f y x"

lemma COMM_DEF: "ALL f::'a::type => 'a::type => 'b::type.
   COMM f = (ALL (x::'a::type) y::'a::type. f x y = f y x)"
  by (import operator COMM_DEF)

definition FCOMM :: "('a => 'b => 'a) => ('c => 'a => 'a) => bool" where 
  "FCOMM ==
%(f::'a::type => 'b::type => 'a::type) g::'c::type => 'a::type => 'a::type.
   ALL (x::'c::type) (y::'a::type) z::'b::type. g x (f y z) = f (g x y) z"

lemma FCOMM_DEF: "ALL (f::'a::type => 'b::type => 'a::type)
   g::'c::type => 'a::type => 'a::type.
   FCOMM f g =
   (ALL (x::'c::type) (y::'a::type) z::'b::type. g x (f y z) = f (g x y) z)"
  by (import operator FCOMM_DEF)

definition RIGHT_ID :: "('a => 'b => 'a) => 'b => bool" where 
  "RIGHT_ID ==
%(f::'a::type => 'b::type => 'a::type) e::'b::type.
   ALL x::'a::type. f x e = x"

lemma RIGHT_ID_DEF: "ALL (f::'a::type => 'b::type => 'a::type) e::'b::type.
   RIGHT_ID f e = (ALL x::'a::type. f x e = x)"
  by (import operator RIGHT_ID_DEF)

definition LEFT_ID :: "('a => 'b => 'b) => 'a => bool" where 
  "LEFT_ID ==
%(f::'a::type => 'b::type => 'b::type) e::'a::type.
   ALL x::'b::type. f e x = x"

lemma LEFT_ID_DEF: "ALL (f::'a::type => 'b::type => 'b::type) e::'a::type.
   LEFT_ID f e = (ALL x::'b::type. f e x = x)"
  by (import operator LEFT_ID_DEF)

definition MONOID :: "('a => 'a => 'a) => 'a => bool" where 
  "MONOID ==
%(f::'a::type => 'a::type => 'a::type) e::'a::type.
   ASSOC f & RIGHT_ID f e & LEFT_ID f e"

lemma MONOID_DEF: "ALL (f::'a::type => 'a::type => 'a::type) e::'a::type.
   MONOID f e = (ASSOC f & RIGHT_ID f e & LEFT_ID f e)"
  by (import operator MONOID_DEF)

lemma ASSOC_CONJ: "ASSOC op &"
  by (import operator ASSOC_CONJ)

lemma ASSOC_DISJ: "ASSOC op |"
  by (import operator ASSOC_DISJ)

lemma FCOMM_ASSOC: "ALL x::'a::type => 'a::type => 'a::type. FCOMM x x = ASSOC x"
  by (import operator FCOMM_ASSOC)

lemma MONOID_CONJ_T: "MONOID op & True"
  by (import operator MONOID_CONJ_T)

lemma MONOID_DISJ_F: "MONOID op | False"
  by (import operator MONOID_DISJ_F)

;end_setup

;setup_theory rich_list

consts
  SNOC :: "'a => 'a list => 'a list" 

specification (SNOC) SNOC: "(ALL x::'a::type. SNOC x [] = [x]) &
(ALL (x::'a::type) (x'::'a::type) l::'a::type list.
    SNOC x (x' # l) = x' # SNOC x l)"
  by (import rich_list SNOC)

consts
  SCANL :: "('b => 'a => 'b) => 'b => 'a list => 'b list" 

specification (SCANL) SCANL: "(ALL (f::'b::type => 'a::type => 'b::type) e::'b::type.
    SCANL f e [] = [e]) &
(ALL (f::'b::type => 'a::type => 'b::type) (e::'b::type) (x::'a::type)
    l::'a::type list. SCANL f e (x # l) = e # SCANL f (f e x) l)"
  by (import rich_list SCANL)

consts
  SCANR :: "('a => 'b => 'b) => 'b => 'a list => 'b list" 

specification (SCANR) SCANR: "(ALL (f::'a::type => 'b::type => 'b::type) e::'b::type.
    SCANR f e [] = [e]) &
(ALL (f::'a::type => 'b::type => 'b::type) (e::'b::type) (x::'a::type)
    l::'a::type list.
    SCANR f e (x # l) = f x (hd (SCANR f e l)) # SCANR f e l)"
  by (import rich_list SCANR)

lemma IS_EL_DEF: "ALL (x::'a::type) l::'a::type list. x mem l = list_ex (op = x) l"
  by (import rich_list IS_EL_DEF)

definition AND_EL :: "bool list => bool" where 
  "AND_EL == list_all I"

lemma AND_EL_DEF: "AND_EL = list_all I"
  by (import rich_list AND_EL_DEF)

definition OR_EL :: "bool list => bool" where 
  "OR_EL == list_ex I"

lemma OR_EL_DEF: "OR_EL = list_ex I"
  by (import rich_list OR_EL_DEF)

consts
  FIRSTN :: "nat => 'a list => 'a list" 

specification (FIRSTN) FIRSTN: "(ALL l::'a::type list. FIRSTN 0 l = []) &
(ALL (n::nat) (x::'a::type) l::'a::type list.
    FIRSTN (Suc n) (x # l) = x # FIRSTN n l)"
  by (import rich_list FIRSTN)

consts
  BUTFIRSTN :: "nat => 'a list => 'a list" 

specification (BUTFIRSTN) BUTFIRSTN: "(ALL l::'a::type list. BUTFIRSTN 0 l = l) &
(ALL (n::nat) (x::'a::type) l::'a::type list.
    BUTFIRSTN (Suc n) (x # l) = BUTFIRSTN n l)"
  by (import rich_list BUTFIRSTN)

consts
  SEG :: "nat => nat => 'a list => 'a list" 

specification (SEG) SEG: "(ALL (k::nat) l::'a::type list. SEG 0 k l = []) &
(ALL (m::nat) (x::'a::type) l::'a::type list.
    SEG (Suc m) 0 (x # l) = x # SEG m 0 l) &
(ALL (m::nat) (k::nat) (x::'a::type) l::'a::type list.
    SEG (Suc m) (Suc k) (x # l) = SEG (Suc m) k l)"
  by (import rich_list SEG)

lemma LAST: "ALL (x::'a::type) l::'a::type list. last (SNOC x l) = x"
  by (import rich_list LAST)

lemma BUTLAST: "ALL (x::'a::type) l::'a::type list. butlast (SNOC x l) = l"
  by (import rich_list BUTLAST)

consts
  LASTN :: "nat => 'a list => 'a list" 

specification (LASTN) LASTN: "(ALL l::'a::type list. LASTN 0 l = []) &
(ALL (n::nat) (x::'a::type) l::'a::type list.
    LASTN (Suc n) (SNOC x l) = SNOC x (LASTN n l))"
  by (import rich_list LASTN)

consts
  BUTLASTN :: "nat => 'a list => 'a list" 

specification (BUTLASTN) BUTLASTN: "(ALL l::'a::type list. BUTLASTN 0 l = l) &
(ALL (n::nat) (x::'a::type) l::'a::type list.
    BUTLASTN (Suc n) (SNOC x l) = BUTLASTN n l)"
  by (import rich_list BUTLASTN)

lemma EL: "(ALL x::'a::type list. EL 0 x = hd x) &
(ALL (x::nat) xa::'a::type list. EL (Suc x) xa = EL x (tl xa))"
  by (import rich_list EL)

consts
  ELL :: "nat => 'a list => 'a" 

specification (ELL) ELL: "(ALL l::'a::type list. ELL 0 l = last l) &
(ALL (n::nat) l::'a::type list. ELL (Suc n) l = ELL n (butlast l))"
  by (import rich_list ELL)

consts
  IS_PREFIX :: "'a list => 'a list => bool" 

specification (IS_PREFIX) IS_PREFIX: "(ALL l::'a::type list. IS_PREFIX l [] = True) &
(ALL (x::'a::type) l::'a::type list. IS_PREFIX [] (x # l) = False) &
(ALL (x1::'a::type) (l1::'a::type list) (x2::'a::type) l2::'a::type list.
    IS_PREFIX (x1 # l1) (x2 # l2) = (x1 = x2 & IS_PREFIX l1 l2))"
  by (import rich_list IS_PREFIX)

lemma SNOC_APPEND: "ALL (x::'a::type) l::'a::type list. SNOC x l = l @ [x]"
  by (import rich_list SNOC_APPEND)

lemma REVERSE: "rev [] = [] &
(ALL (x::'a::type) xa::'a::type list. rev (x # xa) = SNOC x (rev xa))"
  by (import rich_list REVERSE)

lemma REVERSE_SNOC: "ALL (x::'a::type) l::'a::type list. rev (SNOC x l) = x # rev l"
  by (import rich_list REVERSE_SNOC)

lemma SNOC_Axiom: "ALL (e::'b::type) f::'a::type => 'a::type list => 'b::type => 'b::type.
   EX x::'a::type list => 'b::type.
      x [] = e &
      (ALL (xa::'a::type) l::'a::type list. x (SNOC xa l) = f xa l (x l))"
  by (import rich_list SNOC_Axiom)

consts
  IS_SUFFIX :: "'a list => 'a list => bool" 

specification (IS_SUFFIX) IS_SUFFIX: "(ALL l::'a::type list. IS_SUFFIX l [] = True) &
(ALL (x::'a::type) l::'a::type list. IS_SUFFIX [] (SNOC x l) = False) &
(ALL (x1::'a::type) (l1::'a::type list) (x2::'a::type) l2::'a::type list.
    IS_SUFFIX (SNOC x1 l1) (SNOC x2 l2) = (x1 = x2 & IS_SUFFIX l1 l2))"
  by (import rich_list IS_SUFFIX)

consts
  IS_SUBLIST :: "'a list => 'a list => bool" 

specification (IS_SUBLIST) IS_SUBLIST: "(ALL l::'a::type list. IS_SUBLIST l [] = True) &
(ALL (x::'a::type) l::'a::type list. IS_SUBLIST [] (x # l) = False) &
(ALL (x1::'a::type) (l1::'a::type list) (x2::'a::type) l2::'a::type list.
    IS_SUBLIST (x1 # l1) (x2 # l2) =
    (x1 = x2 & IS_PREFIX l1 l2 | IS_SUBLIST l1 (x2 # l2)))"
  by (import rich_list IS_SUBLIST)

consts
  SPLITP :: "('a => bool) => 'a list => 'a list * 'a list" 

specification (SPLITP) SPLITP: "(ALL P::'a::type => bool. SPLITP P [] = ([], [])) &
(ALL (P::'a::type => bool) (x::'a::type) l::'a::type list.
    SPLITP P (x # l) =
    (if P x then ([], x # l) else (x # fst (SPLITP P l), snd (SPLITP P l))))"
  by (import rich_list SPLITP)

definition PREFIX :: "('a => bool) => 'a list => 'a list" where 
  "PREFIX == %(P::'a::type => bool) l::'a::type list. fst (SPLITP (Not o P) l)"

lemma PREFIX_DEF: "ALL (P::'a::type => bool) l::'a::type list.
   PREFIX P l = fst (SPLITP (Not o P) l)"
  by (import rich_list PREFIX_DEF)

definition SUFFIX :: "('a => bool) => 'a list => 'a list" where 
  "SUFFIX ==
%P::'a::type => bool.
   foldl (%(l'::'a::type list) x::'a::type. if P x then SNOC x l' else [])
    []"

lemma SUFFIX_DEF: "ALL (P::'a::type => bool) l::'a::type list.
   SUFFIX P l =
   foldl (%(l'::'a::type list) x::'a::type. if P x then SNOC x l' else [])
    [] l"
  by (import rich_list SUFFIX_DEF)

definition UNZIP_FST :: "('a * 'b) list => 'a list" where 
  "UNZIP_FST == %l::('a::type * 'b::type) list. fst (unzip l)"

lemma UNZIP_FST_DEF: "ALL l::('a::type * 'b::type) list. UNZIP_FST l = fst (unzip l)"
  by (import rich_list UNZIP_FST_DEF)

definition UNZIP_SND :: "('a * 'b) list => 'b list" where 
  "UNZIP_SND == %l::('a::type * 'b::type) list. snd (unzip l)"

lemma UNZIP_SND_DEF: "ALL l::('a::type * 'b::type) list. UNZIP_SND l = snd (unzip l)"
  by (import rich_list UNZIP_SND_DEF)

consts
  GENLIST :: "(nat => 'a) => nat => 'a list" 

specification (GENLIST) GENLIST: "(ALL f::nat => 'a::type. GENLIST f 0 = []) &
(ALL (f::nat => 'a::type) n::nat.
    GENLIST f (Suc n) = SNOC (f n) (GENLIST f n))"
  by (import rich_list GENLIST)

consts
  REPLICATE :: "nat => 'a => 'a list" 

specification (REPLICATE) REPLICATE: "(ALL x::'a::type. REPLICATE 0 x = []) &
(ALL (n::nat) x::'a::type. REPLICATE (Suc n) x = x # REPLICATE n x)"
  by (import rich_list REPLICATE)

lemma LENGTH_MAP2: "ALL (l1::'a::type list) l2::'b::type list.
   length l1 = length l2 -->
   (ALL f::'a::type => 'b::type => 'c::type.
       length (map2 f l1 l2) = length l1 &
       length (map2 f l1 l2) = length l2)"
  by (import rich_list LENGTH_MAP2)

lemma NULL_EQ_NIL: "ALL l::'a::type list. null l = (l = [])"
  by (import rich_list NULL_EQ_NIL)

lemma LENGTH_EQ: "ALL (x::'a::type list) y::'a::type list. x = y --> length x = length y"
  by (import rich_list LENGTH_EQ)

lemma LENGTH_NOT_NULL: "ALL l::'a::type list. (0 < length l) = (~ null l)"
  by (import rich_list LENGTH_NOT_NULL)

lemma SNOC_INDUCT: "ALL P::'a::type list => bool.
   P [] &
   (ALL l::'a::type list. P l --> (ALL x::'a::type. P (SNOC x l))) -->
   All P"
  by (import rich_list SNOC_INDUCT)

lemma SNOC_CASES: "ALL x'::'a::type list.
   x' = [] | (EX (x::'a::type) l::'a::type list. x' = SNOC x l)"
  by (import rich_list SNOC_CASES)

lemma LENGTH_SNOC: "ALL (x::'a::type) l::'a::type list. length (SNOC x l) = Suc (length l)"
  by (import rich_list LENGTH_SNOC)

lemma NOT_NIL_SNOC: "ALL (x::'a::type) xa::'a::type list. [] ~= SNOC x xa"
  by (import rich_list NOT_NIL_SNOC)

lemma NOT_SNOC_NIL: "ALL (x::'a::type) xa::'a::type list. SNOC x xa ~= []"
  by (import rich_list NOT_SNOC_NIL)

lemma SNOC_11: "ALL (x::'a::type) (l::'a::type list) (x'::'a::type) l'::'a::type list.
   (SNOC x l = SNOC x' l') = (x = x' & l = l')"
  by (import rich_list SNOC_11)

lemma SNOC_EQ_LENGTH_EQ: "ALL (x1::'a::type) (l1::'a::type list) (x2::'a::type) l2::'a::type list.
   SNOC x1 l1 = SNOC x2 l2 --> length l1 = length l2"
  by (import rich_list SNOC_EQ_LENGTH_EQ)

lemma SNOC_REVERSE_CONS: "ALL (x::'a::type) xa::'a::type list. SNOC x xa = rev (x # rev xa)"
  by (import rich_list SNOC_REVERSE_CONS)

lemma MAP_SNOC: "ALL (x::'a::type => 'b::type) (xa::'a::type) xb::'a::type list.
   map x (SNOC xa xb) = SNOC (x xa) (map x xb)"
  by (import rich_list MAP_SNOC)

lemma FOLDR_SNOC: "ALL (f::'a::type => 'b::type => 'b::type) (e::'b::type) (x::'a::type)
   l::'a::type list. foldr f (SNOC x l) e = foldr f l (f x e)"
  by (import rich_list FOLDR_SNOC)

lemma FOLDL_SNOC: "ALL (f::'b::type => 'a::type => 'b::type) (e::'b::type) (x::'a::type)
   l::'a::type list. foldl f e (SNOC x l) = f (foldl f e l) x"
  by (import rich_list FOLDL_SNOC)

lemma FOLDR_FOLDL: "ALL (f::'a::type => 'a::type => 'a::type) e::'a::type.
   MONOID f e --> (ALL l::'a::type list. foldr f l e = foldl f e l)"
  by (import rich_list FOLDR_FOLDL)

lemma LENGTH_FOLDR: "ALL l::'a::type list. length l = foldr (%x::'a::type. Suc) l 0"
  by (import rich_list LENGTH_FOLDR)

lemma LENGTH_FOLDL: "ALL l::'a::type list. length l = foldl (%(l'::nat) x::'a::type. Suc l') 0 l"
  by (import rich_list LENGTH_FOLDL)

lemma MAP_FOLDR: "ALL (f::'a::type => 'b::type) l::'a::type list.
   map f l = foldr (%x::'a::type. op # (f x)) l []"
  by (import rich_list MAP_FOLDR)

lemma MAP_FOLDL: "ALL (f::'a::type => 'b::type) l::'a::type list.
   map f l = foldl (%(l'::'b::type list) x::'a::type. SNOC (f x) l') [] l"
  by (import rich_list MAP_FOLDL)

lemma MAP_o: "ALL (f::'b::type => 'c::type) g::'a::type => 'b::type.
   map (f o g) = map f o map g"
  by (import rich_list MAP_o)

lemma FILTER_FOLDR: "ALL (P::'a::type => bool) l::'a::type list.
   filter P l =
   foldr (%(x::'a::type) l'::'a::type list. if P x then x # l' else l') l []"
  by (import rich_list FILTER_FOLDR)

lemma FILTER_SNOC: "ALL (P::'a::type => bool) (x::'a::type) l::'a::type list.
   filter P (SNOC x l) = (if P x then SNOC x (filter P l) else filter P l)"
  by (import rich_list FILTER_SNOC)

lemma FILTER_FOLDL: "ALL (P::'a::type => bool) l::'a::type list.
   filter P l =
   foldl (%(l'::'a::type list) x::'a::type. if P x then SNOC x l' else l')
    [] l"
  by (import rich_list FILTER_FOLDL)

lemma FILTER_COMM: "ALL (f1::'a::type => bool) (f2::'a::type => bool) l::'a::type list.
   filter f1 (filter f2 l) = filter f2 (filter f1 l)"
  by (import rich_list FILTER_COMM)

lemma FILTER_IDEM: "ALL (f::'a::type => bool) l::'a::type list.
   filter f (filter f l) = filter f l"
  by (import rich_list FILTER_IDEM)

lemma LENGTH_SEG: "ALL (n::nat) (k::nat) l::'a::type list.
   n + k <= length l --> length (SEG n k l) = n"
  by (import rich_list LENGTH_SEG)

lemma APPEND_NIL: "(ALL l::'a::type list. l @ [] = l) & (ALL x::'a::type list. [] @ x = x)"
  by (import rich_list APPEND_NIL)

lemma APPEND_SNOC: "ALL (l1::'a::type list) (x::'a::type) l2::'a::type list.
   l1 @ SNOC x l2 = SNOC x (l1 @ l2)"
  by (import rich_list APPEND_SNOC)

lemma APPEND_FOLDR: "ALL (l1::'a::type list) l2::'a::type list. l1 @ l2 = foldr op # l1 l2"
  by (import rich_list APPEND_FOLDR)

lemma APPEND_FOLDL: "ALL (l1::'a::type list) l2::'a::type list.
   l1 @ l2 = foldl (%(l'::'a::type list) x::'a::type. SNOC x l') l1 l2"
  by (import rich_list APPEND_FOLDL)

lemma CONS_APPEND: "ALL (x::'a::type) l::'a::type list. x # l = [x] @ l"
  by (import rich_list CONS_APPEND)

lemma ASSOC_APPEND: "ASSOC op @"
  by (import rich_list ASSOC_APPEND)

lemma MONOID_APPEND_NIL: "MONOID op @ []"
  by (import rich_list MONOID_APPEND_NIL)

lemma APPEND_LENGTH_EQ: "ALL (l1::'a::type list) l1'::'a::type list.
   length l1 = length l1' -->
   (ALL (l2::'a::type list) l2'::'a::type list.
       length l2 = length l2' -->
       (l1 @ l2 = l1' @ l2') = (l1 = l1' & l2 = l2'))"
  by (import rich_list APPEND_LENGTH_EQ)

lemma FLAT_SNOC: "ALL (x::'a::type list) l::'a::type list list.
   concat (SNOC x l) = concat l @ x"
  by (import rich_list FLAT_SNOC)

lemma FLAT_FOLDR: "ALL l::'a::type list list. concat l = foldr op @ l []"
  by (import rich_list FLAT_FOLDR)

lemma FLAT_FOLDL: "ALL l::'a::type list list. concat l = foldl op @ [] l"
  by (import rich_list FLAT_FOLDL)

lemma LENGTH_FLAT: "ALL l::'a::type list list. length (concat l) = sum (map size l)"
  by (import rich_list LENGTH_FLAT)

lemma REVERSE_FOLDR: "ALL l::'a::type list. rev l = foldr SNOC l []"
  by (import rich_list REVERSE_FOLDR)

lemma REVERSE_FOLDL: "ALL l::'a::type list.
   rev l = foldl (%(l'::'a::type list) x::'a::type. x # l') [] l"
  by (import rich_list REVERSE_FOLDL)

lemma ALL_EL_SNOC: "ALL (P::'a::type => bool) (x::'a::type) l::'a::type list.
   list_all P (SNOC x l) = (list_all P l & P x)"
  by (import rich_list ALL_EL_SNOC)

lemma ALL_EL_MAP: "ALL (P::'b::type => bool) (f::'a::type => 'b::type) l::'a::type list.
   list_all P (map f l) = list_all (P o f) l"
  by (import rich_list ALL_EL_MAP)

lemma SOME_EL_SNOC: "ALL (P::'a::type => bool) (x::'a::type) l::'a::type list.
   list_ex P (SNOC x l) = (P x | list_ex P l)"
  by (import rich_list SOME_EL_SNOC)

lemma IS_EL_SNOC: "ALL (y::'a::type) (x::'a::type) l::'a::type list.
   y mem SNOC x l = (y = x | y mem l)"
  by (import rich_list IS_EL_SNOC)

lemma SUM_SNOC: "ALL (x::nat) l::nat list. sum (SNOC x l) = sum l + x"
  by (import rich_list SUM_SNOC)

lemma SUM_FOLDL: "ALL l::nat list. sum l = foldl op + 0 l"
  by (import rich_list SUM_FOLDL)

lemma IS_PREFIX_APPEND: "ALL (l1::'a::type list) l2::'a::type list.
   IS_PREFIX l1 l2 = (EX l::'a::type list. l1 = l2 @ l)"
  by (import rich_list IS_PREFIX_APPEND)

lemma IS_SUFFIX_APPEND: "ALL (l1::'a::type list) l2::'a::type list.
   IS_SUFFIX l1 l2 = (EX l::'a::type list. l1 = l @ l2)"
  by (import rich_list IS_SUFFIX_APPEND)

lemma IS_SUBLIST_APPEND: "ALL (l1::'a::type list) l2::'a::type list.
   IS_SUBLIST l1 l2 =
   (EX (l::'a::type list) l'::'a::type list. l1 = l @ l2 @ l')"
  by (import rich_list IS_SUBLIST_APPEND)

lemma IS_PREFIX_IS_SUBLIST: "ALL (l1::'a::type list) l2::'a::type list.
   IS_PREFIX l1 l2 --> IS_SUBLIST l1 l2"
  by (import rich_list IS_PREFIX_IS_SUBLIST)

lemma IS_SUFFIX_IS_SUBLIST: "ALL (l1::'a::type list) l2::'a::type list.
   IS_SUFFIX l1 l2 --> IS_SUBLIST l1 l2"
  by (import rich_list IS_SUFFIX_IS_SUBLIST)

lemma IS_PREFIX_REVERSE: "ALL (l1::'a::type list) l2::'a::type list.
   IS_PREFIX (rev l1) (rev l2) = IS_SUFFIX l1 l2"
  by (import rich_list IS_PREFIX_REVERSE)

lemma IS_SUFFIX_REVERSE: "ALL (l2::'a::type list) l1::'a::type list.
   IS_SUFFIX (rev l1) (rev l2) = IS_PREFIX l1 l2"
  by (import rich_list IS_SUFFIX_REVERSE)

lemma IS_SUBLIST_REVERSE: "ALL (l1::'a::type list) l2::'a::type list.
   IS_SUBLIST (rev l1) (rev l2) = IS_SUBLIST l1 l2"
  by (import rich_list IS_SUBLIST_REVERSE)

lemma PREFIX_FOLDR: "ALL (P::'a::type => bool) x::'a::type list.
   PREFIX P x =
   foldr (%(x::'a::type) l'::'a::type list. if P x then x # l' else []) x []"
  by (import rich_list PREFIX_FOLDR)

lemma PREFIX: "(ALL x::'a::type => bool. PREFIX x [] = []) &
(ALL (x::'a::type => bool) (xa::'a::type) xb::'a::type list.
    PREFIX x (xa # xb) = (if x xa then xa # PREFIX x xb else []))"
  by (import rich_list PREFIX)

lemma IS_PREFIX_PREFIX: "ALL (P::'a::type => bool) l::'a::type list. IS_PREFIX l (PREFIX P l)"
  by (import rich_list IS_PREFIX_PREFIX)

lemma LENGTH_SCANL: "ALL (f::'b::type => 'a::type => 'b::type) (e::'b::type) l::'a::type list.
   length (SCANL f e l) = Suc (length l)"
  by (import rich_list LENGTH_SCANL)

lemma LENGTH_SCANR: "ALL (f::'a::type => 'b::type => 'b::type) (e::'b::type) l::'a::type list.
   length (SCANR f e l) = Suc (length l)"
  by (import rich_list LENGTH_SCANR)

lemma COMM_MONOID_FOLDL: "ALL x::'a::type => 'a::type => 'a::type.
   COMM x -->
   (ALL xa::'a::type.
       MONOID x xa -->
       (ALL (e::'a::type) l::'a::type list.
           foldl x e l = x e (foldl x xa l)))"
  by (import rich_list COMM_MONOID_FOLDL)

lemma COMM_MONOID_FOLDR: "ALL x::'a::type => 'a::type => 'a::type.
   COMM x -->
   (ALL xa::'a::type.
       MONOID x xa -->
       (ALL (e::'a::type) l::'a::type list.
           foldr x l e = x e (foldr x l xa)))"
  by (import rich_list COMM_MONOID_FOLDR)

lemma FCOMM_FOLDR_APPEND: "ALL (x::'a::type => 'a::type => 'a::type)
   xa::'b::type => 'a::type => 'a::type.
   FCOMM x xa -->
   (ALL xb::'a::type.
       LEFT_ID x xb -->
       (ALL (l1::'b::type list) l2::'b::type list.
           foldr xa (l1 @ l2) xb = x (foldr xa l1 xb) (foldr xa l2 xb)))"
  by (import rich_list FCOMM_FOLDR_APPEND)

lemma FCOMM_FOLDL_APPEND: "ALL (x::'a::type => 'b::type => 'a::type)
   xa::'a::type => 'a::type => 'a::type.
   FCOMM x xa -->
   (ALL xb::'a::type.
       RIGHT_ID xa xb -->
       (ALL (l1::'b::type list) l2::'b::type list.
           foldl x xb (l1 @ l2) = xa (foldl x xb l1) (foldl x xb l2)))"
  by (import rich_list FCOMM_FOLDL_APPEND)

lemma FOLDL_SINGLE: "ALL (x::'a::type => 'b::type => 'a::type) (xa::'a::type) xb::'b::type.
   foldl x xa [xb] = x xa xb"
  by (import rich_list FOLDL_SINGLE)

lemma FOLDR_SINGLE: "ALL (x::'a::type => 'b::type => 'b::type) (xa::'b::type) xb::'a::type.
   foldr x [xb] xa = x xb xa"
  by (import rich_list FOLDR_SINGLE)

lemma FOLDR_CONS_NIL: "ALL l::'a::type list. foldr op # l [] = l"
  by (import rich_list FOLDR_CONS_NIL)

lemma FOLDL_SNOC_NIL: "ALL l::'a::type list.
   foldl (%(xs::'a::type list) x::'a::type. SNOC x xs) [] l = l"
  by (import rich_list FOLDL_SNOC_NIL)

lemma FOLDR_REVERSE: "ALL (x::'a::type => 'b::type => 'b::type) (xa::'b::type) xb::'a::type list.
   foldr x (rev xb) xa = foldl (%(xa::'b::type) y::'a::type. x y xa) xa xb"
  by (import rich_list FOLDR_REVERSE)

lemma FOLDL_REVERSE: "ALL (x::'a::type => 'b::type => 'a::type) (xa::'a::type) xb::'b::type list.
   foldl x xa (rev xb) = foldr (%(xa::'b::type) y::'a::type. x y xa) xb xa"
  by (import rich_list FOLDL_REVERSE)

lemma FOLDR_MAP: "ALL (f::'a::type => 'a::type => 'a::type) (e::'a::type)
   (g::'b::type => 'a::type) l::'b::type list.
   foldr f (map g l) e = foldr (%x::'b::type. f (g x)) l e"
  by (import rich_list FOLDR_MAP)

lemma FOLDL_MAP: "ALL (f::'a::type => 'a::type => 'a::type) (e::'a::type)
   (g::'b::type => 'a::type) l::'b::type list.
   foldl f e (map g l) = foldl (%(x::'a::type) y::'b::type. f x (g y)) e l"
  by (import rich_list FOLDL_MAP)

lemma ALL_EL_FOLDR: "ALL (P::'a::type => bool) l::'a::type list.
   list_all P l = foldr (%x::'a::type. op & (P x)) l True"
  by (import rich_list ALL_EL_FOLDR)

lemma ALL_EL_FOLDL: "ALL (P::'a::type => bool) l::'a::type list.
   list_all P l = foldl (%(l'::bool) x::'a::type. l' & P x) True l"
  by (import rich_list ALL_EL_FOLDL)

lemma SOME_EL_FOLDR: "ALL (P::'a::type => bool) l::'a::type list.
   list_ex P l = foldr (%x::'a::type. op | (P x)) l False"
  by (import rich_list SOME_EL_FOLDR)

lemma SOME_EL_FOLDL: "ALL (P::'a::type => bool) l::'a::type list.
   list_ex P l = foldl (%(l'::bool) x::'a::type. l' | P x) False l"
  by (import rich_list SOME_EL_FOLDL)

lemma ALL_EL_FOLDR_MAP: "ALL (x::'a::type => bool) xa::'a::type list.
   list_all x xa = foldr op & (map x xa) True"
  by (import rich_list ALL_EL_FOLDR_MAP)

lemma ALL_EL_FOLDL_MAP: "ALL (x::'a::type => bool) xa::'a::type list.
   list_all x xa = foldl op & True (map x xa)"
  by (import rich_list ALL_EL_FOLDL_MAP)

lemma SOME_EL_FOLDR_MAP: "ALL (x::'a::type => bool) xa::'a::type list.
   list_ex x xa = foldr op | (map x xa) False"
  by (import rich_list SOME_EL_FOLDR_MAP)

lemma SOME_EL_FOLDL_MAP: "ALL (x::'a::type => bool) xa::'a::type list.
   list_ex x xa = foldl op | False (map x xa)"
  by (import rich_list SOME_EL_FOLDL_MAP)

lemma FOLDR_FILTER: "ALL (f::'a::type => 'a::type => 'a::type) (e::'a::type)
   (P::'a::type => bool) l::'a::type list.
   foldr f (filter P l) e =
   foldr (%(x::'a::type) y::'a::type. if P x then f x y else y) l e"
  by (import rich_list FOLDR_FILTER)

lemma FOLDL_FILTER: "ALL (f::'a::type => 'a::type => 'a::type) (e::'a::type)
   (P::'a::type => bool) l::'a::type list.
   foldl f e (filter P l) =
   foldl (%(x::'a::type) y::'a::type. if P y then f x y else x) e l"
  by (import rich_list FOLDL_FILTER)

lemma ASSOC_FOLDR_FLAT: "ALL f::'a::type => 'a::type => 'a::type.
   ASSOC f -->
   (ALL e::'a::type.
       LEFT_ID f e -->
       (ALL l::'a::type list list.
           foldr f (concat l) e = foldr f (map (FOLDR f e) l) e))"
  by (import rich_list ASSOC_FOLDR_FLAT)

lemma ASSOC_FOLDL_FLAT: "ALL f::'a::type => 'a::type => 'a::type.
   ASSOC f -->
   (ALL e::'a::type.
       RIGHT_ID f e -->
       (ALL l::'a::type list list.
           foldl f e (concat l) = foldl f e (map (foldl f e) l)))"
  by (import rich_list ASSOC_FOLDL_FLAT)

lemma SOME_EL_MAP: "ALL (P::'b::type => bool) (f::'a::type => 'b::type) l::'a::type list.
   list_ex P (map f l) = list_ex (P o f) l"
  by (import rich_list SOME_EL_MAP)

lemma SOME_EL_DISJ: "ALL (P::'a::type => bool) (Q::'a::type => bool) l::'a::type list.
   list_ex (%x::'a::type. P x | Q x) l =
   (list_ex P l | list_ex Q l)"
  by (import rich_list SOME_EL_DISJ)

lemma IS_EL_FOLDR: "ALL (x::'a::type) xa::'a::type list.
   x mem xa = foldr (%xa::'a::type. op | (x = xa)) xa False"
  by (import rich_list IS_EL_FOLDR)

lemma IS_EL_FOLDL: "ALL (x::'a::type) xa::'a::type list.
   x mem xa = foldl (%(l'::bool) xa::'a::type. l' | x = xa) False xa"
  by (import rich_list IS_EL_FOLDL)

lemma NULL_FOLDR: "ALL l::'a::type list. null l = foldr (%(x::'a::type) l'::bool. False) l True"
  by (import rich_list NULL_FOLDR)

lemma NULL_FOLDL: "ALL l::'a::type list. null l = foldl (%(x::bool) l'::'a::type. False) True l"
  by (import rich_list NULL_FOLDL)

lemma SEG_LENGTH_ID: "ALL l::'a::type list. SEG (length l) 0 l = l"
  by (import rich_list SEG_LENGTH_ID)

lemma SEG_SUC_CONS: "ALL (m::nat) (n::nat) (l::'a::type list) x::'a::type.
   SEG m (Suc n) (x # l) = SEG m n l"
  by (import rich_list SEG_SUC_CONS)

lemma SEG_0_SNOC: "ALL (m::nat) (l::'a::type list) x::'a::type.
   m <= length l --> SEG m 0 (SNOC x l) = SEG m 0 l"
  by (import rich_list SEG_0_SNOC)

lemma BUTLASTN_SEG: "ALL (n::nat) l::'a::type list.
   n <= length l --> BUTLASTN n l = SEG (length l - n) 0 l"
  by (import rich_list BUTLASTN_SEG)

lemma LASTN_CONS: "ALL (n::nat) l::'a::type list.
   n <= length l --> (ALL x::'a::type. LASTN n (x # l) = LASTN n l)"
  by (import rich_list LASTN_CONS)

lemma LENGTH_LASTN: "ALL (n::nat) l::'a::type list. n <= length l --> length (LASTN n l) = n"
  by (import rich_list LENGTH_LASTN)

lemma LASTN_LENGTH_ID: "ALL l::'a::type list. LASTN (length l) l = l"
  by (import rich_list LASTN_LENGTH_ID)

lemma LASTN_LASTN: "ALL (l::'a::type list) (n::nat) m::nat.
   m <= length l --> n <= m --> LASTN n (LASTN m l) = LASTN n l"
  by (import rich_list LASTN_LASTN)

lemma FIRSTN_LENGTH_ID: "ALL l::'a::type list. FIRSTN (length l) l = l"
  by (import rich_list FIRSTN_LENGTH_ID)

lemma FIRSTN_SNOC: "ALL (n::nat) l::'a::type list.
   n <= length l --> (ALL x::'a::type. FIRSTN n (SNOC x l) = FIRSTN n l)"
  by (import rich_list FIRSTN_SNOC)

lemma BUTLASTN_LENGTH_NIL: "ALL l::'a::type list. BUTLASTN (length l) l = []"
  by (import rich_list BUTLASTN_LENGTH_NIL)

lemma BUTLASTN_SUC_BUTLAST: "ALL (n::nat) l::'a::type list.
   n < length l --> BUTLASTN (Suc n) l = BUTLASTN n (butlast l)"
  by (import rich_list BUTLASTN_SUC_BUTLAST)

lemma BUTLASTN_BUTLAST: "ALL (n::nat) l::'a::type list.
   n < length l --> BUTLASTN n (butlast l) = butlast (BUTLASTN n l)"
  by (import rich_list BUTLASTN_BUTLAST)

lemma LENGTH_BUTLASTN: "ALL (n::nat) l::'a::type list.
   n <= length l --> length (BUTLASTN n l) = length l - n"
  by (import rich_list LENGTH_BUTLASTN)

lemma BUTLASTN_BUTLASTN: "ALL (m::nat) (n::nat) l::'a::type list.
   n + m <= length l --> BUTLASTN n (BUTLASTN m l) = BUTLASTN (n + m) l"
  by (import rich_list BUTLASTN_BUTLASTN)

lemma APPEND_BUTLASTN_LASTN: "ALL (n::nat) l::'a::type list.
   n <= length l --> BUTLASTN n l @ LASTN n l = l"
  by (import rich_list APPEND_BUTLASTN_LASTN)

lemma APPEND_FIRSTN_LASTN: "ALL (m::nat) (n::nat) l::'a::type list.
   m + n = length l --> FIRSTN n l @ LASTN m l = l"
  by (import rich_list APPEND_FIRSTN_LASTN)

lemma BUTLASTN_APPEND2: "ALL (n::nat) (l1::'a::type list) l2::'a::type list.
   n <= length l2 --> BUTLASTN n (l1 @ l2) = l1 @ BUTLASTN n l2"
  by (import rich_list BUTLASTN_APPEND2)

lemma BUTLASTN_LENGTH_APPEND: "ALL (l2::'a::type list) l1::'a::type list.
   BUTLASTN (length l2) (l1 @ l2) = l1"
  by (import rich_list BUTLASTN_LENGTH_APPEND)

lemma LASTN_LENGTH_APPEND: "ALL (l2::'a::type list) l1::'a::type list. LASTN (length l2) (l1 @ l2) = l2"
  by (import rich_list LASTN_LENGTH_APPEND)

lemma BUTLASTN_CONS: "ALL (n::nat) l::'a::type list.
   n <= length l -->
   (ALL x::'a::type. BUTLASTN n (x # l) = x # BUTLASTN n l)"
  by (import rich_list BUTLASTN_CONS)

lemma BUTLASTN_LENGTH_CONS: "ALL (l::'a::type list) x::'a::type. BUTLASTN (length l) (x # l) = [x]"
  by (import rich_list BUTLASTN_LENGTH_CONS)

lemma LAST_LASTN_LAST: "ALL (n::nat) l::'a::type list.
   n <= length l --> 0 < n --> last (LASTN n l) = last l"
  by (import rich_list LAST_LASTN_LAST)

lemma BUTLASTN_LASTN_NIL: "ALL (n::nat) l::'a::type list. n <= length l --> BUTLASTN n (LASTN n l) = []"
  by (import rich_list BUTLASTN_LASTN_NIL)

lemma LASTN_BUTLASTN: "ALL (n::nat) (m::nat) l::'a::type list.
   n + m <= length l -->
   LASTN n (BUTLASTN m l) = BUTLASTN m (LASTN (n + m) l)"
  by (import rich_list LASTN_BUTLASTN)

lemma BUTLASTN_LASTN: "ALL (m::nat) (n::nat) l::'a::type list.
   m <= n & n <= length l -->
   BUTLASTN m (LASTN n l) = LASTN (n - m) (BUTLASTN m l)"
  by (import rich_list BUTLASTN_LASTN)

lemma LASTN_1: "ALL l::'a::type list. l ~= [] --> LASTN 1 l = [last l]"
  by (import rich_list LASTN_1)

lemma BUTLASTN_1: "ALL l::'a::type list. l ~= [] --> BUTLASTN 1 l = butlast l"
  by (import rich_list BUTLASTN_1)

lemma BUTLASTN_APPEND1: "ALL (l2::'a::type list) n::nat.
   length l2 <= n -->
   (ALL l1::'a::type list.
       BUTLASTN n (l1 @ l2) = BUTLASTN (n - length l2) l1)"
  by (import rich_list BUTLASTN_APPEND1)

lemma LASTN_APPEND2: "ALL (n::nat) l2::'a::type list.
   n <= length l2 -->
   (ALL l1::'a::type list. LASTN n (l1 @ l2) = LASTN n l2)"
  by (import rich_list LASTN_APPEND2)

lemma LASTN_APPEND1: "ALL (l2::'a::type list) n::nat.
   length l2 <= n -->
   (ALL l1::'a::type list.
       LASTN n (l1 @ l2) = LASTN (n - length l2) l1 @ l2)"
  by (import rich_list LASTN_APPEND1)

lemma LASTN_MAP: "ALL (n::nat) l::'a::type list.
   n <= length l -->
   (ALL f::'a::type => 'b::type. LASTN n (map f l) = map f (LASTN n l))"
  by (import rich_list LASTN_MAP)

lemma BUTLASTN_MAP: "ALL (n::nat) l::'a::type list.
   n <= length l -->
   (ALL f::'a::type => 'b::type.
       BUTLASTN n (map f l) = map f (BUTLASTN n l))"
  by (import rich_list BUTLASTN_MAP)

lemma ALL_EL_LASTN: "(All::(('a::type => bool) => bool) => bool)
 (%P::'a::type => bool.
     (All::('a::type list => bool) => bool)
      (%l::'a::type list.
          (op -->::bool => bool => bool)
           ((list_all::('a::type => bool) => 'a::type list => bool) P l)
           ((All::(nat => bool) => bool)
             (%m::nat.
                 (op -->::bool => bool => bool)
                  ((op <=::nat => nat => bool) m
                    ((size::'a::type list => nat) l))
                  ((list_all::('a::type => bool) => 'a::type list => bool) P
                    ((LASTN::nat => 'a::type list => 'a::type list) m
                      l))))))"
  by (import rich_list ALL_EL_LASTN)

lemma ALL_EL_BUTLASTN: "(All::(('a::type => bool) => bool) => bool)
 (%P::'a::type => bool.
     (All::('a::type list => bool) => bool)
      (%l::'a::type list.
          (op -->::bool => bool => bool)
           ((list_all::('a::type => bool) => 'a::type list => bool) P l)
           ((All::(nat => bool) => bool)
             (%m::nat.
                 (op -->::bool => bool => bool)
                  ((op <=::nat => nat => bool) m
                    ((size::'a::type list => nat) l))
                  ((list_all::('a::type => bool) => 'a::type list => bool) P
                    ((BUTLASTN::nat => 'a::type list => 'a::type list) m
                      l))))))"
  by (import rich_list ALL_EL_BUTLASTN)

lemma LENGTH_FIRSTN: "ALL (n::nat) l::'a::type list. n <= length l --> length (FIRSTN n l) = n"
  by (import rich_list LENGTH_FIRSTN)

lemma FIRSTN_FIRSTN: "(All::(nat => bool) => bool)
 (%m::nat.
     (All::('a::type list => bool) => bool)
      (%l::'a::type list.
          (op -->::bool => bool => bool)
           ((op <=::nat => nat => bool) m ((size::'a::type list => nat) l))
           ((All::(nat => bool) => bool)
             (%n::nat.
                 (op -->::bool => bool => bool)
                  ((op <=::nat => nat => bool) n m)
                  ((op =::'a::type list => 'a::type list => bool)
                    ((FIRSTN::nat => 'a::type list => 'a::type list) n
                      ((FIRSTN::nat => 'a::type list => 'a::type list) m l))
                    ((FIRSTN::nat => 'a::type list => 'a::type list) n
                      l))))))"
  by (import rich_list FIRSTN_FIRSTN)

lemma LENGTH_BUTFIRSTN: "ALL (n::nat) l::'a::type list.
   n <= length l --> length (BUTFIRSTN n l) = length l - n"
  by (import rich_list LENGTH_BUTFIRSTN)

lemma BUTFIRSTN_LENGTH_NIL: "ALL l::'a::type list. BUTFIRSTN (length l) l = []"
  by (import rich_list BUTFIRSTN_LENGTH_NIL)

lemma BUTFIRSTN_APPEND1: "ALL (n::nat) l1::'a::type list.
   n <= length l1 -->
   (ALL l2::'a::type list. BUTFIRSTN n (l1 @ l2) = BUTFIRSTN n l1 @ l2)"
  by (import rich_list BUTFIRSTN_APPEND1)

lemma BUTFIRSTN_APPEND2: "ALL (l1::'a::type list) n::nat.
   length l1 <= n -->
   (ALL l2::'a::type list.
       BUTFIRSTN n (l1 @ l2) = BUTFIRSTN (n - length l1) l2)"
  by (import rich_list BUTFIRSTN_APPEND2)

lemma BUTFIRSTN_BUTFIRSTN: "ALL (n::nat) (m::nat) l::'a::type list.
   n + m <= length l --> BUTFIRSTN n (BUTFIRSTN m l) = BUTFIRSTN (n + m) l"
  by (import rich_list BUTFIRSTN_BUTFIRSTN)

lemma APPEND_FIRSTN_BUTFIRSTN: "ALL (n::nat) l::'a::type list.
   n <= length l --> FIRSTN n l @ BUTFIRSTN n l = l"
  by (import rich_list APPEND_FIRSTN_BUTFIRSTN)

lemma LASTN_SEG: "ALL (n::nat) l::'a::type list.
   n <= length l --> LASTN n l = SEG n (length l - n) l"
  by (import rich_list LASTN_SEG)

lemma FIRSTN_SEG: "ALL (n::nat) l::'a::type list. n <= length l --> FIRSTN n l = SEG n 0 l"
  by (import rich_list FIRSTN_SEG)

lemma BUTFIRSTN_SEG: "ALL (n::nat) l::'a::type list.
   n <= length l --> BUTFIRSTN n l = SEG (length l - n) n l"
  by (import rich_list BUTFIRSTN_SEG)

lemma BUTFIRSTN_SNOC: "ALL (n::nat) l::'a::type list.
   n <= length l -->
   (ALL x::'a::type. BUTFIRSTN n (SNOC x l) = SNOC x (BUTFIRSTN n l))"
  by (import rich_list BUTFIRSTN_SNOC)

lemma APPEND_BUTLASTN_BUTFIRSTN: "ALL (m::nat) (n::nat) l::'a::type list.
   m + n = length l --> BUTLASTN m l @ BUTFIRSTN n l = l"
  by (import rich_list APPEND_BUTLASTN_BUTFIRSTN)

lemma SEG_SEG: "ALL (n1::nat) (m1::nat) (n2::nat) (m2::nat) l::'a::type list.
   n1 + m1 <= length l & n2 + m2 <= n1 -->
   SEG n2 m2 (SEG n1 m1 l) = SEG n2 (m1 + m2) l"
  by (import rich_list SEG_SEG)

lemma SEG_APPEND1: "ALL (n::nat) (m::nat) l1::'a::type list.
   n + m <= length l1 -->
   (ALL l2::'a::type list. SEG n m (l1 @ l2) = SEG n m l1)"
  by (import rich_list SEG_APPEND1)

lemma SEG_APPEND2: "ALL (l1::'a::type list) (m::nat) (n::nat) l2::'a::type list.
   length l1 <= m & n <= length l2 -->
   SEG n m (l1 @ l2) = SEG n (m - length l1) l2"
  by (import rich_list SEG_APPEND2)

lemma SEG_FIRSTN_BUTFISTN: "ALL (n::nat) (m::nat) l::'a::type list.
   n + m <= length l --> SEG n m l = FIRSTN n (BUTFIRSTN m l)"
  by (import rich_list SEG_FIRSTN_BUTFISTN)

lemma SEG_APPEND: "ALL (m::nat) (l1::'a::type list) (n::nat) l2::'a::type list.
   m < length l1 & length l1 <= n + m & n + m <= length l1 + length l2 -->
   SEG n m (l1 @ l2) =
   SEG (length l1 - m) m l1 @ SEG (n + m - length l1) 0 l2"
  by (import rich_list SEG_APPEND)

lemma SEG_LENGTH_SNOC: "ALL (x::'a::type list) xa::'a::type. SEG 1 (length x) (SNOC xa x) = [xa]"
  by (import rich_list SEG_LENGTH_SNOC)

lemma SEG_SNOC: "ALL (n::nat) (m::nat) l::'a::type list.
   n + m <= length l --> (ALL x::'a::type. SEG n m (SNOC x l) = SEG n m l)"
  by (import rich_list SEG_SNOC)

lemma ELL_SEG: "ALL (n::nat) l::'a::type list.
   n < length l --> ELL n l = hd (SEG 1 (PRE (length l - n)) l)"
  by (import rich_list ELL_SEG)

lemma SNOC_FOLDR: "ALL (x::'a::type) l::'a::type list. SNOC x l = foldr op # l [x]"
  by (import rich_list SNOC_FOLDR)

lemma IS_EL_FOLDR_MAP: "ALL (x::'a::type) xa::'a::type list.
   x mem xa = foldr op | (map (op = x) xa) False"
  by (import rich_list IS_EL_FOLDR_MAP)

lemma IS_EL_FOLDL_MAP: "ALL (x::'a::type) xa::'a::type list.
   x mem xa = foldl op | False (map (op = x) xa)"
  by (import rich_list IS_EL_FOLDL_MAP)

lemma FILTER_FILTER: "ALL (P::'a::type => bool) (Q::'a::type => bool) l::'a::type list.
   filter P (filter Q l) = [x::'a::type<-l. P x & Q x]"
  by (import rich_list FILTER_FILTER)

lemma FCOMM_FOLDR_FLAT: "ALL (g::'a::type => 'a::type => 'a::type)
   f::'b::type => 'a::type => 'a::type.
   FCOMM g f -->
   (ALL e::'a::type.
       LEFT_ID g e -->
       (ALL l::'b::type list list.
           foldr f (concat l) e = foldr g (map (FOLDR f e) l) e))"
  by (import rich_list FCOMM_FOLDR_FLAT)

lemma FCOMM_FOLDL_FLAT: "ALL (f::'a::type => 'b::type => 'a::type)
   g::'a::type => 'a::type => 'a::type.
   FCOMM f g -->
   (ALL e::'a::type.
       RIGHT_ID g e -->
       (ALL l::'b::type list list.
           foldl f e (concat l) = foldl g e (map (foldl f e) l)))"
  by (import rich_list FCOMM_FOLDL_FLAT)

lemma FOLDR_MAP_REVERSE: "ALL f::'a::type => 'a::type => 'a::type.
   (ALL (a::'a::type) (b::'a::type) c::'a::type.
       f a (f b c) = f b (f a c)) -->
   (ALL (e::'a::type) (g::'b::type => 'a::type) l::'b::type list.
       foldr f (map g (rev l)) e = foldr f (map g l) e)"
  by (import rich_list FOLDR_MAP_REVERSE)

lemma FOLDR_FILTER_REVERSE: "ALL f::'a::type => 'a::type => 'a::type.
   (ALL (a::'a::type) (b::'a::type) c::'a::type.
       f a (f b c) = f b (f a c)) -->
   (ALL (e::'a::type) (P::'a::type => bool) l::'a::type list.
       foldr f (filter P (rev l)) e = foldr f (filter P l) e)"
  by (import rich_list FOLDR_FILTER_REVERSE)

lemma COMM_ASSOC_FOLDR_REVERSE: "ALL f::'a::type => 'a::type => 'a::type.
   COMM f -->
   ASSOC f -->
   (ALL (e::'a::type) l::'a::type list. foldr f (rev l) e = foldr f l e)"
  by (import rich_list COMM_ASSOC_FOLDR_REVERSE)

lemma COMM_ASSOC_FOLDL_REVERSE: "ALL f::'a::type => 'a::type => 'a::type.
   COMM f -->
   ASSOC f -->
   (ALL (e::'a::type) l::'a::type list. foldl f e (rev l) = foldl f e l)"
  by (import rich_list COMM_ASSOC_FOLDL_REVERSE)

lemma ELL_LAST: "ALL l::'a::type list. ~ null l --> ELL 0 l = last l"
  by (import rich_list ELL_LAST)

lemma ELL_0_SNOC: "ALL (l::'a::type list) x::'a::type. ELL 0 (SNOC x l) = x"
  by (import rich_list ELL_0_SNOC)

lemma ELL_SNOC: "ALL n>0.
   ALL (x::'a::type) l::'a::type list. ELL n (SNOC x l) = ELL (PRE n) l"
  by (import rich_list ELL_SNOC)

lemma ELL_SUC_SNOC: "ALL (n::nat) (x::'a::type) xa::'a::type list.
   ELL (Suc n) (SNOC x xa) = ELL n xa"
  by (import rich_list ELL_SUC_SNOC)

lemma ELL_CONS: "ALL (n::nat) l::'a::type list.
   n < length l --> (ALL x::'a::type. ELL n (x # l) = ELL n l)"
  by (import rich_list ELL_CONS)

lemma ELL_LENGTH_CONS: "ALL (l::'a::type list) x::'a::type. ELL (length l) (x # l) = x"
  by (import rich_list ELL_LENGTH_CONS)

lemma ELL_LENGTH_SNOC: "ALL (l::'a::type list) x::'a::type.
   ELL (length l) (SNOC x l) = (if null l then x else hd l)"
  by (import rich_list ELL_LENGTH_SNOC)

lemma ELL_APPEND2: "ALL (n::nat) l2::'a::type list.
   n < length l2 --> (ALL l1::'a::type list. ELL n (l1 @ l2) = ELL n l2)"
  by (import rich_list ELL_APPEND2)

lemma ELL_APPEND1: "ALL (l2::'a::type list) n::nat.
   length l2 <= n -->
   (ALL l1::'a::type list. ELL n (l1 @ l2) = ELL (n - length l2) l1)"
  by (import rich_list ELL_APPEND1)

lemma ELL_PRE_LENGTH: "ALL l::'a::type list. l ~= [] --> ELL (PRE (length l)) l = hd l"
  by (import rich_list ELL_PRE_LENGTH)

lemma EL_LENGTH_SNOC: "ALL (l::'a::type list) x::'a::type. EL (length l) (SNOC x l) = x"
  by (import rich_list EL_LENGTH_SNOC)

lemma EL_PRE_LENGTH: "ALL l::'a::type list. l ~= [] --> EL (PRE (length l)) l = last l"
  by (import rich_list EL_PRE_LENGTH)

lemma EL_SNOC: "ALL (n::nat) l::'a::type list.
   n < length l --> (ALL x::'a::type. EL n (SNOC x l) = EL n l)"
  by (import rich_list EL_SNOC)

lemma EL_ELL: "ALL (n::nat) l::'a::type list.
   n < length l --> EL n l = ELL (PRE (length l - n)) l"
  by (import rich_list EL_ELL)

lemma EL_LENGTH_APPEND: "ALL (l2::'a::type list) l1::'a::type list.
   ~ null l2 --> EL (length l1) (l1 @ l2) = hd l2"
  by (import rich_list EL_LENGTH_APPEND)

lemma ELL_EL: "ALL (n::nat) l::'a::type list.
   n < length l --> ELL n l = EL (PRE (length l - n)) l"
  by (import rich_list ELL_EL)

lemma ELL_MAP: "ALL (n::nat) (l::'a::type list) f::'a::type => 'b::type.
   n < length l --> ELL n (map f l) = f (ELL n l)"
  by (import rich_list ELL_MAP)

lemma LENGTH_BUTLAST: "ALL l::'a::type list. l ~= [] --> length (butlast l) = PRE (length l)"
  by (import rich_list LENGTH_BUTLAST)

lemma BUTFIRSTN_LENGTH_APPEND: "ALL (l1::'a::type list) l2::'a::type list.
   BUTFIRSTN (length l1) (l1 @ l2) = l2"
  by (import rich_list BUTFIRSTN_LENGTH_APPEND)

lemma FIRSTN_APPEND1: "ALL (n::nat) l1::'a::type list.
   n <= length l1 -->
   (ALL l2::'a::type list. FIRSTN n (l1 @ l2) = FIRSTN n l1)"
  by (import rich_list FIRSTN_APPEND1)

lemma FIRSTN_APPEND2: "ALL (l1::'a::type list) n::nat.
   length l1 <= n -->
   (ALL l2::'a::type list.
       FIRSTN n (l1 @ l2) = l1 @ FIRSTN (n - length l1) l2)"
  by (import rich_list FIRSTN_APPEND2)

lemma FIRSTN_LENGTH_APPEND: "ALL (l1::'a::type list) l2::'a::type list. FIRSTN (length l1) (l1 @ l2) = l1"
  by (import rich_list FIRSTN_LENGTH_APPEND)

lemma REVERSE_FLAT: "ALL l::'a::type list list. rev (concat l) = concat (rev (map rev l))"
  by (import rich_list REVERSE_FLAT)

lemma MAP_FILTER: "ALL (f::'a::type => 'a::type) (P::'a::type => bool) l::'a::type list.
   (ALL x::'a::type. P (f x) = P x) -->
   map f (filter P l) = filter P (map f l)"
  by (import rich_list MAP_FILTER)

lemma FLAT_REVERSE: "ALL l::'a::type list list. concat (rev l) = rev (concat (map rev l))"
  by (import rich_list FLAT_REVERSE)

lemma FLAT_FLAT: "ALL l::'a::type list list list. concat (concat l) = concat (map concat l)"
  by (import rich_list FLAT_FLAT)

lemma SOME_EL_REVERSE: "ALL (P::'a::type => bool) l::'a::type list.
   list_ex P (rev l) = list_ex P l"
  by (import rich_list SOME_EL_REVERSE)

lemma ALL_EL_SEG: "ALL (P::'a::type => bool) l::'a::type list.
   list_all P l -->
   (ALL (m::nat) k::nat. m + k <= length l --> list_all P (SEG m k l))"
  by (import rich_list ALL_EL_SEG)

lemma ALL_EL_FIRSTN: "(All::(('a::type => bool) => bool) => bool)
 (%P::'a::type => bool.
     (All::('a::type list => bool) => bool)
      (%l::'a::type list.
          (op -->::bool => bool => bool)
           ((list_all::('a::type => bool) => 'a::type list => bool) P l)
           ((All::(nat => bool) => bool)
             (%m::nat.
                 (op -->::bool => bool => bool)
                  ((op <=::nat => nat => bool) m
                    ((size::'a::type list => nat) l))
                  ((list_all::('a::type => bool) => 'a::type list => bool) P
                    ((FIRSTN::nat => 'a::type list => 'a::type list) m
                      l))))))"
  by (import rich_list ALL_EL_FIRSTN)

lemma ALL_EL_BUTFIRSTN: "(All::(('a::type => bool) => bool) => bool)
 (%P::'a::type => bool.
     (All::('a::type list => bool) => bool)
      (%l::'a::type list.
          (op -->::bool => bool => bool)
           ((list_all::('a::type => bool) => 'a::type list => bool) P l)
           ((All::(nat => bool) => bool)
             (%m::nat.
                 (op -->::bool => bool => bool)
                  ((op <=::nat => nat => bool) m
                    ((size::'a::type list => nat) l))
                  ((list_all::('a::type => bool) => 'a::type list => bool) P
                    ((BUTFIRSTN::nat => 'a::type list => 'a::type list) m
                      l))))))"
  by (import rich_list ALL_EL_BUTFIRSTN)

lemma SOME_EL_SEG: "ALL (m::nat) (k::nat) l::'a::type list.
   m + k <= length l -->
   (ALL P::'a::type => bool. list_ex P (SEG m k l) --> list_ex P l)"
  by (import rich_list SOME_EL_SEG)

lemma SOME_EL_FIRSTN: "ALL (m::nat) l::'a::type list.
   m <= length l -->
   (ALL P::'a::type => bool. list_ex P (FIRSTN m l) --> list_ex P l)"
  by (import rich_list SOME_EL_FIRSTN)

lemma SOME_EL_BUTFIRSTN: "ALL (m::nat) l::'a::type list.
   m <= length l -->
   (ALL P::'a::type => bool.
       list_ex P (BUTFIRSTN m l) --> list_ex P l)"
  by (import rich_list SOME_EL_BUTFIRSTN)

lemma SOME_EL_LASTN: "ALL (m::nat) l::'a::type list.
   m <= length l -->
   (ALL P::'a::type => bool. list_ex P (LASTN m l) --> list_ex P l)"
  by (import rich_list SOME_EL_LASTN)

lemma SOME_EL_BUTLASTN: "ALL (m::nat) l::'a::type list.
   m <= length l -->
   (ALL P::'a::type => bool.
       list_ex P (BUTLASTN m l) --> list_ex P l)"
  by (import rich_list SOME_EL_BUTLASTN)

lemma IS_EL_REVERSE: "ALL (x::'a::type) l::'a::type list. x mem rev l = x mem l"
  by (import rich_list IS_EL_REVERSE)

lemma IS_EL_FILTER: "ALL (P::'a::type => bool) x::'a::type.
   P x --> (ALL l::'a::type list. x mem filter P l = x mem l)"
  by (import rich_list IS_EL_FILTER)

lemma IS_EL_SEG: "ALL (n::nat) (m::nat) l::'a::type list.
   n + m <= length l --> (ALL x::'a::type. x mem SEG n m l --> x mem l)"
  by (import rich_list IS_EL_SEG)

lemma IS_EL_SOME_EL: "ALL (x::'a::type) l::'a::type list. x mem l = list_ex (op = x) l"
  by (import rich_list IS_EL_SOME_EL)

lemma IS_EL_FIRSTN: "ALL (x::nat) xa::'a::type list.
   x <= length xa --> (ALL xb::'a::type. xb mem FIRSTN x xa --> xb mem xa)"
  by (import rich_list IS_EL_FIRSTN)

lemma IS_EL_BUTFIRSTN: "ALL (x::nat) xa::'a::type list.
   x <= length xa -->
   (ALL xb::'a::type. xb mem BUTFIRSTN x xa --> xb mem xa)"
  by (import rich_list IS_EL_BUTFIRSTN)

lemma IS_EL_BUTLASTN: "ALL (x::nat) xa::'a::type list.
   x <= length xa --> (ALL xb::'a::type. xb mem BUTLASTN x xa --> xb mem xa)"
  by (import rich_list IS_EL_BUTLASTN)

lemma IS_EL_LASTN: "ALL (x::nat) xa::'a::type list.
   x <= length xa --> (ALL xb::'a::type. xb mem LASTN x xa --> xb mem xa)"
  by (import rich_list IS_EL_LASTN)

lemma ZIP_SNOC: "ALL (l1::'a::type list) l2::'b::type list.
   length l1 = length l2 -->
   (ALL (x1::'a::type) x2::'b::type.
       zip (SNOC x1 l1) (SNOC x2 l2) = SNOC (x1, x2) (zip l1 l2))"
  by (import rich_list ZIP_SNOC)

lemma UNZIP_SNOC: "ALL (x::'a::type * 'b::type) l::('a::type * 'b::type) list.
   unzip (SNOC x l) =
   (SNOC (fst x) (fst (unzip l)), SNOC (snd x) (snd (unzip l)))"
  by (import rich_list UNZIP_SNOC)

lemma LENGTH_UNZIP_FST: "ALL x::('a::type * 'b::type) list. length (UNZIP_FST x) = length x"
  by (import rich_list LENGTH_UNZIP_FST)

lemma LENGTH_UNZIP_SND: "ALL x::('a::type * 'b::type) list. length (UNZIP_SND x) = length x"
  by (import rich_list LENGTH_UNZIP_SND)

lemma SUM_APPEND: "ALL (l1::nat list) l2::nat list. sum (l1 @ l2) = sum l1 + sum l2"
  by (import rich_list SUM_APPEND)

lemma SUM_REVERSE: "ALL l::nat list. sum (rev l) = sum l"
  by (import rich_list SUM_REVERSE)

lemma SUM_FLAT: "ALL l::nat list list. sum (concat l) = sum (map sum l)"
  by (import rich_list SUM_FLAT)

lemma EL_APPEND1: "ALL (n::nat) (l1::'a::type list) l2::'a::type list.
   n < length l1 --> EL n (l1 @ l2) = EL n l1"
  by (import rich_list EL_APPEND1)

lemma EL_APPEND2: "ALL (l1::'a::type list) n::nat.
   length l1 <= n -->
   (ALL l2::'a::type list. EL n (l1 @ l2) = EL (n - length l1) l2)"
  by (import rich_list EL_APPEND2)

lemma EL_MAP: "ALL (n::nat) l::'a::type list.
   n < length l -->
   (ALL f::'a::type => 'b::type. EL n (map f l) = f (EL n l))"
  by (import rich_list EL_MAP)

lemma EL_CONS: "ALL n>0. ALL (x::'a::type) l::'a::type list. EL n (x # l) = EL (PRE n) l"
  by (import rich_list EL_CONS)

lemma EL_SEG: "ALL (n::nat) l::'a::type list. n < length l --> EL n l = hd (SEG 1 n l)"
  by (import rich_list EL_SEG)

lemma EL_IS_EL: "ALL (n::nat) l::'a::type list. n < length l --> EL n l mem l"
  by (import rich_list EL_IS_EL)

lemma TL_SNOC: "ALL (x::'a::type) l::'a::type list.
   tl (SNOC x l) = (if null l then [] else SNOC x (tl l))"
  by (import rich_list TL_SNOC)

lemma EL_REVERSE: "ALL (n::nat) l::'a::type list.
   n < length l --> EL n (rev l) = EL (PRE (length l - n)) l"
  by (import rich_list EL_REVERSE)

lemma EL_REVERSE_ELL: "ALL (n::nat) l::'a::type list. n < length l --> EL n (rev l) = ELL n l"
  by (import rich_list EL_REVERSE_ELL)

lemma ELL_LENGTH_APPEND: "ALL (l1::'a::type list) l2::'a::type list.
   ~ null l1 --> ELL (length l2) (l1 @ l2) = last l1"
  by (import rich_list ELL_LENGTH_APPEND)

lemma ELL_IS_EL: "ALL (n::nat) l::'a::type list. n < length l --> ELL n l mem l"
  by (import rich_list ELL_IS_EL)

lemma ELL_REVERSE: "ALL (n::nat) l::'a::type list.
   n < length l --> ELL n (rev l) = ELL (PRE (length l - n)) l"
  by (import rich_list ELL_REVERSE)

lemma ELL_REVERSE_EL: "ALL (n::nat) l::'a::type list. n < length l --> ELL n (rev l) = EL n l"
  by (import rich_list ELL_REVERSE_EL)

lemma FIRSTN_BUTLASTN: "ALL (n::nat) l::'a::type list.
   n <= length l --> FIRSTN n l = BUTLASTN (length l - n) l"
  by (import rich_list FIRSTN_BUTLASTN)

lemma BUTLASTN_FIRSTN: "ALL (n::nat) l::'a::type list.
   n <= length l --> BUTLASTN n l = FIRSTN (length l - n) l"
  by (import rich_list BUTLASTN_FIRSTN)

lemma LASTN_BUTFIRSTN: "ALL (n::nat) l::'a::type list.
   n <= length l --> LASTN n l = BUTFIRSTN (length l - n) l"
  by (import rich_list LASTN_BUTFIRSTN)

lemma BUTFIRSTN_LASTN: "ALL (n::nat) l::'a::type list.
   n <= length l --> BUTFIRSTN n l = LASTN (length l - n) l"
  by (import rich_list BUTFIRSTN_LASTN)

lemma SEG_LASTN_BUTLASTN: "ALL (n::nat) (m::nat) l::'a::type list.
   n + m <= length l -->
   SEG n m l = LASTN n (BUTLASTN (length l - (n + m)) l)"
  by (import rich_list SEG_LASTN_BUTLASTN)

lemma BUTFIRSTN_REVERSE: "ALL (n::nat) l::'a::type list.
   n <= length l --> BUTFIRSTN n (rev l) = rev (BUTLASTN n l)"
  by (import rich_list BUTFIRSTN_REVERSE)

lemma BUTLASTN_REVERSE: "ALL (n::nat) l::'a::type list.
   n <= length l --> BUTLASTN n (rev l) = rev (BUTFIRSTN n l)"
  by (import rich_list BUTLASTN_REVERSE)

lemma LASTN_REVERSE: "ALL (n::nat) l::'a::type list.
   n <= length l --> LASTN n (rev l) = rev (FIRSTN n l)"
  by (import rich_list LASTN_REVERSE)

lemma FIRSTN_REVERSE: "ALL (n::nat) l::'a::type list.
   n <= length l --> FIRSTN n (rev l) = rev (LASTN n l)"
  by (import rich_list FIRSTN_REVERSE)

lemma SEG_REVERSE: "ALL (n::nat) (m::nat) l::'a::type list.
   n + m <= length l -->
   SEG n m (rev l) = rev (SEG n (length l - (n + m)) l)"
  by (import rich_list SEG_REVERSE)

lemma LENGTH_GENLIST: "ALL (f::nat => 'a::type) n::nat. length (GENLIST f n) = n"
  by (import rich_list LENGTH_GENLIST)

lemma LENGTH_REPLICATE: "ALL (n::nat) x::'a::type. length (REPLICATE n x) = n"
  by (import rich_list LENGTH_REPLICATE)

lemma IS_EL_REPLICATE: "ALL n>0. ALL x::'a::type. x mem REPLICATE n x"
  by (import rich_list IS_EL_REPLICATE)

lemma ALL_EL_REPLICATE: "ALL (x::'a::type) n::nat. list_all (op = x) (REPLICATE n x)"
  by (import rich_list ALL_EL_REPLICATE)

lemma AND_EL_FOLDL: "ALL l::bool list. AND_EL l = foldl op & True l"
  by (import rich_list AND_EL_FOLDL)

lemma AND_EL_FOLDR: "ALL l::bool list. AND_EL l = foldr op & l True"
  by (import rich_list AND_EL_FOLDR)

lemma OR_EL_FOLDL: "ALL l::bool list. OR_EL l = foldl op | False l"
  by (import rich_list OR_EL_FOLDL)

lemma OR_EL_FOLDR: "ALL l::bool list. OR_EL l = foldr op | l False"
  by (import rich_list OR_EL_FOLDR)

;end_setup

;setup_theory state_transformer

definition UNIT :: "'b => 'a => 'b * 'a" where 
  "(op ==::('b::type => 'a::type => 'b::type * 'a::type)
        => ('b::type => 'a::type => 'b::type * 'a::type) => prop)
 (UNIT::'b::type => 'a::type => 'b::type * 'a::type)
 (Pair::'b::type => 'a::type => 'b::type * 'a::type)"

lemma UNIT_DEF: "ALL x::'b::type. UNIT x = Pair x"
  by (import state_transformer UNIT_DEF)

definition BIND :: "('a => 'b * 'a) => ('b => 'a => 'c * 'a) => 'a => 'c * 'a" where 
  "(op ==::(('a::type => 'b::type * 'a::type)
         => ('b::type => 'a::type => 'c::type * 'a::type)
            => 'a::type => 'c::type * 'a::type)
        => (('a::type => 'b::type * 'a::type)
            => ('b::type => 'a::type => 'c::type * 'a::type)
               => 'a::type => 'c::type * 'a::type)
           => prop)
 (BIND::('a::type => 'b::type * 'a::type)
        => ('b::type => 'a::type => 'c::type * 'a::type)
           => 'a::type => 'c::type * 'a::type)
 (%(g::'a::type => 'b::type * 'a::type)
     f::'b::type => 'a::type => 'c::type * 'a::type.
     (op o::('b::type * 'a::type => 'c::type * 'a::type)
            => ('a::type => 'b::type * 'a::type)
               => 'a::type => 'c::type * 'a::type)
      ((split::('b::type => 'a::type => 'c::type * 'a::type)
               => 'b::type * 'a::type => 'c::type * 'a::type)
        f)
      g)"

lemma BIND_DEF: "(All::(('a::type => 'b::type * 'a::type) => bool) => bool)
 (%g::'a::type => 'b::type * 'a::type.
     (All::(('b::type => 'a::type => 'c::type * 'a::type) => bool) => bool)
      (%f::'b::type => 'a::type => 'c::type * 'a::type.
          (op =::('a::type => 'c::type * 'a::type)
                 => ('a::type => 'c::type * 'a::type) => bool)
           ((BIND::('a::type => 'b::type * 'a::type)
                   => ('b::type => 'a::type => 'c::type * 'a::type)
                      => 'a::type => 'c::type * 'a::type)
             g f)
           ((op o::('b::type * 'a::type => 'c::type * 'a::type)
                   => ('a::type => 'b::type * 'a::type)
                      => 'a::type => 'c::type * 'a::type)
             ((split::('b::type => 'a::type => 'c::type * 'a::type)
                      => 'b::type * 'a::type => 'c::type * 'a::type)
               f)
             g)))"
  by (import state_transformer BIND_DEF)

definition MMAP :: "('c => 'b) => ('a => 'c * 'a) => 'a => 'b * 'a" where 
  "MMAP ==
%(f::'c::type => 'b::type) m::'a::type => 'c::type * 'a::type.
   BIND m (UNIT o f)"

lemma MMAP_DEF: "ALL (f::'c::type => 'b::type) m::'a::type => 'c::type * 'a::type.
   MMAP f m = BIND m (UNIT o f)"
  by (import state_transformer MMAP_DEF)

definition JOIN :: "('a => ('a => 'b * 'a) * 'a) => 'a => 'b * 'a" where 
  "JOIN ==
%z::'a::type => ('a::type => 'b::type * 'a::type) * 'a::type. BIND z I"

lemma JOIN_DEF: "ALL z::'a::type => ('a::type => 'b::type * 'a::type) * 'a::type.
   JOIN z = BIND z I"
  by (import state_transformer JOIN_DEF)

lemma BIND_LEFT_UNIT: "ALL (k::'a::type => 'b::type => 'c::type * 'b::type) x::'a::type.
   BIND (UNIT x) k = k x"
  by (import state_transformer BIND_LEFT_UNIT)

lemma UNIT_UNCURRY: "ALL x::'a::type * 'b::type. split UNIT x = x"
  by (import state_transformer UNIT_UNCURRY)

lemma BIND_RIGHT_UNIT: "ALL k::'a::type => 'b::type * 'a::type. BIND k UNIT = k"
  by (import state_transformer BIND_RIGHT_UNIT)

lemma BIND_ASSOC: "ALL (x::'a::type => 'b::type * 'a::type)
   (xa::'b::type => 'a::type => 'c::type * 'a::type)
   xb::'c::type => 'a::type => 'd::type * 'a::type.
   BIND x (%a::'b::type. BIND (xa a) xb) = BIND (BIND x xa) xb"
  by (import state_transformer BIND_ASSOC)

lemma MMAP_ID: "MMAP I = I"
  by (import state_transformer MMAP_ID)

lemma MMAP_COMP: "ALL (f::'c::type => 'd::type) g::'b::type => 'c::type.
   MMAP (f o g) = MMAP f o MMAP g"
  by (import state_transformer MMAP_COMP)

lemma MMAP_UNIT: "ALL f::'b::type => 'c::type. MMAP f o UNIT = UNIT o f"
  by (import state_transformer MMAP_UNIT)

lemma MMAP_JOIN: "ALL f::'b::type => 'c::type. MMAP f o JOIN = JOIN o MMAP (MMAP f)"
  by (import state_transformer MMAP_JOIN)

lemma JOIN_UNIT: "JOIN o UNIT = I"
  by (import state_transformer JOIN_UNIT)

lemma JOIN_MMAP_UNIT: "JOIN o MMAP UNIT = I"
  by (import state_transformer JOIN_MMAP_UNIT)

lemma JOIN_MAP_JOIN: "JOIN o MMAP JOIN = JOIN o JOIN"
  by (import state_transformer JOIN_MAP_JOIN)

lemma JOIN_MAP: "ALL (x::'a::type => 'b::type * 'a::type)
   xa::'b::type => 'a::type => 'c::type * 'a::type.
   BIND x xa = JOIN (MMAP xa x)"
  by (import state_transformer JOIN_MAP)

lemma FST_o_UNIT: "ALL x::'a::type. fst o UNIT x = K x"
  by (import state_transformer FST_o_UNIT)

lemma SND_o_UNIT: "ALL x::'a::type. snd o UNIT x = I"
  by (import state_transformer SND_o_UNIT)

lemma FST_o_MMAP: "ALL (x::'a::type => 'b::type) xa::'c::type => 'a::type * 'c::type.
   fst o MMAP x xa = x o (fst o xa)"
  by (import state_transformer FST_o_MMAP)

;end_setup

end

