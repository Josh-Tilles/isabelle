(*  Title:      ZF/Integ/Int.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

*)

header{*The Integers as Equivalence Classes Over Pairs of Natural Numbers*}

theory Int = EquivClass + ArithSimp:

constdefs
  intrel :: i
    "intrel == {p : (nat*nat)*(nat*nat).                 
                EX x1 y1 x2 y2. p=<<x1,y1>,<x2,y2>> & x1#+y2 = x2#+y1}"

  int :: i
    "int == (nat*nat)//intrel"  

  int_of :: "i=>i" --{*coercion from nat to int*}    ("$# _" [80] 80)
    "$# m == intrel `` {<natify(m), 0>}"

  intify :: "i=>i" --{*coercion from ANYTHING to int*}
    "intify(m) == if m : int then m else $#0"

  raw_zminus :: "i=>i"
    "raw_zminus(z) == UN <x,y>: z. intrel``{<y,x>}"

  zminus :: "i=>i"                                 ("$- _" [80] 80)
    "$- z == raw_zminus (intify(z))"

  znegative   ::      "i=>o"
    "znegative(z) == EX x y. x<y & y:nat & <x,y>:z"

  iszero      ::      "i=>o"
    "iszero(z) == z = $# 0"
    
  raw_nat_of  :: "i=>i"
  "raw_nat_of(z) == if znegative(z) then 0
                    else (THE m. m: nat & z = int_of(m))"

  nat_of  :: "i=>i"
  "nat_of(z) == raw_nat_of (intify(z))"

  zmagnitude  ::      "i=>i"
  --{*could be replaced by an absolute value function from int to int?*}
    "zmagnitude(z) ==
     THE m. m : nat & ((~ znegative(z) & z = $# m) |
		       (znegative(z) & $- z = $# m))"

  raw_zmult   ::      "[i,i]=>i"
    (*Cannot use UN<x1,y2> here or in zadd because of the form of congruent2.
      Perhaps a "curried" or even polymorphic congruent predicate would be
      better.*)
     "raw_zmult(z1,z2) == 
       UN p1:z1. UN p2:z2.  split(%x1 y1. split(%x2 y2.        
                   intrel``{<x1#*x2 #+ y1#*y2, x1#*y2 #+ y1#*x2>}, p2), p1)"

  zmult       ::      "[i,i]=>i"      (infixl "$*" 70)
     "z1 $* z2 == raw_zmult (intify(z1),intify(z2))"

  raw_zadd    ::      "[i,i]=>i"
     "raw_zadd (z1, z2) == 
       UN z1:z1. UN z2:z2. let <x1,y1>=z1; <x2,y2>=z2                 
                           in intrel``{<x1#+x2, y1#+y2>}"

  zadd        ::      "[i,i]=>i"      (infixl "$+" 65)
     "z1 $+ z2 == raw_zadd (intify(z1),intify(z2))"

  zdiff        ::      "[i,i]=>i"      (infixl "$-" 65)
     "z1 $- z2 == z1 $+ zminus(z2)"

  zless        ::      "[i,i]=>o"      (infixl "$<" 50)
     "z1 $< z2 == znegative(z1 $- z2)"
  
  zle          ::      "[i,i]=>o"      (infixl "$<=" 50)
     "z1 $<= z2 == z1 $< z2 | intify(z1)=intify(z2)"
  

syntax (xsymbols)
  zmult :: "[i,i]=>i"          (infixl "$\<times>" 70)
  zle   :: "[i,i]=>o"          (infixl "$\<le>" 50)  --{*less than or equals*}

syntax (HTML output)
  zmult :: "[i,i]=>i"          (infixl "$\<times>" 70)


declare quotientE [elim!]

subsection{*Proving that @{term intrel} is an equivalence relation*}

(** Natural deduction for intrel **)

lemma intrel_iff [simp]: 
    "<<x1,y1>,<x2,y2>>: intrel <->  
     x1: nat & y1: nat & x2: nat & y2: nat & x1#+y2 = x2#+y1"
by (unfold intrel_def, fast)

lemma intrelI [intro!]: 
    "[| x1#+y2 = x2#+y1; x1: nat; y1: nat; x2: nat; y2: nat |]   
     ==> <<x1,y1>,<x2,y2>>: intrel"
by (unfold intrel_def, fast)

lemma intrelE [elim!]:
  "[| p: intrel;   
      !!x1 y1 x2 y2. [| p = <<x1,y1>,<x2,y2>>;  x1#+y2 = x2#+y1;  
                        x1: nat; y1: nat; x2: nat; y2: nat |] ==> Q |]  
   ==> Q"
by (unfold intrel_def, blast) 

lemma int_trans_lemma:
     "[| x1 #+ y2 = x2 #+ y1; x2 #+ y3 = x3 #+ y2 |] ==> x1 #+ y3 = x3 #+ y1"
apply (rule sym)
apply (erule add_left_cancel)+
apply (simp_all (no_asm_simp))
done

lemma equiv_intrel: "equiv(nat*nat, intrel)"
apply (unfold equiv_def refl_def sym_def trans_def)
apply (fast elim!: sym int_trans_lemma)
done

lemma image_intrel_int: "[| m: nat; n: nat |] ==> intrel `` {<m,n>} : int"
apply (unfold int_def)
apply (blast intro: quotientI)
done

declare equiv_intrel [THEN eq_equiv_class_iff, simp]
declare conj_cong [cong]

lemmas eq_intrelD = eq_equiv_class [OF _ equiv_intrel]

(** int_of: the injection from nat to int **)

lemma int_of_type [simp,TC]: "$#m : int"
by (unfold int_def quotient_def int_of_def, auto)

lemma int_of_eq [iff]: "($# m = $# n) <-> natify(m)=natify(n)"
by (unfold int_of_def, auto)

lemma int_of_inject: "[| $#m = $#n;  m: nat;  n: nat |] ==> m=n"
by (drule int_of_eq [THEN iffD1], auto)


(** intify: coercion from anything to int **)

lemma intify_in_int [iff,TC]: "intify(x) : int"
by (simp add: intify_def)

lemma intify_ident [simp]: "n : int ==> intify(n) = n"
by (simp add: intify_def)


subsection{*Collapsing rules: to remove @{term intify}
            from arithmetic expressions*}

lemma intify_idem [simp]: "intify(intify(x)) = intify(x)"
by simp

lemma int_of_natify [simp]: "$# (natify(m)) = $# m"
by (simp add: int_of_def)

lemma zminus_intify [simp]: "$- (intify(m)) = $- m"
by (simp add: zminus_def)

(** Addition **)

lemma zadd_intify1 [simp]: "intify(x) $+ y = x $+ y"
by (simp add: zadd_def)

lemma zadd_intify2 [simp]: "x $+ intify(y) = x $+ y"
by (simp add: zadd_def)

(** Subtraction **)

lemma zdiff_intify1 [simp]:"intify(x) $- y = x $- y"
by (simp add: zdiff_def)

lemma zdiff_intify2 [simp]:"x $- intify(y) = x $- y"
by (simp add: zdiff_def)

(** Multiplication **)

lemma zmult_intify1 [simp]:"intify(x) $* y = x $* y"
by (simp add: zmult_def)

lemma zmult_intify2 [simp]:"x $* intify(y) = x $* y"
by (simp add: zmult_def)

(** Orderings **)

lemma zless_intify1 [simp]:"intify(x) $< y <-> x $< y"
by (simp add: zless_def)

lemma zless_intify2 [simp]:"x $< intify(y) <-> x $< y"
by (simp add: zless_def)

lemma zle_intify1 [simp]:"intify(x) $<= y <-> x $<= y"
by (simp add: zle_def)

lemma zle_intify2 [simp]:"x $<= intify(y) <-> x $<= y"
by (simp add: zle_def)


subsection{*@{term zminus}: unary negation on @{term int}*}

lemma zminus_congruent: "congruent(intrel, %<x,y>. intrel``{<y,x>})"
apply (unfold congruent_def, safe)
apply (simp add: add_ac)
done

lemma raw_zminus_type: "z : int ==> raw_zminus(z) : int"
apply (unfold int_def raw_zminus_def)
apply (typecheck add: UN_equiv_class_type [OF equiv_intrel zminus_congruent])
done

lemma zminus_type [TC,iff]: "$-z : int"
apply (unfold zminus_def)
apply (simp add: zminus_def raw_zminus_type)
done

lemma raw_zminus_inject: 
     "[| raw_zminus(z) = raw_zminus(w);  z: int;  w: int |] ==> z=w"
apply (unfold int_def raw_zminus_def)
apply (erule UN_equiv_class_inject [OF equiv_intrel zminus_congruent], safe)
apply (auto dest: eq_intrelD simp add: add_ac)
done

lemma zminus_inject_intify [dest!]: "$-z = $-w ==> intify(z) = intify(w)"
apply (unfold zminus_def)
apply (blast dest!: raw_zminus_inject)
done

lemma zminus_inject: "[| $-z = $-w;  z: int;  w: int |] ==> z=w"
by auto

lemma raw_zminus: 
    "[| x: nat;  y: nat |] ==> raw_zminus(intrel``{<x,y>}) = intrel `` {<y,x>}"
apply (unfold raw_zminus_def)
apply (simp add: UN_equiv_class [OF equiv_intrel zminus_congruent])
done

lemma zminus: 
    "[| x: nat;  y: nat |]  
     ==> $- (intrel``{<x,y>}) = intrel `` {<y,x>}"
apply (unfold zminus_def)
apply (simp (no_asm_simp) add: raw_zminus image_intrel_int)
done

lemma raw_zminus_zminus: "z : int ==> raw_zminus (raw_zminus(z)) = z"
apply (unfold int_def)
apply (auto simp add: raw_zminus)
done

lemma zminus_zminus_intify [simp]: "$- ($- z) = intify(z)"
by (simp add: zminus_def raw_zminus_type raw_zminus_zminus)

lemma zminus_int0 [simp]: "$- ($#0) = $#0"
apply (unfold int_of_def)
apply (simp add: zminus)
done

lemma zminus_zminus: "z : int ==> $- ($- z) = z"
by simp


subsection{*@{term znegative}: the test for negative integers*}

(*No natural number is negative!*)
lemma not_znegative_int_of [iff]: "~ znegative($# n)"
apply (unfold znegative_def int_of_def, safe)
apply (drule_tac psi = "?lhs=?rhs" in asm_rl)
apply (drule_tac psi = "?lhs<?rhs" in asm_rl)
apply (force simp add: add_le_self2 [THEN le_imp_not_lt] natify_succ)
done

lemma znegative_zminus_int_of [simp]: "znegative($- $# succ(n))"
apply (unfold znegative_def int_of_def)
apply (simp (no_asm_simp) add: zminus natify_succ)
apply (blast intro: nat_0_le)
done

lemma not_znegative_imp_zero: "~ znegative($- $# n) ==> natify(n)=0"
apply (unfold znegative_def int_of_def)
apply (simp add: zminus image_singleton_iff)
apply (drule_tac x = 0 in spec)
apply (auto simp add: nat_into_Ord [THEN Ord_0_lt_iff, THEN iff_sym])
done


subsection{*@{term nat_of}: Coercion of an Integer to a Natural Number*}

lemma nat_of_intify [simp]: "nat_of(intify(z)) = nat_of(z)"
by (unfold nat_of_def, auto)

lemma nat_of_int_of [simp]: "nat_of($# n) = natify(n)"
apply (unfold nat_of_def raw_nat_of_def)
apply (auto simp add: int_of_eq)
done

lemma raw_nat_of_type: "raw_nat_of(z) : nat"
apply (unfold raw_nat_of_def, auto)
apply (case_tac "EX! m. m: nat & z = int_of (m) ")
apply (rule theI2)
apply (simp_all add: the_0) 
done

lemma nat_of_type [iff,TC]: "nat_of(z) : nat"
apply (unfold nat_of_def)
apply (simp add: raw_nat_of_type)
done

subsection{*zmagnitude: magnitide of an integer, as a natural number*}

lemma zmagnitude_int_of [simp]: "zmagnitude($# n) = natify(n)"
apply (unfold zmagnitude_def)
apply (auto simp add: int_of_eq)
done

lemma natify_int_of_eq: "natify(x)=n ==> $#x = $# n"
apply (drule sym)
apply (simp (no_asm_simp) add: int_of_eq)
done

lemma zmagnitude_zminus_int_of [simp]: "zmagnitude($- $# n) = natify(n)"
apply (unfold zmagnitude_def)
apply (rule the_equality)
apply (auto dest!: not_znegative_imp_zero natify_int_of_eq
            iff del: int_of_eq, auto)
done

lemma zmagnitude_type [iff,TC]: "zmagnitude(z) : nat"
apply (unfold zmagnitude_def)
apply (rule theI2, auto)
done

lemma not_zneg_int_of: 
     "[| z: int; ~ znegative(z) |] ==> EX n:nat. z = $# n"
apply (unfold int_def znegative_def int_of_def)
apply (auto simp add: image_singleton_iff)
apply (rename_tac i j)
apply (drule_tac x = i in spec)
apply (drule_tac x = j in spec)
apply (rule bexI)
apply (rule add_diff_inverse2 [symmetric], auto)
apply (simp add: not_lt_iff_le)
done

lemma not_zneg_mag [simp]:
     "[| z: int; ~ znegative(z) |] ==> $# (zmagnitude(z)) = z"
by (drule not_zneg_int_of, auto)

lemma zneg_int_of: 
     "[| znegative(z); z: int |] ==> EX n:nat. z = $- ($# succ(n))"
apply (unfold int_def znegative_def int_of_def)
apply (auto dest!: less_imp_succ_add simp add: zminus image_singleton_iff)
done

lemma zneg_mag [simp]:
     "[| znegative(z); z: int |] ==> $# (zmagnitude(z)) = $- z"
apply (drule zneg_int_of, auto)
done

lemma int_cases: "z : int ==> EX n: nat. z = $# n | z = $- ($# succ(n))"
apply (case_tac "znegative (z) ")
prefer 2 apply (blast dest: not_zneg_mag sym)
apply (blast dest: zneg_int_of)
done

lemma not_zneg_raw_nat_of:
     "[| ~ znegative(z); z: int |] ==> $# (raw_nat_of(z)) = z"
apply (drule not_zneg_int_of)
apply (auto simp add: raw_nat_of_type)
apply (auto simp add: raw_nat_of_def)
done

lemma not_zneg_nat_of_intify:
     "~ znegative(intify(z)) ==> $# (nat_of(z)) = intify(z)"
by (simp (no_asm_simp) add: nat_of_def not_zneg_raw_nat_of)

lemma not_zneg_nat_of: "[| ~ znegative(z); z: int |] ==> $# (nat_of(z)) = z"
apply (simp (no_asm_simp) add: not_zneg_nat_of_intify)
done

lemma zneg_nat_of [simp]: "znegative(intify(z)) ==> nat_of(z) = 0"
by (unfold nat_of_def raw_nat_of_def, auto)


subsection{*@{term zadd}: addition on int*}

text{*Congruence Property for Addition*}
lemma zadd_congruent2: 
    "congruent2(intrel, %z1 z2.                       
          let <x1,y1>=z1; <x2,y2>=z2                  
                            in intrel``{<x1#+x2, y1#+y2>})"
apply (unfold congruent2_def)
(*Proof via congruent2_commuteI seems longer*)
apply safe
apply (simp (no_asm_simp) add: add_assoc Let_def)
(*The rest should be trivial, but rearranging terms is hard
  add_ac does not help rewriting with the assumptions.*)
apply (rule_tac m1 = x1a in add_left_commute [THEN ssubst])
apply (rule_tac m1 = x2a in add_left_commute [THEN ssubst])
apply (simp (no_asm_simp) add: add_assoc [symmetric])
done

lemma raw_zadd_type: "[| z: int;  w: int |] ==> raw_zadd(z,w) : int"
apply (unfold int_def raw_zadd_def)
apply (rule UN_equiv_class_type2 [OF equiv_intrel zadd_congruent2], assumption+)
apply (simp add: Let_def)
done

lemma zadd_type [iff,TC]: "z $+ w : int"
by (simp add: zadd_def raw_zadd_type)

lemma raw_zadd: 
  "[| x1: nat; y1: nat;  x2: nat; y2: nat |]               
   ==> raw_zadd (intrel``{<x1,y1>}, intrel``{<x2,y2>}) =   
       intrel `` {<x1#+x2, y1#+y2>}"
apply (unfold raw_zadd_def)
apply (simp add: UN_equiv_class2 [OF equiv_intrel zadd_congruent2])
apply (simp add: Let_def)
done

lemma zadd: 
  "[| x1: nat; y1: nat;  x2: nat; y2: nat |]          
   ==> (intrel``{<x1,y1>}) $+ (intrel``{<x2,y2>}) =   
       intrel `` {<x1#+x2, y1#+y2>}"
apply (unfold zadd_def)
apply (simp (no_asm_simp) add: raw_zadd image_intrel_int)
done

lemma raw_zadd_int0: "z : int ==> raw_zadd ($#0,z) = z"
apply (unfold int_def int_of_def)
apply (auto simp add: raw_zadd)
done

lemma zadd_int0_intify [simp]: "$#0 $+ z = intify(z)"
by (simp add: zadd_def raw_zadd_int0)

lemma zadd_int0: "z: int ==> $#0 $+ z = z"
by simp

lemma raw_zminus_zadd_distrib: 
     "[| z: int;  w: int |] ==> $- raw_zadd(z,w) = raw_zadd($- z, $- w)"
apply (unfold int_def)
apply (auto simp add: zminus raw_zadd)
done

lemma zminus_zadd_distrib [simp]: "$- (z $+ w) = $- z $+ $- w"
by (simp add: zadd_def raw_zminus_zadd_distrib)

lemma raw_zadd_commute:
     "[| z: int;  w: int |] ==> raw_zadd(z,w) = raw_zadd(w,z)"
apply (unfold int_def)
apply (auto simp add: raw_zadd add_ac)
done

lemma zadd_commute: "z $+ w = w $+ z"
by (simp add: zadd_def raw_zadd_commute)

lemma raw_zadd_assoc: 
    "[| z1: int;  z2: int;  z3: int |]    
     ==> raw_zadd (raw_zadd(z1,z2),z3) = raw_zadd(z1,raw_zadd(z2,z3))"
apply (unfold int_def)
apply (auto simp add: raw_zadd add_assoc)
done

lemma zadd_assoc: "(z1 $+ z2) $+ z3 = z1 $+ (z2 $+ z3)"
by (simp add: zadd_def raw_zadd_type raw_zadd_assoc)

(*For AC rewriting*)
lemma zadd_left_commute: "z1$+(z2$+z3) = z2$+(z1$+z3)"
apply (simp add: zadd_assoc [symmetric])
apply (simp add: zadd_commute)
done

(*Integer addition is an AC operator*)
lemmas zadd_ac = zadd_assoc zadd_commute zadd_left_commute

lemma int_of_add: "$# (m #+ n) = ($#m) $+ ($#n)"
apply (unfold int_of_def)
apply (simp add: zadd)
done

lemma int_succ_int_1: "$# succ(m) = $# 1 $+ ($# m)"
by (simp add: int_of_add [symmetric] natify_succ)

lemma int_of_diff: 
     "[| m: nat;  n le m |] ==> $# (m #- n) = ($#m) $- ($#n)"
apply (unfold int_of_def zdiff_def)
apply (frule lt_nat_in_nat)
apply (simp_all add: zadd zminus add_diff_inverse2)
done

lemma raw_zadd_zminus_inverse: "z : int ==> raw_zadd (z, $- z) = $#0"
apply (unfold int_def int_of_def)
apply (auto simp add: zminus raw_zadd add_commute)
done

lemma zadd_zminus_inverse [simp]: "z $+ ($- z) = $#0"
apply (simp add: zadd_def)
apply (subst zminus_intify [symmetric])
apply (rule intify_in_int [THEN raw_zadd_zminus_inverse])
done

lemma zadd_zminus_inverse2 [simp]: "($- z) $+ z = $#0"
by (simp add: zadd_commute zadd_zminus_inverse)

lemma zadd_int0_right_intify [simp]: "z $+ $#0 = intify(z)"
by (rule trans [OF zadd_commute zadd_int0_intify])

lemma zadd_int0_right: "z:int ==> z $+ $#0 = z"
by simp


subsection{*@{term zmult}: Integer Multiplication*}

text{*Congruence property for multiplication*}
lemma zmult_congruent2:
    "congruent2(intrel, %p1 p2.                  
                split(%x1 y1. split(%x2 y2.      
                    intrel``{<x1#*x2 #+ y1#*y2, x1#*y2 #+ y1#*x2>}, p2), p1))"
apply (rule equiv_intrel [THEN congruent2_commuteI], auto)
(*Proof that zmult is congruent in one argument*)
apply (rename_tac x y)
apply (frule_tac t = "%u. x#*u" in sym [THEN subst_context])
apply (drule_tac t = "%u. y#*u" in subst_context)
apply (erule add_left_cancel)+
apply (simp_all add: add_mult_distrib_left)
done


lemma raw_zmult_type: "[| z: int;  w: int |] ==> raw_zmult(z,w) : int"
apply (unfold int_def raw_zmult_def)
apply (rule UN_equiv_class_type2 [OF equiv_intrel zmult_congruent2], assumption+)
apply (simp add: Let_def)
done

lemma zmult_type [iff,TC]: "z $* w : int"
by (simp add: zmult_def raw_zmult_type)

lemma raw_zmult: 
     "[| x1: nat; y1: nat;  x2: nat; y2: nat |]     
      ==> raw_zmult(intrel``{<x1,y1>}, intrel``{<x2,y2>}) =      
          intrel `` {<x1#*x2 #+ y1#*y2, x1#*y2 #+ y1#*x2>}"
apply (unfold raw_zmult_def)
apply (simp add: UN_equiv_class2 [OF equiv_intrel zmult_congruent2])
done

lemma zmult: 
     "[| x1: nat; y1: nat;  x2: nat; y2: nat |]     
      ==> (intrel``{<x1,y1>}) $* (intrel``{<x2,y2>}) =      
          intrel `` {<x1#*x2 #+ y1#*y2, x1#*y2 #+ y1#*x2>}"
apply (unfold zmult_def)
apply (simp add: raw_zmult image_intrel_int)
done

lemma raw_zmult_int0: "z : int ==> raw_zmult ($#0,z) = $#0"
apply (unfold int_def int_of_def)
apply (auto simp add: raw_zmult)
done

lemma zmult_int0 [simp]: "$#0 $* z = $#0"
by (simp add: zmult_def raw_zmult_int0)

lemma raw_zmult_int1: "z : int ==> raw_zmult ($#1,z) = z"
apply (unfold int_def int_of_def)
apply (auto simp add: raw_zmult)
done

lemma zmult_int1_intify [simp]: "$#1 $* z = intify(z)"
by (simp add: zmult_def raw_zmult_int1)

lemma zmult_int1: "z : int ==> $#1 $* z = z"
by simp

lemma raw_zmult_commute:
     "[| z: int;  w: int |] ==> raw_zmult(z,w) = raw_zmult(w,z)"
apply (unfold int_def)
apply (auto simp add: raw_zmult add_ac mult_ac)
done

lemma zmult_commute: "z $* w = w $* z"
by (simp add: zmult_def raw_zmult_commute)

lemma raw_zmult_zminus: 
     "[| z: int;  w: int |] ==> raw_zmult($- z, w) = $- raw_zmult(z, w)"
apply (unfold int_def)
apply (auto simp add: zminus raw_zmult add_ac)
done

lemma zmult_zminus [simp]: "($- z) $* w = $- (z $* w)"
apply (simp add: zmult_def raw_zmult_zminus)
apply (subst zminus_intify [symmetric], rule raw_zmult_zminus, auto)
done

lemma zmult_zminus_right [simp]: "w $* ($- z) = $- (w $* z)"
by (simp add: zmult_commute [of w])

lemma raw_zmult_assoc: 
    "[| z1: int;  z2: int;  z3: int |]    
     ==> raw_zmult (raw_zmult(z1,z2),z3) = raw_zmult(z1,raw_zmult(z2,z3))"
apply (unfold int_def)
apply (auto simp add: raw_zmult add_mult_distrib_left add_ac mult_ac)
done

lemma zmult_assoc: "(z1 $* z2) $* z3 = z1 $* (z2 $* z3)"
by (simp add: zmult_def raw_zmult_type raw_zmult_assoc)

(*For AC rewriting*)
lemma zmult_left_commute: "z1$*(z2$*z3) = z2$*(z1$*z3)"
apply (simp add: zmult_assoc [symmetric])
apply (simp add: zmult_commute)
done

(*Integer multiplication is an AC operator*)
lemmas zmult_ac = zmult_assoc zmult_commute zmult_left_commute

lemma raw_zadd_zmult_distrib: 
    "[| z1: int;  z2: int;  w: int |]   
     ==> raw_zmult(raw_zadd(z1,z2), w) =  
         raw_zadd (raw_zmult(z1,w), raw_zmult(z2,w))"
apply (unfold int_def)
apply (auto simp add: raw_zadd raw_zmult add_mult_distrib_left add_ac mult_ac)
done

lemma zadd_zmult_distrib: "(z1 $+ z2) $* w = (z1 $* w) $+ (z2 $* w)"
by (simp add: zmult_def zadd_def raw_zadd_type raw_zmult_type 
              raw_zadd_zmult_distrib)

lemma zadd_zmult_distrib2: "w $* (z1 $+ z2) = (w $* z1) $+ (w $* z2)"
by (simp add: zmult_commute [of w] zadd_zmult_distrib)

lemmas int_typechecks = 
  int_of_type zminus_type zmagnitude_type zadd_type zmult_type


(*** Subtraction laws ***)

lemma zdiff_type [iff,TC]: "z $- w : int"
by (simp add: zdiff_def)

lemma zminus_zdiff_eq [simp]: "$- (z $- y) = y $- z"
by (simp add: zdiff_def zadd_commute)

lemma zdiff_zmult_distrib: "(z1 $- z2) $* w = (z1 $* w) $- (z2 $* w)"
apply (unfold zdiff_def)
apply (subst zadd_zmult_distrib)
apply (simp add: zmult_zminus)
done

lemma zdiff_zmult_distrib2: "w $* (z1 $- z2) = (w $* z1) $- (w $* z2)"
by (simp add: zmult_commute [of w] zdiff_zmult_distrib)

lemma zadd_zdiff_eq: "x $+ (y $- z) = (x $+ y) $- z"
by (simp add: zdiff_def zadd_ac)

lemma zdiff_zadd_eq: "(x $- y) $+ z = (x $+ z) $- y"
by (simp add: zdiff_def zadd_ac)


subsection{*The "Less Than" Relation*}

(*"Less than" is a linear ordering*)
lemma zless_linear_lemma: 
     "[| z: int; w: int |] ==> z$<w | z=w | w$<z"
apply (unfold int_def zless_def znegative_def zdiff_def, auto)
apply (simp add: zadd zminus image_iff Bex_def)
apply (rule_tac i = "xb#+ya" and j = "xc #+ y" in Ord_linear_lt)
apply (force dest!: spec simp add: add_ac)+
done

lemma zless_linear: "z$<w | intify(z)=intify(w) | w$<z"
apply (cut_tac z = " intify (z) " and w = " intify (w) " in zless_linear_lemma)
apply auto
done

lemma zless_not_refl [iff]: "~ (z$<z)"
apply (auto simp add: zless_def znegative_def int_of_def zdiff_def)
apply (rotate_tac 2, auto)
done

lemma neq_iff_zless: "[| x: int; y: int |] ==> (x ~= y) <-> (x $< y | y $< x)"
by (cut_tac z = x and w = y in zless_linear, auto)

lemma zless_imp_intify_neq: "w $< z ==> intify(w) ~= intify(z)"
apply auto
apply (subgoal_tac "~ (intify (w) $< intify (z))")
apply (erule_tac [2] ssubst)
apply (simp (no_asm_use))
apply auto
done

(*This lemma allows direct proofs of other <-properties*)
lemma zless_imp_succ_zadd_lemma: 
    "[| w $< z; w: int; z: int |] ==> (EX n: nat. z = w $+ $#(succ(n)))"
apply (unfold zless_def znegative_def zdiff_def int_def)
apply (auto dest!: less_imp_succ_add simp add: zadd zminus int_of_def)
apply (rule_tac x = k in bexI)
apply (erule add_left_cancel, auto)
done

lemma zless_imp_succ_zadd:
     "w $< z ==> (EX n: nat. w $+ $#(succ(n)) = intify(z))"
apply (subgoal_tac "intify (w) $< intify (z) ")
apply (drule_tac w = "intify (w) " in zless_imp_succ_zadd_lemma)
apply auto
done

lemma zless_succ_zadd_lemma: 
    "w : int ==> w $< w $+ $# succ(n)"
apply (unfold zless_def znegative_def zdiff_def int_def)
apply (auto simp add: zadd zminus int_of_def image_iff)
apply (rule_tac x = 0 in exI, auto)
done

lemma zless_succ_zadd: "w $< w $+ $# succ(n)"
by (cut_tac intify_in_int [THEN zless_succ_zadd_lemma], auto)

lemma zless_iff_succ_zadd:
     "w $< z <-> (EX n: nat. w $+ $#(succ(n)) = intify(z))"
apply (rule iffI)
apply (erule zless_imp_succ_zadd, auto)
apply (rename_tac "n")
apply (cut_tac w = w and n = n in zless_succ_zadd, auto)
done

lemma zless_int_of [simp]: "[| m: nat; n: nat |] ==> ($#m $< $#n) <-> (m<n)"
apply (simp add: less_iff_succ_add zless_iff_succ_zadd int_of_add [symmetric])
apply (blast intro: sym)
done

lemma zless_trans_lemma: 
    "[| x $< y; y $< z; x: int; y : int; z: int |] ==> x $< z"
apply (unfold zless_def znegative_def zdiff_def int_def)
apply (auto simp add: zadd zminus image_iff)
apply (rename_tac x1 x2 y1 y2)
apply (rule_tac x = "x1#+x2" in exI)
apply (rule_tac x = "y1#+y2" in exI)
apply (auto simp add: add_lt_mono)
apply (rule sym)
apply (erule add_left_cancel)+
apply auto
done

lemma zless_trans: "[| x $< y; y $< z |] ==> x $< z"
apply (subgoal_tac "intify (x) $< intify (z) ")
apply (rule_tac [2] y = "intify (y) " in zless_trans_lemma)
apply auto
done

lemma zless_not_sym: "z $< w ==> ~ (w $< z)"
by (blast dest: zless_trans)

(* [| z $< w; ~ P ==> w $< z |] ==> P *)
lemmas zless_asym = zless_not_sym [THEN swap, standard]

lemma zless_imp_zle: "z $< w ==> z $<= w"
apply (unfold zle_def)
apply (blast elim: zless_asym)
done

lemma zle_linear: "z $<= w | w $<= z"
apply (simp add: zle_def)
apply (cut_tac zless_linear, blast)
done


subsection{*Less Than or Equals*}

lemma zle_refl: "z $<= z"
by (unfold zle_def, auto)

lemma zle_eq_refl: "x=y ==> x $<= y"
by (simp add: zle_refl)

lemma zle_anti_sym_intify: "[| x $<= y; y $<= x |] ==> intify(x) = intify(y)"
apply (unfold zle_def, auto)
apply (blast dest: zless_trans)
done

lemma zle_anti_sym: "[| x $<= y; y $<= x; x: int; y: int |] ==> x=y"
by (drule zle_anti_sym_intify, auto)

lemma zle_trans_lemma:
     "[| x: int; y: int; z: int; x $<= y; y $<= z |] ==> x $<= z"
apply (unfold zle_def, auto)
apply (blast intro: zless_trans)
done

lemma zle_trans: "[| x $<= y; y $<= z |] ==> x $<= z"
apply (subgoal_tac "intify (x) $<= intify (z) ")
apply (rule_tac [2] y = "intify (y) " in zle_trans_lemma)
apply auto
done

lemma zle_zless_trans: "[| i $<= j; j $< k |] ==> i $< k"
apply (auto simp add: zle_def)
apply (blast intro: zless_trans)
apply (simp add: zless_def zdiff_def zadd_def)
done

lemma zless_zle_trans: "[| i $< j; j $<= k |] ==> i $< k"
apply (auto simp add: zle_def)
apply (blast intro: zless_trans)
apply (simp add: zless_def zdiff_def zminus_def)
done

lemma not_zless_iff_zle: "~ (z $< w) <-> (w $<= z)"
apply (cut_tac z = z and w = w in zless_linear)
apply (auto dest: zless_trans simp add: zle_def)
apply (auto dest!: zless_imp_intify_neq)
done

lemma not_zle_iff_zless: "~ (z $<= w) <-> (w $< z)"
by (simp add: not_zless_iff_zle [THEN iff_sym])


subsection{*More subtraction laws (for @{text zcompare_rls})*}

lemma zdiff_zdiff_eq: "(x $- y) $- z = x $- (y $+ z)"
by (simp add: zdiff_def zadd_ac)

lemma zdiff_zdiff_eq2: "x $- (y $- z) = (x $+ z) $- y"
by (simp add: zdiff_def zadd_ac)

lemma zdiff_zless_iff: "(x$-y $< z) <-> (x $< z $+ y)"
apply (unfold zless_def zdiff_def)
apply (simp add: zadd_ac)
done

lemma zless_zdiff_iff: "(x $< z$-y) <-> (x $+ y $< z)"
apply (unfold zless_def zdiff_def)
apply (simp add: zadd_ac)
done

lemma zdiff_eq_iff: "[| x: int; z: int |] ==> (x$-y = z) <-> (x = z $+ y)"
apply (unfold zdiff_def)
apply (auto simp add: zadd_assoc)
done

lemma eq_zdiff_iff: "[| x: int; z: int |] ==> (x = z$-y) <-> (x $+ y = z)"
apply (unfold zdiff_def)
apply (auto simp add: zadd_assoc)
done

lemma zdiff_zle_iff_lemma:
     "[| x: int; z: int |] ==> (x$-y $<= z) <-> (x $<= z $+ y)"
apply (unfold zle_def)
apply (auto simp add: zdiff_eq_iff zdiff_zless_iff)
done

lemma zdiff_zle_iff: "(x$-y $<= z) <-> (x $<= z $+ y)"
by (cut_tac zdiff_zle_iff_lemma [OF intify_in_int intify_in_int], simp)

lemma zle_zdiff_iff_lemma:
     "[| x: int; z: int |] ==>(x $<= z$-y) <-> (x $+ y $<= z)"
apply (unfold zle_def)
apply (auto simp add: zdiff_eq_iff zless_zdiff_iff)
apply (auto simp add: zdiff_def zadd_assoc)
done

lemma zle_zdiff_iff: "(x $<= z$-y) <-> (x $+ y $<= z)"
by (cut_tac zle_zdiff_iff_lemma [ OF intify_in_int intify_in_int], simp)

text{*This list of rewrites simplifies (in)equalities by bringing subtractions
  to the top and then moving negative terms to the other side.  
  Use with @{text zadd_ac}*}
lemmas zcompare_rls =
     zdiff_def [symmetric]
     zadd_zdiff_eq zdiff_zadd_eq zdiff_zdiff_eq zdiff_zdiff_eq2 
     zdiff_zless_iff zless_zdiff_iff zdiff_zle_iff zle_zdiff_iff 
     zdiff_eq_iff eq_zdiff_iff


subsection{*Monotonicity and Cancellation Results for Instantiation
     of the CancelNumerals Simprocs*}

lemma zadd_left_cancel:
     "[| w: int; w': int |] ==> (z $+ w' = z $+ w) <-> (w' = w)"
apply safe
apply (drule_tac t = "%x. x $+ ($-z) " in subst_context)
apply (simp add: zadd_ac)
done

lemma zadd_left_cancel_intify [simp]:
     "(z $+ w' = z $+ w) <-> intify(w') = intify(w)"
apply (rule iff_trans)
apply (rule_tac [2] zadd_left_cancel, auto)
done

lemma zadd_right_cancel:
     "[| w: int; w': int |] ==> (w' $+ z = w $+ z) <-> (w' = w)"
apply safe
apply (drule_tac t = "%x. x $+ ($-z) " in subst_context)
apply (simp add: zadd_ac)
done

lemma zadd_right_cancel_intify [simp]:
     "(w' $+ z = w $+ z) <-> intify(w') = intify(w)"
apply (rule iff_trans)
apply (rule_tac [2] zadd_right_cancel, auto)
done

lemma zadd_right_cancel_zless [simp]: "(w' $+ z $< w $+ z) <-> (w' $< w)"
apply (simp add: zdiff_zless_iff [THEN iff_sym])
apply (simp add: zdiff_def zadd_assoc)
done

lemma zadd_left_cancel_zless [simp]: "(z $+ w' $< z $+ w) <-> (w' $< w)"
by (simp add: zadd_commute [of z] zadd_right_cancel_zless)

lemma zadd_right_cancel_zle [simp]: "(w' $+ z $<= w $+ z) <-> w' $<= w"
by (simp add: zle_def)

lemma zadd_left_cancel_zle [simp]: "(z $+ w' $<= z $+ w) <->  w' $<= w"
by (simp add: zadd_commute [of z]  zadd_right_cancel_zle)


(*"v $<= w ==> v$+z $<= w$+z"*)
lemmas zadd_zless_mono1 = zadd_right_cancel_zless [THEN iffD2, standard]

(*"v $<= w ==> z$+v $<= z$+w"*)
lemmas zadd_zless_mono2 = zadd_left_cancel_zless [THEN iffD2, standard]

(*"v $<= w ==> v$+z $<= w$+z"*)
lemmas zadd_zle_mono1 = zadd_right_cancel_zle [THEN iffD2, standard]

(*"v $<= w ==> z$+v $<= z$+w"*)
lemmas zadd_zle_mono2 = zadd_left_cancel_zle [THEN iffD2, standard]

lemma zadd_zle_mono: "[| w' $<= w; z' $<= z |] ==> w' $+ z' $<= w $+ z"
by (erule zadd_zle_mono1 [THEN zle_trans], simp)

lemma zadd_zless_mono: "[| w' $< w; z' $<= z |] ==> w' $+ z' $< w $+ z"
by (erule zadd_zless_mono1 [THEN zless_zle_trans], simp)


subsection{*Comparison laws*}

lemma zminus_zless_zminus [simp]: "($- x $< $- y) <-> (y $< x)"
by (simp add: zless_def zdiff_def zadd_ac)

lemma zminus_zle_zminus [simp]: "($- x $<= $- y) <-> (y $<= x)"
by (simp add: not_zless_iff_zle [THEN iff_sym])

subsubsection{*More inequality lemmas*}

lemma equation_zminus: "[| x: int;  y: int |] ==> (x = $- y) <-> (y = $- x)"
by auto

lemma zminus_equation: "[| x: int;  y: int |] ==> ($- x = y) <-> ($- y = x)"
by auto

lemma equation_zminus_intify: "(intify(x) = $- y) <-> (intify(y) = $- x)"
apply (cut_tac x = "intify (x) " and y = "intify (y) " in equation_zminus)
apply auto
done

lemma zminus_equation_intify: "($- x = intify(y)) <-> ($- y = intify(x))"
apply (cut_tac x = "intify (x) " and y = "intify (y) " in zminus_equation)
apply auto
done


subsubsection{*The next several equations are permutative: watch out!*}

lemma zless_zminus: "(x $< $- y) <-> (y $< $- x)"
by (simp add: zless_def zdiff_def zadd_ac)

lemma zminus_zless: "($- x $< y) <-> ($- y $< x)"
by (simp add: zless_def zdiff_def zadd_ac)

lemma zle_zminus: "(x $<= $- y) <-> (y $<= $- x)"
by (simp add: not_zless_iff_zle [THEN iff_sym] zminus_zless)

lemma zminus_zle: "($- x $<= y) <-> ($- y $<= x)"
by (simp add: not_zless_iff_zle [THEN iff_sym] zless_zminus)

ML
{*
val zdiff_def = thm "zdiff_def";
val int_of_type = thm "int_of_type";
val int_of_eq = thm "int_of_eq";
val int_of_inject = thm "int_of_inject";
val intify_in_int = thm "intify_in_int";
val intify_ident = thm "intify_ident";
val intify_idem = thm "intify_idem";
val int_of_natify = thm "int_of_natify";
val zminus_intify = thm "zminus_intify";
val zadd_intify1 = thm "zadd_intify1";
val zadd_intify2 = thm "zadd_intify2";
val zdiff_intify1 = thm "zdiff_intify1";
val zdiff_intify2 = thm "zdiff_intify2";
val zmult_intify1 = thm "zmult_intify1";
val zmult_intify2 = thm "zmult_intify2";
val zless_intify1 = thm "zless_intify1";
val zless_intify2 = thm "zless_intify2";
val zle_intify1 = thm "zle_intify1";
val zle_intify2 = thm "zle_intify2";
val zminus_congruent = thm "zminus_congruent";
val zminus_type = thm "zminus_type";
val zminus_inject_intify = thm "zminus_inject_intify";
val zminus_inject = thm "zminus_inject";
val zminus = thm "zminus";
val zminus_zminus_intify = thm "zminus_zminus_intify";
val zminus_int0 = thm "zminus_int0";
val zminus_zminus = thm "zminus_zminus";
val not_znegative_int_of = thm "not_znegative_int_of";
val znegative_zminus_int_of = thm "znegative_zminus_int_of";
val not_znegative_imp_zero = thm "not_znegative_imp_zero";
val nat_of_intify = thm "nat_of_intify";
val nat_of_int_of = thm "nat_of_int_of";
val nat_of_type = thm "nat_of_type";
val zmagnitude_int_of = thm "zmagnitude_int_of";
val natify_int_of_eq = thm "natify_int_of_eq";
val zmagnitude_zminus_int_of = thm "zmagnitude_zminus_int_of";
val zmagnitude_type = thm "zmagnitude_type";
val not_zneg_int_of = thm "not_zneg_int_of";
val not_zneg_mag = thm "not_zneg_mag";
val zneg_int_of = thm "zneg_int_of";
val zneg_mag = thm "zneg_mag";
val int_cases = thm "int_cases";
val not_zneg_nat_of_intify = thm "not_zneg_nat_of_intify";
val not_zneg_nat_of = thm "not_zneg_nat_of";
val zneg_nat_of = thm "zneg_nat_of";
val zadd_congruent2 = thm "zadd_congruent2";
val zadd_type = thm "zadd_type";
val zadd = thm "zadd";
val zadd_int0_intify = thm "zadd_int0_intify";
val zadd_int0 = thm "zadd_int0";
val zminus_zadd_distrib = thm "zminus_zadd_distrib";
val zadd_commute = thm "zadd_commute";
val zadd_assoc = thm "zadd_assoc";
val zadd_left_commute = thm "zadd_left_commute";
val zadd_ac = thms "zadd_ac";
val int_of_add = thm "int_of_add";
val int_succ_int_1 = thm "int_succ_int_1";
val int_of_diff = thm "int_of_diff";
val zadd_zminus_inverse = thm "zadd_zminus_inverse";
val zadd_zminus_inverse2 = thm "zadd_zminus_inverse2";
val zadd_int0_right_intify = thm "zadd_int0_right_intify";
val zadd_int0_right = thm "zadd_int0_right";
val zmult_congruent2 = thm "zmult_congruent2";
val zmult_type = thm "zmult_type";
val zmult = thm "zmult";
val zmult_int0 = thm "zmult_int0";
val zmult_int1_intify = thm "zmult_int1_intify";
val zmult_int1 = thm "zmult_int1";
val zmult_commute = thm "zmult_commute";
val zmult_zminus = thm "zmult_zminus";
val zmult_zminus_right = thm "zmult_zminus_right";
val zmult_assoc = thm "zmult_assoc";
val zmult_left_commute = thm "zmult_left_commute";
val zmult_ac = thms "zmult_ac";
val zadd_zmult_distrib = thm "zadd_zmult_distrib";
val zadd_zmult_distrib2 = thm "zadd_zmult_distrib2";
val int_typechecks = thms "int_typechecks";
val zdiff_type = thm "zdiff_type";
val zminus_zdiff_eq = thm "zminus_zdiff_eq";
val zdiff_zmult_distrib = thm "zdiff_zmult_distrib";
val zdiff_zmult_distrib2 = thm "zdiff_zmult_distrib2";
val zadd_zdiff_eq = thm "zadd_zdiff_eq";
val zdiff_zadd_eq = thm "zdiff_zadd_eq";
val zless_linear = thm "zless_linear";
val zless_not_refl = thm "zless_not_refl";
val neq_iff_zless = thm "neq_iff_zless";
val zless_imp_intify_neq = thm "zless_imp_intify_neq";
val zless_imp_succ_zadd = thm "zless_imp_succ_zadd";
val zless_succ_zadd = thm "zless_succ_zadd";
val zless_iff_succ_zadd = thm "zless_iff_succ_zadd";
val zless_int_of = thm "zless_int_of";
val zless_trans = thm "zless_trans";
val zless_not_sym = thm "zless_not_sym";
val zless_asym = thm "zless_asym";
val zless_imp_zle = thm "zless_imp_zle";
val zle_linear = thm "zle_linear";
val zle_refl = thm "zle_refl";
val zle_eq_refl = thm "zle_eq_refl";
val zle_anti_sym_intify = thm "zle_anti_sym_intify";
val zle_anti_sym = thm "zle_anti_sym";
val zle_trans = thm "zle_trans";
val zle_zless_trans = thm "zle_zless_trans";
val zless_zle_trans = thm "zless_zle_trans";
val not_zless_iff_zle = thm "not_zless_iff_zle";
val not_zle_iff_zless = thm "not_zle_iff_zless";
val zdiff_zdiff_eq = thm "zdiff_zdiff_eq";
val zdiff_zdiff_eq2 = thm "zdiff_zdiff_eq2";
val zdiff_zless_iff = thm "zdiff_zless_iff";
val zless_zdiff_iff = thm "zless_zdiff_iff";
val zdiff_eq_iff = thm "zdiff_eq_iff";
val eq_zdiff_iff = thm "eq_zdiff_iff";
val zdiff_zle_iff = thm "zdiff_zle_iff";
val zle_zdiff_iff = thm "zle_zdiff_iff";
val zcompare_rls = thms "zcompare_rls";
val zadd_left_cancel = thm "zadd_left_cancel";
val zadd_left_cancel_intify = thm "zadd_left_cancel_intify";
val zadd_right_cancel = thm "zadd_right_cancel";
val zadd_right_cancel_intify = thm "zadd_right_cancel_intify";
val zadd_right_cancel_zless = thm "zadd_right_cancel_zless";
val zadd_left_cancel_zless = thm "zadd_left_cancel_zless";
val zadd_right_cancel_zle = thm "zadd_right_cancel_zle";
val zadd_left_cancel_zle = thm "zadd_left_cancel_zle";
val zadd_zless_mono1 = thm "zadd_zless_mono1";
val zadd_zless_mono2 = thm "zadd_zless_mono2";
val zadd_zle_mono1 = thm "zadd_zle_mono1";
val zadd_zle_mono2 = thm "zadd_zle_mono2";
val zadd_zle_mono = thm "zadd_zle_mono";
val zadd_zless_mono = thm "zadd_zless_mono";
val zminus_zless_zminus = thm "zminus_zless_zminus";
val zminus_zle_zminus = thm "zminus_zle_zminus";
val equation_zminus = thm "equation_zminus";
val zminus_equation = thm "zminus_equation";
val equation_zminus_intify = thm "equation_zminus_intify";
val zminus_equation_intify = thm "zminus_equation_intify";
val zless_zminus = thm "zless_zminus";
val zminus_zless = thm "zminus_zless";
val zle_zminus = thm "zle_zminus";
val zminus_zle = thm "zminus_zle";
*}


end
