(*  Title:      ZF/ex/integ.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

The integers as equivalence classes over nat*nat.
*)

Integ = EquivClass + Arith +
consts
    intrel,integ::      i
    znat        ::      i=>i            ("$# _" [80] 80)
    zminus      ::      i=>i            ("$~ _" [80] 80)
    znegative   ::      i=>o
    zmagnitude  ::      i=>i
    "$*"        ::      [i,i]=>i      (infixl 70)
    "$'/"       ::      [i,i]=>i      (infixl 70) 
    "$'/'/"     ::      [i,i]=>i      (infixl 70)
    "$+"        ::      [i,i]=>i      (infixl 65)
    "$-"        ::      [i,i]=>i      (infixl 65)
    "$<"        ::      [i,i]=>o        (infixl 50)

defs

    intrel_def
     "intrel == {p:(nat*nat)*(nat*nat).                 
        EX x1 y1 x2 y2. p=<<x1,y1>,<x2,y2>> & x1#+y2 = x2#+y1}"

    integ_def   "integ == (nat*nat)/intrel"
    
    znat_def    "$# m == intrel `` {<m,0>}"
    
    zminus_def  "$~ Z == UN <x,y>:Z. intrel``{<y,x>}"
    
    znegative_def
        "znegative(Z) == EX x y. x<y & y:nat & <x,y>:Z"
    
    zmagnitude_def
        "zmagnitude(Z) ==
	 THE m. m : nat & ((~ znegative(Z) & Z = $# m) |
	                   (znegative(Z) & $~ Z = $# m))"
    
    (*Cannot use UN<x1,y2> here or in zmult because of the form of congruent2.
      Perhaps a "curried" or even polymorphic congruent predicate would be
      better.*)
    zadd_def
     "Z1 $+ Z2 == 
       UN z1:Z1. UN z2:Z2. let <x1,y1>=z1; <x2,y2>=z2                 
                           in intrel``{<x1#+x2, y1#+y2>}"
    
    zdiff_def   "Z1 $- Z2 == Z1 $+ zminus(Z2)"
    zless_def   "Z1 $< Z2 == znegative(Z1 $- Z2)"
    
    (*This illustrates the primitive form of definitions (no patterns)*)
    zmult_def
     "Z1 $* Z2 == 
       UN p1:Z1. UN p2:Z2.  split(%x1 y1. split(%x2 y2.        
                   intrel``{<x1#*x2 #+ y1#*y2, x1#*y2 #+ y1#*x2>}, p2), p1)"
    
 end
