(*  Title:      IntDef.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

The integers as equivalence classes over nat*nat.
*)

IntDef = Equiv + NatArith + 
constdefs
  intrel      :: "((nat * nat) * (nat * nat)) set"
  "intrel == {p. EX x1 y1 x2 y2. p=((x1::nat,y1),(x2,y2)) & x1+y2 = x2+y1}"

typedef (Integ)
  int = "UNIV//intrel"            (quotient_def)

instance
  int :: {ord, zero, one, plus, times, minus}

defs
  zminus_def
    "- Z == Abs_Integ(UN (x,y):Rep_Integ(Z). intrel``{(y,x)})"

constdefs

  int :: nat => int
  "int m == Abs_Integ(intrel `` {(m,0)})"

  neg   :: int => bool
  "neg(Z) == EX x y. x<y & (x,y::nat):Rep_Integ(Z)"

  (*For simplifying equalities*)
  iszero :: int => bool
  "iszero z == z = (0::int)"
  
defs (*of overloaded constants*)
  
  Zero_int_def "0 == int 0"
  One_int_def "1 == int 1"

  zadd_def
   "z + w == 
       Abs_Integ(UN (x1,y1):Rep_Integ(z). UN (x2,y2):Rep_Integ(w).   
		 intrel``{(x1+x2, y1+y2)})"

  zdiff_def "z - (w::int) == z + (-w)"

  zless_def "z<w == neg(z - w)"

  zle_def   "z <= (w::int) == ~(w < z)"

  zmult_def
   "z * w == 
       Abs_Integ(UN (x1,y1):Rep_Integ(z). UN (x2,y2):Rep_Integ(w).   
		 intrel``{(x1*x2 + y1*y2, x1*y2 + y1*x2)})"

end
