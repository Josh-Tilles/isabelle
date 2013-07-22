(*  Title:      HOL/BNF/BNF.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Bounded natural functors for (co)datatypes.
*)

header {* Bounded Natural Functors for (Co)datatypes *}

theory BNF
imports More_BNFs
begin

hide_const (open) vimagep Gr Grp collect fsts snds setl setr 
  convol thePull pick_middlep fstOp sndOp csquare inver
  image2 relImage relInvImage prefCl PrefCl Succ Shift shift

end
