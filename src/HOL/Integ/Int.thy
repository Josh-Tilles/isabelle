(*  Title:      Integ/Int.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Type "int" is a linear order
*)

Int = IntDef +

instance int :: order (zle_refl,zle_trans,zle_anti_sym,int_less_le)
instance int :: linorder (zle_linear)

constdefs
  nat  :: int => nat
  "nat(Z) == if neg Z then 0 else (@ m. Z = $# m)"

end
