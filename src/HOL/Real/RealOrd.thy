(*  Title:	Real/RealOrd.thy
    ID: 	$Id$
    Author:     Lawrence C. Paulson
                Jacques D. Fleuriot
    Copyright:   1998  University of Cambridge
    Description: Type "real" is a linear order
*)

RealOrd = RealDef +

instance real :: order (real_le_refl,real_le_trans,real_le_anti_sym,real_less_le)
instance real :: linorder (real_le_linear)

defs
  abs_real_def "abs r == (if 0r <= r then r else -r)"

end
