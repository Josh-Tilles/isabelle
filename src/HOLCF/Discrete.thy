(*  Title:      HOLCF/Discrete.thy
    ID:         $Id$
    Author:     Tobias Nipkow

Discrete CPOs.
*)

Discrete = Discrete1 +

instance discr :: (type)cpo   (discr_cpo)

constdefs
   undiscr :: ('a::type)discr => 'a
  "undiscr x == (case x of Discr y => y)"

end
