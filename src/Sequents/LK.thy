(*  Title:      LK/LK.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Axiom to express monotonicity (a variant of the deduction theorem).  Makes the
link between |- and ==>, needed for instance to prove imp_cong.

Axiom left_cong allows the simplifier to use left-side formulas.  Ideally it
should be derived from lower-level axioms.

CANNOT be added to LK0.thy because modal logic is built upon it, and
various modal rules would become inconsistent.
*)

theory LK
imports LK0
uses ("simpdata.ML")
begin

axioms

  monotonic:  "($H |- P ==> $H |- Q) ==> $H, P |- Q"

  left_cong:  "[| P == P';  |- P' ==> ($H |- $F) == ($H' |- $F') |]
               ==> (P, $H |- $F) == (P', $H' |- $F')"

ML {* use_legacy_bindings (the_context ()) *}

use "simpdata.ML"

end
