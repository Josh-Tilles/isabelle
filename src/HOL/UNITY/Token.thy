(*  Title:      HOL/UNITY/Token
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Token Ring.

From Misra, "A Logic for Concurrent Programming" (1994), sections 5.2 and 13.2.
*)


Token = WFair + 

(*process states*)
datatype pstate = Hungry | Eating | Thinking

record state =
  token :: nat
  proc  :: nat => pstate


constdefs
  HasTok :: nat => state set
    "HasTok i == {s. token s = i}"

  H :: nat => state set
    "H i == {s. proc s i = Hungry}"

  E :: nat => state set
    "E i == {s. proc s i = Eating}"

  T :: nat => state set
    "T i == {s. proc s i = Thinking}"


locale Token =
  fixes
    N         :: nat	 (*number of nodes in the ring*)
    F         :: state program
    nodeOrder :: "nat => (nat*nat)set"
    next      :: nat => nat

  assumes
    N_positive "0<N"

    TR2  "F : constrains (T i) (T i Un H i)"

    TR3  "F : constrains (H i) (H i Un E i)"

    TR4  "F : constrains (H i - HasTok i) (H i)"

    TR5  "F : constrains (HasTok i) (HasTok i Un Compl(E i))"

    TR6  "F : leadsTo (H i Int HasTok i) (E i)"

    TR7  "F : leadsTo (HasTok i) (HasTok (next i))"

  defines
    nodeOrder_def
      "nodeOrder j == (inv_image less_than (%i. ((j+N)-i) mod N))  Int
		      (lessThan N Times lessThan N)"

    next_def
      "next i == (Suc i) mod N"

end
