(*  Title:      CCL/Wfd.thy
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

header {* Well-founded relations in CCL *}

theory Wfd
imports Trancl Type Hered
uses ("wfd.ML") ("genrec.ML") ("typecheck.ML") ("eval.ML")
begin

consts
      (*** Predicates ***)
  Wfd        ::       "[i set] => o"
      (*** Relations ***)
  wf         ::       "[i set] => i set"
  wmap       ::       "[i=>i,i set] => i set"
  "**"       ::       "[i set,i set] => i set"      (infixl 70)
  NatPR      ::       "i set"
  ListPR     ::       "i set => i set"

axioms

  Wfd_def:
  "Wfd(R) == ALL P.(ALL x.(ALL y.<y,x> : R --> y:P) --> x:P) --> (ALL a. a:P)"

  wf_def:         "wf(R) == {x. x:R & Wfd(R)}"

  wmap_def:       "wmap(f,R) == {p. EX x y. p=<x,y>  &  <f(x),f(y)> : R}"
  lex_def:
  "ra**rb == {p. EX a a' b b'. p = <<a,b>,<a',b'>> & (<a,a'> : ra | (a=a' & <b,b'> : rb))}"

  NatPR_def:      "NatPR == {p. EX x:Nat. p=<x,succ(x)>}"
  ListPR_def:     "ListPR(A) == {p. EX h:A. EX t:List(A). p=<t,h$t>}"

ML {* use_legacy_bindings (the_context ()) *}

use "wfd.ML"
use "genrec.ML"
use "typecheck.ML"
use "eval.ML"

end
