(*  Title:      HOL/IMP/Natural.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Robert Sandner, TUM
    Copyright   1996 TUM

Natural semantics of commands
*)

Natural = Com + Inductive +

(** Execution of commands **)
consts  evalc    :: "(com*state*state)set"
        "@evalc" :: [com,state,state] => bool ("<_,_>/ -c-> _" [0,0,50] 50)

translations  "<ce,sig> -c-> s" == "(ce,sig,s) : evalc"

consts
  update  :: "('a => 'b) => 'a => 'b => ('a => 'b)"
           ("_/[_/:=/_]" [900,0,0] 900)
(* update is NOT defined, only declared!
   Thus the whole theory is independent of its meaning!
   If theory Update is included, proofs break.
*)

inductive evalc
  intrs
    Skip    "<SKIP,s> -c-> s"

    Assign  "<x := a,s> -c-> s[x:=a(s)]"

    Semi    "[| <c0,s> -c-> s2; <c1,s2> -c-> s1 |] 
            ==> <c0 ; c1, s> -c-> s1"

    IfTrue "[| b s; <c0,s> -c-> s1 |] 
            ==> <IF b THEN c0 ELSE c1, s> -c-> s1"

    IfFalse "[| ~b s; <c1,s> -c-> s1 |] 
             ==> <IF b THEN c0 ELSE c1, s> -c-> s1"

    WhileFalse "~b s ==> <WHILE b DO c,s> -c-> s"

    WhileTrue  "[| b s;  <c,s> -c-> s2;  <WHILE b DO c, s2> -c-> s1 |] 
               ==> <WHILE b DO c, s> -c-> s1"

end
