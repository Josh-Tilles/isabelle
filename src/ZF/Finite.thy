(*  Title:      ZF/Finite.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Finite powerset operator
*)

Finite = Arith + Inductive +
consts
  Fin       :: i=>i
  FiniteFun :: [i,i]=>i         ("(_ -||>/ _)" [61, 60] 60)

inductive
  domains   "Fin(A)" <= "Pow(A)"
  intrs
    emptyI  "0 : Fin(A)"
    consI   "[| a: A;  b: Fin(A) |] ==> cons(a,b) : Fin(A)"
  type_intrs empty_subsetI, cons_subsetI, PowI
  type_elims "[make_elim PowD]"

inductive
  domains   "FiniteFun(A,B)" <= "Fin(A*B)"
  intrs
    emptyI  "0 : A -||> B"
    consI   "[| a: A;  b: B;  h: A -||> B;  a ~: domain(h)   
             |] ==> cons(<a,b>,h) : A -||> B"
  type_intrs "Fin.intrs"
end
