(*  Title:      HOL/UNITY/Union.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Unions of programs

Partly from Misra's Chapter 5: Asynchronous Compositions of Programs
*)

Union = SubstAx + FP +

constdefs
  JOIN  :: ['a set, 'a => 'b program] => 'b program
    "JOIN I F == mk_program (INT i:I. Init (F i), UN i:I. Acts (F i))"

  Join :: ['a program, 'a program] => 'a program      (infixl 65)
    "F Join G == mk_program (Init F Int Init G, Acts F Un Acts G)"

  SKIP :: 'a program
    "SKIP == mk_program (UNIV, {})"

  Diff :: "['a program, ('a * 'a)set set] => 'a program"
    "Diff F acts == mk_program (Init F, Acts F - acts)"

  (*The set of systems that regard "v" as local to F*)
  localTo :: ['a => 'b, 'a program] => 'a program set  (infixl 80)
    "v localTo F == {G. ALL z. Diff G (Acts F) : stable {s. v s = z}}"

  (*Two programs with disjoint actions, except for Id (idling)*)
  Disjoint :: ['a program, 'a program] => bool
    "Disjoint F G == Acts F Int Acts G <= {Id}"

syntax
  "@JOIN"      :: [pttrn, 'a set, 'b set] => 'b set  ("(3JN _:_./ _)" 10)

translations
  "JN x:A. B"   == "JOIN A (%x. B)"

end
