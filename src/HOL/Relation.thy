(*  Title:      Relation.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

Relation = Prod +
consts
    Id          :: "('a * 'a)set"               (*the identity relation*)
    O           :: "[('b * 'c)set, ('a * 'b)set] => ('a * 'c)set" (infixr 60)
    converse    :: "('a*'b) set => ('b*'a) set"     ("(_^-1)" [1000] 999)
    "^^"        :: "[('a*'b) set,'a set] => 'b set" (infixl 90)
    Domain      :: "('a*'b) set => 'a set"
    Range       :: "('a*'b) set => 'b set"
    trans       :: "('a * 'a)set => bool"       (*transitivity predicate*)
    Univalent   :: "('a * 'b)set => bool"
defs
    Id_def        "Id == {p. ? x. p = (x,x)}"
    comp_def      "r O s == {(x,z). ? y. (x,y):s & (y,z):r}"
    converse_def   "r^-1 == {(y,x). (x,y):r}"
    Domain_def    "Domain(r) == {x. ? y. (x,y):r}"
    Range_def     "Range(r) == Domain(r^-1)"
    Image_def     "r ^^ s == {y. ? x:s. (x,y):r}"
    trans_def     "trans(r) == (!x y z. (x,y):r --> (y,z):r --> (x,z):r)"
    Univalent_def "Univalent r == !x y. (x,y):r --> (!z. (x,z):r --> y=z)"
end
