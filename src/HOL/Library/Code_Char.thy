(*  Title:      HOL/Library/Code_Char.thy
    ID:         $Id$
    Author:     Florian Haftmann
*)

header {* Code generation of pretty characters (and strings) *}

theory Code_Char
imports Plain "~~/src/HOL/List" "~~/src/HOL/Code_Eval"
begin

code_type char
  (SML "char")
  (OCaml "char")
  (Haskell "Char")

setup {*
  fold (fn target => add_literal_char target) ["SML", "OCaml", "Haskell"] 
  #> add_literal_list_string "Haskell"
*}

code_instance char :: eq
  (Haskell -)

code_reserved SML
  char

code_reserved OCaml
  char

code_const "op = \<Colon> char \<Rightarrow> char \<Rightarrow> bool"
  (SML "!((_ : char) = _)")
  (OCaml "!((_ : char) = _)")
  (Haskell infixl 4 "==")

code_const "Code_Eval.term_of \<Colon> char \<Rightarrow> term"
  (SML "HOLogic.mk'_char/ (IntInf.fromInt/ (Char.ord/ _))")

end
