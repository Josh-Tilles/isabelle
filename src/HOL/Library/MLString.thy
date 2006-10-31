(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Monolithic strings for ML  *}

theory MLString
imports List
begin

section {* Monolithic strings for ML *}

subsection {* Motivation *}

text {*
  Strings are represented in HOL as list of characters.
  For code generation to Haskell, this is no problem
  since in Haskell "abc" is equivalent to ['a', 'b', 'c'].
  On the other hand, in ML all strings have to
  be represented as list of characters which
  is awkward to read. This theory provides a distinguished
  datatype for strings which then by convention
  are serialized as monolithic ML strings. Note
  that in Haskell these strings are identified
  with Haskell strings.
*}


subsection {* Datatype of monolithic strings *}

datatype ml_string = STR string

consts
  explode :: "ml_string \<Rightarrow> string"

primrec
  "explode (STR s) = s"


subsection {* ML interface *}

ML {*
structure MLString =
struct

local
  val thy = the_context ();
  val const_STR = Sign.intern_const thy "STR";
in
  val typ_ml_string = Type (Sign.intern_type thy "ml_string", []);
  fun term_ml_string s = Const (const_STR, HOList.typ_string --> typ_ml_string)
    $ HOList.term_string s
end;

end;
*}


subsection {* Code serialization *}

code_type ml_string
  (SML "string")
  (Haskell "String")

code_const STR
  (Haskell "_")

setup {*
  CodegenSerializer.add_pretty_ml_string "SML" "List.list.Nil" "List.list.Cons" "MLString.ml_string.STR"
    HOList.print_char HOList.print_string "String.implode"
*}

code_const explode
  (SML "String.explode")
  (Haskell "_")

code_reserved SML string explode
code_reserved Haskell string

end
