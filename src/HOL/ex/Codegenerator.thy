(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Tests and examples for code generator *}

theory Codegenerator
imports ExecutableContent
begin

code_gen "*" in SML module_name CodegenTest
  in OCaml file -
  in Haskell file -

end
