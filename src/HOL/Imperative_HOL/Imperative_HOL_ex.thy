(*  Title:      HOL/Imperative_HOL/Imperative_HOL_ex.thy
    Author:     John Matthews, Galois Connections;
                Alexander Krauss, Lukas Bulwahn & Florian Haftmann, TU Muenchen
*)

header {* Monadic imperative HOL with examples *}

theory Imperative_HOL_ex
imports Imperative_HOL
  "ex/Imperative_Quicksort" "ex/Imperative_Reverse" "ex/Linked_Lists" "ex/SatChecker"
begin

export_code "Array.*" "Ref.*" checking SML SML_imp OCaml? OCaml_imp? Haskell?

end
