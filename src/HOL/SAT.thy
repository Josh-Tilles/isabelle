(*  Title:      HOL/SAT.thy
    Author:     Alwen Tiu, Tjark Weber
    Copyright   2005

Basic setup for the 'sat' and 'satx' tactics.
*)

header {* Reconstructing external resolution proofs for propositional logic *}

theory SAT
imports IHOL
begin

ML_file "Tools/prop_logic.ML"
ML_file "Tools/sat_solver.ML"
ML_file "Tools/sat.ML"

method_setup sat = {* Scan.succeed (SIMPLE_METHOD' o SAT.sat_tac) *}
  "SAT solver"

method_setup satx = {* Scan.succeed (SIMPLE_METHOD' o SAT.satx_tac) *}
  "SAT solver (with definitional CNF)"

end
