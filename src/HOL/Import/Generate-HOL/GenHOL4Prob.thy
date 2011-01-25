(*  Title:      HOL/Import/Generate-HOL/GenHOL4Prob.thy
    Author:     Sebastian Skalberg, TU Muenchen
*)

theory GenHOL4Prob imports GenHOL4Real begin

import_segment "hol4";

setup_dump "../HOL" "HOL4Prob";

append_dump "theory HOL4Prob imports HOL4Real begin";

import_theory prob_extra;

const_moves
  COMPL > GenHOL4Base.pred_set.COMPL;

end_import;

import_theory prob_canon;
end_import;

import_theory boolean_sequence;
end_import;

import_theory prob_algebra;
end_import;

import_theory prob;
end_import;

import_theory prob_pseudo;
end_import;

import_theory prob_indep;
end_import;

import_theory prob_uniform;
end_import;

append_dump "end";

flush_dump;

import_segment "";

end
