(*  Title:      HOL/Import/Generate-HOL/GenHOL4Word32.thy
    Author:     Sebastian Skalberg, TU Muenchen
*)

theory GenHOL4Word32 imports GenHOL4Base begin;

import_segment "hol4";

setup_dump "../HOL" "HOL4Word32";

append_dump "theory HOL4Word32 imports HOL4Base begin";

import_theory bits;

const_renames
  BIT > bit

end_import;

import_theory word32;

const_renames
  "==" > EQUIV;

end_import;

append_dump "end";

flush_dump;

import_segment "";

end
