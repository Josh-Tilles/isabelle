(*  Title:      HOL/Import/Generate-HOL/GenHOL4Real.thy
    Author:     Sebastian Skalberg (TU Muenchen)
*)

theory GenHOL4Real imports GenHOL4Base begin

import_segment "hol4";

setup_dump "../HOL" "HOL4Real";

append_dump "theory HOL4Real imports HOL4Base begin";

import_theory realax;

type_maps
  real > RealDef.real;

const_maps
  real_0   > Groups.zero_class.zero :: real
  real_1   > Groups.one_class.one   :: real
  real_neg > Groups.uminus_class.uminus :: "real \<Rightarrow> real"
  inv > Fields.inverse_class.inverse :: "real \<Rightarrow> real"
  real_add > Groups.plus_class.plus :: "real \<Rightarrow> real \<Rightarrow> real"
  real_sub > Groups.minus_class.minus :: "real \<Rightarrow> real \<Rightarrow> real"
  real_mul > Groups.times_class.times :: "real \<Rightarrow> real \<Rightarrow> real"
  real_div > Fields.inverse_class.divide :: "real \<Rightarrow> real \<Rightarrow> real"
  real_lt > Orderings.ord_class.less :: "real \<Rightarrow> real \<Rightarrow> bool"
  mk_real > HOL.undefined   (* Otherwise proof_import_concl fails *)
  dest_real > HOL.undefined

ignore_thms
    real_TY_DEF
    real_tybij
    real_0
    real_1
    real_neg
    real_inv
    real_add
    real_mul
    real_lt
    real_of_hreal
    hreal_of_real
    REAL_ISO_EQ
    REAL_POS
    SUP_ALLPOS_LEMMA1
    SUP_ALLPOS_LEMMA2
    SUP_ALLPOS_LEMMA3
    SUP_ALLPOS_LEMMA4;

end_import;

import_theory real;

const_maps
  real_gt     > HOL4Compat.real_gt
  real_ge     > HOL4Compat.real_ge
  real_lte    > Orderings.ord_class.less_eq :: "real \<Rightarrow> real \<Rightarrow> bool"
  real_sub    > Groups.minus_class.minus :: "real \<Rightarrow> real \<Rightarrow> real"
  "/"         > Fields.inverse_class.divide :: "real \<Rightarrow> real \<Rightarrow> real"
  pow         > Power.power_class.power :: "real \<Rightarrow> nat \<Rightarrow> real"
  abs         > Groups.abs_class.abs :: "real => real"
  real_of_num > RealDef.real :: "nat => real";

end_import;

import_theory topology;
end_import;

import_theory nets;
end_import;

import_theory seq;
const_renames
"-->" > "hol4-->";

end_import;

import_theory lim;
end_import;

import_theory powser;
end_import;

import_theory transc;
end_import;

import_theory poly;
end_import;

append_dump "end";

flush_dump;

import_segment "";

end
