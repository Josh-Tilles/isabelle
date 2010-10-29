(*  Title:      HOLCF/HOLCF.thy
    Author:     Franz Regensburger

HOLCF -- a semantic extension of HOL by the LCF logic.
*)

theory HOLCF
imports
  Main
  Domain
  Powerdomains
begin

default_sort pcpo

ML {* path_add "~~/src/HOLCF/Library" *}

text {* Legacy theorem names deprecated after Isabelle2009-2: *}

lemmas expand_fun_below = fun_below_iff
lemmas below_fun_ext = fun_belowI
lemmas expand_cfun_eq = cfun_eq_iff
lemmas ext_cfun = cfun_eqI
lemmas expand_cfun_below = cfun_below_iff
lemmas below_cfun_ext = cfun_belowI
lemmas monofun_fun_fun = fun_belowD
lemmas monofun_fun_arg = monofunE
lemmas monofun_lub_fun = adm_monofun [THEN admD]
lemmas cont_lub_fun = adm_cont [THEN admD]
lemmas cont2cont_Rep_CFun = cont2cont_APP
lemmas cont_Rep_CFun_app = cont_APP_app
lemmas cont_Rep_CFun_app_app = cont_APP_app_app

text {* Older legacy theorem names: *}

lemmas sq_ord_less_eq_trans = below_eq_trans
lemmas sq_ord_eq_less_trans = eq_below_trans
lemmas refl_less = below_refl
lemmas trans_less = below_trans
lemmas antisym_less = below_antisym
lemmas antisym_less_inverse = below_antisym_inverse
lemmas box_less = box_below
lemmas rev_trans_less = rev_below_trans
lemmas not_less2not_eq = not_below2not_eq
lemmas less_UU_iff = below_UU_iff
lemmas flat_less_iff = flat_below_iff
lemmas adm_less = adm_below
lemmas adm_not_less = adm_not_below
lemmas adm_compact_not_less = adm_compact_not_below
lemmas less_fun_def = below_fun_def
lemmas expand_fun_less = expand_fun_below
lemmas less_fun_ext = below_fun_ext
lemmas less_discr_def = below_discr_def
lemmas discr_less_eq = discr_below_eq
lemmas less_unit_def = below_unit_def
lemmas less_cprod_def = below_prod_def
lemmas prod_lessI = prod_belowI
lemmas Pair_less_iff = Pair_below_iff
lemmas fst_less_iff = fst_below_iff
lemmas snd_less_iff = snd_below_iff
lemmas expand_cfun_less = expand_cfun_below
lemmas less_cfun_ext = below_cfun_ext
lemmas injection_less = injection_below
lemmas less_up_def = below_up_def
lemmas not_Iup_less = not_Iup_below
lemmas Iup_less = Iup_below
lemmas up_less = up_below
lemmas Def_inject_less_eq = Def_below_Def
lemmas Def_less_is_eq = Def_below_iff
lemmas spair_less_iff = spair_below_iff
lemmas less_sprod = below_sprod
lemmas spair_less = spair_below
lemmas sfst_less_iff = sfst_below_iff
lemmas ssnd_less_iff = ssnd_below_iff
lemmas fix_least_less = fix_least_below
lemmas dist_less_one = dist_below_one
lemmas less_ONE = below_ONE
lemmas ONE_less_iff = ONE_below_iff
lemmas less_sinlD = below_sinlD
lemmas less_sinrD = below_sinrD

end
