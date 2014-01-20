(*  Title:      HOL/Tools/BNF/bnf_fp_def_sugar_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Tactics for datatype and codatatype sugar.
*)

signature BNF_FP_DEF_SUGAR_TACTICS =
sig
  val sum_prod_thms_map: thm list
  val sum_prod_thms_set: thm list
  val sum_prod_thms_rel: thm list

  val mk_coinduct_tac: Proof.context -> thm list -> int -> int list -> thm -> thm list ->
    thm list -> thm list -> thm list list -> thm list list list -> thm list list list -> tactic
  val mk_coiter_tac: thm list -> thm list -> thm -> thm -> thm -> Proof.context -> tactic
  val mk_ctor_iff_dtor_tac: Proof.context -> ctyp option list -> cterm -> cterm -> thm -> thm ->
    tactic
  val mk_disc_coiter_iff_tac: thm list -> thm list -> thm list -> Proof.context -> tactic
  val mk_exhaust_tac: Proof.context -> int -> thm list -> thm -> thm -> tactic
  val mk_half_distinct_tac: Proof.context -> thm -> thm list -> tactic
  val mk_induct_tac: Proof.context -> int -> int list -> int list list -> int list list list ->
    thm list -> thm -> thm list -> thm list list -> tactic
  val mk_inject_tac: Proof.context -> thm -> thm -> tactic
  val mk_iter_tac: thm list -> thm list -> thm list -> thm -> thm -> Proof.context -> tactic
end;

structure BNF_FP_Def_Sugar_Tactics : BNF_FP_DEF_SUGAR_TACTICS =
struct

open BNF_Tactics
open BNF_Util
open BNF_FP_Util

val basic_simp_thms = @{thms simp_thms(7,8,12,14,22,24)};
val more_simp_thms = basic_simp_thms @ @{thms simp_thms(11,15,16,21)};

val sum_prod_thms_map = @{thms id_apply map_pair_simp prod.cases sum.cases sum_map.simps};
val sum_prod_thms_set0 =
  @{thms SUP_empty Sup_empty Sup_insert UN_insert Un_empty_left Un_empty_right Un_iff
      Union_Un_distrib collect_def[abs_def] image_def o_apply map_pair_simp
      mem_Collect_eq mem_UN_compreh_eq prod_set_simps sum_map.simps sum_set_simps};
val sum_prod_thms_set = @{thms UN_compreh_eq_eq} @ sum_prod_thms_set0;
val sum_prod_thms_rel = @{thms prod_rel_simp sum_rel_simps id_apply};

fun hhf_concl_conv cv ctxt ct =
  (case Thm.term_of ct of
    Const (@{const_name all}, _) $ Abs _ =>
    Conv.arg_conv (Conv.abs_conv (hhf_concl_conv cv o snd) ctxt) ct
  | _ => Conv.concl_conv ~1 cv ct);

fun co_induct_inst_as_projs ctxt k thm =
  let
    val fs = Term.add_vars (prop_of thm) []
      |> filter (fn (_, Type (@{type_name fun}, [_, T'])) => T' <> HOLogic.boolT | _ => false);
    fun mk_cfp (f as (_, T)) =
      (certify ctxt (Var f), certify ctxt (mk_proj T (num_binder_types T) k));
    val cfps = map mk_cfp fs;
  in
    Drule.cterm_instantiate cfps thm
  end;

val co_induct_inst_as_projs_tac = PRIMITIVE oo co_induct_inst_as_projs;

fun mk_exhaust_tac ctxt n ctr_defs ctor_iff_dtor sumEN' =
  unfold_thms_tac ctxt (ctor_iff_dtor :: ctr_defs) THEN HEADGOAL (rtac sumEN') THEN
  unfold_thms_tac ctxt @{thms split_paired_all} THEN
  HEADGOAL (EVERY' (maps (fn k => [select_prem_tac n (rotate_tac 1) k,
    REPEAT_DETERM o dtac meta_spec, etac meta_mp, atac]) (1 upto n)));

fun mk_ctor_iff_dtor_tac ctxt cTs cctor cdtor ctor_dtor dtor_ctor =
  HEADGOAL (rtac iffI THEN'
    EVERY' (map3 (fn cTs => fn cx => fn th =>
      dtac (Drule.instantiate' cTs [NONE, NONE, SOME cx] arg_cong) THEN'
      SELECT_GOAL (unfold_thms_tac ctxt [th]) THEN'
      atac) [rev cTs, cTs] [cdtor, cctor] [dtor_ctor, ctor_dtor]));

fun mk_half_distinct_tac ctxt ctor_inject ctr_defs =
  unfold_thms_tac ctxt (ctor_inject :: @{thms sum.inject} @ ctr_defs) THEN
  HEADGOAL (rtac @{thm sum.distinct(1)});

fun mk_inject_tac ctxt ctr_def ctor_inject =
  unfold_thms_tac ctxt [ctr_def] THEN HEADGOAL (rtac (ctor_inject RS ssubst)) THEN
  unfold_thms_tac ctxt @{thms sum.inject Pair_eq conj_assoc} THEN HEADGOAL (rtac refl);

val iter_unfold_thms =
  @{thms comp_def convol_def fst_conv id_def prod_case_Pair_iden snd_conv
      split_conv unit_case_Unity} @ sum_prod_thms_map;

fun mk_iter_tac pre_map_defs map_idents iter_defs ctor_iter ctr_def ctxt =
  unfold_thms_tac ctxt (ctr_def :: ctor_iter :: iter_defs @ pre_map_defs @ map_idents @
    iter_unfold_thms) THEN HEADGOAL (rtac refl);

val coiter_unfold_thms = @{thms id_def} @ sum_prod_thms_map;
val ss_if_True_False = simpset_of (ss_only @{thms if_True if_False} @{context});

fun mk_coiter_tac coiter_defs map_idents ctor_dtor_coiter pre_map_def ctr_def ctxt =
  unfold_thms_tac ctxt (ctr_def :: coiter_defs) THEN
  HEADGOAL (rtac (ctor_dtor_coiter RS trans) THEN'
    asm_simp_tac (put_simpset ss_if_True_False ctxt)) THEN_MAYBE
  (unfold_thms_tac ctxt (pre_map_def :: map_idents @ coiter_unfold_thms) THEN
   HEADGOAL (rtac refl ORELSE' rtac (@{thm unit_eq} RS arg_cong)));

fun mk_disc_coiter_iff_tac case_splits' coiters discs ctxt =
  EVERY (map3 (fn case_split_tac => fn coiter_thm => fn disc =>
      HEADGOAL case_split_tac THEN unfold_thms_tac ctxt [coiter_thm] THEN
      HEADGOAL (asm_simp_tac (ss_only basic_simp_thms ctxt)) THEN
      (if is_refl disc then all_tac else HEADGOAL (rtac disc)))
    (map rtac case_splits' @ [K all_tac]) coiters discs);

fun solve_prem_prem_tac ctxt =
  REPEAT o (eresolve_tac @{thms bexE rev_bexI} ORELSE' rtac @{thm rev_bexI[OF UNIV_I]} ORELSE'
    hyp_subst_tac ctxt ORELSE' resolve_tac @{thms disjI1 disjI2}) THEN'
  (rtac refl ORELSE' atac ORELSE' rtac @{thm singletonI});

fun mk_induct_leverage_prem_prems_tac ctxt nn kks set_maps pre_set_defs =
  HEADGOAL (EVERY' (maps (fn kk => [select_prem_tac nn (dtac meta_spec) kk, etac meta_mp,
    SELECT_GOAL (unfold_thms_tac ctxt (pre_set_defs @ set_maps @ sum_prod_thms_set0)),
    solve_prem_prem_tac ctxt]) (rev kks)));

fun mk_induct_discharge_prem_tac ctxt nn n set_maps pre_set_defs m k kks =
  let val r = length kks in
    HEADGOAL (EVERY' [select_prem_tac n (rotate_tac 1) k, rotate_tac ~1, hyp_subst_tac ctxt,
      REPEAT_DETERM_N m o (dtac meta_spec THEN' rotate_tac ~1)]) THEN
    EVERY [REPEAT_DETERM_N r
        (HEADGOAL (rotate_tac ~1 THEN' dtac meta_mp THEN' rotate_tac 1) THEN prefer_tac 2),
      if r > 0 then ALLGOALS (Goal.norm_hhf_tac ctxt) else all_tac, HEADGOAL atac,
      mk_induct_leverage_prem_prems_tac ctxt nn kks set_maps pre_set_defs]
  end;

fun mk_induct_tac ctxt nn ns mss kkss ctr_defs ctor_induct' set_maps pre_set_defss =
  let val n = Integer.sum ns in
    unfold_thms_tac ctxt ctr_defs THEN HEADGOAL (rtac ctor_induct') THEN
    co_induct_inst_as_projs_tac ctxt 0 THEN
    EVERY (map4 (EVERY oooo map3 o mk_induct_discharge_prem_tac ctxt nn n set_maps) pre_set_defss
      mss (unflat mss (1 upto n)) kkss)
  end;

fun mk_coinduct_same_ctr_tac ctxt rel_eqs pre_rel_def dtor_ctor ctr_def discs sels =
  hyp_subst_tac ctxt THEN'
  CONVERSION (hhf_concl_conv
    (Conv.top_conv (K (Conv.try_conv (Conv.rewr_conv ctr_def))) ctxt) ctxt) THEN'
  SELECT_GOAL (unfold_thms_tac ctxt (pre_rel_def :: dtor_ctor :: sels)) THEN'
  SELECT_GOAL (unfold_thms_tac ctxt (pre_rel_def :: dtor_ctor :: sels @ sum_prod_thms_rel)) THEN'
  (atac ORELSE' REPEAT o etac conjE THEN'
     full_simp_tac
       (ss_only (@{thm prod.inject} :: no_refl discs @ rel_eqs @ more_simp_thms) ctxt) THEN'
     REPEAT o etac conjE THEN_MAYBE' REPEAT o hyp_subst_tac ctxt THEN'
     REPEAT o (resolve_tac [refl, conjI] ORELSE' atac));

fun mk_coinduct_distinct_ctrs_tac ctxt discs discs' =
  let
    val discs'' = map (perhaps (try (fn th => th RS @{thm notnotD}))) (discs @ discs')
      |> distinct Thm.eq_thm_prop;
  in
    hyp_subst_tac ctxt THEN' REPEAT o etac conjE THEN'
    full_simp_tac (ss_only (refl :: no_refl discs'' @ basic_simp_thms) ctxt)
  end;

fun mk_coinduct_discharge_prem_tac ctxt rel_eqs' nn kk n pre_rel_def dtor_ctor exhaust ctr_defs
    discss selss =
  let val ks = 1 upto n in
    EVERY' ([rtac allI, rtac allI, rtac impI, select_prem_tac nn (dtac meta_spec) kk,
        dtac meta_spec, dtac meta_mp, atac, rtac exhaust, K (co_induct_inst_as_projs_tac ctxt 0),
        hyp_subst_tac ctxt] @
      map4 (fn k => fn ctr_def => fn discs => fn sels =>
        EVERY' ([rtac exhaust, K (co_induct_inst_as_projs_tac ctxt 1)] @
          map2 (fn k' => fn discs' =>
            if k' = k then
              mk_coinduct_same_ctr_tac ctxt rel_eqs' pre_rel_def dtor_ctor ctr_def discs sels
            else
              mk_coinduct_distinct_ctrs_tac ctxt discs discs') ks discss)) ks ctr_defs discss selss)
  end;

fun mk_coinduct_tac ctxt rel_eqs' nn ns dtor_coinduct' pre_rel_defs dtor_ctors exhausts ctr_defss
    discsss selsss =
  HEADGOAL (rtac dtor_coinduct' THEN'
    EVERY' (map8 (mk_coinduct_discharge_prem_tac ctxt rel_eqs' nn)
      (1 upto nn) ns pre_rel_defs dtor_ctors exhausts ctr_defss discsss selsss));

end;