(*  Title:      HOL/Library/Code_Abstract_Nat.thy
    Author:     Stefan Berghofer, Florian Haftmann, TU Muenchen
*)

header {* Avoidance of pattern matching on natural numbers *}

theory Code_Abstract_Nat
imports Main
begin

text {*
  When natural numbers are implemented in another than the
  conventional inductive @{term "0::nat"}/@{term Suc} representation,
  it is necessary to avoid all pattern matching on natural numbers
  altogether.  This is accomplished by this theory (up to a certain
  extent).
*}

subsection {* Case analysis *}

text {*
  Case analysis on natural numbers is rephrased using a conditional
  expression:
*}

lemma [code, code_unfold]:
  "case_nat = (\<lambda>f g n. if n = 0 then f else g (n - 1))"
  by (auto simp add: fun_eq_iff dest!: gr0_implies_Suc)


subsection {* Preprocessors *}

text {*
  The term @{term "Suc n"} is no longer a valid pattern.  Therefore,
  all occurrences of this term in a position where a pattern is
  expected (i.e.~on the left-hand side of a code equation) must be
  eliminated.  This can be accomplished – as far as possible – by
  applying the following transformation rule:
*}

lemma Suc_if_eq: "(\<And>n. f (Suc n) \<equiv> h n) \<Longrightarrow> f 0 \<equiv> g \<Longrightarrow>
  f n \<equiv> if n = 0 then g else h (n - 1)"
  by (rule eq_reflection) (cases n, simp_all)

text {*
  The rule above is built into a preprocessor that is plugged into
  the code generator.
*}

setup {*
let

fun remove_suc thy thms =
  let
    val vname = singleton (Name.variant_list (map fst
      (fold (Term.add_var_names o Thm.full_prop_of) thms []))) "n";
    val cv = cterm_of thy (Var ((vname, 0), HOLogic.natT));
    fun lhs_of th = snd (Thm.dest_comb
      (fst (Thm.dest_comb (cprop_of th))));
    fun rhs_of th = snd (Thm.dest_comb (cprop_of th));
    fun find_vars ct = (case term_of ct of
        (Const (@{const_name Suc}, _) $ Var _) => [(cv, snd (Thm.dest_comb ct))]
      | _ $ _ =>
        let val (ct1, ct2) = Thm.dest_comb ct
        in 
          map (apfst (fn ct => Thm.apply ct ct2)) (find_vars ct1) @
          map (apfst (Thm.apply ct1)) (find_vars ct2)
        end
      | _ => []);
    val eqs = maps
      (fn th => map (pair th) (find_vars (lhs_of th))) thms;
    fun mk_thms (th, (ct, cv')) =
      let
        val th' =
          Thm.implies_elim
           (Conv.fconv_rule (Thm.beta_conversion true)
             (Drule.instantiate'
               [SOME (ctyp_of_term ct)] [SOME (Thm.lambda cv ct),
                 SOME (Thm.lambda cv' (rhs_of th)), NONE, SOME cv']
               @{thm Suc_if_eq})) (Thm.forall_intr cv' th)
      in
        case map_filter (fn th'' =>
            SOME (th'', singleton
              (Variable.trade (K (fn [th'''] => [th''' RS th']))
                (Variable.global_thm_context th'')) th'')
          handle THM _ => NONE) thms of
            [] => NONE
          | thps =>
              let val (ths1, ths2) = split_list thps
              in SOME (subtract Thm.eq_thm (th :: ths1) thms @ ths2) end
      end
  in get_first mk_thms eqs end;

fun eqn_suc_base_preproc thy thms =
  let
    val dest = fst o Logic.dest_equals o prop_of;
    val contains_suc = exists_Const (fn (c, _) => c = @{const_name Suc});
  in
    if forall (can dest) thms andalso exists (contains_suc o dest) thms
      then thms |> perhaps_loop (remove_suc thy) |> (Option.map o map) Drule.zero_var_indexes
       else NONE
  end;

val eqn_suc_preproc = Code_Preproc.simple_functrans eqn_suc_base_preproc;

in

  Code_Preproc.add_functrans ("eqn_Suc", eqn_suc_preproc)

end;
*}

end
