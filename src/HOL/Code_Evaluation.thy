(*  Title:      HOL/Code_Evaluation.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Term evaluation using the generic code generator *}

theory Code_Evaluation
imports Plain Typerep Code_Numeral
begin

subsection {* Term representation *}

subsubsection {* Terms and class @{text term_of} *}

datatype "term" = dummy_term

definition Const :: "String.literal \<Rightarrow> typerep \<Rightarrow> term" where
  "Const _ _ = dummy_term"

definition App :: "term \<Rightarrow> term \<Rightarrow> term" where
  "App _ _ = dummy_term"

code_datatype Const App

class term_of = typerep +
  fixes term_of :: "'a \<Rightarrow> term"

lemma term_of_anything: "term_of x \<equiv> t"
  by (rule eq_reflection) (cases "term_of x", cases t, simp)

definition valapp :: "('a \<Rightarrow> 'b) \<times> (unit \<Rightarrow> term)
  \<Rightarrow> 'a \<times> (unit \<Rightarrow> term) \<Rightarrow> 'b \<times> (unit \<Rightarrow> term)" where
  "valapp f x = (fst f (fst x), \<lambda>u. App (snd f ()) (snd x ()))"

lemma valapp_code [code, code_unfold]:
  "valapp (f, tf) (x, tx) = (f x, \<lambda>u. App (tf ()) (tx ()))"
  by (simp only: valapp_def fst_conv snd_conv)


subsubsection {* @{text term_of} instances *}

instantiation "fun" :: (typerep, typerep) term_of
begin

definition
  "term_of (f \<Colon> 'a \<Rightarrow> 'b) = Const (STR ''dummy_pattern'') (Typerep.Typerep (STR ''fun'')
     [Typerep.typerep TYPE('a), Typerep.typerep TYPE('b)])"

instance ..

end

setup {*
let
  fun add_term_of tyco raw_vs thy =
    let
      val vs = map (fn (v, _) => (v, @{sort typerep})) raw_vs;
      val ty = Type (tyco, map TFree vs);
      val lhs = Const (@{const_name term_of}, ty --> @{typ term})
        $ Free ("x", ty);
      val rhs = @{term "undefined \<Colon> term"};
      val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
      fun triv_name_of t = (fst o dest_Free o fst o strip_comb o fst
        o HOLogic.dest_eq o HOLogic.dest_Trueprop) t ^ "_triv";
    in
      thy
      |> Class.instantiation ([tyco], vs, @{sort term_of})
      |> `(fn lthy => Syntax.check_term lthy eq)
      |-> (fn eq => Specification.definition (NONE, ((Binding.name (triv_name_of eq), []), eq)))
      |> snd
      |> Class.prove_instantiation_exit (K (Class.intro_classes_tac []))
    end;
  fun ensure_term_of (tyco, (raw_vs, _)) thy =
    let
      val need_inst = not (can (Sorts.mg_domain (Sign.classes_of thy) tyco) @{sort term_of})
        andalso can (Sorts.mg_domain (Sign.classes_of thy) tyco) @{sort typerep};
    in if need_inst then add_term_of tyco raw_vs thy else thy end;
in
  Code.datatype_interpretation ensure_term_of
  #> Code.abstype_interpretation ensure_term_of
end
*}

setup {*
let
  fun mk_term_of_eq thy ty vs tyco (c, tys) =
    let
      val t = list_comb (Const (c, tys ---> ty),
        map Free (Name.names Name.context "a" tys));
      val (arg, rhs) =
        pairself (Thm.cterm_of thy o map_types Logic.unvarifyT_global o Logic.varify_global)
          (t, (map_aterms (fn t as Free (v, ty) => HOLogic.mk_term_of ty t | t => t) o HOLogic.reflect_term) t)
      val cty = Thm.ctyp_of thy ty;
    in
      @{thm term_of_anything}
      |> Drule.instantiate' [SOME cty] [SOME arg, SOME rhs]
      |> Thm.varifyT_global
    end;
  fun add_term_of_code tyco raw_vs raw_cs thy =
    let
      val algebra = Sign.classes_of thy;
      val vs = map (fn (v, sort) =>
        (v, curry (Sorts.inter_sort algebra) @{sort typerep} sort)) raw_vs;
      val ty = Type (tyco, map TFree vs);
      val cs = (map o apsnd o map o map_atyps)
        (fn TFree (v, _) => TFree (v, (the o AList.lookup (op =) vs) v)) raw_cs;
      val const = AxClass.param_of_inst thy (@{const_name term_of}, tyco);
      val eqs = map (mk_term_of_eq thy ty vs tyco) cs;
   in
      thy
      |> Code.del_eqns const
      |> fold Code.add_eqn eqs
    end;
  fun ensure_term_of_code (tyco, (raw_vs, cs)) thy =
    let
      val has_inst = can (Sorts.mg_domain (Sign.classes_of thy) tyco) @{sort term_of};
    in if has_inst then add_term_of_code tyco raw_vs cs thy else thy end;
in
  Code.datatype_interpretation ensure_term_of_code
end
*}

setup {*
let
  fun mk_term_of_eq thy ty vs tyco abs ty_rep proj =
    let
      val arg = Var (("x", 0), ty);
      val rhs = Abs ("y", @{typ term}, HOLogic.reflect_term (Const (abs, ty_rep --> ty) $ Bound 0)) $
        (HOLogic.mk_term_of ty_rep (Const (proj, ty --> ty_rep) $ arg))
        |> Thm.cterm_of thy;
      val cty = Thm.ctyp_of thy ty;
    in
      @{thm term_of_anything}
      |> Drule.instantiate' [SOME cty] [SOME (Thm.cterm_of thy arg), SOME rhs]
      |> Thm.varifyT_global
    end;
  fun add_term_of_code tyco raw_vs abs raw_ty_rep proj thy =
    let
      val algebra = Sign.classes_of thy;
      val vs = map (fn (v, sort) =>
        (v, curry (Sorts.inter_sort algebra) @{sort typerep} sort)) raw_vs;
      val ty = Type (tyco, map TFree vs);
      val ty_rep = map_atyps
        (fn TFree (v, _) => TFree (v, (the o AList.lookup (op =) vs) v)) raw_ty_rep;
      val const = AxClass.param_of_inst thy (@{const_name term_of}, tyco);
      val eq = mk_term_of_eq thy ty vs tyco abs ty_rep proj;
   in
      thy
      |> Code.del_eqns const
      |> Code.add_eqn eq
    end;
  fun ensure_term_of_code (tyco, (raw_vs, ((abs, ty), (proj, _)))) thy =
    let
      val has_inst = can (Sorts.mg_domain (Sign.classes_of thy) tyco) @{sort term_of};
    in if has_inst then add_term_of_code tyco raw_vs abs ty proj thy else thy end;
in
  Code.abstype_interpretation ensure_term_of_code
end
*}


subsubsection {* Code generator setup *}

lemmas [code del] = term.recs term.cases term.size
lemma [code, code del]: "HOL.equal (t1\<Colon>term) t2 \<longleftrightarrow> HOL.equal t1 t2" ..

lemma [code, code del]: "(term_of \<Colon> typerep \<Rightarrow> term) = term_of" ..
lemma [code, code del]: "(term_of \<Colon> term \<Rightarrow> term) = term_of" ..
lemma [code, code del]: "(term_of \<Colon> String.literal \<Rightarrow> term) = term_of" ..
lemma [code, code del]:
  "(Code_Evaluation.term_of \<Colon> 'a::{type, term_of} Predicate.pred \<Rightarrow> Code_Evaluation.term) = Code_Evaluation.term_of" ..
lemma [code, code del]:
  "(Code_Evaluation.term_of \<Colon> 'a::{type, term_of} Predicate.seq \<Rightarrow> Code_Evaluation.term) = Code_Evaluation.term_of" ..

lemma term_of_char [unfolded typerep_fun_def typerep_char_def typerep_nibble_def, code]: "Code_Evaluation.term_of c =
    (let (n, m) = nibble_pair_of_char c
  in Code_Evaluation.App (Code_Evaluation.App (Code_Evaluation.Const (STR ''String.char.Char'') (TYPEREP(nibble \<Rightarrow> nibble \<Rightarrow> char)))
    (Code_Evaluation.term_of n)) (Code_Evaluation.term_of m))"
  by (subst term_of_anything) rule 

code_type "term"
  (Eval "Term.term")

code_const Const and App
  (Eval "Term.Const/ ((_), (_))" and "Term.$/ ((_), (_))")

code_const "term_of \<Colon> String.literal \<Rightarrow> term"
  (Eval "HOLogic.mk'_literal")

code_reserved Eval HOLogic


subsubsection {* Syntax *}

definition termify :: "'a \<Rightarrow> term" where
  [code del]: "termify x = dummy_term"

abbreviation valtermify :: "'a \<Rightarrow> 'a \<times> (unit \<Rightarrow> term)" where
  "valtermify x \<equiv> (x, \<lambda>u. termify x)"

setup {*
let
  fun map_default f xs =
    let val ys = map f xs
    in if exists is_some ys
      then SOME (map2 the_default xs ys)
      else NONE
    end;
  fun subst_termify_app (Const (@{const_name termify}, T), [t]) =
        if not (Term.has_abs t)
        then if fold_aterms (fn Const _ => I | _ => K false) t true
          then SOME (HOLogic.reflect_term t)
          else error "Cannot termify expression containing variables"
        else error "Cannot termify expression containing abstraction"
    | subst_termify_app (t, ts) = case map_default subst_termify ts
       of SOME ts' => SOME (list_comb (t, ts'))
        | NONE => NONE
  and subst_termify (Abs (v, T, t)) = (case subst_termify t
       of SOME t' => SOME (Abs (v, T, t'))
        | NONE => NONE)
    | subst_termify t = subst_termify_app (strip_comb t) 
  fun check_termify ts ctxt = map_default subst_termify ts
    |> Option.map (rpair ctxt)
in
  Context.theory_map (Syntax.add_term_check 0 "termify" check_termify)
end;
*}

locale term_syntax
begin

notation App (infixl "<\<cdot>>" 70)
  and valapp (infixl "{\<cdot>}" 70)

end

interpretation term_syntax .

no_notation App (infixl "<\<cdot>>" 70)
  and valapp (infixl "{\<cdot>}" 70)


subsection {* Numeric types *}

definition term_of_num :: "'a\<Colon>{semiring_div} \<Rightarrow> 'a\<Colon>{semiring_div} \<Rightarrow> term" where
  "term_of_num two = (\<lambda>_. dummy_term)"

lemma (in term_syntax) term_of_num_code [code]:
  "term_of_num two k = (if k = 0 then termify Int.Pls
    else (if k mod two = 0
      then termify Int.Bit0 <\<cdot>> term_of_num two (k div two)
      else termify Int.Bit1 <\<cdot>> term_of_num two (k div two)))"
  by (auto simp add: term_of_anything Const_def App_def term_of_num_def Let_def)

lemma (in term_syntax) term_of_nat_code [code]:
  "term_of (n::nat) = termify (number_of :: int \<Rightarrow> nat) <\<cdot>> term_of_num (2::nat) n"
  by (simp only: term_of_anything)

lemma (in term_syntax) term_of_int_code [code]:
  "term_of (k::int) = (if k = 0 then termify (0 :: int)
    else if k > 0 then termify (number_of :: int \<Rightarrow> int) <\<cdot>> term_of_num (2::int) k
      else termify (uminus :: int \<Rightarrow> int) <\<cdot>> (termify (number_of :: int \<Rightarrow> int) <\<cdot>> term_of_num (2::int) (- k)))"
  by (simp only: term_of_anything)

lemma (in term_syntax) term_of_code_numeral_code [code]:
  "term_of (k::code_numeral) = termify (number_of :: int \<Rightarrow> code_numeral) <\<cdot>> term_of_num (2::code_numeral) k"
  by (simp only: term_of_anything)

subsection {* Obfuscate *}

print_translation {*
let
  val term = Const ("<TERM>", dummyT);
  fun tr1' [_, _] = term;
  fun tr2' [] = term;
in
  [(@{const_syntax Const}, tr1'),
    (@{const_syntax App}, tr1'),
    (@{const_syntax dummy_term}, tr2')]
end
*}

hide_const dummy_term App valapp
hide_const (open) Const termify valtermify term_of term_of_num

subsection {* Tracing of generated and evaluated code *}

definition tracing :: "String.literal => 'a => 'a"
where
  [code del]: "tracing s x = x"

ML {*
structure Code_Evaluation =
struct

fun tracing s x = (Output.tracing s; x)

end
*}

code_const "tracing :: String.literal => 'a => 'a"
  (Eval "Code'_Evaluation.tracing")

hide_const (open) tracing
code_reserved Eval Code_Evaluation

subsection {* Evaluation setup *}

ML {*
signature EVAL =
sig
  val eval_ref: (unit -> term) option Unsynchronized.ref
  val eval_term: theory -> term -> term
end;

structure Eval : EVAL =
struct

val eval_ref = Unsynchronized.ref (NONE : (unit -> term) option);

fun eval_term thy t =
  Code_Eval.eval NONE ("Eval.eval_ref", eval_ref) I thy (HOLogic.mk_term_of (fastype_of t) t) [];

end;
*}

setup {*
  Value.add_evaluator ("code", Eval.eval_term o ProofContext.theory_of)
*}

end
