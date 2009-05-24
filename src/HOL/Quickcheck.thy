(* Author: Florian Haftmann, TU Muenchen *)

header {* A simple counterexample generator *}

theory Quickcheck
imports Random Code_Eval
begin

notation fcomp (infixl "o>" 60)
notation scomp (infixl "o\<rightarrow>" 60)


subsection {* The @{text random} class *}

class random = typerep +
  fixes random :: "code_numeral \<Rightarrow> Random.seed \<Rightarrow> ('a \<times> (unit \<Rightarrow> term)) \<times> Random.seed"


subsection {* Quickcheck generator *}

ML {*
structure Quickcheck =
struct

open Quickcheck;

val eval_ref : (unit -> int -> int * int -> term list option * (int * int)) option ref = ref NONE;

val target = "Quickcheck";

fun mk_generator_expr thy prop tys =
  let
    val bound_max = length tys - 1;
    val bounds = map_index (fn (i, ty) =>
      (2 * (bound_max - i) + 1, 2 * (bound_max - i), 2 * i, ty)) tys;
    val result = list_comb (prop, map (fn (i, _, _, _) => Bound i) bounds);
    val terms = HOLogic.mk_list @{typ term} (map (fn (_, i, _, _) => Bound i $ @{term "()"}) bounds);
    val check = @{term "If \<Colon> bool \<Rightarrow> term list option \<Rightarrow> term list option \<Rightarrow> term list option"}
      $ result $ @{term "None \<Colon> term list option"} $ (@{term "Some \<Colon> term list \<Rightarrow> term list option "} $ terms);
    val return = @{term "Pair \<Colon> term list option \<Rightarrow> Random.seed \<Rightarrow> term list option \<times> Random.seed"};
    fun liftT T sT = sT --> HOLogic.mk_prodT (T, sT);
    fun mk_termtyp ty = HOLogic.mk_prodT (ty, @{typ "unit \<Rightarrow> term"});
    fun mk_scomp T1 T2 sT f g = Const (@{const_name scomp},
      liftT T1 sT --> (T1 --> liftT T2 sT) --> liftT T2 sT) $ f $ g;
    fun mk_split ty = Sign.mk_const thy
      (@{const_name split}, [ty, @{typ "unit \<Rightarrow> term"}, liftT @{typ "term list option"} @{typ Random.seed}]);
    fun mk_scomp_split ty t t' =
      mk_scomp (mk_termtyp ty) @{typ "term list option"} @{typ Random.seed} t
        (mk_split ty $ Abs ("", ty, Abs ("", @{typ "unit \<Rightarrow> term"}, t')));
    fun mk_bindclause (_, _, i, ty) = mk_scomp_split ty
      (Sign.mk_const thy (@{const_name random}, [ty]) $ Bound i);
  in Abs ("n", @{typ code_numeral}, fold_rev mk_bindclause bounds (return $ check)) end;

fun compile_generator_expr thy t =
  let
    val tys = (map snd o fst o strip_abs) t;
    val t' = mk_generator_expr thy t tys;
    val f = Code_ML.eval (SOME target) ("Quickcheck.eval_ref", eval_ref)
      (fn proc => fn g => fn s => g s #>> (Option.map o map) proc) thy t' [];
  in f #> Random_Engine.run end;

end
*}

setup {*
  Code_Target.extend_target (Quickcheck.target, (Code_ML.target_Eval, K I))
  #> Quickcheck.add_generator ("code", Quickcheck.compile_generator_expr o ProofContext.theory_of)
*}


subsection {* Fundamental types*}

instantiation bool :: random
begin

definition
  "random i = Random.range i o\<rightarrow>
    (\<lambda>k. Pair (if (k div 2 = 0) then Code_Eval.valtermify True else Code_Eval.valtermify False))"

instance ..

end

instantiation itself :: (typerep) random
begin

definition random_itself :: "code_numeral \<Rightarrow> Random.seed \<Rightarrow> ('a itself \<times> (unit \<Rightarrow> term)) \<times> Random.seed" where
  "random_itself _ = Pair (Code_Eval.valtermify TYPE('a))"

instance ..

end

text {* Type @{typ "'a \<Rightarrow> 'b"} *}

ML {*
structure Random_Engine =
struct

open Random_Engine;

fun random_fun (T1 : typ) (T2 : typ) (eq : 'a -> 'a -> bool) (term_of : 'a -> term)
    (random : Random_Engine.seed -> ('b * (unit -> term)) * Random_Engine.seed)
    (random_split : Random_Engine.seed -> Random_Engine.seed * Random_Engine.seed)
    (seed : Random_Engine.seed) =
  let
    val (seed', seed'') = random_split seed;
    val state = ref (seed', [], Const (@{const_name undefined}, T1 --> T2));
    val fun_upd = Const (@{const_name fun_upd},
      (T1 --> T2) --> T1 --> T2 --> T1 --> T2);
    fun random_fun' x =
      let
        val (seed, fun_map, f_t) = ! state;
      in case AList.lookup (uncurry eq) fun_map x
       of SOME y => y
        | NONE => let
              val t1 = term_of x;
              val ((y, t2), seed') = random seed;
              val fun_map' = (x, y) :: fun_map;
              val f_t' = fun_upd $ f_t $ t1 $ t2 ();
              val _ = state := (seed', fun_map', f_t');
            in y end
      end;
    fun term_fun' () = #3 (! state);
  in ((random_fun', term_fun'), seed'') end;

end
*}

axiomatization random_fun_aux :: "typerep \<Rightarrow> typerep \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> term)
  \<Rightarrow> (Random.seed \<Rightarrow> ('b \<times> (unit \<Rightarrow> term)) \<times> Random.seed) \<Rightarrow> (Random.seed \<Rightarrow> Random.seed \<times> Random.seed)
  \<Rightarrow> Random.seed \<Rightarrow> (('a \<Rightarrow> 'b) \<times> (unit \<Rightarrow> term)) \<times> Random.seed"

code_const random_fun_aux (Quickcheck "Random'_Engine.random'_fun")
  -- {* With enough criminal energy this can be abused to derive @{prop False};
  for this reason we use a distinguished target @{text Quickcheck}
  not spoiling the regular trusted code generation *}

instantiation "fun" :: ("{eq, term_of}", "{type, random}") random
begin

definition random_fun :: "code_numeral \<Rightarrow> Random.seed \<Rightarrow> (('a \<Rightarrow> 'b) \<times> (unit \<Rightarrow> term)) \<times> Random.seed" where
  "random n = random_fun_aux TYPEREP('a) TYPEREP('b) (op =) Code_Eval.term_of (random n) Random.split_seed"

instance ..

end

code_reserved Quickcheck Random_Engine


subsection {* Numeric types *}

instantiation nat :: random
begin

definition random_nat :: "code_numeral \<Rightarrow> Random.seed \<Rightarrow> (nat \<times> (unit \<Rightarrow> Code_Eval.term)) \<times> Random.seed" where
  "random_nat i = Random.range (i + 1) o\<rightarrow> (\<lambda>k. Pair (
     let n = Code_Numeral.nat_of k
     in (n, \<lambda>_. Code_Eval.term_of n)))"

instance ..

end

instantiation int :: random
begin

definition
  "random i = Random.range (2 * i + 1) o\<rightarrow> (\<lambda>k. Pair (
     let j = (if k \<ge> i then Code_Numeral.int_of (k - i) else - Code_Numeral.int_of (i - k))
     in (j, \<lambda>_. Code_Eval.term_of j)))"

instance ..

end

subsection {* Type copies *}

setup {*
let

fun mk_random_typecopy tyco vs constr typ thy =
  let
    val Ts = map TFree vs;  
    val T = Type (tyco, Ts);
    fun mk_termifyT T = HOLogic.mk_prodT (T, @{typ "unit \<Rightarrow> term"})
    val Ttm = mk_termifyT T;
    val typtm = mk_termifyT typ;
    fun mk_const c Ts = Const (c, Sign.const_instance thy (c, Ts));
    fun mk_random T = mk_const @{const_name random} [T];
    val size = @{term "k\<Colon>code_numeral"};
    val v = "x";
    val t_v = Free (v, typtm);
    val t_constr = mk_const constr Ts;
    val lhs = mk_random T $ size;
    val rhs = HOLogic.mk_ST [(((mk_random typ) $ size, @{typ Random.seed}), SOME (v, typtm))]
      (HOLogic.mk_return Ttm @{typ Random.seed}
      (mk_const "Code_Eval.valapp" [typ, T]
        $ HOLogic.mk_prod (t_constr, Abs ("u", @{typ unit}, HOLogic.reflect_term t_constr)) $ t_v))
      @{typ Random.seed} (SOME Ttm, @{typ Random.seed});
    val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in   
    thy
    |> TheoryTarget.instantiation ([tyco], vs, @{sort random})
    |> `(fn lthy => Syntax.check_term lthy eq)
    |-> (fn eq => Specification.definition (NONE, (Attrib.empty_binding, eq)))
    |> snd
    |> Class.prove_instantiation_exit (K (Class.intro_classes_tac []))
  end;

fun ensure_random_typecopy tyco thy =
  let
    val SOME { vs = raw_vs, constr, typ = raw_typ, ... } =
      TypecopyPackage.get_info thy tyco;
    val constrain = curry (Sorts.inter_sort (Sign.classes_of thy));
    val typ = map_atyps (fn TFree (v, sort) =>
      TFree (v, constrain sort @{sort random})) raw_typ;
    val vs' = Term.add_tfreesT typ [];
    val vs = map (fn (v, sort) =>
      (v, the_default (constrain sort @{sort typerep}) (AList.lookup (op =) vs' v))) raw_vs;
    val do_inst = Sign.of_sort thy (typ, @{sort random});
  in if do_inst then mk_random_typecopy tyco vs constr typ thy else thy end;

in

TypecopyPackage.interpretation ensure_random_typecopy

end
*}


subsection {* Type copies *}

setup {*
let

fun mk_random_typecopy tyco vs constr typ thy =
  let
    val Ts = map TFree vs;
    val T = Type (tyco, Ts);
    fun mk_termifyT T = HOLogic.mk_prodT (T, @{typ "unit \<Rightarrow> term"})
    val Ttm = mk_termifyT T;
    val typtm = mk_termifyT typ;
    fun mk_const c Ts = Const (c, Sign.const_instance thy (c, Ts));
    fun mk_random T = mk_const @{const_name random} [T];
    val size = @{term "k\<Colon>code_numeral"};
    val v = "x";
    val t_v = Free (v, typtm);
    val t_constr = mk_const constr Ts;
    val lhs = mk_random T $ size;
    val rhs = HOLogic.mk_ST [(((mk_random typ) $ size, @{typ Random.seed}), SOME (v, typtm))]
      (HOLogic.mk_return Ttm @{typ Random.seed}
      (mk_const "Code_Eval.valapp" [typ, T]
        $ HOLogic.mk_prod (t_constr, Abs ("u", @{typ unit}, HOLogic.reflect_term t_constr)) $ t_v))
      @{typ Random.seed} (SOME Ttm, @{typ Random.seed});
    val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in
    thy
    |> TheoryTarget.instantiation ([tyco], vs, @{sort random})
    |> `(fn lthy => Syntax.check_term lthy eq)
    |-> (fn eq => Specification.definition (NONE, (Attrib.empty_binding, eq)))
    |> snd
    |> Class.prove_instantiation_exit (K (Class.intro_classes_tac []))
  end;

fun ensure_random_typecopy tyco thy =
  let
    val SOME { vs = raw_vs, constr, typ = raw_typ, ... } =
      TypecopyPackage.get_info thy tyco;
    val constrain = curry (Sorts.inter_sort (Sign.classes_of thy));
    val typ = map_atyps (fn TFree (v, sort) =>
      TFree (v, constrain sort @{sort random})) raw_typ;
    val vs' = Term.add_tfreesT typ [];
    val vs = map (fn (v, sort) =>
      (v, the_default (constrain sort @{sort typerep}) (AList.lookup (op =) vs' v))) raw_vs;
    val do_inst = Sign.of_sort thy (typ, @{sort random});
  in if do_inst then mk_random_typecopy tyco vs constr typ thy else thy end;

in

TypecopyPackage.interpretation ensure_random_typecopy

end
*}


subsection {* Datatypes *}

text {* under construction *}


no_notation fcomp (infixl "o>" 60)
no_notation scomp (infixl "o\<rightarrow>" 60)

end
