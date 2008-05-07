(*  Title:      HOL/Orderings.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Markus Wenzel, and Larry Paulson
*)

header {* Abstract orderings *}

theory Orderings
imports Code_Setup
uses
  "~~/src/Provers/order.ML"
begin

subsection {* Partial orders *}

class order = ord +
  assumes less_le: "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"
  and order_refl [iff]: "x \<le> x"
  and order_trans: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  assumes antisym: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
begin

text {* Reflexivity. *}

lemma eq_refl: "x = y \<Longrightarrow> x \<le> y"
    -- {* This form is useful with the classical reasoner. *}
by (erule ssubst) (rule order_refl)

lemma less_irrefl [iff]: "\<not> x < x"
by (simp add: less_le)

lemma le_less: "x \<le> y \<longleftrightarrow> x < y \<or> x = y"
    -- {* NOT suitable for iff, since it can cause PROOF FAILED. *}
by (simp add: less_le) blast

lemma le_imp_less_or_eq: "x \<le> y \<Longrightarrow> x < y \<or> x = y"
unfolding less_le by blast

lemma less_imp_le: "x < y \<Longrightarrow> x \<le> y"
unfolding less_le by blast


text {* Useful for simplification, but too risky to include by default. *}

lemma less_imp_not_eq: "x < y \<Longrightarrow> (x = y) \<longleftrightarrow> False"
by auto

lemma less_imp_not_eq2: "x < y \<Longrightarrow> (y = x) \<longleftrightarrow> False"
by auto


text {* Transitivity rules for calculational reasoning *}

lemma neq_le_trans: "a \<noteq> b \<Longrightarrow> a \<le> b \<Longrightarrow> a < b"
by (simp add: less_le)

lemma le_neq_trans: "a \<le> b \<Longrightarrow> a \<noteq> b \<Longrightarrow> a < b"
by (simp add: less_le)


text {* Asymmetry. *}

lemma less_not_sym: "x < y \<Longrightarrow> \<not> (y < x)"
by (simp add: less_le antisym)

lemma less_asym: "x < y \<Longrightarrow> (\<not> P \<Longrightarrow> y < x) \<Longrightarrow> P"
by (drule less_not_sym, erule contrapos_np) simp

lemma eq_iff: "x = y \<longleftrightarrow> x \<le> y \<and> y \<le> x"
by (blast intro: antisym)

lemma antisym_conv: "y \<le> x \<Longrightarrow> x \<le> y \<longleftrightarrow> x = y"
by (blast intro: antisym)

lemma less_imp_neq: "x < y \<Longrightarrow> x \<noteq> y"
by (erule contrapos_pn, erule subst, rule less_irrefl)


text {* Transitivity. *}

lemma less_trans: "x < y \<Longrightarrow> y < z \<Longrightarrow> x < z"
by (simp add: less_le) (blast intro: order_trans antisym)

lemma le_less_trans: "x \<le> y \<Longrightarrow> y < z \<Longrightarrow> x < z"
by (simp add: less_le) (blast intro: order_trans antisym)

lemma less_le_trans: "x < y \<Longrightarrow> y \<le> z \<Longrightarrow> x < z"
by (simp add: less_le) (blast intro: order_trans antisym)


text {* Useful for simplification, but too risky to include by default. *}

lemma less_imp_not_less: "x < y \<Longrightarrow> (\<not> y < x) \<longleftrightarrow> True"
by (blast elim: less_asym)

lemma less_imp_triv: "x < y \<Longrightarrow> (y < x \<longrightarrow> P) \<longleftrightarrow> True"
by (blast elim: less_asym)


text {* Transitivity rules for calculational reasoning *}

lemma less_asym': "a < b \<Longrightarrow> b < a \<Longrightarrow> P"
by (rule less_asym)


text {* Dual order *}

lemma dual_order:
  "order (op \<ge>) (op >)"
by unfold_locales
   (simp add: less_le, auto intro: antisym order_trans)

end


subsection {* Linear (total) orders *}

class linorder = order +
  assumes linear: "x \<le> y \<or> y \<le> x"
begin

lemma less_linear: "x < y \<or> x = y \<or> y < x"
unfolding less_le using less_le linear by blast

lemma le_less_linear: "x \<le> y \<or> y < x"
by (simp add: le_less less_linear)

lemma le_cases [case_names le ge]:
  "(x \<le> y \<Longrightarrow> P) \<Longrightarrow> (y \<le> x \<Longrightarrow> P) \<Longrightarrow> P"
using linear by blast

lemma linorder_cases [case_names less equal greater]:
  "(x < y \<Longrightarrow> P) \<Longrightarrow> (x = y \<Longrightarrow> P) \<Longrightarrow> (y < x \<Longrightarrow> P) \<Longrightarrow> P"
using less_linear by blast

lemma not_less: "\<not> x < y \<longleftrightarrow> y \<le> x"
apply (simp add: less_le)
using linear apply (blast intro: antisym)
done

lemma not_less_iff_gr_or_eq:
 "\<not>(x < y) \<longleftrightarrow> (x > y | x = y)"
apply(simp add:not_less le_less)
apply blast
done

lemma not_le: "\<not> x \<le> y \<longleftrightarrow> y < x"
apply (simp add: less_le)
using linear apply (blast intro: antisym)
done

lemma neq_iff: "x \<noteq> y \<longleftrightarrow> x < y \<or> y < x"
by (cut_tac x = x and y = y in less_linear, auto)

lemma neqE: "x \<noteq> y \<Longrightarrow> (x < y \<Longrightarrow> R) \<Longrightarrow> (y < x \<Longrightarrow> R) \<Longrightarrow> R"
by (simp add: neq_iff) blast

lemma antisym_conv1: "\<not> x < y \<Longrightarrow> x \<le> y \<longleftrightarrow> x = y"
by (blast intro: antisym dest: not_less [THEN iffD1])

lemma antisym_conv2: "x \<le> y \<Longrightarrow> \<not> x < y \<longleftrightarrow> x = y"
by (blast intro: antisym dest: not_less [THEN iffD1])

lemma antisym_conv3: "\<not> y < x \<Longrightarrow> \<not> x < y \<longleftrightarrow> x = y"
by (blast intro: antisym dest: not_less [THEN iffD1])

text{*Replacing the old Nat.leI*}
lemma leI: "\<not> x < y \<Longrightarrow> y \<le> x"
unfolding not_less .

lemma leD: "y \<le> x \<Longrightarrow> \<not> x < y"
unfolding not_less .

(*FIXME inappropriate name (or delete altogether)*)
lemma not_leE: "\<not> y \<le> x \<Longrightarrow> x < y"
unfolding not_le .


text {* Dual order *}

lemma dual_linorder:
  "linorder (op \<ge>) (op >)"
by unfold_locales
  (simp add: less_le, auto intro: antisym order_trans simp add: linear)


text {* min/max *}

text {* for historic reasons, definitions are done in context ord *}

definition (in ord)
  min :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  [code unfold, code inline del]: "min a b = (if a \<le> b then a else b)"

definition (in ord)
  max :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  [code unfold, code inline del]: "max a b = (if a \<le> b then b else a)"

lemma min_le_iff_disj:
  "min x y \<le> z \<longleftrightarrow> x \<le> z \<or> y \<le> z"
unfolding min_def using linear by (auto intro: order_trans)

lemma le_max_iff_disj:
  "z \<le> max x y \<longleftrightarrow> z \<le> x \<or> z \<le> y"
unfolding max_def using linear by (auto intro: order_trans)

lemma min_less_iff_disj:
  "min x y < z \<longleftrightarrow> x < z \<or> y < z"
unfolding min_def le_less using less_linear by (auto intro: less_trans)

lemma less_max_iff_disj:
  "z < max x y \<longleftrightarrow> z < x \<or> z < y"
unfolding max_def le_less using less_linear by (auto intro: less_trans)

lemma min_less_iff_conj [simp]:
  "z < min x y \<longleftrightarrow> z < x \<and> z < y"
unfolding min_def le_less using less_linear by (auto intro: less_trans)

lemma max_less_iff_conj [simp]:
  "max x y < z \<longleftrightarrow> x < z \<and> y < z"
unfolding max_def le_less using less_linear by (auto intro: less_trans)

lemma split_min [noatp]:
  "P (min i j) \<longleftrightarrow> (i \<le> j \<longrightarrow> P i) \<and> (\<not> i \<le> j \<longrightarrow> P j)"
by (simp add: min_def)

lemma split_max [noatp]:
  "P (max i j) \<longleftrightarrow> (i \<le> j \<longrightarrow> P j) \<and> (\<not> i \<le> j \<longrightarrow> P i)"
by (simp add: max_def)

end


subsection {* Reasoning tools setup *}

ML {*

signature ORDERS =
sig
  val print_structures: Proof.context -> unit
  val setup: theory -> theory
  val order_tac: thm list -> Proof.context -> int -> tactic
end;

structure Orders: ORDERS =
struct

(** Theory and context data **)

fun struct_eq ((s1: string, ts1), (s2, ts2)) =
  (s1 = s2) andalso eq_list (op aconv) (ts1, ts2);

structure Data = GenericDataFun
(
  type T = ((string * term list) * Order_Tac.less_arith) list;
    (* Order structures:
       identifier of the structure, list of operations and record of theorems
       needed to set up the transitivity reasoner,
       identifier and operations identify the structure uniquely. *)
  val empty = [];
  val extend = I;
  fun merge _ = AList.join struct_eq (K fst);
);

fun print_structures ctxt =
  let
    val structs = Data.get (Context.Proof ctxt);
    fun pretty_term t = Pretty.block
      [Pretty.quote (Syntax.pretty_term ctxt t), Pretty.brk 1,
        Pretty.str "::", Pretty.brk 1,
        Pretty.quote (Syntax.pretty_typ ctxt (type_of t))];
    fun pretty_struct ((s, ts), _) = Pretty.block
      [Pretty.str s, Pretty.str ":", Pretty.brk 1,
       Pretty.enclose "(" ")" (Pretty.breaks (map pretty_term ts))];
  in
    Pretty.writeln (Pretty.big_list "Order structures:" (map pretty_struct structs))
  end;


(** Method **)

fun struct_tac ((s, [eq, le, less]), thms) prems =
  let
    fun decomp thy (Trueprop $ t) =
      let
        fun excluded t =
          (* exclude numeric types: linear arithmetic subsumes transitivity *)
          let val T = type_of t
          in
	    T = HOLogic.natT orelse T = HOLogic.intT orelse T = HOLogic.realT
          end;
	fun rel (bin_op $ t1 $ t2) =
              if excluded t1 then NONE
              else if Pattern.matches thy (eq, bin_op) then SOME (t1, "=", t2)
              else if Pattern.matches thy (le, bin_op) then SOME (t1, "<=", t2)
              else if Pattern.matches thy (less, bin_op) then SOME (t1, "<", t2)
              else NONE
	  | rel _ = NONE;
	fun dec (Const (@{const_name Not}, _) $ t) = (case rel t
	      of NONE => NONE
	       | SOME (t1, rel, t2) => SOME (t1, "~" ^ rel, t2))
          | dec x = rel x;
      in dec t end;
  in
    case s of
      "order" => Order_Tac.partial_tac decomp thms prems
    | "linorder" => Order_Tac.linear_tac decomp thms prems
    | _ => error ("Unknown kind of order `" ^ s ^ "' encountered in transitivity reasoner.")
  end

fun order_tac prems ctxt =
  FIRST' (map (fn s => CHANGED o struct_tac s prems) (Data.get (Context.Proof ctxt)));


(** Attribute **)

fun add_struct_thm s tag =
  Thm.declaration_attribute
    (fn thm => Data.map (AList.map_default struct_eq (s, Order_Tac.empty TrueI) (Order_Tac.update tag thm)));
fun del_struct s =
  Thm.declaration_attribute
    (fn _ => Data.map (AList.delete struct_eq s));

val attribute = Attrib.syntax
     (Scan.lift ((Args.add -- Args.name >> (fn (_, s) => SOME s) ||
          Args.del >> K NONE) --| Args.colon (* FIXME ||
        Scan.succeed true *) ) -- Scan.lift Args.name --
      Scan.repeat Args.term
      >> (fn ((SOME tag, n), ts) => add_struct_thm (n, ts) tag
           | ((NONE, n), ts) => del_struct (n, ts)));


(** Diagnostic command **)

val print = Toplevel.unknown_context o
  Toplevel.keep (Toplevel.node_case
    (Context.cases (print_structures o ProofContext.init) print_structures)
    (print_structures o Proof.context_of));

val _ =
  OuterSyntax.improper_command "print_orders"
    "print order structures available to transitivity reasoner" OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o print));


(** Setup **)

val setup =
  Method.add_methods
    [("order", Method.ctxt_args (Method.SIMPLE_METHOD' o order_tac []), "transitivity reasoner")] #>
  Attrib.add_attributes [("order", attribute, "theorems controlling transitivity reasoner")];

end;

*}

setup Orders.setup


text {* Declarations to set up transitivity reasoner of partial and linear orders. *}

context order
begin

(* The type constraint on @{term op =} below is necessary since the operation
   is not a parameter of the locale. *)

lemmas
  [order add less_reflE: order "op = :: 'a \<Rightarrow> 'a \<Rightarrow> bool" "op <=" "op <"] =
  less_irrefl [THEN notE]
lemmas
  [order add le_refl: order "op = :: 'a => 'a => bool" "op <=" "op <"] =
  order_refl
lemmas
  [order add less_imp_le: order "op = :: 'a => 'a => bool" "op <=" "op <"] =
  less_imp_le
lemmas
  [order add eqI: order "op = :: 'a => 'a => bool" "op <=" "op <"] =
  antisym
lemmas
  [order add eqD1: order "op = :: 'a => 'a => bool" "op <=" "op <"] =
  eq_refl
lemmas
  [order add eqD2: order "op = :: 'a => 'a => bool" "op <=" "op <"] =
  sym [THEN eq_refl]
lemmas
  [order add less_trans: order "op = :: 'a => 'a => bool" "op <=" "op <"] =
  less_trans
lemmas
  [order add less_le_trans: order "op = :: 'a => 'a => bool" "op <=" "op <"] =
  less_le_trans
lemmas
  [order add le_less_trans: order "op = :: 'a => 'a => bool" "op <=" "op <"] =
  le_less_trans
lemmas
  [order add le_trans: order "op = :: 'a => 'a => bool" "op <=" "op <"] =
  order_trans
lemmas
  [order add le_neq_trans: order "op = :: 'a => 'a => bool" "op <=" "op <"] =
  le_neq_trans
lemmas
  [order add neq_le_trans: order "op = :: 'a => 'a => bool" "op <=" "op <"] =
  neq_le_trans
lemmas
  [order add less_imp_neq: order "op = :: 'a => 'a => bool" "op <=" "op <"] =
  less_imp_neq
lemmas
  [order add eq_neq_eq_imp_neq: order "op = :: 'a => 'a => bool" "op <=" "op <"] =
   eq_neq_eq_imp_neq
lemmas
  [order add not_sym: order "op = :: 'a => 'a => bool" "op <=" "op <"] =
  not_sym

end

context linorder
begin

lemmas
  [order del: order "op = :: 'a => 'a => bool" "op <=" "op <"] = _

lemmas
  [order add less_reflE: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  less_irrefl [THEN notE]
lemmas
  [order add le_refl: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  order_refl
lemmas
  [order add less_imp_le: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  less_imp_le
lemmas
  [order add not_lessI: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  not_less [THEN iffD2]
lemmas
  [order add not_leI: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  not_le [THEN iffD2]
lemmas
  [order add not_lessD: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  not_less [THEN iffD1]
lemmas
  [order add not_leD: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  not_le [THEN iffD1]
lemmas
  [order add eqI: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  antisym
lemmas
  [order add eqD1: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  eq_refl
lemmas
  [order add eqD2: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  sym [THEN eq_refl]
lemmas
  [order add less_trans: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  less_trans
lemmas
  [order add less_le_trans: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  less_le_trans
lemmas
  [order add le_less_trans: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  le_less_trans
lemmas
  [order add le_trans: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  order_trans
lemmas
  [order add le_neq_trans: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  le_neq_trans
lemmas
  [order add neq_le_trans: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  neq_le_trans
lemmas
  [order add less_imp_neq: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  less_imp_neq
lemmas
  [order add eq_neq_eq_imp_neq: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  eq_neq_eq_imp_neq
lemmas
  [order add not_sym: linorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  not_sym

end


setup {*
let

fun prp t thm = (#prop (rep_thm thm) = t);

fun prove_antisym_le sg ss ((le as Const(_,T)) $ r $ s) =
  let val prems = prems_of_ss ss;
      val less = Const (@{const_name less}, T);
      val t = HOLogic.mk_Trueprop(le $ s $ r);
  in case find_first (prp t) prems of
       NONE =>
         let val t = HOLogic.mk_Trueprop(HOLogic.Not $ (less $ r $ s))
         in case find_first (prp t) prems of
              NONE => NONE
            | SOME thm => SOME(mk_meta_eq(thm RS @{thm linorder_class.antisym_conv1}))
         end
     | SOME thm => SOME(mk_meta_eq(thm RS @{thm order_class.antisym_conv}))
  end
  handle THM _ => NONE;

fun prove_antisym_less sg ss (NotC $ ((less as Const(_,T)) $ r $ s)) =
  let val prems = prems_of_ss ss;
      val le = Const (@{const_name less_eq}, T);
      val t = HOLogic.mk_Trueprop(le $ r $ s);
  in case find_first (prp t) prems of
       NONE =>
         let val t = HOLogic.mk_Trueprop(NotC $ (less $ s $ r))
         in case find_first (prp t) prems of
              NONE => NONE
            | SOME thm => SOME(mk_meta_eq(thm RS @{thm linorder_class.antisym_conv3}))
         end
     | SOME thm => SOME(mk_meta_eq(thm RS @{thm linorder_class.antisym_conv2}))
  end
  handle THM _ => NONE;

fun add_simprocs procs thy =
  Simplifier.map_simpset (fn ss => ss
    addsimprocs (map (fn (name, raw_ts, proc) =>
      Simplifier.simproc thy name raw_ts proc) procs)) thy;
fun add_solver name tac =
  Simplifier.map_simpset (fn ss => ss addSolver
    mk_solver' name (fn ss => tac (Simplifier.prems_of_ss ss) (Simplifier.the_context ss)));

in
  add_simprocs [
       ("antisym le", ["(x::'a::order) <= y"], prove_antisym_le),
       ("antisym less", ["~ (x::'a::linorder) < y"], prove_antisym_less)
     ]
  #> add_solver "Transitivity" Orders.order_tac
  (* Adding the transitivity reasoners also as safe solvers showed a slight
     speed up, but the reasoning strength appears to be not higher (at least
     no breaking of additional proofs in the entire HOL distribution, as
     of 5 March 2004, was observed). *)
end
*}


subsection {* Name duplicates *}

lemmas order_less_le = less_le
lemmas order_eq_refl = order_class.eq_refl
lemmas order_less_irrefl = order_class.less_irrefl
lemmas order_le_less = order_class.le_less
lemmas order_le_imp_less_or_eq = order_class.le_imp_less_or_eq
lemmas order_less_imp_le = order_class.less_imp_le
lemmas order_less_imp_not_eq = order_class.less_imp_not_eq
lemmas order_less_imp_not_eq2 = order_class.less_imp_not_eq2
lemmas order_neq_le_trans = order_class.neq_le_trans
lemmas order_le_neq_trans = order_class.le_neq_trans

lemmas order_antisym = antisym
lemmas order_less_not_sym = order_class.less_not_sym
lemmas order_less_asym = order_class.less_asym
lemmas order_eq_iff = order_class.eq_iff
lemmas order_antisym_conv = order_class.antisym_conv
lemmas order_less_trans = order_class.less_trans
lemmas order_le_less_trans = order_class.le_less_trans
lemmas order_less_le_trans = order_class.less_le_trans
lemmas order_less_imp_not_less = order_class.less_imp_not_less
lemmas order_less_imp_triv = order_class.less_imp_triv
lemmas order_less_asym' = order_class.less_asym'

lemmas linorder_linear = linear
lemmas linorder_less_linear = linorder_class.less_linear
lemmas linorder_le_less_linear = linorder_class.le_less_linear
lemmas linorder_le_cases = linorder_class.le_cases
lemmas linorder_not_less = linorder_class.not_less
lemmas linorder_not_le = linorder_class.not_le
lemmas linorder_neq_iff = linorder_class.neq_iff
lemmas linorder_neqE = linorder_class.neqE
lemmas linorder_antisym_conv1 = linorder_class.antisym_conv1
lemmas linorder_antisym_conv2 = linorder_class.antisym_conv2
lemmas linorder_antisym_conv3 = linorder_class.antisym_conv3


subsection {* Bounded quantifiers *}

syntax
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3ALL _<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3EX _<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3ALL _<=_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3EX _<=_./ _)" [0, 0, 10] 10)

  "_All_greater" :: "[idt, 'a, bool] => bool"    ("(3ALL _>_./ _)"  [0, 0, 10] 10)
  "_Ex_greater" :: "[idt, 'a, bool] => bool"    ("(3EX _>_./ _)"  [0, 0, 10] 10)
  "_All_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3ALL _>=_./ _)" [0, 0, 10] 10)
  "_Ex_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3EX _>=_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<le>_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<le>_./ _)" [0, 0, 10] 10)

  "_All_greater" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_>_./ _)"  [0, 0, 10] 10)
  "_Ex_greater" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_>_./ _)"  [0, 0, 10] 10)
  "_All_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<ge>_./ _)" [0, 0, 10] 10)
  "_Ex_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<ge>_./ _)" [0, 0, 10] 10)

syntax (HOL)
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3! _<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3? _<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3! _<=_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3? _<=_./ _)" [0, 0, 10] 10)

syntax (HTML output)
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<le>_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<le>_./ _)" [0, 0, 10] 10)

  "_All_greater" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_>_./ _)"  [0, 0, 10] 10)
  "_Ex_greater" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_>_./ _)"  [0, 0, 10] 10)
  "_All_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<ge>_./ _)" [0, 0, 10] 10)
  "_Ex_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<ge>_./ _)" [0, 0, 10] 10)

translations
  "ALL x<y. P"   =>  "ALL x. x < y \<longrightarrow> P"
  "EX x<y. P"    =>  "EX x. x < y \<and> P"
  "ALL x<=y. P"  =>  "ALL x. x <= y \<longrightarrow> P"
  "EX x<=y. P"   =>  "EX x. x <= y \<and> P"
  "ALL x>y. P"   =>  "ALL x. x > y \<longrightarrow> P"
  "EX x>y. P"    =>  "EX x. x > y \<and> P"
  "ALL x>=y. P"  =>  "ALL x. x >= y \<longrightarrow> P"
  "EX x>=y. P"   =>  "EX x. x >= y \<and> P"

print_translation {*
let
  val All_binder = Syntax.binder_name @{const_syntax All};
  val Ex_binder = Syntax.binder_name @{const_syntax Ex};
  val impl = @{const_syntax "op -->"};
  val conj = @{const_syntax "op &"};
  val less = @{const_syntax less};
  val less_eq = @{const_syntax less_eq};

  val trans =
   [((All_binder, impl, less), ("_All_less", "_All_greater")),
    ((All_binder, impl, less_eq), ("_All_less_eq", "_All_greater_eq")),
    ((Ex_binder, conj, less), ("_Ex_less", "_Ex_greater")),
    ((Ex_binder, conj, less_eq), ("_Ex_less_eq", "_Ex_greater_eq"))];

  fun matches_bound v t = 
     case t of (Const ("_bound", _) $ Free (v', _)) => (v = v')
              | _ => false
  fun contains_var v = Term.exists_subterm (fn Free (x, _) => x = v | _ => false)
  fun mk v c n P = Syntax.const c $ Syntax.mark_bound v $ n $ P

  fun tr' q = (q,
    fn [Const ("_bound", _) $ Free (v, _), Const (c, _) $ (Const (d, _) $ t $ u) $ P] =>
      (case AList.lookup (op =) trans (q, c, d) of
        NONE => raise Match
      | SOME (l, g) =>
          if matches_bound v t andalso not (contains_var v u) then mk v l u P
          else if matches_bound v u andalso not (contains_var v t) then mk v g t P
          else raise Match)
     | _ => raise Match);
in [tr' All_binder, tr' Ex_binder] end
*}


subsection {* Transitivity reasoning *}

context ord
begin

lemma ord_le_eq_trans: "a \<le> b \<Longrightarrow> b = c \<Longrightarrow> a \<le> c"
  by (rule subst)

lemma ord_eq_le_trans: "a = b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c"
  by (rule ssubst)

lemma ord_less_eq_trans: "a < b \<Longrightarrow> b = c \<Longrightarrow> a < c"
  by (rule subst)

lemma ord_eq_less_trans: "a = b \<Longrightarrow> b < c \<Longrightarrow> a < c"
  by (rule ssubst)

end

lemma order_less_subst2: "(a::'a::order) < b ==> f b < (c::'c::order) ==>
  (!!x y. x < y ==> f x < f y) ==> f a < c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < b" hence "f a < f b" by (rule r)
  also assume "f b < c"
  finally (order_less_trans) show ?thesis .
qed

lemma order_less_subst1: "(a::'a::order) < f b ==> (b::'b::order) < c ==>
  (!!x y. x < y ==> f x < f y) ==> a < f c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < f b"
  also assume "b < c" hence "f b < f c" by (rule r)
  finally (order_less_trans) show ?thesis .
qed

lemma order_le_less_subst2: "(a::'a::order) <= b ==> f b < (c::'c::order) ==>
  (!!x y. x <= y ==> f x <= f y) ==> f a < c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= b" hence "f a <= f b" by (rule r)
  also assume "f b < c"
  finally (order_le_less_trans) show ?thesis .
qed

lemma order_le_less_subst1: "(a::'a::order) <= f b ==> (b::'b::order) < c ==>
  (!!x y. x < y ==> f x < f y) ==> a < f c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a <= f b"
  also assume "b < c" hence "f b < f c" by (rule r)
  finally (order_le_less_trans) show ?thesis .
qed

lemma order_less_le_subst2: "(a::'a::order) < b ==> f b <= (c::'c::order) ==>
  (!!x y. x < y ==> f x < f y) ==> f a < c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < b" hence "f a < f b" by (rule r)
  also assume "f b <= c"
  finally (order_less_le_trans) show ?thesis .
qed

lemma order_less_le_subst1: "(a::'a::order) < f b ==> (b::'b::order) <= c ==>
  (!!x y. x <= y ==> f x <= f y) ==> a < f c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a < f b"
  also assume "b <= c" hence "f b <= f c" by (rule r)
  finally (order_less_le_trans) show ?thesis .
qed

lemma order_subst1: "(a::'a::order) <= f b ==> (b::'b::order) <= c ==>
  (!!x y. x <= y ==> f x <= f y) ==> a <= f c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= f b"
  also assume "b <= c" hence "f b <= f c" by (rule r)
  finally (order_trans) show ?thesis .
qed

lemma order_subst2: "(a::'a::order) <= b ==> f b <= (c::'c::order) ==>
  (!!x y. x <= y ==> f x <= f y) ==> f a <= c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= b" hence "f a <= f b" by (rule r)
  also assume "f b <= c"
  finally (order_trans) show ?thesis .
qed

lemma ord_le_eq_subst: "a <= b ==> f b = c ==>
  (!!x y. x <= y ==> f x <= f y) ==> f a <= c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= b" hence "f a <= f b" by (rule r)
  also assume "f b = c"
  finally (ord_le_eq_trans) show ?thesis .
qed

lemma ord_eq_le_subst: "a = f b ==> b <= c ==>
  (!!x y. x <= y ==> f x <= f y) ==> a <= f c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a = f b"
  also assume "b <= c" hence "f b <= f c" by (rule r)
  finally (ord_eq_le_trans) show ?thesis .
qed

lemma ord_less_eq_subst: "a < b ==> f b = c ==>
  (!!x y. x < y ==> f x < f y) ==> f a < c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < b" hence "f a < f b" by (rule r)
  also assume "f b = c"
  finally (ord_less_eq_trans) show ?thesis .
qed

lemma ord_eq_less_subst: "a = f b ==> b < c ==>
  (!!x y. x < y ==> f x < f y) ==> a < f c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a = f b"
  also assume "b < c" hence "f b < f c" by (rule r)
  finally (ord_eq_less_trans) show ?thesis .
qed

text {*
  Note that this list of rules is in reverse order of priorities.
*}

lemmas order_trans_rules [trans] =
  order_less_subst2
  order_less_subst1
  order_le_less_subst2
  order_le_less_subst1
  order_less_le_subst2
  order_less_le_subst1
  order_subst2
  order_subst1
  ord_le_eq_subst
  ord_eq_le_subst
  ord_less_eq_subst
  ord_eq_less_subst
  forw_subst
  back_subst
  rev_mp
  mp
  order_neq_le_trans
  order_le_neq_trans
  order_less_trans
  order_less_asym'
  order_le_less_trans
  order_less_le_trans
  order_trans
  order_antisym
  ord_le_eq_trans
  ord_eq_le_trans
  ord_less_eq_trans
  ord_eq_less_trans
  trans


(* FIXME cleanup *)

text {* These support proving chains of decreasing inequalities
    a >= b >= c ... in Isar proofs. *}

lemma xt1:
  "a = b ==> b > c ==> a > c"
  "a > b ==> b = c ==> a > c"
  "a = b ==> b >= c ==> a >= c"
  "a >= b ==> b = c ==> a >= c"
  "(x::'a::order) >= y ==> y >= x ==> x = y"
  "(x::'a::order) >= y ==> y >= z ==> x >= z"
  "(x::'a::order) > y ==> y >= z ==> x > z"
  "(x::'a::order) >= y ==> y > z ==> x > z"
  "(a::'a::order) > b ==> b > a ==> P"
  "(x::'a::order) > y ==> y > z ==> x > z"
  "(a::'a::order) >= b ==> a ~= b ==> a > b"
  "(a::'a::order) ~= b ==> a >= b ==> a > b"
  "a = f b ==> b > c ==> (!!x y. x > y ==> f x > f y) ==> a > f c" 
  "a > b ==> f b = c ==> (!!x y. x > y ==> f x > f y) ==> f a > c"
  "a = f b ==> b >= c ==> (!!x y. x >= y ==> f x >= f y) ==> a >= f c"
  "a >= b ==> f b = c ==> (!! x y. x >= y ==> f x >= f y) ==> f a >= c"
  by auto

lemma xt2:
  "(a::'a::order) >= f b ==> b >= c ==> (!!x y. x >= y ==> f x >= f y) ==> a >= f c"
by (subgoal_tac "f b >= f c", force, force)

lemma xt3: "(a::'a::order) >= b ==> (f b::'b::order) >= c ==> 
    (!!x y. x >= y ==> f x >= f y) ==> f a >= c"
by (subgoal_tac "f a >= f b", force, force)

lemma xt4: "(a::'a::order) > f b ==> (b::'b::order) >= c ==>
  (!!x y. x >= y ==> f x >= f y) ==> a > f c"
by (subgoal_tac "f b >= f c", force, force)

lemma xt5: "(a::'a::order) > b ==> (f b::'b::order) >= c==>
    (!!x y. x > y ==> f x > f y) ==> f a > c"
by (subgoal_tac "f a > f b", force, force)

lemma xt6: "(a::'a::order) >= f b ==> b > c ==>
    (!!x y. x > y ==> f x > f y) ==> a > f c"
by (subgoal_tac "f b > f c", force, force)

lemma xt7: "(a::'a::order) >= b ==> (f b::'b::order) > c ==>
    (!!x y. x >= y ==> f x >= f y) ==> f a > c"
by (subgoal_tac "f a >= f b", force, force)

lemma xt8: "(a::'a::order) > f b ==> (b::'b::order) > c ==>
    (!!x y. x > y ==> f x > f y) ==> a > f c"
by (subgoal_tac "f b > f c", force, force)

lemma xt9: "(a::'a::order) > b ==> (f b::'b::order) > c ==>
    (!!x y. x > y ==> f x > f y) ==> f a > c"
by (subgoal_tac "f a > f b", force, force)

lemmas xtrans = xt1 xt2 xt3 xt4 xt5 xt6 xt7 xt8 xt9

(* 
  Since "a >= b" abbreviates "b <= a", the abbreviation "..." stands
  for the wrong thing in an Isar proof.

  The extra transitivity rules can be used as follows: 

lemma "(a::'a::order) > z"
proof -
  have "a >= b" (is "_ >= ?rhs")
    sorry
  also have "?rhs >= c" (is "_ >= ?rhs")
    sorry
  also (xtrans) have "?rhs = d" (is "_ = ?rhs")
    sorry
  also (xtrans) have "?rhs >= e" (is "_ >= ?rhs")
    sorry
  also (xtrans) have "?rhs > f" (is "_ > ?rhs")
    sorry
  also (xtrans) have "?rhs > z"
    sorry
  finally (xtrans) show ?thesis .
qed

  Alternatively, one can use "declare xtrans [trans]" and then
  leave out the "(xtrans)" above.
*)

subsection {* Order on bool *}

instantiation bool :: order
begin

definition
  le_bool_def [code func del]: "P \<le> Q \<longleftrightarrow> P \<longrightarrow> Q"

definition
  less_bool_def [code func del]: "(P\<Colon>bool) < Q \<longleftrightarrow> P \<le> Q \<and> P \<noteq> Q"

instance
  by intro_classes (auto simp add: le_bool_def less_bool_def)

end

lemma le_boolI: "(P \<Longrightarrow> Q) \<Longrightarrow> P \<le> Q"
by (simp add: le_bool_def)

lemma le_boolI': "P \<longrightarrow> Q \<Longrightarrow> P \<le> Q"
by (simp add: le_bool_def)

lemma le_boolE: "P \<le> Q \<Longrightarrow> P \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R"
by (simp add: le_bool_def)

lemma le_boolD: "P \<le> Q \<Longrightarrow> P \<longrightarrow> Q"
by (simp add: le_bool_def)

lemma [code func]:
  "False \<le> b \<longleftrightarrow> True"
  "True \<le> b \<longleftrightarrow> b"
  "False < b \<longleftrightarrow> b"
  "True < b \<longleftrightarrow> False"
  unfolding le_bool_def less_bool_def by simp_all


subsection {* Order on functions *}

instantiation "fun" :: (type, ord) ord
begin

definition
  le_fun_def [code func del]: "f \<le> g \<longleftrightarrow> (\<forall>x. f x \<le> g x)"

definition
  less_fun_def [code func del]: "(f\<Colon>'a \<Rightarrow> 'b) < g \<longleftrightarrow> f \<le> g \<and> f \<noteq> g"

instance ..

end

instance "fun" :: (type, order) order
  by default
    (auto simp add: le_fun_def less_fun_def
       intro: order_trans order_antisym intro!: ext)

lemma le_funI: "(\<And>x. f x \<le> g x) \<Longrightarrow> f \<le> g"
  unfolding le_fun_def by simp

lemma le_funE: "f \<le> g \<Longrightarrow> (f x \<le> g x \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding le_fun_def by simp

lemma le_funD: "f \<le> g \<Longrightarrow> f x \<le> g x"
  unfolding le_fun_def by simp

text {*
  Handy introduction and elimination rules for @{text "\<le>"}
  on unary and binary predicates
*}

lemma predicate1I:
  assumes PQ: "\<And>x. P x \<Longrightarrow> Q x"
  shows "P \<le> Q"
  apply (rule le_funI)
  apply (rule le_boolI)
  apply (rule PQ)
  apply assumption
  done

lemma predicate1D [Pure.dest, dest]: "P \<le> Q \<Longrightarrow> P x \<Longrightarrow> Q x"
  apply (erule le_funE)
  apply (erule le_boolE)
  apply assumption+
  done

lemma predicate2I [Pure.intro!, intro!]:
  assumes PQ: "\<And>x y. P x y \<Longrightarrow> Q x y"
  shows "P \<le> Q"
  apply (rule le_funI)+
  apply (rule le_boolI)
  apply (rule PQ)
  apply assumption
  done

lemma predicate2D [Pure.dest, dest]: "P \<le> Q \<Longrightarrow> P x y \<Longrightarrow> Q x y"
  apply (erule le_funE)+
  apply (erule le_boolE)
  apply assumption+
  done

lemma rev_predicate1D: "P x ==> P <= Q ==> Q x"
  by (rule predicate1D)

lemma rev_predicate2D: "P x y ==> P <= Q ==> Q x y"
  by (rule predicate2D)


subsection {* Monotonicity, least value operator and min/max *}

context order
begin

definition
  mono :: "('a \<Rightarrow> 'b\<Colon>order) \<Rightarrow> bool"
where
  "mono f \<longleftrightarrow> (\<forall>x y. x \<le> y \<longrightarrow> f x \<le> f y)"

lemma monoI [intro?]:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>order"
  shows "(\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y) \<Longrightarrow> mono f"
  unfolding mono_def by iprover

lemma monoD [dest?]:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>order"
  shows "mono f \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  unfolding mono_def by iprover

end

context linorder
begin

lemma min_of_mono:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>linorder"
  shows "mono f \<Longrightarrow> min (f m) (f n) = f (min m n)"
  by (auto simp: mono_def Orderings.min_def min_def intro: Orderings.antisym)

lemma max_of_mono:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>linorder"
  shows "mono f \<Longrightarrow> max (f m) (f n) = f (max m n)"
  by (auto simp: mono_def Orderings.max_def max_def intro: Orderings.antisym)

end

lemma LeastI2_order:
  "[| P (x::'a::order);
      !!y. P y ==> x <= y;
      !!x. [| P x; ALL y. P y --> x \<le> y |] ==> Q x |]
   ==> Q (Least P)"
apply (unfold Least_def)
apply (rule theI2)
  apply (blast intro: order_antisym)+
done

lemma min_leastL: "(!!x. least <= x) ==> min least x = least"
by (simp add: min_def)

lemma max_leastL: "(!!x. least <= x) ==> max least x = x"
by (simp add: max_def)

lemma min_leastR: "(\<And>x\<Colon>'a\<Colon>order. least \<le> x) \<Longrightarrow> min x least = least"
apply (simp add: min_def)
apply (blast intro: order_antisym)
done

lemma max_leastR: "(\<And>x\<Colon>'a\<Colon>order. least \<le> x) \<Longrightarrow> max x least = x"
apply (simp add: max_def)
apply (blast intro: order_antisym)
done

end
