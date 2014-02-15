(*  Title:      HOL/IHOL.thy
    Author:     Tobias Nipkow, Markus Wenzel, and Larry Paulson
*)

header {* The basis of Higher-Order Logic *}

theory IHOL
imports Pure "~~/src/Tools/Code_Generator"
keywords
  "try" "solve_direct" "quickcheck" "print_coercions" "print_claset"
    "print_induct_rules" :: diag and
  "quickcheck_params" :: thy_decl
begin

ML_file "~~/src/Tools/misc_legacy.ML"
ML_file "~~/src/Tools/try.ML"
ML_file "~~/src/Tools/quickcheck.ML"
ML_file "~~/src/Tools/solve_direct.ML"
ML_file "~~/src/Tools/IsaPlanner/zipper.ML"
ML_file "~~/src/Tools/IsaPlanner/isand.ML"
ML_file "~~/src/Tools/IsaPlanner/rw_inst.ML"
ML_file "~~/src/Provers/hypsubst.ML"
ML_file "~~/src/Provers/splitter.ML"
ML_file "~~/src/Provers/classical.ML"
ML_file "~~/src/Provers/blast.ML"
ML_file "~~/src/Provers/clasimp.ML"
ML_file "~~/src/Tools/coherent.ML"
ML_file "~~/src/Tools/eqsubst.ML"
ML_file "~~/src/Provers/quantifier1.ML"
ML_file "~~/src/Tools/atomize_elim.ML"
ML_file "~~/src/Tools/induct.ML"
ML_file "~~/src/Tools/cong_tac.ML"
ML_file "~~/src/Tools/intuitionistic.ML"
ML_file "~~/src/Tools/project_rule.ML"
ML_file "~~/src/Tools/subtyping.ML"
ML_file "~~/src/Tools/case_product.ML"

setup {*
  Intuitionistic.method_setup @{binding iprover}
  #> Subtyping.setup
  #> Case_Product.setup
*}

subsection {* Primitive logic *}

subsubsection {* Core syntax *}

setup {* Axclass.axiomatize_class (@{binding type}, []) *}
default_sort type
setup {* Object_Logic.add_base_sort @{sort type} *}

axiomatization where fun_arity: "OFCLASS('a \<Rightarrow> 'b, type_class)"
instance "fun" :: (type, type) type by (rule fun_arity)

axiomatization where itself_arity: "OFCLASS('a itself, type_class)"
instance itself :: (type) type by (rule itself_arity)

typedecl bool

judgment
  Trueprop      :: "bool => prop"                   ("(_)" 5)

axiomatization
  implies       :: "[bool, bool] => bool"           (infixr "-->" 25)  and
  eq            :: "['a, 'a] => bool"               (infixl "=" 50)  and
  The           :: "('a => bool) => 'a"

consts
  True          :: bool
  False         :: bool
  Not           :: "bool => bool"                   ("~ _" [40] 40)

  conj          :: "[bool, bool] => bool"           (infixr "&" 35)
  disj          :: "[bool, bool] => bool"           (infixr "|" 30)

  All           :: "('a => bool) => bool"           (binder "ALL " 10)
  Ex            :: "('a => bool) => bool"           (binder "EX " 10)
  Ex1           :: "('a => bool) => bool"           (binder "EX! " 10)


subsubsection {* Additional concrete syntax *}

notation (output)
  eq  (infix "=" 50)

abbreviation
  not_equal :: "['a, 'a] => bool"  (infixl "~=" 50) where
  "x ~= y == ~ (x = y)"

notation (output)
  not_equal  (infix "~=" 50)

notation (xsymbols)
  Not  ("\<not> _" [40] 40) and
  conj  (infixr "\<and>" 35) and
  disj  (infixr "\<or>" 30) and
  implies  (infixr "\<longrightarrow>" 25) and
  not_equal  (infixl "\<noteq>" 50)

notation (xsymbols output)
  not_equal  (infix "\<noteq>" 50)

notation (HTML output)
  Not  ("\<not> _" [40] 40) and
  conj  (infixr "\<and>" 35) and
  disj  (infixr "\<or>" 30) and
  not_equal  (infix "\<noteq>" 50)

abbreviation (iff)
  iff :: "[bool, bool] => bool"  (infixr "<->" 25) where
  "A <-> B == A = B"

notation (xsymbols)
  iff  (infixr "\<longleftrightarrow>" 25)

syntax "_The" :: "[pttrn, bool] => 'a"  ("(3THE _./ _)" [0, 10] 10)
translations "THE x. P" == "CONST The (%x. P)"
print_translation {*
  [(@{const_syntax The}, fn _ => fn [Abs abs] =>
      let val (x, t) = Syntax_Trans.atomic_abs_tr' abs
      in Syntax.const @{syntax_const "_The"} $ x $ t end)]
*}  -- {* To avoid eta-contraction of body *}

nonterminal letbinds and letbind
syntax
  "_bind"       :: "[pttrn, 'a] => letbind"              ("(2_ =/ _)" 10)
  ""            :: "letbind => letbinds"                 ("_")
  "_binds"      :: "[letbind, letbinds] => letbinds"     ("_;/ _")
  "_Let"        :: "[letbinds, 'a] => 'a"                ("(let (_)/ in (_))" [0, 10] 10)

nonterminal case_syn and cases_syn
syntax
  "_case_syntax" :: "['a, cases_syn] => 'b"  ("(case _ of/ _)" 10)
  "_case1" :: "['a, 'b] => case_syn"  ("(2_ =>/ _)" 10)
  "" :: "case_syn => cases_syn"  ("_")
  "_case2" :: "[case_syn, cases_syn] => cases_syn"  ("_/ | _")
syntax (xsymbols)
  "_case1" :: "['a, 'b] => case_syn"  ("(2_ \<Rightarrow>/ _)" 10)

notation (xsymbols)
  All  (binder "\<forall>" 10) and
  Ex  (binder "\<exists>" 10) and
  Ex1  (binder "\<exists>!" 10)

notation (HTML output)
  All  (binder "\<forall>" 10) and
  Ex  (binder "\<exists>" 10) and
  Ex1  (binder "\<exists>!" 10)

notation (HOL)
  All  (binder "! " 10) and
  Ex  (binder "? " 10) and
  Ex1  (binder "?! " 10)


subsubsection {* Axioms and basic definitions *}

axiomatization where
  refl: "t = (t::'a)" and
  subst: "s = t \<Longrightarrow> P s \<Longrightarrow> P t" and
  ext: "(!!x::'a. (f x ::'b) = g x) ==> (%x. f x) = (%x. g x)"
    -- {*Extensionality is built into the meta-logic, and this rule expresses
         a related property.  It is an eta-expanded version of the traditional
         rule, and similar to the ABS rule of HOL*} and

  the_eq_trivial: "(THE x. x = a) = (a::'a)"

axiomatization where
  impI: "(P ==> Q) ==> P-->Q" and
  mp: "[| P-->Q;  P |] ==> Q" and
  iff: "(P-->Q) --> (Q-->P) --> (P=Q)"


defs
  True_def:     "True      == ((%x::bool. x) = (%x. x))"
  All_def:      "All(P)    == (P = (%x. True))"
  Ex_def:       "Ex(P)     == !Q. (!x. P x --> Q) --> Q"
  False_def:    "False     == (!P. P)"
  not_def:      "~ P       == P-->False"
  and_def:      "P & Q     == !R. (P-->Q-->R) --> R"
  or_def:       "P | Q     == !R. (P-->R) --> (Q-->R) --> R"
  Ex1_def:      "Ex1(P)    == ? x. P(x) & (! y. P(y) --> y=x)"


definition If :: "bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("(if (_)/ then (_)/ else (_))" [0, 0, 10] 10)
  where "If P x y \<equiv> (THE z::'a. (P=True --> z=x) & (P=False --> z=y))"

definition Let :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b"
  where "Let s f \<equiv> f s"

translations
  "_Let (_binds b bs) e"  == "_Let b (_Let bs e)"
  "let x = a in e"        == "CONST Let a (%x. e)"

axiomatization undefined :: 'a

class default = fixes default :: 'a

end
