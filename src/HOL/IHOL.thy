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


subsection {* Fundamental rules *}

subsubsection {* Equality *}

lemma sym: "s = t ==> t = s"
  by (erule subst) (rule refl)

lemma ssubst: "t = s ==> P s ==> P t"
  by (drule sym) (erule subst)

lemma trans: "[| r=s; s=t |] ==> r=t"
  by (erule subst)

lemma trans_sym [Pure.elim?]: "r = s ==> t = s ==> r = t"
  by (rule trans [OF _ sym])

lemma meta_eq_to_obj_eq: 
  assumes meq: "A == B"
  shows "A = B"
  by (unfold meq) (rule refl)

text {* Useful with @{text erule} for proving equalities from known equalities. *}
     (* a = b
        |   |
        c = d   *)
lemma box_equals: "[| a=b;  a=c;  b=d |] ==> c=d"
apply (rule trans)
apply (rule trans)
apply (rule sym)
apply assumption+
done

text {* For calculational reasoning: *}

lemma forw_subst: "a = b ==> P b ==> P a"
  by (rule ssubst)

lemma back_subst: "P a ==> a = b ==> P b"
  by (rule subst)


subsubsection {* Congruence rules for application *}

text {* Similar to @{text AP_THM} in Gordon's HOL. *}
lemma fun_cong: "(f::'a=>'b) = g ==> f(x)=g(x)"
apply (erule subst)
apply (rule refl)
done

text {* Similar to @{text AP_TERM} in Gordon's HOL and FOL's @{text subst_context}. *}
lemma arg_cong: "x=y ==> f(x)=f(y)"
apply (erule subst)
apply (rule refl)
done

lemma arg_cong2: "\<lbrakk> a = b; c = d \<rbrakk> \<Longrightarrow> f a c = f b d"
apply (erule ssubst)+
apply (rule refl)
done

lemma cong: "[| f = g; (x::'a) = y |] ==> f x = g y"
apply (erule subst)+
apply (rule refl)
done

ML {* val cong_tac = Cong_Tac.cong_tac @{thm cong} *}


subsubsection {* Equality of booleans -- iff *}

lemma iffI: assumes "P ==> Q" and "Q ==> P" shows "P=Q"
  by (iprover intro: iff [THEN mp, THEN mp] impI assms)

lemma iffD2: "[| P=Q; Q |] ==> P"
  by (erule ssubst)

lemma rev_iffD2: "[| Q; P=Q |] ==> P"
  by (erule iffD2)

lemma iffD1: "Q = P \<Longrightarrow> Q \<Longrightarrow> P"
  by (drule sym) (rule iffD2)

lemma rev_iffD1: "Q \<Longrightarrow> Q = P \<Longrightarrow> P"
  by (drule sym) (rule rev_iffD2)

lemma iffE:
  assumes major: "P=Q"
    and minor: "[| P --> Q; Q --> P |] ==> R"
  shows R
  by (iprover intro: minor impI major [THEN iffD2] major [THEN iffD1])


subsubsection {*True*}

lemma TrueI: "True"
  unfolding True_def by (rule refl)

lemma eqTrueI: "P ==> P = True"
  by (iprover intro: iffI TrueI)

lemma eqTrueE: "P = True ==> P"
  by (erule iffD2) (rule TrueI)


subsubsection {*Universal quantifier*}

lemma allI: assumes "!!x::'a. P(x)" shows "ALL x. P(x)"
  unfolding All_def by (iprover intro: ext eqTrueI assms)

lemma spec: "ALL x::'a. P(x) ==> P(x)"
apply (unfold All_def)
apply (rule eqTrueE)
apply (erule fun_cong)
done

lemma allE:
  assumes major: "ALL x. P(x)"
    and minor: "P(x) ==> R"
  shows R
  by (iprover intro: minor major [THEN spec])

lemma all_dupE:
  assumes major: "ALL x. P(x)"
    and minor: "[| P(x); ALL x. P(x) |] ==> R"
  shows R
  by (iprover intro: minor major major [THEN spec])


subsubsection {* False *}

text {*
  Depends upon @{text spec}; it is impossible to do propositional
  logic before quantifiers!
*}

lemma FalseE: "False ==> P"
  apply (unfold False_def)
  apply (erule spec)
  done

lemma False_neq_True: "False = True ==> P"
  by (erule eqTrueE [THEN FalseE])


subsubsection {* Negation *}

lemma notI:
  assumes "P ==> False"
  shows "~P"
  apply (unfold not_def)
  apply (iprover intro: impI assms)
  done

lemma False_not_True: "False ~= True"
  apply (rule notI)
  apply (erule False_neq_True)
  done

lemma True_not_False: "True ~= False"
  apply (rule notI)
  apply (drule sym)
  apply (erule False_neq_True)
  done

lemma notE: "[| ~P;  P |] ==> R"
  apply (unfold not_def)
  apply (erule mp [THEN FalseE])
  apply assumption
  done

lemma notI2: "(P \<Longrightarrow> \<not> Pa) \<Longrightarrow> (P \<Longrightarrow> Pa) \<Longrightarrow> \<not> P"
  by (erule notE [THEN notI]) (erule meta_mp)


subsubsection {*Implication*}

lemma impE:
  assumes "P-->Q" "P" "Q ==> R"
  shows "R"
by (iprover intro: assms mp)

(* Reduces Q to P-->Q, allowing substitution in P. *)
lemma rev_mp: "[| P;  P --> Q |] ==> Q"
by (iprover intro: mp)

lemma contrapos_nn:
  assumes major: "~Q"
      and minor: "P==>Q"
  shows "~P"
by (iprover intro: notI minor major [THEN notE])

(*not used at all, but we already have the other 3 combinations *)
lemma contrapos_pn:
  assumes major: "Q"
      and minor: "P ==> ~Q"
  shows "~P"
by (iprover intro: notI minor major notE)

lemma not_sym: "t ~= s ==> s ~= t"
  by (erule contrapos_nn) (erule sym)

lemma eq_neq_eq_imp_neq: "[| x = a ; a ~= b; b = y |] ==> x ~= y"
  by (erule subst, erule ssubst, assumption)


subsubsection {*Existential quantifier*}

lemma exI: "P x ==> EX x::'a. P x"
apply (unfold Ex_def)
apply (iprover intro: allI allE impI mp)
done

lemma exE:
  assumes major: "EX x::'a. P(x)"
      and minor: "!!x. P(x) ==> Q"
  shows "Q"
apply (rule major [unfolded Ex_def, THEN spec, THEN mp])
apply (iprover intro: impI [THEN allI] minor)
done


subsubsection {*Conjunction*}

lemma conjI: "[| P; Q |] ==> P&Q"
apply (unfold and_def)
apply (iprover intro: impI [THEN allI] mp)
done

lemma conjunct1: "[| P & Q |] ==> P"
apply (unfold and_def)
apply (iprover intro: impI dest: spec mp)
done

lemma conjunct2: "[| P & Q |] ==> Q"
apply (unfold and_def)
apply (iprover intro: impI dest: spec mp)
done

lemma conjE:
  assumes major: "P&Q"
      and minor: "[| P; Q |] ==> R"
  shows "R"
apply (rule minor)
apply (rule major [THEN conjunct1])
apply (rule major [THEN conjunct2])
done

lemma context_conjI:
  assumes "P" "P ==> Q" shows "P & Q"
by (iprover intro: conjI assms)


subsubsection {*Disjunction*}

lemma disjI1: "P ==> P|Q"
apply (unfold or_def)
apply (iprover intro: allI impI mp)
done

lemma disjI2: "Q ==> P|Q"
apply (unfold or_def)
apply (iprover intro: allI impI mp)
done

lemma disjE:
  assumes major: "P|Q"
      and minorP: "P ==> R"
      and minorQ: "Q ==> R"
  shows "R"
by (iprover intro: minorP minorQ impI
                 major [unfolded or_def, THEN spec, THEN mp, THEN mp])


end
