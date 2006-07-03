(*  ID:         $Id$
    Authors:    Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

header {* Equivalence Relations in Higher-Order Set Theory *}

theory Equiv_Relations
imports Relation Finite_Set
begin

subsection {* Equivalence relations *}

locale equiv =
  fixes A and r
  assumes refl: "refl A r"
    and sym: "sym r"
    and trans: "trans r"

text {*
  Suppes, Theorem 70: @{text r} is an equiv relation iff @{text "r\<inverse> O
  r = r"}.

  First half: @{text "equiv A r ==> r\<inverse> O r = r"}.
*}

lemma sym_trans_comp_subset:
    "sym r ==> trans r ==> r\<inverse> O r \<subseteq> r"
  by (unfold trans_def sym_def converse_def) blast

lemma refl_comp_subset: "refl A r ==> r \<subseteq> r\<inverse> O r"
  by (unfold refl_def) blast

lemma equiv_comp_eq: "equiv A r ==> r\<inverse> O r = r"
  apply (unfold equiv_def)
  apply clarify
  apply (rule equalityI)
   apply (iprover intro: sym_trans_comp_subset refl_comp_subset)+
  done

text {* Second half. *}

lemma comp_equivI:
    "r\<inverse> O r = r ==> Domain r = A ==> equiv A r"
  apply (unfold equiv_def refl_def sym_def trans_def)
  apply (erule equalityE)
  apply (subgoal_tac "\<forall>x y. (x, y) \<in> r --> (y, x) \<in> r")
   apply fast
  apply fast
  done


subsection {* Equivalence classes *}

lemma equiv_class_subset:
  "equiv A r ==> (a, b) \<in> r ==> r``{a} \<subseteq> r``{b}"
  -- {* lemma for the next result *}
  by (unfold equiv_def trans_def sym_def) blast

theorem equiv_class_eq: "equiv A r ==> (a, b) \<in> r ==> r``{a} = r``{b}"
  apply (assumption | rule equalityI equiv_class_subset)+
  apply (unfold equiv_def sym_def)
  apply blast
  done

lemma equiv_class_self: "equiv A r ==> a \<in> A ==> a \<in> r``{a}"
  by (unfold equiv_def refl_def) blast

lemma subset_equiv_class:
    "equiv A r ==> r``{b} \<subseteq> r``{a} ==> b \<in> A ==> (a,b) \<in> r"
  -- {* lemma for the next result *}
  by (unfold equiv_def refl_def) blast

lemma eq_equiv_class:
    "r``{a} = r``{b} ==> equiv A r ==> b \<in> A ==> (a, b) \<in> r"
  by (iprover intro: equalityD2 subset_equiv_class)

lemma equiv_class_nondisjoint:
    "equiv A r ==> x \<in> (r``{a} \<inter> r``{b}) ==> (a, b) \<in> r"
  by (unfold equiv_def trans_def sym_def) blast

lemma equiv_type: "equiv A r ==> r \<subseteq> A \<times> A"
  by (unfold equiv_def refl_def) blast

theorem equiv_class_eq_iff:
  "equiv A r ==> ((x, y) \<in> r) = (r``{x} = r``{y} & x \<in> A & y \<in> A)"
  by (blast intro!: equiv_class_eq dest: eq_equiv_class equiv_type)

theorem eq_equiv_class_iff:
  "equiv A r ==> x \<in> A ==> y \<in> A ==> (r``{x} = r``{y}) = ((x, y) \<in> r)"
  by (blast intro!: equiv_class_eq dest: eq_equiv_class equiv_type)


subsection {* Quotients *}

constdefs
  quotient :: "['a set, ('a*'a) set] => 'a set set"  (infixl "'/'/" 90)
  "A//r == \<Union>x \<in> A. {r``{x}}"  -- {* set of equiv classes *}

lemma quotientI: "x \<in> A ==> r``{x} \<in> A//r"
  by (unfold quotient_def) blast

lemma quotientE:
  "X \<in> A//r ==> (!!x. X = r``{x} ==> x \<in> A ==> P) ==> P"
  by (unfold quotient_def) blast

lemma Union_quotient: "equiv A r ==> Union (A//r) = A"
  by (unfold equiv_def refl_def quotient_def) blast

lemma quotient_disj:
  "equiv A r ==> X \<in> A//r ==> Y \<in> A//r ==> X = Y | (X \<inter> Y = {})"
  apply (unfold quotient_def)
  apply clarify
  apply (rule equiv_class_eq)
   apply assumption
  apply (unfold equiv_def trans_def sym_def)
  apply blast
  done

lemma quotient_eqI:
  "[|equiv A r; X \<in> A//r; Y \<in> A//r; x \<in> X; y \<in> Y; (x,y) \<in> r|] ==> X = Y" 
  apply (clarify elim!: quotientE)
  apply (rule equiv_class_eq, assumption)
  apply (unfold equiv_def sym_def trans_def, blast)
  done

lemma quotient_eq_iff:
  "[|equiv A r; X \<in> A//r; Y \<in> A//r; x \<in> X; y \<in> Y|] ==> (X = Y) = ((x,y) \<in> r)" 
  apply (rule iffI)  
   prefer 2 apply (blast del: equalityI intro: quotient_eqI) 
  apply (clarify elim!: quotientE)
  apply (unfold equiv_def sym_def trans_def, blast)
  done

lemma eq_equiv_class_iff2:
  "\<lbrakk> equiv A r; x \<in> A; y \<in> A \<rbrakk> \<Longrightarrow> ({x}//r = {y}//r) = ((x,y) : r)"
by(simp add:quotient_def eq_equiv_class_iff)


lemma quotient_empty [simp]: "{}//r = {}"
by(simp add: quotient_def)

lemma quotient_is_empty [iff]: "(A//r = {}) = (A = {})"
by(simp add: quotient_def)

lemma quotient_is_empty2 [iff]: "({} = A//r) = (A = {})"
by(simp add: quotient_def)


lemma singleton_quotient: "{x}//r = {r `` {x}}"
by(simp add:quotient_def)

lemma quotient_diff1:
  "\<lbrakk> inj_on (%a. {a}//r) A; a \<in> A \<rbrakk> \<Longrightarrow> (A - {a})//r = A//r - {a}//r"
apply(simp add:quotient_def inj_on_def)
apply blast
done

subsection {* Defining unary operations upon equivalence classes *}

text{*A congruence-preserving function*}
locale congruent =
  fixes r and f
  assumes congruent: "(y,z) \<in> r ==> f y = f z"

abbreviation
  RESPECTS :: "('a => 'b) => ('a * 'a) set => bool"  (infixr "respects" 80)
  "f respects r == congruent r f"


lemma UN_constant_eq: "a \<in> A ==> \<forall>y \<in> A. f y = c ==> (\<Union>y \<in> A. f(y))=c"
  -- {* lemma required to prove @{text UN_equiv_class} *}
  by auto

lemma UN_equiv_class:
  "equiv A r ==> f respects r ==> a \<in> A
    ==> (\<Union>x \<in> r``{a}. f x) = f a"
  -- {* Conversion rule *}
  apply (rule equiv_class_self [THEN UN_constant_eq], assumption+)
  apply (unfold equiv_def congruent_def sym_def)
  apply (blast del: equalityI)
  done

lemma UN_equiv_class_type:
  "equiv A r ==> f respects r ==> X \<in> A//r ==>
    (!!x. x \<in> A ==> f x \<in> B) ==> (\<Union>x \<in> X. f x) \<in> B"
  apply (unfold quotient_def)
  apply clarify
  apply (subst UN_equiv_class)
     apply auto
  done

text {*
  Sufficient conditions for injectiveness.  Could weaken premises!
  major premise could be an inclusion; bcong could be @{text "!!y. y \<in>
  A ==> f y \<in> B"}.
*}

lemma UN_equiv_class_inject:
  "equiv A r ==> f respects r ==>
    (\<Union>x \<in> X. f x) = (\<Union>y \<in> Y. f y) ==> X \<in> A//r ==> Y \<in> A//r
    ==> (!!x y. x \<in> A ==> y \<in> A ==> f x = f y ==> (x, y) \<in> r)
    ==> X = Y"
  apply (unfold quotient_def)
  apply clarify
  apply (rule equiv_class_eq)
   apply assumption
  apply (subgoal_tac "f x = f xa")
   apply blast
  apply (erule box_equals)
   apply (assumption | rule UN_equiv_class)+
  done


subsection {* Defining binary operations upon equivalence classes *}

text{*A congruence-preserving function of two arguments*}
locale congruent2 =
  fixes r1 and r2 and f
  assumes congruent2:
    "(y1,z1) \<in> r1 ==> (y2,z2) \<in> r2 ==> f y1 y2 = f z1 z2"

text{*Abbreviation for the common case where the relations are identical*}
abbreviation
  RESPECTS2:: "['a => 'a => 'b, ('a * 'a)set] => bool" (infixr "respects2 " 80)
  "f respects2 r == congruent2 r r f"


lemma congruent2_implies_congruent:
    "equiv A r1 ==> congruent2 r1 r2 f ==> a \<in> A ==> congruent r2 (f a)"
  by (unfold congruent_def congruent2_def equiv_def refl_def) blast

lemma congruent2_implies_congruent_UN:
  "equiv A1 r1 ==> equiv A2 r2 ==> congruent2 r1 r2 f ==> a \<in> A2 ==>
    congruent r1 (\<lambda>x1. \<Union>x2 \<in> r2``{a}. f x1 x2)"
  apply (unfold congruent_def)
  apply clarify
  apply (rule equiv_type [THEN subsetD, THEN SigmaE2], assumption+)
  apply (simp add: UN_equiv_class congruent2_implies_congruent)
  apply (unfold congruent2_def equiv_def refl_def)
  apply (blast del: equalityI)
  done

lemma UN_equiv_class2:
  "equiv A1 r1 ==> equiv A2 r2 ==> congruent2 r1 r2 f ==> a1 \<in> A1 ==> a2 \<in> A2
    ==> (\<Union>x1 \<in> r1``{a1}. \<Union>x2 \<in> r2``{a2}. f x1 x2) = f a1 a2"
  by (simp add: UN_equiv_class congruent2_implies_congruent
    congruent2_implies_congruent_UN)

lemma UN_equiv_class_type2:
  "equiv A1 r1 ==> equiv A2 r2 ==> congruent2 r1 r2 f
    ==> X1 \<in> A1//r1 ==> X2 \<in> A2//r2
    ==> (!!x1 x2. x1 \<in> A1 ==> x2 \<in> A2 ==> f x1 x2 \<in> B)
    ==> (\<Union>x1 \<in> X1. \<Union>x2 \<in> X2. f x1 x2) \<in> B"
  apply (unfold quotient_def)
  apply clarify
  apply (blast intro: UN_equiv_class_type congruent2_implies_congruent_UN
    congruent2_implies_congruent quotientI)
  done

lemma UN_UN_split_split_eq:
  "(\<Union>(x1, x2) \<in> X. \<Union>(y1, y2) \<in> Y. A x1 x2 y1 y2) =
    (\<Union>x \<in> X. \<Union>y \<in> Y. (\<lambda>(x1, x2). (\<lambda>(y1, y2). A x1 x2 y1 y2) y) x)"
  -- {* Allows a natural expression of binary operators, *}
  -- {* without explicit calls to @{text split} *}
  by auto

lemma congruent2I:
  "equiv A1 r1 ==> equiv A2 r2
    ==> (!!y z w. w \<in> A2 ==> (y,z) \<in> r1 ==> f y w = f z w)
    ==> (!!y z w. w \<in> A1 ==> (y,z) \<in> r2 ==> f w y = f w z)
    ==> congruent2 r1 r2 f"
  -- {* Suggested by John Harrison -- the two subproofs may be *}
  -- {* \emph{much} simpler than the direct proof. *}
  apply (unfold congruent2_def equiv_def refl_def)
  apply clarify
  apply (blast intro: trans)
  done

lemma congruent2_commuteI:
  assumes equivA: "equiv A r"
    and commute: "!!y z. y \<in> A ==> z \<in> A ==> f y z = f z y"
    and congt: "!!y z w. w \<in> A ==> (y,z) \<in> r ==> f w y = f w z"
  shows "f respects2 r"
  apply (rule congruent2I [OF equivA equivA])
   apply (rule commute [THEN trans])
     apply (rule_tac [3] commute [THEN trans, symmetric])
       apply (rule_tac [5] sym)
       apply (assumption | rule congt |
         erule equivA [THEN equiv_type, THEN subsetD, THEN SigmaE2])+
  done


subsection {* Cardinality results *}

text {*Suggested by Florian Kamm�ller*}

lemma finite_quotient: "finite A ==> r \<subseteq> A \<times> A ==> finite (A//r)"
  -- {* recall @{thm equiv_type} *}
  apply (rule finite_subset)
   apply (erule_tac [2] finite_Pow_iff [THEN iffD2])
  apply (unfold quotient_def)
  apply blast
  done

lemma finite_equiv_class:
  "finite A ==> r \<subseteq> A \<times> A ==> X \<in> A//r ==> finite X"
  apply (unfold quotient_def)
  apply (rule finite_subset)
   prefer 2 apply assumption
  apply blast
  done

lemma equiv_imp_dvd_card:
  "finite A ==> equiv A r ==> \<forall>X \<in> A//r. k dvd card X
    ==> k dvd card A"
  apply (rule Union_quotient [THEN subst])
   apply assumption
  apply (rule dvd_partition)
     prefer 3 apply (blast dest: quotient_disj)
    apply (simp_all add: Union_quotient equiv_type)
  done

lemma card_quotient_disjoint:
 "\<lbrakk> finite A; inj_on (\<lambda>x. {x} // r) A \<rbrakk> \<Longrightarrow> card(A//r) = card A"
apply(simp add:quotient_def)
apply(subst card_UN_disjoint)
   apply assumption
  apply simp
 apply(fastsimp simp add:inj_on_def)
apply (simp add:setsum_constant)
done
(*
ML
{*
val UN_UN_split_split_eq = thm "UN_UN_split_split_eq";
val UN_constant_eq = thm "UN_constant_eq";
val UN_equiv_class = thm "UN_equiv_class";
val UN_equiv_class2 = thm "UN_equiv_class2";
val UN_equiv_class_inject = thm "UN_equiv_class_inject";
val UN_equiv_class_type = thm "UN_equiv_class_type";
val UN_equiv_class_type2 = thm "UN_equiv_class_type2";
val Union_quotient = thm "Union_quotient";
val comp_equivI = thm "comp_equivI";
val congruent2I = thm "congruent2I";
val congruent2_commuteI = thm "congruent2_commuteI";
val congruent2_def = thm "congruent2_def";
val congruent2_implies_congruent = thm "congruent2_implies_congruent";
val congruent2_implies_congruent_UN = thm "congruent2_implies_congruent_UN";
val congruent_def = thm "congruent_def";
val eq_equiv_class = thm "eq_equiv_class";
val eq_equiv_class_iff = thm "eq_equiv_class_iff";
val equiv_class_eq = thm "equiv_class_eq";
val equiv_class_eq_iff = thm "equiv_class_eq_iff";
val equiv_class_nondisjoint = thm "equiv_class_nondisjoint";
val equiv_class_self = thm "equiv_class_self";
val equiv_comp_eq = thm "equiv_comp_eq";
val equiv_def = thm "equiv_def";
val equiv_imp_dvd_card = thm "equiv_imp_dvd_card";
val equiv_type = thm "equiv_type";
val finite_equiv_class = thm "finite_equiv_class";
val finite_quotient = thm "finite_quotient";
val quotientE = thm "quotientE";
val quotientI = thm "quotientI";
val quotient_def = thm "quotient_def";
val quotient_disj = thm "quotient_disj";
val refl_comp_subset = thm "refl_comp_subset";
val subset_equiv_class = thm "subset_equiv_class";
val sym_trans_comp_subset = thm "sym_trans_comp_subset";
*}
*)
end
