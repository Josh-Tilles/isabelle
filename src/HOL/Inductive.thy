(*  Title:      HOL/Inductive.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Setup packages for inductive sets and types etc.
*)

theory Inductive = Gfp + Sum_Type + NatDef
files
  ("Tools/induct_method.ML")
  ("Tools/inductive_package.ML")
  ("Tools/datatype_aux.ML")
  ("Tools/datatype_prop.ML")
  ("Tools/datatype_rep_proofs.ML")
  ("Tools/datatype_abs_proofs.ML")
  ("Tools/datatype_package.ML")
  ("Tools/primrec_package.ML"):


(* handling of proper rules *)

constdefs
  forall :: "('a => bool) => bool"
  "forall P == \<forall>x. P x"
  implies :: "bool => bool => bool"
  "implies A B == A --> B"
  equal :: "'a => 'a => bool"
  "equal x y == x = y"
  conj :: "bool => bool => bool"
  "conj A B == A & B"

lemma forall_eq: "(!!x. P x) == Trueprop (forall (\<lambda>x. P x))"
  by (simp only: atomize_all forall_def)

lemma implies_eq: "(A ==> B) == Trueprop (implies A B)"
  by (simp only: atomize_imp implies_def)

lemma equal_eq: "(x == y) == Trueprop (equal x y)"
  by (simp only: atomize_eq equal_def)

lemma forall_conj: "forall (\<lambda>x. conj (A x) (B x)) = conj (forall A) (forall B)"
  by (unfold forall_def conj_def) blast

lemma implies_conj: "implies C (conj A B) = conj (implies C A) (implies C B)"
  by (unfold implies_def conj_def) blast

lemma conj_curry: "(conj A B ==> C) == (A ==> B ==> C)"
  by (simp only: atomize_imp atomize_eq conj_def) (rule equal_intr_rule, blast+)

lemmas inductive_atomize = forall_eq implies_eq equal_eq
lemmas inductive_rulify1 = inductive_atomize [symmetric, standard]
lemmas inductive_rulify2 = forall_def implies_def equal_def conj_def
lemmas inductive_conj = forall_conj implies_conj conj_curry

hide const forall implies equal conj


(* setup packages *)

use "Tools/induct_method.ML"
setup InductMethod.setup

use "Tools/inductive_package.ML"
setup InductivePackage.setup

use "Tools/datatype_aux.ML"
use "Tools/datatype_prop.ML"
use "Tools/datatype_rep_proofs.ML"
use "Tools/datatype_abs_proofs.ML"
use "Tools/datatype_package.ML"
setup DatatypePackage.setup

use "Tools/primrec_package.ML"
setup PrimrecPackage.setup

theorems basic_monos [mono] =
  subset_refl imp_refl disj_mono conj_mono ex_mono all_mono
  Collect_mono in_mono vimage_mono
  imp_conv_disj not_not de_Morgan_disj de_Morgan_conj
  not_all not_ex
  Ball_def Bex_def
  inductive_rulify2


(*belongs to theory Transitive_Closure*)
declare rtrancl_induct [induct set: rtrancl]
declare rtranclE [cases set: rtrancl]
declare trancl_induct [induct set: trancl]
declare tranclE [cases set: trancl]

end
