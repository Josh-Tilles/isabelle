(*  Title:      HOL/Inductive.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

header {* Knaster-Tarski Fixpoint Theorem and inductive definitions *}

theory Inductive 
imports Lattices Sum_Type
uses
  ("Tools/inductive_package.ML")
  "Tools/dseq.ML"
  ("Tools/inductive_codegen.ML")
  ("Tools/datatype_aux.ML")
  ("Tools/datatype_prop.ML")
  ("Tools/datatype_rep_proofs.ML")
  ("Tools/datatype_abs_proofs.ML")
  ("Tools/datatype_case.ML")
  ("Tools/datatype_package.ML")
  ("Tools/primrec_package.ML")
  ("Tools/datatype_codegen.ML")
begin

subsection {* Least and greatest fixed points *}

definition
  lfp :: "('a\<Colon>complete_lattice \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "lfp f = Inf {u. f u \<le> u}"    --{*least fixed point*}

definition
  gfp :: "('a\<Colon>complete_lattice \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "gfp f = Sup {u. u \<le> f u}"    --{*greatest fixed point*}


subsection{* Proof of Knaster-Tarski Theorem using @{term lfp} *}

text{*@{term "lfp f"} is the least upper bound of 
      the set @{term "{u. f(u) \<le> u}"} *}

lemma lfp_lowerbound: "f A \<le> A ==> lfp f \<le> A"
  by (auto simp add: lfp_def intro: Inf_lower)

lemma lfp_greatest: "(!!u. f u \<le> u ==> A \<le> u) ==> A \<le> lfp f"
  by (auto simp add: lfp_def intro: Inf_greatest)

lemma lfp_lemma2: "mono f ==> f (lfp f) \<le> lfp f"
  by (iprover intro: lfp_greatest order_trans monoD lfp_lowerbound)

lemma lfp_lemma3: "mono f ==> lfp f \<le> f (lfp f)"
  by (iprover intro: lfp_lemma2 monoD lfp_lowerbound)

lemma lfp_unfold: "mono f ==> lfp f = f (lfp f)"
  by (iprover intro: order_antisym lfp_lemma2 lfp_lemma3)

lemma lfp_const: "lfp (\<lambda>x. t) = t"
  by (rule lfp_unfold) (simp add:mono_def)


subsection {* General induction rules for least fixed points *}

theorem lfp_induct:
  assumes mono: "mono f" and ind: "f (inf (lfp f) P) <= P"
  shows "lfp f <= P"
proof -
  have "inf (lfp f) P <= lfp f" by (rule inf_le1)
  with mono have "f (inf (lfp f) P) <= f (lfp f)" ..
  also from mono have "f (lfp f) = lfp f" by (rule lfp_unfold [symmetric])
  finally have "f (inf (lfp f) P) <= lfp f" .
  from this and ind have "f (inf (lfp f) P) <= inf (lfp f) P" by (rule le_infI)
  hence "lfp f <= inf (lfp f) P" by (rule lfp_lowerbound)
  also have "inf (lfp f) P <= P" by (rule inf_le2)
  finally show ?thesis .
qed

lemma lfp_induct_set:
  assumes lfp: "a: lfp(f)"
      and mono: "mono(f)"
      and indhyp: "!!x. [| x: f(lfp(f) Int {x. P(x)}) |] ==> P(x)"
  shows "P(a)"
  by (rule lfp_induct [THEN subsetD, THEN CollectD, OF mono _ lfp])
    (auto simp: inf_set_eq intro: indhyp)

lemma lfp_ordinal_induct: 
  assumes mono: "mono f"
  and P_f: "!!S. P S ==> P(f S)"
  and P_Union: "!!M. !S:M. P S ==> P(Union M)"
  shows "P(lfp f)"
proof -
  let ?M = "{S. S \<subseteq> lfp f & P S}"
  have "P (Union ?M)" using P_Union by simp
  also have "Union ?M = lfp f"
  proof
    show "Union ?M \<subseteq> lfp f" by blast
    hence "f (Union ?M) \<subseteq> f (lfp f)" by (rule mono [THEN monoD])
    hence "f (Union ?M) \<subseteq> lfp f" using mono [THEN lfp_unfold] by simp
    hence "f (Union ?M) \<in> ?M" using P_f P_Union by simp
    hence "f (Union ?M) \<subseteq> Union ?M" by (rule Union_upper)
    thus "lfp f \<subseteq> Union ?M" by (rule lfp_lowerbound)
  qed
  finally show ?thesis .
qed


text{*Definition forms of @{text lfp_unfold} and @{text lfp_induct}, 
    to control unfolding*}

lemma def_lfp_unfold: "[| h==lfp(f);  mono(f) |] ==> h = f(h)"
by (auto intro!: lfp_unfold)

lemma def_lfp_induct: 
    "[| A == lfp(f); mono(f);
        f (inf A P) \<le> P
     |] ==> A \<le> P"
  by (blast intro: lfp_induct)

lemma def_lfp_induct_set: 
    "[| A == lfp(f);  mono(f);   a:A;                    
        !!x. [| x: f(A Int {x. P(x)}) |] ==> P(x)         
     |] ==> P(a)"
  by (blast intro: lfp_induct_set)

(*Monotonicity of lfp!*)
lemma lfp_mono: "(!!Z. f Z \<le> g Z) ==> lfp f \<le> lfp g"
  by (rule lfp_lowerbound [THEN lfp_greatest], blast intro: order_trans)


subsection {* Proof of Knaster-Tarski Theorem using @{term gfp} *}

text{*@{term "gfp f"} is the greatest lower bound of 
      the set @{term "{u. u \<le> f(u)}"} *}

lemma gfp_upperbound: "X \<le> f X ==> X \<le> gfp f"
  by (auto simp add: gfp_def intro: Sup_upper)

lemma gfp_least: "(!!u. u \<le> f u ==> u \<le> X) ==> gfp f \<le> X"
  by (auto simp add: gfp_def intro: Sup_least)

lemma gfp_lemma2: "mono f ==> gfp f \<le> f (gfp f)"
  by (iprover intro: gfp_least order_trans monoD gfp_upperbound)

lemma gfp_lemma3: "mono f ==> f (gfp f) \<le> gfp f"
  by (iprover intro: gfp_lemma2 monoD gfp_upperbound)

lemma gfp_unfold: "mono f ==> gfp f = f (gfp f)"
  by (iprover intro: order_antisym gfp_lemma2 gfp_lemma3)


subsection {* Coinduction rules for greatest fixed points *}

text{*weak version*}
lemma weak_coinduct: "[| a: X;  X \<subseteq> f(X) |] ==> a : gfp(f)"
by (rule gfp_upperbound [THEN subsetD], auto)

lemma weak_coinduct_image: "!!X. [| a : X; g`X \<subseteq> f (g`X) |] ==> g a : gfp f"
apply (erule gfp_upperbound [THEN subsetD])
apply (erule imageI)
done

lemma coinduct_lemma:
     "[| X \<le> f (sup X (gfp f));  mono f |] ==> sup X (gfp f) \<le> f (sup X (gfp f))"
  apply (frule gfp_lemma2)
  apply (drule mono_sup)
  apply (rule le_supI)
  apply assumption
  apply (rule order_trans)
  apply (rule order_trans)
  apply assumption
  apply (rule sup_ge2)
  apply assumption
  done

text{*strong version, thanks to Coen and Frost*}
lemma coinduct_set: "[| mono(f);  a: X;  X \<subseteq> f(X Un gfp(f)) |] ==> a : gfp(f)"
by (blast intro: weak_coinduct [OF _ coinduct_lemma, simplified sup_set_eq])

lemma coinduct: "[| mono(f); X \<le> f (sup X (gfp f)) |] ==> X \<le> gfp(f)"
  apply (rule order_trans)
  apply (rule sup_ge1)
  apply (erule gfp_upperbound [OF coinduct_lemma])
  apply assumption
  done

lemma gfp_fun_UnI2: "[| mono(f);  a: gfp(f) |] ==> a: f(X Un gfp(f))"
by (blast dest: gfp_lemma2 mono_Un)


subsection {* Even Stronger Coinduction Rule, by Martin Coen *}

text{* Weakens the condition @{term "X \<subseteq> f(X)"} to one expressed using both
  @{term lfp} and @{term gfp}*}

lemma coinduct3_mono_lemma: "mono(f) ==> mono(%x. f(x) Un X Un B)"
by (iprover intro: subset_refl monoI Un_mono monoD)

lemma coinduct3_lemma:
     "[| X \<subseteq> f(lfp(%x. f(x) Un X Un gfp(f)));  mono(f) |]
      ==> lfp(%x. f(x) Un X Un gfp(f)) \<subseteq> f(lfp(%x. f(x) Un X Un gfp(f)))"
apply (rule subset_trans)
apply (erule coinduct3_mono_lemma [THEN lfp_lemma3])
apply (rule Un_least [THEN Un_least])
apply (rule subset_refl, assumption)
apply (rule gfp_unfold [THEN equalityD1, THEN subset_trans], assumption)
apply (rule monoD, assumption)
apply (subst coinduct3_mono_lemma [THEN lfp_unfold], auto)
done

lemma coinduct3: 
  "[| mono(f);  a:X;  X \<subseteq> f(lfp(%x. f(x) Un X Un gfp(f))) |] ==> a : gfp(f)"
apply (rule coinduct3_lemma [THEN [2] weak_coinduct])
apply (rule coinduct3_mono_lemma [THEN lfp_unfold, THEN ssubst], auto)
done


text{*Definition forms of @{text gfp_unfold} and @{text coinduct}, 
    to control unfolding*}

lemma def_gfp_unfold: "[| A==gfp(f);  mono(f) |] ==> A = f(A)"
by (auto intro!: gfp_unfold)

lemma def_coinduct:
     "[| A==gfp(f);  mono(f);  X \<le> f(sup X A) |] ==> X \<le> A"
by (iprover intro!: coinduct)

lemma def_coinduct_set:
     "[| A==gfp(f);  mono(f);  a:X;  X \<subseteq> f(X Un A) |] ==> a: A"
by (auto intro!: coinduct_set)

(*The version used in the induction/coinduction package*)
lemma def_Collect_coinduct:
    "[| A == gfp(%w. Collect(P(w)));  mono(%w. Collect(P(w)));   
        a: X;  !!z. z: X ==> P (X Un A) z |] ==>  
     a : A"
apply (erule def_coinduct_set, auto) 
done

lemma def_coinduct3:
    "[| A==gfp(f); mono(f);  a:X;  X \<subseteq> f(lfp(%x. f(x) Un X Un A)) |] ==> a: A"
by (auto intro!: coinduct3)

text{*Monotonicity of @{term gfp}!*}
lemma gfp_mono: "(!!Z. f Z \<le> g Z) ==> gfp f \<le> gfp g"
  by (rule gfp_upperbound [THEN gfp_least], blast intro: order_trans)


subsection {* Inductive predicates and sets *}

text {* Inversion of injective functions. *}

constdefs
  myinv :: "('a => 'b) => ('b => 'a)"
  "myinv (f :: 'a => 'b) == \<lambda>y. THE x. f x = y"

lemma myinv_f_f: "inj f ==> myinv f (f x) = x"
proof -
  assume "inj f"
  hence "(THE x'. f x' = f x) = (THE x'. x' = x)"
    by (simp only: inj_eq)
  also have "... = x" by (rule the_eq_trivial)
  finally show ?thesis by (unfold myinv_def)
qed

lemma f_myinv_f: "inj f ==> y \<in> range f ==> f (myinv f y) = y"
proof (unfold myinv_def)
  assume inj: "inj f"
  assume "y \<in> range f"
  then obtain x where "y = f x" ..
  hence x: "f x = y" ..
  thus "f (THE x. f x = y) = y"
  proof (rule theI)
    fix x' assume "f x' = y"
    with x have "f x' = f x" by simp
    with inj show "x' = x" by (rule injD)
  qed
qed

hide const myinv


text {* Package setup. *}

theorems basic_monos =
  subset_refl imp_refl disj_mono conj_mono ex_mono all_mono if_bool_eq_conj
  Collect_mono in_mono vimage_mono
  imp_conv_disj not_not de_Morgan_disj de_Morgan_conj
  not_all not_ex
  Ball_def Bex_def
  induct_rulify_fallback

ML {*
val def_lfp_unfold = @{thm def_lfp_unfold}
val def_gfp_unfold = @{thm def_gfp_unfold}
val def_lfp_induct = @{thm def_lfp_induct}
val def_coinduct = @{thm def_coinduct}
val inf_bool_eq = @{thm inf_bool_eq} RS @{thm eq_reflection}
val inf_fun_eq = @{thm inf_fun_eq} RS @{thm eq_reflection}
val sup_bool_eq = @{thm sup_bool_eq} RS @{thm eq_reflection}
val sup_fun_eq = @{thm sup_fun_eq} RS @{thm eq_reflection}
val le_boolI = @{thm le_boolI}
val le_boolI' = @{thm le_boolI'}
val le_funI = @{thm le_funI}
val le_boolE = @{thm le_boolE}
val le_funE = @{thm le_funE}
val le_boolD = @{thm le_boolD}
val le_funD = @{thm le_funD}
val le_bool_def = @{thm le_bool_def} RS @{thm eq_reflection}
val le_fun_def = @{thm le_fun_def} RS @{thm eq_reflection}
*}

use "Tools/inductive_package.ML"
setup InductivePackage.setup

theorems [mono] =
  imp_refl disj_mono conj_mono ex_mono all_mono if_bool_eq_conj
  imp_conv_disj not_not de_Morgan_disj de_Morgan_conj
  not_all not_ex
  Ball_def Bex_def
  induct_rulify_fallback


subsection {* Inductive datatypes and primitive recursion *}

text {* Package setup. *}

use "Tools/datatype_aux.ML"
use "Tools/datatype_prop.ML"
use "Tools/datatype_rep_proofs.ML"
use "Tools/datatype_abs_proofs.ML"
use "Tools/datatype_case.ML"
use "Tools/datatype_package.ML"
setup DatatypePackage.setup
use "Tools/primrec_package.ML"

use "Tools/datatype_codegen.ML"
setup DatatypeCodegen.setup

use "Tools/inductive_codegen.ML"
setup InductiveCodegen.setup

text{* Lambda-abstractions with pattern matching: *}

syntax
  "_lam_pats_syntax" :: "cases_syn => 'a => 'b"               ("(%_)" 10)
syntax (xsymbols)
  "_lam_pats_syntax" :: "cases_syn => 'a => 'b"               ("(\<lambda>_)" 10)

parse_translation (advanced) {*
let
  fun fun_tr ctxt [cs] =
    let
      val x = Free (Name.variant (add_term_free_names (cs, [])) "x", dummyT);
      val ft = DatatypeCase.case_tr true DatatypePackage.datatype_of_constr
                 ctxt [x, cs]
    in lambda x ft end
in [("_lam_pats_syntax", fun_tr)] end
*}

end
