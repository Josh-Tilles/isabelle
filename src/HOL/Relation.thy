(*  Title:      HOL/Relation.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

header {* Relations *}

theory Relation
imports Product_Type
begin

subsection {* Definitions *}

definition
  converse :: "('a * 'b) set => ('b * 'a) set"
    ("(_^-1)" [1000] 999) where
  "r^-1 == {(y, x). (x, y) : r}"

notation (xsymbols)
  converse  ("(_\<inverse>)" [1000] 999)

definition
  rel_comp  :: "[('b * 'c) set, ('a * 'b) set] => ('a * 'c) set"
    (infixr "O" 75) where
  "r O s == {(x,z). EX y. (x, y) : s & (y, z) : r}"

definition
  Image :: "[('a * 'b) set, 'a set] => 'b set"
    (infixl "``" 90) where
  "r `` s == {y. EX x:s. (x,y):r}"

definition
  Id :: "('a * 'a) set" where -- {* the identity relation *}
  "Id == {p. EX x. p = (x,x)}"

definition
  diag  :: "'a set => ('a * 'a) set" where -- {* diagonal: identity over a set *}
  "diag A == \<Union>x\<in>A. {(x,x)}"

definition
  Domain :: "('a * 'b) set => 'a set" where
  "Domain r == {x. EX y. (x,y):r}"

definition
  Range  :: "('a * 'b) set => 'b set" where
  "Range r == Domain(r^-1)"

definition
  Field :: "('a * 'a) set => 'a set" where
  "Field r == Domain r \<union> Range r"

definition
  refl :: "['a set, ('a * 'a) set] => bool" where -- {* reflexivity over a set *}
  "refl A r == r \<subseteq> A \<times> A & (ALL x: A. (x,x) : r)"

definition
  sym :: "('a * 'a) set => bool" where -- {* symmetry predicate *}
  "sym r == ALL x y. (x,y): r --> (y,x): r"

definition
  antisym :: "('a * 'a) set => bool" where -- {* antisymmetry predicate *}
  "antisym r == ALL x y. (x,y):r --> (y,x):r --> x=y"

definition
  trans :: "('a * 'a) set => bool" where -- {* transitivity predicate *}
  "trans r == (ALL x y z. (x,y):r --> (y,z):r --> (x,z):r)"

definition
  single_valued :: "('a * 'b) set => bool" where
  "single_valued r == ALL x y. (x,y):r --> (ALL z. (x,z):r --> y=z)"

definition
  inv_image :: "('b * 'b) set => ('a => 'b) => ('a * 'a) set" where
  "inv_image r f == {(x, y). (f x, f y) : r}"

abbreviation
  reflexive :: "('a * 'a) set => bool" where -- {* reflexivity over a type *}
  "reflexive == refl UNIV"


subsection {* The identity relation *}

lemma IdI [intro]: "(a, a) : Id"
  by (simp add: Id_def)

lemma IdE [elim!]: "p : Id ==> (!!x. p = (x, x) ==> P) ==> P"
  by (unfold Id_def) (iprover elim: CollectE)

lemma pair_in_Id_conv [iff]: "((a, b) : Id) = (a = b)"
  by (unfold Id_def) blast

lemma reflexive_Id: "reflexive Id"
  by (simp add: refl_def)

lemma antisym_Id: "antisym Id"
  -- {* A strange result, since @{text Id} is also symmetric. *}
  by (simp add: antisym_def)

lemma sym_Id: "sym Id"
  by (simp add: sym_def)

lemma trans_Id: "trans Id"
  by (simp add: trans_def)


subsection {* Diagonal: identity over a set *}

lemma diag_empty [simp]: "diag {} = {}"
  by (simp add: diag_def) 

lemma diag_eqI: "a = b ==> a : A ==> (a, b) : diag A"
  by (simp add: diag_def)

lemma diagI [intro!,noatp]: "a : A ==> (a, a) : diag A"
  by (rule diag_eqI) (rule refl)

lemma diagE [elim!]:
  "c : diag A ==> (!!x. x : A ==> c = (x, x) ==> P) ==> P"
  -- {* The general elimination rule. *}
  by (unfold diag_def) (iprover elim!: UN_E singletonE)

lemma diag_iff: "((x, y) : diag A) = (x = y & x : A)"
  by blast

lemma diag_subset_Times: "diag A \<subseteq> A \<times> A"
  by blast


subsection {* Composition of two relations *}

lemma rel_compI [intro]:
  "(a, b) : s ==> (b, c) : r ==> (a, c) : r O s"
  by (unfold rel_comp_def) blast

lemma rel_compE [elim!]: "xz : r O s ==>
  (!!x y z. xz = (x, z) ==> (x, y) : s ==> (y, z) : r  ==> P) ==> P"
  by (unfold rel_comp_def) (iprover elim!: CollectE splitE exE conjE)

lemma rel_compEpair:
  "(a, c) : r O s ==> (!!y. (a, y) : s ==> (y, c) : r ==> P) ==> P"
  by (iprover elim: rel_compE Pair_inject ssubst)

lemma R_O_Id [simp]: "R O Id = R"
  by fast

lemma Id_O_R [simp]: "Id O R = R"
  by fast

lemma rel_comp_empty1[simp]: "{} O R = {}"
  by blast

lemma rel_comp_empty2[simp]: "R O {} = {}"
  by blast

lemma O_assoc: "(R O S) O T = R O (S O T)"
  by blast

lemma trans_O_subset: "trans r ==> r O r \<subseteq> r"
  by (unfold trans_def) blast

lemma rel_comp_mono: "r' \<subseteq> r ==> s' \<subseteq> s ==> (r' O s') \<subseteq> (r O s)"
  by blast

lemma rel_comp_subset_Sigma:
    "s \<subseteq> A \<times> B ==> r \<subseteq> B \<times> C ==> (r O s) \<subseteq> A \<times> C"
  by blast


subsection {* Reflexivity *}

lemma reflI: "r \<subseteq> A \<times> A ==> (!!x. x : A ==> (x, x) : r) ==> refl A r"
  by (unfold refl_def) (iprover intro!: ballI)

lemma reflD: "refl A r ==> a : A ==> (a, a) : r"
  by (unfold refl_def) blast

lemma reflD1: "refl A r ==> (x, y) : r ==> x : A"
  by (unfold refl_def) blast

lemma reflD2: "refl A r ==> (x, y) : r ==> y : A"
  by (unfold refl_def) blast

lemma refl_Int: "refl A r ==> refl B s ==> refl (A \<inter> B) (r \<inter> s)"
  by (unfold refl_def) blast

lemma refl_Un: "refl A r ==> refl B s ==> refl (A \<union> B) (r \<union> s)"
  by (unfold refl_def) blast

lemma refl_INTER:
  "ALL x:S. refl (A x) (r x) ==> refl (INTER S A) (INTER S r)"
  by (unfold refl_def) fast

lemma refl_UNION:
  "ALL x:S. refl (A x) (r x) \<Longrightarrow> refl (UNION S A) (UNION S r)"
  by (unfold refl_def) blast

lemma refl_diag: "refl A (diag A)"
  by (rule reflI [OF diag_subset_Times diagI])


subsection {* Antisymmetry *}

lemma antisymI:
  "(!!x y. (x, y) : r ==> (y, x) : r ==> x=y) ==> antisym r"
  by (unfold antisym_def) iprover

lemma antisymD: "antisym r ==> (a, b) : r ==> (b, a) : r ==> a = b"
  by (unfold antisym_def) iprover

lemma antisym_subset: "r \<subseteq> s ==> antisym s ==> antisym r"
  by (unfold antisym_def) blast

lemma antisym_empty [simp]: "antisym {}"
  by (unfold antisym_def) blast

lemma antisym_diag [simp]: "antisym (diag A)"
  by (unfold antisym_def) blast


subsection {* Symmetry *}

lemma symI: "(!!a b. (a, b) : r ==> (b, a) : r) ==> sym r"
  by (unfold sym_def) iprover

lemma symD: "sym r ==> (a, b) : r ==> (b, a) : r"
  by (unfold sym_def, blast)

lemma sym_Int: "sym r ==> sym s ==> sym (r \<inter> s)"
  by (fast intro: symI dest: symD)

lemma sym_Un: "sym r ==> sym s ==> sym (r \<union> s)"
  by (fast intro: symI dest: symD)

lemma sym_INTER: "ALL x:S. sym (r x) ==> sym (INTER S r)"
  by (fast intro: symI dest: symD)

lemma sym_UNION: "ALL x:S. sym (r x) ==> sym (UNION S r)"
  by (fast intro: symI dest: symD)

lemma sym_diag [simp]: "sym (diag A)"
  by (rule symI) clarify


subsection {* Transitivity *}

lemma transI:
  "(!!x y z. (x, y) : r ==> (y, z) : r ==> (x, z) : r) ==> trans r"
  by (unfold trans_def) iprover

lemma transD: "trans r ==> (a, b) : r ==> (b, c) : r ==> (a, c) : r"
  by (unfold trans_def) iprover

lemma trans_Int: "trans r ==> trans s ==> trans (r \<inter> s)"
  by (fast intro: transI elim: transD)

lemma trans_INTER: "ALL x:S. trans (r x) ==> trans (INTER S r)"
  by (fast intro: transI elim: transD)

lemma trans_diag [simp]: "trans (diag A)"
  by (fast intro: transI elim: transD)


subsection {* Converse *}

lemma converse_iff [iff]: "((a,b): r^-1) = ((b,a) : r)"
  by (simp add: converse_def)

lemma converseI[sym]: "(a, b) : r ==> (b, a) : r^-1"
  by (simp add: converse_def)

lemma converseD[sym]: "(a,b) : r^-1 ==> (b, a) : r"
  by (simp add: converse_def)

lemma converseE [elim!]:
  "yx : r^-1 ==> (!!x y. yx = (y, x) ==> (x, y) : r ==> P) ==> P"
    -- {* More general than @{text converseD}, as it ``splits'' the member of the relation. *}
  by (unfold converse_def) (iprover elim!: CollectE splitE bexE)

lemma converse_converse [simp]: "(r^-1)^-1 = r"
  by (unfold converse_def) blast

lemma converse_rel_comp: "(r O s)^-1 = s^-1 O r^-1"
  by blast

lemma converse_Int: "(r \<inter> s)^-1 = r^-1 \<inter> s^-1"
  by blast

lemma converse_Un: "(r \<union> s)^-1 = r^-1 \<union> s^-1"
  by blast

lemma converse_INTER: "(INTER S r)^-1 = (INT x:S. (r x)^-1)"
  by fast

lemma converse_UNION: "(UNION S r)^-1 = (UN x:S. (r x)^-1)"
  by blast

lemma converse_Id [simp]: "Id^-1 = Id"
  by blast

lemma converse_diag [simp]: "(diag A)^-1 = diag A"
  by blast

lemma refl_converse [simp]: "refl A (converse r) = refl A r"
  by (unfold refl_def) auto

lemma sym_converse [simp]: "sym (converse r) = sym r"
  by (unfold sym_def) blast

lemma antisym_converse [simp]: "antisym (converse r) = antisym r"
  by (unfold antisym_def) blast

lemma trans_converse [simp]: "trans (converse r) = trans r"
  by (unfold trans_def) blast

lemma sym_conv_converse_eq: "sym r = (r^-1 = r)"
  by (unfold sym_def) fast

lemma sym_Un_converse: "sym (r \<union> r^-1)"
  by (unfold sym_def) blast

lemma sym_Int_converse: "sym (r \<inter> r^-1)"
  by (unfold sym_def) blast


subsection {* Domain *}

declare Domain_def [noatp]

lemma Domain_iff: "(a : Domain r) = (EX y. (a, y) : r)"
  by (unfold Domain_def) blast

lemma DomainI [intro]: "(a, b) : r ==> a : Domain r"
  by (iprover intro!: iffD2 [OF Domain_iff])

lemma DomainE [elim!]:
  "a : Domain r ==> (!!y. (a, y) : r ==> P) ==> P"
  by (iprover dest!: iffD1 [OF Domain_iff])

lemma Domain_empty [simp]: "Domain {} = {}"
  by blast

lemma Domain_insert: "Domain (insert (a, b) r) = insert a (Domain r)"
  by blast

lemma Domain_Id [simp]: "Domain Id = UNIV"
  by blast

lemma Domain_diag [simp]: "Domain (diag A) = A"
  by blast

lemma Domain_Un_eq: "Domain(A \<union> B) = Domain(A) \<union> Domain(B)"
  by blast

lemma Domain_Int_subset: "Domain(A \<inter> B) \<subseteq> Domain(A) \<inter> Domain(B)"
  by blast

lemma Domain_Diff_subset: "Domain(A) - Domain(B) \<subseteq> Domain(A - B)"
  by blast

lemma Domain_Union: "Domain (Union S) = (\<Union>A\<in>S. Domain A)"
  by blast

lemma Domain_mono: "r \<subseteq> s ==> Domain r \<subseteq> Domain s"
  by blast

lemma fst_eq_Domain: "fst ` R = Domain R";
  apply auto
  apply (rule image_eqI, auto) 
  done


subsection {* Range *}

lemma Range_iff: "(a : Range r) = (EX y. (y, a) : r)"
  by (simp add: Domain_def Range_def)

lemma RangeI [intro]: "(a, b) : r ==> b : Range r"
  by (unfold Range_def) (iprover intro!: converseI DomainI)

lemma RangeE [elim!]: "b : Range r ==> (!!x. (x, b) : r ==> P) ==> P"
  by (unfold Range_def) (iprover elim!: DomainE dest!: converseD)

lemma Range_empty [simp]: "Range {} = {}"
  by blast

lemma Range_insert: "Range (insert (a, b) r) = insert b (Range r)"
  by blast

lemma Range_Id [simp]: "Range Id = UNIV"
  by blast

lemma Range_diag [simp]: "Range (diag A) = A"
  by auto

lemma Range_Un_eq: "Range(A \<union> B) = Range(A) \<union> Range(B)"
  by blast

lemma Range_Int_subset: "Range(A \<inter> B) \<subseteq> Range(A) \<inter> Range(B)"
  by blast

lemma Range_Diff_subset: "Range(A) - Range(B) \<subseteq> Range(A - B)"
  by blast

lemma Range_Union: "Range (Union S) = (\<Union>A\<in>S. Range A)"
  by blast

lemma snd_eq_Range: "snd ` R = Range R";
  apply auto
  apply (rule image_eqI, auto) 
  done


subsection {* Image of a set under a relation *}

declare Image_def [noatp]

lemma Image_iff: "(b : r``A) = (EX x:A. (x, b) : r)"
  by (simp add: Image_def)

lemma Image_singleton: "r``{a} = {b. (a, b) : r}"
  by (simp add: Image_def)

lemma Image_singleton_iff [iff]: "(b : r``{a}) = ((a, b) : r)"
  by (rule Image_iff [THEN trans]) simp

lemma ImageI [intro,noatp]: "(a, b) : r ==> a : A ==> b : r``A"
  by (unfold Image_def) blast

lemma ImageE [elim!]:
    "b : r `` A ==> (!!x. (x, b) : r ==> x : A ==> P) ==> P"
  by (unfold Image_def) (iprover elim!: CollectE bexE)

lemma rev_ImageI: "a : A ==> (a, b) : r ==> b : r `` A"
  -- {* This version's more effective when we already have the required @{text a} *}
  by blast

lemma Image_empty [simp]: "R``{} = {}"
  by blast

lemma Image_Id [simp]: "Id `` A = A"
  by blast

lemma Image_diag [simp]: "diag A `` B = A \<inter> B"
  by blast

lemma Image_Int_subset: "R `` (A \<inter> B) \<subseteq> R `` A \<inter> R `` B"
  by blast

lemma Image_Int_eq:
     "single_valued (converse R) ==> R `` (A \<inter> B) = R `` A \<inter> R `` B"
  by (simp add: single_valued_def, blast) 

lemma Image_Un: "R `` (A \<union> B) = R `` A \<union> R `` B"
  by blast

lemma Un_Image: "(R \<union> S) `` A = R `` A \<union> S `` A"
  by blast

lemma Image_subset: "r \<subseteq> A \<times> B ==> r``C \<subseteq> B"
  by (iprover intro!: subsetI elim!: ImageE dest!: subsetD SigmaD2)

lemma Image_eq_UN: "r``B = (\<Union>y\<in> B. r``{y})"
  -- {* NOT suitable for rewriting *}
  by blast

lemma Image_mono: "r' \<subseteq> r ==> A' \<subseteq> A ==> (r' `` A') \<subseteq> (r `` A)"
  by blast

lemma Image_UN: "(r `` (UNION A B)) = (\<Union>x\<in>A. r `` (B x))"
  by blast

lemma Image_INT_subset: "(r `` INTER A B) \<subseteq> (\<Inter>x\<in>A. r `` (B x))"
  by blast

text{*Converse inclusion requires some assumptions*}
lemma Image_INT_eq:
     "[|single_valued (r\<inverse>); A\<noteq>{}|] ==> r `` INTER A B = (\<Inter>x\<in>A. r `` B x)"
apply (rule equalityI)
 apply (rule Image_INT_subset) 
apply  (simp add: single_valued_def, blast)
done

lemma Image_subset_eq: "(r``A \<subseteq> B) = (A \<subseteq> - ((r^-1) `` (-B)))"
  by blast


subsection {* Single valued relations *}

lemma single_valuedI:
  "ALL x y. (x,y):r --> (ALL z. (x,z):r --> y=z) ==> single_valued r"
  by (unfold single_valued_def)

lemma single_valuedD:
  "single_valued r ==> (x, y) : r ==> (x, z) : r ==> y = z"
  by (simp add: single_valued_def)

lemma single_valued_rel_comp:
  "single_valued r ==> single_valued s ==> single_valued (r O s)"
  by (unfold single_valued_def) blast

lemma single_valued_subset:
  "r \<subseteq> s ==> single_valued s ==> single_valued r"
  by (unfold single_valued_def) blast

lemma single_valued_Id [simp]: "single_valued Id"
  by (unfold single_valued_def) blast

lemma single_valued_diag [simp]: "single_valued (diag A)"
  by (unfold single_valued_def) blast


subsection {* Graphs given by @{text Collect} *}

lemma Domain_Collect_split [simp]: "Domain{(x,y). P x y} = {x. EX y. P x y}"
  by auto

lemma Range_Collect_split [simp]: "Range{(x,y). P x y} = {y. EX x. P x y}"
  by auto

lemma Image_Collect_split [simp]: "{(x,y). P x y} `` A = {y. EX x:A. P x y}"
  by auto


subsection {* Inverse image *}

lemma sym_inv_image: "sym r ==> sym (inv_image r f)"
  by (unfold sym_def inv_image_def) blast

lemma trans_inv_image: "trans r ==> trans (inv_image r f)"
  apply (unfold trans_def inv_image_def)
  apply (simp (no_asm))
  apply blast
  done


subsection {* Version of @{text lfp_induct} for binary relations *}

lemmas lfp_induct2 = 
  lfp_induct_set [of "(a, b)", split_format (complete)]

end
