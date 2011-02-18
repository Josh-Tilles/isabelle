(*  Title:      ZF/OrdQuant.thy
    Authors:    Krzysztof Grabczewski and L C Paulson
*)

header {*Special quantifiers*}

theory OrdQuant imports Ordinal begin

subsection {*Quantifiers and union operator for ordinals*}

definition
  (* Ordinal Quantifiers *)
  oall :: "[i, i => o] => o"  where
    "oall(A, P) == ALL x. x<A --> P(x)"

definition
  oex :: "[i, i => o] => o"  where
    "oex(A, P)  == EX x. x<A & P(x)"

definition
  (* Ordinal Union *)
  OUnion :: "[i, i => i] => i"  where
    "OUnion(i,B) == {z: \<Union>x\<in>i. B(x). Ord(i)}"

syntax
  "_oall"     :: "[idt, i, o] => o"        ("(3ALL _<_./ _)" 10)
  "_oex"      :: "[idt, i, o] => o"        ("(3EX _<_./ _)" 10)
  "_OUNION"   :: "[idt, i, i] => i"        ("(3UN _<_./ _)" 10)

translations
  "ALL x<a. P"  == "CONST oall(a, %x. P)"
  "EX x<a. P"   == "CONST oex(a, %x. P)"
  "UN x<a. B"   == "CONST OUnion(a, %x. B)"

syntax (xsymbols)
  "_oall"     :: "[idt, i, o] => o"        ("(3\<forall>_<_./ _)" 10)
  "_oex"      :: "[idt, i, o] => o"        ("(3\<exists>_<_./ _)" 10)
  "_OUNION"   :: "[idt, i, i] => i"        ("(3\<Union>_<_./ _)" 10)
syntax (HTML output)
  "_oall"     :: "[idt, i, o] => o"        ("(3\<forall>_<_./ _)" 10)
  "_oex"      :: "[idt, i, o] => o"        ("(3\<exists>_<_./ _)" 10)
  "_OUNION"   :: "[idt, i, i] => i"        ("(3\<Union>_<_./ _)" 10)


subsubsection {*simplification of the new quantifiers*}


(*MOST IMPORTANT that this is added to the simpset BEFORE Ord_atomize
  is proved.  Ord_atomize would convert this rule to
    x < 0 ==> P(x) == True, which causes dire effects!*)
lemma [simp]: "(ALL x<0. P(x))"
by (simp add: oall_def)

lemma [simp]: "~(EX x<0. P(x))"
by (simp add: oex_def)

lemma [simp]: "(ALL x<succ(i). P(x)) <-> (Ord(i) --> P(i) & (ALL x<i. P(x)))"
apply (simp add: oall_def le_iff)
apply (blast intro: lt_Ord2)
done

lemma [simp]: "(EX x<succ(i). P(x)) <-> (Ord(i) & (P(i) | (EX x<i. P(x))))"
apply (simp add: oex_def le_iff)
apply (blast intro: lt_Ord2)
done

subsubsection {*Union over ordinals*}

lemma Ord_OUN [intro,simp]:
     "[| !!x. x<A ==> Ord(B(x)) |] ==> Ord(\<Union>x<A. B(x))"
by (simp add: OUnion_def ltI Ord_UN)

lemma OUN_upper_lt:
     "[| a<A;  i < b(a);  Ord(\<Union>x<A. b(x)) |] ==> i < (\<Union>x<A. b(x))"
by (unfold OUnion_def lt_def, blast )

lemma OUN_upper_le:
     "[| a<A;  i\<le>b(a);  Ord(\<Union>x<A. b(x)) |] ==> i \<le> (\<Union>x<A. b(x))"
apply (unfold OUnion_def, auto)
apply (rule UN_upper_le )
apply (auto simp add: lt_def)
done

lemma Limit_OUN_eq: "Limit(i) ==> (\<Union>x<i. x) = i"
by (simp add: OUnion_def Limit_Union_eq Limit_is_Ord)

(* No < version; consider (\<Union>i\<in>nat.i)=nat *)
lemma OUN_least:
     "(!!x. x<A ==> B(x) \<subseteq> C) ==> (\<Union>x<A. B(x)) \<subseteq> C"
by (simp add: OUnion_def UN_least ltI)

(* No < version; consider (\<Union>i\<in>nat.i)=nat *)
lemma OUN_least_le:
     "[| Ord(i);  !!x. x<A ==> b(x) \<le> i |] ==> (\<Union>x<A. b(x)) \<le> i"
by (simp add: OUnion_def UN_least_le ltI Ord_0_le)

lemma le_implies_OUN_le_OUN:
     "[| !!x. x<A ==> c(x) \<le> d(x) |] ==> (\<Union>x<A. c(x)) \<le> (\<Union>x<A. d(x))"
by (blast intro: OUN_least_le OUN_upper_le le_Ord2 Ord_OUN)

lemma OUN_UN_eq:
     "(!!x. x:A ==> Ord(B(x)))
      ==> (\<Union>z < (\<Union>x\<in>A. B(x)). C(z)) = (\<Union>x\<in>A. \<Union>z < B(x). C(z))"
by (simp add: OUnion_def)

lemma OUN_Union_eq:
     "(!!x. x:X ==> Ord(x))
      ==> (\<Union>z < Union(X). C(z)) = (\<Union>x\<in>X. \<Union>z < x. C(z))"
by (simp add: OUnion_def)

(*So that rule_format will get rid of ALL x<A...*)
lemma atomize_oall [symmetric, rulify]:
     "(!!x. x<A ==> P(x)) == Trueprop (ALL x<A. P(x))"
by (simp add: oall_def atomize_all atomize_imp)

subsubsection {*universal quantifier for ordinals*}

lemma oallI [intro!]:
    "[| !!x. x<A ==> P(x) |] ==> ALL x<A. P(x)"
by (simp add: oall_def)

lemma ospec: "[| ALL x<A. P(x);  x<A |] ==> P(x)"
by (simp add: oall_def)

lemma oallE:
    "[| ALL x<A. P(x);  P(x) ==> Q;  ~x<A ==> Q |] ==> Q"
by (simp add: oall_def, blast)

lemma rev_oallE [elim]:
    "[| ALL x<A. P(x);  ~x<A ==> Q;  P(x) ==> Q |] ==> Q"
by (simp add: oall_def, blast)


(*Trival rewrite rule;   (ALL x<a.P)<->P holds only if a is not 0!*)
lemma oall_simp [simp]: "(ALL x<a. True) <-> True"
by blast

(*Congruence rule for rewriting*)
lemma oall_cong [cong]:
    "[| a=a';  !!x. x<a' ==> P(x) <-> P'(x) |]
     ==> oall(a, %x. P(x)) <-> oall(a', %x. P'(x))"
by (simp add: oall_def)


subsubsection {*existential quantifier for ordinals*}

lemma oexI [intro]:
    "[| P(x);  x<A |] ==> EX x<A. P(x)"
apply (simp add: oex_def, blast)
done

(*Not of the general form for such rules; ~EX has become ALL~ *)
lemma oexCI:
   "[| ALL x<A. ~P(x) ==> P(a);  a<A |] ==> EX x<A. P(x)"
apply (simp add: oex_def, blast)
done

lemma oexE [elim!]:
    "[| EX x<A. P(x);  !!x. [| x<A; P(x) |] ==> Q |] ==> Q"
apply (simp add: oex_def, blast)
done

lemma oex_cong [cong]:
    "[| a=a';  !!x. x<a' ==> P(x) <-> P'(x) |]
     ==> oex(a, %x. P(x)) <-> oex(a', %x. P'(x))"
apply (simp add: oex_def cong add: conj_cong)
done


subsubsection {*Rules for Ordinal-Indexed Unions*}

lemma OUN_I [intro]: "[| a<i;  b: B(a) |] ==> b: (\<Union>z<i. B(z))"
by (unfold OUnion_def lt_def, blast)

lemma OUN_E [elim!]:
    "[| b : (\<Union>z<i. B(z));  !!a.[| b: B(a);  a<i |] ==> R |] ==> R"
apply (unfold OUnion_def lt_def, blast)
done

lemma OUN_iff: "b : (\<Union>x<i. B(x)) <-> (EX x<i. b : B(x))"
by (unfold OUnion_def oex_def lt_def, blast)

lemma OUN_cong [cong]:
    "[| i=j;  !!x. x<j ==> C(x)=D(x) |] ==> (\<Union>x<i. C(x)) = (\<Union>x<j. D(x))"
by (simp add: OUnion_def lt_def OUN_iff)

lemma lt_induct:
    "[| i<k;  !!x.[| x<k;  ALL y<x. P(y) |] ==> P(x) |]  ==>  P(i)"
apply (simp add: lt_def oall_def)
apply (erule conjE)
apply (erule Ord_induct, assumption, blast)
done


subsection {*Quantification over a class*}

definition
  "rall"     :: "[i=>o, i=>o] => o"  where
    "rall(M, P) == ALL x. M(x) --> P(x)"

definition
  "rex"      :: "[i=>o, i=>o] => o"  where
    "rex(M, P) == EX x. M(x) & P(x)"

syntax
  "_rall"     :: "[pttrn, i=>o, o] => o"        ("(3ALL _[_]./ _)" 10)
  "_rex"      :: "[pttrn, i=>o, o] => o"        ("(3EX _[_]./ _)" 10)

syntax (xsymbols)
  "_rall"     :: "[pttrn, i=>o, o] => o"        ("(3\<forall>_[_]./ _)" 10)
  "_rex"      :: "[pttrn, i=>o, o] => o"        ("(3\<exists>_[_]./ _)" 10)
syntax (HTML output)
  "_rall"     :: "[pttrn, i=>o, o] => o"        ("(3\<forall>_[_]./ _)" 10)
  "_rex"      :: "[pttrn, i=>o, o] => o"        ("(3\<exists>_[_]./ _)" 10)

translations
  "ALL x[M]. P"  == "CONST rall(M, %x. P)"
  "EX x[M]. P"   == "CONST rex(M, %x. P)"


subsubsection{*Relativized universal quantifier*}

lemma rallI [intro!]: "[| !!x. M(x) ==> P(x) |] ==> ALL x[M]. P(x)"
by (simp add: rall_def)

lemma rspec: "[| ALL x[M]. P(x); M(x) |] ==> P(x)"
by (simp add: rall_def)

(*Instantiates x first: better for automatic theorem proving?*)
lemma rev_rallE [elim]:
    "[| ALL x[M]. P(x);  ~ M(x) ==> Q;  P(x) ==> Q |] ==> Q"
by (simp add: rall_def, blast)

lemma rallE: "[| ALL x[M]. P(x);  P(x) ==> Q;  ~ M(x) ==> Q |] ==> Q"
by blast

(*Trival rewrite rule;   (ALL x[M].P)<->P holds only if A is nonempty!*)
lemma rall_triv [simp]: "(ALL x[M]. P) <-> ((EX x. M(x)) --> P)"
by (simp add: rall_def)

(*Congruence rule for rewriting*)
lemma rall_cong [cong]:
    "(!!x. M(x) ==> P(x) <-> P'(x)) ==> (ALL x[M]. P(x)) <-> (ALL x[M]. P'(x))"
by (simp add: rall_def)


subsubsection{*Relativized existential quantifier*}

lemma rexI [intro]: "[| P(x); M(x) |] ==> EX x[M]. P(x)"
by (simp add: rex_def, blast)

(*The best argument order when there is only one M(x)*)
lemma rev_rexI: "[| M(x);  P(x) |] ==> EX x[M]. P(x)"
by blast

(*Not of the general form for such rules; ~EX has become ALL~ *)
lemma rexCI: "[| ALL x[M]. ~P(x) ==> P(a); M(a) |] ==> EX x[M]. P(x)"
by blast

lemma rexE [elim!]: "[| EX x[M]. P(x);  !!x. [| M(x); P(x) |] ==> Q |] ==> Q"
by (simp add: rex_def, blast)

(*We do not even have (EX x[M]. True) <-> True unless A is nonempty!!*)
lemma rex_triv [simp]: "(EX x[M]. P) <-> ((EX x. M(x)) & P)"
by (simp add: rex_def)

lemma rex_cong [cong]:
    "(!!x. M(x) ==> P(x) <-> P'(x)) ==> (EX x[M]. P(x)) <-> (EX x[M]. P'(x))"
by (simp add: rex_def cong: conj_cong)

lemma rall_is_ball [simp]: "(\<forall>x[%z. z\<in>A]. P(x)) <-> (\<forall>x\<in>A. P(x))"
by blast

lemma rex_is_bex [simp]: "(\<exists>x[%z. z\<in>A]. P(x)) <-> (\<exists>x\<in>A. P(x))"
by blast

lemma atomize_rall: "(!!x. M(x) ==> P(x)) == Trueprop (ALL x[M]. P(x))";
by (simp add: rall_def atomize_all atomize_imp)

declare atomize_rall [symmetric, rulify]

lemma rall_simps1:
     "(ALL x[M]. P(x) & Q)   <-> (ALL x[M]. P(x)) & ((ALL x[M]. False) | Q)"
     "(ALL x[M]. P(x) | Q)   <-> ((ALL x[M]. P(x)) | Q)"
     "(ALL x[M]. P(x) --> Q) <-> ((EX x[M]. P(x)) --> Q)"
     "(~(ALL x[M]. P(x))) <-> (EX x[M]. ~P(x))"
by blast+

lemma rall_simps2:
     "(ALL x[M]. P & Q(x))   <-> ((ALL x[M]. False) | P) & (ALL x[M]. Q(x))"
     "(ALL x[M]. P | Q(x))   <-> (P | (ALL x[M]. Q(x)))"
     "(ALL x[M]. P --> Q(x)) <-> (P --> (ALL x[M]. Q(x)))"
by blast+

lemmas rall_simps [simp] = rall_simps1 rall_simps2

lemma rall_conj_distrib:
    "(ALL x[M]. P(x) & Q(x)) <-> ((ALL x[M]. P(x)) & (ALL x[M]. Q(x)))"
by blast

lemma rex_simps1:
     "(EX x[M]. P(x) & Q) <-> ((EX x[M]. P(x)) & Q)"
     "(EX x[M]. P(x) | Q) <-> (EX x[M]. P(x)) | ((EX x[M]. True) & Q)"
     "(EX x[M]. P(x) --> Q) <-> ((ALL x[M]. P(x)) --> ((EX x[M]. True) & Q))"
     "(~(EX x[M]. P(x))) <-> (ALL x[M]. ~P(x))"
by blast+

lemma rex_simps2:
     "(EX x[M]. P & Q(x)) <-> (P & (EX x[M]. Q(x)))"
     "(EX x[M]. P | Q(x)) <-> ((EX x[M]. True) & P) | (EX x[M]. Q(x))"
     "(EX x[M]. P --> Q(x)) <-> (((ALL x[M]. False) | P) --> (EX x[M]. Q(x)))"
by blast+

lemmas rex_simps [simp] = rex_simps1 rex_simps2

lemma rex_disj_distrib:
    "(EX x[M]. P(x) | Q(x)) <-> ((EX x[M]. P(x)) | (EX x[M]. Q(x)))"
by blast


subsubsection{*One-point rule for bounded quantifiers*}

lemma rex_triv_one_point1 [simp]: "(EX x[M]. x=a) <-> ( M(a))"
by blast

lemma rex_triv_one_point2 [simp]: "(EX x[M]. a=x) <-> ( M(a))"
by blast

lemma rex_one_point1 [simp]: "(EX x[M]. x=a & P(x)) <-> ( M(a) & P(a))"
by blast

lemma rex_one_point2 [simp]: "(EX x[M]. a=x & P(x)) <-> ( M(a) & P(a))"
by blast

lemma rall_one_point1 [simp]: "(ALL x[M]. x=a --> P(x)) <-> ( M(a) --> P(a))"
by blast

lemma rall_one_point2 [simp]: "(ALL x[M]. a=x --> P(x)) <-> ( M(a) --> P(a))"
by blast


subsubsection{*Sets as Classes*}

definition
  setclass :: "[i,i] => o"       ("##_" [40] 40)  where
   "setclass(A) == %x. x : A"

lemma setclass_iff [simp]: "setclass(A,x) <-> x : A"
by (simp add: setclass_def)

lemma rall_setclass_is_ball [simp]: "(\<forall>x[##A]. P(x)) <-> (\<forall>x\<in>A. P(x))"
by auto

lemma rex_setclass_is_bex [simp]: "(\<exists>x[##A]. P(x)) <-> (\<exists>x\<in>A. P(x))"
by auto


ML
{*
val Ord_atomize =
    atomize ([("OrdQuant.oall", [@{thm ospec}]),("OrdQuant.rall", [@{thm rspec}])]@
                 ZF_conn_pairs,
             ZF_mem_pairs);
*}
declaration {* fn _ =>
  Simplifier.map_ss (fn ss => ss setmksimps (K (map mk_eq o Ord_atomize o gen_all)))
*}

text {* Setting up the one-point-rule simproc *}

ML {*
local

val unfold_rex_tac = unfold_tac [@{thm rex_def}];
fun prove_rex_tac ss = unfold_rex_tac ss THEN Quantifier1.prove_one_point_ex_tac;
val rearrange_bex = Quantifier1.rearrange_bex prove_rex_tac;

val unfold_rall_tac = unfold_tac [@{thm rall_def}];
fun prove_rall_tac ss = unfold_rall_tac ss THEN Quantifier1.prove_one_point_all_tac;
val rearrange_ball = Quantifier1.rearrange_ball prove_rall_tac;

in

val defREX_regroup = Simplifier.simproc_global @{theory}
  "defined REX" ["EX x[M]. P(x) & Q(x)"] rearrange_bex;
val defRALL_regroup = Simplifier.simproc_global @{theory}
  "defined RALL" ["ALL x[M]. P(x) --> Q(x)"] rearrange_ball;

end;

Addsimprocs [defRALL_regroup,defREX_regroup];
*}

end
