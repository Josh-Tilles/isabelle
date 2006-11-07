(*  Title:      HOL/Transitive_Closure.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header {* Reflexive and Transitive closure of a relation *}

theory Transitive_Closure
imports Inductive
uses ("../Provers/trancl.ML")
begin

text {*
  @{text rtrancl} is reflexive/transitive closure,
  @{text trancl} is transitive closure,
  @{text reflcl} is reflexive closure.

  These postfix operators have \emph{maximum priority}, forcing their
  operands to be atomic.
*}

consts
  rtrancl :: "('a \<times> 'a) set => ('a \<times> 'a) set"    ("(_^*)" [1000] 999)

inductive "r^*"
  intros
    rtrancl_refl [intro!, Pure.intro!, simp]: "(a, a) : r^*"
    rtrancl_into_rtrancl [Pure.intro]: "(a, b) : r^* ==> (b, c) : r ==> (a, c) : r^*"

consts
  trancl :: "('a \<times> 'a) set => ('a \<times> 'a) set"    ("(_^+)" [1000] 999)

inductive "r^+"
  intros
    r_into_trancl [intro, Pure.intro]: "(a, b) : r ==> (a, b) : r^+"
    trancl_into_trancl [Pure.intro]: "(a, b) : r^+ ==> (b, c) : r ==> (a,c) : r^+"

abbreviation
  reflcl :: "('a \<times> 'a) set => ('a \<times> 'a) set"    ("(_^=)" [1000] 999)
  "r^= == r \<union> Id"

notation (xsymbols)
  rtrancl  ("(_\<^sup>*)" [1000] 999)
  trancl  ("(_\<^sup>+)" [1000] 999)
  reflcl  ("(_\<^sup>=)" [1000] 999)

notation (HTML output)
  rtrancl  ("(_\<^sup>*)" [1000] 999)
  trancl  ("(_\<^sup>+)" [1000] 999)
  reflcl  ("(_\<^sup>=)" [1000] 999)


subsection {* Reflexive-transitive closure *}

lemma r_into_rtrancl [intro]: "!!p. p \<in> r ==> p \<in> r^*"
  -- {* @{text rtrancl} of @{text r} contains @{text r} *}
  apply (simp only: split_tupled_all)
  apply (erule rtrancl_refl [THEN rtrancl_into_rtrancl])
  done

lemma rtrancl_mono: "r \<subseteq> s ==> r^* \<subseteq> s^*"
  -- {* monotonicity of @{text rtrancl} *}
  apply (rule subsetI)
  apply (simp only: split_tupled_all)
  apply (erule rtrancl.induct)
   apply (rule_tac [2] rtrancl_into_rtrancl, blast+)
  done

theorem rtrancl_induct [consumes 1, induct set: rtrancl]:
  assumes a: "(a, b) : r^*"
    and cases: "P a" "!!y z. [| (a, y) : r^*; (y, z) : r; P y |] ==> P z"
  shows "P b"
proof -
  from a have "a = a --> P b"
    by (induct "%x y. x = a --> P y" a b) (iprover intro: cases)+
  thus ?thesis by iprover
qed

lemmas rtrancl_induct2 =
  rtrancl_induct[of "(ax,ay)" "(bx,by)", split_format (complete),
                 consumes 1, case_names refl step]

lemma reflexive_rtrancl: "reflexive (r^*)"
  by (unfold refl_def) fast

lemma trans_rtrancl: "trans(r^*)"
  -- {* transitivity of transitive closure!! -- by induction *}
proof (rule transI)
  fix x y z
  assume "(x, y) \<in> r\<^sup>*"
  assume "(y, z) \<in> r\<^sup>*"
  thus "(x, z) \<in> r\<^sup>*" by induct (iprover!)+
qed

lemmas rtrancl_trans = trans_rtrancl [THEN transD, standard]

lemma rtranclE:
  assumes major: "(a::'a,b) : r^*"
    and cases: "(a = b) ==> P"
      "!!y. [| (a,y) : r^*; (y,b) : r |] ==> P"
  shows P
  -- {* elimination of @{text rtrancl} -- by induction on a special formula *}
  apply (subgoal_tac "(a::'a) = b | (EX y. (a,y) : r^* & (y,b) : r)")
   apply (rule_tac [2] major [THEN rtrancl_induct])
    prefer 2 apply blast
   prefer 2 apply blast
  apply (erule asm_rl exE disjE conjE cases)+
  done

lemma converse_rtrancl_into_rtrancl:
  "(a, b) \<in> r \<Longrightarrow> (b, c) \<in> r\<^sup>* \<Longrightarrow> (a, c) \<in> r\<^sup>*"
  by (rule rtrancl_trans) iprover+

text {*
  \medskip More @{term "r^*"} equations and inclusions.
*}

lemma rtrancl_idemp [simp]: "(r^*)^* = r^*"
  apply auto
  apply (erule rtrancl_induct)
   apply (rule rtrancl_refl)
  apply (blast intro: rtrancl_trans)
  done

lemma rtrancl_idemp_self_comp [simp]: "R^* O R^* = R^*"
  apply (rule set_ext)
  apply (simp only: split_tupled_all)
  apply (blast intro: rtrancl_trans)
  done

lemma rtrancl_subset_rtrancl: "r \<subseteq> s^* ==> r^* \<subseteq> s^*"
by (drule rtrancl_mono, simp)

lemma rtrancl_subset: "R \<subseteq> S ==> S \<subseteq> R^* ==> S^* = R^*"
  apply (drule rtrancl_mono)
  apply (drule rtrancl_mono, simp)
  done

lemma rtrancl_Un_rtrancl: "(R^* \<union> S^*)^* = (R \<union> S)^*"
  by (blast intro!: rtrancl_subset intro: r_into_rtrancl rtrancl_mono [THEN subsetD])

lemma rtrancl_reflcl [simp]: "(R^=)^* = R^*"
  by (blast intro!: rtrancl_subset intro: r_into_rtrancl)

lemma rtrancl_r_diff_Id: "(r - Id)^* = r^*"
  apply (rule sym)
  apply (rule rtrancl_subset, blast, clarify)
  apply (rename_tac a b)
  apply (case_tac "a = b", blast)
  apply (blast intro!: r_into_rtrancl)
  done

theorem rtrancl_converseD:
  assumes r: "(x, y) \<in> (r^-1)^*"
  shows "(y, x) \<in> r^*"
proof -
  from r show ?thesis
    by induct (iprover intro: rtrancl_trans dest!: converseD)+
qed

theorem rtrancl_converseI:
  assumes r: "(y, x) \<in> r^*"
  shows "(x, y) \<in> (r^-1)^*"
proof -
  from r show ?thesis
    by induct (iprover intro: rtrancl_trans converseI)+
qed

lemma rtrancl_converse: "(r^-1)^* = (r^*)^-1"
  by (fast dest!: rtrancl_converseD intro!: rtrancl_converseI)

lemma sym_rtrancl: "sym r ==> sym (r^*)"
  by (simp only: sym_conv_converse_eq rtrancl_converse [symmetric])

theorem converse_rtrancl_induct[consumes 1]:
  assumes major: "(a, b) : r^*"
    and cases: "P b" "!!y z. [| (y, z) : r; (z, b) : r^*; P z |] ==> P y"
  shows "P a"
proof -
  from rtrancl_converseI [OF major]
  show ?thesis
    by induct (iprover intro: cases dest!: converseD rtrancl_converseD)+
qed

lemmas converse_rtrancl_induct2 =
  converse_rtrancl_induct[of "(ax,ay)" "(bx,by)", split_format (complete),
                 consumes 1, case_names refl step]

lemma converse_rtranclE:
  assumes major: "(x,z):r^*"
    and cases: "x=z ==> P"
      "!!y. [| (x,y):r; (y,z):r^* |] ==> P"
  shows P
  apply (subgoal_tac "x = z | (EX y. (x,y) : r & (y,z) : r^*)")
   apply (rule_tac [2] major [THEN converse_rtrancl_induct])
    prefer 2 apply iprover
   prefer 2 apply iprover
  apply (erule asm_rl exE disjE conjE cases)+
  done

ML_setup {*
  bind_thm ("converse_rtranclE2", split_rule
    (read_instantiate [("x","(xa,xb)"), ("z","(za,zb)")] (thm "converse_rtranclE")));
*}

lemma r_comp_rtrancl_eq: "r O r^* = r^* O r"
  by (blast elim: rtranclE converse_rtranclE
    intro: rtrancl_into_rtrancl converse_rtrancl_into_rtrancl)

lemma rtrancl_unfold: "r^* = Id Un r O r^*"
  by (auto intro: rtrancl_into_rtrancl elim: rtranclE)


subsection {* Transitive closure *}

lemma trancl_mono: "!!p. p \<in> r^+ ==> r \<subseteq> s ==> p \<in> s^+"
  apply (simp only: split_tupled_all)
  apply (erule trancl.induct)
  apply (iprover dest: subsetD)+
  done

lemma r_into_trancl': "!!p. p : r ==> p : r^+"
  by (simp only: split_tupled_all) (erule r_into_trancl)

text {*
  \medskip Conversions between @{text trancl} and @{text rtrancl}.
*}

lemma trancl_into_rtrancl: "(a, b) \<in> r^+ ==> (a, b) \<in> r^*"
  by (erule trancl.induct) iprover+

lemma rtrancl_into_trancl1: assumes r: "(a, b) \<in> r^*"
  shows "!!c. (b, c) \<in> r ==> (a, c) \<in> r^+" using r
  by induct iprover+

lemma rtrancl_into_trancl2: "[| (a,b) : r;  (b,c) : r^* |]   ==>  (a,c) : r^+"
  -- {* intro rule from @{text r} and @{text rtrancl} *}
  apply (erule rtranclE, iprover)
  apply (rule rtrancl_trans [THEN rtrancl_into_trancl1])
   apply (assumption | rule r_into_rtrancl)+
  done

lemma trancl_induct [consumes 1, induct set: trancl]:
  assumes a: "(a,b) : r^+"
  and cases: "!!y. (a, y) : r ==> P y"
    "!!y z. (a,y) : r^+ ==> (y, z) : r ==> P y ==> P z"
  shows "P b"
  -- {* Nice induction rule for @{text trancl} *}
proof -
  from a have "a = a --> P b"
    by (induct "%x y. x = a --> P y" a b) (iprover intro: cases)+
  thus ?thesis by iprover
qed

lemma trancl_trans_induct:
  assumes major: "(x,y) : r^+"
    and cases: "!!x y. (x,y) : r ==> P x y"
      "!!x y z. [| (x,y) : r^+; P x y; (y,z) : r^+; P y z |] ==> P x z"
  shows "P x y"
  -- {* Another induction rule for trancl, incorporating transitivity *}
  by (iprover intro: r_into_trancl major [THEN trancl_induct] cases)

inductive_cases tranclE: "(a, b) : r^+"

lemma trancl_unfold: "r^+ = r Un r O r^+"
  by (auto intro: trancl_into_trancl elim: tranclE)

lemma trans_trancl[simp]: "trans(r^+)"
  -- {* Transitivity of @{term "r^+"} *}
proof (rule transI)
  fix x y z
  assume xy: "(x, y) \<in> r^+"
  assume "(y, z) \<in> r^+"
  thus "(x, z) \<in> r^+" by induct (insert xy, iprover)+
qed

lemmas trancl_trans = trans_trancl [THEN transD, standard]

lemma trancl_id[simp]: "trans r \<Longrightarrow> r^+ = r"
apply(auto)
apply(erule trancl_induct)
apply assumption
apply(unfold trans_def)
apply(blast)
done

lemma rtrancl_trancl_trancl: assumes r: "(x, y) \<in> r^*"
  shows "!!z. (y, z) \<in> r^+ ==> (x, z) \<in> r^+" using r
  by induct (iprover intro: trancl_trans)+

lemma trancl_into_trancl2: "(a, b) \<in> r ==> (b, c) \<in> r^+ ==> (a, c) \<in> r^+"
  by (erule transD [OF trans_trancl r_into_trancl])

lemma trancl_insert:
  "(insert (y, x) r)^+ = r^+ \<union> {(a, b). (a, y) \<in> r^* \<and> (x, b) \<in> r^*}"
  -- {* primitive recursion for @{text trancl} over finite relations *}
  apply (rule equalityI)
   apply (rule subsetI)
   apply (simp only: split_tupled_all)
   apply (erule trancl_induct, blast)
   apply (blast intro: rtrancl_into_trancl1 trancl_into_rtrancl r_into_trancl trancl_trans)
  apply (rule subsetI)
  apply (blast intro: trancl_mono rtrancl_mono
    [THEN [2] rev_subsetD] rtrancl_trancl_trancl rtrancl_into_trancl2)
  done

lemma trancl_converseI: "(x, y) \<in> (r^+)^-1 ==> (x, y) \<in> (r^-1)^+"
  apply (drule converseD)
  apply (erule trancl.induct)
  apply (iprover intro: converseI trancl_trans)+
  done

lemma trancl_converseD: "(x, y) \<in> (r^-1)^+ ==> (x, y) \<in> (r^+)^-1"
  apply (rule converseI)
  apply (erule trancl.induct)
  apply (iprover dest: converseD intro: trancl_trans)+
  done

lemma trancl_converse: "(r^-1)^+ = (r^+)^-1"
  by (fastsimp simp add: split_tupled_all
    intro!: trancl_converseI trancl_converseD)

lemma sym_trancl: "sym r ==> sym (r^+)"
  by (simp only: sym_conv_converse_eq trancl_converse [symmetric])

lemma converse_trancl_induct:
  assumes major: "(a,b) : r^+"
    and cases: "!!y. (y,b) : r ==> P(y)"
      "!!y z.[| (y,z) : r;  (z,b) : r^+;  P(z) |] ==> P(y)"
  shows "P a"
  apply (rule major [THEN converseI, THEN trancl_converseI [THEN trancl_induct]])
   apply (rule cases)
   apply (erule converseD)
  apply (blast intro: prems dest!: trancl_converseD)
  done

lemma tranclD: "(x, y) \<in> R^+ ==> EX z. (x, z) \<in> R \<and> (z, y) \<in> R^*"
  apply (erule converse_trancl_induct, auto)
  apply (blast intro: rtrancl_trans)
  done

lemma irrefl_tranclI: "r^-1 \<inter> r^* = {} ==> (x, x) \<notin> r^+"
  by (blast elim: tranclE dest: trancl_into_rtrancl)

lemma irrefl_trancl_rD: "!!X. ALL x. (x, x) \<notin> r^+ ==> (x, y) \<in> r ==> x \<noteq> y"
  by (blast dest: r_into_trancl)

lemma trancl_subset_Sigma_aux:
    "(a, b) \<in> r^* ==> r \<subseteq> A \<times> A ==> a = b \<or> a \<in> A"
  by (induct rule: rtrancl_induct) auto

lemma trancl_subset_Sigma: "r \<subseteq> A \<times> A ==> r^+ \<subseteq> A \<times> A"
  apply (rule subsetI)
  apply (simp only: split_tupled_all)
  apply (erule tranclE)
  apply (blast dest!: trancl_into_rtrancl trancl_subset_Sigma_aux)+
  done

lemma reflcl_trancl [simp]: "(r^+)^= = r^*"
  apply safe
   apply (erule trancl_into_rtrancl)
  apply (blast elim: rtranclE dest: rtrancl_into_trancl1)
  done

lemma trancl_reflcl [simp]: "(r^=)^+ = r^*"
  apply safe
   apply (drule trancl_into_rtrancl, simp)
  apply (erule rtranclE, safe)
   apply (rule r_into_trancl, simp)
  apply (rule rtrancl_into_trancl1)
   apply (erule rtrancl_reflcl [THEN equalityD2, THEN subsetD], fast)
  done

lemma trancl_empty [simp]: "{}^+ = {}"
  by (auto elim: trancl_induct)

lemma rtrancl_empty [simp]: "{}^* = Id"
  by (rule subst [OF reflcl_trancl]) simp

lemma rtranclD: "(a, b) \<in> R^* ==> a = b \<or> a \<noteq> b \<and> (a, b) \<in> R^+"
  by (force simp add: reflcl_trancl [symmetric] simp del: reflcl_trancl)

lemma rtrancl_eq_or_trancl:
  "(x,y) \<in> R\<^sup>* = (x=y \<or> x\<noteq>y \<and> (x,y) \<in> R\<^sup>+)"
  by (fast elim: trancl_into_rtrancl dest: rtranclD)

text {* @{text Domain} and @{text Range} *}

lemma Domain_rtrancl [simp]: "Domain (R^*) = UNIV"
  by blast

lemma Range_rtrancl [simp]: "Range (R^*) = UNIV"
  by blast

lemma rtrancl_Un_subset: "(R^* \<union> S^*) \<subseteq> (R Un S)^*"
  by (rule rtrancl_Un_rtrancl [THEN subst]) fast

lemma in_rtrancl_UnI: "x \<in> R^* \<or> x \<in> S^* ==> x \<in> (R \<union> S)^*"
  by (blast intro: subsetD [OF rtrancl_Un_subset])

lemma trancl_domain [simp]: "Domain (r^+) = Domain r"
  by (unfold Domain_def) (blast dest: tranclD)

lemma trancl_range [simp]: "Range (r^+) = Range r"
  by (simp add: Range_def trancl_converse [symmetric])

lemma Not_Domain_rtrancl:
    "x ~: Domain R ==> ((x, y) : R^*) = (x = y)"
  apply auto
  by (erule rev_mp, erule rtrancl_induct, auto)


text {* More about converse @{text rtrancl} and @{text trancl}, should
  be merged with main body. *}

lemma single_valued_confluent:
  "\<lbrakk> single_valued r; (x,y) \<in> r^*; (x,z) \<in> r^* \<rbrakk>
  \<Longrightarrow> (y,z) \<in> r^* \<or> (z,y) \<in> r^*"
apply(erule rtrancl_induct)
 apply simp
apply(erule disjE)
 apply(blast elim:converse_rtranclE dest:single_valuedD)
apply(blast intro:rtrancl_trans)
done

lemma r_r_into_trancl: "(a, b) \<in> R ==> (b, c) \<in> R ==> (a, c) \<in> R^+"
  by (fast intro: trancl_trans)

lemma trancl_into_trancl [rule_format]:
    "(a, b) \<in> r\<^sup>+ ==> (b, c) \<in> r --> (a,c) \<in> r\<^sup>+"
  apply (erule trancl_induct)
   apply (fast intro: r_r_into_trancl)
  apply (fast intro: r_r_into_trancl trancl_trans)
  done

lemma trancl_rtrancl_trancl:
    "(a, b) \<in> r\<^sup>+ ==> (b, c) \<in> r\<^sup>* ==> (a, c) \<in> r\<^sup>+"
  apply (drule tranclD)
  apply (erule exE, erule conjE)
  apply (drule rtrancl_trans, assumption)
  apply (drule rtrancl_into_trancl2, assumption, assumption)
  done

lemmas transitive_closure_trans [trans] =
  r_r_into_trancl trancl_trans rtrancl_trans
  trancl_into_trancl trancl_into_trancl2
  rtrancl_into_rtrancl converse_rtrancl_into_rtrancl
  rtrancl_trancl_trancl trancl_rtrancl_trancl

declare trancl_into_rtrancl [elim]

declare rtranclE [cases set: rtrancl]
declare tranclE [cases set: trancl]





subsection {* Setup of transitivity reasoner *}

use "../Provers/trancl.ML";

ML_setup {*

structure Trancl_Tac = Trancl_Tac_Fun (
  struct
    val r_into_trancl = thm "r_into_trancl";
    val trancl_trans  = thm "trancl_trans";
    val rtrancl_refl = thm "rtrancl_refl";
    val r_into_rtrancl = thm "r_into_rtrancl";
    val trancl_into_rtrancl = thm "trancl_into_rtrancl";
    val rtrancl_trancl_trancl = thm "rtrancl_trancl_trancl";
    val trancl_rtrancl_trancl = thm "trancl_rtrancl_trancl";
    val rtrancl_trans = thm "rtrancl_trans";

  fun decomp (Trueprop $ t) =
    let fun dec (Const ("op :", _) $ (Const ("Pair", _) $ a $ b) $ rel ) =
        let fun decr (Const ("Transitive_Closure.rtrancl", _ ) $ r) = (r,"r*")
              | decr (Const ("Transitive_Closure.trancl", _ ) $ r)  = (r,"r+")
              | decr r = (r,"r");
            val (rel,r) = decr rel;
        in SOME (a,b,rel,r) end
      | dec _ =  NONE
    in dec t end;

  end); (* struct *)

change_simpset (fn ss => ss
  addSolver (mk_solver "Trancl" (fn _ => Trancl_Tac.trancl_tac))
  addSolver (mk_solver "Rtrancl" (fn _ => Trancl_Tac.rtrancl_tac)));

*}

(* Optional methods

method_setup trancl =
  {* Method.no_args (Method.SIMPLE_METHOD' HEADGOAL (trancl_tac)) *}
  {* simple transitivity reasoner *}
method_setup rtrancl =
  {* Method.no_args (Method.SIMPLE_METHOD' HEADGOAL (rtrancl_tac)) *}
  {* simple transitivity reasoner *}

*)

end
