(* Author: Tobias Nipkow *)

theory VCG imports Hoare begin

subsection "Verification Conditions"

text{* Annotated commands: commands where loops are annotated with
invariants. *}

datatype acom =
  Askip                  ("SKIP") |
  Aassign vname aexp     ("(_ ::= _)" [1000, 61] 61) |
  Aseq   acom acom       ("_;;/ _"  [60, 61] 60) |
  Aif bexp acom acom     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61) |
  Awhile assn bexp acom  ("({_}/ WHILE _/ DO _)"  [0, 0, 61] 61)


text{* Strip annotations: *}

fun strip :: "acom \<Rightarrow> com" where
"strip SKIP = com.SKIP" |
"strip (x ::= a) = (x ::= a)" |
"strip (C\<^isub>1;; C\<^isub>2) = (strip C\<^isub>1;; strip C\<^isub>2)" |
"strip (IF b THEN C\<^isub>1 ELSE C\<^isub>2) = (IF b THEN strip C\<^isub>1 ELSE strip C\<^isub>2)" |
"strip ({_} WHILE b DO C) = (WHILE b DO strip C)"

text{* Weakest precondition from annotated commands: *}

fun pre :: "acom \<Rightarrow> assn \<Rightarrow> assn" where
"pre SKIP Q = Q" |
"pre (x ::= a) Q = (\<lambda>s. Q(s(x := aval a s)))" |
"pre (C\<^isub>1;; C\<^isub>2) Q = pre C\<^isub>1 (pre C\<^isub>2 Q)" |
"pre (IF b THEN C\<^isub>1 ELSE C\<^isub>2) Q =
  (\<lambda>s. if bval b s then pre C\<^isub>1 Q s else pre C\<^isub>2 Q s)" |
"pre ({I} WHILE b DO C) Q = I"

text{* Verification condition: *}

fun vc :: "acom \<Rightarrow> assn \<Rightarrow> assn" where
"vc SKIP Q = (\<lambda>s. True)" |
"vc (x ::= a) Q = (\<lambda>s. True)" |
"vc (C\<^isub>1;; C\<^isub>2) Q = (\<lambda>s. vc C\<^isub>1 (pre C\<^isub>2 Q) s \<and> vc C\<^isub>2 Q s)" |
"vc (IF b THEN C\<^isub>1 ELSE C\<^isub>2) Q = (\<lambda>s. vc C\<^isub>1 Q s \<and> vc C\<^isub>2 Q s)" |
"vc ({I} WHILE b DO C) Q =
  (\<lambda>s. (I s \<and> \<not> bval b s \<longrightarrow> Q s) \<and>
       (I s \<and> bval b s \<longrightarrow> pre C I s) \<and>
       vc C I s)"


text {* Soundness: *}

lemma vc_sound: "\<forall>s. vc C Q s \<Longrightarrow> \<turnstile> {pre C Q} strip C {Q}"
proof(induction C arbitrary: Q)
  case (Awhile I b C)
  show ?case
  proof(simp, rule While')
    from `\<forall>s. vc (Awhile I b C) Q s`
    have vc: "\<forall>s. vc C I s" and IQ: "\<forall>s. I s \<and> \<not> bval b s \<longrightarrow> Q s" and
         pre: "\<forall>s. I s \<and> bval b s \<longrightarrow> pre C I s" by simp_all
    have "\<turnstile> {pre C I} strip C {I}" by(rule Awhile.IH[OF vc])
    with pre show "\<turnstile> {\<lambda>s. I s \<and> bval b s} strip C {I}"
      by(rule strengthen_pre)
    show "\<forall>s. I s \<and> \<not>bval b s \<longrightarrow> Q s" by(rule IQ)
  qed
qed (auto intro: hoare.conseq)

corollary vc_sound':
  "\<lbrakk> \<forall>s. vc C Q s; \<forall>s. P s \<longrightarrow> pre C Q s \<rbrakk> \<Longrightarrow> \<turnstile> {P} strip C {Q}"
by (metis strengthen_pre vc_sound)


text{* Completeness: *}

lemma pre_mono:
  "\<forall>s. P s \<longrightarrow> P' s \<Longrightarrow> pre C P s \<Longrightarrow> pre C P' s"
proof (induction C arbitrary: P P' s)
  case Aseq thus ?case by simp metis
qed simp_all

lemma vc_mono:
  "\<forall>s. P s \<longrightarrow> P' s \<Longrightarrow> vc C P s \<Longrightarrow> vc C P' s"
proof(induction C arbitrary: P P')
  case Aseq thus ?case by simp (metis pre_mono)
qed simp_all

lemma vc_complete:
 "\<turnstile> {P}c{Q} \<Longrightarrow> \<exists>C. strip C = c \<and> (\<forall>s. vc C Q s) \<and> (\<forall>s. P s \<longrightarrow> pre C Q s)"
  (is "_ \<Longrightarrow> \<exists>C. ?G P c Q C")
proof (induction rule: hoare.induct)
  case Skip
  show ?case (is "\<exists>C. ?C C")
  proof show "?C Askip" by simp qed
next
  case (Assign P a x)
  show ?case (is "\<exists>C. ?C C")
  proof show "?C(Aassign x a)" by simp qed
next
  case (Seq P c1 Q c2 R)
  from Seq.IH obtain C1 where ih1: "?G P c1 Q C1" by blast
  from Seq.IH obtain C2 where ih2: "?G Q c2 R C2" by blast
  show ?case (is "\<exists>C. ?C C")
  proof
    show "?C(Aseq C1 C2)"
      using ih1 ih2 by (fastforce elim!: pre_mono vc_mono)
  qed
next
  case (If P b c1 Q c2)
  from If.IH obtain C1 where ih1: "?G (\<lambda>s. P s \<and> bval b s) c1 Q C1"
    by blast
  from If.IH obtain C2 where ih2: "?G (\<lambda>s. P s \<and> \<not>bval b s) c2 Q C2"
    by blast
  show ?case (is "\<exists>C. ?C C")
  proof
    show "?C(Aif b C1 C2)" using ih1 ih2 by simp
  qed
next
  case (While P b c)
  from While.IH obtain C where ih: "?G (\<lambda>s. P s \<and> bval b s) c P C" by blast
  show ?case (is "\<exists>C. ?C C")
  proof show "?C(Awhile P b C)" using ih by simp qed
next
  case conseq thus ?case by(fast elim!: pre_mono vc_mono)
qed

end
