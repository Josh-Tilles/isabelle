(*  Title:      HOL/Finite_Set.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Lawrence C Paulson and Markus Wenzel
                Additions by Jeremy Avigad in Feb 2004

FIXME split up, get rid of LC, define foldSet f g e (instead of just f)

Possible improvements: simplify card lemmas using the card_eq_setsum.
Unfortunately it appears necessary to define card before foldSet
because the uniqueness proof of foldSet uses card (but only very
elementary properties).
*)

header {* Finite sets *}

theory Finite_Set
imports Divides Power Inductive
begin

subsection {* Collection of finite sets *}

consts Finites :: "'a set set"
syntax
  finite :: "'a set => bool"
translations
  "finite A" == "A : Finites"

inductive Finites
  intros
    emptyI [simp, intro!]: "{} : Finites"
    insertI [simp, intro!]: "A : Finites ==> insert a A : Finites"

axclass finite \<subseteq> type
  finite: "finite UNIV"

lemma ex_new_if_finite: -- "does not depend on def of finite at all"
  assumes "\<not> finite (UNIV :: 'a set)" and "finite A"
  shows "\<exists>a::'a. a \<notin> A"
proof -
  from prems have "A \<noteq> UNIV" by blast
  thus ?thesis by blast
qed

lemma finite_induct [case_names empty insert, induct set: Finites]:
  "finite F ==>
    P {} ==> (!!x F. finite F ==> x \<notin> F ==> P F ==> P (insert x F)) ==> P F"
  -- {* Discharging @{text "x \<notin> F"} entails extra work. *}
proof -
  assume "P {}" and
    insert: "!!x F. finite F ==> x \<notin> F ==> P F ==> P (insert x F)"
  assume "finite F"
  thus "P F"
  proof induct
    show "P {}" .
    fix x F assume F: "finite F" and P: "P F"
    show "P (insert x F)"
    proof cases
      assume "x \<in> F"
      hence "insert x F = F" by (rule insert_absorb)
      with P show ?thesis by (simp only:)
    next
      assume "x \<notin> F"
      from F this P show ?thesis by (rule insert)
    qed
  qed
qed

lemma finite_subset_induct [consumes 2, case_names empty insert]:
  "finite F ==> F \<subseteq> A ==>
    P {} ==> (!!a F. finite F ==> a \<in> A ==> a \<notin> F ==> P F ==> P (insert a F)) ==>
    P F"
proof -
  assume "P {}" and insert:
    "!!a F. finite F ==> a \<in> A ==> a \<notin> F ==> P F ==> P (insert a F)"
  assume "finite F"
  thus "F \<subseteq> A ==> P F"
  proof induct
    show "P {}" .
    fix x F assume "finite F" and "x \<notin> F"
      and P: "F \<subseteq> A ==> P F" and i: "insert x F \<subseteq> A"
    show "P (insert x F)"
    proof (rule insert)
      from i show "x \<in> A" by blast
      from i have "F \<subseteq> A" by blast
      with P show "P F" .
    qed
  qed
qed

lemma finite_UnI: "finite F ==> finite G ==> finite (F Un G)"
  -- {* The union of two finite sets is finite. *}
  by (induct set: Finites) simp_all

lemma finite_subset: "A \<subseteq> B ==> finite B ==> finite A"
  -- {* Every subset of a finite set is finite. *}
proof -
  assume "finite B"
  thus "!!A. A \<subseteq> B ==> finite A"
  proof induct
    case empty
    thus ?case by simp
  next
    case (insert x F A)
    have A: "A \<subseteq> insert x F" and r: "A - {x} \<subseteq> F ==> finite (A - {x})" .
    show "finite A"
    proof cases
      assume x: "x \<in> A"
      with A have "A - {x} \<subseteq> F" by (simp add: subset_insert_iff)
      with r have "finite (A - {x})" .
      hence "finite (insert x (A - {x}))" ..
      also have "insert x (A - {x}) = A" by (rule insert_Diff)
      finally show ?thesis .
    next
      show "A \<subseteq> F ==> ?thesis" .
      assume "x \<notin> A"
      with A show "A \<subseteq> F" by (simp add: subset_insert_iff)
    qed
  qed
qed

lemma finite_Un [iff]: "finite (F Un G) = (finite F & finite G)"
  by (blast intro: finite_subset [of _ "X Un Y", standard] finite_UnI)

lemma finite_Int [simp, intro]: "finite F | finite G ==> finite (F Int G)"
  -- {* The converse obviously fails. *}
  by (blast intro: finite_subset)

lemma finite_insert [simp]: "finite (insert a A) = finite A"
  apply (subst insert_is_Un)
  apply (simp only: finite_Un, blast)
  done

lemma finite_Union[simp, intro]:
 "\<lbrakk> finite A; !!M. M \<in> A \<Longrightarrow> finite M \<rbrakk> \<Longrightarrow> finite(\<Union>A)"
by (induct rule:finite_induct) simp_all

lemma finite_empty_induct:
  "finite A ==>
  P A ==> (!!a A. finite A ==> a:A ==> P A ==> P (A - {a})) ==> P {}"
proof -
  assume "finite A"
    and "P A" and "!!a A. finite A ==> a:A ==> P A ==> P (A - {a})"
  have "P (A - A)"
  proof -
    fix c b :: "'a set"
    presume c: "finite c" and b: "finite b"
      and P1: "P b" and P2: "!!x y. finite y ==> x \<in> y ==> P y ==> P (y - {x})"
    from c show "c \<subseteq> b ==> P (b - c)"
    proof induct
      case empty
      from P1 show ?case by simp
    next
      case (insert x F)
      have "P (b - F - {x})"
      proof (rule P2)
        from _ b show "finite (b - F)" by (rule finite_subset) blast
        from insert show "x \<in> b - F" by simp
        from insert show "P (b - F)" by simp
      qed
      also have "b - F - {x} = b - insert x F" by (rule Diff_insert [symmetric])
      finally show ?case .
    qed
  next
    show "A \<subseteq> A" ..
  qed
  thus "P {}" by simp
qed

lemma finite_Diff [simp]: "finite B ==> finite (B - Ba)"
  by (rule Diff_subset [THEN finite_subset])

lemma finite_Diff_insert [iff]: "finite (A - insert a B) = finite (A - B)"
  apply (subst Diff_insert)
  apply (case_tac "a : A - B")
   apply (rule finite_insert [symmetric, THEN trans])
   apply (subst insert_Diff, simp_all)
  done


subsubsection {* Image and Inverse Image over Finite Sets *}

lemma finite_imageI[simp]: "finite F ==> finite (h ` F)"
  -- {* The image of a finite set is finite. *}
  by (induct set: Finites) simp_all

lemma finite_surj: "finite A ==> B <= f ` A ==> finite B"
  apply (frule finite_imageI)
  apply (erule finite_subset, assumption)
  done

lemma finite_range_imageI:
    "finite (range g) ==> finite (range (%x. f (g x)))"
  apply (drule finite_imageI, simp)
  done

lemma finite_imageD: "finite (f`A) ==> inj_on f A ==> finite A"
proof -
  have aux: "!!A. finite (A - {}) = finite A" by simp
  fix B :: "'a set"
  assume "finite B"
  thus "!!A. f`A = B ==> inj_on f A ==> finite A"
    apply induct
     apply simp
    apply (subgoal_tac "EX y:A. f y = x & F = f ` (A - {y})")
     apply clarify
     apply (simp (no_asm_use) add: inj_on_def)
     apply (blast dest!: aux [THEN iffD1], atomize)
    apply (erule_tac V = "ALL A. ?PP (A)" in thin_rl)
    apply (frule subsetD [OF equalityD2 insertI1], clarify)
    apply (rule_tac x = xa in bexI)
     apply (simp_all add: inj_on_image_set_diff)
    done
qed (rule refl)


lemma inj_vimage_singleton: "inj f ==> f-`{a} \<subseteq> {THE x. f x = a}"
  -- {* The inverse image of a singleton under an injective function
         is included in a singleton. *}
  apply (auto simp add: inj_on_def)
  apply (blast intro: the_equality [symmetric])
  done

lemma finite_vimageI: "[|finite F; inj h|] ==> finite (h -` F)"
  -- {* The inverse image of a finite set under an injective function
         is finite. *}
  apply (induct set: Finites, simp_all)
  apply (subst vimage_insert)
  apply (simp add: finite_Un finite_subset [OF inj_vimage_singleton])
  done


subsubsection {* The finite UNION of finite sets *}

lemma finite_UN_I: "finite A ==> (!!a. a:A ==> finite (B a)) ==> finite (UN a:A. B a)"
  by (induct set: Finites) simp_all

text {*
  Strengthen RHS to
  @{prop "((ALL x:A. finite (B x)) & finite {x. x:A & B x \<noteq> {}})"}?

  We'd need to prove
  @{prop "finite C ==> ALL A B. (UNION A B) <= C --> finite {x. x:A & B x \<noteq> {}}"}
  by induction. *}

lemma finite_UN [simp]: "finite A ==> finite (UNION A B) = (ALL x:A. finite (B x))"
  by (blast intro: finite_UN_I finite_subset)


subsubsection {* Sigma of finite sets *}

lemma finite_SigmaI [simp]:
    "finite A ==> (!!a. a:A ==> finite (B a)) ==> finite (SIGMA a:A. B a)"
  by (unfold Sigma_def) (blast intro!: finite_UN_I)

lemma finite_Prod_UNIV:
    "finite (UNIV::'a set) ==> finite (UNIV::'b set) ==> finite (UNIV::('a * 'b) set)"
  apply (subgoal_tac "(UNIV:: ('a * 'b) set) = Sigma UNIV (%x. UNIV)")
   apply (erule ssubst)
   apply (erule finite_SigmaI, auto)
  done

instance unit :: finite
proof
  have "finite {()}" by simp
  also have "{()} = UNIV" by auto
  finally show "finite (UNIV :: unit set)" .
qed

instance * :: (finite, finite) finite
proof
  show "finite (UNIV :: ('a \<times> 'b) set)"
  proof (rule finite_Prod_UNIV)
    show "finite (UNIV :: 'a set)" by (rule finite)
    show "finite (UNIV :: 'b set)" by (rule finite)
  qed
qed


subsubsection {* The powerset of a finite set *}

lemma finite_Pow_iff [iff]: "finite (Pow A) = finite A"
proof
  assume "finite (Pow A)"
  with _ have "finite ((%x. {x}) ` A)" by (rule finite_subset) blast
  thus "finite A" by (rule finite_imageD [unfolded inj_on_def]) simp
next
  assume "finite A"
  thus "finite (Pow A)"
    by induct (simp_all add: finite_UnI finite_imageI Pow_insert)
qed

lemma finite_converse [iff]: "finite (r^-1) = finite r"
  apply (subgoal_tac "r^-1 = (%(x,y). (y,x))`r")
   apply simp
   apply (rule iffI)
    apply (erule finite_imageD [unfolded inj_on_def])
    apply (simp split add: split_split)
   apply (erule finite_imageI)
  apply (simp add: converse_def image_def, auto)
  apply (rule bexI)
   prefer 2 apply assumption
  apply simp
  done


subsubsection {* Finiteness of transitive closure *}

text {* (Thanks to Sidi Ehmety) *}

lemma finite_Field: "finite r ==> finite (Field r)"
  -- {* A finite relation has a finite field (@{text "= domain \<union> range"}. *}
  apply (induct set: Finites)
   apply (auto simp add: Field_def Domain_insert Range_insert)
  done

lemma trancl_subset_Field2: "r^+ <= Field r \<times> Field r"
  apply clarify
  apply (erule trancl_induct)
   apply (auto simp add: Field_def)
  done

lemma finite_trancl: "finite (r^+) = finite r"
  apply auto
   prefer 2
   apply (rule trancl_subset_Field2 [THEN finite_subset])
   apply (rule finite_SigmaI)
    prefer 3
    apply (blast intro: r_into_trancl' finite_subset)
   apply (auto simp add: finite_Field)
  done

lemma finite_cartesian_product: "[| finite A; finite B |] ==>
    finite (A <*> B)"
  by (rule finite_SigmaI)


subsection {* Finite cardinality *}

text {*
  This definition, although traditional, is ugly to work with: @{text
  "card A == LEAST n. EX f. A = {f i | i. i < n}"}.  Therefore we have
  switched to an inductive one:
*}

consts cardR :: "('a set \<times> nat) set"

inductive cardR
  intros
    EmptyI: "({}, 0) : cardR"
    InsertI: "(A, n) : cardR ==> a \<notin> A ==> (insert a A, Suc n) : cardR"

constdefs
  card :: "'a set => nat"
  "card A == THE n. (A, n) : cardR"

inductive_cases cardR_emptyE: "({}, n) : cardR"
inductive_cases cardR_insertE: "(insert a A,n) : cardR"

lemma cardR_SucD: "(A, n) : cardR ==> a : A --> (EX m. n = Suc m)"
  by (induct set: cardR) simp_all

lemma cardR_determ_aux1:
    "(A, m): cardR ==> (!!n a. m = Suc n ==> a:A ==> (A - {a}, n) : cardR)"
  apply (induct set: cardR, auto)
  apply (simp add: insert_Diff_if, auto)
  apply (drule cardR_SucD)
  apply (blast intro!: cardR.intros)
  done

lemma cardR_determ_aux2: "(insert a A, Suc m) : cardR ==> a \<notin> A ==> (A, m) : cardR"
  by (drule cardR_determ_aux1) auto

lemma cardR_determ: "(A, m): cardR ==> (!!n. (A, n) : cardR ==> n = m)"
  apply (induct set: cardR)
   apply (safe elim!: cardR_emptyE cardR_insertE)
  apply (rename_tac B b m)
  apply (case_tac "a = b")
   apply (subgoal_tac "A = B")
    prefer 2 apply (blast elim: equalityE, blast)
  apply (subgoal_tac "EX C. A = insert b C & B = insert a C")
   prefer 2
   apply (rule_tac x = "A Int B" in exI)
   apply (blast elim: equalityE)
  apply (frule_tac A = B in cardR_SucD)
  apply (blast intro!: cardR.intros dest!: cardR_determ_aux2)
  done

lemma cardR_imp_finite: "(A, n) : cardR ==> finite A"
  by (induct set: cardR) simp_all

lemma finite_imp_cardR: "finite A ==> EX n. (A, n) : cardR"
  by (induct set: Finites) (auto intro!: cardR.intros)

lemma card_equality: "(A,n) : cardR ==> card A = n"
  by (unfold card_def) (blast intro: cardR_determ)

lemma card_empty [simp]: "card {} = 0"
  by (unfold card_def) (blast intro!: cardR.intros elim!: cardR_emptyE)

lemma card_insert_disjoint [simp]:
  "finite A ==> x \<notin> A ==> card (insert x A) = Suc(card A)"
proof -
  assume x: "x \<notin> A"
  hence aux: "!!n. ((insert x A, n) : cardR) = (EX m. (A, m) : cardR & n = Suc m)"
    apply (auto intro!: cardR.intros)
    apply (rule_tac A1 = A in finite_imp_cardR [THEN exE])
     apply (force dest: cardR_imp_finite)
    apply (blast intro!: cardR.intros intro: cardR_determ)
    done
  assume "finite A"
  thus ?thesis
    apply (simp add: card_def aux)
    apply (rule the_equality)
     apply (auto intro: finite_imp_cardR
       cong: conj_cong simp: card_def [symmetric] card_equality)
    done
qed

lemma card_0_eq [simp]: "finite A ==> (card A = 0) = (A = {})"
  apply auto
  apply (drule_tac a = x in mk_disjoint_insert, clarify)
  apply (rotate_tac -1, auto)
  done

lemma card_insert_if:
    "finite A ==> card (insert x A) = (if x:A then card A else Suc(card(A)))"
  by (simp add: insert_absorb)

lemma card_Suc_Diff1: "finite A ==> x: A ==> Suc (card (A - {x})) = card A"
apply(rule_tac t = A in insert_Diff [THEN subst], assumption)
apply(simp del:insert_Diff_single)
done

lemma card_Diff_singleton:
    "finite A ==> x: A ==> card (A - {x}) = card A - 1"
  by (simp add: card_Suc_Diff1 [symmetric])

lemma card_Diff_singleton_if:
    "finite A ==> card (A-{x}) = (if x : A then card A - 1 else card A)"
  by (simp add: card_Diff_singleton)

lemma card_insert: "finite A ==> card (insert x A) = Suc (card (A - {x}))"
  by (simp add: card_insert_if card_Suc_Diff1)

lemma card_insert_le: "finite A ==> card A <= card (insert x A)"
  by (simp add: card_insert_if)

lemma card_seteq: "finite B ==> (!!A. A <= B ==> card B <= card A ==> A = B)"
  apply (induct set: Finites, simp, clarify)
  apply (subgoal_tac "finite A & A - {x} <= F")
   prefer 2 apply (blast intro: finite_subset, atomize)
  apply (drule_tac x = "A - {x}" in spec)
  apply (simp add: card_Diff_singleton_if split add: split_if_asm)
  apply (case_tac "card A", auto)
  done

lemma psubset_card_mono: "finite B ==> A < B ==> card A < card B"
  apply (simp add: psubset_def linorder_not_le [symmetric])
  apply (blast dest: card_seteq)
  done

lemma card_mono: "finite B ==> A <= B ==> card A <= card B"
  apply (case_tac "A = B", simp)
  apply (simp add: linorder_not_less [symmetric])
  apply (blast dest: card_seteq intro: order_less_imp_le)
  done

lemma card_Un_Int: "finite A ==> finite B
    ==> card A + card B = card (A Un B) + card (A Int B)"
  apply (induct set: Finites, simp)
  apply (simp add: insert_absorb Int_insert_left)
  done

lemma card_Un_disjoint: "finite A ==> finite B
    ==> A Int B = {} ==> card (A Un B) = card A + card B"
  by (simp add: card_Un_Int)

lemma card_Diff_subset:
    "finite A ==> B <= A ==> card A - card B = card (A - B)"
  apply (subgoal_tac "(A - B) Un B = A")
   prefer 2 apply blast
  apply (rule nat_add_right_cancel [THEN iffD1])
  apply (rule card_Un_disjoint [THEN subst])
     apply (erule_tac [4] ssubst)
     prefer 3 apply blast
    apply (simp_all add: add_commute not_less_iff_le
      add_diff_inverse card_mono finite_subset)
  done

lemma card_Diff1_less: "finite A ==> x: A ==> card (A - {x}) < card A"
  apply (rule Suc_less_SucD)
  apply (simp add: card_Suc_Diff1)
  done

lemma card_Diff2_less:
    "finite A ==> x: A ==> y: A ==> card (A - {x} - {y}) < card A"
  apply (case_tac "x = y")
   apply (simp add: card_Diff1_less)
  apply (rule less_trans)
   prefer 2 apply (auto intro!: card_Diff1_less)
  done

lemma card_Diff1_le: "finite A ==> card (A - {x}) <= card A"
  apply (case_tac "x : A")
   apply (simp_all add: card_Diff1_less less_imp_le)
  done

lemma card_psubset: "finite B ==> A \<subseteq> B ==> card A < card B ==> A < B"
by (erule psubsetI, blast)

lemma insert_partition:
     "[| x \<notin> F; \<forall>c1\<in>insert x F. \<forall>c2 \<in> insert x F. c1 \<noteq> c2 --> c1 \<inter> c2 = {}|] 
      ==> x \<inter> \<Union> F = {}"
by auto

(* main cardinality theorem *)
lemma card_partition [rule_format]:
     "finite C ==>  
        finite (\<Union> C) -->  
        (\<forall>c\<in>C. card c = k) -->   
        (\<forall>c1 \<in> C. \<forall>c2 \<in> C. c1 \<noteq> c2 --> c1 \<inter> c2 = {}) -->  
        k * card(C) = card (\<Union> C)"
apply (erule finite_induct, simp)
apply (simp add: card_insert_disjoint card_Un_disjoint insert_partition 
       finite_subset [of _ "\<Union> (insert x F)"])
done


subsubsection {* Cardinality of image *}

lemma card_image_le: "finite A ==> card (f ` A) <= card A"
  apply (induct set: Finites, simp)
  apply (simp add: le_SucI finite_imageI card_insert_if)
  done

lemma card_image: "finite A ==> inj_on f A ==> card (f ` A) = card A"
by (induct set: Finites, simp_all)

lemma endo_inj_surj: "finite A ==> f ` A \<subseteq> A ==> inj_on f A ==> f ` A = A"
  by (simp add: card_seteq card_image)

lemma eq_card_imp_inj_on:
  "[| finite A; card(f ` A) = card A |] ==> inj_on f A"
apply(induct rule:finite_induct)
 apply simp
apply(frule card_image_le[where f = f])
apply(simp add:card_insert_if split:if_splits)
done

lemma inj_on_iff_eq_card:
  "finite A ==> inj_on f A = (card(f ` A) = card A)"
by(blast intro: card_image eq_card_imp_inj_on)


subsubsection {* Cardinality of the Powerset *}

lemma card_Pow: "finite A ==> card (Pow A) = Suc (Suc 0) ^ card A"  (* FIXME numeral 2 (!?) *)
  apply (induct set: Finites)
   apply (simp_all add: Pow_insert)
  apply (subst card_Un_disjoint, blast)
    apply (blast intro: finite_imageI, blast)
  apply (subgoal_tac "inj_on (insert x) (Pow F)")
   apply (simp add: card_image Pow_insert)
  apply (unfold inj_on_def)
  apply (blast elim!: equalityE)
  done

text {*
  \medskip Relates to equivalence classes.  Based on a theorem of
  F. Kamm�ller's.  The @{prop "finite C"} premise is redundant.
*}

lemma dvd_partition:
  "finite C ==> finite (Union C) ==>
    ALL c : C. k dvd card c ==>
    (ALL c1: C. ALL c2: C. c1 \<noteq> c2 --> c1 Int c2 = {}) ==>
  k dvd card (Union C)"
  apply (induct set: Finites, simp_all, clarify)
  apply (subst card_Un_disjoint)
  apply (auto simp add: dvd_add disjoint_eq_subset_Compl)
  done


subsection {* A fold functional for finite sets *}

text {*
  For @{text n} non-negative we have @{text "fold f e {x1, ..., xn} =
  f x1 (... (f xn e))"} where @{text f} is at least left-commutative.
*}

consts
  foldSet :: "('b => 'a => 'a) => 'a => ('b set \<times> 'a) set"

inductive "foldSet f e"
  intros
    emptyI [intro]: "({}, e) : foldSet f e"
    insertI [intro]: "x \<notin> A ==> (A, y) : foldSet f e ==> (insert x A, f x y) : foldSet f e"

inductive_cases empty_foldSetE [elim!]: "({}, x) : foldSet f e"

constdefs
  fold :: "('b => 'a => 'a) => 'a => 'b set => 'a"
  "fold f e A == THE x. (A, x) : foldSet f e"

lemma Diff1_foldSet: "(A - {x}, y) : foldSet f e ==> x: A ==> (A, f x y) : foldSet f e"
by (erule insert_Diff [THEN subst], rule foldSet.intros, auto)

lemma foldSet_imp_finite [simp]: "(A, x) : foldSet f e ==> finite A"
  by (induct set: foldSet) auto

lemma finite_imp_foldSet: "finite A ==> EX x. (A, x) : foldSet f e"
  by (induct set: Finites) auto


subsubsection {* Left-commutative operations *}

locale LC =
  fixes f :: "'b => 'a => 'a"    (infixl "\<cdot>" 70)
  assumes left_commute: "x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"

lemma (in LC) foldSet_determ_aux:
  "ALL A x. card A < n --> (A, x) : foldSet f e -->
    (ALL y. (A, y) : foldSet f e --> y = x)"
  apply (induct n)
   apply (auto simp add: less_Suc_eq)
  apply (erule foldSet.cases, blast)
  apply (erule foldSet.cases, blast, clarify)
  txt {* force simplification of @{text "card A < card (insert ...)"}. *}
  apply (erule rev_mp)
  apply (simp add: less_Suc_eq_le)
  apply (rule impI)
  apply (rename_tac Aa xa ya Ab xb yb, case_tac "xa = xb")
   apply (subgoal_tac "Aa = Ab")
    prefer 2 apply (blast elim!: equalityE, blast)
  txt {* case @{prop "xa \<notin> xb"}. *}
  apply (subgoal_tac "Aa - {xb} = Ab - {xa} & xb : Aa & xa : Ab")
   prefer 2 apply (blast elim!: equalityE, clarify)
  apply (subgoal_tac "Aa = insert xb Ab - {xa}")
   prefer 2 apply blast
  apply (subgoal_tac "card Aa <= card Ab")
   prefer 2
   apply (rule Suc_le_mono [THEN subst])
   apply (simp add: card_Suc_Diff1)
  apply (rule_tac A1 = "Aa - {xb}" and f1 = f in finite_imp_foldSet [THEN exE])
  apply (blast intro: foldSet_imp_finite finite_Diff)
  apply (frule (1) Diff1_foldSet)
  apply (subgoal_tac "ya = f xb x")
   prefer 2 apply (blast del: equalityCE)
  apply (subgoal_tac "(Ab - {xa}, x) : foldSet f e")
   prefer 2 apply simp
  apply (subgoal_tac "yb = f xa x")
   prefer 2 apply (blast del: equalityCE dest: Diff1_foldSet)
  apply (simp (no_asm_simp) add: left_commute)
  done

lemma (in LC) foldSet_determ:
  "(A, x) : foldSet f e ==> (A, y) : foldSet f e ==> y = x"
by (blast intro: foldSet_determ_aux [rule_format])

lemma (in LC) fold_equality: "(A, y) : foldSet f e ==> fold f e A = y"
  by (unfold fold_def) (blast intro: foldSet_determ)

lemma fold_empty [simp]: "fold f e {} = e"
  by (unfold fold_def) blast

lemma (in LC) fold_insert_aux: "x \<notin> A ==>
    ((insert x A, v) : foldSet f e) =
    (EX y. (A, y) : foldSet f e & v = f x y)"
  apply auto
  apply (rule_tac A1 = A and f1 = f in finite_imp_foldSet [THEN exE])
   apply (fastsimp dest: foldSet_imp_finite)
  apply (blast intro: foldSet_determ)
  done

lemma (in LC) fold_insert[simp]:
    "finite A ==> x \<notin> A ==> fold f e (insert x A) = f x (fold f e A)"
  apply (unfold fold_def)
  apply (simp add: fold_insert_aux)
  apply (rule the_equality)
  apply (auto intro: finite_imp_foldSet
    cong add: conj_cong simp add: fold_def [symmetric] fold_equality)
  done

corollary (in LC) fold_insert_def:
    "\<lbrakk> F \<equiv> fold f e; finite A; x \<notin> A \<rbrakk> \<Longrightarrow> F (insert x A) = f x (F A)"
by(simp)

lemma (in LC) fold_commute:
  "finite A ==> (!!e. f x (fold f e A) = fold f (f x e) A)"
  apply (induct set: Finites, simp)
  apply (simp add: left_commute)
  done

lemma (in LC) fold_nest_Un_Int:
  "finite A ==> finite B
    ==> fold f (fold f e B) A = fold f (fold f e (A Int B)) (A Un B)"
  apply (induct set: Finites, simp)
  apply (simp add: fold_commute Int_insert_left insert_absorb)
  done

lemma (in LC) fold_nest_Un_disjoint:
  "finite A ==> finite B ==> A Int B = {}
    ==> fold f e (A Un B) = fold f (fold f e B) A"
  by (simp add: fold_nest_Un_Int)

declare foldSet_imp_finite [simp del]
    empty_foldSetE [rule del]  foldSet.intros [rule del]
  -- {* Delete rules to do with @{text foldSet} relation. *}

lemma (in LC) o_closed: "LC(f o g)"
by(insert prems, simp add:LC_def)

lemma (in LC) fold_reindex:
assumes fin: "finite B"
shows "inj_on g B \<Longrightarrow> fold f e (g ` B) = fold (f \<circ> g) e B"
using fin apply (induct)
 apply simp
apply simp
apply(simp add:LC.fold_insert[OF o_closed])
done

subsubsection {* Commutative monoids *}

text {*
  We enter a more restrictive context, with @{text "f :: 'a => 'a => 'a"}
  instead of @{text "'b => 'a => 'a"}.
*}

locale ACf =
  fixes f :: "'a => 'a => 'a"    (infixl "\<cdot>" 70)
  assumes commute: "x \<cdot> y = y \<cdot> x"
    and assoc: "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"

locale ACe = ACf +
  fixes e :: 'a
  assumes ident [simp]: "x \<cdot> e = x"

lemma (in ACf) left_commute: "x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
proof -
  have "x \<cdot> (y \<cdot> z) = (y \<cdot> z) \<cdot> x" by (simp only: commute)
  also have "... = y \<cdot> (z \<cdot> x)" by (simp only: assoc)
  also have "z \<cdot> x = x \<cdot> z" by (simp only: commute)
  finally show ?thesis .
qed

corollary (in ACf) LC: "LC f"
by(simp add:LC_def left_commute)

lemmas (in ACf) AC = assoc commute left_commute

lemma (in ACe) left_ident [simp]: "e \<cdot> x = x"
proof -
  have "x \<cdot> e = x" by (rule ident)
  thus ?thesis by (subst commute)
qed

lemma (in ACe) fold_o_Un_Int:
  "finite A ==> finite B ==>
    fold (f o g) e A \<cdot> fold (f o g) e B =
    fold (f o g) e (A Un B) \<cdot> fold (f o g) e (A Int B)"
  apply (induct set: Finites, simp)
  apply (simp add: AC insert_absorb Int_insert_left
    LC.fold_insert [OF LC.intro])
  done

corollary (in ACe) fold_Un_Int:
  "finite A ==> finite B ==>
    fold f e A \<cdot> fold f e B = fold f e (A Un B) \<cdot> fold f e (A Int B)"
  by (rule fold_o_Un_Int[where g = id,simplified])

corollary (in ACe) fold_o_Un_disjoint:
  "finite A ==> finite B ==> A Int B = {} ==>
    fold (f o g) e (A Un B) = fold (f o g) e A \<cdot> fold (f o g) e B"
  by (simp add: fold_o_Un_Int)

corollary (in ACe) fold_Un_disjoint:
  "finite A ==> finite B ==> A Int B = {} ==>
    fold f e (A Un B) = fold f e A \<cdot> fold f e B"
  by (simp add: fold_Un_Int)

lemma (in ACe) fold_o_UN_disjoint:
  "\<lbrakk> finite I; ALL i:I. finite (A i);
     ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {} \<rbrakk>
   \<Longrightarrow> fold (f o g) e (UNION I A) =
       fold (f o (%i. fold (f o g) e (A i))) e I"
  apply (induct set: Finites, simp, atomize)
  apply (subgoal_tac "ALL i:F. x \<noteq> i")
   prefer 2 apply blast
  apply (subgoal_tac "A x Int UNION F A = {}")
   prefer 2 apply blast
  apply (simp add: fold_o_Un_disjoint LC.fold_insert[OF LC.o_closed[OF LC]])
  done

lemma (in ACf) fold_cong:
  "finite A \<Longrightarrow> (!!x. x:A ==> g x = h x) ==> fold (f o g) a A = fold (f o h) a A"
  apply (subgoal_tac "ALL C. C <= A --> (ALL x:C. g x = h x) --> fold (f o g) a C = fold (f o h) a C")
   apply simp
  apply (erule finite_induct, simp)
  apply (simp add: subset_insert_iff, clarify)
  apply (subgoal_tac "finite C")
   prefer 2 apply (blast dest: finite_subset [COMP swap_prems_rl])
  apply (subgoal_tac "C = insert x (C - {x})")
   prefer 2 apply blast
  apply (erule ssubst)
  apply (drule spec)
  apply (erule (1) notE impE)
  apply (fold o_def)
  apply (simp add: Ball_def LC.fold_insert[OF LC.o_closed[OF LC]]
              del: insert_Diff_single)
  done

lemma (in ACe) fold_o_Sigma: "finite A ==> ALL x:A. finite (B x) ==>
fold (f o (%x. fold (f o g x) e (B x))) e A =
fold (f o (split g)) e (SIGMA x:A. B x)"
apply (subst Sigma_def)
apply (subst fold_o_UN_disjoint)
   apply assumption
  apply simp
 apply blast
apply (erule fold_cong)
apply (subst fold_o_UN_disjoint)
   apply simp
  apply simp
 apply blast
apply (simp add: LC.fold_insert [OF LC.o_closed[OF LC]])
apply(simp add:o_def)
done

lemma (in ACe) fold_o_distrib: "finite A \<Longrightarrow>
   fold (f o (%x. f (g x) (h x))) e A =
   f (fold (f o g) e A) (fold (f o h) e A)"
apply (erule finite_induct)
 apply simp
apply(simp add: LC.fold_insert[OF LC.o_closed[OF LC]] del:o_apply)
apply(subgoal_tac "(%x. f(g x)) = (%u ua. f ua (g u))")
 prefer 2 apply(rule ext, rule ext, simp add:AC)
apply(subgoal_tac "(%x. f(h x)) = (%u ua. f ua (h u))")
 prefer 2 apply(rule ext, rule ext, simp add:AC)
apply (simp add:AC o_def)
done


subsection {* Generalized summation over a set *}

constdefs
  setsum :: "('a => 'b) => 'a set => 'b::comm_monoid_add"
  "setsum f A == if finite A then fold (op + o f) 0 A else 0"

text{* Now: lot's of fancy syntax. First, @{term "setsum (%x. e) A"} is
written @{text"\<Sum>x\<in>A. e"}. *}

syntax
  "_setsum" :: "idt => 'a set => 'b => 'b::comm_monoid_add"    ("(3SUM _:_. _)" [0, 51, 10] 10)
syntax (xsymbols)
  "_setsum" :: "idt => 'a set => 'b => 'b::comm_monoid_add"    ("(3\<Sum>_\<in>_. _)" [0, 51, 10] 10)
syntax (HTML output)
  "_setsum" :: "idt => 'a set => 'b => 'b::comm_monoid_add"    ("(3\<Sum>_\<in>_. _)" [0, 51, 10] 10)

translations -- {* Beware of argument permutation! *}
  "SUM i:A. b" == "setsum (%i. b) A"
  "\<Sum>i\<in>A. b" == "setsum (%i. b) A"

text{* Instead of @{term"\<Sum>x\<in>{x. P}. e"} we introduce the shorter
 @{text"\<Sum>x|P. e"}. *}

syntax
  "_qsetsum" :: "idt \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3SUM _ |/ _./ _)" [0,0,10] 10)
syntax (xsymbols)
  "_qsetsum" :: "idt \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3\<Sum>_ | (_)./ _)" [0,0,10] 10)
syntax (HTML output)
  "_qsetsum" :: "idt \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3\<Sum>_ | (_)./ _)" [0,0,10] 10)

translations
  "SUM x|P. t" => "setsum (%x. t) {x. P}"
  "\<Sum>x|P. t" => "setsum (%x. t) {x. P}"

print_translation {*
let
  fun setsum_tr' [Abs(x,Tx,t), Const ("Collect",_) $ Abs(y,Ty,P)] = 
    (if x<>y then raise Match
     else let val x' = Syntax.mark_bound x
              val t' = subst_bound(x',t)
              val P' = subst_bound(x',P)
          in Syntax.const "_qsetsum" $ Syntax.mark_bound x $ P' $ t' end)
in
[("setsum", setsum_tr')]
end
*}

text{* Instantiation of locales: *}

lemma ACf_add: "ACf (op + :: 'a::comm_monoid_add \<Rightarrow> 'a \<Rightarrow> 'a)"
by(fastsimp intro: ACf.intro add_assoc add_commute)

lemma ACe_add: "ACe (op +) (0::'a::comm_monoid_add)"
by(fastsimp intro: ACe.intro ACe_axioms.intro ACf_add)

corollary LC_add_o: "LC(op + o f :: 'a \<Rightarrow> 'b::comm_monoid_add \<Rightarrow> 'b)"
by(rule LC.o_closed[OF ACf.LC[OF ACf_add]])

lemma setsum_empty [simp]: "setsum f {} = 0"
  by (simp add: setsum_def)

lemma setsum_insert [simp]:
    "finite F ==> a \<notin> F ==> setsum f (insert a F) = f a + setsum f F"
  by (simp add: setsum_def LC.fold_insert [OF LC_add_o])

lemma setsum_reindex:
     "finite B ==> inj_on f B ==> setsum h (f ` B) = setsum (h \<circ> f) B"
by (simp add: setsum_def LC.fold_reindex[OF LC_add_o] o_assoc)

lemma setsum_reindex_id:
     "finite B ==> inj_on f B ==> setsum f B = setsum id (f ` B)"
by (auto simp add: setsum_reindex id_o)

lemma setsum_cong:
  "A = B ==> (!!x. x:B ==> f x = g x) ==> setsum f A = setsum g B"
by(fastsimp simp: setsum_def intro: ACf.fold_cong[OF ACf_add])

lemma setsum_reindex_cong:
     "[|finite A; inj_on f A; B = f ` A; !!a. g a = h (f a)|] 
      ==> setsum h B = setsum g A"
  by (simp add: setsum_reindex cong: setsum_cong)

lemma setsum_0: "setsum (%i. 0) A = 0"
  apply (case_tac "finite A")
   prefer 2 apply (simp add: setsum_def)
  apply (erule finite_induct, auto)
  done

lemma setsum_0': "ALL a:F. f a = 0 ==> setsum f F = 0"
  apply (subgoal_tac "setsum f F = setsum (%x. 0) F")
  apply (erule ssubst, rule setsum_0)
  apply (rule setsum_cong, auto)
  done

lemma card_eq_setsum: "finite A ==> card A = setsum (%x. 1) A"
  -- {* Could allow many @{text "card"} proofs to be simplified. *}
  by (induct set: Finites) auto

lemma setsum_Un_Int: "finite A ==> finite B
    ==> setsum g (A Un B) + setsum g (A Int B) = setsum g A + setsum g B"
  -- {* The reversed orientation looks more natural, but LOOPS as a simprule! *}
by(simp add: setsum_def ACe.fold_o_Un_Int[OF ACe_add,symmetric])

lemma setsum_Un_disjoint: "finite A ==> finite B
  ==> A Int B = {} ==> setsum g (A Un B) = setsum g A + setsum g B"
by (subst setsum_Un_Int [symmetric], auto)

lemma setsum_UN_disjoint:
    "finite I ==> (ALL i:I. finite (A i)) ==>
        (ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {}) ==>
      setsum f (UNION I A) = setsum (%i. setsum f (A i)) I"
by(simp add: setsum_def ACe.fold_o_UN_disjoint[OF ACe_add] cong: setsum_cong)


lemma setsum_Union_disjoint:
  "finite C ==> (ALL A:C. finite A) ==>
        (ALL A:C. ALL B:C. A \<noteq> B --> A Int B = {}) ==>
      setsum f (Union C) = setsum (setsum f) C"
  apply (frule setsum_UN_disjoint [of C id f])
  apply (unfold Union_def id_def, assumption+)
  done

lemma setsum_Sigma: "finite A ==> ALL x:A. finite (B x) ==>
    (\<Sum>x\<in>A. (\<Sum>y\<in>B x. f x y)) =
    (\<Sum>z\<in>(SIGMA x:A. B x). f (fst z) (snd z))"
by(simp add:setsum_def ACe.fold_o_Sigma[OF ACe_add] split_def cong:setsum_cong)

lemma setsum_cartesian_product: "finite A ==> finite B ==>
    (\<Sum>x\<in>A. (\<Sum>y\<in>B. f x y)) =
    (\<Sum>z\<in>A <*> B. f (fst z) (snd z))"
  by (erule setsum_Sigma, auto)

lemma setsum_addf: "setsum (%x. f x + g x) A = (setsum f A + setsum g A)"
by(simp add:setsum_def ACe.fold_o_distrib[OF ACe_add])


subsubsection {* Properties in more restricted classes of structures *}

lemma setsum_SucD: "setsum f A = Suc n ==> EX a:A. 0 < f a"
  apply (case_tac "finite A")
   prefer 2 apply (simp add: setsum_def)
  apply (erule rev_mp)
  apply (erule finite_induct, auto)
  done

lemma setsum_eq_0_iff [simp]:
    "finite F ==> (setsum f F = 0) = (ALL a:F. f a = (0::nat))"
  by (induct set: Finites) auto

lemma setsum_constant_nat:
    "finite A ==> (\<Sum>x\<in>A. y) = (card A) * y"
  -- {* Generalized to any @{text comm_semiring_1_cancel} in
        @{text IntDef} as @{text setsum_constant}. *}
  by (erule finite_induct, auto)

lemma setsum_Un: "finite A ==> finite B ==>
    (setsum f (A Un B) :: nat) = setsum f A + setsum f B - setsum f (A Int B)"
  -- {* For the natural numbers, we have subtraction. *}
  by (subst setsum_Un_Int [symmetric], auto simp add: ring_eq_simps)

lemma setsum_Un_ring: "finite A ==> finite B ==>
    (setsum f (A Un B) :: 'a :: ab_group_add) =
      setsum f A + setsum f B - setsum f (A Int B)"
  by (subst setsum_Un_Int [symmetric], auto simp add: ring_eq_simps)

lemma setsum_diff1_nat: "(setsum f (A - {a}) :: nat) =
    (if a:A then setsum f A - f a else setsum f A)"
  apply (case_tac "finite A")
   prefer 2 apply (simp add: setsum_def)
  apply (erule finite_induct)
   apply (auto simp add: insert_Diff_if)
  apply (drule_tac a = a in mk_disjoint_insert, auto)
  done

lemma setsum_diff1: "finite A \<Longrightarrow>
  (setsum f (A - {a}) :: ('a::{pordered_ab_group_add})) =
  (if a:A then setsum f A - f a else setsum f A)"
  by (erule finite_induct) (auto simp add: insert_Diff_if)

(* By Jeremy Siek: *)

lemma setsum_diff_nat: 
  assumes finB: "finite B"
  shows "B \<subseteq> A \<Longrightarrow> (setsum f (A - B) :: nat) = (setsum f A) - (setsum f B)"
using finB
proof (induct)
  show "setsum f (A - {}) = (setsum f A) - (setsum f {})" by simp
next
  fix F x assume finF: "finite F" and xnotinF: "x \<notin> F"
    and xFinA: "insert x F \<subseteq> A"
    and IH: "F \<subseteq> A \<Longrightarrow> setsum f (A - F) = setsum f A - setsum f F"
  from xnotinF xFinA have xinAF: "x \<in> (A - F)" by simp
  from xinAF have A: "setsum f ((A - F) - {x}) = setsum f (A - F) - f x"
    by (simp add: setsum_diff1_nat)
  from xFinA have "F \<subseteq> A" by simp
  with IH have "setsum f (A - F) = setsum f A - setsum f F" by simp
  with A have B: "setsum f ((A - F) - {x}) = setsum f A - setsum f F - f x"
    by simp
  from xnotinF have "A - insert x F = (A - F) - {x}" by auto
  with B have C: "setsum f (A - insert x F) = setsum f A - setsum f F - f x"
    by simp
  from finF xnotinF have "setsum f (insert x F) = setsum f F + f x" by simp
  with C have "setsum f (A - insert x F) = setsum f A - setsum f (insert x F)"
    by simp
  thus "setsum f (A - insert x F) = setsum f A - setsum f (insert x F)" by simp
qed

lemma setsum_diff:
  assumes le: "finite A" "B \<subseteq> A"
  shows "setsum f (A - B) = setsum f A - ((setsum f B)::('a::pordered_ab_group_add))"
proof -
  from le have finiteB: "finite B" using finite_subset by auto
  show ?thesis using finiteB le
    proof (induct)
      case empty
      thus ?case by auto
    next
      case (insert x F)
      thus ?case using le finiteB 
	by (simp add: Diff_insert[where a=x and B=F] setsum_diff1 insert_absorb)
    qed
  qed

lemma setsum_mono:
  assumes le: "\<And>i. i\<in>K \<Longrightarrow> f (i::'a) \<le> ((g i)::('b::{comm_monoid_add, pordered_ab_semigroup_add}))"
  shows "(\<Sum>i\<in>K. f i) \<le> (\<Sum>i\<in>K. g i)"
proof (cases "finite K")
  case True
  thus ?thesis using le
  proof (induct)
    case empty
    thus ?case by simp
  next
    case insert
    thus ?case using add_mono 
      by force
  qed
next
  case False
  thus ?thesis
    by (simp add: setsum_def)
qed

lemma setsum_negf: "finite A ==> setsum (%x. - (f x)::'a::ab_group_add) A =
  - setsum f A"
  by (induct set: Finites, auto)

lemma setsum_subtractf: "finite A ==> setsum (%x. ((f x)::'a::ab_group_add) - g x) A =
  setsum f A - setsum g A"
  by (simp add: diff_minus setsum_addf setsum_negf)

lemma setsum_nonneg: "[| finite A;
    \<forall>x \<in> A. (0::'a::{pordered_ab_semigroup_add, comm_monoid_add}) \<le> f x |] ==>
    0 \<le> setsum f A";
  apply (induct set: Finites, auto)
  apply (subgoal_tac "0 + 0 \<le> f x + setsum f F", simp)
  apply (blast intro: add_mono)
  done

lemma setsum_nonpos: "[| finite A;
    \<forall>x \<in> A. f x \<le> (0::'a::{pordered_ab_semigroup_add, comm_monoid_add}) |] ==>
    setsum f A \<le> 0";
  apply (induct set: Finites, auto)
  apply (subgoal_tac "f x + setsum f F \<le> 0 + 0", simp)
  apply (blast intro: add_mono)
  done

lemma setsum_mult: 
  fixes f :: "'a => ('b::semiring_0_cancel)"
  shows "r * setsum f A = setsum (%n. r * f n) A"
proof (cases "finite A")
  case True
  thus ?thesis
  proof (induct)
    case empty thus ?case by simp
  next
    case (insert x A) thus ?case by (simp add: right_distrib)
  qed
next
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma setsum_abs: 
  fixes f :: "'a => ('b::lordered_ab_group_abs)"
  assumes fin: "finite A" 
  shows "abs (setsum f A) \<le> setsum (%i. abs(f i)) A"
using fin 
proof (induct) 
  case empty thus ?case by simp
next
  case (insert x A)
  thus ?case by (auto intro: abs_triangle_ineq order_trans)
qed

lemma setsum_abs_ge_zero: 
  fixes f :: "'a => ('b::lordered_ab_group_abs)"
  assumes fin: "finite A" 
  shows "0 \<le> setsum (%i. abs(f i)) A"
using fin 
proof (induct) 
  case empty thus ?case by simp
next
  case (insert x A) thus ?case by (auto intro: order_trans)
qed

subsubsection {* Cardinality of unions and Sigma sets *}

lemma card_UN_disjoint:
    "finite I ==> (ALL i:I. finite (A i)) ==>
        (ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {}) ==>
      card (UNION I A) = setsum (%i. card (A i)) I"
  apply (subst card_eq_setsum)
  apply (subst finite_UN, assumption+)
  apply (subgoal_tac
           "setsum (%i. card (A i)) I = setsum (%i. (setsum (%x. 1) (A i))) I")
  apply (simp add: setsum_UN_disjoint) 
  apply (simp add: setsum_constant_nat cong: setsum_cong) 
  done

lemma card_Union_disjoint:
  "finite C ==> (ALL A:C. finite A) ==>
        (ALL A:C. ALL B:C. A \<noteq> B --> A Int B = {}) ==>
      card (Union C) = setsum card C"
  apply (frule card_UN_disjoint [of C id])
  apply (unfold Union_def id_def, assumption+)
  done

lemma SigmaI_insert: "y \<notin> A ==>
  (SIGMA x:(insert y A). B x) = (({y} <*> (B y)) \<union> (SIGMA x: A. B x))"
  by auto

lemma card_cartesian_product_singleton: "finite A ==>
    card({x} <*> A) = card(A)"
  apply (subgoal_tac "inj_on (%y .(x,y)) A")
  apply (frule card_image, assumption)
  apply (subgoal_tac "(Pair x ` A) = {x} <*> A")
  apply (auto simp add: inj_on_def)
  done

lemma card_SigmaI [rule_format,simp]: "finite A ==>
  (ALL a:A. finite (B a)) -->
  card (SIGMA x: A. B x) = (\<Sum>a\<in>A. card (B a))"
  apply (erule finite_induct, auto)
  apply (subst SigmaI_insert, assumption)
  apply (subst card_Un_disjoint)
  apply (auto intro: finite_SigmaI simp add: card_cartesian_product_singleton)
  done

lemma card_cartesian_product:
     "[| finite A; finite B |] ==> card (A <*> B) = card(A) * card(B)"
  by (simp add: setsum_constant_nat)



subsection {* Generalized product over a set *}

constdefs
  setprod :: "('a => 'b) => 'a set => 'b::comm_monoid_mult"
  "setprod f A == if finite A then fold (op * o f) 1 A else 1"

syntax
  "_setprod" :: "idt => 'a set => 'b => 'b::comm_monoid_mult"  ("(3\<Prod>_:_. _)" [0, 51, 10] 10)

syntax (xsymbols)
  "_setprod" :: "idt => 'a set => 'b => 'b::comm_monoid_mult"  ("(3\<Prod>_\<in>_. _)" [0, 51, 10] 10)
syntax (HTML output)
  "_setprod" :: "idt => 'a set => 'b => 'b::comm_monoid_mult"  ("(3\<Prod>_\<in>_. _)" [0, 51, 10] 10)
translations
  "\<Prod>i:A. b" == "setprod (%i. b) A"  -- {* Beware of argument permutation! *}

text{* Instantiation of locales: *}

lemma ACf_mult: "ACf (op * :: 'a::comm_monoid_mult \<Rightarrow> 'a \<Rightarrow> 'a)"
by(fast intro: ACf.intro mult_assoc ab_semigroup_mult.mult_commute)

lemma ACe_mult: "ACe (op *) (1::'a::comm_monoid_mult)"
by(fastsimp intro: ACe.intro ACe_axioms.intro ACf_mult)

corollary LC_mult_o: "LC(op * o f :: 'a \<Rightarrow> 'b::comm_monoid_mult \<Rightarrow> 'b)"
by(rule LC.o_closed[OF ACf.LC[OF ACf_mult]])

lemma setprod_empty [simp]: "setprod f {} = 1"
  by (auto simp add: setprod_def)

lemma setprod_insert [simp]: "[| finite A; a \<notin> A |] ==>
    setprod f (insert a A) = f a * setprod f A"
by (simp add: setprod_def LC.fold_insert [OF LC_mult_o])

lemma setprod_reindex:
     "finite B ==> inj_on f B ==> setprod h (f ` B) = setprod (h \<circ> f) B"
by (simp add: setprod_def LC.fold_reindex[OF LC_mult_o] o_assoc)

lemma setprod_reindex_id: "finite B ==> inj_on f B ==>
    setprod f B = setprod id (f ` B)"
by (auto simp add: setprod_reindex id_o)

lemma setprod_cong:
  "A = B ==> (!!x. x:B ==> f x = g x) ==> setprod f A = setprod g B"
by(fastsimp simp: setprod_def intro: ACf.fold_cong[OF ACf_mult])

lemma setprod_reindex_cong: "finite A ==> inj_on f A ==>
    B = f ` A ==> g = h \<circ> f ==> setprod h B = setprod g A"
  by (frule setprod_reindex, assumption, simp)


lemma setprod_1: "setprod (%i. 1) A = 1"
  apply (case_tac "finite A")
  apply (erule finite_induct, auto simp add: mult_ac)
  apply (simp add: setprod_def)
  done

lemma setprod_1': "ALL a:F. f a = 1 ==> setprod f F = 1"
  apply (subgoal_tac "setprod f F = setprod (%x. 1) F")
  apply (erule ssubst, rule setprod_1)
  apply (rule setprod_cong, auto)
  done

lemma setprod_Un_Int: "finite A ==> finite B
    ==> setprod g (A Un B) * setprod g (A Int B) = setprod g A * setprod g B"
by(simp add: setprod_def ACe.fold_o_Un_Int[OF ACe_mult,symmetric])

lemma setprod_Un_disjoint: "finite A ==> finite B
  ==> A Int B = {} ==> setprod g (A Un B) = setprod g A * setprod g B"
by (subst setprod_Un_Int [symmetric], auto)

lemma setprod_UN_disjoint:
    "finite I ==> (ALL i:I. finite (A i)) ==>
        (ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {}) ==>
      setprod f (UNION I A) = setprod (%i. setprod f (A i)) I"
by(simp add: setprod_def ACe.fold_o_UN_disjoint[OF ACe_mult] cong: setprod_cong)

lemma setprod_Union_disjoint:
  "finite C ==> (ALL A:C. finite A) ==>
        (ALL A:C. ALL B:C. A \<noteq> B --> A Int B = {}) ==>
      setprod f (Union C) = setprod (setprod f) C"
  apply (frule setprod_UN_disjoint [of C id f])
  apply (unfold Union_def id_def, assumption+)
  done

lemma setprod_Sigma: "finite A ==> ALL x:A. finite (B x) ==>
    (\<Prod>x:A. (\<Prod>y: B x. f x y)) =
    (\<Prod>z:(SIGMA x:A. B x). f (fst z) (snd z))"
by(simp add:setprod_def ACe.fold_o_Sigma[OF ACe_mult] split_def cong:setprod_cong)

lemma setprod_cartesian_product: "finite A ==> finite B ==>
    (\<Prod>x:A. (\<Prod>y: B. f x y)) =
    (\<Prod>z:(A <*> B). f (fst z) (snd z))"
  by (erule setprod_Sigma, auto)

lemma setprod_timesf:
  "setprod (%x. f x * g x) A = (setprod f A * setprod g A)"
by(simp add:setprod_def ACe.fold_o_distrib[OF ACe_mult])


subsubsection {* Properties in more restricted classes of structures *}

lemma setprod_eq_1_iff [simp]:
    "finite F ==> (setprod f F = 1) = (ALL a:F. f a = (1::nat))"
  by (induct set: Finites) auto

lemma setprod_constant: "finite A ==> (\<Prod>x: A. (y::'a::recpower)) = y^(card A)"
  apply (erule finite_induct)
  apply (auto simp add: power_Suc)
  done

lemma setprod_zero:
     "finite A ==> EX x: A. f x = (0::'a::comm_semiring_1_cancel) ==> setprod f A = 0"
  apply (induct set: Finites, force, clarsimp)
  apply (erule disjE, auto)
  done

lemma setprod_nonneg [rule_format]:
     "(ALL x: A. (0::'a::ordered_idom) \<le> f x) --> 0 \<le> setprod f A"
  apply (case_tac "finite A")
  apply (induct set: Finites, force, clarsimp)
  apply (subgoal_tac "0 * 0 \<le> f x * setprod f F", force)
  apply (rule mult_mono, assumption+)
  apply (auto simp add: setprod_def)
  done

lemma setprod_pos [rule_format]: "(ALL x: A. (0::'a::ordered_idom) < f x)
     --> 0 < setprod f A"
  apply (case_tac "finite A")
  apply (induct set: Finites, force, clarsimp)
  apply (subgoal_tac "0 * 0 < f x * setprod f F", force)
  apply (rule mult_strict_mono, assumption+)
  apply (auto simp add: setprod_def)
  done

lemma setprod_nonzero [rule_format]:
    "(ALL x y. (x::'a::comm_semiring_1_cancel) * y = 0 --> x = 0 | y = 0) ==>
      finite A ==> (ALL x: A. f x \<noteq> (0::'a)) --> setprod f A \<noteq> 0"
  apply (erule finite_induct, auto)
  done

lemma setprod_zero_eq:
    "(ALL x y. (x::'a::comm_semiring_1_cancel) * y = 0 --> x = 0 | y = 0) ==>
     finite A ==> (setprod f A = (0::'a)) = (EX x: A. f x = 0)"
  apply (insert setprod_zero [of A f] setprod_nonzero [of A f], blast)
  done

lemma setprod_nonzero_field:
    "finite A ==> (ALL x: A. f x \<noteq> (0::'a::field)) ==> setprod f A \<noteq> 0"
  apply (rule setprod_nonzero, auto)
  done

lemma setprod_zero_eq_field:
    "finite A ==> (setprod f A = (0::'a::field)) = (EX x: A. f x = 0)"
  apply (rule setprod_zero_eq, auto)
  done

lemma setprod_Un: "finite A ==> finite B ==> (ALL x: A Int B. f x \<noteq> 0) ==>
    (setprod f (A Un B) :: 'a ::{field})
      = setprod f A * setprod f B / setprod f (A Int B)"
  apply (subst setprod_Un_Int [symmetric], auto)
  apply (subgoal_tac "finite (A Int B)")
  apply (frule setprod_nonzero_field [of "A Int B" f], assumption)
  apply (subst times_divide_eq_right [THEN sym], auto simp add: divide_self)
  done

lemma setprod_diff1: "finite A ==> f a \<noteq> 0 ==>
    (setprod f (A - {a}) :: 'a :: {field}) =
      (if a:A then setprod f A / f a else setprod f A)"
  apply (erule finite_induct)
   apply (auto simp add: insert_Diff_if)
  apply (subgoal_tac "f a * setprod f F / f a = setprod f F * f a / f a")
  apply (erule ssubst)
  apply (subst times_divide_eq_right [THEN sym])
  apply (auto simp add: mult_ac times_divide_eq_right divide_self)
  done

lemma setprod_inversef: "finite A ==>
    ALL x: A. f x \<noteq> (0::'a::{field,division_by_zero}) ==>
      setprod (inverse \<circ> f) A = inverse (setprod f A)"
  apply (erule finite_induct)
  apply (simp, simp)
  done

lemma setprod_dividef:
     "[|finite A;
        \<forall>x \<in> A. g x \<noteq> (0::'a::{field,division_by_zero})|]
      ==> setprod (%x. f x / g x) A = setprod f A / setprod g A"
  apply (subgoal_tac
         "setprod (%x. f x / g x) A = setprod (%x. f x * (inverse \<circ> g) x) A")
  apply (erule ssubst)
  apply (subst divide_inverse)
  apply (subst setprod_timesf)
  apply (subst setprod_inversef, assumption+, rule refl)
  apply (rule setprod_cong, rule refl)
  apply (subst divide_inverse, auto)
  done


subsection{* Min and Max of finite linearly ordered sets *}

consts
  foldSet1 :: "('a => 'a => 'a) => ('a set \<times> 'a) set"

inductive "foldSet1 f"
intros
fold1_singletonI [intro]: "({a}, a) : foldSet1 f"
fold1_insertI [intro]:
 "\<lbrakk> (A, x) : foldSet1 f; a \<notin> A; A \<noteq> {} \<rbrakk>
  \<Longrightarrow> (insert a A, f a x) : foldSet1 f"

constdefs
  fold1 :: "('a => 'a => 'a) => 'a set => 'a"
  "fold1 f A == THE x. (A, x) : foldSet1 f"

lemma foldSet1_nonempty:
 "(A, x) : foldSet1 f \<Longrightarrow> A \<noteq> {}"
by(erule foldSet1.cases, simp_all) 


inductive_cases empty_foldSet1E [elim!]: "({}, x) : foldSet1 f"

lemma foldSet1_sing[iff]: "(({a},b) : foldSet1 f) = (a = b)"
apply(rule iffI)
 prefer 2 apply fast
apply (erule foldSet1.cases)
 apply blast
apply (erule foldSet1.cases)
 apply blast
apply blast
done

lemma Diff1_foldSet1:
  "(A - {x}, y) : foldSet1 f ==> x: A ==> (A, f x y) : foldSet1 f"
by (erule insert_Diff [THEN subst], rule foldSet1.intros,
    auto dest!:foldSet1_nonempty)

lemma foldSet_imp_finite [simp]: "(A, x) : foldSet1 f ==> finite A"
  by (induct set: foldSet1) auto

lemma finite_nonempty_imp_foldSet1:
  "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> EX x. (A, x) : foldSet1 f"
  by (induct set: Finites) auto

lemma lem: "(A \<subseteq> {a}) = (A = {} \<or> A = {a})"
by blast

(* FIXME structured proof to avoid ML hack and speed things up *)
ML"simp_depth_limit := 3"
lemma (in ACf) foldSet1_determ_aux:
  "ALL A x. card A < n --> (A, x) : foldSet1 f -->
    (ALL y. (A, y) : foldSet1 f --> y = x)"
apply (induct n)
 apply (auto simp add: less_Suc_eq)
apply (erule foldSet1.cases)
 apply (simp add:foldSet1_sing)
apply (erule foldSet1.cases)
 apply (fastsimp simp:foldSet1_sing lem)
apply (clarify)
  txt {* force simplification of @{text "card A < card (insert ...)"}. *}
apply (erule rev_mp)
apply (simp add: less_Suc_eq_le)
apply (rule impI)
apply (rename_tac Aa xa ya Ab xb yb, case_tac "xa = xb")
 apply (subgoal_tac "Aa = Ab")
  prefer 2 apply (blast elim!: equalityE, blast)
  txt {* case @{prop "xa \<notin> xb"}. *}
apply (subgoal_tac "Aa - {xb} = Ab - {xa} & xb : Aa & xa : Ab")
 prefer 2 apply (blast elim!: equalityE, clarify)
apply (subgoal_tac "Aa = insert xb Ab - {xa}")
 prefer 2 apply blast
apply (subgoal_tac "card Aa <= card Ab")
 prefer 2
 apply (rule Suc_le_mono [THEN subst])
 apply (simp add: card_Suc_Diff1)
apply(case_tac "Aa - {xb} = {}")
 apply(subgoal_tac "Aa = {xb}")
  prefer 2 apply (fast elim!: equalityE)
 apply(subgoal_tac "Ab = {xa}")
  prefer 2 apply (fast elim!: equalityE)
 apply (simp add:insert_Diff_if AC)
apply (rule_tac A1 = "Aa - {xb}" and f1 = f in finite_nonempty_imp_foldSet1 [THEN exE])
  apply (blast intro: foldSet_imp_finite finite_Diff)
 apply assumption
apply (frule (1) Diff1_foldSet1)
apply (subgoal_tac "ya = f xb x")
 prefer 2 apply (blast del: equalityCE)
apply (subgoal_tac "(Ab - {xa}, x) : foldSet1 f")
 prefer 2 apply (simp)
apply (subgoal_tac "yb = f xa x")
 prefer 2 apply (blast del: equalityCE dest: Diff1_foldSet1)
apply (simp (no_asm_simp) add: left_commute)
done
ML"simp_depth_limit := 1000"

lemma (in ACf) foldSet1_determ:
  "(A, x) : foldSet1 f ==> (A, y) : foldSet1 f ==> y = x"
by (blast intro: foldSet1_determ_aux [rule_format])

lemma (in ACf) fold1_equality: "(A, y) : foldSet1 f ==> fold1 f A = y"
  by (unfold fold1_def) (blast intro: foldSet1_determ)

lemma fold1_singleton [simp]: "fold1 f {a} = a"
  by (unfold fold1_def) blast

lemma (in ACf) fold1_insert_aux: "x \<notin> A ==> A \<noteq> {} \<Longrightarrow> 
    ((insert x A, v) : foldSet1 f) =
    (EX y. (A, y) : foldSet1 f & v = f x y)"
apply auto
apply (rule_tac A1 = A and f1 = f in finite_nonempty_imp_foldSet1 [THEN exE])
  apply (fastsimp dest: foldSet_imp_finite)
 apply blast
apply (blast intro: foldSet1_determ)
done

lemma (in ACf) fold1_insert:
  "finite A ==> x \<notin> A ==> A \<noteq> {} \<Longrightarrow> fold1 f (insert x A) = f x (fold1 f A)"
apply (unfold fold1_def)
apply (simp add: fold1_insert_aux)
apply (rule the_equality)
apply (auto intro: finite_nonempty_imp_foldSet1
    cong add: conj_cong simp add: fold1_def [symmetric] fold1_equality)
done

locale ACIf = ACf +
  assumes idem: "x \<cdot> x = x"

lemma (in ACIf) fold1_insert2:
assumes finA: "finite A" and nonA: "A \<noteq> {}"
shows "fold1 f (insert a A) = f a (fold1 f A)"
proof cases
  assume "a \<in> A"
  then obtain B where A: "A = insert a B" and disj: "a \<notin> B"
    by(blast dest: mk_disjoint_insert)
  show ?thesis
  proof cases
    assume "B = {}"
    thus ?thesis using A by(simp add:idem)
  next
    assume nonB: "B \<noteq> {}"
    from finA A have finB: "finite B" by(blast intro: finite_subset)
    have "fold1 f (insert a A) = fold1 f (insert a B)" using A by simp
    also have "\<dots> = f a (fold1 f B)"
      using finB nonB disj by(simp add: fold1_insert)
    also have "\<dots> = f a (fold1 f A)"
      using A finB nonB disj by(simp add: idem fold1_insert assoc[symmetric])
    finally show ?thesis .
  qed
next
  assume "a \<notin> A"
  with finA nonA show ?thesis by(simp add:fold1_insert)
qed

text{* Seemed easier to define directly than via fold. *}

(* FIXME define Min/Max via fold1 *)

lemma ex_Max: fixes S :: "('a::linorder)set"
  assumes fin: "finite S" shows "S \<noteq> {} ==> \<exists>m\<in>S. \<forall>s \<in> S. s \<le> m"
using fin
proof (induct)
  case empty thus ?case by simp
next
  case (insert x S)
  show ?case
  proof (cases)
    assume "S = {}" thus ?thesis by simp
  next
    assume nonempty: "S \<noteq> {}"
    then obtain m where m: "m\<in>S" "\<forall>s\<in>S. s \<le> m" using insert by blast
    show ?thesis
    proof (cases)
      assume "x \<le> m" thus ?thesis using m by blast
    next
      assume "~ x \<le> m" thus ?thesis using m
        by(simp add:linorder_not_le order_less_le)(blast intro: order_trans)
    qed
  qed
qed

lemma ex_Min: fixes S :: "('a::linorder)set"
  assumes fin: "finite S" shows "S \<noteq> {} ==> \<exists>m\<in>S. \<forall>s \<in> S. m \<le> s"
using fin
proof (induct)
  case empty thus ?case by simp
next
  case (insert x S)
  show ?case
  proof (cases)
    assume "S = {}" thus ?thesis by simp
  next
    assume nonempty: "S \<noteq> {}"
    then obtain m where m: "m\<in>S" "\<forall>s\<in>S. m \<le> s" using insert by blast
    show ?thesis
    proof (cases)
      assume "m \<le> x" thus ?thesis using m by blast
    next
      assume "~ m \<le> x" thus ?thesis using m
        by(simp add:linorder_not_le order_less_le)(blast intro: order_trans)
    qed
  qed
qed

constdefs
  Min :: "('a::linorder)set => 'a"
  "Min S  ==  THE m. m \<in> S \<and> (\<forall>s \<in> S. m \<le> s)"

  Max :: "('a::linorder)set => 'a"
  "Max S  ==  THE m. m \<in> S \<and> (\<forall>s \<in> S. s \<le> m)"

lemma Min [simp]:
  assumes a: "finite S"  "S \<noteq> {}"
  shows "Min S \<in> S \<and> (\<forall>s \<in> S. Min S \<le> s)" (is "?P(Min S)")
proof (unfold Min_def, rule theI')
  show "\<exists>!m. ?P m"
  proof (rule ex_ex1I)
    show "\<exists>m. ?P m" using ex_Min[OF a] by blast
  next
    fix m1 m2 assume "?P m1" and "?P m2"
    thus "m1 = m2" by (blast dest: order_antisym)
  qed
qed

lemma Max [simp]:
  assumes a: "finite S"  "S \<noteq> {}"
  shows "Max S \<in> S \<and> (\<forall>s \<in> S. s \<le> Max S)" (is "?P(Max S)")
proof (unfold Max_def, rule theI')
  show "\<exists>!m. ?P m"
  proof (rule ex_ex1I)
    show "\<exists>m. ?P m" using ex_Max[OF a] by blast
  next
    fix m1 m2 assume "?P m1" "?P m2"
    thus "m1 = m2" by (blast dest: order_antisym)
  qed
qed


subsection {* Theorems about @{text "choose"} *}

text {*
  \medskip Basic theorem about @{text "choose"}.  By Florian
  Kamm\"uller, tidied by LCP.
*}

lemma card_s_0_eq_empty:
    "finite A ==> card {B. B \<subseteq> A & card B = 0} = 1"
  apply (simp cong add: conj_cong add: finite_subset [THEN card_0_eq])
  apply (simp cong add: rev_conj_cong)
  done

lemma choose_deconstruct: "finite M ==> x \<notin> M
  ==> {s. s <= insert x M & card(s) = Suc k}
       = {s. s <= M & card(s) = Suc k} Un
         {s. EX t. t <= M & card(t) = k & s = insert x t}"
  apply safe
   apply (auto intro: finite_subset [THEN card_insert_disjoint])
  apply (drule_tac x = "xa - {x}" in spec)
  apply (subgoal_tac "x \<notin> xa", auto)
  apply (erule rev_mp, subst card_Diff_singleton)
  apply (auto intro: finite_subset)
  done

lemma card_inj_on_le:
    "[|inj_on f A; f ` A \<subseteq> B; finite B |] ==> card A \<le> card B"
apply (subgoal_tac "finite A") 
 apply (force intro: card_mono simp add: card_image [symmetric])
apply (blast intro: finite_imageD dest: finite_subset) 
done

lemma card_bij_eq:
    "[|inj_on f A; f ` A \<subseteq> B; inj_on g B; g ` B \<subseteq> A;
       finite A; finite B |] ==> card A = card B"
  by (auto intro: le_anti_sym card_inj_on_le)

text{*There are as many subsets of @{term A} having cardinality @{term k}
 as there are sets obtained from the former by inserting a fixed element
 @{term x} into each.*}
lemma constr_bij:
   "[|finite A; x \<notin> A|] ==>
    card {B. EX C. C <= A & card(C) = k & B = insert x C} =
    card {B. B <= A & card(B) = k}"
  apply (rule_tac f = "%s. s - {x}" and g = "insert x" in card_bij_eq)
       apply (auto elim!: equalityE simp add: inj_on_def)
    apply (subst Diff_insert0, auto)
   txt {* finiteness of the two sets *}
   apply (rule_tac [2] B = "Pow (A)" in finite_subset)
   apply (rule_tac B = "Pow (insert x A)" in finite_subset)
   apply fast+
  done

text {*
  Main theorem: combinatorial statement about number of subsets of a set.
*}

lemma n_sub_lemma:
  "!!A. finite A ==> card {B. B <= A & card B = k} = (card A choose k)"
  apply (induct k)
   apply (simp add: card_s_0_eq_empty, atomize)
  apply (rotate_tac -1, erule finite_induct)
   apply (simp_all (no_asm_simp) cong add: conj_cong
     add: card_s_0_eq_empty choose_deconstruct)
  apply (subst card_Un_disjoint)
     prefer 4 apply (force simp add: constr_bij)
    prefer 3 apply force
   prefer 2 apply (blast intro: finite_Pow_iff [THEN iffD2]
     finite_subset [of _ "Pow (insert x F)", standard])
  apply (blast intro: finite_Pow_iff [THEN iffD2, THEN [2] finite_subset])
  done

theorem n_subsets:
    "finite A ==> card {B. B <= A & card B = k} = (card A choose k)"
  by (simp add: n_sub_lemma)

end
