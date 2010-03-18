(*  Title:      HOL/Finite_Set.thy
    Author:     Tobias Nipkow, Lawrence C Paulson and Markus Wenzel
                with contributions by Jeremy Avigad
*)

header {* Finite sets *}

theory Finite_Set
imports Power Option
begin

subsection {* Definition and basic properties *}

inductive finite :: "'a set => bool"
  where
    emptyI [simp, intro!]: "finite {}"
  | insertI [simp, intro!]: "finite A ==> finite (insert a A)"

lemma ex_new_if_finite: -- "does not depend on def of finite at all"
  assumes "\<not> finite (UNIV :: 'a set)" and "finite A"
  shows "\<exists>a::'a. a \<notin> A"
proof -
  from assms have "A \<noteq> UNIV" by blast
  thus ?thesis by blast
qed

lemma finite_induct [case_names empty insert, induct set: finite]:
  "finite F ==>
    P {} ==> (!!x F. finite F ==> x \<notin> F ==> P F ==> P (insert x F)) ==> P F"
  -- {* Discharging @{text "x \<notin> F"} entails extra work. *}
proof -
  assume "P {}" and
    insert: "!!x F. finite F ==> x \<notin> F ==> P F ==> P (insert x F)"
  assume "finite F"
  thus "P F"
  proof induct
    show "P {}" by fact
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

lemma finite_ne_induct[case_names singleton insert, consumes 2]:
assumes fin: "finite F" shows "F \<noteq> {} \<Longrightarrow>
 \<lbrakk> \<And>x. P{x};
   \<And>x F. \<lbrakk> finite F; F \<noteq> {}; x \<notin> F; P F \<rbrakk> \<Longrightarrow> P (insert x F) \<rbrakk>
 \<Longrightarrow> P F"
using fin
proof induct
  case empty thus ?case by simp
next
  case (insert x F)
  show ?case
  proof cases
    assume "F = {}"
    thus ?thesis using `P {x}` by simp
  next
    assume "F \<noteq> {}"
    thus ?thesis using insert by blast
  qed
qed

lemma finite_subset_induct [consumes 2, case_names empty insert]:
  assumes "finite F" and "F \<subseteq> A"
    and empty: "P {}"
    and insert: "!!a F. finite F ==> a \<in> A ==> a \<notin> F ==> P F ==> P (insert a F)"
  shows "P F"
proof -
  from `finite F` and `F \<subseteq> A`
  show ?thesis
  proof induct
    show "P {}" by fact
  next
    fix x F
    assume "finite F" and "x \<notin> F" and
      P: "F \<subseteq> A ==> P F" and i: "insert x F \<subseteq> A"
    show "P (insert x F)"
    proof (rule insert)
      from i show "x \<in> A" by blast
      from i have "F \<subseteq> A" by blast
      with P show "P F" .
      show "finite F" by fact
      show "x \<notin> F" by fact
    qed
  qed
qed


text{* A finite choice principle. Does not need the SOME choice operator. *}
lemma finite_set_choice:
  "finite A \<Longrightarrow> ALL x:A. (EX y. P x y) \<Longrightarrow> EX f. ALL x:A. P x (f x)"
proof (induct set: finite)
  case empty thus ?case by simp
next
  case (insert a A)
  then obtain f b where f: "ALL x:A. P x (f x)" and ab: "P a b" by auto
  show ?case (is "EX f. ?P f")
  proof
    show "?P(%x. if x = a then b else f x)" using f ab by auto
  qed
qed


text{* Finite sets are the images of initial segments of natural numbers: *}

lemma finite_imp_nat_seg_image_inj_on:
  assumes fin: "finite A" 
  shows "\<exists> (n::nat) f. A = f ` {i. i<n} & inj_on f {i. i<n}"
using fin
proof induct
  case empty
  show ?case  
  proof show "\<exists>f. {} = f ` {i::nat. i < 0} & inj_on f {i. i<0}" by simp 
  qed
next
  case (insert a A)
  have notinA: "a \<notin> A" by fact
  from insert.hyps obtain n f
    where "A = f ` {i::nat. i < n}" "inj_on f {i. i < n}" by blast
  hence "insert a A = f(n:=a) ` {i. i < Suc n}"
        "inj_on (f(n:=a)) {i. i < Suc n}" using notinA
    by (auto simp add: image_def Ball_def inj_on_def less_Suc_eq)
  thus ?case by blast
qed

lemma nat_seg_image_imp_finite:
  "!!f A. A = f ` {i::nat. i<n} \<Longrightarrow> finite A"
proof (induct n)
  case 0 thus ?case by simp
next
  case (Suc n)
  let ?B = "f ` {i. i < n}"
  have finB: "finite ?B" by(rule Suc.hyps[OF refl])
  show ?case
  proof cases
    assume "\<exists>k<n. f n = f k"
    hence "A = ?B" using Suc.prems by(auto simp:less_Suc_eq)
    thus ?thesis using finB by simp
  next
    assume "\<not>(\<exists> k<n. f n = f k)"
    hence "A = insert (f n) ?B" using Suc.prems by(auto simp:less_Suc_eq)
    thus ?thesis using finB by simp
  qed
qed

lemma finite_conv_nat_seg_image:
  "finite A = (\<exists> (n::nat) f. A = f ` {i::nat. i<n})"
by(blast intro: nat_seg_image_imp_finite dest: finite_imp_nat_seg_image_inj_on)

lemma finite_imp_inj_to_nat_seg:
assumes "finite A"
shows "EX f n::nat. f`A = {i. i<n} & inj_on f A"
proof -
  from finite_imp_nat_seg_image_inj_on[OF `finite A`]
  obtain f and n::nat where bij: "bij_betw f {i. i<n} A"
    by (auto simp:bij_betw_def)
  let ?f = "the_inv_into {i. i<n} f"
  have "inj_on ?f A & ?f ` A = {i. i<n}"
    by (fold bij_betw_def) (rule bij_betw_the_inv_into[OF bij])
  thus ?thesis by blast
qed

lemma finite_Collect_less_nat[iff]: "finite{n::nat. n<k}"
by(fastsimp simp: finite_conv_nat_seg_image)


subsubsection{* Finiteness and set theoretic constructions *}

lemma finite_UnI: "finite F ==> finite G ==> finite (F Un G)"
by (induct set: finite) simp_all

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
    have A: "A \<subseteq> insert x F" and r: "A - {x} \<subseteq> F ==> finite (A - {x})" by fact+
    show "finite A"
    proof cases
      assume x: "x \<in> A"
      with A have "A - {x} \<subseteq> F" by (simp add: subset_insert_iff)
      with r have "finite (A - {x})" .
      hence "finite (insert x (A - {x}))" ..
      also have "insert x (A - {x}) = A" using x by (rule insert_Diff)
      finally show ?thesis .
    next
      show "A \<subseteq> F ==> ?thesis" by fact
      assume "x \<notin> A"
      with A show "A \<subseteq> F" by (simp add: subset_insert_iff)
    qed
  qed
qed

lemma rev_finite_subset: "finite B ==> A \<subseteq> B ==> finite A"
by (rule finite_subset)

lemma finite_Un [iff]: "finite (F Un G) = (finite F & finite G)"
by (blast intro: finite_subset [of _ "X Un Y", standard] finite_UnI)

lemma finite_Collect_disjI[simp]:
  "finite{x. P x | Q x} = (finite{x. P x} & finite{x. Q x})"
by(simp add:Collect_disj_eq)

lemma finite_Int [simp, intro]: "finite F | finite G ==> finite (F Int G)"
  -- {* The converse obviously fails. *}
by (blast intro: finite_subset)

lemma finite_Collect_conjI [simp, intro]:
  "finite{x. P x} | finite{x. Q x} ==> finite{x. P x & Q x}"
  -- {* The converse obviously fails. *}
by(simp add:Collect_conj_eq)

lemma finite_Collect_le_nat[iff]: "finite{n::nat. n<=k}"
by(simp add: le_eq_less_or_eq)

lemma finite_insert [simp]: "finite (insert a A) = finite A"
  apply (subst insert_is_Un)
  apply (simp only: finite_Un, blast)
  done

lemma finite_Union[simp, intro]:
 "\<lbrakk> finite A; !!M. M \<in> A \<Longrightarrow> finite M \<rbrakk> \<Longrightarrow> finite(\<Union>A)"
by (induct rule:finite_induct) simp_all

lemma finite_Inter[intro]: "EX A:M. finite(A) \<Longrightarrow> finite(Inter M)"
by (blast intro: Inter_lower finite_subset)

lemma finite_INT[intro]: "EX x:I. finite(A x) \<Longrightarrow> finite(INT x:I. A x)"
by (blast intro: INT_lower finite_subset)

lemma finite_empty_induct:
  assumes "finite A"
    and "P A"
    and "!!a A. finite A ==> a:A ==> P A ==> P (A - {a})"
  shows "P {}"
proof -
  have "P (A - A)"
  proof -
    {
      fix c b :: "'a set"
      assume c: "finite c" and b: "finite b"
        and P1: "P b" and P2: "!!x y. finite y ==> x \<in> y ==> P y ==> P (y - {x})"
      have "c \<subseteq> b ==> P (b - c)"
        using c
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
    }
    then show ?thesis by this (simp_all add: assms)
  qed
  then show ?thesis by simp
qed

lemma finite_Diff [simp]: "finite A ==> finite (A - B)"
by (rule Diff_subset [THEN finite_subset])

lemma finite_Diff2 [simp]:
  assumes "finite B" shows "finite (A - B) = finite A"
proof -
  have "finite A \<longleftrightarrow> finite((A-B) Un (A Int B))" by(simp add: Un_Diff_Int)
  also have "\<dots> \<longleftrightarrow> finite(A-B)" using `finite B` by(simp)
  finally show ?thesis ..
qed

lemma finite_compl[simp]:
  "finite(A::'a set) \<Longrightarrow> finite(-A) = finite(UNIV::'a set)"
by(simp add:Compl_eq_Diff_UNIV)

lemma finite_Collect_not[simp]:
  "finite{x::'a. P x} \<Longrightarrow> finite{x. ~P x} = finite(UNIV::'a set)"
by(simp add:Collect_neg_eq)

lemma finite_Diff_insert [iff]: "finite (A - insert a B) = finite (A - B)"
  apply (subst Diff_insert)
  apply (case_tac "a : A - B")
   apply (rule finite_insert [symmetric, THEN trans])
   apply (subst insert_Diff, simp_all)
  done


text {* Image and Inverse Image over Finite Sets *}

lemma finite_imageI[simp]: "finite F ==> finite (h ` F)"
  -- {* The image of a finite set is finite. *}
  by (induct set: finite) simp_all

lemma finite_image_set [simp]:
  "finite {x. P x} \<Longrightarrow> finite { f x | x. P x }"
  by (simp add: image_Collect [symmetric])

lemma finite_surj: "finite A ==> B <= f ` A ==> finite B"
  apply (frule finite_imageI)
  apply (erule finite_subset, assumption)
  done

lemma finite_range_imageI:
    "finite (range g) ==> finite (range (%x. f (g x)))"
  apply (drule finite_imageI, simp add: range_composition)
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
  apply (induct set: finite)
   apply simp_all
  apply (subst vimage_insert)
  apply (simp add: finite_subset [OF inj_vimage_singleton])
  done

lemma finite_vimageD:
  assumes fin: "finite (h -` F)" and surj: "surj h"
  shows "finite F"
proof -
  have "finite (h ` (h -` F))" using fin by (rule finite_imageI)
  also have "h ` (h -` F) = F" using surj by (rule surj_image_vimage_eq)
  finally show "finite F" .
qed

lemma finite_vimage_iff: "bij h \<Longrightarrow> finite (h -` F) \<longleftrightarrow> finite F"
  unfolding bij_def by (auto elim: finite_vimageD finite_vimageI)


text {* The finite UNION of finite sets *}

lemma finite_UN_I: "finite A ==> (!!a. a:A ==> finite (B a)) ==> finite (UN a:A. B a)"
  by (induct set: finite) simp_all

text {*
  Strengthen RHS to
  @{prop "((ALL x:A. finite (B x)) & finite {x. x:A & B x \<noteq> {}})"}?

  We'd need to prove
  @{prop "finite C ==> ALL A B. (UNION A B) <= C --> finite {x. x:A & B x \<noteq> {}}"}
  by induction. *}

lemma finite_UN [simp]:
  "finite A ==> finite (UNION A B) = (ALL x:A. finite (B x))"
by (blast intro: finite_UN_I finite_subset)

lemma finite_Collect_bex[simp]: "finite A \<Longrightarrow>
  finite{x. EX y:A. Q x y} = (ALL y:A. finite{x. Q x y})"
apply(subgoal_tac "{x. EX y:A. Q x y} = UNION A (%y. {x. Q x y})")
 apply auto
done

lemma finite_Collect_bounded_ex[simp]: "finite{y. P y} \<Longrightarrow>
  finite{x. EX y. P y & Q x y} = (ALL y. P y \<longrightarrow> finite{x. Q x y})"
apply(subgoal_tac "{x. EX y. P y & Q x y} = UNION {y. P y} (%y. {x. Q x y})")
 apply auto
done


lemma finite_Plus: "[| finite A; finite B |] ==> finite (A <+> B)"
by (simp add: Plus_def)

lemma finite_PlusD: 
  fixes A :: "'a set" and B :: "'b set"
  assumes fin: "finite (A <+> B)"
  shows "finite A" "finite B"
proof -
  have "Inl ` A \<subseteq> A <+> B" by auto
  hence "finite (Inl ` A :: ('a + 'b) set)" using fin by(rule finite_subset)
  thus "finite A" by(rule finite_imageD)(auto intro: inj_onI)
next
  have "Inr ` B \<subseteq> A <+> B" by auto
  hence "finite (Inr ` B :: ('a + 'b) set)" using fin by(rule finite_subset)
  thus "finite B" by(rule finite_imageD)(auto intro: inj_onI)
qed

lemma finite_Plus_iff[simp]: "finite (A <+> B) \<longleftrightarrow> finite A \<and> finite B"
by(auto intro: finite_PlusD finite_Plus)

lemma finite_Plus_UNIV_iff[simp]:
  "finite (UNIV :: ('a + 'b) set) =
  (finite (UNIV :: 'a set) & finite (UNIV :: 'b set))"
by(subst UNIV_Plus_UNIV[symmetric])(rule finite_Plus_iff)


text {* Sigma of finite sets *}

lemma finite_SigmaI [simp]:
    "finite A ==> (!!a. a:A ==> finite (B a)) ==> finite (SIGMA a:A. B a)"
  by (unfold Sigma_def) (blast intro!: finite_UN_I)

lemma finite_cartesian_product: "[| finite A; finite B |] ==>
    finite (A <*> B)"
  by (rule finite_SigmaI)

lemma finite_Prod_UNIV:
    "finite (UNIV::'a set) ==> finite (UNIV::'b set) ==> finite (UNIV::('a * 'b) set)"
  apply (subgoal_tac "(UNIV:: ('a * 'b) set) = Sigma UNIV (%x. UNIV)")
   apply (erule ssubst)
   apply (erule finite_SigmaI, auto)
  done

lemma finite_cartesian_productD1:
     "[| finite (A <*> B); B \<noteq> {} |] ==> finite A"
apply (auto simp add: finite_conv_nat_seg_image) 
apply (drule_tac x=n in spec) 
apply (drule_tac x="fst o f" in spec) 
apply (auto simp add: o_def) 
 prefer 2 apply (force dest!: equalityD2) 
apply (drule equalityD1) 
apply (rename_tac y x)
apply (subgoal_tac "\<exists>k. k<n & f k = (x,y)") 
 prefer 2 apply force
apply clarify
apply (rule_tac x=k in image_eqI, auto)
done

lemma finite_cartesian_productD2:
     "[| finite (A <*> B); A \<noteq> {} |] ==> finite B"
apply (auto simp add: finite_conv_nat_seg_image) 
apply (drule_tac x=n in spec) 
apply (drule_tac x="snd o f" in spec) 
apply (auto simp add: o_def) 
 prefer 2 apply (force dest!: equalityD2) 
apply (drule equalityD1)
apply (rename_tac x y)
apply (subgoal_tac "\<exists>k. k<n & f k = (x,y)") 
 prefer 2 apply force
apply clarify
apply (rule_tac x=k in image_eqI, auto)
done


text {* The powerset of a finite set *}

lemma finite_Pow_iff [iff]: "finite (Pow A) = finite A"
proof
  assume "finite (Pow A)"
  with _ have "finite ((%x. {x}) ` A)" by (rule finite_subset) blast
  thus "finite A" by (rule finite_imageD [unfolded inj_on_def]) simp
next
  assume "finite A"
  thus "finite (Pow A)"
    by induct (simp_all add: Pow_insert)
qed

lemma finite_Collect_subsets[simp,intro]: "finite A \<Longrightarrow> finite{B. B \<subseteq> A}"
by(simp add: Pow_def[symmetric])


lemma finite_UnionD: "finite(\<Union>A) \<Longrightarrow> finite A"
by(blast intro: finite_subset[OF subset_Pow_Union])


lemma finite_subset_image:
  assumes "finite B"
  shows "B \<subseteq> f ` A \<Longrightarrow> \<exists>C\<subseteq>A. finite C \<and> B = f ` C"
using assms proof(induct)
  case empty thus ?case by simp
next
  case insert thus ?case
    by (clarsimp simp del: image_insert simp add: image_insert[symmetric])
       blast
qed


subsection {* Class @{text finite}  *}

setup {* Sign.add_path "finite" *} -- {*FIXME: name tweaking*}
class finite =
  assumes finite_UNIV: "finite (UNIV \<Colon> 'a set)"
setup {* Sign.parent_path *}
hide const finite

context finite
begin

lemma finite [simp]: "finite (A \<Colon> 'a set)"
  by (rule subset_UNIV finite_UNIV finite_subset)+

end

lemma UNIV_unit [no_atp]:
  "UNIV = {()}" by auto

instance unit :: finite proof
qed (simp add: UNIV_unit)

lemma UNIV_bool [no_atp]:
  "UNIV = {False, True}" by auto

instance bool :: finite proof
qed (simp add: UNIV_bool)

instance * :: (finite, finite) finite proof
qed (simp only: UNIV_Times_UNIV [symmetric] finite_cartesian_product finite)

lemma finite_option_UNIV [simp]:
  "finite (UNIV :: 'a option set) = finite (UNIV :: 'a set)"
  by (auto simp add: UNIV_option_conv elim: finite_imageD intro: inj_Some)

instance option :: (finite) finite proof
qed (simp add: UNIV_option_conv)

lemma inj_graph: "inj (%f. {(x, y). y = f x})"
  by (rule inj_onI, auto simp add: expand_set_eq expand_fun_eq)

instance "fun" :: (finite, finite) finite
proof
  show "finite (UNIV :: ('a => 'b) set)"
  proof (rule finite_imageD)
    let ?graph = "%f::'a => 'b. {(x, y). y = f x}"
    have "range ?graph \<subseteq> Pow UNIV" by simp
    moreover have "finite (Pow (UNIV :: ('a * 'b) set))"
      by (simp only: finite_Pow_iff finite)
    ultimately show "finite (range ?graph)"
      by (rule finite_subset)
    show "inj ?graph" by (rule inj_graph)
  qed
qed

instance "+" :: (finite, finite) finite proof
qed (simp only: UNIV_Plus_UNIV [symmetric] finite_Plus finite)


subsection {* A fold functional for finite sets *}

text {* The intended behaviour is
@{text "fold f z {x\<^isub>1, ..., x\<^isub>n} = f x\<^isub>1 (\<dots> (f x\<^isub>n z)\<dots>)"}
if @{text f} is ``left-commutative'':
*}

locale fun_left_comm =
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes fun_left_comm: "f x (f y z) = f y (f x z)"
begin

text{* On a functional level it looks much nicer: *}

lemma fun_comp_comm:  "f x \<circ> f y = f y \<circ> f x"
by (simp add: fun_left_comm expand_fun_eq)

end

inductive fold_graph :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool"
for f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and z :: 'b where
  emptyI [intro]: "fold_graph f z {} z" |
  insertI [intro]: "x \<notin> A \<Longrightarrow> fold_graph f z A y
      \<Longrightarrow> fold_graph f z (insert x A) (f x y)"

inductive_cases empty_fold_graphE [elim!]: "fold_graph f z {} x"

definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b" where
[code del]: "fold f z A = (THE y. fold_graph f z A y)"

text{*A tempting alternative for the definiens is
@{term "if finite A then THE y. fold_graph f z A y else e"}.
It allows the removal of finiteness assumptions from the theorems
@{text fold_comm}, @{text fold_reindex} and @{text fold_distrib}.
The proofs become ugly. It is not worth the effort. (???) *}


lemma Diff1_fold_graph:
  "fold_graph f z (A - {x}) y \<Longrightarrow> x \<in> A \<Longrightarrow> fold_graph f z A (f x y)"
by (erule insert_Diff [THEN subst], rule fold_graph.intros, auto)

lemma fold_graph_imp_finite: "fold_graph f z A x \<Longrightarrow> finite A"
by (induct set: fold_graph) auto

lemma finite_imp_fold_graph: "finite A \<Longrightarrow> \<exists>x. fold_graph f z A x"
by (induct set: finite) auto


subsubsection{*From @{const fold_graph} to @{term fold}*}

lemma image_less_Suc: "h ` {i. i < Suc m} = insert (h m) (h ` {i. i < m})"
  by (auto simp add: less_Suc_eq) 

lemma insert_image_inj_on_eq:
     "[|insert (h m) A = h ` {i. i < Suc m}; h m \<notin> A; 
        inj_on h {i. i < Suc m}|] 
      ==> A = h ` {i. i < m}"
apply (auto simp add: image_less_Suc inj_on_def)
apply (blast intro: less_trans) 
done

lemma insert_inj_onE:
  assumes aA: "insert a A = h`{i::nat. i<n}" and anot: "a \<notin> A" 
      and inj_on: "inj_on h {i::nat. i<n}"
  shows "\<exists>hm m. inj_on hm {i::nat. i<m} & A = hm ` {i. i<m} & m < n"
proof (cases n)
  case 0 thus ?thesis using aA by auto
next
  case (Suc m)
  have nSuc: "n = Suc m" by fact
  have mlessn: "m<n" by (simp add: nSuc)
  from aA obtain k where hkeq: "h k = a" and klessn: "k<n" by (blast elim!: equalityE)
  let ?hm = "Fun.swap k m h"
  have inj_hm: "inj_on ?hm {i. i < n}" using klessn mlessn 
    by (simp add: inj_on)
  show ?thesis
  proof (intro exI conjI)
    show "inj_on ?hm {i. i < m}" using inj_hm
      by (auto simp add: nSuc less_Suc_eq intro: subset_inj_on)
    show "m<n" by (rule mlessn)
    show "A = ?hm ` {i. i < m}" 
    proof (rule insert_image_inj_on_eq)
      show "inj_on (Fun.swap k m h) {i. i < Suc m}" using inj_hm nSuc by simp
      show "?hm m \<notin> A" by (simp add: swap_def hkeq anot) 
      show "insert (?hm m) A = ?hm ` {i. i < Suc m}"
        using aA hkeq nSuc klessn
        by (auto simp add: swap_def image_less_Suc fun_upd_image 
                           less_Suc_eq inj_on_image_set_diff [OF inj_on])
    qed
  qed
qed

context fun_left_comm
begin

lemma fold_graph_determ_aux:
  "A = h`{i::nat. i<n} \<Longrightarrow> inj_on h {i. i<n}
   \<Longrightarrow> fold_graph f z A x \<Longrightarrow> fold_graph f z A x'
   \<Longrightarrow> x' = x"
proof (induct n arbitrary: A x x' h rule: less_induct)
  case (less n)
  have IH: "\<And>m h A x x'. m < n \<Longrightarrow> A = h ` {i. i<m}
      \<Longrightarrow> inj_on h {i. i<m} \<Longrightarrow> fold_graph f z A x
      \<Longrightarrow> fold_graph f z A x' \<Longrightarrow> x' = x" by fact
  have Afoldx: "fold_graph f z A x" and Afoldx': "fold_graph f z A x'"
    and A: "A = h`{i. i<n}" and injh: "inj_on h {i. i<n}" by fact+
  show ?case
  proof (rule fold_graph.cases [OF Afoldx])
    assume "A = {}" and "x = z"
    with Afoldx' show "x' = x" by auto
  next
    fix B b u
    assume AbB: "A = insert b B" and x: "x = f b u"
      and notinB: "b \<notin> B" and Bu: "fold_graph f z B u"
    show "x'=x" 
    proof (rule fold_graph.cases [OF Afoldx'])
      assume "A = {}" and "x' = z"
      with AbB show "x' = x" by blast
    next
      fix C c v
      assume AcC: "A = insert c C" and x': "x' = f c v"
        and notinC: "c \<notin> C" and Cv: "fold_graph f z C v"
      from A AbB have Beq: "insert b B = h`{i. i<n}" by simp
      from insert_inj_onE [OF Beq notinB injh]
      obtain hB mB where inj_onB: "inj_on hB {i. i < mB}" 
        and Beq: "B = hB ` {i. i < mB}" and lessB: "mB < n" by auto 
      from A AcC have Ceq: "insert c C = h`{i. i<n}" by simp
      from insert_inj_onE [OF Ceq notinC injh]
      obtain hC mC where inj_onC: "inj_on hC {i. i < mC}"
        and Ceq: "C = hC ` {i. i < mC}" and lessC: "mC < n" by auto 
      show "x'=x"
      proof cases
        assume "b=c"
        then moreover have "B = C" using AbB AcC notinB notinC by auto
        ultimately show ?thesis  using Bu Cv x x' IH [OF lessC Ceq inj_onC]
          by auto
      next
        assume diff: "b \<noteq> c"
        let ?D = "B - {c}"
        have B: "B = insert c ?D" and C: "C = insert b ?D"
          using AbB AcC notinB notinC diff by(blast elim!:equalityE)+
        have "finite A" by(rule fold_graph_imp_finite [OF Afoldx])
        with AbB have "finite ?D" by simp
        then obtain d where Dfoldd: "fold_graph f z ?D d"
          using finite_imp_fold_graph by iprover
        moreover have cinB: "c \<in> B" using B by auto
        ultimately have "fold_graph f z B (f c d)" by(rule Diff1_fold_graph)
        hence "f c d = u" by (rule IH [OF lessB Beq inj_onB Bu]) 
        moreover have "f b d = v"
        proof (rule IH[OF lessC Ceq inj_onC Cv])
          show "fold_graph f z C (f b d)" using C notinB Dfoldd by fastsimp
        qed
        ultimately show ?thesis
          using fun_left_comm [of c b] x x' by (auto simp add: o_def)
      qed
    qed
  qed
qed

lemma fold_graph_determ:
  "fold_graph f z A x \<Longrightarrow> fold_graph f z A y \<Longrightarrow> y = x"
apply (frule fold_graph_imp_finite [THEN finite_imp_nat_seg_image_inj_on]) 
apply (blast intro: fold_graph_determ_aux [rule_format])
done

lemma fold_equality:
  "fold_graph f z A y \<Longrightarrow> fold f z A = y"
by (unfold fold_def) (blast intro: fold_graph_determ)

text{* The base case for @{text fold}: *}

lemma (in -) fold_empty [simp]: "fold f z {} = z"
by (unfold fold_def) blast

text{* The various recursion equations for @{const fold}: *}

lemma fold_insert_aux: "x \<notin> A
  \<Longrightarrow> fold_graph f z (insert x A) v \<longleftrightarrow>
      (\<exists>y. fold_graph f z A y \<and> v = f x y)"
apply auto
apply (rule_tac A1 = A and f1 = f in finite_imp_fold_graph [THEN exE])
 apply (fastsimp dest: fold_graph_imp_finite)
apply (blast intro: fold_graph_determ)
done

lemma fold_insert [simp]:
  "finite A ==> x \<notin> A ==> fold f z (insert x A) = f x (fold f z A)"
apply (simp add: fold_def fold_insert_aux)
apply (rule the_equality)
 apply (auto intro: finite_imp_fold_graph
        cong add: conj_cong simp add: fold_def[symmetric] fold_equality)
done

lemma fold_fun_comm:
  "finite A \<Longrightarrow> f x (fold f z A) = fold f (f x z) A"
proof (induct rule: finite_induct)
  case empty then show ?case by simp
next
  case (insert y A) then show ?case
    by (simp add: fun_left_comm[of x])
qed

lemma fold_insert2:
  "finite A \<Longrightarrow> x \<notin> A \<Longrightarrow> fold f z (insert x A) = fold f (f x z) A"
by (simp add: fold_fun_comm)

lemma fold_rec:
assumes "finite A" and "x \<in> A"
shows "fold f z A = f x (fold f z (A - {x}))"
proof -
  have A: "A = insert x (A - {x})" using `x \<in> A` by blast
  then have "fold f z A = fold f z (insert x (A - {x}))" by simp
  also have "\<dots> = f x (fold f z (A - {x}))"
    by (rule fold_insert) (simp add: `finite A`)+
  finally show ?thesis .
qed

lemma fold_insert_remove:
  assumes "finite A"
  shows "fold f z (insert x A) = f x (fold f z (A - {x}))"
proof -
  from `finite A` have "finite (insert x A)" by auto
  moreover have "x \<in> insert x A" by auto
  ultimately have "fold f z (insert x A) = f x (fold f z (insert x A - {x}))"
    by (rule fold_rec)
  then show ?thesis by simp
qed

end

text{* A simplified version for idempotent functions: *}

locale fun_left_comm_idem = fun_left_comm +
  assumes fun_left_idem: "f x (f x z) = f x z"
begin

text{* The nice version: *}
lemma fun_comp_idem : "f x o f x = f x"
by (simp add: fun_left_idem expand_fun_eq)

lemma fold_insert_idem:
  assumes fin: "finite A"
  shows "fold f z (insert x A) = f x (fold f z A)"
proof cases
  assume "x \<in> A"
  then obtain B where "A = insert x B" and "x \<notin> B" by (rule set_insert)
  then show ?thesis using assms by (simp add:fun_left_idem)
next
  assume "x \<notin> A" then show ?thesis using assms by simp
qed

declare fold_insert[simp del] fold_insert_idem[simp]

lemma fold_insert_idem2:
  "finite A \<Longrightarrow> fold f z (insert x A) = fold f (f x z) A"
by(simp add:fold_fun_comm)

end

context ab_semigroup_idem_mult
begin

lemma fun_left_comm_idem: "fun_left_comm_idem(op *)"
apply unfold_locales
 apply (rule mult_left_commute)
apply (rule mult_left_idem)
done

end

context semilattice_inf
begin

lemma ab_semigroup_idem_mult_inf: "ab_semigroup_idem_mult inf"
proof qed (rule inf_assoc inf_commute inf_idem)+

lemma fold_inf_insert[simp]: "finite A \<Longrightarrow> fold inf b (insert a A) = inf a (fold inf b A)"
by(rule fun_left_comm_idem.fold_insert_idem[OF ab_semigroup_idem_mult.fun_left_comm_idem[OF ab_semigroup_idem_mult_inf]])

lemma inf_le_fold_inf: "finite A \<Longrightarrow> ALL a:A. b \<le> a \<Longrightarrow> inf b c \<le> fold inf c A"
by (induct pred: finite) (auto intro: le_infI1)

lemma fold_inf_le_inf: "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> fold inf b A \<le> inf a b"
proof(induct arbitrary: a pred:finite)
  case empty thus ?case by simp
next
  case (insert x A)
  show ?case
  proof cases
    assume "A = {}" thus ?thesis using insert by simp
  next
    assume "A \<noteq> {}" thus ?thesis using insert by (auto intro: le_infI2)
  qed
qed

end

context semilattice_sup
begin

lemma ab_semigroup_idem_mult_sup: "ab_semigroup_idem_mult sup"
by (rule semilattice_inf.ab_semigroup_idem_mult_inf)(rule dual_semilattice)

lemma fold_sup_insert[simp]: "finite A \<Longrightarrow> fold sup b (insert a A) = sup a (fold sup b A)"
by(rule semilattice_inf.fold_inf_insert)(rule dual_semilattice)

lemma fold_sup_le_sup: "finite A \<Longrightarrow> ALL a:A. a \<le> b \<Longrightarrow> fold sup c A \<le> sup b c"
by(rule semilattice_inf.inf_le_fold_inf)(rule dual_semilattice)

lemma sup_le_fold_sup: "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> sup a b \<le> fold sup b A"
by(rule semilattice_inf.fold_inf_le_inf)(rule dual_semilattice)

end


subsubsection{* The derived combinator @{text fold_image} *}

definition fold_image :: "('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b"
where "fold_image f g = fold (%x y. f (g x) y)"

lemma fold_image_empty[simp]: "fold_image f g z {} = z"
by(simp add:fold_image_def)

context ab_semigroup_mult
begin

lemma fold_image_insert[simp]:
assumes "finite A" and "a \<notin> A"
shows "fold_image times g z (insert a A) = g a * (fold_image times g z A)"
proof -
  interpret I: fun_left_comm "%x y. (g x) * y"
    by unfold_locales (simp add: mult_ac)
  show ?thesis using assms by(simp add:fold_image_def)
qed

(*
lemma fold_commute:
  "finite A ==> (!!z. x * (fold times g z A) = fold times g (x * z) A)"
  apply (induct set: finite)
   apply simp
  apply (simp add: mult_left_commute [of x])
  done

lemma fold_nest_Un_Int:
  "finite A ==> finite B
    ==> fold times g (fold times g z B) A = fold times g (fold times g z (A Int B)) (A Un B)"
  apply (induct set: finite)
   apply simp
  apply (simp add: fold_commute Int_insert_left insert_absorb)
  done

lemma fold_nest_Un_disjoint:
  "finite A ==> finite B ==> A Int B = {}
    ==> fold times g z (A Un B) = fold times g (fold times g z B) A"
  by (simp add: fold_nest_Un_Int)
*)

lemma fold_image_reindex:
assumes fin: "finite A"
shows "inj_on h A \<Longrightarrow> fold_image times g z (h`A) = fold_image times (g\<circ>h) z A"
using fin by induct auto

(*
text{*
  Fusion theorem, as described in Graham Hutton's paper,
  A Tutorial on the Universality and Expressiveness of Fold,
  JFP 9:4 (355-372), 1999.
*}

lemma fold_fusion:
  assumes "ab_semigroup_mult g"
  assumes fin: "finite A"
    and hyp: "\<And>x y. h (g x y) = times x (h y)"
  shows "h (fold g j w A) = fold times j (h w) A"
proof -
  class_interpret ab_semigroup_mult [g] by fact
  show ?thesis using fin hyp by (induct set: finite) simp_all
qed
*)

lemma fold_image_cong:
  "finite A \<Longrightarrow>
  (!!x. x:A ==> g x = h x) ==> fold_image times g z A = fold_image times h z A"
apply (subgoal_tac "ALL C. C <= A --> (ALL x:C. g x = h x) --> fold_image times g z C = fold_image times h z C")
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
apply (simp add: Ball_def del: insert_Diff_single)
done

end

context comm_monoid_mult
begin

lemma fold_image_Un_Int:
  "finite A ==> finite B ==>
    fold_image times g 1 A * fold_image times g 1 B =
    fold_image times g 1 (A Un B) * fold_image times g 1 (A Int B)"
by (induct set: finite) 
   (auto simp add: mult_ac insert_absorb Int_insert_left)

corollary fold_Un_disjoint:
  "finite A ==> finite B ==> A Int B = {} ==>
   fold_image times g 1 (A Un B) =
   fold_image times g 1 A * fold_image times g 1 B"
by (simp add: fold_image_Un_Int)

lemma fold_image_UN_disjoint:
  "\<lbrakk> finite I; ALL i:I. finite (A i);
     ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {} \<rbrakk>
   \<Longrightarrow> fold_image times g 1 (UNION I A) =
       fold_image times (%i. fold_image times g 1 (A i)) 1 I"
apply (induct set: finite, simp, atomize)
apply (subgoal_tac "ALL i:F. x \<noteq> i")
 prefer 2 apply blast
apply (subgoal_tac "A x Int UNION F A = {}")
 prefer 2 apply blast
apply (simp add: fold_Un_disjoint)
done

lemma fold_image_Sigma: "finite A ==> ALL x:A. finite (B x) ==>
  fold_image times (%x. fold_image times (g x) 1 (B x)) 1 A =
  fold_image times (split g) 1 (SIGMA x:A. B x)"
apply (subst Sigma_def)
apply (subst fold_image_UN_disjoint, assumption, simp)
 apply blast
apply (erule fold_image_cong)
apply (subst fold_image_UN_disjoint, simp, simp)
 apply blast
apply simp
done

lemma fold_image_distrib: "finite A \<Longrightarrow>
   fold_image times (%x. g x * h x) 1 A =
   fold_image times g 1 A *  fold_image times h 1 A"
by (erule finite_induct) (simp_all add: mult_ac)

lemma fold_image_related: 
  assumes Re: "R e e" 
  and Rop: "\<forall>x1 y1 x2 y2. R x1 x2 \<and> R y1 y2 \<longrightarrow> R (x1 * y1) (x2 * y2)" 
  and fS: "finite S" and Rfg: "\<forall>x\<in>S. R (h x) (g x)"
  shows "R (fold_image (op *) h e S) (fold_image (op *) g e S)"
  using fS by (rule finite_subset_induct) (insert assms, auto)

lemma  fold_image_eq_general:
  assumes fS: "finite S"
  and h: "\<forall>y\<in>S'. \<exists>!x. x\<in> S \<and> h(x) = y" 
  and f12:  "\<forall>x\<in>S. h x \<in> S' \<and> f2(h x) = f1 x"
  shows "fold_image (op *) f1 e S = fold_image (op *) f2 e S'"
proof-
  from h f12 have hS: "h ` S = S'" by auto
  {fix x y assume H: "x \<in> S" "y \<in> S" "h x = h y"
    from f12 h H  have "x = y" by auto }
  hence hinj: "inj_on h S" unfolding inj_on_def Ex1_def by blast
  from f12 have th: "\<And>x. x \<in> S \<Longrightarrow> (f2 \<circ> h) x = f1 x" by auto 
  from hS have "fold_image (op *) f2 e S' = fold_image (op *) f2 e (h ` S)" by simp
  also have "\<dots> = fold_image (op *) (f2 o h) e S" 
    using fold_image_reindex[OF fS hinj, of f2 e] .
  also have "\<dots> = fold_image (op *) f1 e S " using th fold_image_cong[OF fS, of "f2 o h" f1 e]
    by blast
  finally show ?thesis ..
qed

lemma fold_image_eq_general_inverses:
  assumes fS: "finite S" 
  and kh: "\<And>y. y \<in> T \<Longrightarrow> k y \<in> S \<and> h (k y) = y"
  and hk: "\<And>x. x \<in> S \<Longrightarrow> h x \<in> T \<and> k (h x) = x  \<and> g (h x) = f x"
  shows "fold_image (op *) f e S = fold_image (op *) g e T"
  (* metis solves it, but not yet available here *)
  apply (rule fold_image_eq_general[OF fS, of T h g f e])
  apply (rule ballI)
  apply (frule kh)
  apply (rule ex1I[])
  apply blast
  apply clarsimp
  apply (drule hk) apply simp
  apply (rule sym)
  apply (erule conjunct1[OF conjunct2[OF hk]])
  apply (rule ballI)
  apply (drule  hk)
  apply blast
  done

end


subsection{* A fold functional for non-empty sets *}

text{* Does not require start value. *}

inductive
  fold1Set :: "('a => 'a => 'a) => 'a set => 'a => bool"
  for f :: "'a => 'a => 'a"
where
  fold1Set_insertI [intro]:
   "\<lbrakk> fold_graph f a A x; a \<notin> A \<rbrakk> \<Longrightarrow> fold1Set f (insert a A) x"

definition fold1 :: "('a => 'a => 'a) => 'a set => 'a" where
  "fold1 f A == THE x. fold1Set f A x"

lemma fold1Set_nonempty:
  "fold1Set f A x \<Longrightarrow> A \<noteq> {}"
by(erule fold1Set.cases, simp_all)

inductive_cases empty_fold1SetE [elim!]: "fold1Set f {} x"

inductive_cases insert_fold1SetE [elim!]: "fold1Set f (insert a X) x"


lemma fold1Set_sing [iff]: "(fold1Set f {a} b) = (a = b)"
by (blast elim: fold_graph.cases)

lemma fold1_singleton [simp]: "fold1 f {a} = a"
by (unfold fold1_def) blast

lemma finite_nonempty_imp_fold1Set:
  "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> EX x. fold1Set f A x"
apply (induct A rule: finite_induct)
apply (auto dest: finite_imp_fold_graph [of _ f])
done

text{*First, some lemmas about @{const fold_graph}.*}

context ab_semigroup_mult
begin

lemma fun_left_comm: "fun_left_comm(op *)"
by unfold_locales (simp add: mult_ac)

lemma fold_graph_insert_swap:
assumes fold: "fold_graph times (b::'a) A y" and "b \<notin> A"
shows "fold_graph times z (insert b A) (z * y)"
proof -
  interpret fun_left_comm "op *::'a \<Rightarrow> 'a \<Rightarrow> 'a" by (rule fun_left_comm)
from assms show ?thesis
proof (induct rule: fold_graph.induct)
  case emptyI thus ?case by (force simp add: fold_insert_aux mult_commute)
next
  case (insertI x A y)
    have "fold_graph times z (insert x (insert b A)) (x * (z * y))"
      using insertI by force  --{*how does @{term id} get unfolded?*}
    thus ?case by (simp add: insert_commute mult_ac)
qed
qed

lemma fold_graph_permute_diff:
assumes fold: "fold_graph times b A x"
shows "!!a. \<lbrakk>a \<in> A; b \<notin> A\<rbrakk> \<Longrightarrow> fold_graph times a (insert b (A-{a})) x"
using fold
proof (induct rule: fold_graph.induct)
  case emptyI thus ?case by simp
next
  case (insertI x A y)
  have "a = x \<or> a \<in> A" using insertI by simp
  thus ?case
  proof
    assume "a = x"
    with insertI show ?thesis
      by (simp add: id_def [symmetric], blast intro: fold_graph_insert_swap)
  next
    assume ainA: "a \<in> A"
    hence "fold_graph times a (insert x (insert b (A - {a}))) (x * y)"
      using insertI by force
    moreover
    have "insert x (insert b (A - {a})) = insert b (insert x A - {a})"
      using ainA insertI by blast
    ultimately show ?thesis by simp
  qed
qed

lemma fold1_eq_fold:
assumes "finite A" "a \<notin> A" shows "fold1 times (insert a A) = fold times a A"
proof -
  interpret fun_left_comm "op *::'a \<Rightarrow> 'a \<Rightarrow> 'a" by (rule fun_left_comm)
  from assms show ?thesis
apply (simp add: fold1_def fold_def)
apply (rule the_equality)
apply (best intro: fold_graph_determ theI dest: finite_imp_fold_graph [of _ times])
apply (rule sym, clarify)
apply (case_tac "Aa=A")
 apply (best intro: fold_graph_determ)
apply (subgoal_tac "fold_graph times a A x")
 apply (best intro: fold_graph_determ)
apply (subgoal_tac "insert aa (Aa - {a}) = A")
 prefer 2 apply (blast elim: equalityE)
apply (auto dest: fold_graph_permute_diff [where a=a])
done
qed

lemma nonempty_iff: "(A \<noteq> {}) = (\<exists>x B. A = insert x B & x \<notin> B)"
apply safe
 apply simp
 apply (drule_tac x=x in spec)
 apply (drule_tac x="A-{x}" in spec, auto)
done

lemma fold1_insert:
  assumes nonempty: "A \<noteq> {}" and A: "finite A" "x \<notin> A"
  shows "fold1 times (insert x A) = x * fold1 times A"
proof -
  interpret fun_left_comm "op *::'a \<Rightarrow> 'a \<Rightarrow> 'a" by (rule fun_left_comm)
  from nonempty obtain a A' where "A = insert a A' & a ~: A'"
    by (auto simp add: nonempty_iff)
  with A show ?thesis
    by (simp add: insert_commute [of x] fold1_eq_fold eq_commute)
qed

end

context ab_semigroup_idem_mult
begin

lemma fold1_insert_idem [simp]:
  assumes nonempty: "A \<noteq> {}" and A: "finite A" 
  shows "fold1 times (insert x A) = x * fold1 times A"
proof -
  interpret fun_left_comm_idem "op *::'a \<Rightarrow> 'a \<Rightarrow> 'a"
    by (rule fun_left_comm_idem)
  from nonempty obtain a A' where A': "A = insert a A' & a ~: A'"
    by (auto simp add: nonempty_iff)
  show ?thesis
  proof cases
    assume "a = x"
    thus ?thesis
    proof cases
      assume "A' = {}"
      with prems show ?thesis by simp
    next
      assume "A' \<noteq> {}"
      with prems show ?thesis
        by (simp add: fold1_insert mult_assoc [symmetric])
    qed
  next
    assume "a \<noteq> x"
    with prems show ?thesis
      by (simp add: insert_commute fold1_eq_fold)
  qed
qed

lemma hom_fold1_commute:
assumes hom: "!!x y. h (x * y) = h x * h y"
and N: "finite N" "N \<noteq> {}" shows "h (fold1 times N) = fold1 times (h ` N)"
using N proof (induct rule: finite_ne_induct)
  case singleton thus ?case by simp
next
  case (insert n N)
  then have "h (fold1 times (insert n N)) = h (n * fold1 times N)" by simp
  also have "\<dots> = h n * h (fold1 times N)" by(rule hom)
  also have "h (fold1 times N) = fold1 times (h ` N)" by(rule insert)
  also have "times (h n) \<dots> = fold1 times (insert (h n) (h ` N))"
    using insert by(simp)
  also have "insert (h n) (h ` N) = h ` insert n N" by simp
  finally show ?case .
qed

lemma fold1_eq_fold_idem:
  assumes "finite A"
  shows "fold1 times (insert a A) = fold times a A"
proof (cases "a \<in> A")
  case False
  with assms show ?thesis by (simp add: fold1_eq_fold)
next
  interpret fun_left_comm_idem times by (fact fun_left_comm_idem)
  case True then obtain b B
    where A: "A = insert a B" and "a \<notin> B" by (rule set_insert)
  with assms have "finite B" by auto
  then have "fold times a (insert a B) = fold times (a * a) B"
    using `a \<notin> B` by (rule fold_insert2)
  then show ?thesis
    using `a \<notin> B` `finite B` by (simp add: fold1_eq_fold A)
qed

end


text{* Now the recursion rules for definitions: *}

lemma fold1_singleton_def: "g = fold1 f \<Longrightarrow> g {a} = a"
by simp

lemma (in ab_semigroup_mult) fold1_insert_def:
  "\<lbrakk> g = fold1 times; finite A; x \<notin> A; A \<noteq> {} \<rbrakk> \<Longrightarrow> g (insert x A) = x * g A"
by (simp add:fold1_insert)

lemma (in ab_semigroup_idem_mult) fold1_insert_idem_def:
  "\<lbrakk> g = fold1 times; finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> g (insert x A) = x * g A"
by simp

subsubsection{* Determinacy for @{term fold1Set} *}

(*Not actually used!!*)
(*
context ab_semigroup_mult
begin

lemma fold_graph_permute:
  "[|fold_graph times id b (insert a A) x; a \<notin> A; b \<notin> A|]
   ==> fold_graph times id a (insert b A) x"
apply (cases "a=b") 
apply (auto dest: fold_graph_permute_diff) 
done

lemma fold1Set_determ:
  "fold1Set times A x ==> fold1Set times A y ==> y = x"
proof (clarify elim!: fold1Set.cases)
  fix A x B y a b
  assume Ax: "fold_graph times id a A x"
  assume By: "fold_graph times id b B y"
  assume anotA:  "a \<notin> A"
  assume bnotB:  "b \<notin> B"
  assume eq: "insert a A = insert b B"
  show "y=x"
  proof cases
    assume same: "a=b"
    hence "A=B" using anotA bnotB eq by (blast elim!: equalityE)
    thus ?thesis using Ax By same by (blast intro: fold_graph_determ)
  next
    assume diff: "a\<noteq>b"
    let ?D = "B - {a}"
    have B: "B = insert a ?D" and A: "A = insert b ?D"
     and aB: "a \<in> B" and bA: "b \<in> A"
      using eq anotA bnotB diff by (blast elim!:equalityE)+
    with aB bnotB By
    have "fold_graph times id a (insert b ?D) y" 
      by (auto intro: fold_graph_permute simp add: insert_absorb)
    moreover
    have "fold_graph times id a (insert b ?D) x"
      by (simp add: A [symmetric] Ax) 
    ultimately show ?thesis by (blast intro: fold_graph_determ) 
  qed
qed

lemma fold1Set_equality: "fold1Set times A y ==> fold1 times A = y"
  by (unfold fold1_def) (blast intro: fold1Set_determ)

end
*)

declare
  empty_fold_graphE [rule del]  fold_graph.intros [rule del]
  empty_fold1SetE [rule del]  insert_fold1SetE [rule del]
  -- {* No more proofs involve these relations. *}

subsubsection {* Lemmas about @{text fold1} *}

context ab_semigroup_mult
begin

lemma fold1_Un:
assumes A: "finite A" "A \<noteq> {}"
shows "finite B \<Longrightarrow> B \<noteq> {} \<Longrightarrow> A Int B = {} \<Longrightarrow>
       fold1 times (A Un B) = fold1 times A * fold1 times B"
using A by (induct rule: finite_ne_induct)
  (simp_all add: fold1_insert mult_assoc)

lemma fold1_in:
  assumes A: "finite (A)" "A \<noteq> {}" and elem: "\<And>x y. x * y \<in> {x,y}"
  shows "fold1 times A \<in> A"
using A
proof (induct rule:finite_ne_induct)
  case singleton thus ?case by simp
next
  case insert thus ?case using elem by (force simp add:fold1_insert)
qed

end

lemma (in ab_semigroup_idem_mult) fold1_Un2:
assumes A: "finite A" "A \<noteq> {}"
shows "finite B \<Longrightarrow> B \<noteq> {} \<Longrightarrow>
       fold1 times (A Un B) = fold1 times A * fold1 times B"
using A
proof(induct rule:finite_ne_induct)
  case singleton thus ?case by simp
next
  case insert thus ?case by (simp add: mult_assoc)
qed


subsection {* Expressing set operations via @{const fold} *}

lemma (in fun_left_comm) fun_left_comm_apply:
  "fun_left_comm (\<lambda>x. f (g x))"
proof
qed (simp_all add: fun_left_comm)

lemma (in fun_left_comm_idem) fun_left_comm_idem_apply:
  "fun_left_comm_idem (\<lambda>x. f (g x))"
  by (rule fun_left_comm_idem.intro, rule fun_left_comm_apply, unfold_locales)
    (simp_all add: fun_left_idem)

lemma fun_left_comm_idem_insert:
  "fun_left_comm_idem insert"
proof
qed auto

lemma fun_left_comm_idem_remove:
  "fun_left_comm_idem (\<lambda>x A. A - {x})"
proof
qed auto

lemma (in semilattice_inf) fun_left_comm_idem_inf:
  "fun_left_comm_idem inf"
proof
qed (auto simp add: inf_left_commute)

lemma (in semilattice_sup) fun_left_comm_idem_sup:
  "fun_left_comm_idem sup"
proof
qed (auto simp add: sup_left_commute)

lemma union_fold_insert:
  assumes "finite A"
  shows "A \<union> B = fold insert B A"
proof -
  interpret fun_left_comm_idem insert by (fact fun_left_comm_idem_insert)
  from `finite A` show ?thesis by (induct A arbitrary: B) simp_all
qed

lemma minus_fold_remove:
  assumes "finite A"
  shows "B - A = fold (\<lambda>x A. A - {x}) B A"
proof -
  interpret fun_left_comm_idem "\<lambda>x A. A - {x}" by (fact fun_left_comm_idem_remove)
  from `finite A` show ?thesis by (induct A arbitrary: B) auto
qed

context complete_lattice
begin

lemma inf_Inf_fold_inf:
  assumes "finite A"
  shows "inf B (Inf A) = fold inf B A"
proof -
  interpret fun_left_comm_idem inf by (fact fun_left_comm_idem_inf)
  from `finite A` show ?thesis by (induct A arbitrary: B)
    (simp_all add: Inf_empty Inf_insert inf_commute fold_fun_comm)
qed

lemma sup_Sup_fold_sup:
  assumes "finite A"
  shows "sup B (Sup A) = fold sup B A"
proof -
  interpret fun_left_comm_idem sup by (fact fun_left_comm_idem_sup)
  from `finite A` show ?thesis by (induct A arbitrary: B)
    (simp_all add: Sup_empty Sup_insert sup_commute fold_fun_comm)
qed

lemma Inf_fold_inf:
  assumes "finite A"
  shows "Inf A = fold inf top A"
  using assms inf_Inf_fold_inf [of A top] by (simp add: inf_absorb2)

lemma Sup_fold_sup:
  assumes "finite A"
  shows "Sup A = fold sup bot A"
  using assms sup_Sup_fold_sup [of A bot] by (simp add: sup_absorb2)

lemma inf_INFI_fold_inf:
  assumes "finite A"
  shows "inf B (INFI A f) = fold (\<lambda>A. inf (f A)) B A" (is "?inf = ?fold") 
proof (rule sym)
  interpret fun_left_comm_idem inf by (fact fun_left_comm_idem_inf)
  interpret fun_left_comm_idem "\<lambda>A. inf (f A)" by (fact fun_left_comm_idem_apply)
  from `finite A` show "?fold = ?inf"
  by (induct A arbitrary: B)
    (simp_all add: INFI_def Inf_empty Inf_insert inf_left_commute)
qed

lemma sup_SUPR_fold_sup:
  assumes "finite A"
  shows "sup B (SUPR A f) = fold (\<lambda>A. sup (f A)) B A" (is "?sup = ?fold") 
proof (rule sym)
  interpret fun_left_comm_idem sup by (fact fun_left_comm_idem_sup)
  interpret fun_left_comm_idem "\<lambda>A. sup (f A)" by (fact fun_left_comm_idem_apply)
  from `finite A` show "?fold = ?sup"
  by (induct A arbitrary: B)
    (simp_all add: SUPR_def Sup_empty Sup_insert sup_left_commute)
qed

lemma INFI_fold_inf:
  assumes "finite A"
  shows "INFI A f = fold (\<lambda>A. inf (f A)) top A"
  using assms inf_INFI_fold_inf [of A top] by simp

lemma SUPR_fold_sup:
  assumes "finite A"
  shows "SUPR A f = fold (\<lambda>A. sup (f A)) bot A"
  using assms sup_SUPR_fold_sup [of A bot] by simp

end


subsection {* Locales as mini-packages *}

locale folding =
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  fixes F :: "'a set \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes commute_comp: "f x \<circ> f y = f y \<circ> f x"
  assumes eq_fold: "finite A \<Longrightarrow> F A s = fold f s A"
begin

lemma fun_left_commute:
  "f x (f y s) = f y (f x s)"
  using commute_comp [of x y] by (simp add: expand_fun_eq)

lemma fun_left_comm:
  "fun_left_comm f"
proof
qed (fact fun_left_commute)

lemma empty [simp]:
  "F {} = id"
  by (simp add: eq_fold expand_fun_eq)

lemma insert [simp]:
  assumes "finite A" and "x \<notin> A"
  shows "F (insert x A) = F A \<circ> f x"
proof -
  interpret fun_left_comm f by (fact fun_left_comm)
  from fold_insert2 assms
  have "\<And>s. fold f s (insert x A) = fold f (f x s) A" .
  with `finite A` show ?thesis by (simp add: eq_fold expand_fun_eq)
qed

lemma remove:
  assumes "finite A" and "x \<in> A"
  shows "F A = F (A - {x}) \<circ> f x"
proof -
  from `x \<in> A` obtain B where A: "A = insert x B" and "x \<notin> B"
    by (auto dest: mk_disjoint_insert)
  moreover from `finite A` this have "finite B" by simp
  ultimately show ?thesis by simp
qed

lemma insert_remove:
  assumes "finite A"
  shows "F (insert x A) = F (A - {x}) \<circ> f x"
  using assms by (cases "x \<in> A") (simp_all add: remove insert_absorb)

lemma commute_comp':
  assumes "finite A"
  shows "f x \<circ> F A = F A \<circ> f x"
proof (rule ext)
  fix s
  from assms show "(f x \<circ> F A) s = (F A \<circ> f x) s"
    by (induct A arbitrary: s) (simp_all add: fun_left_commute)
qed

lemma fun_left_commute':
  assumes "finite A"
  shows "f x (F A s) = F A (f x s)"
  using commute_comp' assms by (simp add: expand_fun_eq)

lemma union:
  assumes "finite A" and "finite B"
  and "A \<inter> B = {}"
  shows "F (A \<union> B) = F A \<circ> F B"
using `finite A` `A \<inter> B = {}` proof (induct A)
  case empty show ?case by simp
next
  case (insert x A)
  then have "A \<inter> B = {}" by auto
  with insert(3) have "F (A \<union> B) = F A \<circ> F B" .
  moreover from insert have "x \<notin> B" by simp
  moreover from `finite A` `finite B` have fin: "finite (A \<union> B)" by simp
  moreover from `x \<notin> A` `x \<notin> B` have "x \<notin> A \<union> B" by simp
  ultimately show ?case by (simp add: fun_left_commute')
qed

end

locale folding_idem = folding +
  assumes idem_comp: "f x \<circ> f x = f x"
begin

declare insert [simp del]

lemma fun_idem:
  "f x (f x s) = f x s"
  using idem_comp [of x] by (simp add: expand_fun_eq)

lemma fun_left_comm_idem:
  "fun_left_comm_idem f"
proof
qed (fact fun_left_commute fun_idem)+

lemma insert_idem [simp]:
  assumes "finite A"
  shows "F (insert x A) = F A \<circ> f x"
proof -
  interpret fun_left_comm_idem f by (fact fun_left_comm_idem)
  from fold_insert_idem2 assms
  have "\<And>s. fold f s (insert x A) = fold f (f x s) A" .
  with assms show ?thesis by (simp add: eq_fold expand_fun_eq)
qed

lemma union_idem:
  assumes "finite A" and "finite B"
  shows "F (A \<union> B) = F A \<circ> F B"
using `finite A` proof (induct A)
  case empty show ?case by simp
next
  case (insert x A)
  from insert(3) have "F (A \<union> B) = F A \<circ> F B" .
  moreover from `finite A` `finite B` have fin: "finite (A \<union> B)" by simp
  ultimately show ?case by (simp add: fun_left_commute')
qed

end

no_notation times (infixl "*" 70)
no_notation Groups.one ("1")

locale folding_image_simple = comm_monoid +
  fixes g :: "('b \<Rightarrow> 'a)"
  fixes F :: "'b set \<Rightarrow> 'a"
  assumes eq_fold: "finite A \<Longrightarrow> F A = fold_image f g 1 A"
begin

lemma empty [simp]:
  "F {} = 1"
  by (simp add: eq_fold)

lemma insert [simp]:
  assumes "finite A" and "x \<notin> A"
  shows "F (insert x A) = g x * F A"
proof -
  interpret fun_left_comm "%x y. (g x) * y" proof
  qed (simp add: ac_simps)
  with assms have "fold_image (op *) g 1 (insert x A) = g x * fold_image (op *) g 1 A"
    by (simp add: fold_image_def)
  with `finite A` show ?thesis by (simp add: eq_fold)
qed

lemma remove:
  assumes "finite A" and "x \<in> A"
  shows "F A = g x * F (A - {x})"
proof -
  from `x \<in> A` obtain B where A: "A = insert x B" and "x \<notin> B"
    by (auto dest: mk_disjoint_insert)
  moreover from `finite A` this have "finite B" by simp
  ultimately show ?thesis by simp
qed

lemma insert_remove:
  assumes "finite A"
  shows "F (insert x A) = g x * F (A - {x})"
  using assms by (cases "x \<in> A") (simp_all add: remove insert_absorb)

lemma union_inter:
  assumes "finite A" and "finite B"
  shows "F A * F B = F (A \<union> B) * F (A \<inter> B)"
using assms proof (induct A)
  case empty then show ?case by simp
next
  case (insert x A) then show ?case
    by (auto simp add: insert_absorb Int_insert_left commute [of _ "g x"] assoc left_commute)
qed

corollary union_disjoint:
  assumes "finite A" and "finite B"
  assumes "A \<inter> B = {}"
  shows "F (A \<union> B) = F A * F B"
  using assms by (simp add: union_inter)

end

locale folding_image = comm_monoid +
  fixes F :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'a"
  assumes eq_fold: "\<And>g. finite A \<Longrightarrow> F g A = fold_image f g 1 A"

sublocale folding_image < folding_image_simple "op *" 1 g "F g" proof
qed (fact eq_fold)

context folding_image
begin

lemma reindex:
  assumes "finite A" and "inj_on h A"
  shows "F g (h ` A) = F (g \<circ> h) A"
  using assms by (induct A) auto

lemma cong:
  assumes "finite A" and "\<And>x. x \<in> A \<Longrightarrow> g x = h x"
  shows "F g A = F h A"
proof -
  from assms have "ALL C. C <= A --> (ALL x:C. g x = h x) --> F g C = F h C"
  apply - apply (erule finite_induct) apply simp
  apply (simp add: subset_insert_iff, clarify)
  apply (subgoal_tac "finite C")
  prefer 2 apply (blast dest: finite_subset [COMP swap_prems_rl])
  apply (subgoal_tac "C = insert x (C - {x})")
  prefer 2 apply blast
  apply (erule ssubst)
  apply (drule spec)
  apply (erule (1) notE impE)
  apply (simp add: Ball_def del: insert_Diff_single)
  done
  with assms show ?thesis by simp
qed

lemma UNION_disjoint:
  assumes "finite I" and "\<forall>i\<in>I. finite (A i)"
  and "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}"
  shows "F g (UNION I A) = F (F g \<circ> A) I"
apply (insert assms)
apply (induct set: finite, simp, atomize)
apply (subgoal_tac "\<forall>i\<in>Fa. x \<noteq> i")
 prefer 2 apply blast
apply (subgoal_tac "A x Int UNION Fa A = {}")
 prefer 2 apply blast
apply (simp add: union_disjoint)
done

lemma distrib:
  assumes "finite A"
  shows "F (\<lambda>x. g x * h x) A = F g A * F h A"
  using assms by (rule finite_induct) (simp_all add: assoc commute left_commute)

lemma related: 
  assumes Re: "R 1 1" 
  and Rop: "\<forall>x1 y1 x2 y2. R x1 x2 \<and> R y1 y2 \<longrightarrow> R (x1 * y1) (x2 * y2)" 
  and fS: "finite S" and Rfg: "\<forall>x\<in>S. R (h x) (g x)"
  shows "R (F h S) (F g S)"
  using fS by (rule finite_subset_induct) (insert assms, auto)

lemma eq_general:
  assumes fS: "finite S"
  and h: "\<forall>y\<in>S'. \<exists>!x. x \<in> S \<and> h x = y" 
  and f12:  "\<forall>x\<in>S. h x \<in> S' \<and> f2 (h x) = f1 x"
  shows "F f1 S = F f2 S'"
proof-
  from h f12 have hS: "h ` S = S'" by blast
  {fix x y assume H: "x \<in> S" "y \<in> S" "h x = h y"
    from f12 h H  have "x = y" by auto }
  hence hinj: "inj_on h S" unfolding inj_on_def Ex1_def by blast
  from f12 have th: "\<And>x. x \<in> S \<Longrightarrow> (f2 \<circ> h) x = f1 x" by auto 
  from hS have "F f2 S' = F f2 (h ` S)" by simp
  also have "\<dots> = F (f2 o h) S" using reindex [OF fS hinj, of f2] .
  also have "\<dots> = F f1 S " using th cong [OF fS, of "f2 o h" f1]
    by blast
  finally show ?thesis ..
qed

lemma eq_general_inverses:
  assumes fS: "finite S" 
  and kh: "\<And>y. y \<in> T \<Longrightarrow> k y \<in> S \<and> h (k y) = y"
  and hk: "\<And>x. x \<in> S \<Longrightarrow> h x \<in> T \<and> k (h x) = x \<and> g (h x) = j x"
  shows "F j S = F g T"
  (* metis solves it, but not yet available here *)
  apply (rule eq_general [OF fS, of T h g j])
  apply (rule ballI)
  apply (frule kh)
  apply (rule ex1I[])
  apply blast
  apply clarsimp
  apply (drule hk) apply simp
  apply (rule sym)
  apply (erule conjunct1[OF conjunct2[OF hk]])
  apply (rule ballI)
  apply (drule hk)
  apply blast
  done

end

notation times (infixl "*" 70)
notation Groups.one ("1")


subsection {* Finite cardinality *}

text {* This definition, although traditional, is ugly to work with:
@{text "card A == LEAST n. EX f. A = {f i | i. i < n}"}.
But now that we have @{text fold_image} things are easy:
*}

definition card :: "'a set \<Rightarrow> nat" where
  "card A = (if finite A then fold_image (op +) (\<lambda>x. 1) 0 A else 0)"

interpretation card!: folding_image_simple "op +" 0 "\<lambda>x. 1" card proof
qed (simp add: card_def)

lemma card_infinite [simp]:
  "\<not> finite A \<Longrightarrow> card A = 0"
  by (simp add: card_def)

lemma card_empty:
  "card {} = 0"
  by (fact card.empty)

lemma card_insert_disjoint:
  "finite A ==> x \<notin> A ==> card (insert x A) = Suc (card A)"
  by simp

lemma card_insert_if:
  "finite A ==> card (insert x A) = (if x \<in> A then card A else Suc (card A))"
  by auto (simp add: card.insert_remove card.remove)

lemma card_ge_0_finite:
  "card A > 0 \<Longrightarrow> finite A"
  by (rule ccontr) simp

lemma card_0_eq [simp, no_atp]:
  "finite A \<Longrightarrow> card A = 0 \<longleftrightarrow> A = {}"
  by (auto dest: mk_disjoint_insert)

lemma finite_UNIV_card_ge_0:
  "finite (UNIV :: 'a set) \<Longrightarrow> card (UNIV :: 'a set) > 0"
  by (rule ccontr) simp

lemma card_eq_0_iff:
  "card A = 0 \<longleftrightarrow> A = {} \<or> \<not> finite A"
  by auto

lemma card_gt_0_iff:
  "0 < card A \<longleftrightarrow> A \<noteq> {} \<and> finite A"
  by (simp add: neq0_conv [symmetric] card_eq_0_iff) 

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

lemma card_Diff_insert[simp]:
assumes "finite A" and "a:A" and "a ~: B"
shows "card(A - insert a B) = card(A - B) - 1"
proof -
  have "A - insert a B = (A - B) - {a}" using assms by blast
  then show ?thesis using assms by(simp add:card_Diff_singleton)
qed

lemma card_insert: "finite A ==> card (insert x A) = Suc (card (A - {x}))"
by (simp add: card_insert_if card_Suc_Diff1 del:card_Diff_insert)

lemma card_insert_le: "finite A ==> card A <= card (insert x A)"
by (simp add: card_insert_if)

lemma card_mono:
  assumes "finite B" and "A \<subseteq> B"
  shows "card A \<le> card B"
proof -
  from assms have "finite A" by (auto intro: finite_subset)
  then show ?thesis using assms proof (induct A arbitrary: B)
    case empty then show ?case by simp
  next
    case (insert x A)
    then have "x \<in> B" by simp
    from insert have "A \<subseteq> B - {x}" and "finite (B - {x})" by auto
    with insert.hyps have "card A \<le> card (B - {x})" by auto
    with `finite A` `x \<notin> A` `finite B` `x \<in> B` show ?case by simp (simp only: card.remove)
  qed
qed

lemma card_seteq: "finite B ==> (!!A. A <= B ==> card B <= card A ==> A = B)"
apply (induct set: finite, simp, clarify)
apply (subgoal_tac "finite A & A - {x} <= F")
 prefer 2 apply (blast intro: finite_subset, atomize)
apply (drule_tac x = "A - {x}" in spec)
apply (simp add: card_Diff_singleton_if split add: split_if_asm)
apply (case_tac "card A", auto)
done

lemma psubset_card_mono: "finite B ==> A < B ==> card A < card B"
apply (simp add: psubset_eq linorder_not_le [symmetric])
apply (blast dest: card_seteq)
done

lemma card_Un_Int: "finite A ==> finite B
    ==> card A + card B = card (A Un B) + card (A Int B)"
  by (fact card.union_inter)

lemma card_Un_disjoint: "finite A ==> finite B
    ==> A Int B = {} ==> card (A Un B) = card A + card B"
  by (fact card.union_disjoint)

lemma card_Diff_subset:
  assumes "finite B" and "B \<subseteq> A"
  shows "card (A - B) = card A - card B"
proof (cases "finite A")
  case False with assms show ?thesis by simp
next
  case True with assms show ?thesis by (induct B arbitrary: A) simp_all
qed

lemma card_Diff_subset_Int:
  assumes AB: "finite (A \<inter> B)" shows "card (A - B) = card A - card (A \<inter> B)"
proof -
  have "A - B = A - A \<inter> B" by auto
  thus ?thesis
    by (simp add: card_Diff_subset AB) 
qed

lemma card_Diff1_less: "finite A ==> x: A ==> card (A - {x}) < card A"
apply (rule Suc_less_SucD)
apply (simp add: card_Suc_Diff1 del:card_Diff_insert)
done

lemma card_Diff2_less:
  "finite A ==> x: A ==> y: A ==> card (A - {x} - {y}) < card A"
apply (case_tac "x = y")
 apply (simp add: card_Diff1_less del:card_Diff_insert)
apply (rule less_trans)
 prefer 2 apply (auto intro!: card_Diff1_less simp del:card_Diff_insert)
done

lemma card_Diff1_le: "finite A ==> card (A - {x}) <= card A"
apply (case_tac "x : A")
 apply (simp_all add: card_Diff1_less less_imp_le)
done

lemma card_psubset: "finite B ==> A \<subseteq> B ==> card A < card B ==> A < B"
by (erule psubsetI, blast)

lemma insert_partition:
  "\<lbrakk> x \<notin> F; \<forall>c1 \<in> insert x F. \<forall>c2 \<in> insert x F. c1 \<noteq> c2 \<longrightarrow> c1 \<inter> c2 = {} \<rbrakk>
  \<Longrightarrow> x \<inter> \<Union> F = {}"
by auto

lemma finite_psubset_induct[consumes 1, case_names psubset]:
  assumes "finite A" and "!!A. finite A \<Longrightarrow> (!!B. finite B \<Longrightarrow> B \<subset> A \<Longrightarrow> P(B)) \<Longrightarrow> P(A)" shows "P A"
using assms(1)
proof (induct A rule: measure_induct_rule[where f=card])
  case (less A)
  show ?case
  proof(rule assms(2)[OF less(2)])
    fix B assume "finite B" "B \<subset> A"
    show "P B" by(rule less(1)[OF psubset_card_mono[OF less(2) `B \<subset> A`] `finite B`])
  qed
qed

text{* main cardinality theorem *}
lemma card_partition [rule_format]:
  "finite C ==>
     finite (\<Union> C) -->
     (\<forall>c\<in>C. card c = k) -->
     (\<forall>c1 \<in> C. \<forall>c2 \<in> C. c1 \<noteq> c2 --> c1 \<inter> c2 = {}) -->
     k * card(C) = card (\<Union> C)"
apply (erule finite_induct, simp)
apply (simp add: card_Un_disjoint insert_partition 
       finite_subset [of _ "\<Union> (insert x F)"])
done

lemma card_eq_UNIV_imp_eq_UNIV:
  assumes fin: "finite (UNIV :: 'a set)"
  and card: "card A = card (UNIV :: 'a set)"
  shows "A = (UNIV :: 'a set)"
proof
  show "A \<subseteq> UNIV" by simp
  show "UNIV \<subseteq> A"
  proof
    fix x
    show "x \<in> A"
    proof (rule ccontr)
      assume "x \<notin> A"
      then have "A \<subset> UNIV" by auto
      with fin have "card A < card (UNIV :: 'a set)" by (fact psubset_card_mono)
      with card show False by simp
    qed
  qed
qed

text{*The form of a finite set of given cardinality*}

lemma card_eq_SucD:
assumes "card A = Suc k"
shows "\<exists>b B. A = insert b B & b \<notin> B & card B = k & (k=0 \<longrightarrow> B={})"
proof -
  have fin: "finite A" using assms by (auto intro: ccontr)
  moreover have "card A \<noteq> 0" using assms by auto
  ultimately obtain b where b: "b \<in> A" by auto
  show ?thesis
  proof (intro exI conjI)
    show "A = insert b (A-{b})" using b by blast
    show "b \<notin> A - {b}" by blast
    show "card (A - {b}) = k" and "k = 0 \<longrightarrow> A - {b} = {}"
      using assms b fin by(fastsimp dest:mk_disjoint_insert)+
  qed
qed

lemma card_Suc_eq:
  "(card A = Suc k) =
   (\<exists>b B. A = insert b B & b \<notin> B & card B = k & (k=0 \<longrightarrow> B={}))"
apply(rule iffI)
 apply(erule card_eq_SucD)
apply(auto)
apply(subst card_insert)
 apply(auto intro:ccontr)
done

lemma finite_fun_UNIVD2:
  assumes fin: "finite (UNIV :: ('a \<Rightarrow> 'b) set)"
  shows "finite (UNIV :: 'b set)"
proof -
  from fin have "finite (range (\<lambda>f :: 'a \<Rightarrow> 'b. f arbitrary))"
    by(rule finite_imageI)
  moreover have "UNIV = range (\<lambda>f :: 'a \<Rightarrow> 'b. f arbitrary)"
    by(rule UNIV_eq_I) auto
  ultimately show "finite (UNIV :: 'b set)" by simp
qed

lemma card_UNIV_unit: "card (UNIV :: unit set) = 1"
  unfolding UNIV_unit by simp


subsubsection {* Cardinality of image *}

lemma card_image_le: "finite A ==> card (f ` A) <= card A"
apply (induct set: finite)
 apply simp
apply (simp add: le_SucI card_insert_if)
done

lemma card_image:
  assumes "inj_on f A"
  shows "card (f ` A) = card A"
proof (cases "finite A")
  case True then show ?thesis using assms by (induct A) simp_all
next
  case False then have "\<not> finite (f ` A)" using assms by (auto dest: finite_imageD)
  with False show ?thesis by simp
qed

lemma bij_betw_same_card: "bij_betw f A B \<Longrightarrow> card A = card B"
by(auto simp: card_image bij_betw_def)

lemma endo_inj_surj: "finite A ==> f ` A \<subseteq> A ==> inj_on f A ==> f ` A = A"
by (simp add: card_seteq card_image)

lemma eq_card_imp_inj_on:
  "[| finite A; card(f ` A) = card A |] ==> inj_on f A"
apply (induct rule:finite_induct)
apply simp
apply(frule card_image_le[where f = f])
apply(simp add:card_insert_if split:if_splits)
done

lemma inj_on_iff_eq_card:
  "finite A ==> inj_on f A = (card(f ` A) = card A)"
by(blast intro: card_image eq_card_imp_inj_on)


lemma card_inj_on_le:
  "[|inj_on f A; f ` A \<subseteq> B; finite B |] ==> card A \<le> card B"
apply (subgoal_tac "finite A") 
 apply (force intro: card_mono simp add: card_image [symmetric])
apply (blast intro: finite_imageD dest: finite_subset) 
done

lemma card_bij_eq:
  "[|inj_on f A; f ` A \<subseteq> B; inj_on g B; g ` B \<subseteq> A;
     finite A; finite B |] ==> card A = card B"
by (auto intro: le_antisym card_inj_on_le)


subsubsection {* Cardinality of sums *}

lemma card_Plus:
  assumes "finite A" and "finite B"
  shows "card (A <+> B) = card A + card B"
proof -
  have "Inl`A \<inter> Inr`B = {}" by fast
  with assms show ?thesis
    unfolding Plus_def
    by (simp add: card_Un_disjoint card_image)
qed

lemma card_Plus_conv_if:
  "card (A <+> B) = (if finite A \<and> finite B then card A + card B else 0)"
  by (auto simp add: card_Plus)


subsubsection {* Cardinality of the Powerset *}

lemma card_Pow: "finite A ==> card (Pow A) = Suc (Suc 0) ^ card A"  (* FIXME numeral 2 (!?) *)
apply (induct set: finite)
 apply (simp_all add: Pow_insert)
apply (subst card_Un_disjoint, blast)
  apply (blast intro: finite_imageI, blast)
apply (subgoal_tac "inj_on (insert x) (Pow F)")
 apply (simp add: card_image Pow_insert)
apply (unfold inj_on_def)
apply (blast elim!: equalityE)
done

text {* Relates to equivalence classes.  Based on a theorem of F. Kammüller.  *}

lemma dvd_partition:
  "finite (Union C) ==>
    ALL c : C. k dvd card c ==>
    (ALL c1: C. ALL c2: C. c1 \<noteq> c2 --> c1 Int c2 = {}) ==>
  k dvd card (Union C)"
apply(frule finite_UnionD)
apply(rotate_tac -1)
apply (induct set: finite, simp_all, clarify)
apply (subst card_Un_disjoint)
   apply (auto simp add: disjoint_eq_subset_Compl)
done


subsubsection {* Relating injectivity and surjectivity *}

lemma finite_surj_inj: "finite(A) \<Longrightarrow> A <= f`A \<Longrightarrow> inj_on f A"
apply(rule eq_card_imp_inj_on, assumption)
apply(frule finite_imageI)
apply(drule (1) card_seteq)
 apply(erule card_image_le)
apply simp
done

lemma finite_UNIV_surj_inj: fixes f :: "'a \<Rightarrow> 'a"
shows "finite(UNIV:: 'a set) \<Longrightarrow> surj f \<Longrightarrow> inj f"
by (blast intro: finite_surj_inj subset_UNIV dest:surj_range)

lemma finite_UNIV_inj_surj: fixes f :: "'a \<Rightarrow> 'a"
shows "finite(UNIV:: 'a set) \<Longrightarrow> inj f \<Longrightarrow> surj f"
by(fastsimp simp:surj_def dest!: endo_inj_surj)

corollary infinite_UNIV_nat[iff]: "~finite(UNIV::nat set)"
proof
  assume "finite(UNIV::nat set)"
  with finite_UNIV_inj_surj[of Suc]
  show False by simp (blast dest: Suc_neq_Zero surjD)
qed

(* Often leads to bogus ATP proofs because of reduced type information, hence no_atp *)
lemma infinite_UNIV_char_0[no_atp]:
  "\<not> finite (UNIV::'a::semiring_char_0 set)"
proof
  assume "finite (UNIV::'a set)"
  with subset_UNIV have "finite (range of_nat::'a set)"
    by (rule finite_subset)
  moreover have "inj (of_nat::nat \<Rightarrow> 'a)"
    by (simp add: inj_on_def)
  ultimately have "finite (UNIV::nat set)"
    by (rule finite_imageD)
  then show "False"
    by simp
qed

end
