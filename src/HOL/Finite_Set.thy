(*  Title:      HOL/Finite_Set.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Lawrence C Paulson and Markus Wenzel
                with contributions by Jeremy Avigad
*)

header {* Finite sets *}

theory Finite_Set
imports Datatype Divides Transitive_Closure
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


subsubsection{* Finiteness and set theoretic constructions *}

lemma finite_UnI: "finite F ==> finite G ==> finite (F Un G)"
  -- {* The union of two finite sets is finite. *}
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

lemma finite_Collect_subset[simp]: "finite A \<Longrightarrow> finite{x \<in> A. P x}"
using finite_subset[of "{x \<in> A. P x}" "A"] by blast

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

lemma finite_Diff [simp]: "finite B ==> finite (B - Ba)"
  by (rule Diff_subset [THEN finite_subset])

lemma finite_Diff_insert [iff]: "finite (A - insert a B) = finite (A - B)"
  apply (subst Diff_insert)
  apply (case_tac "a : A - B")
   apply (rule finite_insert [symmetric, THEN trans])
   apply (subst insert_Diff, simp_all)
  done

lemma finite_Diff_singleton [simp]: "finite (A - {a}) = finite A"
  by simp


text {* Image and Inverse Image over Finite Sets *}

lemma finite_imageI[simp]: "finite F ==> finite (h ` F)"
  -- {* The image of a finite set is finite. *}
  by (induct set: finite) simp_all

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
  apply (simp add: finite_Un finite_subset [OF inj_vimage_singleton])
  done


text {* The finite UNION of finite sets *}

lemma finite_UN_I: "finite A ==> (!!a. a:A ==> finite (B a)) ==> finite (UN a:A. B a)"
  by (induct set: finite) simp_all

text {*
  Strengthen RHS to
  @{prop "((ALL x:A. finite (B x)) & finite {x. x:A & B x \<noteq> {}})"}?

  We'd need to prove
  @{prop "finite C ==> ALL A B. (UNION A B) <= C --> finite {x. x:A & B x \<noteq> {}}"}
  by induction. *}

lemma finite_UN [simp]: "finite A ==> finite (UNION A B) = (ALL x:A. finite (B x))"
  by (blast intro: finite_UN_I finite_subset)


lemma finite_Plus: "[| finite A; finite B |] ==> finite (A <+> B)"
by (simp add: Plus_def)

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
    by induct (simp_all add: finite_UnI finite_imageI Pow_insert)
qed


lemma finite_UnionD: "finite(\<Union>A) \<Longrightarrow> finite A"
by(blast intro: finite_subset[OF subset_Pow_Union])


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


text {* \paragraph{Finiteness of transitive closure} (Thanks to Sidi
Ehmety) *}

lemma finite_Field: "finite r ==> finite (Field r)"
  -- {* A finite relation has a finite field (@{text "= domain \<union> range"}. *}
  apply (induct set: finite)
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


subsection {* Class @{text finite}  *}

setup {* Sign.add_path "finite" *} -- {*FIXME: name tweaking*}
class finite = itself +
  assumes finite_UNIV: "finite (UNIV \<Colon> 'a set)"
setup {* Sign.parent_path *}
hide const finite

context finite
begin

lemma finite [simp]: "finite (A \<Colon> 'a set)"
  by (rule subset_UNIV finite_UNIV finite_subset)+

end

lemma UNIV_unit [noatp]:
  "UNIV = {()}" by auto

instance unit :: finite
  by default (simp add: UNIV_unit)

lemma UNIV_bool [noatp]:
  "UNIV = {False, True}" by auto

instance bool :: finite
  by default (simp add: UNIV_bool)

instance * :: (finite, finite) finite
  by default (simp only: UNIV_Times_UNIV [symmetric] finite_cartesian_product finite)

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

instance "+" :: (finite, finite) finite
  by default (simp only: UNIV_Plus_UNIV [symmetric] finite_Plus finite)

instance option :: (finite) finite
  by default (simp add: insert_None_conv_UNIV [symmetric])


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
    by (simp add: inj_on_swap_iff inj_on)
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
by (simp add: fold_insert fold_fun_comm)

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
  show ?thesis using assms by(simp add:fold_image_def I.fold_insert)
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
using fin apply induct
 apply simp
apply simp
done

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

end


subsection {* Generalized summation over a set *}

interpretation comm_monoid_add!: comm_monoid_mult "0::'a::comm_monoid_add" "op +"
  proof qed (auto intro: add_assoc add_commute)

definition setsum :: "('a => 'b) => 'a set => 'b::comm_monoid_add"
where "setsum f A == if finite A then fold_image (op +) f 0 A else 0"

abbreviation
  Setsum  ("\<Sum>_" [1000] 999) where
  "\<Sum>A == setsum (%x. x) A"

text{* Now: lot's of fancy syntax. First, @{term "setsum (%x. e) A"} is
written @{text"\<Sum>x\<in>A. e"}. *}

syntax
  "_setsum" :: "pttrn => 'a set => 'b => 'b::comm_monoid_add"    ("(3SUM _:_. _)" [0, 51, 10] 10)
syntax (xsymbols)
  "_setsum" :: "pttrn => 'a set => 'b => 'b::comm_monoid_add"    ("(3\<Sum>_\<in>_. _)" [0, 51, 10] 10)
syntax (HTML output)
  "_setsum" :: "pttrn => 'a set => 'b => 'b::comm_monoid_add"    ("(3\<Sum>_\<in>_. _)" [0, 51, 10] 10)

translations -- {* Beware of argument permutation! *}
  "SUM i:A. b" == "CONST setsum (%i. b) A"
  "\<Sum>i\<in>A. b" == "CONST setsum (%i. b) A"

text{* Instead of @{term"\<Sum>x\<in>{x. P}. e"} we introduce the shorter
 @{text"\<Sum>x|P. e"}. *}

syntax
  "_qsetsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3SUM _ |/ _./ _)" [0,0,10] 10)
syntax (xsymbols)
  "_qsetsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3\<Sum>_ | (_)./ _)" [0,0,10] 10)
syntax (HTML output)
  "_qsetsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3\<Sum>_ | (_)./ _)" [0,0,10] 10)

translations
  "SUM x|P. t" => "CONST setsum (%x. t) {x. P}"
  "\<Sum>x|P. t" => "CONST setsum (%x. t) {x. P}"

print_translation {*
let
  fun setsum_tr' [Abs(x,Tx,t), Const ("Collect",_) $ Abs(y,Ty,P)] = 
    if x<>y then raise Match
    else let val x' = Syntax.mark_bound x
             val t' = subst_bound(x',t)
             val P' = subst_bound(x',P)
         in Syntax.const "_qsetsum" $ Syntax.mark_bound x $ P' $ t' end
in [("setsum", setsum_tr')] end
*}


lemma setsum_empty [simp]: "setsum f {} = 0"
by (simp add: setsum_def)

lemma setsum_insert [simp]:
  "finite F ==> a \<notin> F ==> setsum f (insert a F) = f a + setsum f F"
by (simp add: setsum_def)

lemma setsum_infinite [simp]: "~ finite A ==> setsum f A = 0"
by (simp add: setsum_def)

lemma setsum_reindex:
     "inj_on f B ==> setsum h (f ` B) = setsum (h \<circ> f) B"
by(auto simp add: setsum_def comm_monoid_add.fold_image_reindex dest!:finite_imageD)

lemma setsum_reindex_id:
     "inj_on f B ==> setsum f B = setsum id (f ` B)"
by (auto simp add: setsum_reindex)

lemma setsum_cong:
  "A = B ==> (!!x. x:B ==> f x = g x) ==> setsum f A = setsum g B"
by(fastsimp simp: setsum_def intro: comm_monoid_add.fold_image_cong)

lemma strong_setsum_cong[cong]:
  "A = B ==> (!!x. x:B =simp=> f x = g x)
   ==> setsum (%x. f x) A = setsum (%x. g x) B"
by(fastsimp simp: simp_implies_def setsum_def intro: comm_monoid_add.fold_image_cong)

lemma setsum_cong2: "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> setsum f A = setsum g A";
by (rule setsum_cong[OF refl], auto);

lemma setsum_reindex_cong:
   "[|inj_on f A; B = f ` A; !!a. a:A \<Longrightarrow> g a = h (f a)|] 
    ==> setsum h B = setsum g A"
by (simp add: setsum_reindex cong: setsum_cong)

lemma setsum_0[simp]: "setsum (%i. 0) A = 0"
apply (clarsimp simp: setsum_def)
apply (erule finite_induct, auto)
done

lemma setsum_0': "ALL a:A. f a = 0 ==> setsum f A = 0"
by(simp add:setsum_cong)

lemma setsum_Un_Int: "finite A ==> finite B ==>
  setsum g (A Un B) + setsum g (A Int B) = setsum g A + setsum g B"
  -- {* The reversed orientation looks more natural, but LOOPS as a simprule! *}
by(simp add: setsum_def comm_monoid_add.fold_image_Un_Int [symmetric])

lemma setsum_Un_disjoint: "finite A ==> finite B
  ==> A Int B = {} ==> setsum g (A Un B) = setsum g A + setsum g B"
by (subst setsum_Un_Int [symmetric], auto)

(*But we can't get rid of finite I. If infinite, although the rhs is 0, 
  the lhs need not be, since UNION I A could still be finite.*)
lemma setsum_UN_disjoint:
    "finite I ==> (ALL i:I. finite (A i)) ==>
        (ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {}) ==>
      setsum f (UNION I A) = (\<Sum>i\<in>I. setsum f (A i))"
by(simp add: setsum_def comm_monoid_add.fold_image_UN_disjoint cong: setsum_cong)

text{*No need to assume that @{term C} is finite.  If infinite, the rhs is
directly 0, and @{term "Union C"} is also infinite, hence the lhs is also 0.*}
lemma setsum_Union_disjoint:
  "[| (ALL A:C. finite A);
      (ALL A:C. ALL B:C. A \<noteq> B --> A Int B = {}) |]
   ==> setsum f (Union C) = setsum (setsum f) C"
apply (cases "finite C") 
 prefer 2 apply (force dest: finite_UnionD simp add: setsum_def)
  apply (frule setsum_UN_disjoint [of C id f])
 apply (unfold Union_def id_def, assumption+)
done

(*But we can't get rid of finite A. If infinite, although the lhs is 0, 
  the rhs need not be, since SIGMA A B could still be finite.*)
lemma setsum_Sigma: "finite A ==> ALL x:A. finite (B x) ==>
    (\<Sum>x\<in>A. (\<Sum>y\<in>B x. f x y)) = (\<Sum>(x,y)\<in>(SIGMA x:A. B x). f x y)"
by(simp add:setsum_def comm_monoid_add.fold_image_Sigma split_def cong:setsum_cong)

text{*Here we can eliminate the finiteness assumptions, by cases.*}
lemma setsum_cartesian_product: 
   "(\<Sum>x\<in>A. (\<Sum>y\<in>B. f x y)) = (\<Sum>(x,y) \<in> A <*> B. f x y)"
apply (cases "finite A") 
 apply (cases "finite B") 
  apply (simp add: setsum_Sigma)
 apply (cases "A={}", simp)
 apply (simp) 
apply (auto simp add: setsum_def
            dest: finite_cartesian_productD1 finite_cartesian_productD2) 
done

lemma setsum_addf: "setsum (%x. f x + g x) A = (setsum f A + setsum g A)"
by(simp add:setsum_def comm_monoid_add.fold_image_distrib)


subsubsection {* Properties in more restricted classes of structures *}

lemma setsum_SucD: "setsum f A = Suc n ==> EX a:A. 0 < f a"
apply (case_tac "finite A")
 prefer 2 apply (simp add: setsum_def)
apply (erule rev_mp)
apply (erule finite_induct, auto)
done

lemma setsum_eq_0_iff [simp]:
    "finite F ==> (setsum f F = 0) = (ALL a:F. f a = (0::nat))"
by (induct set: finite) auto

lemma setsum_Un_nat: "finite A ==> finite B ==>
  (setsum f (A Un B) :: nat) = setsum f A + setsum f B - setsum f (A Int B)"
  -- {* For the natural numbers, we have subtraction. *}
by (subst setsum_Un_Int [symmetric], auto simp add: ring_simps)

lemma setsum_Un: "finite A ==> finite B ==>
  (setsum f (A Un B) :: 'a :: ab_group_add) =
   setsum f A + setsum f B - setsum f (A Int B)"
by (subst setsum_Un_Int [symmetric], auto simp add: ring_simps)

lemma setsum_diff1_nat: "(setsum f (A - {a}) :: nat) =
  (if a:A then setsum f A - f a else setsum f A)"
apply (case_tac "finite A")
 prefer 2 apply (simp add: setsum_def)
apply (erule finite_induct)
 apply (auto simp add: insert_Diff_if)
apply (drule_tac a = a in mk_disjoint_insert, auto)
done

lemma setsum_diff1: "finite A \<Longrightarrow>
  (setsum f (A - {a}) :: ('a::ab_group_add)) =
  (if a:A then setsum f A - f a else setsum f A)"
by (erule finite_induct) (auto simp add: insert_Diff_if)

lemma setsum_diff1'[rule_format]:
  "finite A \<Longrightarrow> a \<in> A \<longrightarrow> (\<Sum> x \<in> A. f x) = f a + (\<Sum> x \<in> (A - {a}). f x)"
apply (erule finite_induct[where F=A and P="% A. (a \<in> A \<longrightarrow> (\<Sum> x \<in> A. f x) = f a + (\<Sum> x \<in> (A - {a}). f x))"])
apply (auto simp add: insert_Diff_if add_ac)
done

(* By Jeremy Siek: *)

lemma setsum_diff_nat: 
assumes "finite B" and "B \<subseteq> A"
shows "(setsum f (A - B) :: nat) = (setsum f A) - (setsum f B)"
using assms
proof induct
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
  shows "setsum f (A - B) = setsum f A - ((setsum f B)::('a::ab_group_add))"
proof -
  from le have finiteB: "finite B" using finite_subset by auto
  show ?thesis using finiteB le
  proof induct
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
  proof induct
    case empty
    thus ?case by simp
  next
    case insert
    thus ?case using add_mono by fastsimp
  qed
next
  case False
  thus ?thesis
    by (simp add: setsum_def)
qed

lemma setsum_strict_mono:
  fixes f :: "'a \<Rightarrow> 'b::{pordered_cancel_ab_semigroup_add,comm_monoid_add}"
  assumes "finite A"  "A \<noteq> {}"
    and "!!x. x:A \<Longrightarrow> f x < g x"
  shows "setsum f A < setsum g A"
  using prems
proof (induct rule: finite_ne_induct)
  case singleton thus ?case by simp
next
  case insert thus ?case by (auto simp: add_strict_mono)
qed

lemma setsum_negf:
  "setsum (%x. - (f x)::'a::ab_group_add) A = - setsum f A"
proof (cases "finite A")
  case True thus ?thesis by (induct set: finite) auto
next
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma setsum_subtractf:
  "setsum (%x. ((f x)::'a::ab_group_add) - g x) A =
    setsum f A - setsum g A"
proof (cases "finite A")
  case True thus ?thesis by (simp add: diff_minus setsum_addf setsum_negf)
next
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma setsum_nonneg:
  assumes nn: "\<forall>x\<in>A. (0::'a::{pordered_ab_semigroup_add,comm_monoid_add}) \<le> f x"
  shows "0 \<le> setsum f A"
proof (cases "finite A")
  case True thus ?thesis using nn
  proof induct
    case empty then show ?case by simp
  next
    case (insert x F)
    then have "0 + 0 \<le> f x + setsum f F" by (blast intro: add_mono)
    with insert show ?case by simp
  qed
next
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma setsum_nonpos:
  assumes np: "\<forall>x\<in>A. f x \<le> (0::'a::{pordered_ab_semigroup_add,comm_monoid_add})"
  shows "setsum f A \<le> 0"
proof (cases "finite A")
  case True thus ?thesis using np
  proof induct
    case empty then show ?case by simp
  next
    case (insert x F)
    then have "f x + setsum f F \<le> 0 + 0" by (blast intro: add_mono)
    with insert show ?case by simp
  qed
next
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma setsum_mono2:
fixes f :: "'a \<Rightarrow> 'b :: {pordered_ab_semigroup_add_imp_le,comm_monoid_add}"
assumes fin: "finite B" and sub: "A \<subseteq> B" and nn: "\<And>b. b \<in> B-A \<Longrightarrow> 0 \<le> f b"
shows "setsum f A \<le> setsum f B"
proof -
  have "setsum f A \<le> setsum f A + setsum f (B-A)"
    by(simp add: add_increasing2[OF setsum_nonneg] nn Ball_def)
  also have "\<dots> = setsum f (A \<union> (B-A))" using fin finite_subset[OF sub fin]
    by (simp add:setsum_Un_disjoint del:Un_Diff_cancel)
  also have "A \<union> (B-A) = B" using sub by blast
  finally show ?thesis .
qed

lemma setsum_mono3: "finite B ==> A <= B ==> 
    ALL x: B - A. 
      0 <= ((f x)::'a::{comm_monoid_add,pordered_ab_semigroup_add}) ==>
        setsum f A <= setsum f B"
  apply (subgoal_tac "setsum f B = setsum f A + setsum f (B - A)")
  apply (erule ssubst)
  apply (subgoal_tac "setsum f A + 0 <= setsum f A + setsum f (B - A)")
  apply simp
  apply (rule add_left_mono)
  apply (erule setsum_nonneg)
  apply (subst setsum_Un_disjoint [THEN sym])
  apply (erule finite_subset, assumption)
  apply (rule finite_subset)
  prefer 2
  apply assumption
  apply auto
  apply (rule setsum_cong)
  apply auto
done

lemma setsum_right_distrib: 
  fixes f :: "'a => ('b::semiring_0)"
  shows "r * setsum f A = setsum (%n. r * f n) A"
proof (cases "finite A")
  case True
  thus ?thesis
  proof induct
    case empty thus ?case by simp
  next
    case (insert x A) thus ?case by (simp add: right_distrib)
  qed
next
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma setsum_left_distrib:
  "setsum f A * (r::'a::semiring_0) = (\<Sum>n\<in>A. f n * r)"
proof (cases "finite A")
  case True
  then show ?thesis
  proof induct
    case empty thus ?case by simp
  next
    case (insert x A) thus ?case by (simp add: left_distrib)
  qed
next
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma setsum_divide_distrib:
  "setsum f A / (r::'a::field) = (\<Sum>n\<in>A. f n / r)"
proof (cases "finite A")
  case True
  then show ?thesis
  proof induct
    case empty thus ?case by simp
  next
    case (insert x A) thus ?case by (simp add: add_divide_distrib)
  qed
next
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma setsum_abs[iff]: 
  fixes f :: "'a => ('b::pordered_ab_group_add_abs)"
  shows "abs (setsum f A) \<le> setsum (%i. abs(f i)) A"
proof (cases "finite A")
  case True
  thus ?thesis
  proof induct
    case empty thus ?case by simp
  next
    case (insert x A)
    thus ?case by (auto intro: abs_triangle_ineq order_trans)
  qed
next
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma setsum_abs_ge_zero[iff]: 
  fixes f :: "'a => ('b::pordered_ab_group_add_abs)"
  shows "0 \<le> setsum (%i. abs(f i)) A"
proof (cases "finite A")
  case True
  thus ?thesis
  proof induct
    case empty thus ?case by simp
  next
    case (insert x A) thus ?case by (auto simp: add_nonneg_nonneg)
  qed
next
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma abs_setsum_abs[simp]: 
  fixes f :: "'a => ('b::pordered_ab_group_add_abs)"
  shows "abs (\<Sum>a\<in>A. abs(f a)) = (\<Sum>a\<in>A. abs(f a))"
proof (cases "finite A")
  case True
  thus ?thesis
  proof induct
    case empty thus ?case by simp
  next
    case (insert a A)
    hence "\<bar>\<Sum>a\<in>insert a A. \<bar>f a\<bar>\<bar> = \<bar>\<bar>f a\<bar> + (\<Sum>a\<in>A. \<bar>f a\<bar>)\<bar>" by simp
    also have "\<dots> = \<bar>\<bar>f a\<bar> + \<bar>\<Sum>a\<in>A. \<bar>f a\<bar>\<bar>\<bar>"  using insert by simp
    also have "\<dots> = \<bar>f a\<bar> + \<bar>\<Sum>a\<in>A. \<bar>f a\<bar>\<bar>"
      by (simp del: abs_of_nonneg)
    also have "\<dots> = (\<Sum>a\<in>insert a A. \<bar>f a\<bar>)" using insert by simp
    finally show ?case .
  qed
next
  case False thus ?thesis by (simp add: setsum_def)
qed


text {* Commuting outer and inner summation *}

lemma swap_inj_on:
  "inj_on (%(i, j). (j, i)) (A \<times> B)"
  by (unfold inj_on_def) fast

lemma swap_product:
  "(%(i, j). (j, i)) ` (A \<times> B) = B \<times> A"
  by (simp add: split_def image_def) blast

lemma setsum_commute:
  "(\<Sum>i\<in>A. \<Sum>j\<in>B. f i j) = (\<Sum>j\<in>B. \<Sum>i\<in>A. f i j)"
proof (simp add: setsum_cartesian_product)
  have "(\<Sum>(x,y) \<in> A <*> B. f x y) =
    (\<Sum>(y,x) \<in> (%(i, j). (j, i)) ` (A \<times> B). f x y)"
    (is "?s = _")
    apply (simp add: setsum_reindex [where f = "%(i, j). (j, i)"] swap_inj_on)
    apply (simp add: split_def)
    done
  also have "... = (\<Sum>(y,x)\<in>B \<times> A. f x y)"
    (is "_ = ?t")
    apply (simp add: swap_product)
    done
  finally show "?s = ?t" .
qed

lemma setsum_product:
  fixes f :: "'a => ('b::semiring_0)"
  shows "setsum f A * setsum g B = (\<Sum>i\<in>A. \<Sum>j\<in>B. f i * g j)"
  by (simp add: setsum_right_distrib setsum_left_distrib) (rule setsum_commute)


subsection {* Generalized product over a set *}

definition setprod :: "('a => 'b) => 'a set => 'b::comm_monoid_mult"
where "setprod f A == if finite A then fold_image (op *) f 1 A else 1"

abbreviation
  Setprod  ("\<Prod>_" [1000] 999) where
  "\<Prod>A == setprod (%x. x) A"

syntax
  "_setprod" :: "pttrn => 'a set => 'b => 'b::comm_monoid_mult"  ("(3PROD _:_. _)" [0, 51, 10] 10)
syntax (xsymbols)
  "_setprod" :: "pttrn => 'a set => 'b => 'b::comm_monoid_mult"  ("(3\<Prod>_\<in>_. _)" [0, 51, 10] 10)
syntax (HTML output)
  "_setprod" :: "pttrn => 'a set => 'b => 'b::comm_monoid_mult"  ("(3\<Prod>_\<in>_. _)" [0, 51, 10] 10)

translations -- {* Beware of argument permutation! *}
  "PROD i:A. b" == "CONST setprod (%i. b) A" 
  "\<Prod>i\<in>A. b" == "CONST setprod (%i. b) A" 

text{* Instead of @{term"\<Prod>x\<in>{x. P}. e"} we introduce the shorter
 @{text"\<Prod>x|P. e"}. *}

syntax
  "_qsetprod" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3PROD _ |/ _./ _)" [0,0,10] 10)
syntax (xsymbols)
  "_qsetprod" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3\<Prod>_ | (_)./ _)" [0,0,10] 10)
syntax (HTML output)
  "_qsetprod" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3\<Prod>_ | (_)./ _)" [0,0,10] 10)

translations
  "PROD x|P. t" => "CONST setprod (%x. t) {x. P}"
  "\<Prod>x|P. t" => "CONST setprod (%x. t) {x. P}"


lemma setprod_empty [simp]: "setprod f {} = 1"
by (auto simp add: setprod_def)

lemma setprod_insert [simp]: "[| finite A; a \<notin> A |] ==>
    setprod f (insert a A) = f a * setprod f A"
by (simp add: setprod_def)

lemma setprod_infinite [simp]: "~ finite A ==> setprod f A = 1"
by (simp add: setprod_def)

lemma setprod_reindex:
   "inj_on f B ==> setprod h (f ` B) = setprod (h \<circ> f) B"
by(auto simp: setprod_def fold_image_reindex dest!:finite_imageD)

lemma setprod_reindex_id: "inj_on f B ==> setprod f B = setprod id (f ` B)"
by (auto simp add: setprod_reindex)

lemma setprod_cong:
  "A = B ==> (!!x. x:B ==> f x = g x) ==> setprod f A = setprod g B"
by(fastsimp simp: setprod_def intro: fold_image_cong)

lemma strong_setprod_cong:
  "A = B ==> (!!x. x:B =simp=> f x = g x) ==> setprod f A = setprod g B"
by(fastsimp simp: simp_implies_def setprod_def intro: fold_image_cong)

lemma setprod_reindex_cong: "inj_on f A ==>
    B = f ` A ==> g = h \<circ> f ==> setprod h B = setprod g A"
by (frule setprod_reindex, simp)


lemma setprod_1: "setprod (%i. 1) A = 1"
apply (case_tac "finite A")
apply (erule finite_induct, auto simp add: mult_ac)
done

lemma setprod_1': "ALL a:F. f a = 1 ==> setprod f F = 1"
apply (subgoal_tac "setprod f F = setprod (%x. 1) F")
apply (erule ssubst, rule setprod_1)
apply (rule setprod_cong, auto)
done

lemma setprod_Un_Int: "finite A ==> finite B
    ==> setprod g (A Un B) * setprod g (A Int B) = setprod g A * setprod g B"
by(simp add: setprod_def fold_image_Un_Int[symmetric])

lemma setprod_Un_disjoint: "finite A ==> finite B
  ==> A Int B = {} ==> setprod g (A Un B) = setprod g A * setprod g B"
by (subst setprod_Un_Int [symmetric], auto)

lemma setprod_UN_disjoint:
    "finite I ==> (ALL i:I. finite (A i)) ==>
        (ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {}) ==>
      setprod f (UNION I A) = setprod (%i. setprod f (A i)) I"
by(simp add: setprod_def fold_image_UN_disjoint cong: setprod_cong)

lemma setprod_Union_disjoint:
  "[| (ALL A:C. finite A);
      (ALL A:C. ALL B:C. A \<noteq> B --> A Int B = {}) |] 
   ==> setprod f (Union C) = setprod (setprod f) C"
apply (cases "finite C") 
 prefer 2 apply (force dest: finite_UnionD simp add: setprod_def)
  apply (frule setprod_UN_disjoint [of C id f])
 apply (unfold Union_def id_def, assumption+)
done

lemma setprod_Sigma: "finite A ==> ALL x:A. finite (B x) ==>
    (\<Prod>x\<in>A. (\<Prod>y\<in> B x. f x y)) =
    (\<Prod>(x,y)\<in>(SIGMA x:A. B x). f x y)"
by(simp add:setprod_def fold_image_Sigma split_def cong:setprod_cong)

text{*Here we can eliminate the finiteness assumptions, by cases.*}
lemma setprod_cartesian_product: 
     "(\<Prod>x\<in>A. (\<Prod>y\<in> B. f x y)) = (\<Prod>(x,y)\<in>(A <*> B). f x y)"
apply (cases "finite A") 
 apply (cases "finite B") 
  apply (simp add: setprod_Sigma)
 apply (cases "A={}", simp)
 apply (simp add: setprod_1) 
apply (auto simp add: setprod_def
            dest: finite_cartesian_productD1 finite_cartesian_productD2) 
done

lemma setprod_timesf:
     "setprod (%x. f x * g x) A = (setprod f A * setprod g A)"
by(simp add:setprod_def fold_image_distrib)


subsubsection {* Properties in more restricted classes of structures *}

lemma setprod_eq_1_iff [simp]:
  "finite F ==> (setprod f F = 1) = (ALL a:F. f a = (1::nat))"
by (induct set: finite) auto

lemma setprod_zero:
     "finite A ==> EX x: A. f x = (0::'a::comm_semiring_1) ==> setprod f A = 0"
apply (induct set: finite, force, clarsimp)
apply (erule disjE, auto)
done

lemma setprod_nonneg [rule_format]:
   "(ALL x: A. (0::'a::ordered_idom) \<le> f x) --> 0 \<le> setprod f A"
apply (case_tac "finite A")
apply (induct set: finite, force, clarsimp)
apply (subgoal_tac "0 * 0 \<le> f x * setprod f F", force)
apply (rule mult_mono, assumption+)
apply (auto simp add: setprod_def)
done

lemma setprod_pos [rule_format]: "(ALL x: A. (0::'a::ordered_idom) < f x)
  --> 0 < setprod f A"
apply (case_tac "finite A")
apply (induct set: finite, force, clarsimp)
apply (subgoal_tac "0 * 0 < f x * setprod f F", force)
apply (rule mult_strict_mono, assumption+)
apply (auto simp add: setprod_def)
done

lemma setprod_nonzero [rule_format]:
  "(ALL x y. (x::'a::comm_semiring_1) * y = 0 --> x = 0 | y = 0) ==>
    finite A ==> (ALL x: A. f x \<noteq> (0::'a)) --> setprod f A \<noteq> 0"
by (erule finite_induct, auto)

lemma setprod_zero_eq:
    "(ALL x y. (x::'a::comm_semiring_1) * y = 0 --> x = 0 | y = 0) ==>
     finite A ==> (setprod f A = (0::'a)) = (EX x: A. f x = 0)"
by (insert setprod_zero [of A f] setprod_nonzero [of A f], blast)

lemma setprod_nonzero_field:
    "finite A ==> (ALL x: A. f x \<noteq> (0::'a::idom)) ==> setprod f A \<noteq> 0"
by (rule setprod_nonzero, auto)

lemma setprod_zero_eq_field:
    "finite A ==> (setprod f A = (0::'a::idom)) = (EX x: A. f x = 0)"
by (rule setprod_zero_eq, auto)

lemma setprod_Un: "finite A ==> finite B ==> (ALL x: A Int B. f x \<noteq> 0) ==>
  (setprod f (A Un B) :: 'a ::{field})
   = setprod f A * setprod f B / setprod f (A Int B)"
apply (subst setprod_Un_Int [symmetric], auto)
apply (subgoal_tac "finite (A Int B)")
apply (frule setprod_nonzero_field [of "A Int B" f], assumption)
apply (subst times_divide_eq_right [THEN sym], auto)
done

lemma setprod_diff1: "finite A ==> f a \<noteq> 0 ==>
  (setprod f (A - {a}) :: 'a :: {field}) =
  (if a:A then setprod f A / f a else setprod f A)"
by (erule finite_induct) (auto simp add: insert_Diff_if)

lemma setprod_inversef: "finite A ==>
  ALL x: A. f x \<noteq> (0::'a::{field,division_by_zero}) ==>
  setprod (inverse \<circ> f) A = inverse (setprod f A)"
by (erule finite_induct) auto

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


subsection {* Finite cardinality *}

text {* This definition, although traditional, is ugly to work with:
@{text "card A == LEAST n. EX f. A = {f i | i. i < n}"}.
But now that we have @{text setsum} things are easy:
*}

definition card :: "'a set \<Rightarrow> nat"
where "card A = setsum (\<lambda>x. 1) A"

lemma card_empty [simp]: "card {} = 0"
by (simp add: card_def)

lemma card_infinite [simp]: "~ finite A ==> card A = 0"
by (simp add: card_def)

lemma card_eq_setsum: "card A = setsum (%x. 1) A"
by (simp add: card_def)

lemma card_insert_disjoint [simp]:
  "finite A ==> x \<notin> A ==> card (insert x A) = Suc(card A)"
by(simp add: card_def)

lemma card_insert_if:
  "finite A ==> card (insert x A) = (if x:A then card A else Suc(card(A)))"
by (simp add: insert_absorb)

lemma card_0_eq [simp,noatp]: "finite A ==> (card A = 0) = (A = {})"
apply auto
apply (drule_tac a = x in mk_disjoint_insert, clarify, auto)
done

lemma card_eq_0_iff: "(card A = 0) = (A = {} | ~ finite A)"
by auto


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

lemma card_mono: "\<lbrakk> finite B; A \<subseteq> B \<rbrakk> \<Longrightarrow> card A \<le> card B"
by (simp add: card_def setsum_mono2)

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
by(simp add:card_def setsum_Un_Int)

lemma card_Un_disjoint: "finite A ==> finite B
    ==> A Int B = {} ==> card (A Un B) = card A + card B"
by (simp add: card_Un_Int)

lemma card_Diff_subset:
  "finite B ==> B <= A ==> card (A - B) = card A - card B"
by(simp add:card_def setsum_diff_nat)

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

text{* main cardinality theorem *}
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

lemma setsum_constant [simp]: "(\<Sum>x \<in> A. y) = of_nat(card A) * y"
apply (cases "finite A")
apply (erule finite_induct)
apply (auto simp add: ring_simps)
done

lemma setprod_constant: "finite A ==> (\<Prod>x\<in> A. (y::'a::{recpower, comm_monoid_mult})) = y^(card A)"
apply (erule finite_induct)
apply (auto simp add: power_Suc)
done

lemma setsum_bounded:
  assumes le: "\<And>i. i\<in>A \<Longrightarrow> f i \<le> (K::'a::{semiring_1, pordered_ab_semigroup_add})"
  shows "setsum f A \<le> of_nat(card A) * K"
proof (cases "finite A")
  case True
  thus ?thesis using le setsum_mono[where K=A and g = "%x. K"] by simp
next
  case False thus ?thesis by (simp add: setsum_def)
qed


subsubsection {* Cardinality of unions *}

lemma card_UN_disjoint:
  "finite I ==> (ALL i:I. finite (A i)) ==>
   (ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {})
   ==> card (UNION I A) = (\<Sum>i\<in>I. card(A i))"
apply (simp add: card_def del: setsum_constant)
apply (subgoal_tac
         "setsum (%i. card (A i)) I = setsum (%i. (setsum (%x. 1) (A i))) I")
apply (simp add: setsum_UN_disjoint del: setsum_constant)
apply (simp cong: setsum_cong)
done

lemma card_Union_disjoint:
  "finite C ==> (ALL A:C. finite A) ==>
   (ALL A:C. ALL B:C. A \<noteq> B --> A Int B = {})
   ==> card (Union C) = setsum card C"
apply (frule card_UN_disjoint [of C id])
apply (unfold Union_def id_def, assumption+)
done


subsubsection {* Cardinality of image *}

text{*The image of a finite set can be expressed using @{term fold_image}.*}
lemma image_eq_fold_image:
  "finite A ==> f ` A = fold_image (op Un) (%x. {f x}) {} A"
proof (induct rule: finite_induct)
  case empty then show ?case by simp
next
  interpret ab_semigroup_mult "op Un"
    proof qed auto
  case insert 
  then show ?case by simp
qed

lemma card_image_le: "finite A ==> card (f ` A) <= card A"
apply (induct set: finite)
 apply simp
apply (simp add: le_SucI finite_imageI card_insert_if)
done

lemma card_image: "inj_on f A ==> card (f ` A) = card A"
by(simp add:card_def setsum_reindex o_def del:setsum_constant)

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
by (auto intro: le_anti_sym card_inj_on_le)


subsubsection {* Cardinality of products *}

(*
lemma SigmaI_insert: "y \<notin> A ==>
  (SIGMA x:(insert y A). B x) = (({y} <*> (B y)) \<union> (SIGMA x: A. B x))"
  by auto
*)

lemma card_SigmaI [simp]:
  "\<lbrakk> finite A; ALL a:A. finite (B a) \<rbrakk>
  \<Longrightarrow> card (SIGMA x: A. B x) = (\<Sum>a\<in>A. card (B a))"
by(simp add:card_def setsum_Sigma del:setsum_constant)

lemma card_cartesian_product: "card (A <*> B) = card(A) * card(B)"
apply (cases "finite A") 
apply (cases "finite B") 
apply (auto simp add: card_eq_0_iff
            dest: finite_cartesian_productD1 finite_cartesian_productD2)
done

lemma card_cartesian_product_singleton:  "card({x} <*> A) = card(A)"
by (simp add: card_cartesian_product)


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

text {* Relates to equivalence classes.  Based on a theorem of F. Kamm�ller.  *}

lemma dvd_partition:
  "finite (Union C) ==>
    ALL c : C. k dvd card c ==>
    (ALL c1: C. ALL c2: C. c1 \<noteq> c2 --> c1 Int c2 = {}) ==>
  k dvd card (Union C)"
apply(frule finite_UnionD)
apply(rotate_tac -1)
apply (induct set: finite, simp_all, clarify)
apply (subst card_Un_disjoint)
   apply (auto simp add: dvd_add disjoint_eq_subset_Compl)
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

corollary infinite_UNIV_nat: "~finite(UNIV::nat set)"
proof
  assume "finite(UNIV::nat set)"
  with finite_UNIV_inj_surj[of Suc]
  show False by simp (blast dest: Suc_neq_Zero surjD)
qed


subsection{* A fold functional for non-empty sets *}

text{* Does not require start value. *}

inductive
  fold1Set :: "('a => 'a => 'a) => 'a set => 'a => bool"
  for f :: "'a => 'a => 'a"
where
  fold1Set_insertI [intro]:
   "\<lbrakk> fold_graph f a A x; a \<notin> A \<rbrakk> \<Longrightarrow> fold1Set f (insert a A) x"

constdefs
  fold1 :: "('a => 'a => 'a) => 'a set => 'a"
  "fold1 f A == THE x. fold1Set f A x"

lemma fold1Set_nonempty:
  "fold1Set f A x \<Longrightarrow> A \<noteq> {}"
by(erule fold1Set.cases, simp_all)

inductive_cases empty_fold1SetE [elim!]: "fold1Set f {} x"

inductive_cases insert_fold1SetE [elim!]: "fold1Set f (insert a X) x"


lemma fold1Set_sing [iff]: "(fold1Set f {a} b) = (a = b)"
by (blast intro: fold_graph.intros elim: fold_graph.cases)

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
 apply (best intro: the_equality fold_graph_determ)
apply (subgoal_tac "fold_graph times a A x")
 apply (best intro: the_equality fold_graph_determ)
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

lemma fun_left_comm_idem: "fun_left_comm_idem(op *)"
apply unfold_locales
 apply (simp add: mult_ac)
apply (simp add: mult_idem mult_assoc[symmetric])
done


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
      with prems show ?thesis by (simp add: mult_idem)
    next
      assume "A' \<noteq> {}"
      with prems show ?thesis
	by (simp add: fold1_insert mult_assoc [symmetric] mult_idem)
    qed
  next
    assume "a \<noteq> x"
    with prems show ?thesis
      by (simp add: insert_commute fold1_eq_fold fold_insert_idem)
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

end


text{* Now the recursion rules for definitions: *}

lemma fold1_singleton_def: "g = fold1 f \<Longrightarrow> g {a} = a"
by(simp add:fold1_singleton)

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


subsubsection {* Fold1 in lattices with @{const inf} and @{const sup} *}

text{*
  As an application of @{text fold1} we define infimum
  and supremum in (not necessarily complete!) lattices
  over (non-empty) sets by means of @{text fold1}.
*}

context lower_semilattice
begin

lemma ab_semigroup_idem_mult_inf:
  "ab_semigroup_idem_mult inf"
  proof qed (rule inf_assoc inf_commute inf_idem)+

lemma below_fold1_iff:
  assumes "finite A" "A \<noteq> {}"
  shows "x \<le> fold1 inf A \<longleftrightarrow> (\<forall>a\<in>A. x \<le> a)"
proof -
  interpret ab_semigroup_idem_mult inf
    by (rule ab_semigroup_idem_mult_inf)
  show ?thesis using assms by (induct rule: finite_ne_induct) simp_all
qed

lemma fold1_belowI:
  assumes "finite A"
    and "a \<in> A"
  shows "fold1 inf A \<le> a"
proof -
  from assms have "A \<noteq> {}" by auto
  from `finite A` `A \<noteq> {}` `a \<in> A` show ?thesis
  proof (induct rule: finite_ne_induct)
    case singleton thus ?case by simp
  next
    interpret ab_semigroup_idem_mult inf
      by (rule ab_semigroup_idem_mult_inf)
    case (insert x F)
    from insert(5) have "a = x \<or> a \<in> F" by simp
    thus ?case
    proof
      assume "a = x" thus ?thesis using insert
        by (simp add: mult_ac_idem)
    next
      assume "a \<in> F"
      hence bel: "fold1 inf F \<le> a" by (rule insert)
      have "inf (fold1 inf (insert x F)) a = inf x (inf (fold1 inf F) a)"
        using insert by (simp add: mult_ac_idem)
      also have "inf (fold1 inf F) a = fold1 inf F"
        using bel by (auto intro: antisym)
      also have "inf x \<dots> = fold1 inf (insert x F)"
        using insert by (simp add: mult_ac_idem)
      finally have aux: "inf (fold1 inf (insert x F)) a = fold1 inf (insert x F)" .
      moreover have "inf (fold1 inf (insert x F)) a \<le> a" by simp
      ultimately show ?thesis by simp
    qed
  qed
qed

end

lemma (in upper_semilattice) ab_semigroup_idem_mult_sup:
  "ab_semigroup_idem_mult sup"
  by (rule lower_semilattice.ab_semigroup_idem_mult_inf)
    (rule dual_lattice)

context lattice
begin

definition
  Inf_fin :: "'a set \<Rightarrow> 'a" ("\<Sqinter>\<^bsub>fin\<^esub>_" [900] 900)
where
  "Inf_fin = fold1 inf"

definition
  Sup_fin :: "'a set \<Rightarrow> 'a" ("\<Squnion>\<^bsub>fin\<^esub>_" [900] 900)
where
  "Sup_fin = fold1 sup"

lemma Inf_le_Sup [simp]: "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> \<Sqinter>\<^bsub>fin\<^esub>A \<le> \<Squnion>\<^bsub>fin\<^esub>A"
apply(unfold Sup_fin_def Inf_fin_def)
apply(subgoal_tac "EX a. a:A")
prefer 2 apply blast
apply(erule exE)
apply(rule order_trans)
apply(erule (1) fold1_belowI)
apply(erule (1) lower_semilattice.fold1_belowI [OF dual_lattice])
done

lemma sup_Inf_absorb [simp]:
  "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> sup a (\<Sqinter>\<^bsub>fin\<^esub>A) = a"
apply(subst sup_commute)
apply(simp add: Inf_fin_def sup_absorb2 fold1_belowI)
done

lemma inf_Sup_absorb [simp]:
  "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> inf a (\<Squnion>\<^bsub>fin\<^esub>A) = a"
by (simp add: Sup_fin_def inf_absorb1
  lower_semilattice.fold1_belowI [OF dual_lattice])

end

context distrib_lattice
begin

lemma sup_Inf1_distrib:
  assumes "finite A"
    and "A \<noteq> {}"
  shows "sup x (\<Sqinter>\<^bsub>fin\<^esub>A) = \<Sqinter>\<^bsub>fin\<^esub>{sup x a|a. a \<in> A}"
proof -
  interpret ab_semigroup_idem_mult inf
    by (rule ab_semigroup_idem_mult_inf)
  from assms show ?thesis
    by (simp add: Inf_fin_def image_def
      hom_fold1_commute [where h="sup x", OF sup_inf_distrib1])
        (rule arg_cong [where f="fold1 inf"], blast)
qed

lemma sup_Inf2_distrib:
  assumes A: "finite A" "A \<noteq> {}" and B: "finite B" "B \<noteq> {}"
  shows "sup (\<Sqinter>\<^bsub>fin\<^esub>A) (\<Sqinter>\<^bsub>fin\<^esub>B) = \<Sqinter>\<^bsub>fin\<^esub>{sup a b|a b. a \<in> A \<and> b \<in> B}"
using A proof (induct rule: finite_ne_induct)
  case singleton thus ?case
    by (simp add: sup_Inf1_distrib [OF B] fold1_singleton_def [OF Inf_fin_def])
next
  interpret ab_semigroup_idem_mult inf
    by (rule ab_semigroup_idem_mult_inf)
  case (insert x A)
  have finB: "finite {sup x b |b. b \<in> B}"
    by(rule finite_surj[where f = "sup x", OF B(1)], auto)
  have finAB: "finite {sup a b |a b. a \<in> A \<and> b \<in> B}"
  proof -
    have "{sup a b |a b. a \<in> A \<and> b \<in> B} = (UN a:A. UN b:B. {sup a b})"
      by blast
    thus ?thesis by(simp add: insert(1) B(1))
  qed
  have ne: "{sup a b |a b. a \<in> A \<and> b \<in> B} \<noteq> {}" using insert B by blast
  have "sup (\<Sqinter>\<^bsub>fin\<^esub>(insert x A)) (\<Sqinter>\<^bsub>fin\<^esub>B) = sup (inf x (\<Sqinter>\<^bsub>fin\<^esub>A)) (\<Sqinter>\<^bsub>fin\<^esub>B)"
    using insert by (simp add: fold1_insert_idem_def [OF Inf_fin_def])
  also have "\<dots> = inf (sup x (\<Sqinter>\<^bsub>fin\<^esub>B)) (sup (\<Sqinter>\<^bsub>fin\<^esub>A) (\<Sqinter>\<^bsub>fin\<^esub>B))" by(rule sup_inf_distrib2)
  also have "\<dots> = inf (\<Sqinter>\<^bsub>fin\<^esub>{sup x b|b. b \<in> B}) (\<Sqinter>\<^bsub>fin\<^esub>{sup a b|a b. a \<in> A \<and> b \<in> B})"
    using insert by(simp add:sup_Inf1_distrib[OF B])
  also have "\<dots> = \<Sqinter>\<^bsub>fin\<^esub>({sup x b |b. b \<in> B} \<union> {sup a b |a b. a \<in> A \<and> b \<in> B})"
    (is "_ = \<Sqinter>\<^bsub>fin\<^esub>?M")
    using B insert
    by (simp add: Inf_fin_def fold1_Un2 [OF finB _ finAB ne])
  also have "?M = {sup a b |a b. a \<in> insert x A \<and> b \<in> B}"
    by blast
  finally show ?case .
qed

lemma inf_Sup1_distrib:
  assumes "finite A" and "A \<noteq> {}"
  shows "inf x (\<Squnion>\<^bsub>fin\<^esub>A) = \<Squnion>\<^bsub>fin\<^esub>{inf x a|a. a \<in> A}"
proof -
  interpret ab_semigroup_idem_mult sup
    by (rule ab_semigroup_idem_mult_sup)
  from assms show ?thesis
    by (simp add: Sup_fin_def image_def hom_fold1_commute [where h="inf x", OF inf_sup_distrib1])
      (rule arg_cong [where f="fold1 sup"], blast)
qed

lemma inf_Sup2_distrib:
  assumes A: "finite A" "A \<noteq> {}" and B: "finite B" "B \<noteq> {}"
  shows "inf (\<Squnion>\<^bsub>fin\<^esub>A) (\<Squnion>\<^bsub>fin\<^esub>B) = \<Squnion>\<^bsub>fin\<^esub>{inf a b|a b. a \<in> A \<and> b \<in> B}"
using A proof (induct rule: finite_ne_induct)
  case singleton thus ?case
    by(simp add: inf_Sup1_distrib [OF B] fold1_singleton_def [OF Sup_fin_def])
next
  case (insert x A)
  have finB: "finite {inf x b |b. b \<in> B}"
    by(rule finite_surj[where f = "%b. inf x b", OF B(1)], auto)
  have finAB: "finite {inf a b |a b. a \<in> A \<and> b \<in> B}"
  proof -
    have "{inf a b |a b. a \<in> A \<and> b \<in> B} = (UN a:A. UN b:B. {inf a b})"
      by blast
    thus ?thesis by(simp add: insert(1) B(1))
  qed
  have ne: "{inf a b |a b. a \<in> A \<and> b \<in> B} \<noteq> {}" using insert B by blast
  interpret ab_semigroup_idem_mult sup
    by (rule ab_semigroup_idem_mult_sup)
  have "inf (\<Squnion>\<^bsub>fin\<^esub>(insert x A)) (\<Squnion>\<^bsub>fin\<^esub>B) = inf (sup x (\<Squnion>\<^bsub>fin\<^esub>A)) (\<Squnion>\<^bsub>fin\<^esub>B)"
    using insert by (simp add: fold1_insert_idem_def [OF Sup_fin_def])
  also have "\<dots> = sup (inf x (\<Squnion>\<^bsub>fin\<^esub>B)) (inf (\<Squnion>\<^bsub>fin\<^esub>A) (\<Squnion>\<^bsub>fin\<^esub>B))" by(rule inf_sup_distrib2)
  also have "\<dots> = sup (\<Squnion>\<^bsub>fin\<^esub>{inf x b|b. b \<in> B}) (\<Squnion>\<^bsub>fin\<^esub>{inf a b|a b. a \<in> A \<and> b \<in> B})"
    using insert by(simp add:inf_Sup1_distrib[OF B])
  also have "\<dots> = \<Squnion>\<^bsub>fin\<^esub>({inf x b |b. b \<in> B} \<union> {inf a b |a b. a \<in> A \<and> b \<in> B})"
    (is "_ = \<Squnion>\<^bsub>fin\<^esub>?M")
    using B insert
    by (simp add: Sup_fin_def fold1_Un2 [OF finB _ finAB ne])
  also have "?M = {inf a b |a b. a \<in> insert x A \<and> b \<in> B}"
    by blast
  finally show ?case .
qed

end

context complete_lattice
begin

text {*
  Coincidence on finite sets in complete lattices:
*}

lemma Inf_fin_Inf:
  assumes "finite A" and "A \<noteq> {}"
  shows "\<Sqinter>\<^bsub>fin\<^esub>A = Inf A"
proof -
    interpret ab_semigroup_idem_mult inf
    by (rule ab_semigroup_idem_mult_inf)
  from assms show ?thesis
  unfolding Inf_fin_def by (induct A set: finite)
    (simp_all add: Inf_insert_simp)
qed

lemma Sup_fin_Sup:
  assumes "finite A" and "A \<noteq> {}"
  shows "\<Squnion>\<^bsub>fin\<^esub>A = Sup A"
proof -
  interpret ab_semigroup_idem_mult sup
    by (rule ab_semigroup_idem_mult_sup)
  from assms show ?thesis
  unfolding Sup_fin_def by (induct A set: finite)
    (simp_all add: Sup_insert_simp)
qed

end


subsubsection {* Fold1 in linear orders with @{const min} and @{const max} *}

text{*
  As an application of @{text fold1} we define minimum
  and maximum in (not necessarily complete!) linear orders
  over (non-empty) sets by means of @{text fold1}.
*}

context linorder
begin

lemma ab_semigroup_idem_mult_min:
  "ab_semigroup_idem_mult min"
  proof qed (auto simp add: min_def)

lemma ab_semigroup_idem_mult_max:
  "ab_semigroup_idem_mult max"
  proof qed (auto simp add: max_def)

lemma min_lattice:
  "lower_semilattice (op \<le>) (op <) min"
  proof qed (auto simp add: min_def)

lemma max_lattice:
  "lower_semilattice (op \<ge>) (op >) max"
  proof qed (auto simp add: max_def)

lemma dual_max:
  "ord.max (op \<ge>) = min"
  by (auto simp add: ord.max_def_raw min_def_raw expand_fun_eq)

lemma dual_min:
  "ord.min (op \<ge>) = max"
  by (auto simp add: ord.min_def_raw max_def_raw expand_fun_eq)

lemma strict_below_fold1_iff:
  assumes "finite A" and "A \<noteq> {}"
  shows "x < fold1 min A \<longleftrightarrow> (\<forall>a\<in>A. x < a)"
proof -
  interpret ab_semigroup_idem_mult min
    by (rule ab_semigroup_idem_mult_min)
  from assms show ?thesis
  by (induct rule: finite_ne_induct)
    (simp_all add: fold1_insert)
qed

lemma fold1_below_iff:
  assumes "finite A" and "A \<noteq> {}"
  shows "fold1 min A \<le> x \<longleftrightarrow> (\<exists>a\<in>A. a \<le> x)"
proof -
  interpret ab_semigroup_idem_mult min
    by (rule ab_semigroup_idem_mult_min)
  from assms show ?thesis
  by (induct rule: finite_ne_induct)
    (simp_all add: fold1_insert min_le_iff_disj)
qed

lemma fold1_strict_below_iff:
  assumes "finite A" and "A \<noteq> {}"
  shows "fold1 min A < x \<longleftrightarrow> (\<exists>a\<in>A. a < x)"
proof -
  interpret ab_semigroup_idem_mult min
    by (rule ab_semigroup_idem_mult_min)
  from assms show ?thesis
  by (induct rule: finite_ne_induct)
    (simp_all add: fold1_insert min_less_iff_disj)
qed

lemma fold1_antimono:
  assumes "A \<noteq> {}" and "A \<subseteq> B" and "finite B"
  shows "fold1 min B \<le> fold1 min A"
proof cases
  assume "A = B" thus ?thesis by simp
next
  interpret ab_semigroup_idem_mult min
    by (rule ab_semigroup_idem_mult_min)
  assume "A \<noteq> B"
  have B: "B = A \<union> (B-A)" using `A \<subseteq> B` by blast
  have "fold1 min B = fold1 min (A \<union> (B-A))" by(subst B)(rule refl)
  also have "\<dots> = min (fold1 min A) (fold1 min (B-A))"
  proof -
    have "finite A" by(rule finite_subset[OF `A \<subseteq> B` `finite B`])
    moreover have "finite(B-A)" by(rule finite_Diff[OF `finite B`]) (* by(blast intro:finite_Diff prems) fails *)
    moreover have "(B-A) \<noteq> {}" using prems by blast
    moreover have "A Int (B-A) = {}" using prems by blast
    ultimately show ?thesis using `A \<noteq> {}` by (rule_tac fold1_Un)
  qed
  also have "\<dots> \<le> fold1 min A" by (simp add: min_le_iff_disj)
  finally show ?thesis .
qed

definition
  Min :: "'a set \<Rightarrow> 'a"
where
  "Min = fold1 min"

definition
  Max :: "'a set \<Rightarrow> 'a"
where
  "Max = fold1 max"

lemmas Min_singleton [simp] = fold1_singleton_def [OF Min_def]
lemmas Max_singleton [simp] = fold1_singleton_def [OF Max_def]

lemma Min_insert [simp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "Min (insert x A) = min x (Min A)"
proof -
  interpret ab_semigroup_idem_mult min
    by (rule ab_semigroup_idem_mult_min)
  from assms show ?thesis by (rule fold1_insert_idem_def [OF Min_def])
qed

lemma Max_insert [simp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "Max (insert x A) = max x (Max A)"
proof -
  interpret ab_semigroup_idem_mult max
    by (rule ab_semigroup_idem_mult_max)
  from assms show ?thesis by (rule fold1_insert_idem_def [OF Max_def])
qed

lemma Min_in [simp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "Min A \<in> A"
proof -
  interpret ab_semigroup_idem_mult min
    by (rule ab_semigroup_idem_mult_min)
  from assms fold1_in show ?thesis by (fastsimp simp: Min_def min_def)
qed

lemma Max_in [simp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "Max A \<in> A"
proof -
  interpret ab_semigroup_idem_mult max
    by (rule ab_semigroup_idem_mult_max)
  from assms fold1_in [of A] show ?thesis by (fastsimp simp: Max_def max_def)
qed

lemma Min_Un:
  assumes "finite A" and "A \<noteq> {}" and "finite B" and "B \<noteq> {}"
  shows "Min (A \<union> B) = min (Min A) (Min B)"
proof -
  interpret ab_semigroup_idem_mult min
    by (rule ab_semigroup_idem_mult_min)
  from assms show ?thesis
    by (simp add: Min_def fold1_Un2)
qed

lemma Max_Un:
  assumes "finite A" and "A \<noteq> {}" and "finite B" and "B \<noteq> {}"
  shows "Max (A \<union> B) = max (Max A) (Max B)"
proof -
  interpret ab_semigroup_idem_mult max
    by (rule ab_semigroup_idem_mult_max)
  from assms show ?thesis
    by (simp add: Max_def fold1_Un2)
qed

lemma hom_Min_commute:
  assumes "\<And>x y. h (min x y) = min (h x) (h y)"
    and "finite N" and "N \<noteq> {}"
  shows "h (Min N) = Min (h ` N)"
proof -
  interpret ab_semigroup_idem_mult min
    by (rule ab_semigroup_idem_mult_min)
  from assms show ?thesis
    by (simp add: Min_def hom_fold1_commute)
qed

lemma hom_Max_commute:
  assumes "\<And>x y. h (max x y) = max (h x) (h y)"
    and "finite N" and "N \<noteq> {}"
  shows "h (Max N) = Max (h ` N)"
proof -
  interpret ab_semigroup_idem_mult max
    by (rule ab_semigroup_idem_mult_max)
  from assms show ?thesis
    by (simp add: Max_def hom_fold1_commute [of h])
qed

lemma Min_le [simp]:
  assumes "finite A" and "x \<in> A"
  shows "Min A \<le> x"
proof -
  interpret lower_semilattice "op \<le>" "op <" min
    by (rule min_lattice)
  from assms show ?thesis by (simp add: Min_def fold1_belowI)
qed

lemma Max_ge [simp]:
  assumes "finite A" and "x \<in> A"
  shows "x \<le> Max A"
proof -
  interpret lower_semilattice "op \<ge>" "op >" max
    by (rule max_lattice)
  from assms show ?thesis by (simp add: Max_def fold1_belowI)
qed

lemma Min_ge_iff [simp, noatp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "x \<le> Min A \<longleftrightarrow> (\<forall>a\<in>A. x \<le> a)"
proof -
  interpret lower_semilattice "op \<le>" "op <" min
    by (rule min_lattice)
  from assms show ?thesis by (simp add: Min_def below_fold1_iff)
qed

lemma Max_le_iff [simp, noatp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "Max A \<le> x \<longleftrightarrow> (\<forall>a\<in>A. a \<le> x)"
proof -
  interpret lower_semilattice "op \<ge>" "op >" max
    by (rule max_lattice)
  from assms show ?thesis by (simp add: Max_def below_fold1_iff)
qed

lemma Min_gr_iff [simp, noatp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "x < Min A \<longleftrightarrow> (\<forall>a\<in>A. x < a)"
proof -
  interpret lower_semilattice "op \<le>" "op <" min
    by (rule min_lattice)
  from assms show ?thesis by (simp add: Min_def strict_below_fold1_iff)
qed

lemma Max_less_iff [simp, noatp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "Max A < x \<longleftrightarrow> (\<forall>a\<in>A. a < x)"
proof -
  note Max = Max_def
  interpret linorder "op \<ge>" "op >"
    by (rule dual_linorder)
  from assms show ?thesis
    by (simp add: Max strict_below_fold1_iff [folded dual_max])
qed

lemma Min_le_iff [noatp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "Min A \<le> x \<longleftrightarrow> (\<exists>a\<in>A. a \<le> x)"
proof -
  interpret lower_semilattice "op \<le>" "op <" min
    by (rule min_lattice)
  from assms show ?thesis
    by (simp add: Min_def fold1_below_iff)
qed

lemma Max_ge_iff [noatp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "x \<le> Max A \<longleftrightarrow> (\<exists>a\<in>A. x \<le> a)"
proof -
  note Max = Max_def
  interpret linorder "op \<ge>" "op >"
    by (rule dual_linorder)
  from assms show ?thesis
    by (simp add: Max fold1_below_iff [folded dual_max])
qed

lemma Min_less_iff [noatp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "Min A < x \<longleftrightarrow> (\<exists>a\<in>A. a < x)"
proof -
  interpret lower_semilattice "op \<le>" "op <" min
    by (rule min_lattice)
  from assms show ?thesis
    by (simp add: Min_def fold1_strict_below_iff)
qed

lemma Max_gr_iff [noatp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "x < Max A \<longleftrightarrow> (\<exists>a\<in>A. x < a)"
proof -
  note Max = Max_def
  interpret linorder "op \<ge>" "op >"
    by (rule dual_linorder)
  from assms show ?thesis
    by (simp add: Max fold1_strict_below_iff [folded dual_max])
qed

lemma Min_antimono:
  assumes "M \<subseteq> N" and "M \<noteq> {}" and "finite N"
  shows "Min N \<le> Min M"
proof -
  interpret distrib_lattice "op \<le>" "op <" min max
    by (rule distrib_lattice_min_max)
  from assms show ?thesis by (simp add: Min_def fold1_antimono)
qed

lemma Max_mono:
  assumes "M \<subseteq> N" and "M \<noteq> {}" and "finite N"
  shows "Max M \<le> Max N"
proof -
  note Max = Max_def
  interpret linorder "op \<ge>" "op >"
    by (rule dual_linorder)
  from assms show ?thesis
    by (simp add: Max fold1_antimono [folded dual_max])
qed

lemma finite_linorder_induct[consumes 1, case_names empty insert]:
 "finite A \<Longrightarrow> P {} \<Longrightarrow>
  (!!A b. finite A \<Longrightarrow> ALL a:A. a < b \<Longrightarrow> P A \<Longrightarrow> P(insert b A))
  \<Longrightarrow> P A"
proof (induct A rule: measure_induct_rule[where f=card])
  fix A :: "'a set"
  assume IH: "!! B. card B < card A \<Longrightarrow> finite B \<Longrightarrow> P {} \<Longrightarrow>
                 (!!A b. finite A \<Longrightarrow> (\<forall>a\<in>A. a<b) \<Longrightarrow> P A \<Longrightarrow> P (insert b A))
                  \<Longrightarrow> P B"
  and "finite A" and "P {}"
  and step: "!!A b. \<lbrakk>finite A; \<forall>a\<in>A. a < b; P A\<rbrakk> \<Longrightarrow> P (insert b A)"
  show "P A"
  proof (cases "A = {}")
    assume "A = {}" thus "P A" using `P {}` by simp
  next
    let ?B = "A - {Max A}" let ?A = "insert (Max A) ?B"
    assume "A \<noteq> {}"
    with `finite A` have "Max A : A" by auto
    hence A: "?A = A" using insert_Diff_single insert_absorb by auto
    note card_Diff1_less[OF `finite A` `Max A : A`]
    moreover have "finite ?B" using `finite A` by simp
    ultimately have "P ?B" using `P {}` step IH by blast
    moreover have "\<forall>a\<in>?B. a < Max A"
      using Max_ge [OF `finite A`] by fastsimp
    ultimately show "P A"
      using A insert_Diff_single step[OF `finite ?B`] by fastsimp
  qed
qed

end

context ordered_ab_semigroup_add
begin

lemma add_Min_commute:
  fixes k
  assumes "finite N" and "N \<noteq> {}"
  shows "k + Min N = Min {k + m | m. m \<in> N}"
proof -
  have "\<And>x y. k + min x y = min (k + x) (k + y)"
    by (simp add: min_def not_le)
      (blast intro: antisym less_imp_le add_left_mono)
  with assms show ?thesis
    using hom_Min_commute [of "plus k" N]
    by simp (blast intro: arg_cong [where f = Min])
qed

lemma add_Max_commute:
  fixes k
  assumes "finite N" and "N \<noteq> {}"
  shows "k + Max N = Max {k + m | m. m \<in> N}"
proof -
  have "\<And>x y. k + max x y = max (k + x) (k + y)"
    by (simp add: max_def not_le)
      (blast intro: antisym less_imp_le add_left_mono)
  with assms show ?thesis
    using hom_Max_commute [of "plus k" N]
    by simp (blast intro: arg_cong [where f = Max])
qed

end

end
