(*  Title:      HOLCF/Universal.thy
    Author:     Brian Huffman
*)

theory Universal
imports CompactBasis NatIso
begin

subsection {* Basis datatype *}

types ubasis = nat

definition
  node :: "nat \<Rightarrow> ubasis \<Rightarrow> ubasis set \<Rightarrow> ubasis"
where
  "node i a S = Suc (prod2nat (i, prod2nat (a, set2nat S)))"

lemma node_not_0 [simp]: "node i a S \<noteq> 0"
unfolding node_def by simp

lemma node_gt_0 [simp]: "0 < node i a S"
unfolding node_def by simp

lemma node_inject [simp]:
  "\<lbrakk>finite S; finite T\<rbrakk>
    \<Longrightarrow> node i a S = node j b T \<longleftrightarrow> i = j \<and> a = b \<and> S = T"
unfolding node_def by simp

lemma node_gt0: "i < node i a S"
unfolding node_def less_Suc_eq_le
by (rule le_prod2nat_1)

lemma node_gt1: "a < node i a S"
unfolding node_def less_Suc_eq_le
by (rule order_trans [OF le_prod2nat_1 le_prod2nat_2])

lemma nat_less_power2: "n < 2^n"
by (induct n) simp_all

lemma node_gt2: "\<lbrakk>finite S; b \<in> S\<rbrakk> \<Longrightarrow> b < node i a S"
unfolding node_def less_Suc_eq_le set2nat_def
apply (rule order_trans [OF _ le_prod2nat_2])
apply (rule order_trans [OF _ le_prod2nat_2])
apply (rule order_trans [where y="setsum (op ^ 2) {b}"])
apply (simp add: nat_less_power2 [THEN order_less_imp_le])
apply (erule setsum_mono2, simp, simp)
done

lemma eq_prod2nat_pairI:
  "\<lbrakk>fst (nat2prod x) = a; snd (nat2prod x) = b\<rbrakk> \<Longrightarrow> x = prod2nat (a, b)"
by (erule subst, erule subst, simp)

lemma node_cases:
  assumes 1: "x = 0 \<Longrightarrow> P"
  assumes 2: "\<And>i a S. \<lbrakk>finite S; x = node i a S\<rbrakk> \<Longrightarrow> P"
  shows "P"
 apply (cases x)
  apply (erule 1)
 apply (rule 2)
  apply (rule finite_nat2set)
 apply (simp add: node_def)
 apply (rule eq_prod2nat_pairI [OF refl])
 apply (rule eq_prod2nat_pairI [OF refl refl])
done

lemma node_induct:
  assumes 1: "P 0"
  assumes 2: "\<And>i a S. \<lbrakk>P a; finite S; \<forall>b\<in>S. P b\<rbrakk> \<Longrightarrow> P (node i a S)"
  shows "P x"
 apply (induct x rule: nat_less_induct)
 apply (case_tac n rule: node_cases)
  apply (simp add: 1)
 apply (simp add: 2 node_gt1 node_gt2)
done

subsection {* Basis ordering *}

inductive
  ubasis_le :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  ubasis_le_refl: "ubasis_le a a"
| ubasis_le_trans:
    "\<lbrakk>ubasis_le a b; ubasis_le b c\<rbrakk> \<Longrightarrow> ubasis_le a c"
| ubasis_le_lower:
    "finite S \<Longrightarrow> ubasis_le a (node i a S)"
| ubasis_le_upper:
    "\<lbrakk>finite S; b \<in> S; ubasis_le a b\<rbrakk> \<Longrightarrow> ubasis_le (node i a S) b"

lemma ubasis_le_minimal: "ubasis_le 0 x"
apply (induct x rule: node_induct)
apply (rule ubasis_le_refl)
apply (erule ubasis_le_trans)
apply (erule ubasis_le_lower)
done

subsubsection {* Generic take function *}

function
  ubasis_until :: "(ubasis \<Rightarrow> bool) \<Rightarrow> ubasis \<Rightarrow> ubasis"
where
  "ubasis_until P 0 = 0"
| "finite S \<Longrightarrow> ubasis_until P (node i a S) =
    (if P (node i a S) then node i a S else ubasis_until P a)"
    apply clarify
    apply (rule_tac x=b in node_cases)
     apply simp
    apply simp
    apply fast
   apply simp
  apply simp
 apply simp
done

termination ubasis_until
apply (relation "measure snd")
apply (rule wf_measure)
apply (simp add: node_gt1)
done

lemma ubasis_until: "P 0 \<Longrightarrow> P (ubasis_until P x)"
by (induct x rule: node_induct) simp_all

lemma ubasis_until': "0 < ubasis_until P x \<Longrightarrow> P (ubasis_until P x)"
by (induct x rule: node_induct) auto

lemma ubasis_until_same: "P x \<Longrightarrow> ubasis_until P x = x"
by (induct x rule: node_induct) simp_all

lemma ubasis_until_idem:
  "P 0 \<Longrightarrow> ubasis_until P (ubasis_until P x) = ubasis_until P x"
by (rule ubasis_until_same [OF ubasis_until])

lemma ubasis_until_0:
  "\<forall>x. x \<noteq> 0 \<longrightarrow> \<not> P x \<Longrightarrow> ubasis_until P x = 0"
by (induct x rule: node_induct) simp_all

lemma ubasis_until_less: "ubasis_le (ubasis_until P x) x"
apply (induct x rule: node_induct)
apply (simp add: ubasis_le_refl)
apply (simp add: ubasis_le_refl)
apply (rule impI)
apply (erule ubasis_le_trans)
apply (erule ubasis_le_lower)
done

lemma ubasis_until_chain:
  assumes PQ: "\<And>x. P x \<Longrightarrow> Q x"
  shows "ubasis_le (ubasis_until P x) (ubasis_until Q x)"
apply (induct x rule: node_induct)
apply (simp add: ubasis_le_refl)
apply (simp add: ubasis_le_refl)
apply (simp add: PQ)
apply clarify
apply (rule ubasis_le_trans)
apply (rule ubasis_until_less)
apply (erule ubasis_le_lower)
done

lemma ubasis_until_mono:
  assumes "\<And>i a S b. \<lbrakk>finite S; P (node i a S); b \<in> S; ubasis_le a b\<rbrakk> \<Longrightarrow> P b"
  shows "ubasis_le a b \<Longrightarrow> ubasis_le (ubasis_until P a) (ubasis_until P b)"
proof (induct set: ubasis_le)
  case (ubasis_le_refl a) show ?case by (rule ubasis_le.ubasis_le_refl)
next
  case (ubasis_le_trans a b c) thus ?case by - (rule ubasis_le.ubasis_le_trans)
next
  case (ubasis_le_lower S a i) thus ?case
    apply (clarsimp simp add: ubasis_le_refl)
    apply (rule ubasis_le_trans [OF ubasis_until_less])
    apply (erule ubasis_le.ubasis_le_lower)
    done
next
  case (ubasis_le_upper S b a i) thus ?case
    apply clarsimp
    apply (subst ubasis_until_same)
     apply (erule (3) prems)
    apply (erule (2) ubasis_le.ubasis_le_upper)
    done
qed

lemma finite_range_ubasis_until:
  "finite {x. P x} \<Longrightarrow> finite (range (ubasis_until P))"
apply (rule finite_subset [where B="insert 0 {x. P x}"])
apply (clarsimp simp add: ubasis_until')
apply simp
done

subsubsection {* Take function for @{typ ubasis} *}

definition
  ubasis_take :: "nat \<Rightarrow> ubasis \<Rightarrow> ubasis"
where
  "ubasis_take n = ubasis_until (\<lambda>x. x \<le> n)"

lemma ubasis_take_le: "ubasis_take n x \<le> n"
unfolding ubasis_take_def by (rule ubasis_until, rule le0)

lemma ubasis_take_same: "x \<le> n \<Longrightarrow> ubasis_take n x = x"
unfolding ubasis_take_def by (rule ubasis_until_same)

lemma ubasis_take_idem: "ubasis_take n (ubasis_take n x) = ubasis_take n x"
by (rule ubasis_take_same [OF ubasis_take_le])

lemma ubasis_take_0 [simp]: "ubasis_take 0 x = 0"
unfolding ubasis_take_def by (simp add: ubasis_until_0)

lemma ubasis_take_less: "ubasis_le (ubasis_take n x) x"
unfolding ubasis_take_def by (rule ubasis_until_less)

lemma ubasis_take_chain: "ubasis_le (ubasis_take n x) (ubasis_take (Suc n) x)"
unfolding ubasis_take_def by (rule ubasis_until_chain) simp

lemma ubasis_take_mono:
  assumes "ubasis_le x y"
  shows "ubasis_le (ubasis_take n x) (ubasis_take n y)"
unfolding ubasis_take_def
 apply (rule ubasis_until_mono [OF _ prems])
 apply (frule (2) order_less_le_trans [OF node_gt2])
 apply (erule order_less_imp_le)
done

lemma finite_range_ubasis_take: "finite (range (ubasis_take n))"
apply (rule finite_subset [where B="{..n}"])
apply (simp add: subset_eq ubasis_take_le)
apply simp
done

lemma ubasis_take_covers: "\<exists>n. ubasis_take n x = x"
apply (rule exI [where x=x])
apply (simp add: ubasis_take_same)
done

interpretation udom: preorder ubasis_le
apply default
apply (rule ubasis_le_refl)
apply (erule (1) ubasis_le_trans)
done

interpretation udom: basis_take ubasis_le ubasis_take
apply default
apply (rule ubasis_take_less)
apply (rule ubasis_take_idem)
apply (erule ubasis_take_mono)
apply (rule ubasis_take_chain)
apply (rule finite_range_ubasis_take)
apply (rule ubasis_take_covers)
done

subsection {* Defining the universal domain by ideal completion *}

typedef (open) udom = "{S. udom.ideal S}"
by (fast intro: udom.ideal_principal)

instantiation udom :: below
begin

definition
  "x \<sqsubseteq> y \<longleftrightarrow> Rep_udom x \<subseteq> Rep_udom y"

instance ..
end

instance udom :: po
by (rule udom.typedef_ideal_po
    [OF type_definition_udom below_udom_def])

instance udom :: cpo
by (rule udom.typedef_ideal_cpo
    [OF type_definition_udom below_udom_def])

lemma Rep_udom_lub:
  "chain Y \<Longrightarrow> Rep_udom (\<Squnion>i. Y i) = (\<Union>i. Rep_udom (Y i))"
by (rule udom.typedef_ideal_rep_contlub
    [OF type_definition_udom below_udom_def])

lemma ideal_Rep_udom: "udom.ideal (Rep_udom xs)"
by (rule Rep_udom [unfolded mem_Collect_eq])

definition
  udom_principal :: "nat \<Rightarrow> udom" where
  "udom_principal t = Abs_udom {u. ubasis_le u t}"

lemma Rep_udom_principal:
  "Rep_udom (udom_principal t) = {u. ubasis_le u t}"
unfolding udom_principal_def
by (simp add: Abs_udom_inverse udom.ideal_principal)

interpretation udom:
  ideal_completion ubasis_le ubasis_take udom_principal Rep_udom
apply unfold_locales
apply (rule ideal_Rep_udom)
apply (erule Rep_udom_lub)
apply (rule Rep_udom_principal)
apply (simp only: below_udom_def)
done

text {* Universal domain is pointed *}

lemma udom_minimal: "udom_principal 0 \<sqsubseteq> x"
apply (induct x rule: udom.principal_induct)
apply (simp, simp add: ubasis_le_minimal)
done

instance udom :: pcpo
by intro_classes (fast intro: udom_minimal)

lemma inst_udom_pcpo: "\<bottom> = udom_principal 0"
by (rule udom_minimal [THEN UU_I, symmetric])

text {* Universal domain is bifinite *}

instantiation udom :: bifinite
begin

definition
  approx_udom_def: "approx = udom.completion_approx"

instance
apply (intro_classes, unfold approx_udom_def)
apply (rule udom.chain_completion_approx)
apply (rule udom.lub_completion_approx)
apply (rule udom.completion_approx_idem)
apply (rule udom.finite_fixes_completion_approx)
done

end

lemma approx_udom_principal [simp]:
  "approx n\<cdot>(udom_principal x) = udom_principal (ubasis_take n x)"
unfolding approx_udom_def
by (rule udom.completion_approx_principal)

lemma approx_eq_udom_principal:
  "\<exists>a\<in>Rep_udom x. approx n\<cdot>x = udom_principal (ubasis_take n a)"
unfolding approx_udom_def
by (rule udom.completion_approx_eq_principal)


subsection {* Universality of @{typ udom} *}

defaultsort bifinite

subsubsection {* Choosing a maximal element from a finite set *}

lemma finite_has_maximal:
  fixes A :: "'a::po set"
  shows "\<lbrakk>finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>x\<in>A. \<forall>y\<in>A. x \<sqsubseteq> y \<longrightarrow> x = y"
proof (induct rule: finite_ne_induct)
  case (singleton x)
    show ?case by simp
next
  case (insert a A)
  from `\<exists>x\<in>A. \<forall>y\<in>A. x \<sqsubseteq> y \<longrightarrow> x = y`
  obtain x where x: "x \<in> A"
           and x_eq: "\<And>y. \<lbrakk>y \<in> A; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> x = y" by fast
  show ?case
  proof (intro bexI ballI impI)
    fix y
    assume "y \<in> insert a A" and "(if x \<sqsubseteq> a then a else x) \<sqsubseteq> y"
    thus "(if x \<sqsubseteq> a then a else x) = y"
      apply auto
      apply (frule (1) below_trans)
      apply (frule (1) x_eq)
      apply (rule below_antisym, assumption)
      apply simp
      apply (erule (1) x_eq)
      done
  next
    show "(if x \<sqsubseteq> a then a else x) \<in> insert a A"
      by (simp add: x)
  qed
qed

definition
  choose :: "'a compact_basis set \<Rightarrow> 'a compact_basis"
where
  "choose A = (SOME x. x \<in> {x\<in>A. \<forall>y\<in>A. x \<sqsubseteq> y \<longrightarrow> x = y})"

lemma choose_lemma:
  "\<lbrakk>finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> choose A \<in> {x\<in>A. \<forall>y\<in>A. x \<sqsubseteq> y \<longrightarrow> x = y}"
unfolding choose_def
apply (rule someI_ex)
apply (frule (1) finite_has_maximal, fast)
done

lemma maximal_choose:
  "\<lbrakk>finite A; y \<in> A; choose A \<sqsubseteq> y\<rbrakk> \<Longrightarrow> choose A = y"
apply (cases "A = {}", simp)
apply (frule (1) choose_lemma, simp)
done

lemma choose_in: "\<lbrakk>finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> choose A \<in> A"
by (frule (1) choose_lemma, simp)

function
  choose_pos :: "'a compact_basis set \<Rightarrow> 'a compact_basis \<Rightarrow> nat"
where
  "choose_pos A x =
    (if finite A \<and> x \<in> A \<and> x \<noteq> choose A
      then Suc (choose_pos (A - {choose A}) x) else 0)"
by auto

termination choose_pos
apply (relation "measure (card \<circ> fst)", simp)
apply clarsimp
apply (rule card_Diff1_less)
apply assumption
apply (erule choose_in)
apply clarsimp
done

declare choose_pos.simps [simp del]

lemma choose_pos_choose: "finite A \<Longrightarrow> choose_pos A (choose A) = 0"
by (simp add: choose_pos.simps)

lemma inj_on_choose_pos [OF refl]:
  "\<lbrakk>card A = n; finite A\<rbrakk> \<Longrightarrow> inj_on (choose_pos A) A"
 apply (induct n arbitrary: A)
  apply simp
 apply (case_tac "A = {}", simp)
 apply (frule (1) choose_in)
 apply (rule inj_onI)
 apply (drule_tac x="A - {choose A}" in meta_spec, simp)
 apply (simp add: choose_pos.simps)
 apply (simp split: split_if_asm)
 apply (erule (1) inj_onD, simp, simp)
done

lemma choose_pos_bounded [OF refl]:
  "\<lbrakk>card A = n; finite A; x \<in> A\<rbrakk> \<Longrightarrow> choose_pos A x < n"
apply (induct n arbitrary: A)
apply simp
 apply (case_tac "A = {}", simp)
 apply (frule (1) choose_in)
apply (subst choose_pos.simps)
apply simp
done

lemma choose_pos_lessD:
  "\<lbrakk>choose_pos A x < choose_pos A y; finite A; x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> \<not> x \<sqsubseteq> y"
 apply (induct A x arbitrary: y rule: choose_pos.induct)
 apply simp
 apply (case_tac "x = choose A")
  apply simp
  apply (rule notI)
  apply (frule (2) maximal_choose)
  apply simp
 apply (case_tac "y = choose A")
  apply (simp add: choose_pos_choose)
 apply (drule_tac x=y in meta_spec)
 apply simp
 apply (erule meta_mp)
 apply (simp add: choose_pos.simps)
done

subsubsection {* Rank of basis elements *}

primrec
  cb_take :: "nat \<Rightarrow> 'a compact_basis \<Rightarrow> 'a compact_basis"
where
  "cb_take 0 = (\<lambda>x. compact_bot)"
| "cb_take (Suc n) = compact_take n"

lemma cb_take_covers: "\<exists>n. cb_take n x = x"
apply (rule exE [OF compact_basis.take_covers [where a=x]])
apply (rename_tac n, rule_tac x="Suc n" in exI, simp)
done

lemma cb_take_less: "cb_take n x \<sqsubseteq> x"
by (cases n, simp, simp add: compact_basis.take_less)

lemma cb_take_idem: "cb_take n (cb_take n x) = cb_take n x"
by (cases n, simp, simp add: compact_basis.take_take)

lemma cb_take_mono: "x \<sqsubseteq> y \<Longrightarrow> cb_take n x \<sqsubseteq> cb_take n y"
by (cases n, simp, simp add: compact_basis.take_mono)

lemma cb_take_chain_le: "m \<le> n \<Longrightarrow> cb_take m x \<sqsubseteq> cb_take n x"
apply (cases m, simp)
apply (cases n, simp)
apply (simp add: compact_basis.take_chain_le)
done

lemma range_const: "range (\<lambda>x. c) = {c}"
by auto

lemma finite_range_cb_take: "finite (range (cb_take n))"
apply (cases n)
apply (simp add: range_const)
apply (simp add: compact_basis.finite_range_take)
done

definition
  rank :: "'a compact_basis \<Rightarrow> nat"
where
  "rank x = (LEAST n. cb_take n x = x)"

lemma compact_approx_rank: "cb_take (rank x) x = x"
unfolding rank_def
apply (rule LeastI_ex)
apply (rule cb_take_covers)
done

lemma rank_leD: "rank x \<le> n \<Longrightarrow> cb_take n x = x"
apply (rule below_antisym [OF cb_take_less])
apply (subst compact_approx_rank [symmetric])
apply (erule cb_take_chain_le)
done

lemma rank_leI: "cb_take n x = x \<Longrightarrow> rank x \<le> n"
unfolding rank_def by (rule Least_le)

lemma rank_le_iff: "rank x \<le> n \<longleftrightarrow> cb_take n x = x"
by (rule iffI [OF rank_leD rank_leI])

lemma rank_compact_bot [simp]: "rank compact_bot = 0"
using rank_leI [of 0 compact_bot] by simp

lemma rank_eq_0_iff [simp]: "rank x = 0 \<longleftrightarrow> x = compact_bot"
using rank_le_iff [of x 0] by auto

definition
  rank_le :: "'a compact_basis \<Rightarrow> 'a compact_basis set"
where
  "rank_le x = {y. rank y \<le> rank x}"

definition
  rank_lt :: "'a compact_basis \<Rightarrow> 'a compact_basis set"
where
  "rank_lt x = {y. rank y < rank x}"

definition
  rank_eq :: "'a compact_basis \<Rightarrow> 'a compact_basis set"
where
  "rank_eq x = {y. rank y = rank x}"

lemma rank_eq_cong: "rank x = rank y \<Longrightarrow> rank_eq x = rank_eq y"
unfolding rank_eq_def by simp

lemma rank_lt_cong: "rank x = rank y \<Longrightarrow> rank_lt x = rank_lt y"
unfolding rank_lt_def by simp

lemma rank_eq_subset: "rank_eq x \<subseteq> rank_le x"
unfolding rank_eq_def rank_le_def by auto

lemma rank_lt_subset: "rank_lt x \<subseteq> rank_le x"
unfolding rank_lt_def rank_le_def by auto

lemma finite_rank_le: "finite (rank_le x)"
unfolding rank_le_def
apply (rule finite_subset [where B="range (cb_take (rank x))"])
apply clarify
apply (rule range_eqI)
apply (erule rank_leD [symmetric])
apply (rule finite_range_cb_take)
done

lemma finite_rank_eq: "finite (rank_eq x)"
by (rule finite_subset [OF rank_eq_subset finite_rank_le])

lemma finite_rank_lt: "finite (rank_lt x)"
by (rule finite_subset [OF rank_lt_subset finite_rank_le])

lemma rank_lt_Int_rank_eq: "rank_lt x \<inter> rank_eq x = {}"
unfolding rank_lt_def rank_eq_def rank_le_def by auto

lemma rank_lt_Un_rank_eq: "rank_lt x \<union> rank_eq x = rank_le x"
unfolding rank_lt_def rank_eq_def rank_le_def by auto

subsubsection {* Sequencing basis elements *}

definition
  place :: "'a compact_basis \<Rightarrow> nat"
where
  "place x = card (rank_lt x) + choose_pos (rank_eq x) x"

lemma place_bounded: "place x < card (rank_le x)"
unfolding place_def
 apply (rule ord_less_eq_trans)
  apply (rule add_strict_left_mono)
  apply (rule choose_pos_bounded)
   apply (rule finite_rank_eq)
  apply (simp add: rank_eq_def)
 apply (subst card_Un_disjoint [symmetric])
    apply (rule finite_rank_lt)
   apply (rule finite_rank_eq)
  apply (rule rank_lt_Int_rank_eq)
 apply (simp add: rank_lt_Un_rank_eq)
done

lemma place_ge: "card (rank_lt x) \<le> place x"
unfolding place_def by simp

lemma place_rank_mono:
  fixes x y :: "'a compact_basis"
  shows "rank x < rank y \<Longrightarrow> place x < place y"
apply (rule less_le_trans [OF place_bounded])
apply (rule order_trans [OF _ place_ge])
apply (rule card_mono)
apply (rule finite_rank_lt)
apply (simp add: rank_le_def rank_lt_def subset_eq)
done

lemma place_eqD: "place x = place y \<Longrightarrow> x = y"
 apply (rule linorder_cases [where x="rank x" and y="rank y"])
   apply (drule place_rank_mono, simp)
  apply (simp add: place_def)
  apply (rule inj_on_choose_pos [where A="rank_eq x", THEN inj_onD])
     apply (rule finite_rank_eq)
    apply (simp cong: rank_lt_cong rank_eq_cong)
   apply (simp add: rank_eq_def)
  apply (simp add: rank_eq_def)
 apply (drule place_rank_mono, simp)
done

lemma inj_place: "inj place"
by (rule inj_onI, erule place_eqD)

subsubsection {* Embedding and projection on basis elements *}

definition
  sub :: "'a compact_basis \<Rightarrow> 'a compact_basis"
where
  "sub x = (case rank x of 0 \<Rightarrow> compact_bot | Suc k \<Rightarrow> cb_take k x)"

lemma rank_sub_less: "x \<noteq> compact_bot \<Longrightarrow> rank (sub x) < rank x"
unfolding sub_def
apply (cases "rank x", simp)
apply (simp add: less_Suc_eq_le)
apply (rule rank_leI)
apply (rule cb_take_idem)
done

lemma place_sub_less: "x \<noteq> compact_bot \<Longrightarrow> place (sub x) < place x"
apply (rule place_rank_mono)
apply (erule rank_sub_less)
done

lemma sub_below: "sub x \<sqsubseteq> x"
unfolding sub_def by (cases "rank x", simp_all add: cb_take_less)

lemma rank_less_imp_below_sub: "\<lbrakk>x \<sqsubseteq> y; rank x < rank y\<rbrakk> \<Longrightarrow> x \<sqsubseteq> sub y"
unfolding sub_def
apply (cases "rank y", simp)
apply (simp add: less_Suc_eq_le)
apply (subgoal_tac "cb_take nat x \<sqsubseteq> cb_take nat y")
apply (simp add: rank_leD)
apply (erule cb_take_mono)
done

function
  basis_emb :: "'a compact_basis \<Rightarrow> ubasis"
where
  "basis_emb x = (if x = compact_bot then 0 else
    node (place x) (basis_emb (sub x))
      (basis_emb ` {y. place y < place x \<and> x \<sqsubseteq> y}))"
by auto

termination basis_emb
apply (relation "measure place", simp)
apply (simp add: place_sub_less)
apply simp
done

declare basis_emb.simps [simp del]

lemma basis_emb_compact_bot [simp]: "basis_emb compact_bot = 0"
by (simp add: basis_emb.simps)

lemma fin1: "finite {y. place y < place x \<and> x \<sqsubseteq> y}"
apply (subst Collect_conj_eq)
apply (rule finite_Int)
apply (rule disjI1)
apply (subgoal_tac "finite (place -` {n. n < place x})", simp)
apply (rule finite_vimageI [OF _ inj_place])
apply (simp add: lessThan_def [symmetric])
done

lemma fin2: "finite (basis_emb ` {y. place y < place x \<and> x \<sqsubseteq> y})"
by (rule finite_imageI [OF fin1])

lemma rank_place_mono:
  "\<lbrakk>place x < place y; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> rank x < rank y"
apply (rule linorder_cases, assumption)
apply (simp add: place_def cong: rank_lt_cong rank_eq_cong)
apply (drule choose_pos_lessD)
apply (rule finite_rank_eq)
apply (simp add: rank_eq_def)
apply (simp add: rank_eq_def)
apply simp
apply (drule place_rank_mono, simp)
done

lemma basis_emb_mono:
  "x \<sqsubseteq> y \<Longrightarrow> ubasis_le (basis_emb x) (basis_emb y)"
proof (induct n \<equiv> "max (place x) (place y)" arbitrary: x y rule: less_induct)
  case (less n)
  hence IH:
    "\<And>(a::'a compact_basis) b.
     \<lbrakk>max (place a) (place b) < max (place x) (place y); a \<sqsubseteq> b\<rbrakk>
        \<Longrightarrow> ubasis_le (basis_emb a) (basis_emb b)"
    by simp
  show ?case proof (rule linorder_cases)
    assume "place x < place y"
    then have "rank x < rank y"
      using `x \<sqsubseteq> y` by (rule rank_place_mono)
    with `place x < place y` show ?case
      apply (case_tac "y = compact_bot", simp)
      apply (simp add: basis_emb.simps [of y])
      apply (rule ubasis_le_trans [OF _ ubasis_le_lower [OF fin2]])
      apply (rule IH)
       apply (simp add: less_max_iff_disj)
       apply (erule place_sub_less)
      apply (erule rank_less_imp_below_sub [OF `x \<sqsubseteq> y`])
      done
  next
    assume "place x = place y"
    hence "x = y" by (rule place_eqD)
    thus ?case by (simp add: ubasis_le_refl)
  next
    assume "place x > place y"
    with `x \<sqsubseteq> y` show ?case
      apply (case_tac "x = compact_bot", simp add: ubasis_le_minimal)
      apply (simp add: basis_emb.simps [of x])
      apply (rule ubasis_le_upper [OF fin2], simp)
      apply (rule IH)
       apply (simp add: less_max_iff_disj)
       apply (erule place_sub_less)
      apply (erule rev_below_trans)
      apply (rule sub_below)
      done
  qed
qed

lemma inj_basis_emb: "inj basis_emb"
 apply (rule inj_onI)
 apply (case_tac "x = compact_bot")
  apply (case_tac [!] "y = compact_bot")
    apply simp
   apply (simp add: basis_emb.simps)
  apply (simp add: basis_emb.simps)
 apply (simp add: basis_emb.simps)
 apply (simp add: fin2 inj_eq [OF inj_place])
done

definition
  basis_prj :: "ubasis \<Rightarrow> 'a compact_basis"
where
  "basis_prj x = inv basis_emb
    (ubasis_until (\<lambda>x. x \<in> range (basis_emb :: 'a compact_basis \<Rightarrow> ubasis)) x)"

lemma basis_prj_basis_emb: "\<And>x. basis_prj (basis_emb x) = x"
unfolding basis_prj_def
 apply (subst ubasis_until_same)
  apply (rule rangeI)
 apply (rule inv_f_f)
 apply (rule inj_basis_emb)
done

lemma basis_prj_node:
  "\<lbrakk>finite S; node i a S \<notin> range (basis_emb :: 'a compact_basis \<Rightarrow> nat)\<rbrakk>
    \<Longrightarrow> basis_prj (node i a S) = (basis_prj a :: 'a compact_basis)"
unfolding basis_prj_def by simp

lemma basis_prj_0: "basis_prj 0 = compact_bot"
apply (subst basis_emb_compact_bot [symmetric])
apply (rule basis_prj_basis_emb)
done

lemma node_eq_basis_emb_iff:
  "finite S \<Longrightarrow> node i a S = basis_emb x \<longleftrightarrow>
    x \<noteq> compact_bot \<and> i = place x \<and> a = basis_emb (sub x) \<and>
        S = basis_emb ` {y. place y < place x \<and> x \<sqsubseteq> y}"
apply (cases "x = compact_bot", simp)
apply (simp add: basis_emb.simps [of x])
apply (simp add: fin2)
done

lemma basis_prj_mono: "ubasis_le a b \<Longrightarrow> basis_prj a \<sqsubseteq> basis_prj b"
proof (induct a b rule: ubasis_le.induct)
  case (ubasis_le_refl a) show ?case by (rule below_refl)
next
  case (ubasis_le_trans a b c) thus ?case by - (rule below_trans)
next
  case (ubasis_le_lower S a i) thus ?case
    apply (cases "node i a S \<in> range (basis_emb :: 'a compact_basis \<Rightarrow> nat)")
     apply (erule rangeE, rename_tac x)
     apply (simp add: basis_prj_basis_emb)
     apply (simp add: node_eq_basis_emb_iff)
     apply (simp add: basis_prj_basis_emb)
     apply (rule sub_below)
    apply (simp add: basis_prj_node)
    done
next
  case (ubasis_le_upper S b a i) thus ?case
    apply (cases "node i a S \<in> range (basis_emb :: 'a compact_basis \<Rightarrow> nat)")
     apply (erule rangeE, rename_tac x)
     apply (simp add: basis_prj_basis_emb)
     apply (clarsimp simp add: node_eq_basis_emb_iff)
     apply (simp add: basis_prj_basis_emb)
    apply (simp add: basis_prj_node)
    done
qed

lemma basis_emb_prj_less: "ubasis_le (basis_emb (basis_prj x)) x"
unfolding basis_prj_def
 apply (subst f_inv_onto_f [where f=basis_emb])
  apply (rule ubasis_until)
  apply (rule range_eqI [where x=compact_bot])
  apply simp
 apply (rule ubasis_until_less)
done

hide (open) const
  node
  choose
  choose_pos
  place
  sub

subsubsection {* EP-pair from any bifinite domain into @{typ udom} *}

definition
  udom_emb :: "'a::bifinite \<rightarrow> udom"
where
  "udom_emb = compact_basis.basis_fun (\<lambda>x. udom_principal (basis_emb x))"

definition
  udom_prj :: "udom \<rightarrow> 'a::bifinite"
where
  "udom_prj = udom.basis_fun (\<lambda>x. Rep_compact_basis (basis_prj x))"

lemma udom_emb_principal:
  "udom_emb\<cdot>(Rep_compact_basis x) = udom_principal (basis_emb x)"
unfolding udom_emb_def
apply (rule compact_basis.basis_fun_principal)
apply (rule udom.principal_mono)
apply (erule basis_emb_mono)
done

lemma udom_prj_principal:
  "udom_prj\<cdot>(udom_principal x) = Rep_compact_basis (basis_prj x)"
unfolding udom_prj_def
apply (rule udom.basis_fun_principal)
apply (rule compact_basis.principal_mono)
apply (erule basis_prj_mono)
done

lemma ep_pair_udom: "ep_pair udom_emb udom_prj"
 apply default
  apply (rule compact_basis.principal_induct, simp)
  apply (simp add: udom_emb_principal udom_prj_principal)
  apply (simp add: basis_prj_basis_emb)
 apply (rule udom.principal_induct, simp)
 apply (simp add: udom_emb_principal udom_prj_principal)
 apply (rule basis_emb_prj_less)
done

end
