(*  Title:      HOLCF/Porder.thy
    ID:         $Id$
    Author:     Franz Regensburger
*)

header {* Partial orders *}

theory Porder
imports Datatype Finite_Set
begin

subsection {* Type class for partial orders *}

class sq_ord = type +
  fixes sq_le :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

notation
  sq_le (infixl "<<" 55)

notation (xsymbols)
  sq_le (infixl "\<sqsubseteq>" 55)

axclass po < sq_ord
  refl_less [iff]: "x \<sqsubseteq> x"
  antisym_less:    "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> x = y"
  trans_less:      "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"

text {* minimal fixes least element *}

lemma minimal2UU[OF allI] : "\<forall>x::'a::po. uu \<sqsubseteq> x \<Longrightarrow> uu = (THE u. \<forall>y. u \<sqsubseteq> y)"
by (blast intro: theI2 antisym_less)

text {* the reverse law of anti-symmetry of @{term "op <<"} *}

lemma antisym_less_inverse: "(x::'a::po) = y \<Longrightarrow> x \<sqsubseteq> y \<and> y \<sqsubseteq> x"
by simp

lemma box_less: "\<lbrakk>(a::'a::po) \<sqsubseteq> b; c \<sqsubseteq> a; b \<sqsubseteq> d\<rbrakk> \<Longrightarrow> c \<sqsubseteq> d"
by (rule trans_less [OF trans_less])

lemma po_eq_conv: "((x::'a::po) = y) = (x \<sqsubseteq> y \<and> y \<sqsubseteq> x)"
by (fast elim!: antisym_less_inverse intro!: antisym_less)

lemma rev_trans_less: "\<lbrakk>(y::'a::po) \<sqsubseteq> z; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
by (rule trans_less)

lemma sq_ord_less_eq_trans: "\<lbrakk>a \<sqsubseteq> b; b = c\<rbrakk> \<Longrightarrow> a \<sqsubseteq> c"
by (rule subst)

lemma sq_ord_eq_less_trans: "\<lbrakk>a = b; b \<sqsubseteq> c\<rbrakk> \<Longrightarrow> a \<sqsubseteq> c"
by (rule ssubst)

lemmas HOLCF_trans_rules [trans] =
  trans_less
  antisym_less
  sq_ord_less_eq_trans
  sq_ord_eq_less_trans

subsection {* Least upper bounds *}

definition
  is_ub :: "['a set, 'a::po] \<Rightarrow> bool"  (infixl "<|" 55)  where
  "(S <| x) = (\<forall>y. y \<in> S \<longrightarrow> y \<sqsubseteq> x)"

definition
  is_lub :: "['a set, 'a::po] \<Rightarrow> bool"  (infixl "<<|" 55)  where
  "(S <<| x) = (S <| x \<and> (\<forall>u. S <| u \<longrightarrow> x \<sqsubseteq> u))"

definition
  lub :: "'a set \<Rightarrow> 'a::po" where
  "lub S = (THE x. S <<| x)"

abbreviation
  Lub  (binder "LUB " 10) where
  "LUB n. t n == lub (range t)"

notation (xsymbols)
  Lub  (binder "\<Squnion> " 10)


text {* lubs are unique *}

lemma unique_lub: "\<lbrakk>S <<| x; S <<| y\<rbrakk> \<Longrightarrow> x = y"
apply (unfold is_lub_def is_ub_def)
apply (blast intro: antisym_less)
done

text {* technical lemmas about @{term lub} and @{term is_lub} *}

lemma lubI: "M <<| x \<Longrightarrow> M <<| lub M"
apply (unfold lub_def)
apply (rule theI)
apply assumption
apply (erule (1) unique_lub)
done

lemma thelubI: "M <<| l \<Longrightarrow> lub M = l"
by (rule unique_lub [OF lubI])

lemma lub_singleton [simp]: "lub {x} = x"
by (simp add: thelubI is_lub_def is_ub_def)

text {* access to some definition as inference rule *}

lemma is_lubD1: "S <<| x \<Longrightarrow> S <| x"
by (unfold is_lub_def, simp)

lemma is_lub_lub: "\<lbrakk>S <<| x; S <| u\<rbrakk> \<Longrightarrow> x \<sqsubseteq> u"
by (unfold is_lub_def, simp)

lemma is_lubI: "\<lbrakk>S <| x; \<And>u. S <| u \<Longrightarrow> x \<sqsubseteq> u\<rbrakk> \<Longrightarrow> S <<| x"
by (unfold is_lub_def, fast)

subsection {* Countable chains *}

definition
  -- {* Here we use countable chains and I prefer to code them as functions! *}
  chain :: "(nat \<Rightarrow> 'a::po) \<Rightarrow> bool" where
  "chain F = (\<forall>i. F i \<sqsubseteq> F (Suc i))"

text {* chains are monotone functions *}

lemma chain_mono [rule_format]: "chain F \<Longrightarrow> x < y \<longrightarrow> F x \<sqsubseteq> F y"
apply (unfold chain_def)
apply (induct_tac y)
apply simp
apply (blast elim: less_SucE intro: trans_less)
done

lemma chain_mono3: "\<lbrakk>chain F; x \<le> y\<rbrakk> \<Longrightarrow> F x \<sqsubseteq> F y"
apply (drule le_imp_less_or_eq)
apply (blast intro: chain_mono)
done

lemma chainE: "chain F \<Longrightarrow> F i \<sqsubseteq> F (Suc i)"
by (unfold chain_def, simp)

lemma chainI: "(\<And>i. F i \<sqsubseteq> F (Suc i)) \<Longrightarrow> chain F"
by (unfold chain_def, simp)

lemma chain_shift: "chain Y \<Longrightarrow> chain (\<lambda>i. Y (i + j))"
apply (rule chainI)
apply simp
apply (erule chainE)
done

text {* technical lemmas about (least) upper bounds of chains *}

lemma ub_rangeD: "range S <| x \<Longrightarrow> S i \<sqsubseteq> x"
by (unfold is_ub_def, simp)

lemma ub_rangeI: "(\<And>i. S i \<sqsubseteq> x) \<Longrightarrow> range S <| x"
by (unfold is_ub_def, fast)

lemma is_ub_lub: "range S <<| x \<Longrightarrow> S i \<sqsubseteq> x"
by (rule is_lubD1 [THEN ub_rangeD])

lemma is_ub_range_shift:
  "chain S \<Longrightarrow> range (\<lambda>i. S (i + j)) <| x = range S <| x"
apply (rule iffI)
apply (rule ub_rangeI)
apply (rule_tac y="S (i + j)" in trans_less)
apply (erule chain_mono3)
apply (rule le_add1)
apply (erule ub_rangeD)
apply (rule ub_rangeI)
apply (erule ub_rangeD)
done

lemma is_lub_range_shift:
  "chain S \<Longrightarrow> range (\<lambda>i. S (i + j)) <<| x = range S <<| x"
by (simp add: is_lub_def is_ub_range_shift)

text {* the lub of a constant chain is the constant *}

lemma chain_const [simp]: "chain (\<lambda>i. c)"
by (simp add: chainI)

lemma lub_const: "range (\<lambda>x. c) <<| c"
by (blast dest: ub_rangeD intro: is_lubI ub_rangeI)

lemma thelub_const [simp]: "(\<Squnion>i. c) = c"
by (rule lub_const [THEN thelubI])

subsection {* Totally ordered sets *}

definition
  -- {* Arbitrary chains are total orders *}
  tord :: "'a::po set \<Rightarrow> bool" where
  "tord S = (\<forall>x y. x \<in> S \<and> y \<in> S \<longrightarrow> (x \<sqsubseteq> y \<or> y \<sqsubseteq> x))"

text {* The range of a chain is a totally ordered *}

lemma chain_tord: "chain F \<Longrightarrow> tord (range F)"
apply (unfold tord_def, clarify)
apply (rule nat_less_cases)
apply (fast intro: chain_mono)+
done

lemma finite_tord_has_max [rule_format]:
  "finite S \<Longrightarrow> S \<noteq> {} \<longrightarrow> tord S \<longrightarrow> (\<exists>y\<in>S. \<forall>x\<in>S. x \<sqsubseteq> y)"
 apply (erule finite_induct, simp)
 apply (rename_tac a S, clarify)
 apply (case_tac "S = {}", simp)
 apply (drule (1) mp)
 apply (drule mp, simp add: tord_def)
 apply (erule bexE, rename_tac z)
 apply (subgoal_tac "a \<sqsubseteq> z \<or> z \<sqsubseteq> a")
  apply (erule disjE)
   apply (rule_tac x="z" in bexI, simp, simp)
  apply (rule_tac x="a" in bexI)
   apply (clarsimp elim!: rev_trans_less)
  apply simp
 apply (simp add: tord_def)
done

subsection {* Finite chains *}

definition
  -- {* finite chains, needed for monotony of continuous functions *}
  max_in_chain :: "[nat, nat \<Rightarrow> 'a::po] \<Rightarrow> bool" where
  "max_in_chain i C = (\<forall>j. i \<le> j \<longrightarrow> C i = C j)"

definition
  finite_chain :: "(nat \<Rightarrow> 'a::po) \<Rightarrow> bool" where
  "finite_chain C = (chain C \<and> (\<exists>i. max_in_chain i C))"

text {* results about finite chains *}

lemma lub_finch1: "\<lbrakk>chain C; max_in_chain i C\<rbrakk> \<Longrightarrow> range C <<| C i"
apply (unfold max_in_chain_def)
apply (rule is_lubI)
apply (rule ub_rangeI, rename_tac j)
apply (rule_tac x=i and y=j in linorder_le_cases)
apply simp
apply (erule (1) chain_mono3)
apply (erule ub_rangeD)
done

lemma lub_finch2:
        "finite_chain C \<Longrightarrow> range C <<| C (LEAST i. max_in_chain i C)"
apply (unfold finite_chain_def)
apply (erule conjE)
apply (erule LeastI2_ex)
apply (erule (1) lub_finch1)
done

lemma finch_imp_finite_range: "finite_chain Y \<Longrightarrow> finite (range Y)"
 apply (unfold finite_chain_def, clarify)
 apply (rule_tac f="Y" and n="Suc i" in nat_seg_image_imp_finite)
 apply (rule equalityI)
  apply (rule subsetI)
  apply (erule rangeE, rename_tac j)
  apply (rule_tac x=i and y=j in linorder_le_cases)
   apply (subgoal_tac "Y j = Y i", simp)
   apply (simp add: max_in_chain_def)
  apply simp
 apply fast
done

lemma finite_range_imp_finch:
  "\<lbrakk>chain Y; finite (range Y)\<rbrakk> \<Longrightarrow> finite_chain Y"
 apply (subgoal_tac "\<exists>y\<in>range Y. \<forall>x\<in>range Y. x \<sqsubseteq> y")
  apply (clarsimp, rename_tac i)
  apply (subgoal_tac "max_in_chain i Y")
   apply (simp add: finite_chain_def exI)
  apply (simp add: max_in_chain_def po_eq_conv chain_mono3)
 apply (erule finite_tord_has_max, simp)
 apply (erule chain_tord)
done

lemma bin_chain: "x \<sqsubseteq> y \<Longrightarrow> chain (\<lambda>i. if i=0 then x else y)"
by (rule chainI, simp)

lemma bin_chainmax:
  "x \<sqsubseteq> y \<Longrightarrow> max_in_chain (Suc 0) (\<lambda>i. if i=0 then x else y)"
by (unfold max_in_chain_def, simp)

lemma lub_bin_chain:
  "x \<sqsubseteq> y \<Longrightarrow> range (\<lambda>i::nat. if i=0 then x else y) <<| y"
apply (frule bin_chain)
apply (drule bin_chainmax)
apply (drule (1) lub_finch1)
apply simp
done

text {* the maximal element in a chain is its lub *}

lemma lub_chain_maxelem: "\<lbrakk>Y i = c; \<forall>i. Y i \<sqsubseteq> c\<rbrakk> \<Longrightarrow> lub (range Y) = c"
by (blast dest: ub_rangeD intro: thelubI is_lubI ub_rangeI)

end
