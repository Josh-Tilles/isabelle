(*  Title:      HOLCF/Pcpo.thy
    Author:     Franz Regensburger
*)

header {* Classes cpo and pcpo *}

theory Pcpo
imports Porder
begin

subsection {* Complete partial orders *}

text {* The class cpo of chain complete partial orders *}

class cpo = po +
  assumes cpo: "chain S \<Longrightarrow> \<exists>x. range S <<| x"
begin

text {* in cpo's everthing equal to THE lub has lub properties for every chain *}

lemma cpo_lubI: "chain S \<Longrightarrow> range S <<| (\<Squnion>i. S i)"
  by (fast dest: cpo elim: lubI)

lemma thelubE: "\<lbrakk>chain S; (\<Squnion>i. S i) = l\<rbrakk> \<Longrightarrow> range S <<| l"
  by (blast dest: cpo intro: lubI)

text {* Properties of the lub *}

lemma is_ub_thelub: "chain S \<Longrightarrow> S x \<sqsubseteq> (\<Squnion>i. S i)"
  by (blast dest: cpo intro: lubI [THEN is_ub_lub])

lemma is_lub_thelub:
  "\<lbrakk>chain S; range S <| x\<rbrakk> \<Longrightarrow> (\<Squnion>i. S i) \<sqsubseteq> x"
  by (blast dest: cpo intro: lubI [THEN is_lub_lub])

lemma lub_below_iff: "chain S \<Longrightarrow> (\<Squnion>i. S i) \<sqsubseteq> x \<longleftrightarrow> (\<forall>i. S i \<sqsubseteq> x)"
  by (simp add: is_lub_below_iff [OF cpo_lubI] is_ub_def)

lemma lub_range_mono:
  "\<lbrakk>range X \<subseteq> range Y; chain Y; chain X\<rbrakk>
    \<Longrightarrow> (\<Squnion>i. X i) \<sqsubseteq> (\<Squnion>i. Y i)"
apply (erule is_lub_thelub)
apply (rule ub_rangeI)
apply (subgoal_tac "\<exists>j. X i = Y j")
apply  clarsimp
apply  (erule is_ub_thelub)
apply auto
done

lemma lub_range_shift:
  "chain Y \<Longrightarrow> (\<Squnion>i. Y (i + j)) = (\<Squnion>i. Y i)"
apply (rule below_antisym)
apply (rule lub_range_mono)
apply    fast
apply   assumption
apply (erule chain_shift)
apply (rule is_lub_thelub)
apply assumption
apply (rule ub_rangeI)
apply (rule_tac y="Y (i + j)" in below_trans)
apply (erule chain_mono)
apply (rule le_add1)
apply (rule is_ub_thelub)
apply (erule chain_shift)
done

lemma maxinch_is_thelub:
  "chain Y \<Longrightarrow> max_in_chain i Y = ((\<Squnion>i. Y i) = Y i)"
apply (rule iffI)
apply (fast intro!: thelubI lub_finch1)
apply (unfold max_in_chain_def)
apply (safe intro!: below_antisym)
apply (fast elim!: chain_mono)
apply (drule sym)
apply (force elim!: is_ub_thelub)
done

text {* the @{text "\<sqsubseteq>"} relation between two chains is preserved by their lubs *}

lemma lub_mono:
  "\<lbrakk>chain X; chain Y; \<And>i. X i \<sqsubseteq> Y i\<rbrakk> 
    \<Longrightarrow> (\<Squnion>i. X i) \<sqsubseteq> (\<Squnion>i. Y i)"
apply (erule is_lub_thelub)
apply (rule ub_rangeI)
apply (rule below_trans)
apply (erule meta_spec)
apply (erule is_ub_thelub)
done

text {* the = relation between two chains is preserved by their lubs *}

lemma lub_equal:
  "\<lbrakk>chain X; chain Y; \<forall>k. X k = Y k\<rbrakk>
    \<Longrightarrow> (\<Squnion>i. X i) = (\<Squnion>i. Y i)"
  by (simp only: fun_eq_iff [symmetric])

lemma lub_eq:
  "(\<And>i. X i = Y i) \<Longrightarrow> (\<Squnion>i. X i) = (\<Squnion>i. Y i)"
  by simp

text {* more results about mono and = of lubs of chains *}

lemma lub_mono2:
  "\<lbrakk>\<exists>j. \<forall>i>j. X i = Y i; chain X; chain Y\<rbrakk>
    \<Longrightarrow> (\<Squnion>i. X i) \<sqsubseteq> (\<Squnion>i. Y i)"
apply (erule exE)
apply (subgoal_tac "(\<Squnion>i. X (i + Suc j)) \<sqsubseteq> (\<Squnion>i. Y (i + Suc j))")
apply (thin_tac "\<forall>i>j. X i = Y i")
apply (simp only: lub_range_shift)
apply simp
done

lemma lub_equal2:
  "\<lbrakk>\<exists>j. \<forall>i>j. X i = Y i; chain X; chain Y\<rbrakk>
    \<Longrightarrow> (\<Squnion>i. X i) = (\<Squnion>i. Y i)"
  by (blast intro: below_antisym lub_mono2 sym)

lemma lub_mono3:
  "\<lbrakk>chain Y; chain X; \<forall>i. \<exists>j. Y i \<sqsubseteq> X j\<rbrakk>
    \<Longrightarrow> (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. X i)"
apply (erule is_lub_thelub)
apply (rule ub_rangeI)
apply (erule allE)
apply (erule exE)
apply (erule below_trans)
apply (erule is_ub_thelub)
done

lemma ch2ch_lub:
  assumes 1: "\<And>j. chain (\<lambda>i. Y i j)"
  assumes 2: "\<And>i. chain (\<lambda>j. Y i j)"
  shows "chain (\<lambda>i. \<Squnion>j. Y i j)"
apply (rule chainI)
apply (rule lub_mono [OF 2 2])
apply (rule chainE [OF 1])
done

lemma diag_lub:
  assumes 1: "\<And>j. chain (\<lambda>i. Y i j)"
  assumes 2: "\<And>i. chain (\<lambda>j. Y i j)"
  shows "(\<Squnion>i. \<Squnion>j. Y i j) = (\<Squnion>i. Y i i)"
proof (rule below_antisym)
  have 3: "chain (\<lambda>i. Y i i)"
    apply (rule chainI)
    apply (rule below_trans)
    apply (rule chainE [OF 1])
    apply (rule chainE [OF 2])
    done
  have 4: "chain (\<lambda>i. \<Squnion>j. Y i j)"
    by (rule ch2ch_lub [OF 1 2])
  show "(\<Squnion>i. \<Squnion>j. Y i j) \<sqsubseteq> (\<Squnion>i. Y i i)"
    apply (rule is_lub_thelub [OF 4])
    apply (rule ub_rangeI)
    apply (rule lub_mono3 [rule_format, OF 2 3])
    apply (rule exI)
    apply (rule below_trans)
    apply (rule chain_mono [OF 1 le_maxI1])
    apply (rule chain_mono [OF 2 le_maxI2])
    done
  show "(\<Squnion>i. Y i i) \<sqsubseteq> (\<Squnion>i. \<Squnion>j. Y i j)"
    apply (rule lub_mono [OF 3 4])
    apply (rule is_ub_thelub [OF 2])
    done
qed

lemma ex_lub:
  assumes 1: "\<And>j. chain (\<lambda>i. Y i j)"
  assumes 2: "\<And>i. chain (\<lambda>j. Y i j)"
  shows "(\<Squnion>i. \<Squnion>j. Y i j) = (\<Squnion>j. \<Squnion>i. Y i j)"
  by (simp add: diag_lub 1 2)

end

subsection {* Pointed cpos *}

text {* The class pcpo of pointed cpos *}

class pcpo = cpo +
  assumes least: "\<exists>x. \<forall>y. x \<sqsubseteq> y"
begin

definition UU :: 'a where
  "UU = (THE x. \<forall>y. x \<sqsubseteq> y)"

notation (xsymbols)
  UU  ("\<bottom>")

text {* derive the old rule minimal *}
 
lemma UU_least: "\<forall>z. \<bottom> \<sqsubseteq> z"
apply (unfold UU_def)
apply (rule theI')
apply (rule ex_ex1I)
apply (rule least)
apply (blast intro: below_antisym)
done

lemma minimal [iff]: "\<bottom> \<sqsubseteq> x"
by (rule UU_least [THEN spec])

end

text {* Simproc to rewrite @{term "\<bottom> = x"} to @{term "x = \<bottom>"}. *}

setup {*
  Reorient_Proc.add
    (fn Const(@{const_name UU}, _) => true | _ => false)
*}

simproc_setup reorient_bottom ("\<bottom> = x") = Reorient_Proc.proc

context pcpo
begin

text {* useful lemmas about @{term \<bottom>} *}

lemma below_UU_iff [simp]: "(x \<sqsubseteq> \<bottom>) = (x = \<bottom>)"
by (simp add: po_eq_conv)

lemma eq_UU_iff: "(x = \<bottom>) = (x \<sqsubseteq> \<bottom>)"
by simp

lemma UU_I: "x \<sqsubseteq> \<bottom> \<Longrightarrow> x = \<bottom>"
by (subst eq_UU_iff)

lemma lub_eq_bottom_iff: "chain Y \<Longrightarrow> (\<Squnion>i. Y i) = \<bottom> \<longleftrightarrow> (\<forall>i. Y i = \<bottom>)"
by (simp only: eq_UU_iff lub_below_iff)

lemma chain_UU_I: "\<lbrakk>chain Y; (\<Squnion>i. Y i) = \<bottom>\<rbrakk> \<Longrightarrow> \<forall>i. Y i = \<bottom>"
by (simp add: lub_eq_bottom_iff)

lemma chain_UU_I_inverse: "\<forall>i::nat. Y i = \<bottom> \<Longrightarrow> (\<Squnion>i. Y i) = \<bottom>"
by simp

lemma chain_UU_I_inverse2: "(\<Squnion>i. Y i) \<noteq> \<bottom> \<Longrightarrow> \<exists>i::nat. Y i \<noteq> \<bottom>"
  by (blast intro: chain_UU_I_inverse)

lemma notUU_I: "\<lbrakk>x \<sqsubseteq> y; x \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> y \<noteq> \<bottom>"
  by (blast intro: UU_I)

lemma chain_mono2: "\<lbrakk>\<exists>j. Y j \<noteq> \<bottom>; chain Y\<rbrakk> \<Longrightarrow> \<exists>j. \<forall>i>j. Y i \<noteq> \<bottom>"
  by (blast dest: notUU_I chain_mono_less)

end

subsection {* Chain-finite and flat cpos *}

text {* further useful classes for HOLCF domains *}

class chfin = po +
  assumes chfin: "chain Y \<Longrightarrow> \<exists>n. max_in_chain n Y"
begin

subclass cpo
apply default
apply (frule chfin)
apply (blast intro: lub_finch1)
done

lemma chfin2finch: "chain Y \<Longrightarrow> finite_chain Y"
  by (simp add: chfin finite_chain_def)

end

class flat = pcpo +
  assumes ax_flat: "x \<sqsubseteq> y \<Longrightarrow> x = \<bottom> \<or> x = y"
begin

subclass chfin
apply default
apply (unfold max_in_chain_def)
apply (case_tac "\<forall>i. Y i = \<bottom>")
apply simp
apply simp
apply (erule exE)
apply (rule_tac x="i" in exI)
apply clarify
apply (blast dest: chain_mono ax_flat)
done

lemma flat_below_iff:
  shows "(x \<sqsubseteq> y) = (x = \<bottom> \<or> x = y)"
  by (safe dest!: ax_flat)

lemma flat_eq: "a \<noteq> \<bottom> \<Longrightarrow> a \<sqsubseteq> b = (a = b)"
  by (safe dest!: ax_flat)

end

subsection {* Discrete cpos *}

class discrete_cpo = below +
  assumes discrete_cpo [simp]: "x \<sqsubseteq> y \<longleftrightarrow> x = y"
begin

subclass po
proof qed simp_all

text {* In a discrete cpo, every chain is constant *}

lemma discrete_chain_const:
  assumes S: "chain S"
  shows "\<exists>x. S = (\<lambda>i. x)"
proof (intro exI ext)
  fix i :: nat
  have "S 0 \<sqsubseteq> S i" using S le0 by (rule chain_mono)
  hence "S 0 = S i" by simp
  thus "S i = S 0" by (rule sym)
qed

subclass chfin
proof
  fix S :: "nat \<Rightarrow> 'a"
  assume S: "chain S"
  hence "\<exists>x. S = (\<lambda>i. x)" by (rule discrete_chain_const)
  hence "max_in_chain 0 S"
    unfolding max_in_chain_def by auto
  thus "\<exists>i. max_in_chain i S" ..
qed

end

end
