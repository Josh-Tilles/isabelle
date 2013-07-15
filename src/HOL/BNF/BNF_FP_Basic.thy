(*  Title:      HOL/BNF/BNF_FP_Basic.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Basic fixed point operations on bounded natural functors.
*)

header {* Basic Fixed Point Operations on Bounded Natural Functors *}

theory BNF_FP_Basic
imports BNF_Comp BNF_Ctr_Sugar
keywords
  "defaults"
begin

lemma mp_conj: "(P \<longrightarrow> Q) \<and> R \<Longrightarrow> P \<Longrightarrow> R \<and> Q"
by auto

lemma eq_sym_Unity_conv: "(x = (() = ())) = x"
by blast

lemma unit_case_Unity: "(case u of () => f) = f"
by (cases u) (hypsubst, rule unit.cases)

lemma prod_case_Pair_iden: "(case p of (x, y) \<Rightarrow> (x, y)) = p"
by simp

lemma unit_all_impI: "(P () \<Longrightarrow> Q ()) \<Longrightarrow> \<forall>x. P x \<longrightarrow> Q x"
by simp

lemma prod_all_impI: "(\<And>x y. P (x, y) \<Longrightarrow> Q (x, y)) \<Longrightarrow> \<forall>x. P x \<longrightarrow> Q x"
by clarify

lemma prod_all_impI_step: "(\<And>x. \<forall>y. P (x, y) \<longrightarrow> Q (x, y)) \<Longrightarrow> \<forall>x. P x \<longrightarrow> Q x"
by auto

lemma pointfree_idE: "f \<circ> g = id \<Longrightarrow> f (g x) = x"
unfolding o_def fun_eq_iff by simp

lemma o_bij:
  assumes gf: "g \<circ> f = id" and fg: "f \<circ> g = id"
  shows "bij f"
unfolding bij_def inj_on_def surj_def proof safe
  fix a1 a2 assume "f a1 = f a2"
  hence "g ( f a1) = g (f a2)" by simp
  thus "a1 = a2" using gf unfolding fun_eq_iff by simp
next
  fix b
  have "b = f (g b)"
  using fg unfolding fun_eq_iff by simp
  thus "EX a. b = f a" by blast
qed

lemma ssubst_mem: "\<lbrakk>t = s; s \<in> X\<rbrakk> \<Longrightarrow> t \<in> X" by simp

lemma sum_case_step:
"sum_case (sum_case f' g') g (Inl p) = sum_case f' g' p"
"sum_case f (sum_case f' g') (Inr p) = sum_case f' g' p"
by auto

lemma one_pointE: "\<lbrakk>\<And>x. s = x \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by simp

lemma obj_one_pointE: "\<forall>x. s = x \<longrightarrow> P \<Longrightarrow> P"
by blast

lemma obj_sumE_f:
"\<lbrakk>\<forall>x. s = f (Inl x) \<longrightarrow> P; \<forall>x. s = f (Inr x) \<longrightarrow> P\<rbrakk> \<Longrightarrow> \<forall>x. s = f x \<longrightarrow> P"
by (rule allI) (metis sumE)

lemma obj_sumE: "\<lbrakk>\<forall>x. s = Inl x \<longrightarrow> P; \<forall>x. s = Inr x \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (cases s) auto

lemma sum_case_if:
"sum_case f g (if p then Inl x else Inr y) = (if p then f x else g y)"
by simp

lemma mem_UN_compreh_eq: "(z : \<Union>{y. \<exists>x\<in>A. y = F x}) = (\<exists>x\<in>A. z : F x)"
by blast

lemma UN_compreh_eq_eq:
"\<Union>{y. \<exists>x\<in>A. y = {}} = {}"
"\<Union>{y. \<exists>x\<in>A. y = {x}} = A"
by blast+

lemma Inl_Inr_False: "(Inl x = Inr y) = False"
by simp

lemma prod_set_simps:
"fsts (x, y) = {x}"
"snds (x, y) = {y}"
unfolding fsts_def snds_def by simp+

lemma sum_set_simps:
"setl (Inl x) = {x}"
"setl (Inr x) = {}"
"setr (Inl x) = {}"
"setr (Inr x) = {x}"
unfolding sum_set_defs by simp+

lemma prod_rel_simp:
"prod_rel P Q (x, y) (x', y') \<longleftrightarrow> P x x' \<and> Q y y'"
unfolding prod_rel_def by simp

lemma sum_rel_simps:
"sum_rel P Q (Inl x) (Inl x') \<longleftrightarrow> P x x'"
"sum_rel P Q (Inr y) (Inr y') \<longleftrightarrow> Q y y'"
"sum_rel P Q (Inl x) (Inr y') \<longleftrightarrow> False"
"sum_rel P Q (Inr y) (Inl x') \<longleftrightarrow> False"
unfolding sum_rel_def by simp+

lemma spec2: "\<forall>x y. P x y \<Longrightarrow> P x y"
by blast

ML_file "Tools/bnf_fp_util.ML"
ML_file "Tools/bnf_fp_def_sugar_tactics.ML"
ML_file "Tools/bnf_fp_def_sugar.ML"

end
