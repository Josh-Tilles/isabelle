(*  Title:      HOL/Lifting_Sum.thy
    Author:     Brian Huffman and Ondrej Kuncar
*)

header {* Setup for Lifting/Transfer for the sum type *}

theory Lifting_Sum
imports Lifting
begin

subsection {* Relator and predicator properties *}

definition
   sum_rel :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'a + 'b \<Rightarrow> 'c + 'd \<Rightarrow> bool"
where
   "sum_rel R1 R2 x y =
     (case (x, y) of (Inl x, Inl y) \<Rightarrow> R1 x y
     | (Inr x, Inr y) \<Rightarrow> R2 x y
     | _ \<Rightarrow> False)"

lemma sum_rel_simps[simp]:
  "sum_rel R1 R2 (Inl a1) (Inl b1) = R1 a1 b1"
  "sum_rel R1 R2 (Inl a1) (Inr b2) = False"
  "sum_rel R1 R2 (Inr a2) (Inl b1) = False"
  "sum_rel R1 R2 (Inr a2) (Inr b2) = R2 a2 b2"
  unfolding sum_rel_def by simp_all

abbreviation (input) "sum_pred \<equiv> sum_case"

lemma sum_rel_eq [relator_eq]:
  "sum_rel (op =) (op =) = (op =)"
  by (simp add: sum_rel_def fun_eq_iff split: sum.split)

lemma sum_rel_mono[relator_mono]:
  assumes "A \<le> C"
  assumes "B \<le> D"
  shows "(sum_rel A B) \<le> (sum_rel C D)"
using assms by (auto simp: sum_rel_def split: sum.splits)

lemma sum_rel_OO[relator_distr]:
  "(sum_rel A B) OO (sum_rel C D) = sum_rel (A OO C) (B OO D)"
by (rule ext)+ (auto simp add: sum_rel_def OO_def split_sum_ex split: sum.split)

lemma Domainp_sum[relator_domain]:
  assumes "Domainp R1 = P1"
  assumes "Domainp R2 = P2"
  shows "Domainp (sum_rel R1 R2) = (sum_pred P1 P2)"
using assms
by (auto simp add: Domainp_iff split_sum_ex iff: fun_eq_iff split: sum.split)

lemma reflp_sum_rel[reflexivity_rule]:
  "reflp R1 \<Longrightarrow> reflp R2 \<Longrightarrow> reflp (sum_rel R1 R2)"
  unfolding reflp_def split_sum_all sum_rel_simps by fast

lemma left_total_sum_rel[reflexivity_rule]:
  "left_total R1 \<Longrightarrow> left_total R2 \<Longrightarrow> left_total (sum_rel R1 R2)"
  using assms unfolding left_total_def split_sum_all split_sum_ex by simp

lemma left_unique_sum_rel [reflexivity_rule]:
  "left_unique R1 \<Longrightarrow> left_unique R2 \<Longrightarrow> left_unique (sum_rel R1 R2)"
  using assms unfolding left_unique_def split_sum_all by simp

lemma right_total_sum_rel [transfer_rule]:
  "right_total R1 \<Longrightarrow> right_total R2 \<Longrightarrow> right_total (sum_rel R1 R2)"
  unfolding right_total_def split_sum_all split_sum_ex by simp

lemma right_unique_sum_rel [transfer_rule]:
  "right_unique R1 \<Longrightarrow> right_unique R2 \<Longrightarrow> right_unique (sum_rel R1 R2)"
  unfolding right_unique_def split_sum_all by simp

lemma bi_total_sum_rel [transfer_rule]:
  "bi_total R1 \<Longrightarrow> bi_total R2 \<Longrightarrow> bi_total (sum_rel R1 R2)"
  using assms unfolding bi_total_def split_sum_all split_sum_ex by simp

lemma bi_unique_sum_rel [transfer_rule]:
  "bi_unique R1 \<Longrightarrow> bi_unique R2 \<Longrightarrow> bi_unique (sum_rel R1 R2)"
  using assms unfolding bi_unique_def split_sum_all by simp

lemma sum_invariant_commute [invariant_commute]: 
  "sum_rel (Lifting.invariant P1) (Lifting.invariant P2) = Lifting.invariant (sum_pred P1 P2)"
  by (auto simp add: fun_eq_iff Lifting.invariant_def sum_rel_def split: sum.split)

subsection {* Quotient theorem for the Lifting package *}

lemma Quotient_sum[quot_map]:
  assumes "Quotient R1 Abs1 Rep1 T1"
  assumes "Quotient R2 Abs2 Rep2 T2"
  shows "Quotient (sum_rel R1 R2) (sum_map Abs1 Abs2)
    (sum_map Rep1 Rep2) (sum_rel T1 T2)"
  using assms unfolding Quotient_alt_def
  by (simp add: split_sum_all)

subsection {* Transfer rules for the Transfer package *}

context
begin
interpretation lifting_syntax .

lemma Inl_transfer [transfer_rule]: "(A ===> sum_rel A B) Inl Inl"
  unfolding fun_rel_def by simp

lemma Inr_transfer [transfer_rule]: "(B ===> sum_rel A B) Inr Inr"
  unfolding fun_rel_def by simp

lemma sum_case_transfer [transfer_rule]:
  "((A ===> C) ===> (B ===> C) ===> sum_rel A B ===> C) sum_case sum_case"
  unfolding fun_rel_def sum_rel_def by (simp split: sum.split)

end

end

