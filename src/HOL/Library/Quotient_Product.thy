(*  Title:      HOL/Library/Quotient_Product.thy
    Author:     Cezary Kaliszyk and Christian Urban
*)

header {* Quotient infrastructure for the product type *}

theory Quotient_Product
imports Main Quotient_Syntax
begin

definition
  prod_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'c \<Rightarrow> 'b \<times> 'd \<Rightarrow> bool"
where
  "prod_rel R1 R2 = (\<lambda>(a, b) (c, d). R1 a c \<and> R2 b d)"

declare [[map prod = (map_pair, prod_rel)]]

lemma prod_rel_apply [simp]:
  "prod_rel R1 R2 (a, b) (c, d) \<longleftrightarrow> R1 a c \<and> R2 b d"
  by (simp add: prod_rel_def)

lemma map_pair_id [id_simps]:
  shows "map_pair id id = id"
  by (simp add: fun_eq_iff)

lemma prod_rel_eq [id_simps]:
  shows "prod_rel (op =) (op =) = (op =)"
  by (simp add: fun_eq_iff)

lemma prod_equivp [quot_equiv]:
  assumes "equivp R1"
  assumes "equivp R2"
  shows "equivp (prod_rel R1 R2)"
  using assms by (auto intro!: equivpI reflpI sympI transpI elim!: equivpE elim: reflpE sympE transpE)

lemma prod_quotient [quot_thm]:
  assumes "Quotient R1 Abs1 Rep1"
  assumes "Quotient R2 Abs2 Rep2"
  shows "Quotient (prod_rel R1 R2) (map_pair Abs1 Abs2) (map_pair Rep1 Rep2)"
  apply (rule QuotientI)
  apply (simp add: map_pair.compositionality map_pair.identity
     Quotient_abs_rep [OF assms(1)] Quotient_abs_rep [OF assms(2)])
  apply (simp add: split_paired_all Quotient_rel_rep [OF assms(1)] Quotient_rel_rep [OF assms(2)])
  using Quotient_rel [OF assms(1)] Quotient_rel [OF assms(2)]
  apply (auto simp add: split_paired_all)
  done

lemma Pair_rsp [quot_respect]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  assumes q2: "Quotient R2 Abs2 Rep2"
  shows "(R1 ===> R2 ===> prod_rel R1 R2) Pair Pair"
  by (auto simp add: prod_rel_def)

lemma Pair_prs [quot_preserve]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  assumes q2: "Quotient R2 Abs2 Rep2"
  shows "(Rep1 ---> Rep2 ---> (map_pair Abs1 Abs2)) Pair = Pair"
  apply(simp add: fun_eq_iff)
  apply(simp add: Quotient_abs_rep[OF q1] Quotient_abs_rep[OF q2])
  done

lemma fst_rsp [quot_respect]:
  assumes "Quotient R1 Abs1 Rep1"
  assumes "Quotient R2 Abs2 Rep2"
  shows "(prod_rel R1 R2 ===> R1) fst fst"
  by auto

lemma fst_prs [quot_preserve]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  assumes q2: "Quotient R2 Abs2 Rep2"
  shows "(map_pair Rep1 Rep2 ---> Abs1) fst = fst"
  by (simp add: fun_eq_iff Quotient_abs_rep[OF q1])

lemma snd_rsp [quot_respect]:
  assumes "Quotient R1 Abs1 Rep1"
  assumes "Quotient R2 Abs2 Rep2"
  shows "(prod_rel R1 R2 ===> R2) snd snd"
  by auto

lemma snd_prs [quot_preserve]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  assumes q2: "Quotient R2 Abs2 Rep2"
  shows "(map_pair Rep1 Rep2 ---> Abs2) snd = snd"
  by (simp add: fun_eq_iff Quotient_abs_rep[OF q2])

lemma split_rsp [quot_respect]:
  shows "((R1 ===> R2 ===> (op =)) ===> (prod_rel R1 R2) ===> (op =)) split split"
  by (auto intro!: fun_relI elim!: fun_relE)

lemma split_prs [quot_preserve]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and     q2: "Quotient R2 Abs2 Rep2"
  shows "(((Abs1 ---> Abs2 ---> id) ---> map_pair Rep1 Rep2 ---> id) split) = split"
  by (simp add: fun_eq_iff Quotient_abs_rep[OF q1] Quotient_abs_rep[OF q2])

lemma [quot_respect]:
  shows "((R2 ===> R2 ===> op =) ===> (R1 ===> R1 ===> op =) ===>
  prod_rel R2 R1 ===> prod_rel R2 R1 ===> op =) prod_rel prod_rel"
  by (auto simp add: fun_rel_def)

lemma [quot_preserve]:
  assumes q1: "Quotient R1 abs1 rep1"
  and     q2: "Quotient R2 abs2 rep2"
  shows "((abs1 ---> abs1 ---> id) ---> (abs2 ---> abs2 ---> id) --->
  map_pair rep1 rep2 ---> map_pair rep1 rep2 ---> id) prod_rel = prod_rel"
  by (simp add: fun_eq_iff Quotient_abs_rep[OF q1] Quotient_abs_rep[OF q2])

lemma [quot_preserve]:
  shows"(prod_rel ((rep1 ---> rep1 ---> id) R1) ((rep2 ---> rep2 ---> id) R2)
  (l1, l2) (r1, r2)) = (R1 (rep1 l1) (rep1 r1) \<and> R2 (rep2 l2) (rep2 r2))"
  by simp

declare Pair_eq[quot_preserve]

end
