(* Title:      HOL/Presburger.thy
   ID:         $Id$
   Author:     Amine Chaieb, TU Muenchen
*)

header {* Decision Procedure for Presburger Arithmetic *}

theory Presburger
imports Arith_Tools SetInterval
uses
  "Tools/Qelim/cooper_data.ML"
  "Tools/Qelim/generated_cooper.ML"
  "Tools/Qelim/qelim.ML"
  ("Tools/Qelim/cooper.ML")
  ("Tools/Qelim/presburger.ML")
begin

setup CooperData.setup

subsection{* The @{text "-\<infinity>"} and @{text "+\<infinity>"} Properties *}


lemma minf:
  "\<lbrakk>\<exists>(z ::'a::linorder).\<forall>x<z. P x = P' x; \<exists>z.\<forall>x<z. Q x = Q' x\<rbrakk> 
     \<Longrightarrow> \<exists>z.\<forall>x<z. (P x \<and> Q x) = (P' x \<and> Q' x)"
  "\<lbrakk>\<exists>(z ::'a::linorder).\<forall>x<z. P x = P' x; \<exists>z.\<forall>x<z. Q x = Q' x\<rbrakk> 
     \<Longrightarrow> \<exists>z.\<forall>x<z. (P x \<or> Q x) = (P' x \<or> Q' x)"
  "\<exists>(z ::'a::{linorder}).\<forall>x<z.(x = t) = False"
  "\<exists>(z ::'a::{linorder}).\<forall>x<z.(x \<noteq> t) = True"
  "\<exists>(z ::'a::{linorder}).\<forall>x<z.(x < t) = True"
  "\<exists>(z ::'a::{linorder}).\<forall>x<z.(x \<le> t) = True"
  "\<exists>(z ::'a::{linorder}).\<forall>x<z.(x > t) = False"
  "\<exists>(z ::'a::{linorder}).\<forall>x<z.(x \<ge> t) = False"
  "\<exists>z.\<forall>(x::'a::{linorder,plus,Divides.div})<z. (d dvd x + s) = (d dvd x + s)"
  "\<exists>z.\<forall>(x::'a::{linorder,plus,Divides.div})<z. (\<not> d dvd x + s) = (\<not> d dvd x + s)"
  "\<exists>z.\<forall>x<z. F = F"
  by ((erule exE, erule exE,rule_tac x="min z za" in exI,simp)+, (rule_tac x="t" in exI,fastsimp)+) simp_all

lemma pinf:
  "\<lbrakk>\<exists>(z ::'a::linorder).\<forall>x>z. P x = P' x; \<exists>z.\<forall>x>z. Q x = Q' x\<rbrakk> 
     \<Longrightarrow> \<exists>z.\<forall>x>z. (P x \<and> Q x) = (P' x \<and> Q' x)"
  "\<lbrakk>\<exists>(z ::'a::linorder).\<forall>x>z. P x = P' x; \<exists>z.\<forall>x>z. Q x = Q' x\<rbrakk> 
     \<Longrightarrow> \<exists>z.\<forall>x>z. (P x \<or> Q x) = (P' x \<or> Q' x)"
  "\<exists>(z ::'a::{linorder}).\<forall>x>z.(x = t) = False"
  "\<exists>(z ::'a::{linorder}).\<forall>x>z.(x \<noteq> t) = True"
  "\<exists>(z ::'a::{linorder}).\<forall>x>z.(x < t) = False"
  "\<exists>(z ::'a::{linorder}).\<forall>x>z.(x \<le> t) = False"
  "\<exists>(z ::'a::{linorder}).\<forall>x>z.(x > t) = True"
  "\<exists>(z ::'a::{linorder}).\<forall>x>z.(x \<ge> t) = True"
  "\<exists>z.\<forall>(x::'a::{linorder,plus,Divides.div})>z. (d dvd x + s) = (d dvd x + s)"
  "\<exists>z.\<forall>(x::'a::{linorder,plus,Divides.div})>z. (\<not> d dvd x + s) = (\<not> d dvd x + s)"
  "\<exists>z.\<forall>x>z. F = F"
  by ((erule exE, erule exE,rule_tac x="max z za" in exI,simp)+,(rule_tac x="t" in exI,fastsimp)+) simp_all

lemma inf_period:
  "\<lbrakk>\<forall>x k. P x = P (x - k*D); \<forall>x k. Q x = Q (x - k*D)\<rbrakk> 
    \<Longrightarrow> \<forall>x k. (P x \<and> Q x) = (P (x - k*D) \<and> Q (x - k*D))"
  "\<lbrakk>\<forall>x k. P x = P (x - k*D); \<forall>x k. Q x = Q (x - k*D)\<rbrakk> 
    \<Longrightarrow> \<forall>x k. (P x \<or> Q x) = (P (x - k*D) \<or> Q (x - k*D))"
  "(d::'a::{comm_ring,Divides.div}) dvd D \<Longrightarrow> \<forall>x k. (d dvd x + t) = (d dvd (x - k*D) + t)"
  "(d::'a::{comm_ring,Divides.div}) dvd D \<Longrightarrow> \<forall>x k. (\<not>d dvd x + t) = (\<not>d dvd (x - k*D) + t)"
  "\<forall>x k. F = F"
by simp_all
  (clarsimp simp add: dvd_def, rule iffI, clarsimp,rule_tac x = "kb - ka*k" in exI,
    simp add: ring_simps, clarsimp,rule_tac x = "kb + ka*k" in exI,simp add: ring_simps)+

subsection{* The A and B sets *}
lemma bset:
  "\<lbrakk>\<forall>x.(\<forall>j \<in> {1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> P x \<longrightarrow> P(x - D) ;
     \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> Q x \<longrightarrow> Q(x - D)\<rbrakk> \<Longrightarrow> 
  \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j) \<longrightarrow> (P x \<and> Q x) \<longrightarrow> (P(x - D) \<and> Q (x - D))"
  "\<lbrakk>\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> P x \<longrightarrow> P(x - D) ;
     \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> Q x \<longrightarrow> Q(x - D)\<rbrakk> \<Longrightarrow> 
  \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (P x \<or> Q x) \<longrightarrow> (P(x - D) \<or> Q (x - D))"
  "\<lbrakk>D>0; t - 1\<in> B\<rbrakk> \<Longrightarrow> (\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x = t) \<longrightarrow> (x - D = t))"
  "\<lbrakk>D>0 ; t \<in> B\<rbrakk> \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x \<noteq> t) \<longrightarrow> (x - D \<noteq> t))"
  "D>0 \<Longrightarrow> (\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x < t) \<longrightarrow> (x - D < t))"
  "D>0 \<Longrightarrow> (\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x \<le> t) \<longrightarrow> (x - D \<le> t))"
  "\<lbrakk>D>0 ; t \<in> B\<rbrakk> \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x > t) \<longrightarrow> (x - D > t))"
  "\<lbrakk>D>0 ; t - 1 \<in> B\<rbrakk> \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x \<ge> t) \<longrightarrow> (x - D \<ge> t))"
  "d dvd D \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (d dvd x+t) \<longrightarrow> (d dvd (x - D) + t))"
  "d dvd D \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (\<not>d dvd x+t) \<longrightarrow> (\<not> d dvd (x - D) + t))"
  "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j) \<longrightarrow> F \<longrightarrow> F"
proof (blast, blast)
  assume dp: "D > 0" and tB: "t - 1\<in> B"
  show "(\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x = t) \<longrightarrow> (x - D = t))" 
    apply (rule allI, rule impI,erule ballE[where x="1"],erule ballE[where x="t - 1"])
    using dp tB by simp_all
next
  assume dp: "D > 0" and tB: "t \<in> B"
  show "(\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x \<noteq> t) \<longrightarrow> (x - D \<noteq> t))" 
    apply (rule allI, rule impI,erule ballE[where x="D"],erule ballE[where x="t"])
    using dp tB by simp_all
next
  assume dp: "D > 0" thus "(\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x < t) \<longrightarrow> (x - D < t))" by arith
next
  assume dp: "D > 0" thus "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x \<le> t) \<longrightarrow> (x - D \<le> t)" by arith
next
  assume dp: "D > 0" and tB:"t \<in> B"
  {fix x assume nob: "\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j" and g: "x > t" and ng: "\<not> (x - D) > t"
    hence "x -t \<le> D" and "1 \<le> x - t" by simp+
      hence "\<exists>j \<in> {1 .. D}. x - t = j" by auto
      hence "\<exists>j \<in> {1 .. D}. x = t + j" by (simp add: ring_simps)
      with nob tB have "False" by simp}
  thus "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x > t) \<longrightarrow> (x - D > t)" by blast
next
  assume dp: "D > 0" and tB:"t - 1\<in> B"
  {fix x assume nob: "\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j" and g: "x \<ge> t" and ng: "\<not> (x - D) \<ge> t"
    hence "x - (t - 1) \<le> D" and "1 \<le> x - (t - 1)" by simp+
      hence "\<exists>j \<in> {1 .. D}. x - (t - 1) = j" by auto
      hence "\<exists>j \<in> {1 .. D}. x = (t - 1) + j" by (simp add: ring_simps)
      with nob tB have "False" by simp}
  thus "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x \<ge> t) \<longrightarrow> (x - D \<ge> t)" by blast
next
  assume d: "d dvd D"
  {fix x assume H: "d dvd x + t" with d have "d dvd (x - D) + t"
      by (clarsimp simp add: dvd_def,rule_tac x= "ka - k" in exI,simp add: ring_simps)}
  thus "\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (d dvd x+t) \<longrightarrow> (d dvd (x - D) + t)" by simp
next
  assume d: "d dvd D"
  {fix x assume H: "\<not>(d dvd x + t)" with d have "\<not>d dvd (x - D) + t"
      by (clarsimp simp add: dvd_def,erule_tac x= "ka + k" in allE,simp add: ring_simps)}
  thus "\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (\<not>d dvd x+t) \<longrightarrow> (\<not>d dvd (x - D) + t)" by auto
qed blast

lemma aset:
  "\<lbrakk>\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> P x \<longrightarrow> P(x + D) ;
     \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> Q x \<longrightarrow> Q(x + D)\<rbrakk> \<Longrightarrow> 
  \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j) \<longrightarrow> (P x \<and> Q x) \<longrightarrow> (P(x + D) \<and> Q (x + D))"
  "\<lbrakk>\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> P x \<longrightarrow> P(x + D) ;
     \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> Q x \<longrightarrow> Q(x + D)\<rbrakk> \<Longrightarrow> 
  \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (P x \<or> Q x) \<longrightarrow> (P(x + D) \<or> Q (x + D))"
  "\<lbrakk>D>0; t + 1\<in> A\<rbrakk> \<Longrightarrow> (\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x = t) \<longrightarrow> (x + D = t))"
  "\<lbrakk>D>0 ; t \<in> A\<rbrakk> \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x \<noteq> t) \<longrightarrow> (x + D \<noteq> t))"
  "\<lbrakk>D>0; t\<in> A\<rbrakk> \<Longrightarrow>(\<forall>(x::int). (\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x < t) \<longrightarrow> (x + D < t))"
  "\<lbrakk>D>0; t + 1 \<in> A\<rbrakk> \<Longrightarrow> (\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x \<le> t) \<longrightarrow> (x + D \<le> t))"
  "D>0 \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x > t) \<longrightarrow> (x + D > t))"
  "D>0 \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x \<ge> t) \<longrightarrow> (x + D \<ge> t))"
  "d dvd D \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (d dvd x+t) \<longrightarrow> (d dvd (x + D) + t))"
  "d dvd D \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (\<not>d dvd x+t) \<longrightarrow> (\<not> d dvd (x + D) + t))"
  "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j) \<longrightarrow> F \<longrightarrow> F"
proof (blast, blast)
  assume dp: "D > 0" and tA: "t + 1 \<in> A"
  show "(\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x = t) \<longrightarrow> (x + D = t))" 
    apply (rule allI, rule impI,erule ballE[where x="1"],erule ballE[where x="t + 1"])
    using dp tA by simp_all
next
  assume dp: "D > 0" and tA: "t \<in> A"
  show "(\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x \<noteq> t) \<longrightarrow> (x + D \<noteq> t))" 
    apply (rule allI, rule impI,erule ballE[where x="D"],erule ballE[where x="t"])
    using dp tA by simp_all
next
  assume dp: "D > 0" thus "(\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x > t) \<longrightarrow> (x + D > t))" by arith
next
  assume dp: "D > 0" thus "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x \<ge> t) \<longrightarrow> (x + D \<ge> t)" by arith
next
  assume dp: "D > 0" and tA:"t \<in> A"
  {fix x assume nob: "\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j" and g: "x < t" and ng: "\<not> (x + D) < t"
    hence "t - x \<le> D" and "1 \<le> t - x" by simp+
      hence "\<exists>j \<in> {1 .. D}. t - x = j" by auto
      hence "\<exists>j \<in> {1 .. D}. x = t - j" by (auto simp add: ring_simps) 
      with nob tA have "False" by simp}
  thus "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x < t) \<longrightarrow> (x + D < t)" by blast
next
  assume dp: "D > 0" and tA:"t + 1\<in> A"
  {fix x assume nob: "\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j" and g: "x \<le> t" and ng: "\<not> (x + D) \<le> t"
    hence "(t + 1) - x \<le> D" and "1 \<le> (t + 1) - x" by (simp_all add: ring_simps)
      hence "\<exists>j \<in> {1 .. D}. (t + 1) - x = j" by auto
      hence "\<exists>j \<in> {1 .. D}. x = (t + 1) - j" by (auto simp add: ring_simps)
      with nob tA have "False" by simp}
  thus "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x \<le> t) \<longrightarrow> (x + D \<le> t)" by blast
next
  assume d: "d dvd D"
  {fix x assume H: "d dvd x + t" with d have "d dvd (x + D) + t"
      by (clarsimp simp add: dvd_def,rule_tac x= "ka + k" in exI,simp add: ring_simps)}
  thus "\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (d dvd x+t) \<longrightarrow> (d dvd (x + D) + t)" by simp
next
  assume d: "d dvd D"
  {fix x assume H: "\<not>(d dvd x + t)" with d have "\<not>d dvd (x + D) + t"
      by (clarsimp simp add: dvd_def,erule_tac x= "ka - k" in allE,simp add: ring_simps)}
  thus "\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (\<not>d dvd x+t) \<longrightarrow> (\<not>d dvd (x + D) + t)" by auto
qed blast

subsection{* Cooper's Theorem @{text "-\<infinity>"} and @{text "+\<infinity>"} Version *}

subsubsection{* First some trivial facts about periodic sets or predicates *}
lemma periodic_finite_ex:
  assumes dpos: "(0::int) < d" and modd: "ALL x k. P x = P(x - k*d)"
  shows "(EX x. P x) = (EX j : {1..d}. P j)"
  (is "?LHS = ?RHS")
proof
  assume ?LHS
  then obtain x where P: "P x" ..
  have "x mod d = x - (x div d)*d" by(simp add:zmod_zdiv_equality mult_ac eq_diff_eq)
  hence Pmod: "P x = P(x mod d)" using modd by simp
  show ?RHS
  proof (cases)
    assume "x mod d = 0"
    hence "P 0" using P Pmod by simp
    moreover have "P 0 = P(0 - (-1)*d)" using modd by blast
    ultimately have "P d" by simp
    moreover have "d : {1..d}" using dpos by(simp add:atLeastAtMost_iff)
    ultimately show ?RHS ..
  next
    assume not0: "x mod d \<noteq> 0"
    have "P(x mod d)" using dpos P Pmod by(simp add:pos_mod_sign pos_mod_bound)
    moreover have "x mod d : {1..d}"
    proof -
      from dpos have "0 \<le> x mod d" by(rule pos_mod_sign)
      moreover from dpos have "x mod d < d" by(rule pos_mod_bound)
      ultimately show ?thesis using not0 by(simp add:atLeastAtMost_iff)
    qed
    ultimately show ?RHS ..
  qed
qed auto

subsubsection{* The @{text "-\<infinity>"} Version*}

lemma decr_lemma: "0 < (d::int) \<Longrightarrow> x - (abs(x-z)+1) * d < z"
by(induct rule: int_gr_induct,simp_all add:int_distrib)

lemma incr_lemma: "0 < (d::int) \<Longrightarrow> z < x + (abs(x-z)+1) * d"
by(induct rule: int_gr_induct, simp_all add:int_distrib)

theorem int_induct[case_names base step1 step2]:
  assumes 
  base: "P(k::int)" and step1: "\<And>i. \<lbrakk>k \<le> i; P i\<rbrakk> \<Longrightarrow> P(i+1)" and
  step2: "\<And>i. \<lbrakk>k \<ge> i; P i\<rbrakk> \<Longrightarrow> P(i - 1)"
  shows "P i"
proof -
  have "i \<le> k \<or> i\<ge> k" by arith
  thus ?thesis using prems int_ge_induct[where P="P" and k="k" and i="i"] int_le_induct[where P="P" and k="k" and i="i"] by blast
qed

lemma decr_mult_lemma:
  assumes dpos: "(0::int) < d" and minus: "\<forall>x. P x \<longrightarrow> P(x - d)" and knneg: "0 <= k"
  shows "ALL x. P x \<longrightarrow> P(x - k*d)"
using knneg
proof (induct rule:int_ge_induct)
  case base thus ?case by simp
next
  case (step i)
  {fix x
    have "P x \<longrightarrow> P (x - i * d)" using step.hyps by blast
    also have "\<dots> \<longrightarrow> P(x - (i + 1) * d)" using minus[THEN spec, of "x - i * d"]
      by (simp add:int_distrib OrderedGroup.diff_diff_eq[symmetric])
    ultimately have "P x \<longrightarrow> P(x - (i + 1) * d)" by blast}
  thus ?case ..
qed

lemma  minusinfinity:
  assumes dpos: "0 < d" and
    P1eqP1: "ALL x k. P1 x = P1(x - k*d)" and ePeqP1: "EX z::int. ALL x. x < z \<longrightarrow> (P x = P1 x)"
  shows "(EX x. P1 x) \<longrightarrow> (EX x. P x)"
proof
  assume eP1: "EX x. P1 x"
  then obtain x where P1: "P1 x" ..
  from ePeqP1 obtain z where P1eqP: "ALL x. x < z \<longrightarrow> (P x = P1 x)" ..
  let ?w = "x - (abs(x-z)+1) * d"
  from dpos have w: "?w < z" by(rule decr_lemma)
  have "P1 x = P1 ?w" using P1eqP1 by blast
  also have "\<dots> = P(?w)" using w P1eqP by blast
  finally have "P ?w" using P1 by blast
  thus "EX x. P x" ..
qed

lemma cpmi: 
  assumes dp: "0 < D" and p1:"\<exists>z. \<forall> x< z. P x = P' x"
  and nb:"\<forall>x.(\<forall> j\<in> {1..D}. \<forall>(b::int) \<in> B. x \<noteq> b+j) --> P (x) --> P (x - D)"
  and pd: "\<forall> x k. P' x = P' (x-k*D)"
  shows "(\<exists>x. P x) = ((\<exists> j\<in> {1..D} . P' j) | (\<exists> j \<in> {1..D}.\<exists> b\<in> B. P (b+j)))" 
         (is "?L = (?R1 \<or> ?R2)")
proof-
 {assume "?R2" hence "?L"  by blast}
 moreover
 {assume H:"?R1" hence "?L" using minusinfinity[OF dp pd p1] periodic_finite_ex[OF dp pd] by simp}
 moreover 
 { fix x
   assume P: "P x" and H: "\<not> ?R2"
   {fix y assume "\<not> (\<exists>j\<in>{1..D}. \<exists>b\<in>B. P (b + j))" and P: "P y"
     hence "~(EX (j::int) : {1..D}. EX (b::int) : B. y = b+j)" by auto
     with nb P  have "P (y - D)" by auto }
   hence "ALL x.~(EX (j::int) : {1..D}. EX (b::int) : B. P(b+j)) --> P (x) --> P (x - D)" by blast
   with H P have th: " \<forall>x. P x \<longrightarrow> P (x - D)" by auto
   from p1 obtain z where z: "ALL x. x < z --> (P x = P' x)" by blast
   let ?y = "x - (\<bar>x - z\<bar> + 1)*D"
   have zp: "0 <= (\<bar>x - z\<bar> + 1)" by arith
   from dp have yz: "?y < z" using decr_lemma[OF dp] by simp   
   from z[rule_format, OF yz] decr_mult_lemma[OF dp th zp, rule_format, OF P] have th2: " P' ?y" by auto
   with periodic_finite_ex[OF dp pd]
   have "?R1" by blast}
 ultimately show ?thesis by blast
qed

subsubsection {* The @{text "+\<infinity>"} Version*}

lemma  plusinfinity:
  assumes dpos: "(0::int) < d" and
    P1eqP1: "\<forall>x k. P' x = P'(x - k*d)" and ePeqP1: "\<exists> z. \<forall> x>z. P x = P' x"
  shows "(\<exists> x. P' x) \<longrightarrow> (\<exists> x. P x)"
proof
  assume eP1: "EX x. P' x"
  then obtain x where P1: "P' x" ..
  from ePeqP1 obtain z where P1eqP: "\<forall>x>z. P x = P' x" ..
  let ?w' = "x + (abs(x-z)+1) * d"
  let ?w = "x - (-(abs(x-z) + 1))*d"
  have ww'[simp]: "?w = ?w'" by (simp add: ring_simps)
  from dpos have w: "?w > z" by(simp only: ww' incr_lemma)
  hence "P' x = P' ?w" using P1eqP1 by blast
  also have "\<dots> = P(?w)" using w P1eqP by blast
  finally have "P ?w" using P1 by blast
  thus "EX x. P x" ..
qed

lemma incr_mult_lemma:
  assumes dpos: "(0::int) < d" and plus: "ALL x::int. P x \<longrightarrow> P(x + d)" and knneg: "0 <= k"
  shows "ALL x. P x \<longrightarrow> P(x + k*d)"
using knneg
proof (induct rule:int_ge_induct)
  case base thus ?case by simp
next
  case (step i)
  {fix x
    have "P x \<longrightarrow> P (x + i * d)" using step.hyps by blast
    also have "\<dots> \<longrightarrow> P(x + (i + 1) * d)" using plus[THEN spec, of "x + i * d"]
      by (simp add:int_distrib zadd_ac)
    ultimately have "P x \<longrightarrow> P(x + (i + 1) * d)" by blast}
  thus ?case ..
qed

lemma cppi: 
  assumes dp: "0 < D" and p1:"\<exists>z. \<forall> x> z. P x = P' x"
  and nb:"\<forall>x.(\<forall> j\<in> {1..D}. \<forall>(b::int) \<in> A. x \<noteq> b - j) --> P (x) --> P (x + D)"
  and pd: "\<forall> x k. P' x= P' (x-k*D)"
  shows "(\<exists>x. P x) = ((\<exists> j\<in> {1..D} . P' j) | (\<exists> j \<in> {1..D}.\<exists> b\<in> A. P (b - j)))" (is "?L = (?R1 \<or> ?R2)")
proof-
 {assume "?R2" hence "?L"  by blast}
 moreover
 {assume H:"?R1" hence "?L" using plusinfinity[OF dp pd p1] periodic_finite_ex[OF dp pd] by simp}
 moreover 
 { fix x
   assume P: "P x" and H: "\<not> ?R2"
   {fix y assume "\<not> (\<exists>j\<in>{1..D}. \<exists>b\<in>A. P (b - j))" and P: "P y"
     hence "~(EX (j::int) : {1..D}. EX (b::int) : A. y = b - j)" by auto
     with nb P  have "P (y + D)" by auto }
   hence "ALL x.~(EX (j::int) : {1..D}. EX (b::int) : A. P(b-j)) --> P (x) --> P (x + D)" by blast
   with H P have th: " \<forall>x. P x \<longrightarrow> P (x + D)" by auto
   from p1 obtain z where z: "ALL x. x > z --> (P x = P' x)" by blast
   let ?y = "x + (\<bar>x - z\<bar> + 1)*D"
   have zp: "0 <= (\<bar>x - z\<bar> + 1)" by arith
   from dp have yz: "?y > z" using incr_lemma[OF dp] by simp
   from z[rule_format, OF yz] incr_mult_lemma[OF dp th zp, rule_format, OF P] have th2: " P' ?y" by auto
   with periodic_finite_ex[OF dp pd]
   have "?R1" by blast}
 ultimately show ?thesis by blast
qed

lemma simp_from_to: "{i..j::int} = (if j < i then {} else insert i {i+1..j})"
apply(simp add:atLeastAtMost_def atLeast_def atMost_def)
apply(fastsimp)
done

theorem unity_coeff_ex: "(\<exists>(x::'a::{semiring_0,Divides.div}). P (l * x)) \<equiv> (\<exists>x. l dvd (x + 0) \<and> P x)"
  apply (rule eq_reflection[symmetric])
  apply (rule iffI)
  defer
  apply (erule exE)
  apply (rule_tac x = "l * x" in exI)
  apply (simp add: dvd_def)
  apply (rule_tac x="x" in exI, simp)
  apply (erule exE)
  apply (erule conjE)
  apply (erule dvdE)
  apply (rule_tac x = k in exI)
  apply simp
  done

lemma zdvd_mono: assumes not0: "(k::int) \<noteq> 0"
shows "((m::int) dvd t) \<equiv> (k*m dvd k*t)" 
  using not0 by (simp add: dvd_def)

lemma uminus_dvd_conv: "(d dvd (t::int)) \<equiv> (-d dvd t)" "(d dvd (t::int)) \<equiv> (d dvd -t)"
  by simp_all
text {* \bigskip Theorems for transforming predicates on nat to predicates on @{text int}*}
lemma all_nat: "(\<forall>x::nat. P x) = (\<forall>x::int. 0 <= x \<longrightarrow> P (nat x))"
  by (simp split add: split_nat)

lemma ex_nat: "(\<exists>x::nat. P x) = (\<exists>x::int. 0 <= x \<and> P (nat x))"
  apply (auto split add: split_nat)
  apply (rule_tac x="int x" in exI, simp)
  apply (rule_tac x = "nat x" in exI,erule_tac x = "nat x" in allE, simp)
  done

lemma zdiff_int_split: "P (int (x - y)) =
  ((y \<le> x \<longrightarrow> P (int x - int y)) \<and> (x < y \<longrightarrow> P 0))"
  by (case_tac "y \<le> x", simp_all add: zdiff_int)

lemma number_of1: "(0::int) <= number_of n \<Longrightarrow> (0::int) <= number_of (Int.Bit0 n) \<and> (0::int) <= number_of (Int.Bit1 n)"
by simp
lemma number_of2: "(0::int) <= Numeral0" by simp
lemma Suc_plus1: "Suc n = n + 1" by simp

text {*
  \medskip Specific instances of congruence rules, to prevent
  simplifier from looping. *}

theorem imp_le_cong: "(0 <= x \<Longrightarrow> P = P') \<Longrightarrow> (0 <= (x::int) \<longrightarrow> P) = (0 <= x \<longrightarrow> P')" by simp

theorem conj_le_cong: "(0 <= x \<Longrightarrow> P = P') \<Longrightarrow> (0 <= (x::int) \<and> P) = (0 <= x \<and> P')" 
  by (simp cong: conj_cong)
lemma int_eq_number_of_eq:
  "(((number_of v)::int) = (number_of w)) = iszero ((number_of (v + (uminus w)))::int)"
  by simp

lemma mod_eq0_dvd_iff[presburger]: "(m::nat) mod n = 0 \<longleftrightarrow> n dvd m"
unfolding dvd_eq_mod_eq_0[symmetric] ..

lemma zmod_eq0_zdvd_iff[presburger]: "(m::int) mod n = 0 \<longleftrightarrow> n dvd m"
unfolding zdvd_iff_zmod_eq_0[symmetric] ..
declare mod_1[presburger]
declare mod_0[presburger]
declare zmod_1[presburger]
declare zmod_zero[presburger]
declare zmod_self[presburger]
declare mod_self[presburger]
declare DIVISION_BY_ZERO_MOD[presburger]
declare nat_mod_div_trivial[presburger]
declare div_mod_equality2[presburger]
declare div_mod_equality[presburger]
declare mod_div_equality2[presburger]
declare mod_div_equality[presburger]
declare mod_mult_self1[presburger]
declare mod_mult_self2[presburger]
declare zdiv_zmod_equality2[presburger]
declare zdiv_zmod_equality[presburger]
declare mod2_Suc_Suc[presburger]
lemma [presburger]: "(a::int) div 0 = 0" and [presburger]: "a mod 0 = a"
using IntDiv.DIVISION_BY_ZERO by blast+

use "Tools/Qelim/cooper.ML"
oracle linzqe_oracle ("term") = Coopereif.cooper_oracle

use "Tools/Qelim/presburger.ML"

declaration {* fn _ =>
  arith_tactic_add
    (mk_arith_tactic "presburger" (fn ctxt => fn i => fn st =>
       (warning "Trying Presburger arithmetic ...";   
    Presburger.cooper_tac true [] [] ctxt i st)))
*}

method_setup presburger = {*
let
 fun keyword k = Scan.lift (Args.$$$ k -- Args.colon) >> K ()
 fun simple_keyword k = Scan.lift (Args.$$$ k) >> K ()
 val addN = "add"
 val delN = "del"
 val elimN = "elim"
 val any_keyword = keyword addN || keyword delN || simple_keyword elimN
 val thms = Scan.repeat (Scan.unless any_keyword Attrib.multi_thm) >> flat;
in
  fn src => Method.syntax 
   ((Scan.optional (simple_keyword elimN >> K false) true) -- 
    (Scan.optional (keyword addN |-- thms) []) -- 
    (Scan.optional (keyword delN |-- thms) [])) src 
  #> (fn (((elim, add_ths), del_ths),ctxt) => 
         Method.SIMPLE_METHOD' (Presburger.cooper_tac elim add_ths del_ths ctxt))
end
*} "Cooper's algorithm for Presburger arithmetic"

lemma [presburger]: "m mod 2 = (1::nat) \<longleftrightarrow> \<not> 2 dvd m " by presburger
lemma [presburger]: "m mod 2 = Suc 0 \<longleftrightarrow> \<not> 2 dvd m " by presburger
lemma [presburger]: "m mod (Suc (Suc 0)) = (1::nat) \<longleftrightarrow> \<not> 2 dvd m " by presburger
lemma [presburger]: "m mod (Suc (Suc 0)) = Suc 0 \<longleftrightarrow> \<not> 2 dvd m " by presburger
lemma [presburger]: "m mod 2 = (1::int) \<longleftrightarrow> \<not> 2 dvd m " by presburger


lemma zdvd_period:
  fixes a d :: int
  assumes advdd: "a dvd d"
  shows "a dvd (x + t) \<longleftrightarrow> a dvd ((x + c * d) + t)"
proof-
  {
    fix x k
    from inf_period(3) [OF advdd, rule_format, where x=x and k="-k"]  
    have "a dvd (x + t) \<longleftrightarrow> a dvd (x + k * d + t)" by simp
  }
  hence "\<forall>x.\<forall>k. ((a::int) dvd (x + t)) = (a dvd (x+k*d + t))"  by simp
  then show ?thesis by simp
qed


subsection {* Code generator setup *}

text {*
  Presburger arithmetic is convenient to prove some
  of the following code lemmas on integer numerals:
*}

lemma eq_Pls_Pls:
  "Int.Pls = Int.Pls \<longleftrightarrow> True" by presburger

lemma eq_Pls_Min:
  "Int.Pls = Int.Min \<longleftrightarrow> False"
  unfolding Pls_def Int.Min_def by presburger

lemma eq_Pls_Bit0:
  "Int.Pls = Int.Bit0 k \<longleftrightarrow> Int.Pls = k"
  unfolding Pls_def Bit0_def by presburger

lemma eq_Pls_Bit1:
  "Int.Pls = Int.Bit1 k \<longleftrightarrow> False"
  unfolding Pls_def Bit1_def by presburger

lemma eq_Min_Pls:
  "Int.Min = Int.Pls \<longleftrightarrow> False"
  unfolding Pls_def Int.Min_def by presburger

lemma eq_Min_Min:
  "Int.Min = Int.Min \<longleftrightarrow> True" by presburger

lemma eq_Min_Bit0:
  "Int.Min = Int.Bit0 k \<longleftrightarrow> False"
  unfolding Int.Min_def Bit0_def by presburger

lemma eq_Min_Bit1:
  "Int.Min = Int.Bit1 k \<longleftrightarrow> Int.Min = k"
  unfolding Int.Min_def Bit1_def by presburger

lemma eq_Bit0_Pls:
  "Int.Bit0 k = Int.Pls \<longleftrightarrow> Int.Pls = k"
  unfolding Pls_def Bit0_def by presburger

lemma eq_Bit1_Pls:
  "Int.Bit1 k = Int.Pls \<longleftrightarrow> False"
  unfolding Pls_def Bit1_def by presburger

lemma eq_Bit0_Min:
  "Int.Bit0 k = Int.Min \<longleftrightarrow> False"
  unfolding Int.Min_def Bit0_def by presburger

lemma eq_Bit1_Min:
  "Int.Bit1 k = Int.Min \<longleftrightarrow> Int.Min = k"
  unfolding Int.Min_def Bit1_def by presburger

lemma eq_Bit0_Bit0:
  "Int.Bit0 k1 = Int.Bit0 k2 \<longleftrightarrow> k1 = k2"
  unfolding Bit0_def by presburger

lemma eq_Bit0_Bit1:
  "Int.Bit0 k1 = Int.Bit1 k2 \<longleftrightarrow> False"
  unfolding Bit0_def Bit1_def by presburger

lemma eq_Bit1_Bit0:
  "Int.Bit1 k1 = Int.Bit0 k2 \<longleftrightarrow> False"
  unfolding Bit0_def Bit1_def by presburger

lemma eq_Bit1_Bit1:
  "Int.Bit1 k1 = Int.Bit1 k2 \<longleftrightarrow> k1 = k2"
  unfolding Bit1_def by presburger

lemma eq_number_of:
  "(number_of k \<Colon> int) = number_of l \<longleftrightarrow> k = l" 
  unfolding number_of_is_id ..


lemma less_eq_Pls_Pls:
  "Int.Pls \<le> Int.Pls \<longleftrightarrow> True" by rule+

lemma less_eq_Pls_Min:
  "Int.Pls \<le> Int.Min \<longleftrightarrow> False"
  unfolding Pls_def Int.Min_def by presburger

lemma less_eq_Pls_Bit0:
  "Int.Pls \<le> Int.Bit0 k \<longleftrightarrow> Int.Pls \<le> k"
  unfolding Pls_def Bit0_def by auto

lemma less_eq_Pls_Bit1:
  "Int.Pls \<le> Int.Bit1 k \<longleftrightarrow> Int.Pls \<le> k"
  unfolding Pls_def Bit1_def by auto

lemma less_eq_Min_Pls:
  "Int.Min \<le> Int.Pls \<longleftrightarrow> True"
  unfolding Pls_def Int.Min_def by presburger

lemma less_eq_Min_Min:
  "Int.Min \<le> Int.Min \<longleftrightarrow> True" by rule+

lemma less_eq_Min_Bit0:
  "Int.Min \<le> Int.Bit0 k \<longleftrightarrow> Int.Min < k"
  unfolding Int.Min_def Bit0_def by auto

lemma less_eq_Min_Bit1:
  "Int.Min \<le> Int.Bit1 k \<longleftrightarrow> Int.Min \<le> k"
  unfolding Int.Min_def Bit1_def by auto

lemma less_eq_Bit0_Pls:
  "Int.Bit0 k \<le> Int.Pls \<longleftrightarrow> k \<le> Int.Pls"
  unfolding Pls_def Bit0_def by simp

lemma less_eq_Bit1_Pls:
  "Int.Bit1 k \<le> Int.Pls \<longleftrightarrow> k < Int.Pls"
  unfolding Pls_def Bit1_def by auto

lemma less_eq_Bit0_Min:
  "Int.Bit0 k \<le> Int.Min \<longleftrightarrow> k \<le> Int.Min"
  unfolding Int.Min_def Bit0_def by auto

lemma less_eq_Bit1_Min:
  "Int.Bit1 k \<le> Int.Min \<longleftrightarrow> k \<le> Int.Min"
  unfolding Int.Min_def Bit1_def by auto

lemma less_eq_Bit0_Bit0:
  "Int.Bit0 k1 \<le> Int.Bit0 k2 \<longleftrightarrow> k1 \<le> k2"
  unfolding Bit0_def by auto

lemma less_eq_Bit0_Bit1:
  "Int.Bit0 k1 \<le> Int.Bit1 k2 \<longleftrightarrow> k1 \<le> k2"
  unfolding Bit0_def Bit1_def by auto

lemma less_eq_Bit1_Bit0:
  "Int.Bit1 k1 \<le> Int.Bit0 k2 \<longleftrightarrow> k1 < k2"
  unfolding Bit0_def Bit1_def by auto

lemma less_eq_Bit1_Bit1:
  "Int.Bit1 k1 \<le> Int.Bit1 k2 \<longleftrightarrow> k1 \<le> k2"
  unfolding Bit1_def by auto

lemma less_eq_number_of:
  "(number_of k \<Colon> int) \<le> number_of l \<longleftrightarrow> k \<le> l"
  unfolding number_of_is_id ..


lemma less_Pls_Pls:
  "Int.Pls < Int.Pls \<longleftrightarrow> False" by simp 

lemma less_Pls_Min:
  "Int.Pls < Int.Min \<longleftrightarrow> False"
  unfolding Pls_def Int.Min_def  by presburger 

lemma less_Pls_Bit0:
  "Int.Pls < Int.Bit0 k \<longleftrightarrow> Int.Pls < k"
  unfolding Pls_def Bit0_def by auto

lemma less_Pls_Bit1:
  "Int.Pls < Int.Bit1 k \<longleftrightarrow> Int.Pls \<le> k"
  unfolding Pls_def Bit1_def by auto

lemma less_Min_Pls:
  "Int.Min < Int.Pls \<longleftrightarrow> True"
  unfolding Pls_def Int.Min_def by presburger 

lemma less_Min_Min:
  "Int.Min < Int.Min \<longleftrightarrow> False"  by simp

lemma less_Min_Bit0:
  "Int.Min < Int.Bit0 k \<longleftrightarrow> Int.Min < k"
  unfolding Int.Min_def Bit0_def by auto

lemma less_Min_Bit1:
  "Int.Min < Int.Bit1 k \<longleftrightarrow> Int.Min < k"
  unfolding Int.Min_def Bit1_def by auto

lemma less_Bit0_Pls:
  "Int.Bit0 k < Int.Pls \<longleftrightarrow> k < Int.Pls"
  unfolding Pls_def Bit0_def by auto

lemma less_Bit1_Pls:
  "Int.Bit1 k < Int.Pls \<longleftrightarrow> k < Int.Pls"
  unfolding Pls_def Bit1_def by auto

lemma less_Bit0_Min:
  "Int.Bit0 k < Int.Min \<longleftrightarrow> k \<le> Int.Min"
  unfolding Int.Min_def Bit0_def by auto

lemma less_Bit1_Min:
  "Int.Bit1 k < Int.Min \<longleftrightarrow> k < Int.Min"
  unfolding Int.Min_def Bit1_def by auto

lemma less_Bit0_Bit0:
  "Int.Bit0 k1 < Int.Bit0 k2 \<longleftrightarrow> k1 < k2"
  unfolding Bit0_def by auto

lemma less_Bit0_Bit1:
  "Int.Bit0 k1 < Int.Bit1 k2 \<longleftrightarrow> k1 \<le> k2"
  unfolding Bit0_def Bit1_def by auto

lemma less_Bit1_Bit0:
  "Int.Bit1 k1 < Int.Bit0 k2 \<longleftrightarrow> k1 < k2"
  unfolding Bit0_def Bit1_def by auto

lemma less_Bit1_Bit1:
  "Int.Bit1 k1 < Int.Bit1 k2 \<longleftrightarrow> k1 < k2"
  unfolding Bit1_def by auto

lemma less_number_of:
  "(number_of k \<Colon> int) < number_of l \<longleftrightarrow> k < l"
  unfolding number_of_is_id ..

lemmas pred_succ_numeral_code [code func] =
  pred_bin_simps succ_bin_simps

lemmas plus_numeral_code [code func] =
  add_bin_simps
  arith_extra_simps(1) [where 'a = int]

lemmas minus_numeral_code [code func] =
  minus_bin_simps
  arith_extra_simps(2) [where 'a = int]
  arith_extra_simps(5) [where 'a = int]

lemmas times_numeral_code [code func] =
  mult_bin_simps
  arith_extra_simps(4) [where 'a = int]

lemmas eq_numeral_code [code func] =
  eq_Pls_Pls eq_Pls_Min eq_Pls_Bit0 eq_Pls_Bit1
  eq_Min_Pls eq_Min_Min eq_Min_Bit0 eq_Min_Bit1
  eq_Bit0_Pls eq_Bit1_Pls eq_Bit0_Min eq_Bit1_Min
  eq_Bit0_Bit0 eq_Bit0_Bit1 eq_Bit1_Bit0 eq_Bit1_Bit1
  eq_number_of

lemmas less_eq_numeral_code [code func] =
  less_eq_Pls_Pls less_eq_Pls_Min less_eq_Pls_Bit0 less_eq_Pls_Bit1
  less_eq_Min_Pls less_eq_Min_Min less_eq_Min_Bit0 less_eq_Min_Bit1
  less_eq_Bit0_Pls less_eq_Bit1_Pls less_eq_Bit0_Min less_eq_Bit1_Min
  less_eq_Bit0_Bit0 less_eq_Bit0_Bit1 less_eq_Bit1_Bit0 less_eq_Bit1_Bit1
  less_eq_number_of

lemmas less_numeral_code [code func] =
  less_Pls_Pls less_Pls_Min less_Pls_Bit0 less_Pls_Bit1
  less_Min_Pls less_Min_Min less_Min_Bit0 less_Min_Bit1
  less_Bit0_Pls less_Bit1_Pls less_Bit0_Min less_Bit1_Min
  less_Bit0_Bit0 less_Bit0_Bit1 less_Bit1_Bit0 less_Bit1_Bit1
  less_number_of

context ring_1
begin

lemma of_int_num [code func]:
  "of_int k = (if k = 0 then 0 else if k < 0 then
     - of_int (- k) else let
       (l, m) = divAlg (k, 2);
       l' = of_int l
     in if m = 0 then l' + l' else l' + l' + 1)"
proof -
  have aux1: "k mod (2\<Colon>int) \<noteq> (0\<Colon>int) \<Longrightarrow> 
    of_int k = of_int (k div 2 * 2 + 1)"
  proof -
    assume "k mod 2 \<noteq> 0"
    then have "k mod 2 = 1" by arith
    moreover have "of_int k = of_int (k div 2 * 2 + k mod 2)" by simp
    ultimately show ?thesis by auto
  qed
  have aux2: "\<And>x. of_int 2 * x = x + x"
  proof -
    fix x
    have int2: "(2::int) = 1 + 1" by arith
    show "of_int 2 * x = x + x"
    unfolding int2 of_int_add left_distrib by simp
  qed
  have aux3: "\<And>x. x * of_int 2 = x + x"
  proof -
    fix x
    have int2: "(2::int) = 1 + 1" by arith
    show "x * of_int 2 = x + x" 
    unfolding int2 of_int_add right_distrib by simp
  qed
  from aux1 show ?thesis by (auto simp add: divAlg_mod_div Let_def aux2 aux3)
qed

end

end
