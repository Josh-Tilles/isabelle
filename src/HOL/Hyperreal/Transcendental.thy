(*  Title       : Transcendental.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998,1999 University of Cambridge
                  1999,2001 University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header{*Power Series, Transcendental Functions etc.*}

theory Transcendental
imports NthRoot Fact Series EvenOdd Deriv
begin

subsection{*Properties of Power Series*}

lemma lemma_realpow_diff [rule_format (no_asm)]:
     "p \<le> n --> y ^ (Suc n - p) = ((y::real) ^ (n - p)) * y"
apply (induct "n", auto)
apply (subgoal_tac "p = Suc n")
apply (simp (no_asm_simp), auto)
apply (drule sym)
apply (simp add: Suc_diff_le mult_commute realpow_Suc [symmetric] 
       del: realpow_Suc)
done

lemma lemma_realpow_diff_sumr:
     "(\<Sum>p=0..<Suc n. (x ^ p) * y ^ ((Suc n) - p)) =  
      y * (\<Sum>p=0..<Suc n. (x ^ p) * (y ^ (n - p))::real)"
by (auto simp add: setsum_right_distrib lemma_realpow_diff mult_ac
  simp del: setsum_op_ivl_Suc cong: strong_setsum_cong)

lemma lemma_realpow_diff_sumr2:
     "x ^ (Suc n) - y ^ (Suc n) =  
      (x - y) * (\<Sum>p=0..<Suc n. (x ^ p) * (y ^(n - p))::real)"
apply (induct "n", simp)
apply (auto simp del: setsum_op_ivl_Suc)
apply (subst setsum_op_ivl_Suc)
apply (drule sym)
apply (auto simp add: lemma_realpow_diff_sumr right_distrib diff_minus mult_ac simp del: setsum_op_ivl_Suc)
done

lemma lemma_realpow_rev_sumr:
     "(\<Sum>p=0..<Suc n. (x ^ p) * (y ^ (n - p))) =  
      (\<Sum>p=0..<Suc n. (x ^ (n - p)) * (y ^ p)::real)"
apply (case_tac "x = y")
apply (auto simp add: mult_commute power_add [symmetric] simp del: setsum_op_ivl_Suc)
apply (rule_tac c1 = "x - y" in real_mult_left_cancel [THEN iffD1])
apply (rule_tac [2] minus_minus [THEN subst], simp)
apply (subst minus_mult_left)
apply (simp add: lemma_realpow_diff_sumr2 [symmetric] del: setsum_op_ivl_Suc)
done

text{*Power series has a `circle` of convergence, i.e. if it sums for @{term
x}, then it sums absolutely for @{term z} with @{term "\<bar>z\<bar> < \<bar>x\<bar>"}.*}

lemma powser_insidea:
  fixes x z :: real
  assumes 1: "summable (\<lambda>n. f n * x ^ n)"
  assumes 2: "\<bar>z\<bar> < \<bar>x\<bar>"
  shows "summable (\<lambda>n. \<bar>f n\<bar> * z ^ n)"
proof -
  from 2 have x_neq_0: "x \<noteq> 0" by clarsimp
  from 1 have "(\<lambda>n. f n * x ^ n) ----> 0"
    by (rule summable_LIMSEQ_zero)
  hence "convergent (\<lambda>n. f n * x ^ n)"
    by (rule convergentI)
  hence "Cauchy (\<lambda>n. f n * x ^ n)"
    by (simp add: Cauchy_convergent_iff)
  hence "Bseq (\<lambda>n. f n * x ^ n)"
    by (rule Cauchy_Bseq)
  then obtain K where 3: "0 < K" and 4: "\<forall>n. \<bar>f n * x ^ n\<bar> \<le> K"
    by (simp add: Bseq_def, safe)
  have "\<exists>N. \<forall>n\<ge>N. norm (\<bar>f n\<bar> * z ^ n) \<le> K * \<bar>z ^ n\<bar> * inverse \<bar>x ^ n\<bar>"
  proof (intro exI allI impI)
    fix n::nat assume "0 \<le> n"
    have "norm (\<bar>f n\<bar> * z ^ n) * \<bar>x ^ n\<bar> = \<bar>f n * x ^ n\<bar> * \<bar>z ^ n\<bar>"
      by (simp add: abs_mult)
    also have "\<dots> \<le> K * \<bar>z ^ n\<bar>"
      by (simp only: mult_right_mono 4 abs_ge_zero)
    also have "\<dots> = K * \<bar>z ^ n\<bar> * (inverse \<bar>x ^ n\<bar> * \<bar>x ^ n\<bar>)"
      by (simp add: x_neq_0)
    also have "\<dots> = K * \<bar>z ^ n\<bar> * inverse \<bar>x ^ n\<bar> * \<bar>x ^ n\<bar>"
      by (simp only: mult_assoc)
    finally show "norm (\<bar>f n\<bar> * z ^ n) \<le> K * \<bar>z ^ n\<bar> * inverse \<bar>x ^ n\<bar>"
      by (simp add: mult_le_cancel_right x_neq_0)
  qed
  moreover have "summable (\<lambda>n. K * \<bar>z ^ n\<bar> * inverse \<bar>x ^ n\<bar>)"
  proof -
    from 2 have "norm \<bar>z * inverse x\<bar> < 1"
      by (simp add: abs_mult divide_inverse [symmetric])
    hence "summable (\<lambda>n. \<bar>z * inverse x\<bar> ^ n)"
      by (rule summable_geometric)
    hence "summable (\<lambda>n. K * \<bar>z * inverse x\<bar> ^ n)"
      by (rule summable_mult)
    thus "summable (\<lambda>n. K * \<bar>z ^ n\<bar> * inverse \<bar>x ^ n\<bar>)"
      by (simp add: abs_mult power_mult_distrib power_abs
                    power_inverse mult_assoc)
  qed
  ultimately show "summable (\<lambda>n. \<bar>f n\<bar> * z ^ n)"
    by (rule summable_comparison_test)
qed

lemma powser_inside:
  fixes f :: "nat \<Rightarrow> real" shows
     "[| summable (%n. f(n) * (x ^ n)); \<bar>z\<bar> < \<bar>x\<bar> |]  
      ==> summable (%n. f(n) * (z ^ n))"
apply (drule_tac z = "\<bar>z\<bar>" in powser_insidea, simp)
apply (rule summable_rabs_cancel)
apply (simp add: abs_mult power_abs [symmetric])
done


subsection{*Term-by-Term Differentiability of Power Series*}

definition
  diffs :: "(nat => real) => nat => real" where
  "diffs c = (%n. real (Suc n) * c(Suc n))"

text{*Lemma about distributing negation over it*}
lemma diffs_minus: "diffs (%n. - c n) = (%n. - diffs c n)"
by (simp add: diffs_def)

text{*Show that we can shift the terms down one*}
lemma lemma_diffs:
     "(\<Sum>n=0..<n. (diffs c)(n) * (x ^ n)) =  
      (\<Sum>n=0..<n. real n * c(n) * (x ^ (n - Suc 0))) +  
      (real n * c(n) * x ^ (n - Suc 0))"
apply (induct "n")
apply (auto simp add: mult_assoc add_assoc [symmetric] diffs_def)
done

lemma lemma_diffs2:
     "(\<Sum>n=0..<n. real n * c(n) * (x ^ (n - Suc 0))) =  
      (\<Sum>n=0..<n. (diffs c)(n) * (x ^ n)) -  
      (real n * c(n) * x ^ (n - Suc 0))"
by (auto simp add: lemma_diffs)


lemma diffs_equiv:
     "summable (%n. (diffs c)(n) * (x ^ n)) ==>  
      (%n. real n * c(n) * (x ^ (n - Suc 0))) sums  
         (\<Sum>n. (diffs c)(n) * (x ^ n))"
apply (subgoal_tac " (%n. real n * c (n) * (x ^ (n - Suc 0))) ----> 0")
apply (rule_tac [2] LIMSEQ_imp_Suc)
apply (drule summable_sums) 
apply (auto simp add: sums_def)
apply (drule_tac X="(\<lambda>n. \<Sum>n = 0..<n. diffs c n * x ^ n)" in LIMSEQ_diff)
apply (auto simp add: lemma_diffs2 [symmetric] diffs_def [symmetric])
apply (simp add: diffs_def summable_LIMSEQ_zero)
done

lemma lemma_termdiff1:
  "(\<Sum>p=0..<m. (((z + h) ^ (m - p)) * (z ^ p)) - (z ^ m)) =  
   (\<Sum>p=0..<m. (z ^ p) * (((z + h) ^ (m - p)) - (z ^ (m - p)))::real)"
by (auto simp add: right_distrib diff_minus power_add [symmetric] mult_ac
  cong: strong_setsum_cong)

lemma less_add_one: "m < n ==> (\<exists>d. n = m + d + Suc 0)"
by (simp add: less_iff_Suc_add)

lemma sumdiff: "a + b - (c + d) = a - c + b - (d::real)"
by arith

lemma lemma_termdiff2:
  assumes h: "h \<noteq> 0" shows
  "((z + h) ^ n - z ^ n) / h - real n * z ^ (n - Suc 0) =
   h * (\<Sum>p=0..< n - Suc 0. \<Sum>q=0..< n - Suc 0 - p.
        (z + h) ^ q * z ^ (n - 2 - q))"
apply (rule real_mult_left_cancel [OF h, THEN iffD1])
apply (simp add: right_diff_distrib diff_divide_distrib h)
apply (simp add: mult_assoc [symmetric])
apply (cases "n", simp)
apply (simp add: lemma_realpow_diff_sumr2 h
                 right_diff_distrib [symmetric] mult_assoc
            del: realpow_Suc setsum_op_ivl_Suc)
apply (subst lemma_realpow_rev_sumr)
apply (subst sumr_diff_mult_const)
apply simp
apply (simp only: lemma_termdiff1 setsum_right_distrib)
apply (rule setsum_cong [OF refl])
apply (simp add: diff_minus [symmetric] less_iff_Suc_add)
apply (clarify)
apply (simp add: setsum_right_distrib lemma_realpow_diff_sumr2 mult_ac
            del: setsum_op_ivl_Suc realpow_Suc)
apply (subst mult_assoc [symmetric], subst power_add [symmetric])
apply (simp add: mult_ac)
done

lemma real_setsum_nat_ivl_bounded2:
  "\<lbrakk>\<And>p::nat. p < n \<Longrightarrow> f p \<le> K; 0 \<le> K\<rbrakk>
   \<Longrightarrow> setsum f {0..<n-k} \<le> real n * K"
apply (rule order_trans [OF real_setsum_nat_ivl_bounded mult_right_mono])
apply simp_all
done

lemma lemma_termdiff3:
  assumes 1: "h \<noteq> 0"
  assumes 2: "\<bar>z\<bar> \<le> K"
  assumes 3: "\<bar>z + h\<bar> \<le> K"
  shows "\<bar>((z + h) ^ n - z ^ n) / h - real n * z ^ (n - Suc 0)\<bar>
          \<le> real n * real (n - Suc 0) * K ^ (n - 2) * \<bar>h\<bar>"
proof -
  have "\<bar>((z + h) ^ n - z ^ n) / h - real n * z ^ (n - Suc 0)\<bar> =
        \<bar>\<Sum>p = 0..<n - Suc 0. \<Sum>q = 0..<n - Suc 0 - p.
          (z + h) ^ q * z ^ (n - 2 - q)\<bar> * \<bar>h\<bar>"
    apply (subst lemma_termdiff2 [OF 1])
    apply (subst abs_mult)
    apply (rule mult_commute)
    done
  also have "\<dots> \<le> real n * (real (n - Suc 0) * K ^ (n - 2)) * \<bar>h\<bar>"
  proof (rule mult_right_mono [OF _ abs_ge_zero])
    from abs_ge_zero 2 have K: "0 \<le> K" by (rule order_trans)
    have le_Kn: "\<And>i j n. i + j = n \<Longrightarrow> \<bar>(z + h) ^ i * z ^ j\<bar> \<le> K ^ n"
      apply (erule subst)
      apply (simp only: abs_mult power_abs power_add)
      apply (intro mult_mono power_mono 2 3 abs_ge_zero zero_le_power K)
      done
    show "\<bar>\<Sum>p = 0..<n - Suc 0. \<Sum>q = 0..<n - Suc 0 - p.
              (z + h) ^ q * z ^ (n - 2 - q)\<bar>
          \<le> real n * (real (n - Suc 0) * K ^ (n - 2))"
      apply (intro
         order_trans [OF setsum_abs]
         real_setsum_nat_ivl_bounded2
         mult_nonneg_nonneg
         real_of_nat_ge_zero
         zero_le_power K)
      apply (rule le_Kn, simp)
      done
  qed
  also have "\<dots> = real n * real (n - Suc 0) * K ^ (n - 2) * \<bar>h\<bar>"
    by (simp only: mult_assoc)
  finally show ?thesis .
qed

lemma lemma_termdiff4:
  assumes k: "0 < (k::real)"
  assumes le: "\<And>h. \<lbrakk>h \<noteq> 0; \<bar>h\<bar> < k\<rbrakk> \<Longrightarrow> \<bar>f h\<bar> \<le> K * \<bar>h\<bar>"
  shows "f -- 0 --> 0"
proof (simp add: LIM_def, safe)
  fix r::real assume r: "0 < r"
  have zero_le_K: "0 \<le> K"
    apply (cut_tac k)
    apply (cut_tac h="k/2" in le, simp, simp)
    apply (subgoal_tac "0 \<le> K*k", simp add: zero_le_mult_iff) 
    apply (force intro: order_trans [of _ "\<bar>f (k / 2)\<bar> * 2"]) 
    done
  show "\<exists>s. 0 < s \<and> (\<forall>x. x \<noteq> 0 \<and> \<bar>x\<bar> < s \<longrightarrow> \<bar>f x\<bar> < r)"
  proof (cases)
    assume "K = 0"
    with k r le have "0 < k \<and> (\<forall>x. x \<noteq> 0 \<and> \<bar>x\<bar> < k \<longrightarrow> \<bar>f x\<bar> < r)"
      by simp
    thus "\<exists>s. 0 < s \<and> (\<forall>x. x \<noteq> 0 \<and> \<bar>x\<bar> < s \<longrightarrow> \<bar>f x\<bar> < r)" ..
  next
    assume K_neq_zero: "K \<noteq> 0"
    with zero_le_K have K: "0 < K" by simp
    show "\<exists>s. 0 < s \<and> (\<forall>x. x \<noteq> 0 \<and> \<bar>x\<bar> < s \<longrightarrow> \<bar>f x\<bar> < r)"
    proof (rule exI, safe)
      from k r K show "0 < min k (r * inverse K / 2)"
        by (simp add: mult_pos_pos positive_imp_inverse_positive)
    next
      fix x::real
      assume x1: "x \<noteq> 0" and x2: "\<bar>x\<bar> < min k (r * inverse K / 2)"
      from x2 have x3: "\<bar>x\<bar> < k" and x4: "\<bar>x\<bar> < r * inverse K / 2"
        by simp_all
      from x1 x3 le have "\<bar>f x\<bar> \<le> K * \<bar>x\<bar>" by simp
      also from x4 K have "K * \<bar>x\<bar> < K * (r * inverse K / 2)"
        by (rule mult_strict_left_mono)
      also have "\<dots> = r / 2"
        using K_neq_zero by simp
      also have "r / 2 < r"
        using r by simp
      finally show "\<bar>f x\<bar> < r" .
    qed
  qed
qed

lemma lemma_termdiff5:
  assumes k: "0 < (k::real)"
  assumes f: "summable f"
  assumes le: "\<And>h n. \<lbrakk>h \<noteq> 0; \<bar>h\<bar> < k\<rbrakk> \<Longrightarrow> \<bar>g h n\<bar> \<le> f n * \<bar>h\<bar>"
  shows "(\<lambda>h. suminf (g h)) -- 0 --> 0"
proof (rule lemma_termdiff4 [OF k])
  fix h assume "h \<noteq> 0" and "\<bar>h\<bar> < k"
  hence A: "\<forall>n. \<bar>g h n\<bar> \<le> f n * \<bar>h\<bar>"
    by (simp add: le)
  hence "\<exists>N. \<forall>n\<ge>N. norm \<bar>g h n\<bar> \<le> f n * \<bar>h\<bar>"
    by simp
  moreover from f have B: "summable (\<lambda>n. f n * \<bar>h\<bar>)"
    by (rule summable_mult2)
  ultimately have C: "summable (\<lambda>n. \<bar>g h n\<bar>)"
    by (rule summable_comparison_test)
  hence "\<bar>suminf (g h)\<bar> \<le> (\<Sum>n. \<bar>g h n\<bar>)"
    by (rule summable_rabs)
  also from A C B have "(\<Sum>n. \<bar>g h n\<bar>) \<le> (\<Sum>n. f n * \<bar>h\<bar>)"
    by (rule summable_le)
  also from f have "(\<Sum>n. f n * \<bar>h\<bar>) = suminf f * \<bar>h\<bar>"
    by (rule suminf_mult2 [symmetric])
  finally show "\<bar>suminf (g h)\<bar> \<le> suminf f * \<bar>h\<bar>" .
qed


text{* FIXME: Long proofs*}

lemma termdiffs_aux:
  assumes 1: "summable (\<lambda>n. diffs (diffs c) n * K ^ n)"
  assumes 2: "\<bar>x\<bar> < \<bar>K\<bar>"
  shows "(\<lambda>h. \<Sum>n. c n * (((x + h) ^ n - x ^ n) / h
             - real n * x ^ (n - Suc 0))) -- 0 --> 0"
proof -
  from dense [OF 2]
  obtain r where r1: "\<bar>x\<bar> < r" and r2: "r < \<bar>K\<bar>" by fast
  from abs_ge_zero r1 have r: "0 < r"
    by (rule order_le_less_trans)
  hence r_neq_0: "r \<noteq> 0" by simp
  show ?thesis
  proof (rule lemma_termdiff5)
    show "0 < r - \<bar>x\<bar>" using r1 by simp
  next
    from r r2 have "\<bar>r\<bar> < \<bar>K\<bar>"
      by (simp only: abs_of_nonneg order_less_imp_le)
    with 1 have "summable (\<lambda>n. \<bar>diffs (diffs c) n\<bar> * (r ^ n))"
      by (rule powser_insidea)
    hence "summable (\<lambda>n. diffs (diffs (\<lambda>n. \<bar>c n\<bar>)) n * r ^ n)"
      by (simp only: diffs_def abs_mult abs_real_of_nat_cancel)
    hence "summable (\<lambda>n. real n * diffs (\<lambda>n. \<bar>c n\<bar>) n * r ^ (n - Suc 0))"
      by (rule diffs_equiv [THEN sums_summable])
    also have "(\<lambda>n. real n * diffs (\<lambda>n. \<bar>c n\<bar>) n * r ^ (n - Suc 0))
      = (\<lambda>n. diffs (%m. real (m - Suc 0) * \<bar>c m\<bar> * inverse r) n * (r ^ n))"
      apply (rule ext)
      apply (simp add: diffs_def)
      apply (case_tac n, simp_all add: r_neq_0)
      done
    finally have "summable 
      (\<lambda>n. real n * (real (n - Suc 0) * \<bar>c n\<bar> * inverse r) * r ^ (n - Suc 0))"
      by (rule diffs_equiv [THEN sums_summable])
    also have
      "(\<lambda>n. real n * (real (n - Suc 0) * \<bar>c n\<bar> * inverse r) *
           r ^ (n - Suc 0)) =
       (\<lambda>n. \<bar>c n\<bar> * real n * real (n - Suc 0) * r ^ (n - 2))"
      apply (rule ext)
      apply (case_tac "n", simp)
      apply (case_tac "nat", simp)
      apply (simp add: r_neq_0)
      done
    finally show
      "summable (\<lambda>n. \<bar>c n\<bar> * real n * real (n - Suc 0) * r ^ (n - 2))" .
  next
    fix h::real and n::nat
    assume h: "h \<noteq> 0"
    assume "\<bar>h\<bar> < r - \<bar>x\<bar>"
    hence "\<bar>x\<bar> + \<bar>h\<bar> < r" by simp
    with abs_triangle_ineq have xh: "\<bar>x + h\<bar> < r"
      by (rule order_le_less_trans)
    show "\<bar>c n * (((x + h) ^ n - x ^ n) / h - real n * x ^ (n - Suc 0))\<bar>
          \<le> \<bar>c n\<bar> * real n * real (n - Suc 0) * r ^ (n - 2) * \<bar>h\<bar>"
      apply (simp only: abs_mult mult_assoc)
      apply (rule mult_left_mono [OF _ abs_ge_zero])
      apply (simp (no_asm) add: mult_assoc [symmetric])
      apply (rule lemma_termdiff3)
      apply (rule h)
      apply (rule r1 [THEN order_less_imp_le])
      apply (rule xh [THEN order_less_imp_le])
      done
  qed
qed

lemma termdiffs:
  assumes 1: "summable (\<lambda>n. c n * K ^ n)"
  assumes 2: "summable (\<lambda>n. (diffs c) n * K ^ n)"
  assumes 3: "summable (\<lambda>n. (diffs (diffs c)) n * K ^ n)"
  assumes 4: "\<bar>x\<bar> < \<bar>K\<bar>"
  shows "DERIV (\<lambda>x. \<Sum>n. c n * x ^ n) x :> (\<Sum>n. (diffs c) n * x ^ n)"
proof (simp add: deriv_def, rule LIM_zero_cancel)
  show "(\<lambda>h. (suminf (\<lambda>n. c n * (x + h) ^ n) - suminf (\<lambda>n. c n * x ^ n)) / h
            - suminf (\<lambda>n. diffs c n * x ^ n)) -- 0 --> 0"
  proof (rule LIM_equal2)
    show "0 < \<bar>K\<bar> - \<bar>x\<bar>" by (simp add: less_diff_eq 4)
  next
    fix h :: real
    assume "h \<noteq> 0"
    assume "norm (h - 0) < \<bar>K\<bar> - \<bar>x\<bar>"
    hence "\<bar>x\<bar> + \<bar>h\<bar> < \<bar>K\<bar>" by simp
    hence 5: "\<bar>x + h\<bar> < \<bar>K\<bar>"
      by (rule abs_triangle_ineq [THEN order_le_less_trans])
    have A: "summable (\<lambda>n. c n * x ^ n)"
      by (rule powser_inside [OF 1 4])
    have B: "summable (\<lambda>n. c n * (x + h) ^ n)"
      by (rule powser_inside [OF 1 5])
    have C: "summable (\<lambda>n. diffs c n * x ^ n)"
      by (rule powser_inside [OF 2 4])
    show "((\<Sum>n. c n * (x + h) ^ n) - (\<Sum>n. c n * x ^ n)) / h
             - (\<Sum>n. diffs c n * x ^ n) = 
          (\<Sum>n. c n * (((x + h) ^ n - x ^ n) / h - real n * x ^ (n - Suc 0)))"
      apply (subst sums_unique [OF diffs_equiv [OF C]])
      apply (subst suminf_diff [OF B A])
      apply (subst suminf_divide [symmetric])
      apply (rule summable_diff [OF B A])
      apply (subst suminf_diff)
      apply (rule summable_divide)
      apply (rule summable_diff [OF B A])
      apply (rule sums_summable [OF diffs_equiv [OF C]])
      apply (rule_tac f="suminf" in arg_cong)
      apply (rule ext)
      apply (simp add: ring_eq_simps)
      done
  next
    show "(\<lambda>h. \<Sum>n. c n * (((x + h) ^ n - x ^ n) / h -
               real n * x ^ (n - Suc 0))) -- 0 --> 0"
        by (rule termdiffs_aux [OF 3 4])
  qed
qed


subsection{*Exponential Function*}

definition
  exp :: "real => real" where
  "exp x = (\<Sum>n. inverse(real (fact n)) * (x ^ n))"

definition
  sin :: "real => real" where
  "sin x = (\<Sum>n. (if even(n) then 0 else
             ((- 1) ^ ((n - Suc 0) div 2))/(real (fact n))) * x ^ n)"
 
definition
  cos :: "real => real" where
  "cos x = (\<Sum>n. (if even(n) then ((- 1) ^ (n div 2))/(real (fact n)) 
                            else 0) * x ^ n)"
  
lemma summable_exp: "summable (%n. inverse (real (fact n)) * x ^ n)"
apply (cut_tac 'a = real in zero_less_one [THEN dense], safe)
apply (cut_tac x = r in reals_Archimedean3, auto)
apply (drule_tac x = "\<bar>x\<bar>" in spec, safe)
apply (rule_tac N = n and c = r in ratio_test)
apply (safe, simp add: abs_mult mult_assoc [symmetric] del: fact_Suc)
apply (rule mult_right_mono)
apply (rule_tac b1 = "\<bar>x\<bar>" in mult_commute [THEN ssubst])
apply (subst fact_Suc)
apply (subst real_of_nat_mult)
apply (auto)
apply (simp add: mult_assoc [symmetric] positive_imp_inverse_positive)
apply (rule order_less_imp_le)
apply (rule_tac z1 = "real (Suc na)" in real_mult_less_iff1 [THEN iffD1])
apply (auto simp add: mult_assoc)
apply (erule order_less_trans)
apply (auto simp add: mult_less_cancel_left mult_ac)
done

lemma summable_sin: 
     "summable (%n.  
           (if even n then 0  
           else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) *  
                x ^ n)"
apply (rule_tac g = "(%n. inverse (real (fact n)) * \<bar>x\<bar> ^ n)" in summable_comparison_test)
apply (rule_tac [2] summable_exp)
apply (rule_tac x = 0 in exI)
apply (auto simp add: divide_inverse abs_mult power_abs [symmetric] zero_le_mult_iff)
done

lemma summable_cos: 
      "summable (%n.  
           (if even n then  
           (- 1) ^ (n div 2)/(real (fact n)) else 0) * x ^ n)"
apply (rule_tac g = "(%n. inverse (real (fact n)) * \<bar>x\<bar> ^ n)" in summable_comparison_test)
apply (rule_tac [2] summable_exp)
apply (rule_tac x = 0 in exI)
apply (auto simp add: divide_inverse abs_mult power_abs [symmetric] zero_le_mult_iff)
done

lemma lemma_STAR_sin [simp]:
     "(if even n then 0  
       else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) * 0 ^ n = 0"
by (induct "n", auto)

lemma lemma_STAR_cos [simp]:
     "0 < n -->  
      (- 1) ^ (n div 2)/(real (fact n)) * 0 ^ n = 0"
by (induct "n", auto)

lemma lemma_STAR_cos1 [simp]:
     "0 < n -->  
      (-1) ^ (n div 2)/(real (fact n)) * 0 ^ n = 0"
by (induct "n", auto)

lemma lemma_STAR_cos2 [simp]:
  "(\<Sum>n=1..<n. if even n then (- 1) ^ (n div 2)/(real (fact n)) *  0 ^ n 
                         else 0) = 0"
apply (induct "n")
apply (case_tac [2] "n", auto)
done

lemma exp_converges: "(%n. inverse (real (fact n)) * x ^ n) sums exp(x)"
apply (simp add: exp_def)
apply (rule summable_exp [THEN summable_sums])
done

lemma sin_converges: 
      "(%n. (if even n then 0  
            else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) *  
                 x ^ n) sums sin(x)"
apply (simp add: sin_def)
apply (rule summable_sin [THEN summable_sums])
done

lemma cos_converges: 
      "(%n. (if even n then  
           (- 1) ^ (n div 2)/(real (fact n))  
           else 0) * x ^ n) sums cos(x)"
apply (simp add: cos_def)
apply (rule summable_cos [THEN summable_sums])
done


subsection{*Formal Derivatives of Exp, Sin, and Cos Series*} 

lemma exp_fdiffs: 
      "diffs (%n. inverse(real (fact n))) = (%n. inverse(real (fact n)))"
by (simp add: diffs_def mult_assoc [symmetric] del: mult_Suc)

lemma sin_fdiffs: 
      "diffs(%n. if even n then 0  
           else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n)))  
       = (%n. if even n then  
                 (- 1) ^ (n div 2)/(real (fact n))  
              else 0)"
by (auto intro!: ext 
         simp add: diffs_def divide_inverse simp del: mult_Suc)

lemma sin_fdiffs2: 
       "diffs(%n. if even n then 0  
           else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) n  
       = (if even n then  
                 (- 1) ^ (n div 2)/(real (fact n))  
              else 0)"
by (auto intro!: ext 
         simp add: diffs_def divide_inverse simp del: mult_Suc)

lemma cos_fdiffs: 
      "diffs(%n. if even n then  
                 (- 1) ^ (n div 2)/(real (fact n)) else 0)  
       = (%n. - (if even n then 0  
           else (- 1) ^ ((n - Suc 0)div 2)/(real (fact n))))"
by (auto intro!: ext 
         simp add: diffs_def divide_inverse odd_Suc_mult_two_ex
         simp del: mult_Suc)


lemma cos_fdiffs2: 
      "diffs(%n. if even n then  
                 (- 1) ^ (n div 2)/(real (fact n)) else 0) n 
       = - (if even n then 0  
           else (- 1) ^ ((n - Suc 0)div 2)/(real (fact n)))"
by (auto intro!: ext 
         simp add: diffs_def divide_inverse odd_Suc_mult_two_ex
         simp del: mult_Suc)

text{*Now at last we can get the derivatives of exp, sin and cos*}

lemma lemma_sin_minus:
     "- sin x = (\<Sum>n. - ((if even n then 0 
                  else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) * x ^ n))"
by (auto intro!: sums_unique sums_minus sin_converges)

lemma lemma_exp_ext: "exp = (%x. \<Sum>n. inverse (real (fact n)) * x ^ n)"
by (auto intro!: ext simp add: exp_def)

lemma DERIV_exp [simp]: "DERIV exp x :> exp(x)"
apply (simp add: exp_def)
apply (subst lemma_exp_ext)
apply (subgoal_tac "DERIV (%u. \<Sum>n. inverse (real (fact n)) * u ^ n) x :> (\<Sum>n. diffs (%n. inverse (real (fact n))) n * x ^ n)")
apply (rule_tac [2] K = "1 + \<bar>x\<bar>" in termdiffs)
apply (auto intro: exp_converges [THEN sums_summable] simp add: exp_fdiffs)
done

lemma lemma_sin_ext:
     "sin = (%x. \<Sum>n. 
                   (if even n then 0  
                       else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) *  
                   x ^ n)"
by (auto intro!: ext simp add: sin_def)

lemma lemma_cos_ext:
     "cos = (%x. \<Sum>n. 
                   (if even n then (- 1) ^ (n div 2)/(real (fact n)) else 0) *
                   x ^ n)"
by (auto intro!: ext simp add: cos_def)

lemma DERIV_sin [simp]: "DERIV sin x :> cos(x)"
apply (simp add: cos_def)
apply (subst lemma_sin_ext)
apply (auto simp add: sin_fdiffs2 [symmetric])
apply (rule_tac K = "1 + \<bar>x\<bar>" in termdiffs)
apply (auto intro: sin_converges cos_converges sums_summable intro!: sums_minus [THEN sums_summable] simp add: cos_fdiffs sin_fdiffs)
done

lemma DERIV_cos [simp]: "DERIV cos x :> -sin(x)"
apply (subst lemma_cos_ext)
apply (auto simp add: lemma_sin_minus cos_fdiffs2 [symmetric] minus_mult_left)
apply (rule_tac K = "1 + \<bar>x\<bar>" in termdiffs)
apply (auto intro: sin_converges cos_converges sums_summable intro!: sums_minus [THEN sums_summable] simp add: cos_fdiffs sin_fdiffs diffs_minus)
done

lemma isCont_exp [simp]: "isCont exp x"
by (rule DERIV_exp [THEN DERIV_isCont])

lemma isCont_sin [simp]: "isCont sin x"
by (rule DERIV_sin [THEN DERIV_isCont])

lemma isCont_cos [simp]: "isCont cos x"
by (rule DERIV_cos [THEN DERIV_isCont])


subsection{*Properties of the Exponential Function*}

lemma exp_zero [simp]: "exp 0 = 1"
proof -
  have "(\<Sum>n = 0..<1. inverse (real (fact n)) * 0 ^ n) =
        (\<Sum>n. inverse (real (fact n)) * 0 ^ n)"
    by (rule series_zero [rule_format, THEN sums_unique],
        case_tac "m", auto)
  thus ?thesis by (simp add:  exp_def) 
qed

lemma exp_ge_add_one_self_aux: "0 \<le> x ==> (1 + x) \<le> exp(x)"
apply (drule order_le_imp_less_or_eq, auto)
apply (simp add: exp_def)
apply (rule real_le_trans)
apply (rule_tac [2] n = 2 and f = "(%n. inverse (real (fact n)) * x ^ n)" in series_pos_le)
apply (auto intro: summable_exp simp add: numeral_2_eq_2 zero_le_power zero_le_mult_iff)
done

lemma exp_gt_one [simp]: "0 < x ==> 1 < exp x"
apply (rule order_less_le_trans)
apply (rule_tac [2] exp_ge_add_one_self_aux, auto)
done

lemma DERIV_exp_add_const: "DERIV (%x. exp (x + y)) x :> exp(x + y)"
proof -
  have "DERIV (exp \<circ> (\<lambda>x. x + y)) x :> exp (x + y) * (1+0)"
    by (fast intro: DERIV_chain DERIV_add DERIV_exp DERIV_Id DERIV_const) 
  thus ?thesis by (simp add: o_def)
qed

lemma DERIV_exp_minus [simp]: "DERIV (%x. exp (-x)) x :> - exp(-x)"
proof -
  have "DERIV (exp \<circ> uminus) x :> exp (- x) * - 1"
    by (fast intro: DERIV_chain DERIV_minus DERIV_exp DERIV_Id) 
  thus ?thesis by (simp add: o_def)
qed

lemma DERIV_exp_exp_zero [simp]: "DERIV (%x. exp (x + y) * exp (- x)) x :> 0"
proof -
  have "DERIV (\<lambda>x. exp (x + y) * exp (- x)) x
       :> exp (x + y) * exp (- x) + - exp (- x) * exp (x + y)"
    by (fast intro: DERIV_exp_add_const DERIV_exp_minus DERIV_mult) 
  thus ?thesis by simp
qed

lemma exp_add_mult_minus [simp]: "exp(x + y)*exp(-x) = exp(y)"
proof -
  have "\<forall>x. DERIV (%x. exp (x + y) * exp (- x)) x :> 0" by simp
  hence "exp (x + y) * exp (- x) = exp (0 + y) * exp (- 0)" 
    by (rule DERIV_isconst_all) 
  thus ?thesis by simp
qed

lemma exp_mult_minus [simp]: "exp x * exp(-x) = 1"
proof -
  have "exp (x + 0) * exp (- x) = exp 0" by (rule exp_add_mult_minus) 
  thus ?thesis by simp
qed

lemma exp_mult_minus2 [simp]: "exp(-x)*exp(x) = 1"
by (simp add: mult_commute)


lemma exp_minus: "exp(-x) = inverse(exp(x))"
by (auto intro: inverse_unique [symmetric])

lemma exp_add: "exp(x + y) = exp(x) * exp(y)"
proof -
  have "exp x * exp y = exp x * (exp (x + y) * exp (- x))" by simp
  thus ?thesis by (simp (no_asm_simp) add: mult_ac)
qed

text{*Proof: because every exponential can be seen as a square.*}
lemma exp_ge_zero [simp]: "0 \<le> exp x"
apply (rule_tac t = x in real_sum_of_halves [THEN subst])
apply (subst exp_add, auto)
done

lemma exp_not_eq_zero [simp]: "exp x \<noteq> 0"
apply (cut_tac x = x in exp_mult_minus2)
apply (auto simp del: exp_mult_minus2)
done

lemma exp_gt_zero [simp]: "0 < exp x"
by (simp add: order_less_le)

lemma inv_exp_gt_zero [simp]: "0 < inverse(exp x)"
by (auto intro: positive_imp_inverse_positive)

lemma abs_exp_cancel [simp]: "\<bar>exp x\<bar> = exp x"
by auto

lemma exp_real_of_nat_mult: "exp(real n * x) = exp(x) ^ n"
apply (induct "n")
apply (auto simp add: real_of_nat_Suc right_distrib exp_add mult_commute)
done

lemma exp_diff: "exp(x - y) = exp(x)/(exp y)"
apply (simp add: diff_minus divide_inverse)
apply (simp (no_asm) add: exp_add exp_minus)
done


lemma exp_less_mono:
  assumes xy: "x < y" shows "exp x < exp y"
proof -
  have "1 < exp (y + - x)"
    by (rule real_less_sum_gt_zero [THEN exp_gt_one])
  hence "exp x * inverse (exp x) < exp y * inverse (exp x)"
    by (auto simp add: exp_add exp_minus)
  thus ?thesis
    by (simp add: divide_inverse [symmetric] pos_less_divide_eq
             del: divide_self_if)
qed

lemma exp_less_cancel: "exp x < exp y ==> x < y"
apply (simp add: linorder_not_le [symmetric]) 
apply (auto simp add: order_le_less exp_less_mono) 
done

lemma exp_less_cancel_iff [iff]: "(exp(x) < exp(y)) = (x < y)"
by (auto intro: exp_less_mono exp_less_cancel)

lemma exp_le_cancel_iff [iff]: "(exp(x) \<le> exp(y)) = (x \<le> y)"
by (auto simp add: linorder_not_less [symmetric])

lemma exp_inj_iff [iff]: "(exp x = exp y) = (x = y)"
by (simp add: order_eq_iff)

lemma lemma_exp_total: "1 \<le> y ==> \<exists>x. 0 \<le> x & x \<le> y - 1 & exp(x) = y"
apply (rule IVT)
apply (auto intro: isCont_exp simp add: le_diff_eq)
apply (subgoal_tac "1 + (y - 1) \<le> exp (y - 1)") 
apply simp 
apply (rule exp_ge_add_one_self_aux, simp)
done

lemma exp_total: "0 < y ==> \<exists>x. exp x = y"
apply (rule_tac x = 1 and y = y in linorder_cases)
apply (drule order_less_imp_le [THEN lemma_exp_total])
apply (rule_tac [2] x = 0 in exI)
apply (frule_tac [3] real_inverse_gt_one)
apply (drule_tac [4] order_less_imp_le [THEN lemma_exp_total], auto)
apply (rule_tac x = "-x" in exI)
apply (simp add: exp_minus)
done


subsection{*Properties of the Logarithmic Function*}

definition
  ln :: "real => real" where
  "ln x = (THE u. exp u = x)"

lemma ln_exp [simp]: "ln (exp x) = x"
by (simp add: ln_def)

lemma exp_ln [simp]: "0 < x \<Longrightarrow> exp (ln x) = x"
by (auto dest: exp_total)

lemma exp_ln_iff [simp]: "(exp (ln x) = x) = (0 < x)"
apply (auto dest: exp_total)
apply (erule subst, simp) 
done

lemma ln_mult: "[| 0 < x; 0 < y |] ==> ln(x * y) = ln(x) + ln(y)"
apply (rule exp_inj_iff [THEN iffD1])
apply (simp add: exp_add exp_ln mult_pos_pos)
done

lemma ln_inj_iff[simp]: "[| 0 < x; 0 < y |] ==> (ln x = ln y) = (x = y)"
apply (simp only: exp_ln_iff [symmetric])
apply (erule subst)+
apply simp 
done

lemma ln_one[simp]: "ln 1 = 0"
by (rule exp_inj_iff [THEN iffD1], auto)

lemma ln_inverse: "0 < x ==> ln(inverse x) = - ln x"
apply (rule_tac a1 = "ln x" in add_left_cancel [THEN iffD1])
apply (auto simp add: positive_imp_inverse_positive ln_mult [symmetric])
done

lemma ln_div: 
    "[|0 < x; 0 < y|] ==> ln(x/y) = ln x - ln y"
apply (simp add: divide_inverse)
apply (auto simp add: positive_imp_inverse_positive ln_mult ln_inverse)
done

lemma ln_less_cancel_iff[simp]: "[| 0 < x; 0 < y|] ==> (ln x < ln y) = (x < y)"
apply (simp only: exp_ln_iff [symmetric])
apply (erule subst)+
apply simp 
done

lemma ln_le_cancel_iff[simp]: "[| 0 < x; 0 < y|] ==> (ln x \<le> ln y) = (x \<le> y)"
by (auto simp add: linorder_not_less [symmetric])

lemma ln_realpow: "0 < x ==> ln(x ^ n) = real n * ln(x)"
by (auto dest!: exp_total simp add: exp_real_of_nat_mult [symmetric])

lemma ln_add_one_self_le_self [simp]: "0 \<le> x ==> ln(1 + x) \<le> x"
apply (rule ln_exp [THEN subst])
apply (rule ln_le_cancel_iff [THEN iffD2]) 
apply (auto simp add: exp_ge_add_one_self_aux)
done

lemma ln_less_self [simp]: "0 < x ==> ln x < x"
apply (rule order_less_le_trans)
apply (rule_tac [2] ln_add_one_self_le_self)
apply (rule ln_less_cancel_iff [THEN iffD2], auto)
done

lemma ln_ge_zero [simp]:
  assumes x: "1 \<le> x" shows "0 \<le> ln x"
proof -
  have "0 < x" using x by arith
  hence "exp 0 \<le> exp (ln x)"
    by (simp add: x)
  thus ?thesis by (simp only: exp_le_cancel_iff)
qed

lemma ln_ge_zero_imp_ge_one:
  assumes ln: "0 \<le> ln x" 
      and x:  "0 < x"
  shows "1 \<le> x"
proof -
  from ln have "ln 1 \<le> ln x" by simp
  thus ?thesis by (simp add: x del: ln_one) 
qed

lemma ln_ge_zero_iff [simp]: "0 < x ==> (0 \<le> ln x) = (1 \<le> x)"
by (blast intro: ln_ge_zero ln_ge_zero_imp_ge_one)

lemma ln_less_zero_iff [simp]: "0 < x ==> (ln x < 0) = (x < 1)"
by (insert ln_ge_zero_iff [of x], arith)

lemma ln_gt_zero:
  assumes x: "1 < x" shows "0 < ln x"
proof -
  have "0 < x" using x by arith
  hence "exp 0 < exp (ln x)" by (simp add: x)
  thus ?thesis  by (simp only: exp_less_cancel_iff)
qed

lemma ln_gt_zero_imp_gt_one:
  assumes ln: "0 < ln x" 
      and x:  "0 < x"
  shows "1 < x"
proof -
  from ln have "ln 1 < ln x" by simp
  thus ?thesis by (simp add: x del: ln_one) 
qed

lemma ln_gt_zero_iff [simp]: "0 < x ==> (0 < ln x) = (1 < x)"
by (blast intro: ln_gt_zero ln_gt_zero_imp_gt_one)

lemma ln_eq_zero_iff [simp]: "0 < x ==> (ln x = 0) = (x = 1)"
by (insert ln_less_zero_iff [of x] ln_gt_zero_iff [of x], arith)

lemma ln_less_zero: "[| 0 < x; x < 1 |] ==> ln x < 0"
by simp

lemma exp_ln_eq: "exp u = x ==> ln x = u"
by auto

lemma isCont_ln: "0 < x \<Longrightarrow> isCont ln x"
apply (subgoal_tac "isCont ln (exp (ln x))", simp)
apply (rule isCont_inverse_function [where f=exp], simp_all)
done

lemma lemma_DERIV_subst: "[| DERIV f x :> D; D = E |] ==> DERIV f x :> E"
by simp (* TODO: put in Deriv.thy *)

lemma DERIV_ln: "0 < x \<Longrightarrow> DERIV ln x :> inverse x"
apply (rule DERIV_inverse_function [where f=exp and a=0 and b="x+1"])
apply (erule lemma_DERIV_subst [OF DERIV_exp exp_ln])
apply (simp_all add: abs_if isCont_ln)
done


subsection{*Basic Properties of the Trigonometric Functions*}

lemma sin_zero [simp]: "sin 0 = 0"
by (auto intro!: sums_unique [symmetric] LIMSEQ_const 
         simp add: sin_def sums_def simp del: power_0_left)

lemma lemma_series_zero2:
 "(\<forall>m. n \<le> m --> f m = 0) --> f sums setsum f {0..<n}"
by (auto intro: series_zero)

lemma cos_zero [simp]: "cos 0 = 1"
apply (simp add: cos_def)
apply (rule sums_unique [symmetric])
apply (cut_tac n = 1 and f = "(%n. (if even n then (- 1) ^ (n div 2) / (real (fact n)) else 0) * 0 ^ n)" in lemma_series_zero2)
apply auto
done

lemma DERIV_sin_sin_mult [simp]:
     "DERIV (%x. sin(x)*sin(x)) x :> cos(x) * sin(x) + cos(x) * sin(x)"
by (rule DERIV_mult, auto)

lemma DERIV_sin_sin_mult2 [simp]:
     "DERIV (%x. sin(x)*sin(x)) x :> 2 * cos(x) * sin(x)"
apply (cut_tac x = x in DERIV_sin_sin_mult)
apply (auto simp add: mult_assoc)
done

lemma DERIV_sin_realpow2 [simp]:
     "DERIV (%x. (sin x)\<twosuperior>) x :> cos(x) * sin(x) + cos(x) * sin(x)"
by (auto simp add: numeral_2_eq_2 real_mult_assoc [symmetric])

lemma DERIV_sin_realpow2a [simp]:
     "DERIV (%x. (sin x)\<twosuperior>) x :> 2 * cos(x) * sin(x)"
by (auto simp add: numeral_2_eq_2)

lemma DERIV_cos_cos_mult [simp]:
     "DERIV (%x. cos(x)*cos(x)) x :> -sin(x) * cos(x) + -sin(x) * cos(x)"
by (rule DERIV_mult, auto)

lemma DERIV_cos_cos_mult2 [simp]:
     "DERIV (%x. cos(x)*cos(x)) x :> -2 * cos(x) * sin(x)"
apply (cut_tac x = x in DERIV_cos_cos_mult)
apply (auto simp add: mult_ac)
done

lemma DERIV_cos_realpow2 [simp]:
     "DERIV (%x. (cos x)\<twosuperior>) x :> -sin(x) * cos(x) + -sin(x) * cos(x)"
by (auto simp add: numeral_2_eq_2 real_mult_assoc [symmetric])

lemma DERIV_cos_realpow2a [simp]:
     "DERIV (%x. (cos x)\<twosuperior>) x :> -2 * cos(x) * sin(x)"
by (auto simp add: numeral_2_eq_2)

lemma lemma_DERIV_subst: "[| DERIV f x :> D; D = E |] ==> DERIV f x :> E"
by auto

lemma DERIV_cos_realpow2b: "DERIV (%x. (cos x)\<twosuperior>) x :> -(2 * cos(x) * sin(x))"
apply (rule lemma_DERIV_subst)
apply (rule DERIV_cos_realpow2a, auto)
done

(* most useful *)
lemma DERIV_cos_cos_mult3 [simp]:
     "DERIV (%x. cos(x)*cos(x)) x :> -(2 * cos(x) * sin(x))"
apply (rule lemma_DERIV_subst)
apply (rule DERIV_cos_cos_mult2, auto)
done

lemma DERIV_sin_circle_all: 
     "\<forall>x. DERIV (%x. (sin x)\<twosuperior> + (cos x)\<twosuperior>) x :>  
             (2*cos(x)*sin(x) - 2*cos(x)*sin(x))"
apply (simp only: diff_minus, safe)
apply (rule DERIV_add) 
apply (auto simp add: numeral_2_eq_2)
done

lemma DERIV_sin_circle_all_zero [simp]:
     "\<forall>x. DERIV (%x. (sin x)\<twosuperior> + (cos x)\<twosuperior>) x :> 0"
by (cut_tac DERIV_sin_circle_all, auto)

lemma sin_cos_squared_add [simp]: "((sin x)\<twosuperior>) + ((cos x)\<twosuperior>) = 1"
apply (cut_tac x = x and y = 0 in DERIV_sin_circle_all_zero [THEN DERIV_isconst_all])
apply (auto simp add: numeral_2_eq_2)
done

lemma sin_cos_squared_add2 [simp]: "((cos x)\<twosuperior>) + ((sin x)\<twosuperior>) = 1"
apply (subst real_add_commute)
apply (simp (no_asm) del: realpow_Suc)
done

lemma sin_cos_squared_add3 [simp]: "cos x * cos x + sin x * sin x = 1"
apply (cut_tac x = x in sin_cos_squared_add2)
apply (auto simp add: numeral_2_eq_2)
done

lemma sin_squared_eq: "(sin x)\<twosuperior> = 1 - (cos x)\<twosuperior>"
apply (rule_tac a1 = "(cos x)\<twosuperior>" in add_right_cancel [THEN iffD1])
apply (simp del: realpow_Suc)
done

lemma cos_squared_eq: "(cos x)\<twosuperior> = 1 - (sin x)\<twosuperior>"
apply (rule_tac a1 = "(sin x)\<twosuperior>" in add_right_cancel [THEN iffD1])
apply (simp del: realpow_Suc)
done

lemma real_gt_one_ge_zero_add_less: "[| 1 < x; 0 \<le> y |] ==> 1 < x + (y::real)"
by arith

lemma abs_sin_le_one [simp]: "\<bar>sin x\<bar> \<le> 1"
apply (auto simp add: linorder_not_less [symmetric])
apply (drule_tac n = "Suc 0" in power_gt1)
apply (auto simp del: realpow_Suc)
apply (drule_tac r1 = "cos x" in realpow_two_le [THEN [2] real_gt_one_ge_zero_add_less])
apply (simp add: numeral_2_eq_2 [symmetric] del: realpow_Suc)
done

lemma sin_ge_minus_one [simp]: "-1 \<le> sin x"
apply (insert abs_sin_le_one [of x]) 
apply (simp add: abs_le_iff del: abs_sin_le_one) 
done

lemma sin_le_one [simp]: "sin x \<le> 1"
apply (insert abs_sin_le_one [of x]) 
apply (simp add: abs_le_iff del: abs_sin_le_one) 
done

lemma abs_cos_le_one [simp]: "\<bar>cos x\<bar> \<le> 1"
apply (auto simp add: linorder_not_less [symmetric])
apply (drule_tac n = "Suc 0" in power_gt1)
apply (auto simp del: realpow_Suc)
apply (drule_tac r1 = "sin x" in realpow_two_le [THEN [2] real_gt_one_ge_zero_add_less])
apply (simp add: numeral_2_eq_2 [symmetric] del: realpow_Suc)
done

lemma cos_ge_minus_one [simp]: "-1 \<le> cos x"
apply (insert abs_cos_le_one [of x]) 
apply (simp add: abs_le_iff del: abs_cos_le_one) 
done

lemma cos_le_one [simp]: "cos x \<le> 1"
apply (insert abs_cos_le_one [of x]) 
apply (simp add: abs_le_iff del: abs_cos_le_one)
done

lemma DERIV_fun_pow: "DERIV g x :> m ==>  
      DERIV (%x. (g x) ^ n) x :> real n * (g x) ^ (n - 1) * m"
apply (rule lemma_DERIV_subst)
apply (rule_tac f = "(%x. x ^ n)" in DERIV_chain2)
apply (rule DERIV_pow, auto)
done

lemma DERIV_fun_exp:
     "DERIV g x :> m ==> DERIV (%x. exp(g x)) x :> exp(g x) * m"
apply (rule lemma_DERIV_subst)
apply (rule_tac f = exp in DERIV_chain2)
apply (rule DERIV_exp, auto)
done

lemma DERIV_fun_sin:
     "DERIV g x :> m ==> DERIV (%x. sin(g x)) x :> cos(g x) * m"
apply (rule lemma_DERIV_subst)
apply (rule_tac f = sin in DERIV_chain2)
apply (rule DERIV_sin, auto)
done

lemma DERIV_fun_cos:
     "DERIV g x :> m ==> DERIV (%x. cos(g x)) x :> -sin(g x) * m"
apply (rule lemma_DERIV_subst)
apply (rule_tac f = cos in DERIV_chain2)
apply (rule DERIV_cos, auto)
done

lemmas DERIV_intros = DERIV_Id DERIV_const DERIV_cos DERIV_cmult 
                    DERIV_sin  DERIV_exp  DERIV_inverse DERIV_pow 
                    DERIV_add  DERIV_diff  DERIV_mult  DERIV_minus 
                    DERIV_inverse_fun DERIV_quotient DERIV_fun_pow 
                    DERIV_fun_exp DERIV_fun_sin DERIV_fun_cos 

(* lemma *)
lemma lemma_DERIV_sin_cos_add:
     "\<forall>x.  
         DERIV (%x. (sin (x + y) - (sin x * cos y + cos x * sin y)) ^ 2 +  
               (cos (x + y) - (cos x * cos y - sin x * sin y)) ^ 2) x :> 0"
apply (safe, rule lemma_DERIV_subst)
apply (best intro!: DERIV_intros intro: DERIV_chain2) 
  --{*replaces the old @{text DERIV_tac}*}
apply (auto simp add: diff_minus left_distrib right_distrib mult_ac add_ac)
done

lemma sin_cos_add [simp]:
     "(sin (x + y) - (sin x * cos y + cos x * sin y)) ^ 2 +  
      (cos (x + y) - (cos x * cos y - sin x * sin y)) ^ 2 = 0"
apply (cut_tac y = 0 and x = x and y7 = y 
       in lemma_DERIV_sin_cos_add [THEN DERIV_isconst_all])
apply (auto simp add: numeral_2_eq_2)
done

lemma sin_add: "sin (x + y) = sin x * cos y + cos x * sin y"
apply (cut_tac x = x and y = y in sin_cos_add)
apply (simp del: sin_cos_add)
done

lemma cos_add: "cos (x + y) = cos x * cos y - sin x * sin y"
apply (cut_tac x = x and y = y in sin_cos_add)
apply (simp del: sin_cos_add)
done

lemma lemma_DERIV_sin_cos_minus:
    "\<forall>x. DERIV (%x. (sin(-x) + (sin x)) ^ 2 + (cos(-x) - (cos x)) ^ 2) x :> 0"
apply (safe, rule lemma_DERIV_subst)
apply (best intro!: DERIV_intros intro: DERIV_chain2) 
apply (auto simp add: diff_minus left_distrib right_distrib mult_ac add_ac)
done

lemma sin_cos_minus [simp]: 
    "(sin(-x) + (sin x)) ^ 2 + (cos(-x) - (cos x)) ^ 2 = 0"
apply (cut_tac y = 0 and x = x 
       in lemma_DERIV_sin_cos_minus [THEN DERIV_isconst_all])
apply simp
done

lemma sin_minus [simp]: "sin (-x) = -sin(x)"
apply (cut_tac x = x in sin_cos_minus)
apply (simp del: sin_cos_minus)
done

lemma cos_minus [simp]: "cos (-x) = cos(x)"
apply (cut_tac x = x in sin_cos_minus)
apply (simp del: sin_cos_minus)
done

lemma sin_diff: "sin (x - y) = sin x * cos y - cos x * sin y"
by (simp add: diff_minus sin_add)

lemma sin_diff2: "sin (x - y) = cos y * sin x - sin y * cos x"
by (simp add: sin_diff mult_commute)

lemma cos_diff: "cos (x - y) = cos x * cos y + sin x * sin y"
by (simp add: diff_minus cos_add)

lemma cos_diff2: "cos (x - y) = cos y * cos x + sin y * sin x"
by (simp add: cos_diff mult_commute)

lemma sin_double [simp]: "sin(2 * x) = 2* sin x * cos x"
by (cut_tac x = x and y = x in sin_add, auto)


lemma cos_double: "cos(2* x) = ((cos x)\<twosuperior>) - ((sin x)\<twosuperior>)"
apply (cut_tac x = x and y = x in cos_add)
apply (simp add: power2_eq_square)
done


subsection{*The Constant Pi*}

definition
  pi :: "real" where
  "pi = 2 * (THE x. 0 \<le> (x::real) & x \<le> 2 & cos x = 0)"

text{*Show that there's a least positive @{term x} with @{term "cos(x) = 0"}; 
   hence define pi.*}

lemma sin_paired:
     "(%n. (- 1) ^ n /(real (fact (2 * n + 1))) * x ^ (2 * n + 1)) 
      sums  sin x"
proof -
  have "(\<lambda>n. \<Sum>k = n * 2..<n * 2 + 2.
            (if even k then 0
             else (- 1) ^ ((k - Suc 0) div 2) / real (fact k)) *
            x ^ k) 
	sums
	(\<Sum>n. (if even n then 0
		     else (- 1) ^ ((n - Suc 0) div 2) / real (fact n)) *
	            x ^ n)" 
    by (rule sin_converges [THEN sums_summable, THEN sums_group], simp) 
  thus ?thesis by (simp add: mult_ac sin_def)
qed

lemma sin_gt_zero: "[|0 < x; x < 2 |] ==> 0 < sin x"
apply (subgoal_tac 
       "(\<lambda>n. \<Sum>k = n * 2..<n * 2 + 2.
              (- 1) ^ k / real (fact (2 * k + 1)) * x ^ (2 * k + 1)) 
     sums (\<Sum>n. (- 1) ^ n / real (fact (2 * n + 1)) * x ^ (2 * n + 1))")
 prefer 2
 apply (rule sin_paired [THEN sums_summable, THEN sums_group], simp) 
apply (rotate_tac 2)
apply (drule sin_paired [THEN sums_unique, THEN ssubst])
apply (auto simp del: fact_Suc realpow_Suc)
apply (frule sums_unique)
apply (auto simp del: fact_Suc realpow_Suc)
apply (rule_tac n1 = 0 in series_pos_less [THEN [2] order_le_less_trans])
apply (auto simp del: fact_Suc realpow_Suc)
apply (erule sums_summable)
apply (case_tac "m=0")
apply (simp (no_asm_simp))
apply (subgoal_tac "6 * (x * (x * x) / real (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) < 6 * x") 
apply (simp only: mult_less_cancel_left, simp)  
apply (simp (no_asm_simp) add: numeral_2_eq_2 [symmetric] mult_assoc [symmetric])
apply (subgoal_tac "x*x < 2*3", simp) 
apply (rule mult_strict_mono)
apply (auto simp add: real_0_less_add_iff real_of_nat_Suc simp del: fact_Suc)
apply (subst fact_Suc)
apply (subst fact_Suc)
apply (subst fact_Suc)
apply (subst fact_Suc)
apply (subst real_of_nat_mult)
apply (subst real_of_nat_mult)
apply (subst real_of_nat_mult)
apply (subst real_of_nat_mult)
apply (simp (no_asm) add: divide_inverse del: fact_Suc)
apply (auto simp add: mult_assoc [symmetric] simp del: fact_Suc)
apply (rule_tac c="real (Suc (Suc (4*m)))" in mult_less_imp_less_right) 
apply (auto simp add: mult_assoc simp del: fact_Suc)
apply (rule_tac c="real (Suc (Suc (Suc (4*m))))" in mult_less_imp_less_right) 
apply (auto simp add: mult_assoc mult_less_cancel_left simp del: fact_Suc)
apply (subgoal_tac "x * (x * x ^ (4*m)) = (x ^ (4*m)) * (x * x)") 
apply (erule ssubst)+
apply (auto simp del: fact_Suc)
apply (subgoal_tac "0 < x ^ (4 * m) ")
 prefer 2 apply (simp only: zero_less_power) 
apply (simp (no_asm_simp) add: mult_less_cancel_left)
apply (rule mult_strict_mono)
apply (simp_all (no_asm_simp))
done

lemma sin_gt_zero1: "[|0 < x; x < 2 |] ==> 0 < sin x"
by (auto intro: sin_gt_zero)

lemma cos_double_less_one: "[| 0 < x; x < 2 |] ==> cos (2 * x) < 1"
apply (cut_tac x = x in sin_gt_zero1)
apply (auto simp add: cos_squared_eq cos_double)
done

lemma cos_paired:
     "(%n. (- 1) ^ n /(real (fact (2 * n))) * x ^ (2 * n)) sums cos x"
proof -
  have "(\<lambda>n. \<Sum>k = n * 2..<n * 2 + 2.
            (if even k then (- 1) ^ (k div 2) / real (fact k) else 0) *
            x ^ k) 
        sums
	(\<Sum>n. (if even n then (- 1) ^ (n div 2) / real (fact n) else 0) *
	      x ^ n)" 
    by (rule cos_converges [THEN sums_summable, THEN sums_group], simp) 
  thus ?thesis by (simp add: mult_ac cos_def)
qed

declare zero_less_power [simp]

lemma fact_lemma: "real (n::nat) * 4 = real (4 * n)"
by simp

lemma cos_two_less_zero [simp]: "cos (2) < 0"
apply (cut_tac x = 2 in cos_paired)
apply (drule sums_minus)
apply (rule neg_less_iff_less [THEN iffD1]) 
apply (frule sums_unique, auto)
apply (rule_tac y =
 "\<Sum>n=0..< Suc(Suc(Suc 0)). - ((- 1) ^ n / (real(fact (2*n))) * 2 ^ (2*n))"
       in order_less_trans)
apply (simp (no_asm) add: fact_num_eq_if realpow_num_eq_if del: fact_Suc realpow_Suc)
apply (simp (no_asm) add: mult_assoc del: setsum_op_ivl_Suc)
apply (rule sumr_pos_lt_pair)
apply (erule sums_summable, safe)
apply (simp (no_asm) add: divide_inverse real_0_less_add_iff mult_assoc [symmetric] 
            del: fact_Suc)
apply (rule real_mult_inverse_cancel2)
apply (rule real_of_nat_fact_gt_zero)+
apply (simp (no_asm) add: mult_assoc [symmetric] del: fact_Suc)
apply (subst fact_lemma) 
apply (subst fact_Suc [of "Suc (Suc (Suc (Suc (Suc (Suc (Suc (4 * d)))))))"])
apply (simp only: real_of_nat_mult)
apply (rule mult_strict_mono, force)
  apply (rule_tac [3] real_of_nat_fact_ge_zero)
 prefer 2 apply force
apply (rule real_of_nat_less_iff [THEN iffD2])
apply (rule fact_less_mono, auto)
done

lemmas cos_two_neq_zero [simp] = cos_two_less_zero [THEN less_imp_neq]
lemmas cos_two_le_zero [simp] = cos_two_less_zero [THEN order_less_imp_le]

lemma cos_is_zero: "EX! x. 0 \<le> x & x \<le> 2 & cos x = 0"
apply (subgoal_tac "\<exists>x. 0 \<le> x & x \<le> 2 & cos x = 0")
apply (rule_tac [2] IVT2)
apply (auto intro: DERIV_isCont DERIV_cos)
apply (cut_tac x = xa and y = y in linorder_less_linear)
apply (rule ccontr)
apply (subgoal_tac " (\<forall>x. cos differentiable x) & (\<forall>x. isCont cos x) ")
apply (auto intro: DERIV_cos DERIV_isCont simp add: differentiable_def)
apply (drule_tac f = cos in Rolle)
apply (drule_tac [5] f = cos in Rolle)
apply (auto dest!: DERIV_cos [THEN DERIV_unique] simp add: differentiable_def)
apply (drule_tac y1 = xa in order_le_less_trans [THEN sin_gt_zero])
apply (assumption, rule_tac y=y in order_less_le_trans, simp_all) 
apply (drule_tac y1 = y in order_le_less_trans [THEN sin_gt_zero], assumption, simp_all) 
done
    
lemma pi_half: "pi/2 = (THE x. 0 \<le> x & x \<le> 2 & cos x = 0)"
by (simp add: pi_def)

lemma cos_pi_half [simp]: "cos (pi / 2) = 0"
by (simp add: pi_half cos_is_zero [THEN theI'])

lemma pi_half_gt_zero [simp]: "0 < pi / 2"
apply (rule order_le_neq_trans)
apply (simp add: pi_half cos_is_zero [THEN theI'])
apply (rule notI, drule arg_cong [where f=cos], simp)
done

lemmas pi_half_neq_zero [simp] = pi_half_gt_zero [THEN less_imp_neq, symmetric]
lemmas pi_half_ge_zero [simp] = pi_half_gt_zero [THEN order_less_imp_le]

lemma pi_half_less_two [simp]: "pi / 2 < 2"
apply (rule order_le_neq_trans)
apply (simp add: pi_half cos_is_zero [THEN theI'])
apply (rule notI, drule arg_cong [where f=cos], simp)
done

lemmas pi_half_neq_two [simp] = pi_half_less_two [THEN less_imp_neq]
lemmas pi_half_le_two [simp] =  pi_half_less_two [THEN order_less_imp_le]

lemma pi_gt_zero [simp]: "0 < pi"
by (insert pi_half_gt_zero, simp)

lemma pi_ge_zero [simp]: "0 \<le> pi"
by (rule pi_gt_zero [THEN order_less_imp_le])

lemma pi_neq_zero [simp]: "pi \<noteq> 0"
by (rule pi_gt_zero [THEN less_imp_neq, THEN not_sym])

lemma pi_not_less_zero [simp]: "\<not> pi < 0"
by (simp add: linorder_not_less)

lemma minus_pi_half_less_zero [simp]: "-(pi/2) < 0"
by auto

lemma sin_pi_half [simp]: "sin(pi/2) = 1"
apply (cut_tac x = "pi/2" in sin_cos_squared_add2)
apply (cut_tac sin_gt_zero [OF pi_half_gt_zero pi_half_less_two])
apply (simp add: power2_eq_square)
done

lemma cos_pi [simp]: "cos pi = -1"
by (cut_tac x = "pi/2" and y = "pi/2" in cos_add, simp)

lemma sin_pi [simp]: "sin pi = 0"
by (cut_tac x = "pi/2" and y = "pi/2" in sin_add, simp)

lemma sin_cos_eq: "sin x = cos (pi/2 - x)"
by (simp add: diff_minus cos_add)
declare sin_cos_eq [symmetric, simp]

lemma minus_sin_cos_eq: "-sin x = cos (x + pi/2)"
by (simp add: cos_add)
declare minus_sin_cos_eq [symmetric, simp]

lemma cos_sin_eq: "cos x = sin (pi/2 - x)"
by (simp add: diff_minus sin_add)
declare cos_sin_eq [symmetric, simp]

lemma sin_periodic_pi [simp]: "sin (x + pi) = - sin x"
by (simp add: sin_add)

lemma sin_periodic_pi2 [simp]: "sin (pi + x) = - sin x"
by (simp add: sin_add)

lemma cos_periodic_pi [simp]: "cos (x + pi) = - cos x"
by (simp add: cos_add)

lemma sin_periodic [simp]: "sin (x + 2*pi) = sin x"
by (simp add: sin_add cos_double)

lemma cos_periodic [simp]: "cos (x + 2*pi) = cos x"
by (simp add: cos_add cos_double)

lemma cos_npi [simp]: "cos (real n * pi) = -1 ^ n"
apply (induct "n")
apply (auto simp add: real_of_nat_Suc left_distrib)
done

lemma cos_npi2 [simp]: "cos (pi * real n) = -1 ^ n"
proof -
  have "cos (pi * real n) = cos (real n * pi)" by (simp only: mult_commute)
  also have "... = -1 ^ n" by (rule cos_npi) 
  finally show ?thesis .
qed

lemma sin_npi [simp]: "sin (real (n::nat) * pi) = 0"
apply (induct "n")
apply (auto simp add: real_of_nat_Suc left_distrib)
done

lemma sin_npi2 [simp]: "sin (pi * real (n::nat)) = 0"
by (simp add: mult_commute [of pi]) 

lemma cos_two_pi [simp]: "cos (2 * pi) = 1"
by (simp add: cos_double)

lemma sin_two_pi [simp]: "sin (2 * pi) = 0"
by simp

lemma sin_gt_zero2: "[| 0 < x; x < pi/2 |] ==> 0 < sin x"
apply (rule sin_gt_zero, assumption)
apply (rule order_less_trans, assumption)
apply (rule pi_half_less_two)
done

lemma sin_less_zero: 
  assumes lb: "- pi/2 < x" and "x < 0" shows "sin x < 0"
proof -
  have "0 < sin (- x)" using prems by (simp only: sin_gt_zero2) 
  thus ?thesis by simp
qed

lemma pi_less_4: "pi < 4"
by (cut_tac pi_half_less_two, auto)

lemma cos_gt_zero: "[| 0 < x; x < pi/2 |] ==> 0 < cos x"
apply (cut_tac pi_less_4)
apply (cut_tac f = cos and a = 0 and b = x and y = 0 in IVT2_objl, safe, simp_all)
apply (cut_tac cos_is_zero, safe)
apply (rename_tac y z)
apply (drule_tac x = y in spec)
apply (drule_tac x = "pi/2" in spec, simp) 
done

lemma cos_gt_zero_pi: "[| -(pi/2) < x; x < pi/2 |] ==> 0 < cos x"
apply (rule_tac x = x and y = 0 in linorder_cases)
apply (rule cos_minus [THEN subst])
apply (rule cos_gt_zero)
apply (auto intro: cos_gt_zero)
done
 
lemma cos_ge_zero: "[| -(pi/2) \<le> x; x \<le> pi/2 |] ==> 0 \<le> cos x"
apply (auto simp add: order_le_less cos_gt_zero_pi)
apply (subgoal_tac "x = pi/2", auto) 
done

lemma sin_gt_zero_pi: "[| 0 < x; x < pi  |] ==> 0 < sin x"
apply (subst sin_cos_eq)
apply (rotate_tac 1)
apply (drule real_sum_of_halves [THEN ssubst])
apply (auto intro!: cos_gt_zero_pi simp del: sin_cos_eq [symmetric])
done

lemma sin_ge_zero: "[| 0 \<le> x; x \<le> pi |] ==> 0 \<le> sin x"
by (auto simp add: order_le_less sin_gt_zero_pi)

lemma cos_total: "[| -1 \<le> y; y \<le> 1 |] ==> EX! x. 0 \<le> x & x \<le> pi & (cos x = y)"
apply (subgoal_tac "\<exists>x. 0 \<le> x & x \<le> pi & cos x = y")
apply (rule_tac [2] IVT2)
apply (auto intro: order_less_imp_le DERIV_isCont DERIV_cos)
apply (cut_tac x = xa and y = y in linorder_less_linear)
apply (rule ccontr, auto)
apply (drule_tac f = cos in Rolle)
apply (drule_tac [5] f = cos in Rolle)
apply (auto intro: order_less_imp_le DERIV_isCont DERIV_cos
            dest!: DERIV_cos [THEN DERIV_unique] 
            simp add: differentiable_def)
apply (auto dest: sin_gt_zero_pi [OF order_le_less_trans order_less_le_trans])
done

lemma sin_total:
     "[| -1 \<le> y; y \<le> 1 |] ==> EX! x. -(pi/2) \<le> x & x \<le> pi/2 & (sin x = y)"
apply (rule ccontr)
apply (subgoal_tac "\<forall>x. (- (pi/2) \<le> x & x \<le> pi/2 & (sin x = y)) = (0 \<le> (x + pi/2) & (x + pi/2) \<le> pi & (cos (x + pi/2) = -y))")
apply (erule contrapos_np)
apply (simp del: minus_sin_cos_eq [symmetric])
apply (cut_tac y="-y" in cos_total, simp) apply simp 
apply (erule ex1E)
apply (rule_tac a = "x - (pi/2)" in ex1I)
apply (simp (no_asm) add: real_add_assoc)
apply (rotate_tac 3)
apply (drule_tac x = "xa + pi/2" in spec, safe, simp_all) 
done

lemma reals_Archimedean4:
     "[| 0 < y; 0 \<le> x |] ==> \<exists>n. real n * y \<le> x & x < real (Suc n) * y"
apply (auto dest!: reals_Archimedean3)
apply (drule_tac x = x in spec, clarify) 
apply (subgoal_tac "x < real(LEAST m::nat. x < real m * y) * y")
 prefer 2 apply (erule LeastI) 
apply (case_tac "LEAST m::nat. x < real m * y", simp) 
apply (subgoal_tac "~ x < real nat * y")
 prefer 2 apply (rule not_less_Least, simp, force)  
done

(* Pre Isabelle99-2 proof was simpler- numerals arithmetic 
   now causes some unwanted re-arrangements of literals!   *)
lemma cos_zero_lemma:
     "[| 0 \<le> x; cos x = 0 |] ==>  
      \<exists>n::nat. ~even n & x = real n * (pi/2)"
apply (drule pi_gt_zero [THEN reals_Archimedean4], safe)
apply (subgoal_tac "0 \<le> x - real n * pi & 
                    (x - real n * pi) \<le> pi & (cos (x - real n * pi) = 0) ")
apply (auto simp add: compare_rls) 
  prefer 3 apply (simp add: cos_diff) 
 prefer 2 apply (simp add: real_of_nat_Suc left_distrib) 
apply (simp add: cos_diff)
apply (subgoal_tac "EX! x. 0 \<le> x & x \<le> pi & cos x = 0")
apply (rule_tac [2] cos_total, safe)
apply (drule_tac x = "x - real n * pi" in spec)
apply (drule_tac x = "pi/2" in spec)
apply (simp add: cos_diff)
apply (rule_tac x = "Suc (2 * n)" in exI)
apply (simp add: real_of_nat_Suc left_distrib, auto)
done

lemma sin_zero_lemma:
     "[| 0 \<le> x; sin x = 0 |] ==>  
      \<exists>n::nat. even n & x = real n * (pi/2)"
apply (subgoal_tac "\<exists>n::nat. ~ even n & x + pi/2 = real n * (pi/2) ")
 apply (clarify, rule_tac x = "n - 1" in exI)
 apply (force simp add: odd_Suc_mult_two_ex real_of_nat_Suc left_distrib)
apply (rule cos_zero_lemma)
apply (simp_all add: add_increasing)  
done


lemma cos_zero_iff:
     "(cos x = 0) =  
      ((\<exists>n::nat. ~even n & (x = real n * (pi/2))) |    
       (\<exists>n::nat. ~even n & (x = -(real n * (pi/2)))))"
apply (rule iffI)
apply (cut_tac linorder_linear [of 0 x], safe)
apply (drule cos_zero_lemma, assumption+)
apply (cut_tac x="-x" in cos_zero_lemma, simp, simp) 
apply (force simp add: minus_equation_iff [of x]) 
apply (auto simp only: odd_Suc_mult_two_ex real_of_nat_Suc left_distrib) 
apply (auto simp add: cos_add)
done

(* ditto: but to a lesser extent *)
lemma sin_zero_iff:
     "(sin x = 0) =  
      ((\<exists>n::nat. even n & (x = real n * (pi/2))) |    
       (\<exists>n::nat. even n & (x = -(real n * (pi/2)))))"
apply (rule iffI)
apply (cut_tac linorder_linear [of 0 x], safe)
apply (drule sin_zero_lemma, assumption+)
apply (cut_tac x="-x" in sin_zero_lemma, simp, simp, safe)
apply (force simp add: minus_equation_iff [of x]) 
apply (auto simp add: even_mult_two_ex)
done


subsection{*Tangent*}

definition
  tan :: "real => real" where
  "tan x = (sin x)/(cos x)"

lemma tan_zero [simp]: "tan 0 = 0"
by (simp add: tan_def)

lemma tan_pi [simp]: "tan pi = 0"
by (simp add: tan_def)

lemma tan_npi [simp]: "tan (real (n::nat) * pi) = 0"
by (simp add: tan_def)

lemma tan_minus [simp]: "tan (-x) = - tan x"
by (simp add: tan_def minus_mult_left)

lemma tan_periodic [simp]: "tan (x + 2*pi) = tan x"
by (simp add: tan_def)

lemma lemma_tan_add1: 
      "[| cos x \<noteq> 0; cos y \<noteq> 0 |]  
        ==> 1 - tan(x)*tan(y) = cos (x + y)/(cos x * cos y)"
apply (simp add: tan_def divide_inverse)
apply (auto simp del: inverse_mult_distrib 
            simp add: inverse_mult_distrib [symmetric] mult_ac)
apply (rule_tac c1 = "cos x * cos y" in real_mult_right_cancel [THEN subst])
apply (auto simp del: inverse_mult_distrib 
            simp add: mult_assoc left_diff_distrib cos_add)
done  

lemma add_tan_eq: 
      "[| cos x \<noteq> 0; cos y \<noteq> 0 |]  
       ==> tan x + tan y = sin(x + y)/(cos x * cos y)"
apply (simp add: tan_def)
apply (rule_tac c1 = "cos x * cos y" in real_mult_right_cancel [THEN subst])
apply (auto simp add: mult_assoc left_distrib)
apply (simp add: sin_add)
done

lemma tan_add:
     "[| cos x \<noteq> 0; cos y \<noteq> 0; cos (x + y) \<noteq> 0 |]  
      ==> tan(x + y) = (tan(x) + tan(y))/(1 - tan(x) * tan(y))"
apply (simp (no_asm_simp) add: add_tan_eq lemma_tan_add1)
apply (simp add: tan_def)
done

lemma tan_double:
     "[| cos x \<noteq> 0; cos (2 * x) \<noteq> 0 |]  
      ==> tan (2 * x) = (2 * tan x)/(1 - (tan(x) ^ 2))"
apply (insert tan_add [of x x]) 
apply (simp add: mult_2 [symmetric])  
apply (auto simp add: numeral_2_eq_2)
done

lemma tan_gt_zero: "[| 0 < x; x < pi/2 |] ==> 0 < tan x"
by (simp add: tan_def zero_less_divide_iff sin_gt_zero2 cos_gt_zero_pi) 

lemma tan_less_zero: 
  assumes lb: "- pi/2 < x" and "x < 0" shows "tan x < 0"
proof -
  have "0 < tan (- x)" using prems by (simp only: tan_gt_zero) 
  thus ?thesis by simp
qed

lemma lemma_DERIV_tan:
     "cos x \<noteq> 0 ==> DERIV (%x. sin(x)/cos(x)) x :> inverse((cos x)\<twosuperior>)"
apply (rule lemma_DERIV_subst)
apply (best intro!: DERIV_intros intro: DERIV_chain2) 
apply (auto simp add: divide_inverse numeral_2_eq_2)
done

lemma DERIV_tan [simp]: "cos x \<noteq> 0 ==> DERIV tan x :> inverse((cos x)\<twosuperior>)"
by (auto dest: lemma_DERIV_tan simp add: tan_def [symmetric])

lemma isCont_tan [simp]: "cos x \<noteq> 0 ==> isCont tan x"
by (rule DERIV_tan [THEN DERIV_isCont])

lemma LIM_cos_div_sin [simp]: "(%x. cos(x)/sin(x)) -- pi/2 --> 0"
apply (subgoal_tac "(\<lambda>x. cos x * inverse (sin x)) -- pi * inverse 2 --> 0*1")
apply (simp add: divide_inverse [symmetric])
apply (rule LIM_mult)
apply (rule_tac [2] inverse_1 [THEN subst])
apply (rule_tac [2] LIM_inverse)
apply (simp_all add: divide_inverse [symmetric]) 
apply (simp_all only: isCont_def [symmetric] cos_pi_half [symmetric] sin_pi_half [symmetric]) 
apply (blast intro!: DERIV_isCont DERIV_sin DERIV_cos)+
done

lemma lemma_tan_total: "0 < y ==> \<exists>x. 0 < x & x < pi/2 & y < tan x"
apply (cut_tac LIM_cos_div_sin)
apply (simp only: LIM_def)
apply (drule_tac x = "inverse y" in spec, safe, force)
apply (drule_tac ?d1.0 = s in pi_half_gt_zero [THEN [2] real_lbound_gt_zero], safe)
apply (rule_tac x = "(pi/2) - e" in exI)
apply (simp (no_asm_simp))
apply (drule_tac x = "(pi/2) - e" in spec)
apply (auto simp add: tan_def)
apply (rule inverse_less_iff_less [THEN iffD1])
apply (auto simp add: divide_inverse)
apply (rule real_mult_order) 
apply (subgoal_tac [3] "0 < sin e & 0 < cos e")
apply (auto intro: cos_gt_zero sin_gt_zero2 simp add: mult_commute) 
done

lemma tan_total_pos: "0 \<le> y ==> \<exists>x. 0 \<le> x & x < pi/2 & tan x = y"
apply (frule order_le_imp_less_or_eq, safe)
 prefer 2 apply force
apply (drule lemma_tan_total, safe)
apply (cut_tac f = tan and a = 0 and b = x and y = y in IVT_objl)
apply (auto intro!: DERIV_tan [THEN DERIV_isCont])
apply (drule_tac y = xa in order_le_imp_less_or_eq)
apply (auto dest: cos_gt_zero)
done

lemma lemma_tan_total1: "\<exists>x. -(pi/2) < x & x < (pi/2) & tan x = y"
apply (cut_tac linorder_linear [of 0 y], safe)
apply (drule tan_total_pos)
apply (cut_tac [2] y="-y" in tan_total_pos, safe)
apply (rule_tac [3] x = "-x" in exI)
apply (auto intro!: exI)
done

lemma tan_total: "EX! x. -(pi/2) < x & x < (pi/2) & tan x = y"
apply (cut_tac y = y in lemma_tan_total1, auto)
apply (cut_tac x = xa and y = y in linorder_less_linear, auto)
apply (subgoal_tac [2] "\<exists>z. y < z & z < xa & DERIV tan z :> 0")
apply (subgoal_tac "\<exists>z. xa < z & z < y & DERIV tan z :> 0")
apply (rule_tac [4] Rolle)
apply (rule_tac [2] Rolle)
apply (auto intro!: DERIV_tan DERIV_isCont exI 
            simp add: differentiable_def)
txt{*Now, simulate TRYALL*}
apply (rule_tac [!] DERIV_tan asm_rl)
apply (auto dest!: DERIV_unique [OF _ DERIV_tan]
	    simp add: cos_gt_zero_pi [THEN less_imp_neq, THEN not_sym]) 
done


subsection {* Inverse Trigonometric Functions *}

definition
  arcsin :: "real => real" where
  "arcsin y = (THE x. -(pi/2) \<le> x & x \<le> pi/2 & sin x = y)"

definition
  arccos :: "real => real" where
  "arccos y = (THE x. 0 \<le> x & x \<le> pi & cos x = y)"

definition     
  arctan :: "real => real" where
  "arctan y = (THE x. -(pi/2) < x & x < pi/2 & tan x = y)"

lemma arcsin:
     "[| -1 \<le> y; y \<le> 1 |]  
      ==> -(pi/2) \<le> arcsin y &  
           arcsin y \<le> pi/2 & sin(arcsin y) = y"
unfolding arcsin_def by (rule theI' [OF sin_total])

lemma arcsin_pi:
     "[| -1 \<le> y; y \<le> 1 |]  
      ==> -(pi/2) \<le> arcsin y & arcsin y \<le> pi & sin(arcsin y) = y"
apply (drule (1) arcsin)
apply (force intro: order_trans)
done

lemma sin_arcsin [simp]: "[| -1 \<le> y; y \<le> 1 |] ==> sin(arcsin y) = y"
by (blast dest: arcsin)
      
lemma arcsin_bounded:
     "[| -1 \<le> y; y \<le> 1 |] ==> -(pi/2) \<le> arcsin y & arcsin y \<le> pi/2"
by (blast dest: arcsin)

lemma arcsin_lbound: "[| -1 \<le> y; y \<le> 1 |] ==> -(pi/2) \<le> arcsin y"
by (blast dest: arcsin)

lemma arcsin_ubound: "[| -1 \<le> y; y \<le> 1 |] ==> arcsin y \<le> pi/2"
by (blast dest: arcsin)

lemma arcsin_lt_bounded:
     "[| -1 < y; y < 1 |] ==> -(pi/2) < arcsin y & arcsin y < pi/2"
apply (frule order_less_imp_le)
apply (frule_tac y = y in order_less_imp_le)
apply (frule arcsin_bounded)
apply (safe, simp)
apply (drule_tac y = "arcsin y" in order_le_imp_less_or_eq)
apply (drule_tac [2] y = "pi/2" in order_le_imp_less_or_eq, safe)
apply (drule_tac [!] f = sin in arg_cong, auto)
done

lemma arcsin_sin: "[|-(pi/2) \<le> x; x \<le> pi/2 |] ==> arcsin(sin x) = x"
apply (unfold arcsin_def)
apply (rule the1_equality)
apply (rule sin_total, auto)
done

lemma arccos:
     "[| -1 \<le> y; y \<le> 1 |]  
      ==> 0 \<le> arccos y & arccos y \<le> pi & cos(arccos y) = y"
unfolding arccos_def by (rule theI' [OF cos_total])

lemma cos_arccos [simp]: "[| -1 \<le> y; y \<le> 1 |] ==> cos(arccos y) = y"
by (blast dest: arccos)
      
lemma arccos_bounded: "[| -1 \<le> y; y \<le> 1 |] ==> 0 \<le> arccos y & arccos y \<le> pi"
by (blast dest: arccos)

lemma arccos_lbound: "[| -1 \<le> y; y \<le> 1 |] ==> 0 \<le> arccos y"
by (blast dest: arccos)

lemma arccos_ubound: "[| -1 \<le> y; y \<le> 1 |] ==> arccos y \<le> pi"
by (blast dest: arccos)

lemma arccos_lt_bounded:
     "[| -1 < y; y < 1 |]  
      ==> 0 < arccos y & arccos y < pi"
apply (frule order_less_imp_le)
apply (frule_tac y = y in order_less_imp_le)
apply (frule arccos_bounded, auto)
apply (drule_tac y = "arccos y" in order_le_imp_less_or_eq)
apply (drule_tac [2] y = pi in order_le_imp_less_or_eq, auto)
apply (drule_tac [!] f = cos in arg_cong, auto)
done

lemma arccos_cos: "[|0 \<le> x; x \<le> pi |] ==> arccos(cos x) = x"
apply (simp add: arccos_def)
apply (auto intro!: the1_equality cos_total)
done

lemma arccos_cos2: "[|x \<le> 0; -pi \<le> x |] ==> arccos(cos x) = -x"
apply (simp add: arccos_def)
apply (auto intro!: the1_equality cos_total)
done

lemma cos_arcsin: "\<lbrakk>-1 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> cos (arcsin x) = sqrt (1 - x\<twosuperior>)"
apply (subgoal_tac "x\<twosuperior> \<le> 1")
apply (rule power2_eq_imp_eq)
apply (simp add: cos_squared_eq)
apply (rule cos_ge_zero)
apply (erule (1) arcsin_lbound)
apply (erule (1) arcsin_ubound)
apply simp
apply (subgoal_tac "\<bar>x\<bar>\<twosuperior> \<le> 1\<twosuperior>", simp)
apply (rule power_mono, simp, simp)
done

lemma sin_arccos: "\<lbrakk>-1 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> sin (arccos x) = sqrt (1 - x\<twosuperior>)"
apply (subgoal_tac "x\<twosuperior> \<le> 1")
apply (rule power2_eq_imp_eq)
apply (simp add: sin_squared_eq)
apply (rule sin_ge_zero)
apply (erule (1) arccos_lbound)
apply (erule (1) arccos_ubound)
apply simp
apply (subgoal_tac "\<bar>x\<bar>\<twosuperior> \<le> 1\<twosuperior>", simp)
apply (rule power_mono, simp, simp)
done

lemma arctan [simp]:
     "- (pi/2) < arctan y  & arctan y < pi/2 & tan (arctan y) = y"
unfolding arctan_def by (rule theI' [OF tan_total])

lemma tan_arctan: "tan(arctan y) = y"
by auto

lemma arctan_bounded: "- (pi/2) < arctan y  & arctan y < pi/2"
by (auto simp only: arctan)

lemma arctan_lbound: "- (pi/2) < arctan y"
by auto

lemma arctan_ubound: "arctan y < pi/2"
by (auto simp only: arctan)

lemma arctan_tan: 
      "[|-(pi/2) < x; x < pi/2 |] ==> arctan(tan x) = x"
apply (unfold arctan_def)
apply (rule the1_equality)
apply (rule tan_total, auto)
done

lemma arctan_zero_zero [simp]: "arctan 0 = 0"
by (insert arctan_tan [of 0], simp)

lemma cos_arctan_not_zero [simp]: "cos(arctan x) \<noteq> 0"
apply (auto simp add: cos_zero_iff)
apply (case_tac "n")
apply (case_tac [3] "n")
apply (cut_tac [2] y = x in arctan_ubound)
apply (cut_tac [4] y = x in arctan_lbound) 
apply (auto simp add: real_of_nat_Suc left_distrib mult_less_0_iff)
done

lemma tan_sec: "cos x \<noteq> 0 ==> 1 + tan(x) ^ 2 = inverse(cos x) ^ 2"
apply (rule power_inverse [THEN subst])
apply (rule_tac c1 = "(cos x)\<twosuperior>" in real_mult_right_cancel [THEN iffD1])
apply (auto dest: field_power_not_zero
        simp add: power_mult_distrib left_distrib power_divide tan_def 
                  mult_assoc power_inverse [symmetric] 
        simp del: realpow_Suc)
done

lemma isCont_inverse_function2:
  fixes f g :: "real \<Rightarrow> real" shows
  "\<lbrakk>a < x; x < b;
    \<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> g (f z) = z;
    \<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> isCont f z\<rbrakk>
   \<Longrightarrow> isCont g (f x)"
apply (rule isCont_inverse_function
       [where f=f and d="min (x - a) (b - x)"])
apply (simp_all add: abs_le_iff)
done

lemma isCont_arcsin: "\<lbrakk>-1 < x; x < 1\<rbrakk> \<Longrightarrow> isCont arcsin x"
apply (subgoal_tac "isCont arcsin (sin (arcsin x))", simp)
apply (rule isCont_inverse_function2 [where f=sin])
apply (erule (1) arcsin_lt_bounded [THEN conjunct1])
apply (erule (1) arcsin_lt_bounded [THEN conjunct2])
apply (fast intro: arcsin_sin, simp)
done

lemma isCont_arccos: "\<lbrakk>-1 < x; x < 1\<rbrakk> \<Longrightarrow> isCont arccos x"
apply (subgoal_tac "isCont arccos (cos (arccos x))", simp)
apply (rule isCont_inverse_function2 [where f=cos])
apply (erule (1) arccos_lt_bounded [THEN conjunct1])
apply (erule (1) arccos_lt_bounded [THEN conjunct2])
apply (fast intro: arccos_cos, simp)
done

lemma isCont_arctan: "isCont arctan x"
apply (rule arctan_lbound [of x, THEN dense, THEN exE], clarify)
apply (rule arctan_ubound [of x, THEN dense, THEN exE], clarify)
apply (subgoal_tac "isCont arctan (tan (arctan x))", simp)
apply (erule (1) isCont_inverse_function2 [where f=tan])
apply (clarify, rule arctan_tan)
apply (erule (1) order_less_le_trans)
apply (erule (1) order_le_less_trans)
apply (clarify, rule isCont_tan)
apply (rule less_imp_neq [symmetric])
apply (rule cos_gt_zero_pi)
apply (erule (1) order_less_le_trans)
apply (erule (1) order_le_less_trans)
done

lemma DERIV_arcsin:
  "\<lbrakk>-1 < x; x < 1\<rbrakk> \<Longrightarrow> DERIV arcsin x :> inverse (sqrt (1 - x\<twosuperior>))"
apply (rule DERIV_inverse_function [where f=sin and a="-1" and b="1"])
apply (rule lemma_DERIV_subst [OF DERIV_sin])
apply (simp add: cos_arcsin)
apply (subgoal_tac "\<bar>x\<bar>\<twosuperior> < 1\<twosuperior>", simp)
apply (rule power_strict_mono, simp, simp, simp)
apply assumption
apply assumption
apply simp
apply (erule (1) isCont_arcsin)
done

lemma DERIV_arccos:
  "\<lbrakk>-1 < x; x < 1\<rbrakk> \<Longrightarrow> DERIV arccos x :> inverse (- sqrt (1 - x\<twosuperior>))"
apply (rule DERIV_inverse_function [where f=cos and a="-1" and b="1"])
apply (rule lemma_DERIV_subst [OF DERIV_cos])
apply (simp add: sin_arccos)
apply (subgoal_tac "\<bar>x\<bar>\<twosuperior> < 1\<twosuperior>", simp)
apply (rule power_strict_mono, simp, simp, simp)
apply assumption
apply assumption
apply simp
apply (erule (1) isCont_arccos)
done

lemma DERIV_arctan: "DERIV arctan x :> inverse (1 + x\<twosuperior>)"
apply (rule DERIV_inverse_function [where f=tan and a="x - 1" and b="x + 1"])
apply (rule lemma_DERIV_subst [OF DERIV_tan])
apply (rule cos_arctan_not_zero)
apply (simp add: power_inverse tan_sec [symmetric])
apply (subgoal_tac "0 < 1 + x\<twosuperior>", simp)
apply (simp add: add_pos_nonneg)
apply (simp, simp, simp, rule isCont_arctan)
done


subsection {* More Theorems about Sin and Cos *}

lemma cos_45: "cos (pi / 4) = sqrt 2 / 2"
proof -
  let ?c = "cos (pi / 4)" and ?s = "sin (pi / 4)"
  have nonneg: "0 \<le> ?c"
    by (rule cos_ge_zero, rule order_trans [where y=0], simp_all)
  have "0 = cos (pi / 4 + pi / 4)"
    by simp
  also have "cos (pi / 4 + pi / 4) = ?c\<twosuperior> - ?s\<twosuperior>"
    by (simp only: cos_add power2_eq_square)
  also have "\<dots> = 2 * ?c\<twosuperior> - 1"
    by (simp add: sin_squared_eq)
  finally have "?c\<twosuperior> = (sqrt 2 / 2)\<twosuperior>"
    by (simp add: power_divide)
  thus ?thesis
    using nonneg by (rule power2_eq_imp_eq) simp
qed

lemma cos_30: "cos (pi / 6) = sqrt 3 / 2"
proof -
  let ?c = "cos (pi / 6)" and ?s = "sin (pi / 6)"
  have pos_c: "0 < ?c"
    by (rule cos_gt_zero, simp, simp)
  have "0 = cos (pi / 6 + pi / 6 + pi / 6)"
    by simp
  also have "\<dots> = (?c * ?c - ?s * ?s) * ?c - (?s * ?c + ?c * ?s) * ?s"
    by (simp only: cos_add sin_add)
  also have "\<dots> = ?c * (?c\<twosuperior> - 3 * ?s\<twosuperior>)"
    by (simp add: ring_eq_simps power2_eq_square)
  finally have "?c\<twosuperior> = (sqrt 3 / 2)\<twosuperior>"
    using pos_c by (simp add: sin_squared_eq power_divide)
  thus ?thesis
    using pos_c [THEN order_less_imp_le]
    by (rule power2_eq_imp_eq) simp
qed

lemma sin_45: "sin (pi / 4) = sqrt 2 / 2"
proof -
  have "sin (pi / 4) = cos (pi / 2 - pi / 4)" by (rule sin_cos_eq)
  also have "pi / 2 - pi / 4 = pi / 4" by simp
  also have "cos (pi / 4) = sqrt 2 / 2" by (rule cos_45)
  finally show ?thesis .
qed

lemma sin_60: "sin (pi / 3) = sqrt 3 / 2"
proof -
  have "sin (pi / 3) = cos (pi / 2 - pi / 3)" by (rule sin_cos_eq)
  also have "pi / 2 - pi / 3 = pi / 6" by simp
  also have "cos (pi / 6) = sqrt 3 / 2" by (rule cos_30)
  finally show ?thesis .
qed

lemma cos_60: "cos (pi / 3) = 1 / 2"
apply (rule power2_eq_imp_eq)
apply (simp add: cos_squared_eq sin_60 power_divide)
apply (rule cos_ge_zero, rule order_trans [where y=0], simp_all)
done

lemma sin_30: "sin (pi / 6) = 1 / 2"
proof -
  have "sin (pi / 6) = cos (pi / 2 - pi / 6)" by (rule sin_cos_eq)
  also have "pi / 2 - pi / 6 = pi / 3" by simp
  also have "cos (pi / 3) = 1 / 2" by (rule cos_60)
  finally show ?thesis .
qed

lemma tan_30: "tan (pi / 6) = 1 / sqrt 3"
unfolding tan_def by (simp add: sin_30 cos_30)

lemma tan_45: "tan (pi / 4) = 1"
unfolding tan_def by (simp add: sin_45 cos_45)

lemma tan_60: "tan (pi / 3) = sqrt 3"
unfolding tan_def by (simp add: sin_60 cos_60)

text{*NEEDED??*}
lemma [simp]:
     "sin (x + 1 / 2 * real (Suc m) * pi) =  
      cos (x + 1 / 2 * real  (m) * pi)"
by (simp only: cos_add sin_add real_of_nat_Suc left_distrib right_distrib, auto)

text{*NEEDED??*}
lemma [simp]:
     "sin (x + real (Suc m) * pi / 2) =  
      cos (x + real (m) * pi / 2)"
by (simp only: cos_add sin_add real_of_nat_Suc add_divide_distrib left_distrib, auto)

lemma DERIV_sin_add [simp]: "DERIV (%x. sin (x + k)) xa :> cos (xa + k)"
apply (rule lemma_DERIV_subst)
apply (rule_tac f = sin and g = "%x. x + k" in DERIV_chain2)
apply (best intro!: DERIV_intros intro: DERIV_chain2)+
apply (simp (no_asm))
done

lemma sin_cos_npi [simp]: "sin (real (Suc (2 * n)) * pi / 2) = (-1) ^ n"
proof -
  have "sin ((real n + 1/2) * pi) = cos (real n * pi)"
    by (auto simp add: right_distrib sin_add left_distrib mult_ac)
  thus ?thesis
    by (simp add: real_of_nat_Suc left_distrib add_divide_distrib 
                  mult_commute [of pi])
qed

lemma cos_2npi [simp]: "cos (2 * real (n::nat) * pi) = 1"
by (simp add: cos_double mult_assoc power_add [symmetric] numeral_2_eq_2)

lemma cos_3over2_pi [simp]: "cos (3 / 2 * pi) = 0"
apply (subgoal_tac "cos (pi + pi/2) = 0", simp)
apply (subst cos_add, simp)
done

lemma sin_2npi [simp]: "sin (2 * real (n::nat) * pi) = 0"
by (auto simp add: mult_assoc)

lemma sin_3over2_pi [simp]: "sin (3 / 2 * pi) = - 1"
apply (subgoal_tac "sin (pi + pi/2) = - 1", simp)
apply (subst sin_add, simp)
done

(*NEEDED??*)
lemma [simp]:
     "cos(x + 1 / 2 * real(Suc m) * pi) = -sin (x + 1 / 2 * real m * pi)"
apply (simp only: cos_add sin_add real_of_nat_Suc right_distrib left_distrib minus_mult_right, auto)
done

(*NEEDED??*)
lemma [simp]: "cos (x + real(Suc m) * pi / 2) = -sin (x + real m * pi / 2)"
by (simp only: cos_add sin_add real_of_nat_Suc left_distrib add_divide_distrib, auto)

lemma cos_pi_eq_zero [simp]: "cos (pi * real (Suc (2 * m)) / 2) = 0"
by (simp only: cos_add sin_add real_of_nat_Suc left_distrib right_distrib add_divide_distrib, auto)

lemma DERIV_cos_add [simp]: "DERIV (%x. cos (x + k)) xa :> - sin (xa + k)"
apply (rule lemma_DERIV_subst)
apply (rule_tac f = cos and g = "%x. x + k" in DERIV_chain2)
apply (best intro!: DERIV_intros intro: DERIV_chain2)+
apply (simp (no_asm))
done

lemma sin_zero_abs_cos_one: "sin x = 0 ==> \<bar>cos x\<bar> = 1"
by (auto simp add: sin_zero_iff even_mult_two_ex)

lemma exp_eq_one_iff [simp]: "(exp x = 1) = (x = 0)"
apply auto
apply (drule_tac f = ln in arg_cong, auto)
done

lemma cos_one_sin_zero: "cos x = 1 ==> sin x = 0"
by (cut_tac x = x in sin_cos_squared_add3, auto)


subsection {* Existence of Polar Coordinates *}

lemma cos_x_y_le_one: "\<bar>x / sqrt (x\<twosuperior> + y\<twosuperior>)\<bar> \<le> 1"
apply (rule power2_le_imp_le [OF _ zero_le_one])
apply (simp add: abs_divide power_divide divide_le_eq not_sum_power2_lt_zero)
done

lemma cos_arccos_abs: "\<bar>y\<bar> \<le> 1 \<Longrightarrow> cos (arccos y) = y"
by (simp add: abs_le_iff)

lemma sin_arccos_abs: "\<bar>y\<bar> \<le> 1 \<Longrightarrow> sin (arccos y) = sqrt (1 - y\<twosuperior>)"
by (simp add: sin_arccos abs_le_iff)

lemmas cos_arccos_lemma1 = cos_arccos_abs [OF cos_x_y_le_one]

lemmas sin_arccos_lemma1 = sin_arccos_abs [OF cos_x_y_le_one]

lemma polar_ex1:
     "0 < y ==> \<exists>r a. x = r * cos a & y = r * sin a"
apply (rule_tac x = "sqrt (x\<twosuperior> + y\<twosuperior>)" in exI)
apply (rule_tac x = "arccos (x / sqrt (x\<twosuperior> + y\<twosuperior>))" in exI)
apply (simp add: cos_arccos_lemma1)
apply (simp add: sin_arccos_lemma1)
apply (simp add: power_divide)
apply (simp add: real_sqrt_mult [symmetric])
apply (simp add: right_diff_distrib)
done

lemma polar_ex2:
     "y < 0 ==> \<exists>r a. x = r * cos a & y = r * sin a"
apply (insert polar_ex1 [where x=x and y="-y"], simp, clarify)
apply (rule_tac x = r in exI)
apply (rule_tac x = "-a" in exI, simp)
done

lemma polar_Ex: "\<exists>r a. x = r * cos a & y = r * sin a"
apply (rule_tac x=0 and y=y in linorder_cases)
apply (erule polar_ex1)
apply (rule_tac x=x in exI, rule_tac x=0 in exI, simp)
apply (erule polar_ex2)
done


subsection {* Theorems about Limits *}

(* need to rename second isCont_inverse *)

lemma isCont_inv_fun:
  fixes f g :: "real \<Rightarrow> real"
  shows "[| 0 < d; \<forall>z. \<bar>z - x\<bar> \<le> d --> g(f(z)) = z;  
         \<forall>z. \<bar>z - x\<bar> \<le> d --> isCont f z |]  
      ==> isCont g (f x)"
by (rule isCont_inverse_function)

lemma isCont_inv_fun_inv:
  fixes f g :: "real \<Rightarrow> real"
  shows "[| 0 < d;  
         \<forall>z. \<bar>z - x\<bar> \<le> d --> g(f(z)) = z;  
         \<forall>z. \<bar>z - x\<bar> \<le> d --> isCont f z |]  
       ==> \<exists>e. 0 < e &  
             (\<forall>y. 0 < \<bar>y - f(x)\<bar> & \<bar>y - f(x)\<bar> < e --> f(g(y)) = y)"
apply (drule isCont_inj_range)
prefer 2 apply (assumption, assumption, auto)
apply (rule_tac x = e in exI, auto)
apply (rotate_tac 2)
apply (drule_tac x = y in spec, auto)
done


text{*Bartle/Sherbert: Introduction to Real Analysis, Theorem 4.2.9, p. 110*}
lemma LIM_fun_gt_zero:
     "[| f -- c --> (l::real); 0 < l |]  
         ==> \<exists>r. 0 < r & (\<forall>x::real. x \<noteq> c & \<bar>c - x\<bar> < r --> 0 < f x)"
apply (auto simp add: LIM_def)
apply (drule_tac x = "l/2" in spec, safe, force)
apply (rule_tac x = s in exI)
apply (auto simp only: abs_less_iff)
done

lemma LIM_fun_less_zero:
     "[| f -- c --> (l::real); l < 0 |]  
      ==> \<exists>r. 0 < r & (\<forall>x::real. x \<noteq> c & \<bar>c - x\<bar> < r --> f x < 0)"
apply (auto simp add: LIM_def)
apply (drule_tac x = "-l/2" in spec, safe, force)
apply (rule_tac x = s in exI)
apply (auto simp only: abs_less_iff)
done


lemma LIM_fun_not_zero:
     "[| f -- c --> (l::real); l \<noteq> 0 |] 
      ==> \<exists>r. 0 < r & (\<forall>x::real. x \<noteq> c & \<bar>c - x\<bar> < r --> f x \<noteq> 0)"
apply (cut_tac x = l and y = 0 in linorder_less_linear, auto)
apply (drule LIM_fun_less_zero)
apply (drule_tac [3] LIM_fun_gt_zero)
apply force+
done
  
end 
