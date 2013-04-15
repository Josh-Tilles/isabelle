(*  Title:      HOL/ex/Sqrt.thy
    Author:     Markus Wenzel, Tobias Nipkow, TU Muenchen
*)

header {*  Square roots of primes are irrational *}

theory Sqrt
imports Complex_Main "~~/src/HOL/Number_Theory/Primes"
begin

text {* The square root of any prime number (including 2) is irrational. *}

theorem sqrt_prime_irrational:
  assumes "prime (p::nat)"
  shows "sqrt p \<notin> \<rat>"
proof
  from `prime p` have p: "1 < p" by (simp add: prime_nat_def)
  assume "sqrt p \<in> \<rat>"
  then obtain m n :: nat where
      n: "n \<noteq> 0" and sqrt_rat: "\<bar>sqrt p\<bar> = m / n"
    and gcd: "gcd m n = 1" by (rule Rats_abs_nat_div_natE)
  have eq: "m\<twosuperior> = p * n\<twosuperior>"
  proof -
    from n and sqrt_rat have "m = \<bar>sqrt p\<bar> * n" by simp
    then have "m\<twosuperior> = (sqrt p)\<twosuperior> * n\<twosuperior>"
      by (auto simp add: power2_eq_square)
    also have "(sqrt p)\<twosuperior> = p" by simp
    also have "\<dots> * n\<twosuperior> = p * n\<twosuperior>" by simp
    finally show ?thesis ..
  qed
  have "p dvd m \<and> p dvd n"
  proof
    from eq have "p dvd m\<twosuperior>" ..
    with `prime p` pos2 show "p dvd m" by (rule prime_dvd_power_nat)
    then obtain k where "m = p * k" ..
    with eq have "p * n\<twosuperior> = p\<twosuperior> * k\<twosuperior>" by (auto simp add: power2_eq_square mult_ac)
    with p have "n\<twosuperior> = p * k\<twosuperior>" by (simp add: power2_eq_square)
    then have "p dvd n\<twosuperior>" ..
    with `prime p` pos2 show "p dvd n" by (rule prime_dvd_power_nat)
  qed
  then have "p dvd gcd m n" ..
  with gcd have "p dvd 1" by simp
  then have "p \<le> 1" by (simp add: dvd_imp_le)
  with p show False by simp
qed

corollary sqrt_2_not_rat: "sqrt 2 \<notin> \<rat>"
  using sqrt_prime_irrational[of 2] by simp

subsection {* Variations *}

text {*
  Here is an alternative version of the main proof, using mostly
  linear forward-reasoning.  While this results in less top-down
  structure, it is probably closer to proofs seen in mathematics.
*}

theorem
  assumes "prime (p::nat)"
  shows "sqrt p \<notin> \<rat>"
proof
  from `prime p` have p: "1 < p" by (simp add: prime_nat_def)
  assume "sqrt p \<in> \<rat>"
  then obtain m n :: nat where
      n: "n \<noteq> 0" and sqrt_rat: "\<bar>sqrt p\<bar> = m / n"
    and gcd: "gcd m n = 1" by (rule Rats_abs_nat_div_natE)
  from n and sqrt_rat have "m = \<bar>sqrt p\<bar> * n" by simp
  then have "m\<twosuperior> = (sqrt p)\<twosuperior> * n\<twosuperior>"
    by (auto simp add: power2_eq_square)
  also have "(sqrt p)\<twosuperior> = p" by simp
  also have "\<dots> * n\<twosuperior> = p * n\<twosuperior>" by simp
  finally have eq: "m\<twosuperior> = p * n\<twosuperior>" ..
  then have "p dvd m\<twosuperior>" ..
  with `prime p` pos2 have dvd_m: "p dvd m" by (rule prime_dvd_power_nat)
  then obtain k where "m = p * k" ..
  with eq have "p * n\<twosuperior> = p\<twosuperior> * k\<twosuperior>" by (auto simp add: power2_eq_square mult_ac)
  with p have "n\<twosuperior> = p * k\<twosuperior>" by (simp add: power2_eq_square)
  then have "p dvd n\<twosuperior>" ..
  with `prime p` pos2 have "p dvd n" by (rule prime_dvd_power_nat)
  with dvd_m have "p dvd gcd m n" by (rule gcd_greatest_nat)
  with gcd have "p dvd 1" by simp
  then have "p \<le> 1" by (simp add: dvd_imp_le)
  with p show False by simp
qed


text {* Another old chestnut, which is a consequence of the irrationality of 2. *}

lemma "\<exists>a b::real. a \<notin> \<rat> \<and> b \<notin> \<rat> \<and> a powr b \<in> \<rat>" (is "EX a b. ?P a b")
proof cases
  assume "sqrt 2 powr sqrt 2 \<in> \<rat>"
  then have "?P (sqrt 2) (sqrt 2)"
    by (metis sqrt_2_not_rat)
  then show ?thesis by blast
next
  assume 1: "sqrt 2 powr sqrt 2 \<notin> \<rat>"
  have "(sqrt 2 powr sqrt 2) powr sqrt 2 = 2"
    using powr_realpow [of _ 2]
    by (simp add: powr_powr power2_eq_square [symmetric])
  then have "?P (sqrt 2 powr sqrt 2) (sqrt 2)"
    by (metis 1 Rats_number_of sqrt_2_not_rat)
  then show ?thesis by blast
qed

end

