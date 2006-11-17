(*  Title:      HOL/Hyperreal/ex/Sqrt.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

*)

header {*  Square roots of primes are irrational *}

theory Sqrt
imports Primes Complex_Main
begin

subsection {* Preliminaries *}

text {*
  The set of rational numbers, including the key representation
  theorem.
*}

definition
  rationals  ("\<rat>") where
  "\<rat> = {x. \<exists>m n. n \<noteq> 0 \<and> \<bar>x\<bar> = real (m::nat) / real (n::nat)}"

theorem rationals_rep [elim?]:
  assumes "x \<in> \<rat>"
  obtains m n where "n \<noteq> 0" and "\<bar>x\<bar> = real m / real n" and "gcd (m, n) = 1"
proof -
  from `x \<in> \<rat>` obtain m n :: nat where
      n: "n \<noteq> 0" and x_rat: "\<bar>x\<bar> = real m / real n"
    unfolding rationals_def by blast
  let ?gcd = "gcd (m, n)"
  from n have gcd: "?gcd \<noteq> 0" by (simp add: gcd_zero)
  let ?k = "m div ?gcd"
  let ?l = "n div ?gcd"
  let ?gcd' = "gcd (?k, ?l)"
  have "?gcd dvd m" .. then have gcd_k: "?gcd * ?k = m"
    by (rule dvd_mult_div_cancel)
  have "?gcd dvd n" .. then have gcd_l: "?gcd * ?l = n"
    by (rule dvd_mult_div_cancel)

  from n and gcd_l have "?l \<noteq> 0"
    by (auto iff del: neq0_conv)
  moreover
  have "\<bar>x\<bar> = real ?k / real ?l"
  proof -
    from gcd have "real ?k / real ?l =
        real (?gcd * ?k) / real (?gcd * ?l)"
      by (simp add: mult_divide_cancel_left)
    also from gcd_k and gcd_l have "\<dots> = real m / real n" by simp
    also from x_rat have "\<dots> = \<bar>x\<bar>" ..
    finally show ?thesis ..
  qed
  moreover
  have "?gcd' = 1"
  proof -
    have "?gcd * ?gcd' = gcd (?gcd * ?k, ?gcd * ?l)"
      by (rule gcd_mult_distrib2)
    with gcd_k gcd_l have "?gcd * ?gcd' = ?gcd" by simp
    with gcd show ?thesis by simp
  qed
  ultimately show ?thesis ..
qed


subsection {* Main theorem *}

text {*
  The square root of any prime number (including @{text 2}) is
  irrational.
*}

theorem sqrt_prime_irrational:
  assumes "prime p"
  shows "sqrt (real p) \<notin> \<rat>"
proof
  from `prime p` have p: "1 < p" by (simp add: prime_def)
  assume "sqrt (real p) \<in> \<rat>"
  then obtain m n where
      n: "n \<noteq> 0" and sqrt_rat: "\<bar>sqrt (real p)\<bar> = real m / real n"
    and gcd: "gcd (m, n) = 1" ..
  have eq: "m\<twosuperior> = p * n\<twosuperior>"
  proof -
    from n and sqrt_rat have "real m = \<bar>sqrt (real p)\<bar> * real n" by simp
    then have "real (m\<twosuperior>) = (sqrt (real p))\<twosuperior> * real (n\<twosuperior>)"
      by (auto simp add: power2_eq_square)
    also have "(sqrt (real p))\<twosuperior> = real p" by simp
    also have "\<dots> * real (n\<twosuperior>) = real (p * n\<twosuperior>)" by simp
    finally show ?thesis ..
  qed
  have "p dvd m \<and> p dvd n"
  proof
    from eq have "p dvd m\<twosuperior>" ..
    with `prime p` show "p dvd m" by (rule prime_dvd_power_two)
    then obtain k where "m = p * k" ..
    with eq have "p * n\<twosuperior> = p\<twosuperior> * k\<twosuperior>" by (auto simp add: power2_eq_square mult_ac)
    with p have "n\<twosuperior> = p * k\<twosuperior>" by (simp add: power2_eq_square)
    then have "p dvd n\<twosuperior>" ..
    with `prime p` show "p dvd n" by (rule prime_dvd_power_two)
  qed
  then have "p dvd gcd (m, n)" ..
  with gcd have "p dvd 1" by simp
  then have "p \<le> 1" by (simp add: dvd_imp_le)
  with p show False by simp
qed

corollary "sqrt (real (2::nat)) \<notin> \<rat>"
  by (rule sqrt_prime_irrational) (rule two_is_prime)


subsection {* Variations *}

text {*
  Here is an alternative version of the main proof, using mostly
  linear forward-reasoning.  While this results in less top-down
  structure, it is probably closer to proofs seen in mathematics.
*}

theorem
  assumes "prime p"
  shows "sqrt (real p) \<notin> \<rat>"
proof
  from `prime p` have p: "1 < p" by (simp add: prime_def)
  assume "sqrt (real p) \<in> \<rat>"
  then obtain m n where
      n: "n \<noteq> 0" and sqrt_rat: "\<bar>sqrt (real p)\<bar> = real m / real n"
    and gcd: "gcd (m, n) = 1" ..
  from n and sqrt_rat have "real m = \<bar>sqrt (real p)\<bar> * real n" by simp
  then have "real (m\<twosuperior>) = (sqrt (real p))\<twosuperior> * real (n\<twosuperior>)"
    by (auto simp add: power2_eq_square)
  also have "(sqrt (real p))\<twosuperior> = real p" by simp
  also have "\<dots> * real (n\<twosuperior>) = real (p * n\<twosuperior>)" by simp
  finally have eq: "m\<twosuperior> = p * n\<twosuperior>" ..
  then have "p dvd m\<twosuperior>" ..
  with `prime p` have dvd_m: "p dvd m" by (rule prime_dvd_power_two)
  then obtain k where "m = p * k" ..
  with eq have "p * n\<twosuperior> = p\<twosuperior> * k\<twosuperior>" by (auto simp add: power2_eq_square mult_ac)
  with p have "n\<twosuperior> = p * k\<twosuperior>" by (simp add: power2_eq_square)
  then have "p dvd n\<twosuperior>" ..
  with `prime p` have "p dvd n" by (rule prime_dvd_power_two)
  with dvd_m have "p dvd gcd (m, n)" by (rule gcd_greatest)
  with gcd have "p dvd 1" by simp
  then have "p \<le> 1" by (simp add: dvd_imp_le)
  with p show False by simp
qed

end
