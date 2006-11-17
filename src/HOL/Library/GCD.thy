(*  Title:      HOL/GCD.thy
    ID:         $Id$
    Author:     Christophe Tabacznyj and Lawrence C Paulson
    Copyright   1996  University of Cambridge
*)

header {* The Greatest Common Divisor *}

theory GCD
imports Main
begin

text {*
  See \cite{davenport92}.
  \bigskip
*}

consts
  gcd  :: "nat \<times> nat => nat"  -- {* Euclid's algorithm *}

recdef gcd  "measure ((\<lambda>(m, n). n) :: nat \<times> nat => nat)"
  "gcd (m, n) = (if n = 0 then m else gcd (n, m mod n))"

definition
  is_gcd :: "nat => nat => nat => bool" where -- {* @{term gcd} as a relation *}
  "is_gcd p m n = (p dvd m \<and> p dvd n \<and>
    (\<forall>d. d dvd m \<and> d dvd n --> d dvd p))"


lemma gcd_induct:
  "(!!m. P m 0) ==>
    (!!m n. 0 < n ==> P n (m mod n) ==> P m n)
  ==> P (m::nat) (n::nat)"
  apply (induct m n rule: gcd.induct)
  apply (case_tac "n = 0")
   apply simp_all
  done


lemma gcd_0 [simp]: "gcd (m, 0) = m"
  by simp

lemma gcd_non_0: "0 < n ==> gcd (m, n) = gcd (n, m mod n)"
  by simp

declare gcd.simps [simp del]

lemma gcd_1 [simp]: "gcd (m, Suc 0) = 1"
  by (simp add: gcd_non_0)

text {*
  \medskip @{term "gcd (m, n)"} divides @{text m} and @{text n}.  The
  conjunctions don't seem provable separately.
*}

lemma gcd_dvd1 [iff]: "gcd (m, n) dvd m"
  and gcd_dvd2 [iff]: "gcd (m, n) dvd n"
  apply (induct m n rule: gcd_induct)
     apply (simp_all add: gcd_non_0)
  apply (blast dest: dvd_mod_imp_dvd)
  done

text {*
  \medskip Maximality: for all @{term m}, @{term n}, @{term k}
  naturals, if @{term k} divides @{term m} and @{term k} divides
  @{term n} then @{term k} divides @{term "gcd (m, n)"}.
*}

lemma gcd_greatest: "k dvd m ==> k dvd n ==> k dvd gcd (m, n)"
  by (induct m n rule: gcd_induct) (simp_all add: gcd_non_0 dvd_mod)

lemma gcd_greatest_iff [iff]: "(k dvd gcd (m, n)) = (k dvd m \<and> k dvd n)"
  by (blast intro!: gcd_greatest intro: dvd_trans)

lemma gcd_zero: "(gcd (m, n) = 0) = (m = 0 \<and> n = 0)"
  by (simp only: dvd_0_left_iff [symmetric] gcd_greatest_iff)


text {*
  \medskip Function gcd yields the Greatest Common Divisor.
*}

lemma is_gcd: "is_gcd (gcd (m, n)) m n"
  apply (simp add: is_gcd_def gcd_greatest)
  done

text {*
  \medskip Uniqueness of GCDs.
*}

lemma is_gcd_unique: "is_gcd m a b ==> is_gcd n a b ==> m = n"
  apply (simp add: is_gcd_def)
  apply (blast intro: dvd_anti_sym)
  done

lemma is_gcd_dvd: "is_gcd m a b ==> k dvd a ==> k dvd b ==> k dvd m"
  apply (auto simp add: is_gcd_def)
  done


text {*
  \medskip Commutativity
*}

lemma is_gcd_commute: "is_gcd k m n = is_gcd k n m"
  apply (auto simp add: is_gcd_def)
  done

lemma gcd_commute: "gcd (m, n) = gcd (n, m)"
  apply (rule is_gcd_unique)
   apply (rule is_gcd)
  apply (subst is_gcd_commute)
  apply (simp add: is_gcd)
  done

lemma gcd_assoc: "gcd (gcd (k, m), n) = gcd (k, gcd (m, n))"
  apply (rule is_gcd_unique)
   apply (rule is_gcd)
  apply (simp add: is_gcd_def)
  apply (blast intro: dvd_trans)
  done

lemma gcd_0_left [simp]: "gcd (0, m) = m"
  apply (simp add: gcd_commute [of 0])
  done

lemma gcd_1_left [simp]: "gcd (Suc 0, m) = 1"
  apply (simp add: gcd_commute [of "Suc 0"])
  done


text {*
  \medskip Multiplication laws
*}

lemma gcd_mult_distrib2: "k * gcd (m, n) = gcd (k * m, k * n)"
    -- {* \cite[page 27]{davenport92} *}
  apply (induct m n rule: gcd_induct)
   apply simp
  apply (case_tac "k = 0")
   apply (simp_all add: mod_geq gcd_non_0 mod_mult_distrib2)
  done

lemma gcd_mult [simp]: "gcd (k, k * n) = k"
  apply (rule gcd_mult_distrib2 [of k 1 n, simplified, symmetric])
  done

lemma gcd_self [simp]: "gcd (k, k) = k"
  apply (rule gcd_mult [of k 1, simplified])
  done

lemma relprime_dvd_mult: "gcd (k, n) = 1 ==> k dvd m * n ==> k dvd m"
  apply (insert gcd_mult_distrib2 [of m k n])
  apply simp
  apply (erule_tac t = m in ssubst)
  apply simp
  done

lemma relprime_dvd_mult_iff: "gcd (k, n) = 1 ==> (k dvd m * n) = (k dvd m)"
  apply (blast intro: relprime_dvd_mult dvd_trans)
  done

lemma gcd_mult_cancel: "gcd (k, n) = 1 ==> gcd (k * m, n) = gcd (m, n)"
  apply (rule dvd_anti_sym)
   apply (rule gcd_greatest)
    apply (rule_tac n = k in relprime_dvd_mult)
     apply (simp add: gcd_assoc)
     apply (simp add: gcd_commute)
    apply (simp_all add: mult_commute)
  apply (blast intro: dvd_trans)
  done


text {* \medskip Addition laws *}

lemma gcd_add1 [simp]: "gcd (m + n, n) = gcd (m, n)"
  apply (case_tac "n = 0")
   apply (simp_all add: gcd_non_0)
  done

lemma gcd_add2 [simp]: "gcd (m, m + n) = gcd (m, n)"
proof -
  have "gcd (m, m + n) = gcd (m + n, m)" by (rule gcd_commute) 
  also have "... = gcd (n + m, m)" by (simp add: add_commute)
  also have "... = gcd (n, m)" by simp
  also have  "... = gcd (m, n)" by (rule gcd_commute) 
  finally show ?thesis .
qed

lemma gcd_add2' [simp]: "gcd (m, n + m) = gcd (m, n)"
  apply (subst add_commute)
  apply (rule gcd_add2)
  done

lemma gcd_add_mult: "gcd (m, k * m + n) = gcd (m, n)"
  by (induct k) (simp_all add: add_assoc)

end
