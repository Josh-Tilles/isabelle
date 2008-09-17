(*  Title:      HOL/Divides.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

header {* The division operators div and mod *}

theory Divides
imports Nat Power Product_Type
uses "~~/src/Provers/Arith/cancel_div_mod.ML"
begin

subsection {* Syntactic division operations *}

class div = dvd +
  fixes div :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "div" 70)
    and mod :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "mod" 70)


subsection {* Abstract division in commutative semirings. *}

class semiring_div = comm_semiring_1_cancel + div + 
  assumes mod_div_equality: "a div b * b + a mod b = a"
    and div_by_0 [simp]: "a div 0 = 0"
    and div_0 [simp]: "0 div a = 0"
    and div_mult_self1 [simp]: "b \<noteq> 0 \<Longrightarrow> (a + c * b) div b = c + a div b"
begin

text {* @{const div} and @{const mod} *}

lemma mod_div_equality2: "b * (a div b) + a mod b = a"
  unfolding mult_commute [of b]
  by (rule mod_div_equality)

lemma div_mod_equality: "((a div b) * b + a mod b) + c = a + c"
  by (simp add: mod_div_equality)

lemma div_mod_equality2: "(b * (a div b) + a mod b) + c = a + c"
  by (simp add: mod_div_equality2)

lemma mod_by_0 [simp]: "a mod 0 = a"
  using mod_div_equality [of a zero] by simp

lemma mod_0 [simp]: "0 mod a = 0"
  using mod_div_equality [of zero a] div_0 by simp 

lemma div_mult_self2 [simp]:
  assumes "b \<noteq> 0"
  shows "(a + b * c) div b = c + a div b"
  using assms div_mult_self1 [of b a c] by (simp add: mult_commute)

lemma mod_mult_self1 [simp]: "(a + c * b) mod b = a mod b"
proof (cases "b = 0")
  case True then show ?thesis by simp
next
  case False
  have "a + c * b = (a + c * b) div b * b + (a + c * b) mod b"
    by (simp add: mod_div_equality)
  also from False div_mult_self1 [of b a c] have
    "\<dots> = (c + a div b) * b + (a + c * b) mod b"
      by (simp add: left_distrib add_ac)
  finally have "a = a div b * b + (a + c * b) mod b"
    by (simp add: add_commute [of a] add_assoc left_distrib)
  then have "a div b * b + (a + c * b) mod b = a div b * b + a mod b"
    by (simp add: mod_div_equality)
  then show ?thesis by simp
qed

lemma mod_mult_self2 [simp]: "(a + b * c) mod b = a mod b"
  by (simp add: mult_commute [of b])

lemma div_mult_self1_is_id [simp]: "b \<noteq> 0 \<Longrightarrow> b * a div b = a"
  using div_mult_self2 [of b 0 a] by simp

lemma div_mult_self2_is_id [simp]: "b \<noteq> 0 \<Longrightarrow> a * b div b = a"
  using div_mult_self1 [of b 0 a] by simp

lemma mod_mult_self1_is_0 [simp]: "b * a mod b = 0"
  using mod_mult_self2 [of 0 b a] by simp

lemma mod_mult_self2_is_0 [simp]: "a * b mod b = 0"
  using mod_mult_self1 [of 0 a b] by simp

lemma div_by_1 [simp]: "a div 1 = a"
  using div_mult_self2_is_id [of 1 a] zero_neq_one by simp

lemma mod_by_1 [simp]: "a mod 1 = 0"
proof -
  from mod_div_equality [of a one] div_by_1 have "a + a mod 1 = a" by simp
  then have "a + a mod 1 = a + 0" by simp
  then show ?thesis by (rule add_left_imp_eq)
qed

lemma mod_self [simp]: "a mod a = 0"
  using mod_mult_self2_is_0 [of 1] by simp

lemma div_self [simp]: "a \<noteq> 0 \<Longrightarrow> a div a = 1"
  using div_mult_self2_is_id [of _ 1] by simp

lemma div_add_self1 [simp]:
  assumes "b \<noteq> 0"
  shows "(b + a) div b = a div b + 1"
  using assms div_mult_self1 [of b a 1] by (simp add: add_commute)

lemma div_add_self2 [simp]:
  assumes "b \<noteq> 0"
  shows "(a + b) div b = a div b + 1"
  using assms div_add_self1 [of b a] by (simp add: add_commute)

lemma mod_add_self1 [simp]:
  "(b + a) mod b = a mod b"
  using mod_mult_self1 [of a 1 b] by (simp add: add_commute)

lemma mod_add_self2 [simp]:
  "(a + b) mod b = a mod b"
  using mod_mult_self1 [of a 1 b] by simp

lemma mod_div_decomp:
  fixes a b
  obtains q r where "q = a div b" and "r = a mod b"
    and "a = q * b + r"
proof -
  from mod_div_equality have "a = a div b * b + a mod b" by simp
  moreover have "a div b = a div b" ..
  moreover have "a mod b = a mod b" ..
  note that ultimately show thesis by blast
qed

lemma dvd_eq_mod_eq_0 [code func]: "a dvd b \<longleftrightarrow> b mod a = 0"
proof
  assume "b mod a = 0"
  with mod_div_equality [of b a] have "b div a * a = b" by simp
  then have "b = a * (b div a)" unfolding mult_commute ..
  then have "\<exists>c. b = a * c" ..
  then show "a dvd b" unfolding dvd_def .
next
  assume "a dvd b"
  then have "\<exists>c. b = a * c" unfolding dvd_def .
  then obtain c where "b = a * c" ..
  then have "b mod a = a * c mod a" by simp
  then have "b mod a = c * a mod a" by (simp add: mult_commute)
  then show "b mod a = 0" by simp
qed

end


subsection {* Division on @{typ nat} *}

text {*
  We define @{const div} and @{const mod} on @{typ nat} by means
  of a characteristic relation with two input arguments
  @{term "m\<Colon>nat"}, @{term "n\<Colon>nat"} and two output arguments
  @{term "q\<Colon>nat"}(uotient) and @{term "r\<Colon>nat"}(emainder).
*}

definition divmod_rel :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "divmod_rel m n q r \<longleftrightarrow> m = q * n + r \<and> (if n > 0 then 0 \<le> r \<and> r < n else q = 0)"

text {* @{const divmod_rel} is total: *}

lemma divmod_rel_ex:
  obtains q r where "divmod_rel m n q r"
proof (cases "n = 0")
  case True with that show thesis
    by (auto simp add: divmod_rel_def)
next
  case False
  have "\<exists>q r. m = q * n + r \<and> r < n"
  proof (induct m)
    case 0 with `n \<noteq> 0`
    have "(0\<Colon>nat) = 0 * n + 0 \<and> 0 < n" by simp
    then show ?case by blast
  next
    case (Suc m) then obtain q' r'
      where m: "m = q' * n + r'" and n: "r' < n" by auto
    then show ?case proof (cases "Suc r' < n")
      case True
      from m n have "Suc m = q' * n + Suc r'" by simp
      with True show ?thesis by blast
    next
      case False then have "n \<le> Suc r'" by auto
      moreover from n have "Suc r' \<le> n" by auto
      ultimately have "n = Suc r'" by auto
      with m have "Suc m = Suc q' * n + 0" by simp
      with `n \<noteq> 0` show ?thesis by blast
    qed
  qed
  with that show thesis
    using `n \<noteq> 0` by (auto simp add: divmod_rel_def)
qed

text {* @{const divmod_rel} is injective: *}

lemma divmod_rel_unique_div:
  assumes "divmod_rel m n q r"
    and "divmod_rel m n q' r'"
  shows "q = q'"
proof (cases "n = 0")
  case True with assms show ?thesis
    by (simp add: divmod_rel_def)
next
  case False
  have aux: "\<And>q r q' r'. q' * n + r' = q * n + r \<Longrightarrow> r < n \<Longrightarrow> q' \<le> (q\<Colon>nat)"
  apply (rule leI)
  apply (subst less_iff_Suc_add)
  apply (auto simp add: add_mult_distrib)
  done
  from `n \<noteq> 0` assms show ?thesis
    by (auto simp add: divmod_rel_def
      intro: order_antisym dest: aux sym)
qed

lemma divmod_rel_unique_mod:
  assumes "divmod_rel m n q r"
    and "divmod_rel m n q' r'"
  shows "r = r'"
proof -
  from assms have "q = q'" by (rule divmod_rel_unique_div)
  with assms show ?thesis by (simp add: divmod_rel_def)
qed

text {*
  We instantiate divisibility on the natural numbers by
  means of @{const divmod_rel}:
*}

instantiation nat :: semiring_div
begin

definition divmod :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  [code func del]: "divmod m n = (THE (q, r). divmod_rel m n q r)"

definition div_nat where
  "m div n = fst (divmod m n)"

definition mod_nat where
  "m mod n = snd (divmod m n)"

lemma divmod_div_mod:
  "divmod m n = (m div n, m mod n)"
  unfolding div_nat_def mod_nat_def by simp

lemma divmod_eq:
  assumes "divmod_rel m n q r" 
  shows "divmod m n = (q, r)"
  using assms by (auto simp add: divmod_def
    dest: divmod_rel_unique_div divmod_rel_unique_mod)

lemma div_eq:
  assumes "divmod_rel m n q r" 
  shows "m div n = q"
  using assms by (auto dest: divmod_eq simp add: div_nat_def)

lemma mod_eq:
  assumes "divmod_rel m n q r" 
  shows "m mod n = r"
  using assms by (auto dest: divmod_eq simp add: mod_nat_def)

lemma divmod_rel: "divmod_rel m n (m div n) (m mod n)"
proof -
  from divmod_rel_ex
    obtain q r where rel: "divmod_rel m n q r" .
  moreover with div_eq mod_eq have "m div n = q" and "m mod n = r"
    by simp_all
  ultimately show ?thesis by simp
qed

lemma divmod_zero:
  "divmod m 0 = (0, m)"
proof -
  from divmod_rel [of m 0] show ?thesis
    unfolding divmod_div_mod divmod_rel_def by simp
qed

lemma divmod_base:
  assumes "m < n"
  shows "divmod m n = (0, m)"
proof -
  from divmod_rel [of m n] show ?thesis
    unfolding divmod_div_mod divmod_rel_def
    using assms by (cases "m div n = 0")
      (auto simp add: gr0_conv_Suc [of "m div n"])
qed

lemma divmod_step:
  assumes "0 < n" and "n \<le> m"
  shows "divmod m n = (Suc ((m - n) div n), (m - n) mod n)"
proof -
  from divmod_rel have divmod_m_n: "divmod_rel m n (m div n) (m mod n)" .
  with assms have m_div_n: "m div n \<ge> 1"
    by (cases "m div n") (auto simp add: divmod_rel_def)
  from assms divmod_m_n have "divmod_rel (m - n) n (m div n - 1) (m mod n)"
    by (cases "m div n") (auto simp add: divmod_rel_def)
  with divmod_eq have "divmod (m - n) n = (m div n - 1, m mod n)" by simp
  moreover from divmod_div_mod have "divmod (m - n) n = ((m - n) div n, (m - n) mod n)" .
  ultimately have "m div n = Suc ((m - n) div n)"
    and "m mod n = (m - n) mod n" using m_div_n by simp_all
  then show ?thesis using divmod_div_mod by simp
qed

text {* The ''recursion'' equations for @{const div} and @{const mod} *}

lemma div_less [simp]:
  fixes m n :: nat
  assumes "m < n"
  shows "m div n = 0"
  using assms divmod_base divmod_div_mod by simp

lemma le_div_geq:
  fixes m n :: nat
  assumes "0 < n" and "n \<le> m"
  shows "m div n = Suc ((m - n) div n)"
  using assms divmod_step divmod_div_mod by simp

lemma mod_less [simp]:
  fixes m n :: nat
  assumes "m < n"
  shows "m mod n = m"
  using assms divmod_base divmod_div_mod by simp

lemma le_mod_geq:
  fixes m n :: nat
  assumes "n \<le> m"
  shows "m mod n = (m - n) mod n"
  using assms divmod_step divmod_div_mod by (cases "n = 0") simp_all

instance proof
  fix m n :: nat show "m div n * n + m mod n = m"
    using divmod_rel [of m n] by (simp add: divmod_rel_def)
next
  fix n :: nat show "n div 0 = 0"
    using divmod_zero divmod_div_mod [of n 0] by simp
next
  fix n :: nat show "0 div n = 0"
    using divmod_rel [of 0 n] by (cases n) (simp_all add: divmod_rel_def)
next
  fix m n q :: nat assume "n \<noteq> 0" then show "(q + m * n) div n = m + q div n"
    by (induct m) (simp_all add: le_div_geq)
qed

end

text {* Simproc for cancelling @{const div} and @{const mod} *}

(*lemmas mod_div_equality_nat = semiring_div_class.times_div_mod_plus_zero_one.mod_div_equality [of "m\<Colon>nat" n, standard]
lemmas mod_div_equality2_nat = mod_div_equality2 [of "n\<Colon>nat" m, standard*)

ML {*
structure CancelDivModData =
struct

val div_name = @{const_name div};
val mod_name = @{const_name mod};
val mk_binop = HOLogic.mk_binop;
val mk_sum = ArithData.mk_sum;
val dest_sum = ArithData.dest_sum;

(*logic*)

val div_mod_eqs = map mk_meta_eq [@{thm div_mod_equality}, @{thm div_mod_equality2}]

val trans = trans

val prove_eq_sums =
  let val simps = @{thm add_0} :: @{thm add_0_right} :: @{thms add_ac}
  in ArithData.prove_conv all_tac (ArithData.simp_all_tac simps) end;

end;

structure CancelDivMod = CancelDivModFun(CancelDivModData);

val cancel_div_mod_proc = Simplifier.simproc (the_context ())
  "cancel_div_mod" ["(m::nat) + n"] (K CancelDivMod.proc);

Addsimprocs[cancel_div_mod_proc];
*}

text {* code generator setup *}

lemma divmod_if [code]: "divmod m n = (if n = 0 \<or> m < n then (0, m) else
  let (q, r) = divmod (m - n) n in (Suc q, r))"
  by (simp add: divmod_zero divmod_base divmod_step)
    (simp add: divmod_div_mod)

code_modulename SML
  Divides Nat

code_modulename OCaml
  Divides Nat

code_modulename Haskell
  Divides Nat


subsubsection {* Quotient *}

lemma div_geq: "0 < n \<Longrightarrow>  \<not> m < n \<Longrightarrow> m div n = Suc ((m - n) div n)"
  by (simp add: le_div_geq linorder_not_less)

lemma div_if: "0 < n \<Longrightarrow> m div n = (if m < n then 0 else Suc ((m - n) div n))"
  by (simp add: div_geq)

lemma div_mult_self_is_m [simp]: "0<n ==> (m*n) div n = (m::nat)"
  by simp

lemma div_mult_self1_is_m [simp]: "0<n ==> (n*m) div n = (m::nat)"
  by simp


subsubsection {* Remainder *}

lemma mod_less_divisor [simp]:
  fixes m n :: nat
  assumes "n > 0"
  shows "m mod n < (n::nat)"
  using assms divmod_rel unfolding divmod_rel_def by auto

lemma mod_less_eq_dividend [simp]:
  fixes m n :: nat
  shows "m mod n \<le> m"
proof (rule add_leD2)
  from mod_div_equality have "m div n * n + m mod n = m" .
  then show "m div n * n + m mod n \<le> m" by auto
qed

lemma mod_geq: "\<not> m < (n\<Colon>nat) \<Longrightarrow> m mod n = (m - n) mod n"
  by (simp add: le_mod_geq linorder_not_less)

lemma mod_if: "m mod (n\<Colon>nat) = (if m < n then m else (m - n) mod n)"
  by (simp add: le_mod_geq)

lemma mod_1 [simp]: "m mod Suc 0 = 0"
  by (induct m) (simp_all add: mod_geq)

lemma mod_mult_distrib: "(m mod n) * (k\<Colon>nat) = (m * k) mod (n * k)"
  apply (cases "n = 0", simp)
  apply (cases "k = 0", simp)
  apply (induct m rule: nat_less_induct)
  apply (subst mod_if, simp)
  apply (simp add: mod_geq diff_mult_distrib)
  done

lemma mod_mult_distrib2: "(k::nat) * (m mod n) = (k*m) mod (k*n)"
  by (simp add: mult_commute [of k] mod_mult_distrib)

(* a simple rearrangement of mod_div_equality: *)
lemma mult_div_cancel: "(n::nat) * (m div n) = m - (m mod n)"
  by (cut_tac a = m and b = n in mod_div_equality2, arith)

lemma mod_le_divisor[simp]: "0 < n \<Longrightarrow> m mod n \<le> (n::nat)"
  apply (drule mod_less_divisor [where m = m])
  apply simp
  done

subsubsection {* Quotient and Remainder *}

lemma divmod_rel_mult1_eq:
  "[| divmod_rel b c q r; c > 0 |]
   ==> divmod_rel (a*b) c (a*q + a*r div c) (a*r mod c)"
by (auto simp add: split_ifs mult_ac divmod_rel_def add_mult_distrib2)

lemma div_mult1_eq: "(a*b) div c = a*(b div c) + a*(b mod c) div (c::nat)"
apply (cases "c = 0", simp)
apply (blast intro: divmod_rel [THEN divmod_rel_mult1_eq, THEN div_eq])
done

lemma mod_mult1_eq: "(a*b) mod c = a*(b mod c) mod (c::nat)"
apply (cases "c = 0", simp)
apply (blast intro: divmod_rel [THEN divmod_rel_mult1_eq, THEN mod_eq])
done

lemma mod_mult1_eq': "(a*b) mod (c::nat) = ((a mod c) * b) mod c"
  apply (rule trans)
   apply (rule_tac s = "b*a mod c" in trans)
    apply (rule_tac [2] mod_mult1_eq)
   apply (simp_all add: mult_commute)
  done

lemma mod_mult_distrib_mod:
  "(a*b) mod (c::nat) = ((a mod c) * (b mod c)) mod c"
apply (rule mod_mult1_eq' [THEN trans])
apply (rule mod_mult1_eq)
done

lemma divmod_rel_add1_eq:
  "[| divmod_rel a c aq ar; divmod_rel b c bq br;  c > 0 |]
   ==> divmod_rel (a + b) c (aq + bq + (ar+br) div c) ((ar + br) mod c)"
by (auto simp add: split_ifs mult_ac divmod_rel_def add_mult_distrib2)

(*NOT suitable for rewriting: the RHS has an instance of the LHS*)
lemma div_add1_eq:
  "(a+b) div (c::nat) = a div c + b div c + ((a mod c + b mod c) div c)"
apply (cases "c = 0", simp)
apply (blast intro: divmod_rel_add1_eq [THEN div_eq] divmod_rel)
done

lemma mod_add1_eq: "(a+b) mod (c::nat) = (a mod c + b mod c) mod c"
apply (cases "c = 0", simp)
apply (blast intro: divmod_rel_add1_eq [THEN mod_eq] divmod_rel)
done

lemma mod_lemma: "[| (0::nat) < c; r < b |] ==> b * (q mod c) + r < b * c"
  apply (cut_tac m = q and n = c in mod_less_divisor)
  apply (drule_tac [2] m = "q mod c" in less_imp_Suc_add, auto)
  apply (erule_tac P = "%x. ?lhs < ?rhs x" in ssubst)
  apply (simp add: add_mult_distrib2)
  done

lemma divmod_rel_mult2_eq: "[| divmod_rel a b q r;  0 < b;  0 < c |]
      ==> divmod_rel a (b*c) (q div c) (b*(q mod c) + r)"
  by (auto simp add: mult_ac divmod_rel_def add_mult_distrib2 [symmetric] mod_lemma)

lemma div_mult2_eq: "a div (b*c) = (a div b) div (c::nat)"
  apply (cases "b = 0", simp)
  apply (cases "c = 0", simp)
  apply (force simp add: divmod_rel [THEN divmod_rel_mult2_eq, THEN div_eq])
  done

lemma mod_mult2_eq: "a mod (b*c) = b*(a div b mod c) + a mod (b::nat)"
  apply (cases "b = 0", simp)
  apply (cases "c = 0", simp)
  apply (auto simp add: mult_commute divmod_rel [THEN divmod_rel_mult2_eq, THEN mod_eq])
  done


subsubsection{*Cancellation of Common Factors in Division*}

lemma div_mult_mult_lemma:
    "[| (0::nat) < b;  0 < c |] ==> (c*a) div (c*b) = a div b"
  by (auto simp add: div_mult2_eq)

lemma div_mult_mult1 [simp]: "(0::nat) < c ==> (c*a) div (c*b) = a div b"
  apply (cases "b = 0")
  apply (auto simp add: linorder_neq_iff [of b] div_mult_mult_lemma)
  done

lemma div_mult_mult2 [simp]: "(0::nat) < c ==> (a*c) div (b*c) = a div b"
  apply (drule div_mult_mult1)
  apply (auto simp add: mult_commute)
  done


subsubsection{*Further Facts about Quotient and Remainder*}

lemma div_1 [simp]: "m div Suc 0 = m"
  by (induct m) (simp_all add: div_geq)


(* Monotonicity of div in first argument *)
lemma div_le_mono [rule_format (no_asm)]:
    "\<forall>m::nat. m \<le> n --> (m div k) \<le> (n div k)"
apply (case_tac "k=0", simp)
apply (induct "n" rule: nat_less_induct, clarify)
apply (case_tac "n<k")
(* 1  case n<k *)
apply simp
(* 2  case n >= k *)
apply (case_tac "m<k")
(* 2.1  case m<k *)
apply simp
(* 2.2  case m>=k *)
apply (simp add: div_geq diff_le_mono)
done

(* Antimonotonicity of div in second argument *)
lemma div_le_mono2: "!!m::nat. [| 0<m; m\<le>n |] ==> (k div n) \<le> (k div m)"
apply (subgoal_tac "0<n")
 prefer 2 apply simp
apply (induct_tac k rule: nat_less_induct)
apply (rename_tac "k")
apply (case_tac "k<n", simp)
apply (subgoal_tac "~ (k<m) ")
 prefer 2 apply simp
apply (simp add: div_geq)
apply (subgoal_tac "(k-n) div n \<le> (k-m) div n")
 prefer 2
 apply (blast intro: div_le_mono diff_le_mono2)
apply (rule le_trans, simp)
apply (simp)
done

lemma div_le_dividend [simp]: "m div n \<le> (m::nat)"
apply (case_tac "n=0", simp)
apply (subgoal_tac "m div n \<le> m div 1", simp)
apply (rule div_le_mono2)
apply (simp_all (no_asm_simp))
done

(* Similar for "less than" *)
lemma div_less_dividend [rule_format]:
     "!!n::nat. 1<n ==> 0 < m --> m div n < m"
apply (induct_tac m rule: nat_less_induct)
apply (rename_tac "m")
apply (case_tac "m<n", simp)
apply (subgoal_tac "0<n")
 prefer 2 apply simp
apply (simp add: div_geq)
apply (case_tac "n<m")
 apply (subgoal_tac "(m-n) div n < (m-n) ")
  apply (rule impI less_trans_Suc)+
apply assumption
  apply (simp_all)
done

declare div_less_dividend [simp]

text{*A fact for the mutilated chess board*}
lemma mod_Suc: "Suc(m) mod n = (if Suc(m mod n) = n then 0 else Suc(m mod n))"
apply (case_tac "n=0", simp)
apply (induct "m" rule: nat_less_induct)
apply (case_tac "Suc (na) <n")
(* case Suc(na) < n *)
apply (frule lessI [THEN less_trans], simp add: less_not_refl3)
(* case n \<le> Suc(na) *)
apply (simp add: linorder_not_less le_Suc_eq mod_geq)
apply (auto simp add: Suc_diff_le le_mod_geq)
done

lemma nat_mod_div_trivial [simp]: "m mod n div n = (0 :: nat)"
  by (cases "n = 0") auto

lemma nat_mod_mod_trivial [simp]: "m mod n mod n = (m mod n :: nat)"
  by (cases "n = 0") auto


subsubsection {* The Divides Relation *}

lemma dvd_1_left [iff]: "Suc 0 dvd k"
  unfolding dvd_def by simp

lemma dvd_1_iff_1 [simp]: "(m dvd Suc 0) = (m = Suc 0)"
  by (simp add: dvd_def)

lemma dvd_anti_sym: "[| m dvd n; n dvd m |] ==> m = (n::nat)"
  unfolding dvd_def
  by (force dest: mult_eq_self_implies_10 simp add: mult_assoc mult_eq_1_iff)

text {* @{term "op dvd"} is a partial order *}

interpretation dvd: order ["op dvd" "\<lambda>n m \<Colon> nat. n dvd m \<and> n \<noteq> m"]
  by unfold_locales (auto intro: dvd_refl dvd_trans dvd_anti_sym)

lemma dvd_diff: "[| k dvd m; k dvd n |] ==> k dvd (m-n :: nat)"
  unfolding dvd_def
  by (blast intro: diff_mult_distrib2 [symmetric])

lemma dvd_diffD: "[| k dvd m-n; k dvd n; n\<le>m |] ==> k dvd (m::nat)"
  apply (erule linorder_not_less [THEN iffD2, THEN add_diff_inverse, THEN subst])
  apply (blast intro: dvd_add)
  done

lemma dvd_diffD1: "[| k dvd m-n; k dvd m; n\<le>m |] ==> k dvd (n::nat)"
  by (drule_tac m = m in dvd_diff, auto)

lemma dvd_reduce: "(k dvd n + k) = (k dvd (n::nat))"
  apply (rule iffI)
   apply (erule_tac [2] dvd_add)
   apply (rule_tac [2] dvd_refl)
  apply (subgoal_tac "n = (n+k) -k")
   prefer 2 apply simp
  apply (erule ssubst)
  apply (erule dvd_diff)
  apply (rule dvd_refl)
  done

lemma dvd_mod: "!!n::nat. [| f dvd m; f dvd n |] ==> f dvd m mod n"
  unfolding dvd_def
  apply (case_tac "n = 0", auto)
  apply (blast intro: mod_mult_distrib2 [symmetric])
  done

lemma dvd_mod_imp_dvd: "[| (k::nat) dvd m mod n;  k dvd n |] ==> k dvd m"
  apply (subgoal_tac "k dvd (m div n) *n + m mod n")
   apply (simp add: mod_div_equality)
  apply (simp only: dvd_add dvd_mult)
  done

lemma dvd_mod_iff: "k dvd n ==> ((k::nat) dvd m mod n) = (k dvd m)"
  by (blast intro: dvd_mod_imp_dvd dvd_mod)

lemma dvd_mult_cancel: "!!k::nat. [| k*m dvd k*n; 0<k |] ==> m dvd n"
  unfolding dvd_def
  apply (erule exE)
  apply (simp add: mult_ac)
  done

lemma dvd_mult_cancel1: "0<m ==> (m*n dvd m) = (n = (1::nat))"
  apply auto
   apply (subgoal_tac "m*n dvd m*1")
   apply (drule dvd_mult_cancel, auto)
  done

lemma dvd_mult_cancel2: "0<m ==> (n*m dvd m) = (n = (1::nat))"
  apply (subst mult_commute)
  apply (erule dvd_mult_cancel1)
  done

lemma dvd_imp_le: "[| k dvd n; 0 < n |] ==> k \<le> (n::nat)"
  apply (unfold dvd_def, clarify)
  apply (simp_all (no_asm_use) add: zero_less_mult_iff)
  apply (erule conjE)
  apply (rule le_trans)
   apply (rule_tac [2] le_refl [THEN mult_le_mono])
   apply (erule_tac [2] Suc_leI, simp)
  done

lemma dvd_mult_div_cancel: "n dvd m ==> n * (m div n) = (m::nat)"
  apply (subgoal_tac "m mod n = 0")
   apply (simp add: mult_div_cancel)
  apply (simp only: dvd_eq_mod_eq_0)
  done

lemma le_imp_power_dvd: "!!i::nat. m \<le> n ==> i^m dvd i^n"
  apply (unfold dvd_def)
  apply (erule linorder_not_less [THEN iffD2, THEN add_diff_inverse, THEN subst])
  apply (simp add: power_add)
  done

lemma mod_add_left_eq: "((a::nat) + b) mod c = (a mod c + b) mod c"
  apply (rule trans [symmetric])
   apply (rule mod_add1_eq, simp)
  apply (rule mod_add1_eq [symmetric])
  done

lemma mod_add_right_eq: "(a+b) mod (c::nat) = (a + (b mod c)) mod c"
  apply (rule trans [symmetric])
   apply (rule mod_add1_eq, simp)
  apply (rule mod_add1_eq [symmetric])
  done

lemma nat_zero_less_power_iff [simp]: "(x^n > 0) = (x > (0::nat) | n=0)"
  by (induct n) auto

lemma power_le_dvd [rule_format]: "k^j dvd n --> i\<le>j --> k^i dvd (n::nat)"
  apply (induct j)
   apply (simp_all add: le_Suc_eq)
  apply (blast dest!: dvd_mult_right)
  done

lemma power_dvd_imp_le: "[|i^m dvd i^n;  (1::nat) < i|] ==> m \<le> n"
  apply (rule power_le_imp_le_exp, assumption)
  apply (erule dvd_imp_le, simp)
  done

lemma mod_eq_0_iff: "(m mod d = 0) = (\<exists>q::nat. m = d*q)"
  by (auto simp add: dvd_eq_mod_eq_0 [symmetric] dvd_def)

lemmas mod_eq_0D [dest!] = mod_eq_0_iff [THEN iffD1]

(*Loses information, namely we also have r<d provided d is nonzero*)
lemma mod_eqD: "(m mod d = r) ==> \<exists>q::nat. m = r + q*d"
  apply (cut_tac a = m in mod_div_equality)
  apply (simp only: add_ac)
  apply (blast intro: sym)
  done

lemma split_div:
 "P(n div k :: nat) =
 ((k = 0 \<longrightarrow> P 0) \<and> (k \<noteq> 0 \<longrightarrow> (!i. !j<k. n = k*i + j \<longrightarrow> P i)))"
 (is "?P = ?Q" is "_ = (_ \<and> (_ \<longrightarrow> ?R))")
proof
  assume P: ?P
  show ?Q
  proof (cases)
    assume "k = 0"
    with P show ?Q by simp
  next
    assume not0: "k \<noteq> 0"
    thus ?Q
    proof (simp, intro allI impI)
      fix i j
      assume n: "n = k*i + j" and j: "j < k"
      show "P i"
      proof (cases)
        assume "i = 0"
        with n j P show "P i" by simp
      next
        assume "i \<noteq> 0"
        with not0 n j P show "P i" by(simp add:add_ac)
      qed
    qed
  qed
next
  assume Q: ?Q
  show ?P
  proof (cases)
    assume "k = 0"
    with Q show ?P by simp
  next
    assume not0: "k \<noteq> 0"
    with Q have R: ?R by simp
    from not0 R[THEN spec,of "n div k",THEN spec, of "n mod k"]
    show ?P by simp
  qed
qed

lemma split_div_lemma:
  assumes "0 < n"
  shows "n * q \<le> m \<and> m < n * Suc q \<longleftrightarrow> q = ((m\<Colon>nat) div n)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  with mult_div_cancel have nq: "n * q = m - (m mod n)" by simp
  then have A: "n * q \<le> m" by simp
  have "n - (m mod n) > 0" using mod_less_divisor assms by auto
  then have "m < m + (n - (m mod n))" by simp
  then have "m < n + (m - (m mod n))" by simp
  with nq have "m < n + n * q" by simp
  then have B: "m < n * Suc q" by simp
  from A B show ?lhs ..
next
  assume P: ?lhs
  then have "divmod_rel m n q (m - n * q)"
    unfolding divmod_rel_def by (auto simp add: mult_ac)
  then show ?rhs using divmod_rel by (rule divmod_rel_unique_div)
qed

theorem split_div':
  "P ((m::nat) div n) = ((n = 0 \<and> P 0) \<or>
   (\<exists>q. (n * q \<le> m \<and> m < n * (Suc q)) \<and> P q))"
  apply (case_tac "0 < n")
  apply (simp only: add: split_div_lemma)
  apply simp_all
  done

lemma split_mod:
 "P(n mod k :: nat) =
 ((k = 0 \<longrightarrow> P n) \<and> (k \<noteq> 0 \<longrightarrow> (!i. !j<k. n = k*i + j \<longrightarrow> P j)))"
 (is "?P = ?Q" is "_ = (_ \<and> (_ \<longrightarrow> ?R))")
proof
  assume P: ?P
  show ?Q
  proof (cases)
    assume "k = 0"
    with P show ?Q by simp
  next
    assume not0: "k \<noteq> 0"
    thus ?Q
    proof (simp, intro allI impI)
      fix i j
      assume "n = k*i + j" "j < k"
      thus "P j" using not0 P by(simp add:add_ac mult_ac)
    qed
  qed
next
  assume Q: ?Q
  show ?P
  proof (cases)
    assume "k = 0"
    with Q show ?P by simp
  next
    assume not0: "k \<noteq> 0"
    with Q have R: ?R by simp
    from not0 R[THEN spec,of "n div k",THEN spec, of "n mod k"]
    show ?P by simp
  qed
qed

theorem mod_div_equality': "(m::nat) mod n = m - (m div n) * n"
  apply (rule_tac P="%x. m mod n = x - (m div n) * n" in
    subst [OF mod_div_equality [of _ n]])
  apply arith
  done

lemma div_mod_equality':
  fixes m n :: nat
  shows "m div n * n = m - m mod n"
proof -
  have "m mod n \<le> m mod n" ..
  from div_mod_equality have 
    "m div n * n + m mod n - m mod n = m - m mod n" by simp
  with diff_add_assoc [OF `m mod n \<le> m mod n`, of "m div n * n"] have
    "m div n * n + (m mod n - m mod n) = m - m mod n"
    by simp
  then show ?thesis by simp
qed


subsubsection {*An ``induction'' law for modulus arithmetic.*}

lemma mod_induct_0:
  assumes step: "\<forall>i<p. P i \<longrightarrow> P ((Suc i) mod p)"
  and base: "P i" and i: "i<p"
  shows "P 0"
proof (rule ccontr)
  assume contra: "\<not>(P 0)"
  from i have p: "0<p" by simp
  have "\<forall>k. 0<k \<longrightarrow> \<not> P (p-k)" (is "\<forall>k. ?A k")
  proof
    fix k
    show "?A k"
    proof (induct k)
      show "?A 0" by simp  -- "by contradiction"
    next
      fix n
      assume ih: "?A n"
      show "?A (Suc n)"
      proof (clarsimp)
        assume y: "P (p - Suc n)"
        have n: "Suc n < p"
        proof (rule ccontr)
          assume "\<not>(Suc n < p)"
          hence "p - Suc n = 0"
            by simp
          with y contra show "False"
            by simp
        qed
        hence n2: "Suc (p - Suc n) = p-n" by arith
        from p have "p - Suc n < p" by arith
        with y step have z: "P ((Suc (p - Suc n)) mod p)"
          by blast
        show "False"
        proof (cases "n=0")
          case True
          with z n2 contra show ?thesis by simp
        next
          case False
          with p have "p-n < p" by arith
          with z n2 False ih show ?thesis by simp
        qed
      qed
    qed
  qed
  moreover
  from i obtain k where "0<k \<and> i+k=p"
    by (blast dest: less_imp_add_positive)
  hence "0<k \<and> i=p-k" by auto
  moreover
  note base
  ultimately
  show "False" by blast
qed

lemma mod_induct:
  assumes step: "\<forall>i<p. P i \<longrightarrow> P ((Suc i) mod p)"
  and base: "P i" and i: "i<p" and j: "j<p"
  shows "P j"
proof -
  have "\<forall>j<p. P j"
  proof
    fix j
    show "j<p \<longrightarrow> P j" (is "?A j")
    proof (induct j)
      from step base i show "?A 0"
        by (auto elim: mod_induct_0)
    next
      fix k
      assume ih: "?A k"
      show "?A (Suc k)"
      proof
        assume suc: "Suc k < p"
        hence k: "k<p" by simp
        with ih have "P k" ..
        with step k have "P (Suc k mod p)"
          by blast
        moreover
        from suc have "Suc k mod p = Suc k"
          by simp
        ultimately
        show "P (Suc k)" by simp
      qed
    qed
  qed
  with j show ?thesis by blast
qed

end
