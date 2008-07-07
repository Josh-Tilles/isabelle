(*  Title:      HOL/Library/NatPair.thy
    ID:         $Id$
    Author:     Stefan Richter
    Copyright   2003 Technische Universitaet Muenchen
*)

header {* Pairs of Natural Numbers *}

theory NatPair
imports Plain "~~/src/HOL/Presburger"
begin

text{*
  An injective function from @{text "\<nat>\<twosuperior>"} to @{text \<nat>}.  Definition
  and proofs are from \cite[page 85]{Oberschelp:1993}.
*}

definition
  nat2_to_nat:: "(nat * nat) \<Rightarrow> nat" where
  "nat2_to_nat pair = (let (n,m) = pair in (n+m) * Suc (n+m) div 2 + n)"

lemma dvd2_a_x_suc_a: "2 dvd a * (Suc a)"
proof (cases "2 dvd a")
  case True
  then show ?thesis by (rule dvd_mult2)
next
  case False
  then have "Suc (a mod 2) = 2" by (simp add: dvd_eq_mod_eq_0)
  then have "Suc a mod 2 = 0" by (simp add: mod_Suc)
  then have "2 dvd Suc a" by (simp only:dvd_eq_mod_eq_0)
  then show ?thesis by (rule dvd_mult)
qed

lemma
  assumes eq: "nat2_to_nat (u,v) = nat2_to_nat (x,y)"
  shows nat2_to_nat_help: "u+v \<le> x+y"
proof (rule classical)
  assume "\<not> ?thesis"
  then have contrapos: "x+y < u+v"
    by simp
  have "nat2_to_nat (x,y) < (x+y) * Suc (x+y) div 2 + Suc (x + y)"
    by (unfold nat2_to_nat_def) (simp add: Let_def)
  also have "\<dots> = (x+y)*Suc(x+y) div 2 + 2 * Suc(x+y) div 2"
    by (simp only: div_mult_self1_is_m)
  also have "\<dots> = (x+y)*Suc(x+y) div 2 + 2 * Suc(x+y) div 2
    + ((x+y)*Suc(x+y) mod 2 + 2 * Suc(x+y) mod 2) div 2"
  proof -
    have "2 dvd (x+y)*Suc(x+y)"
      by (rule dvd2_a_x_suc_a)
    then have "(x+y)*Suc(x+y) mod 2 = 0"
      by (simp only: dvd_eq_mod_eq_0)
    also
    have "2 * Suc(x+y) mod 2 = 0"
      by (rule mod_mult_self1_is_0)
    ultimately have
      "((x+y)*Suc(x+y) mod 2 + 2 * Suc(x+y) mod 2) div 2 = 0"
      by simp
    then show ?thesis
      by simp
  qed
  also have "\<dots> = ((x+y)*Suc(x+y) + 2*Suc(x+y)) div 2"
    by (rule div_add1_eq [symmetric])
  also have "\<dots> = ((x+y+2)*Suc(x+y)) div 2"
    by (simp only: add_mult_distrib [symmetric])
  also from contrapos have "\<dots> \<le> ((Suc(u+v))*(u+v)) div 2"
    by (simp only: mult_le_mono div_le_mono)
  also have "\<dots> \<le> nat2_to_nat (u,v)"
    by (unfold nat2_to_nat_def) (simp add: Let_def)
  finally show ?thesis
    by (simp only: eq)
qed

theorem nat2_to_nat_inj: "inj nat2_to_nat"
proof -
  {
    fix u v x y
    assume eq1: "nat2_to_nat (u,v) = nat2_to_nat (x,y)"
    then have "u+v \<le> x+y" by (rule nat2_to_nat_help)
    also from eq1 [symmetric] have "x+y \<le> u+v"
      by (rule nat2_to_nat_help)
    finally have eq2: "u+v = x+y" .
    with eq1 have ux: "u=x"
      by (simp add: nat2_to_nat_def Let_def)
    with eq2 have vy: "v=y" by simp
    with ux have "(u,v) = (x,y)" by simp
  }
  then have "\<And>x y. nat2_to_nat x = nat2_to_nat y \<Longrightarrow> x=y" by fast
  then show ?thesis unfolding inj_on_def by simp
qed

end
