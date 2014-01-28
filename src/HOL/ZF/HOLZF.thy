(*  Title:      HOL/ZF/HOLZF.thy
    Author:     Steven Obua

Axiomatizes the ZFC universe as an HOL type.  See "Partizan Games in
Isabelle/HOLZF", available from http://www4.in.tum.de/~obua/partizan
*)

theory HOLZF 
imports Main
begin

typedecl ZF

axiomatization
  Empty :: ZF and (* @TODO add empty-set symbol *)
  Elem :: "ZF \<Rightarrow> ZF \<Rightarrow> bool" and
  Sum :: "ZF \<Rightarrow> ZF" and
  Power :: "ZF \<Rightarrow> ZF" and (* @TODO add scripty "P" *)
  Replace :: "ZF \<Rightarrow> (ZF \<Rightarrow> ZF) \<Rightarrow> ZF" and
  Inf :: ZF

definition Upair :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "Upair a b \<equiv> Replace (Power (Power Empty)) (\<lambda> x. if x = Empty then a else b)"

definition Singleton :: "ZF \<Rightarrow> ZF" where
  "Singleton x \<equiv> Upair x x"

definition union :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "union A B \<equiv> Sum (Upair A B)"

definition SucNat:: "ZF \<Rightarrow> ZF" where
  "SucNat x \<equiv> union x (Singleton x)"

definition subset :: "ZF \<Rightarrow> ZF \<Rightarrow> bool" where
  "subset A B \<longleftrightarrow> (\<forall> x. Elem x A \<longrightarrow> Elem x B)"

axiomatization where
  Empty: "\<not>(Elem x Empty)" and
  Ext: "(x = y) \<longleftrightarrow> (\<forall> z. Elem z x = Elem z y)" and
  Sum: "Elem z (Sum x) \<longleftrightarrow> (\<exists> y. Elem z y \<and> Elem y x)" and
  Power: "Elem y (Power x) \<longleftrightarrow> (subset y x)" and
  Replace: "Elem b (Replace A f) \<longleftrightarrow> (\<exists> a. Elem a A \<and> b = f a)" and
  Regularity: "A \<noteq> Empty \<longrightarrow> (\<exists> x. Elem x A \<and> (\<forall> y. Elem y x \<longrightarrow> Not (Elem y A)))" and
  Infinity: "Elem Empty Inf \<and> (\<forall> x. Elem x Inf \<longrightarrow> Elem (SucNat x) Inf)"

definition Sep :: "ZF \<Rightarrow> (ZF \<Rightarrow> bool) \<Rightarrow> ZF" where
  "Sep A p \<equiv> (if (\<forall>x. Elem x A \<longrightarrow> Not (p x)) then Empty else 
    (let z = (\<some> x. Elem x A \<and> p x) in
     let f = (\<lambda> y. (if p y then y else z)) in 
     Replace A f))" 

thm Power[unfolded subset_def]

theorem Sep: "Elem b (Sep A p) \<longleftrightarrow> (Elem b A \<and> p b)"
  apply (auto simp add: Sep_def Empty)
  apply (auto simp add: Replace)
  apply (rule someI2)
  apply auto
  apply (rule someI2)
  apply auto
  oops
lemma "Elem b (Sep A p)"
  apply (unfold Sep_def)
  apply (split split_if)
  apply (rule conjI)
  apply auto oops
lemma "Elem b (Sep A p) \<longleftrightarrow> (Elem b A \<and> p b)"
proof -
  fix x and a
  assume 3: "Elem x A" and 4: "p x"
     and 5: "Elem a A" and 6: "\<not> (p a)"
  have 1: "Elem (SOME x. Elem x A \<and> p x) A"
    apply (rule someI2)
      apply (rule conjI)
        using `Elem x A` apply assumption
      using `p x` apply assumption
    apply (erule conjE)
    apply assumption
    done
  have 2: "p (SOME x. Elem x A \<and> p x)"
    apply (rule someI2)
      apply (rule conjI)
        using `Elem x A` apply assumption
      using `p x` apply assumption
    apply (erule conjE)
    apply assumption
    done
 oops

lemma
  fixes p q :: "'a \<Rightarrow> bool"
  assumes "\<exists>x. q x" and "q x \<Longrightarrow> p x"
  shows "p (\<some> y. q y)"
  oops

(*
CRUCIAL
*)
thm Replace

theorem Sep: "Elem b (Sep A p) \<longleftrightarrow> (Elem b A \<and> p b)"
  unfolding Sep_def
proof (split split_if) (* @TODO figure out which `[of \<dots>]` or `[OF \<dots>]` would work? *)
  have "Elem b (Sep A p) \<longleftrightarrow> Elem b (
    (if (\<forall>x. Elem x A \<longrightarrow> Not (p x))
      then Empty
      else (let z = (\<some> x. Elem x A \<and> p x) in
             let f = (\<lambda> y. (if p y then y else z)) in 
              Replace A f))
)" by (simp only: Sep_def)
  also have "\<dots> \<longleftrightarrow> (
((\<forall>x. Elem x A \<longrightarrow> \<not> p x) \<longrightarrow> Elem b Empty) 
 \<and>
 (\<not> (\<forall>x. Elem x A \<longrightarrow> \<not> p x) \<longrightarrow> Elem b (let z = (\<some> x. Elem x A \<and> p x) in let f = (\<lambda> y. (if p y then y else z)) in Replace A f))
)" by (rule split_if)
  also have "\<dots> = (Elem b A \<and> p b)"
thm split_if[where ?P="Elem b" and ?Q="\<forall> x. Elem x A \<longrightarrow> \<not>(p x)" and ?x=Empty]
  show "((\<forall>x. Elem x A \<longrightarrow> \<not> p x) \<longrightarrow> Elem b Empty = (Elem b A \<and> p b)) \<and>
    (\<not> (\<forall>x. Elem x A \<longrightarrow> \<not> p x) \<longrightarrow>
     Elem b (let z = SOME x. Elem x A \<and> p x in Let (\<lambda>y. if p y then y else z) (Replace A)) =
     (Elem b A \<and> p b))"
  proof (rule conjI)
    
  
  have "Elem b (Sep A p) \<longleftrightarrow> Elem b ((if (\<forall>x. Elem x A \<longrightarrow> Not (p x)) then Empty else 
(let z = (\<some> x. Elem x A \<and> p x) in
 let f = (\<lambda> y. (if p y then y else z)) in 
 Replace A f)))" by (unfold Sep_def) (rule refl)
  
  also have "\<dots> \<longleftrightarrow> ((\<forall>x. Elem x A \<longrightarrow> \<not> p x) \<longrightarrow> Elem b Empty) \<and>
    (\<not> (\<forall>x. Elem x A \<longrightarrow> \<not> p x) \<longrightarrow>
     Elem b (let z = SOME x. Elem x A \<and> p x in Let (\<lambda>y. if p y then y else z) (Replace A)))"
apply (split split_if)
oops

theorem Sep: "Elem b (Sep A p) \<longleftrightarrow> (Elem b A \<and> p b)"
proof (rule iffI)
  assume left_premise: "Elem b (Sep A p)"
  show "Elem b A \<and> p b"
  proof -(* (rule conjI) *)
    from `Elem b (Sep A p)` 
     have unfolded_premise: "Elem b (if \<forall>x. Elem x A \<longrightarrow> \<not> p x then Empty else 
                                          let z = \<some> x. Elem x A \<and> p x in let f = (\<lambda> y. (if p y then y else z)) in Replace A f)"
     by (simp only: Sep_def)
    have "\<not>(\<forall>x. Elem x A \<longrightarrow> \<not>(p x))"
    proof (rule notI)
      assume "\<forall>x. Elem x A \<longrightarrow> \<not>(p x)"
      with unfolded_premise (*have "Elem b
     (if True then Empty
      else let z = SOME x. Elem x A \<and> p x in Let (\<lambda>y. if p y then y else z) (Replace A))" by simp (* @TODO Cf. "congruence rule": Q \<equiv> ?c \<Longrightarrow> if Q then x else y \<equiv> if ?c then x else y *)

      hence*) have "Elem b Empty" by simp
      with Empty show False by (simp only: HOL.simp_thms(27))
    qed
    with unfolded_premise
     have "Elem b (let z = \<some> x. Elem x A \<and> p x in let f = (\<lambda> y. (if p y then y else z)) in Replace A f)"
     by (simp only: if_False)
    hence "Elem b (let z = \<some> x. Elem x A \<and> p x in Replace A (\<lambda> y. if p y then y else z))" by (unfold Let_def)
    hence simplified_premise: "Elem b (Replace A (\<lambda> y. if p y then y else \<some> x. Elem x A \<and> p x))" by (unfold Let_def)
    hence "\<exists> i. Elem i A \<and> b = ((\<lambda> y. if p y then y else \<some> x. Elem x A \<and> p x) i)" by (simp only: Replace)
    hence "\<exists> i. Elem i A \<and> b = (if p i then i else \<some> x. Elem x A \<and> p x)" .

obtain w where
    
    from `\<not>(\<forall>x. Elem x A \<longrightarrow> \<not>(p x))`
     obtain z where "Elem z A" and "p z"
     by blast
    
    from `\<not>(\<forall>x. Elem x A \<longrightarrow> \<not>(p x))` have tmpex: "\<exists>x. Elem x A \<and> p x" by blast
    thm someI2
    find_theorems "(\<some>_. _) = _"
thm HOL.simp_thms(27)
 have "Elem b Empty"
    hence "Elem b (let z = \<some> x. Elem x A \<and> p x in
                    let f = \<lambda> y. if p y then y else z in
                     Replace A f)"
    { assume "\<forall>x. Elem x A \<longrightarrow> \<not> p x"
      hence "Elem b Empty" using tmp by simp
      with Empty have False by (simp only: HOL.simp_thms(27)) }
    hence "\<not>(\<forall>x. Elem x A \<longrightarrow> \<not> p x)" by (rule notI)
    hence tmp2: "Elem b (let z = \<some> x. Elem x A \<and> p x in
                    let f = \<lambda> y. if p y then y else z in
                     Replace A f)" using tmp by (simp only: if_False)
    let ?f = "(let z = \<some> x. Elem x A \<and> p x in (\<lambda> y. if p y then y else z))"
    from tmp2 have "Elem b (Replace A ?f)" by (simp only: Let_def)
    hence tmp3: "\<exists>x. Elem x A \<and> b = ?f x" by (simp only: Replace)
    thus "Elem b A \<and> p b"
    proof -
      fix t
      assume "Elem t A" and "b = ?f t"
      from `b = ?f t` have "b = (let z = SOME x. Elem x A \<and> p x in if p t then t else z)" by (unfold Let_def)
      hence b_eq: "b = (if p t then t else (\<some> x. Elem x A \<and> p x))" by (unfold Let_def)
      hence "p b"
      proof (cases "p t")
        assume "p t"
        hence "b = t" using b_eq by simp (* @TODO which? *)
        thus "p b" by (simp only: `p t`)
      next
        assume "\<not>(p t)"
        hence b_eq_some: "b = (\<some> x. Elem x A \<and> p x)" using b_eq by simp (* @TODO which? *)
        have "p (\<some> x. Elem x A \<and> p x)"
          apply (rule someI2)
          defer
          apply (erule conjE)
          apply assumption
        proof -
          show "Elem t A \<and> p t" apply (rule conjI)
 sorry
        thus "p b" using b_eq_some by simp (* @TODO which? *)
      qed
        thm some_equality
        show "b = (if p t then t else SOME x. Elem x A \<and> p x) \<Longrightarrow> p t \<Longrightarrow> p b" by simp

      proof -
        assume "b = (SOME x. Elem x A \<and> p x)"
           and "\<not>(p t)"
        from 
        show "p (SOME x. Elem x A \<and> p x)"
          using `b = (SOME x. Elem x A \<and> p x)` apply simp
          apply (simp only: `b = (SOME x. Elem x A \<and> p x)`)
        apply (subst `b = (SOME x. Elem x A \<and> p x)`)
        apply (rule someI)
thm someI
        apply (simp only: split_if)
        apply (erule conjE)
      

    proof -
      obtain t where t: "Elem t A \<and> b = ?f t" using tmp3 by auto (* @TODO cheap *)
      from t have "Elem t A" by (rule conjE)
      from t have "b = ?f t" by (rule conjE)
       
      hence "p b"
        apply (simp only: Let_def)
        apply cases
        apply (simp only: some_eq_ex)
        apply (rule someI2, auto)
        thm some_equality
        apply (simp only: someI2)
      have "p (?f t)"
        apply (simp only: Let_def)
        apply (split split_if)
        apply auto
        apply (rule someI)
        thm someI2
      
      hence "Elem x A" and "b = ?f x" apply (rule conjE) apply assumption using x apply (rule conjE) apply assumption
    thm exE
    thm Replace
    have "Elem b (let z = \<some> x. Elem x A \<and> p x in
                    let f = \<lambda> y. if p y then y else z in
                     Replace A f)
          =
          Elem b (Replace A
                          (let z = \<some> x. Elem x A \<and> p x in (\<lambda> y. if p y then y else z)))"
      by (simp only: Let_def)
    have "Elem b (let z = \<some> x. Elem x A \<and> p x in
                   let f = \<lambda> y. if p y then y else z in
                    Replace A f)
          =
          Elem b (Replace A ?f)"
      by (simp only: Let_def)
    also have "\<dots> = (\<exists>a. Elem a A \<and> b = (?f a))" by (rule Replace)
(*
    also have "\<dots> = (\<exists>a. Elem a A \<and> b = ((let z = \<some> x. Elem x A \<and> p x in (\<lambda> y. if p y then y else z))) a)"
      by (rule Replace)
*)
    also have "\<dots> = (\<exists>a. Elem a A \<and> b = (?f a))" by (rule Replace)
thm someI2
    thm Replace[of b A "let z = \<some> x. Elem x A \<and> p x in (\<lambda> y. if p y then y else z)"]
thm Replace
    
    
    hence "\<exists>x. Elem x A \<and> p x" by auto (* @TODO cheap? *)
thm split_if
      then obtain c where "Elem c A \<and> p c" by (rule exE)
thm spec
thm FalseE
find_theorems "?P \<and> \<not>?P"
    have "\<forall>x. Elem x A \<longrightarrow> Not (p x)"
    proof (rule ccontr)
oops
theorem Sep: "Elem b (Sep A p) \<longleftrightarrow> (Elem b A \<and> p b)" sorry

lemma subset_empty: "subset Empty A"
  by (simp add: subset_def Empty)

thm split_if[of "\<lambda>y. x = y" B a b] (* key! *)

lemma "Elem x (Upair a b) \<longleftrightarrow> (x=a \<or> x=b)"
  apply (auto simp add: Upair_def Replace)
    apply (rule exI[where x=Empty])
    apply (simp add: Power subset_empty)
  apply (rule exI[where x="Power Empty"])
  apply (auto)
  apply (auto simp add: Ext Power subset_def Empty)
  apply (drule spec[where x=Empty], simp add: Empty)+
  oops


theorem Upair: "Elem x (Upair a b) \<longleftrightarrow> (x = a \<or> x = b)"
  apply (simp only: Upair_def Replace)
  apply (subst exI)
  (* apply (subst split_if) *)
  apply (simp only: split_if)
  apply auto
  
  apply (unfold Upair_def)
  apply (simp only: Replace)
  apply (rule iffI)
  apply (rule disjCI)
  apply (erule exE)
  apply (erule conjE)
  
thm disjCI
thm exI[where x=Empty]
thm exI[where x="Power Empty"]
thm spec[where x=Empty]
  apply auto
  apply (rule exI[where x=Empty])
  apply (simp only: Power)
  apply (simp only: subset_empty)
  apply simp
proof -
  have "\<exists> Y. subset Y (Power Empty)"
  apply (rule exI)
  apply (rule subset_empty) done
  have "Upair a b = (Replace (Power (Power Empty)) (\<lambda> x. if x = Empty then a else b))" by (unfold Upair_def) (rule refl)
  hence "Elem x (Upair a b) \<longleftrightarrow> Elem x \<dots>" by simp
  also have "\<dots> \<longleftrightarrow> (\<exists> A. Elem A (Power (Power Empty)) \<and> x = (if A = Empty then a else b))" by (simp only: Replace)
(*  also have "\<dots> \<longleftrightarrow> (\<exists> Y. subset Y (Power Empty) \<and> x = (if Y = Empty then a else b))" by (simp only: Power)
  also have "\<dots> \<longleftrightarrow> (\<exists> Y. (\<forall> w. Elem w Y \<longrightarrow> Elem w (Power Empty)) \<and> x = (if Y = Empty then a else b))" by (simp only: subset_def)
  also have "\<dots> \<longleftrightarrow> (\<exists> Y. (\<forall> w. Elem w Y \<longrightarrow> subset w Empty) \<and> x = (if Y = Empty then a else b))" by (simp only: Power)
*)  also have "\<dots> \<longleftrightarrow> (x=a \<or> x=b)"
  proof -
    fix A :: ZF
    have "Elem A (Power (Power Empty)) \<longleftrightarrow> subset A (Power Empty)" by (subst Power) (rule refl)
    also have "\<dots> \<longleftrightarrow> (\<forall> y. Elem y A \<longrightarrow> Elem y (Power Empty))" by (unfold subset_def) (rule refl)
    also have "\<dots> \<longleftrightarrow> (\<forall> y. Elem y A \<longrightarrow> subset y Empty)" by (simp only: Power)
    also have "\<dots> \<longleftrightarrow> (\<forall> y. Elem y A \<longrightarrow> (\<forall> z. Elem z y \<longrightarrow> Elem z Empty))" by (simp only: subset_def)
    also have "\<dots> \<longleftrightarrow> (\<forall> y. Elem y A \<longrightarrow> (\<forall> z. Elem z y \<longrightarrow> False))" by (subst Empty) (rule refl)
    also have "\<dots> \<longleftrightarrow> (\<forall> y. Elem y A \<longrightarrow> \<not>(\<exists> z. Elem z y))" by auto (* @TODO *)
    
    

 apply auto apply (rule exI) apply (auto simp add: Power subset_empty Empty) apply (rule exI) apply auto

  thm exI[where x="Power Empty"]
  (* have "subset Y (Power Empty) \<longleftrightarrow> (\<forall> y. Elem y Y \<longrightarrow> Elem y (Power Empty))" by (simp only: subset_def *)
  also have "\<dots> = (\<exists> Y. (\<forall> y. Elem y Y \<longrightarrow> Elem y (Power Empty)) \<and> x = (if Y = Empty then a else b))" by (simp only: subset_def)
  also have "\<dots> = (\<exists> Y. (\<forall> y. Elem y Y \<longrightarrow> Elem y (Power Empty)) \<and> (x = a \<or> x = b))" apply simp
  have "Elem x (Upair a b) = Elem x (Replace (Power (Power Empty)) (\<lambda>x. if x = Empty then a else b))"
  apply (auto simp add: Upair_def Replace)
  apply (rule exI[where x=Empty])
  apply (simp add: Power subset_empty)
  apply (rule exI[where x="Power Empty"])
  apply (auto)
  apply (auto simp add: Ext Power subset_def Empty)
  apply (drule spec[where x=Empty], simp add: Empty)+
  done
  oops
lemma Upair: "Elem x (Upair a b) \<longleftrightarrow> (x = a \<or> x = b)" sorry

lemma Singleton: "Elem x (Singleton y) \<longleftrightarrow> x = y"
  by (simp add: Singleton_def Upair)

definition Opair :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "Opair a b \<equiv> Upair (Upair a a) (Upair a b)"

lemma Upair_singleton: "(Upair a a = Upair c d) \<longleftrightarrow> (a = c \<and> a = d)"
  by (auto simp add: Ext[where x="Upair a a"] Upair)

lemma Upair_fsteq: "(Upair a b = Upair a c) \<longleftrightarrow> ((a = b \<and> a = c) \<or> (b = c))"
  by (auto simp add: Ext[where x="Upair a b"] Upair)

lemma Upair_comm: "Upair a b = Upair b a"
  by (auto simp add: Ext Upair)

theorem Opair: "(Opair a b = Opair c d) \<longleftrightarrow> (a = c \<and> b = d)"
  proof -
    have fst: "(Opair a b = Opair c d) \<Longrightarrow> a = c"
      apply (simp add: Opair_def)
      apply (simp add: Ext[where x="Upair (Upair a a) (Upair a b)"])
      apply (drule spec[where x="Upair a a"])
      apply (auto simp add: Upair Upair_singleton)
      done
    show ?thesis
      apply (auto)
      apply (erule fst)
      apply (frule fst)
      apply (auto simp add: Opair_def Upair_fsteq)
      done
  qed

definition Replacement :: "ZF \<Rightarrow> (ZF \<Rightarrow> ZF option) \<Rightarrow> ZF" where
  "Replacement A f \<equiv> Replace (Sep A (\<lambda> a. f a \<noteq> None)) (the \<circ> f)"

theorem Replacement: "Elem y (Replacement A f) \<longleftrightarrow> (\<exists> x. Elem x A \<and> f x = Some y)"
  by (auto simp add: Replacement_def Replace Sep) 

definition Fst :: "ZF \<Rightarrow> ZF" where
  "Fst q \<equiv> \<some> x. \<exists> y. q = Opair x y"

definition Snd :: "ZF \<Rightarrow> ZF" where
  "Snd q \<equiv> \<some> y. \<exists> x. q = Opair x y"
thm someI2
theorem Fst: "Fst (Opair x y) = x"
  apply (simp add: Fst_def)
  apply (rule someI2)
  apply (simp_all add: Opair)
  done

theorem Snd: "Snd (Opair x y) = y"
  apply (simp add: Snd_def)
  apply (rule someI2)
  apply (simp_all add: Opair)
  done

definition isOpair :: "ZF \<Rightarrow> bool" where
  "isOpair q \<longleftrightarrow> (\<exists> x y. q = Opair x y)"

lemma isOpair: "isOpair (Opair x y) = True"
  by (auto simp add: isOpair_def)

lemma FstSnd: "isOpair x \<Longrightarrow> Opair (Fst x) (Snd x) = x"
  by (auto simp add: isOpair_def Fst Snd)
  
definition CartProd :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "CartProd A B \<equiv> Sum(Replace A (\<lambda> a. Replace B (\<lambda> b. Opair a b)))"

lemma CartProd: "Elem x (CartProd A B) = (\<exists> a b. Elem a A \<and> Elem b B \<and> x = (Opair a b))"
  apply (auto simp add: CartProd_def Sum Replace)
  apply (rule_tac x="Replace B (Opair a)" in exI)
  apply (auto simp add: Replace)
  done

definition explode :: "ZF \<Rightarrow> ZF set" where
  "explode z \<equiv> { x. Elem x z }"

lemma explode_Empty: "(explode x = {}) = (x = Empty)"
  by (auto simp add: explode_def Ext Empty)

lemma explode_Elem: "(x \<in> explode X) = (Elem x X)"
  by (simp add: explode_def)

lemma Elem_explode_in: "\<lbrakk> Elem a A; explode A \<subseteq> B\<rbrakk> \<Longrightarrow> a \<in> B"
  by (auto simp add: explode_def)

lemma explode_CartProd_eq: "explode (CartProd a b) = (\<lambda> (x,y). Opair x y) ` ((explode a) \<times> (explode b))"
  by (simp add: explode_def set_eq_iff CartProd image_def)

lemma explode_Repl_eq: "explode (Replace A f) = image f (explode A)"
  by (simp add: explode_def Replace image_def)

definition Domain :: "ZF \<Rightarrow> ZF" where
  "Domain f \<equiv> Replacement f (\<lambda> p. if isOpair p then Some (Fst p) else None)"

definition Range :: "ZF \<Rightarrow> ZF" where
  "Range f \<equiv> Replacement f (\<lambda> p. if isOpair p then Some (Snd p) else None)"

theorem Domain: "Elem x (Domain f) = (\<exists> y. Elem (Opair x y) f)"
  apply (auto simp add: Domain_def Replacement)
  apply (rule_tac x="Snd x" in exI)
  apply (simp add: FstSnd)
  apply (rule_tac x="Opair x y" in exI)
  apply (simp add: isOpair Fst)
  done

theorem Range: "Elem y (Range f) = (\<exists> x. Elem (Opair x y) f)"
  apply (auto simp add: Range_def Replacement)
  apply (rule_tac x="Fst x" in exI)
  apply (simp add: FstSnd)
  apply (rule_tac x="Opair x y" in exI)
  apply (simp add: isOpair Snd)
  done

theorem union: "Elem x (union A B) = (Elem x A | Elem x B)"
  by (auto simp add: union_def Sum Upair)

definition Field :: "ZF \<Rightarrow> ZF" where
  "Field A \<equiv> union (Domain A) (Range A)"

definition app :: "ZF \<Rightarrow> ZF => ZF" (infixl "\<acute>" 90) --{*function application*} where
  "f \<acute> x \<equiv> (THE y. Elem (Opair x y) f)"

definition isFun :: "ZF \<Rightarrow> bool" where
  "isFun f \<longleftrightarrow> (\<forall> x y1 y2. Elem (Opair x y1) f \<and> Elem (Opair x y2) f \<longrightarrow> y1 = y2)"

definition Lambda :: "ZF \<Rightarrow> (ZF \<Rightarrow> ZF) \<Rightarrow> ZF" where
  "Lambda A f \<equiv> Replace A (\<lambda> x. Opair x (f x))"

lemma Lambda_app: "Elem x A \<Longrightarrow> (Lambda A f)\<acute>x = f x"
  by (simp add: app_def Lambda_def Replace Opair)

lemma isFun_Lambda: "isFun (Lambda A f)"
  by (auto simp add: isFun_def Lambda_def Replace Opair)

lemma domain_Lambda: "Domain (Lambda A f) = A"
  apply (auto simp add: Domain_def)
  apply (subst Ext)
  apply (auto simp add: Replacement)
  apply (simp add: Lambda_def Replace)
  apply (auto simp add: Fst)
  apply (simp add: Lambda_def Replace)
  apply (rule_tac x="Opair z (f z)" in exI)
  apply (auto simp add: Fst isOpair_def)
  done

lemma Lambda_ext: "(Lambda s f = Lambda t g) \<longleftrightarrow> (s = t \<and> (\<forall> x. Elem x s \<longrightarrow> f x = g x))"
proof -
  have "Lambda s f = Lambda t g \<Longrightarrow> s = t"
    apply (subst domain_Lambda[where A = s and f = f, symmetric])
    apply (subst domain_Lambda[where A = t and f = g, symmetric])
    apply auto
    done
  then show ?thesis
    apply auto
    apply (subst Lambda_app[where f=f, symmetric], simp)
    apply (subst Lambda_app[where f=g, symmetric], simp)
    apply auto
    apply (auto simp add: Lambda_def Replace Ext)
    apply (auto simp add: Ext[symmetric])
    done
qed

definition PFun :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "PFun A B \<equiv> Sep (Power (CartProd A B)) isFun"

definition Fun :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "Fun A B \<equiv> Sep (PFun A B) (\<lambda> f. Domain f = A)"

lemma Fun_Range: "Elem f (Fun U V) \<Longrightarrow> subset (Range f) V"
  apply (simp add: Fun_def Sep PFun_def Power subset_def CartProd)
  apply (auto simp add: Domain Range)
  apply (erule_tac x="Opair xa x" in allE)
  apply (auto simp add: Opair)
  done

lemma Elem_Elem_PFun: "Elem F (PFun U V) \<Longrightarrow> Elem p F \<Longrightarrow> isOpair p \<and> Elem (Fst p) U \<and> Elem (Snd p) V"
  apply (simp add: PFun_def Sep Power subset_def, clarify)
  apply (erule_tac x=p in allE)
  apply (auto simp add: CartProd isOpair Fst Snd)
  done

lemma Fun_implies_PFun[simp]: "Elem f (Fun U V) \<Longrightarrow> Elem f (PFun U V)"
  by (simp add: Fun_def Sep)

lemma Elem_Elem_Fun: "Elem F (Fun U V) \<Longrightarrow> Elem p F \<Longrightarrow> isOpair p \<and> Elem (Fst p) U \<and> Elem (Snd p) V" 
  by (auto simp add: Elem_Elem_PFun dest: Fun_implies_PFun)

lemma PFun_inj: "Elem F (PFun U V) \<Longrightarrow> Elem x F \<Longrightarrow> Elem y F \<Longrightarrow> Fst x = Fst y \<Longrightarrow> Snd x = Snd y"
  apply (frule Elem_Elem_PFun[where p=x], simp)
  apply (frule Elem_Elem_PFun[where p=y], simp)
  apply (subgoal_tac "isFun F")
  apply (simp add: isFun_def isOpair_def)  
  apply (auto simp add: Fst Snd, blast)
  apply (auto simp add: PFun_def Sep)
  done

lemma Fun_total: "\<lbrakk>Elem F (Fun U V); Elem a U\<rbrakk> \<Longrightarrow> \<exists>x. Elem (Opair a x) F"
  using [[simp_depth_limit = 2]]
  by (auto simp add: Fun_def Sep Domain)


lemma unique_fun_value: "\<lbrakk>isFun f; Elem x (Domain f)\<rbrakk> \<Longrightarrow> ?! y. Elem (Opair x y) f"
  by (auto simp add: Domain isFun_def)

lemma fun_value_in_range: "\<lbrakk>isFun f; Elem x (Domain f)\<rbrakk> \<Longrightarrow> Elem (f\<acute>x) (Range f)"
  apply (auto simp add: Range)
  apply (drule unique_fun_value)
  apply simp
  apply (simp add: app_def)
  apply (rule exI[where x=x])
  apply (auto simp add: the_equality)
  done

lemma fun_range_witness: "\<lbrakk>isFun f; Elem y (Range f)\<rbrakk> \<Longrightarrow> ? x. Elem x (Domain f) \<and> f\<acute>x = y"
  apply (auto simp add: Range)
  apply (rule_tac x="x" in exI)
  apply (auto simp add: app_def the_equality isFun_def Domain)
  done

lemma Elem_Fun_Lambda: "Elem F (Fun U V) \<Longrightarrow> ? f. F = Lambda U f"
  apply (rule exI[where x= "% x. (THE y. Elem (Opair x y) F)"])
  apply (simp add: Ext Lambda_def Replace Domain)
  apply (simp add: Ext[symmetric])
  apply auto
  apply (frule Elem_Elem_Fun)
  apply auto
  apply (rule_tac x="Fst z" in exI)
  apply (simp add: isOpair_def)
  apply (auto simp add: Fst Snd Opair)
  apply (rule the1I2)
  apply auto
  apply (drule Fun_implies_PFun)
  apply (drule_tac x="Opair x ya" and y="Opair x yb" in PFun_inj)
  apply (auto simp add: Fst Snd)
  apply (drule Fun_implies_PFun)
  apply (drule_tac x="Opair x y" and y="Opair x ya" in PFun_inj)
  apply (auto simp add: Fst Snd)
  apply (rule the1I2)
  apply (auto simp add: Fun_total)
  apply (drule Fun_implies_PFun)
  apply (drule_tac x="Opair a x" and y="Opair a y" in PFun_inj)
  apply (auto simp add: Fst Snd)
  done
 
lemma Elem_Lambda_Fun: "Elem (Lambda A f) (Fun U V) = (A = U \<and> (\<forall> x. Elem x A \<longrightarrow> Elem (f x) V))"
proof -
  have "Elem (Lambda A f) (Fun U V) \<Longrightarrow> A = U"
    by (simp add: Fun_def Sep domain_Lambda)
  then show ?thesis
    apply auto
    apply (drule Fun_Range)
    apply (subgoal_tac "f x = ((Lambda U f) \<acute> x)")
    prefer 2
    apply (simp add: Lambda_app)
    apply simp
    apply (subgoal_tac "Elem (Lambda U f \<acute> x) (Range (Lambda U f))")
    apply (simp add: subset_def)
    apply (rule fun_value_in_range)
    apply (simp_all add: isFun_Lambda domain_Lambda)
    apply (simp add: Fun_def Sep PFun_def Power domain_Lambda isFun_Lambda)
    apply (auto simp add: subset_def CartProd)
    apply (rule_tac x="Fst x" in exI)
    apply (auto simp add: Lambda_def Replace Fst)
    done
qed    


definition is_Elem_of :: "(ZF * ZF) set" where
  "is_Elem_of \<equiv> { (a,b) | a b. Elem a b }"

lemma cond_wf_Elem:
  assumes hyps:"\<forall>x. (\<forall>y. Elem y x \<longrightarrow> Elem y U \<longrightarrow> P y) \<longrightarrow> Elem x U \<longrightarrow> P x" "Elem a U"
  shows "P a"
proof -
  {
    fix P
    fix U
    fix a
    assume P_induct: "(\<forall>x. (\<forall>y. Elem y x \<longrightarrow> Elem y U \<longrightarrow> P y) \<longrightarrow> (Elem x U \<longrightarrow> P x))"
    assume a_in_U: "Elem a U"
    have "P a"
      proof -
        term "P"
        term Sep
        let ?Z = "Sep U (Not o P)"
        have "?Z = Empty \<longrightarrow> P a" by (simp add: Ext Sep Empty a_in_U)     
        moreover have "?Z \<noteq> Empty \<longrightarrow> False"
          proof 
            assume not_empty: "?Z \<noteq> Empty" 
            note thereis_x = Regularity[where A="?Z", simplified not_empty, simplified]
            then obtain x where x_def: "Elem x ?Z \<and> (\<forall> y. Elem y x \<longrightarrow> Not (Elem y ?Z))" ..
            then have x_induct:"\<forall> y. Elem y x \<longrightarrow> Elem y U \<longrightarrow> P y" by (simp add: Sep)
            have "Elem x U \<longrightarrow> P x" 
              by (rule impE[OF spec[OF P_induct, where x=x], OF x_induct], assumption)
            moreover have "Elem x U \<and> Not(P x)"
              apply (insert x_def)
              apply (simp add: Sep)
              done
            ultimately show "False" by auto
          qed
        ultimately show "P a" by auto
      qed
  }
  with hyps show ?thesis by blast
qed    

lemma cond2_wf_Elem:
  assumes 
     special_P: "? U. ! x. Not(Elem x U) \<longrightarrow> (P x)"
     and P_induct: "\<forall>x. (\<forall>y. Elem y x \<longrightarrow> P y) \<longrightarrow> P x"
  shows
     "P a"
proof -
  have "? U Q. P = (\<lambda> x. (Elem x U \<longrightarrow> Q x))"
  proof -
    from special_P obtain U where U:"\<forall> x. Not(Elem x U) \<longrightarrow> (P x)" ..
    show ?thesis
      apply (rule_tac exI[where x=U])
      apply (rule exI[where x="P"])
      apply (rule ext)
      apply (auto simp add: U)
      done
  qed    
  then obtain U where "? Q. P = (\<lambda> x. (Elem x U \<longrightarrow> Q x))" ..
  then obtain Q where UQ: "P = (\<lambda> x. (Elem x U \<longrightarrow> Q x))" ..
  show ?thesis
    apply (auto simp add: UQ)
    apply (rule cond_wf_Elem)
    apply (rule P_induct[simplified UQ])
    apply simp
    done
qed

primrec nat2Nat :: "nat \<Rightarrow> ZF" where
  nat2Nat_0[intro]:  "nat2Nat 0 = Empty"
| nat2Nat_Suc[intro]:  "nat2Nat (Suc n) = SucNat (nat2Nat n)"

definition Nat2nat :: "ZF \<Rightarrow> nat" where
  "Nat2nat \<equiv> inv nat2Nat"

lemma Elem_nat2Nat_inf[intro]: "Elem (nat2Nat n) Inf"
  apply (induct n)
  apply (simp_all add: Infinity)
  done

definition Nat :: ZF
 where  "Nat \<equiv> Sep Inf (\<lambda> N. ? n. nat2Nat n = N)"

lemma Elem_nat2Nat_Nat[intro]: "Elem (nat2Nat n) Nat"
  by (auto simp add: Nat_def Sep)

lemma Elem_Empty_Nat: "Elem Empty Nat"
  by (auto simp add: Nat_def Sep Infinity)

lemma Elem_SucNat_Nat: "Elem N Nat \<Longrightarrow> Elem (SucNat N) Nat"
  by (auto simp add: Nat_def Sep Infinity)
  
lemma no_infinite_Elem_down_chain:
  "Not (\<exists> f. isFun f \<and> Domain f = Nat \<and> (\<forall> N. Elem N Nat \<longrightarrow> Elem (f\<acute>(SucNat N)) (f\<acute>N)))"
proof -
  {
    fix f
    assume f:"isFun f \<and> Domain f = Nat \<and> (\<forall> N. Elem N Nat \<longrightarrow> Elem (f\<acute>(SucNat N)) (f\<acute>N))"
    let ?r = "Range f"
    have "?r \<noteq> Empty"
      apply (auto simp add: Ext Empty)
      apply (rule exI[where x="f\<acute>Empty"])
      apply (rule fun_value_in_range)
      apply (auto simp add: f Elem_Empty_Nat)
      done
    then have "? x. Elem x ?r \<and> (\<forall> y. Elem y x \<longrightarrow> Not(Elem y ?r))"
      by (simp add: Regularity)
    then obtain x where x: "Elem x ?r \<and> (\<forall> y. Elem y x \<longrightarrow> Not(Elem y ?r))" ..
    then have "? N. Elem N (Domain f) \<and> f\<acute>N = x" 
      apply (rule_tac fun_range_witness)
      apply (simp_all add: f)
      done
    then have "? N. Elem N Nat \<and> f\<acute>N = x" 
      by (simp add: f)
    then obtain N where N: "Elem N Nat \<and> f\<acute>N = x" ..
    from N have N': "Elem N Nat" by auto
    let ?y = "f\<acute>(SucNat N)"
    have Elem_y_r: "Elem ?y ?r"
      by (simp_all add: f Elem_SucNat_Nat N fun_value_in_range)
    have "Elem ?y (f\<acute>N)" by (auto simp add: f N')
    then have "Elem ?y x" by (simp add: N)
    with x have "Not (Elem ?y ?r)" by auto
    with Elem_y_r have "False" by auto
  }
  then show ?thesis by auto
qed

lemma Upair_nonEmpty: "Upair a b \<noteq> Empty"
  by (auto simp add: Ext Empty Upair)  

lemma Singleton_nonEmpty: "Singleton x \<noteq> Empty"
  by (auto simp add: Singleton_def Upair_nonEmpty)

lemma notsym_Elem: "Not(Elem a b \<and> Elem b a)"
proof -
  {
    fix a b
    assume ab: "Elem a b"
    assume ba: "Elem b a"
    let ?Z = "Upair a b"
    have "?Z \<noteq> Empty" by (simp add: Upair_nonEmpty)
    then have "\<exists> x. Elem x ?Z \<and> (\<forall> y. Elem y x \<longrightarrow> Not(Elem y ?Z))"
      by (simp add: Regularity)
    then obtain x where x:"Elem x ?Z \<and> (\<forall> y. Elem y x \<longrightarrow> Not(Elem y ?Z))" ..
    then have "x = a \<or> x = b" by (simp add: Upair)
    moreover have "x = a \<longrightarrow> Not (Elem b ?Z)"
      by (auto simp add: x ba)
    moreover have "x = b \<longrightarrow> Not (Elem a ?Z)"
      by (auto simp add: x ab)
    ultimately have "False"
      by (auto simp add: Upair)
  }    
  then show ?thesis by auto
qed

lemma irreflexiv_Elem: "Not(Elem a a)"
  by (simp add: notsym_Elem[of a a, simplified])

lemma antisym_Elem: "Elem a b \<Longrightarrow> Not (Elem b a)"
  apply (insert notsym_Elem[of a b])
  apply auto
  done

primrec NatInterval :: "nat \<Rightarrow> nat \<Rightarrow> ZF" where
  "NatInterval n 0 = Singleton (nat2Nat n)"
| "NatInterval n (Suc m) = union (NatInterval n m) (Singleton (nat2Nat (n+m+1)))"

lemma n_Elem_NatInterval[rule_format]: "\<forall> q. q <= m \<longrightarrow> Elem (nat2Nat (n+q)) (NatInterval n m)"
  apply (induct m)
  apply (auto simp add: Singleton union)
  apply (case_tac "q <= m")
  apply auto
  apply (subgoal_tac "q = Suc m")
  apply auto
  done

lemma NatInterval_not_Empty: "NatInterval n m \<noteq> Empty"
  by (auto intro:   n_Elem_NatInterval[where q = 0, simplified] simp add: Empty Ext)

lemma increasing_nat2Nat[rule_format]: "0 < n \<longrightarrow> Elem (nat2Nat (n - 1)) (nat2Nat n)"
  apply (case_tac "\<exists> m. n = Suc m")
  apply (auto simp add: SucNat_def union Singleton)
  apply (drule spec[where x="n - 1"])
  apply arith
  done

lemma represent_NatInterval[rule_format]: "Elem x (NatInterval n m) \<longrightarrow> (\<exists> u. n \<le> u \<and> u \<le> n+m \<and> nat2Nat u = x)"
  apply (induct m)
  apply (auto simp add: Singleton union)
  apply (rule_tac x="Suc (n+m)" in exI)
  apply auto
  done

lemma inj_nat2Nat: "inj nat2Nat"
proof -
  {
    fix n m :: nat
    assume nm: "nat2Nat n = nat2Nat (n+m)"
    assume mg0: "0 < m"
    let ?Z = "NatInterval n m"
    have "?Z \<noteq> Empty" by (simp add: NatInterval_not_Empty)
    then have "\<exists> x. (Elem x ?Z) \<and> (\<forall> y. Elem y x \<longrightarrow> Not (Elem y ?Z))" 
      by (auto simp add: Regularity)
    then obtain x where x:"Elem x ?Z \<and> (\<forall> y. Elem y x \<longrightarrow> Not (Elem y ?Z))" ..
    then have "\<exists> u. n \<le> u \<and> u \<le> n+m \<and> nat2Nat u = x" 
      by (simp add: represent_NatInterval)
    then obtain u where u: "n \<le> u \<and> u \<le> n+m \<and> nat2Nat u = x" ..
    have "n < u \<longrightarrow> False"
    proof 
      assume n_less_u: "n < u"
      let ?y = "nat2Nat (u - 1)"
      have "Elem ?y (nat2Nat u)"
        apply (rule increasing_nat2Nat)
        apply (insert n_less_u)
        apply arith
        done
      with u have "Elem ?y x" by auto
      with x have "Not (Elem ?y ?Z)" by auto
      moreover have "Elem ?y ?Z" 
        apply (insert n_Elem_NatInterval[where q = "u - n - 1" and n=n and m=m])
        apply (insert n_less_u)
        apply (insert u)
        apply auto
        done
      ultimately show False by auto
    qed
    moreover have "u = n \<longrightarrow> False"
    proof 
      assume "u = n"
      with u have "nat2Nat n = x" by auto
      then have nm_eq_x: "nat2Nat (n+m) = x" by (simp add: nm)
      let ?y = "nat2Nat (n+m - 1)"
      have "Elem ?y (nat2Nat (n+m))"
        apply (rule increasing_nat2Nat)
        apply (insert mg0)
        apply arith
        done
      with nm_eq_x have "Elem ?y x" by auto
      with x have "Not (Elem ?y ?Z)" by auto
      moreover have "Elem ?y ?Z" 
        apply (insert n_Elem_NatInterval[where q = "m - 1" and n=n and m=m])
        apply (insert mg0)
        apply auto
        done
      ultimately show False by auto      
    qed
    ultimately have "False" using u by arith
  }
  note lemma_nat2Nat = this
  have th:"\<And>x y. \<not> (x < y \<and> (\<forall>(m\<Colon>nat). y \<noteq> x + m))" by presburger
  have th': "\<And>x y. \<not> (x \<noteq> y \<and> (\<not> x < y) \<and> (\<forall>(m\<Colon>nat). x \<noteq> y + m))" by presburger
  show ?thesis
    apply (auto simp add: inj_on_def)
    apply (case_tac "x = y")
    apply auto
    apply (case_tac "x < y")
    apply (case_tac "\<exists> m. y = x + m \<and> 0 < m")
    apply (auto intro: lemma_nat2Nat)
    apply (case_tac "y < x")
    apply (case_tac "\<exists> m. x = y + m \<and> 0 < m")
    apply simp
    apply simp
    using th apply blast
    apply (case_tac "\<exists> m. x = y + m")
    apply (auto intro: lemma_nat2Nat)
    apply (drule sym)
    using lemma_nat2Nat apply blast
    using th' apply blast    
    done
qed

lemma Nat2nat_nat2Nat[simp]: "Nat2nat (nat2Nat n) = n"
  by (simp add: Nat2nat_def inv_f_f[OF inj_nat2Nat])

lemma nat2Nat_Nat2nat[simp]: "Elem n Nat \<Longrightarrow> nat2Nat (Nat2nat n) = n"
  apply (simp add: Nat2nat_def)
  apply (rule_tac f_inv_into_f)
  apply (auto simp add: image_def Nat_def Sep)
  done

lemma Nat2nat_SucNat: "Elem N Nat \<Longrightarrow> Nat2nat (SucNat N) = Suc (Nat2nat N)"
  apply (auto simp add: Nat_def Sep Nat2nat_def)
  apply (auto simp add: inv_f_f[OF inj_nat2Nat])
  apply (simp only: nat2Nat.simps[symmetric])
  apply (simp only: inv_f_f[OF inj_nat2Nat])
  done
  

(*lemma Elem_induct: "(\<And>x. \<forall>y. Elem y x \<longrightarrow> P y \<Longrightarrow> P x) \<Longrightarrow> P a"
  by (erule wf_induct[OF wf_is_Elem_of, simplified is_Elem_of_def, simplified])*)

lemma Elem_Opair_exists: "\<exists> z. Elem x z \<and> Elem y z \<and> Elem z (Opair x y)"
  apply (rule exI[where x="Upair x y"])
  by (simp add: Upair Opair_def)

lemma UNIV_is_not_in_ZF: "UNIV \<noteq> explode R"
proof
  let ?Russell = "{ x. Not(Elem x x) }"
  have "?Russell = UNIV" by (simp add: irreflexiv_Elem)
  moreover assume "UNIV = explode R"
  ultimately have russell: "?Russell = explode R" by simp
  then show "False"
  proof(cases "Elem R R")
    case True     
    then show ?thesis 
      by (insert irreflexiv_Elem, auto)
  next
    case False
    then have "R \<in> ?Russell" by auto
    then have "Elem R R" by (simp add: russell explode_def)
    with False show ?thesis by auto
  qed
qed

definition SpecialR :: "(ZF * ZF) set" where
  "SpecialR \<equiv> { (x, y) . x \<noteq> Empty \<and> y = Empty}"

lemma "wf SpecialR"
  apply (subst wf_def)
  apply (auto simp add: SpecialR_def)
  done

definition Ext :: "('a * 'b) set \<Rightarrow> 'b \<Rightarrow> 'a set" where
  "Ext R y \<equiv> { x . (x, y) \<in> R }" 

lemma Ext_Elem: "Ext is_Elem_of = explode"
  by (auto simp add: Ext_def is_Elem_of_def explode_def)

lemma "Ext SpecialR Empty \<noteq> explode z"
proof 
  have "Ext SpecialR Empty = UNIV - {Empty}"
    by (auto simp add: Ext_def SpecialR_def)
  moreover assume "Ext SpecialR Empty = explode z"
  ultimately have "UNIV = explode(union z (Singleton Empty)) "
    by (auto simp add: explode_def union Singleton)
  then show "False" by (simp add: UNIV_is_not_in_ZF)
qed

definition implode :: "ZF set \<Rightarrow> ZF" where
  "implode \<equiv> inv explode"

lemma inj_explode: "inj explode"
  by (auto simp add: inj_on_def explode_def Ext)

lemma implode_explode[simp]: "implode (explode x) = x"
  by (simp add: implode_def inj_explode)

definition regular :: "(ZF * ZF) set \<Rightarrow> bool" where
  "regular R \<longleftrightarrow> (\<forall> A. A \<noteq> Empty \<longrightarrow> (\<exists> x. Elem x A \<and> (\<forall> y. (y, x) \<in> R \<longrightarrow> Not (Elem y A))))"

definition set_like :: "(ZF * ZF) set \<Rightarrow> bool" where
  "set_like R \<longleftrightarrow> (\<forall> y. Ext R y \<in> range explode)"

definition wfzf :: "(ZF * ZF) set \<Rightarrow> bool" where
  "wfzf R \<longleftrightarrow> regular R \<and> set_like R"

lemma regular_Elem: "regular is_Elem_of"
  by (simp add: regular_def is_Elem_of_def Regularity)

lemma set_like_Elem: "set_like is_Elem_of"
  by (auto simp add: set_like_def image_def Ext_Elem)

lemma wfzf_is_Elem_of: "wfzf is_Elem_of"
  by (auto simp add: wfzf_def regular_Elem set_like_Elem)

definition SeqSum :: "(nat \<Rightarrow> ZF) \<Rightarrow> ZF" where
  "SeqSum f \<equiv> Sum (Replace Nat (f o Nat2nat))"

lemma SeqSum: "Elem x (SeqSum f) = (\<exists> n. Elem x (f n))"
  apply (auto simp add: SeqSum_def Sum Replace)
  apply (rule_tac x = "f n" in exI)
  apply auto
  done

definition Ext_ZF :: "(ZF * ZF) set \<Rightarrow> ZF \<Rightarrow> ZF" where
  "Ext_ZF R s \<equiv> implode (Ext R s)"

lemma Elem_implode: "A \<in> range explode \<Longrightarrow> Elem x (implode A) = (x \<in> A)"
  apply (auto)
  apply (simp_all add: explode_def)
  done

lemma Elem_Ext_ZF: "set_like R \<Longrightarrow> Elem x (Ext_ZF R s) = ((x,s) \<in> R)"
  apply (simp add: Ext_ZF_def)
  apply (subst Elem_implode)
  apply (simp add: set_like_def)
  apply (simp add: Ext_def)
  done

primrec Ext_ZF_n :: "(ZF * ZF) set \<Rightarrow> ZF \<Rightarrow> nat \<Rightarrow> ZF" where
  "Ext_ZF_n R s 0 = Ext_ZF R s"
| "Ext_ZF_n R s (Suc n) = Sum (Replace (Ext_ZF_n R s n) (Ext_ZF R))"

definition Ext_ZF_hull :: "(ZF * ZF) set \<Rightarrow> ZF \<Rightarrow> ZF" where
  "Ext_ZF_hull R s \<equiv> SeqSum (Ext_ZF_n R s)"

lemma Elem_Ext_ZF_hull:
  assumes set_like_R: "set_like R" 
  shows "Elem x (Ext_ZF_hull R S) = (\<exists> n. Elem x (Ext_ZF_n R S n))"
  by (simp add: Ext_ZF_hull_def SeqSum)
  
lemma Elem_Elem_Ext_ZF_hull:
  assumes set_like_R: "set_like R" 
          and x_hull: "Elem x (Ext_ZF_hull R S)"
          and y_R_x: "(y, x) \<in> R"
  shows "Elem y (Ext_ZF_hull R S)"
proof -
  from Elem_Ext_ZF_hull[OF set_like_R] x_hull 
  have "\<exists> n. Elem x (Ext_ZF_n R S n)" by auto
  then obtain n where n:"Elem x (Ext_ZF_n R S n)" ..
  with y_R_x have "Elem y (Ext_ZF_n R S (Suc n))"
    apply (auto simp add: Replace Sum)
    apply (rule_tac x="Ext_ZF R x" in exI) 
    apply (auto simp add: Elem_Ext_ZF[OF set_like_R])
    done
  with Elem_Ext_ZF_hull[OF set_like_R, where x=y] show ?thesis
    by (auto simp del: Ext_ZF_n.simps)
qed

lemma wfzf_minimal:
  assumes hyps: "wfzf R" "C \<noteq> {}"
  shows "\<exists>x. x \<in> C \<and> (\<forall>y. (y, x) \<in> R \<longrightarrow> y \<notin> C)"
proof -
  from hyps have "\<exists>S. S \<in> C" by auto
  then obtain S where S:"S \<in> C" by auto  
  let ?T = "Sep (Ext_ZF_hull R S) (\<lambda> s. s \<in> C)"
  from hyps have set_like_R: "set_like R" by (simp add: wfzf_def)
  show ?thesis
  proof (cases "?T = Empty")
    case True
    then have "\<forall> z. \<not> (Elem z (Sep (Ext_ZF R S) (\<lambda> s. s \<in> C)))"      
      apply (auto simp add: Ext Empty Sep Ext_ZF_hull_def SeqSum)
      apply (erule_tac x="z" in allE, auto)
      apply (erule_tac x=0 in allE, auto)
      done
    then show ?thesis 
      apply (rule_tac exI[where x=S])
      apply (auto simp add: Sep Empty S)
      apply (erule_tac x=y in allE)
      apply (simp add: set_like_R Elem_Ext_ZF)
      done
  next
    case False
    from hyps have regular_R: "regular R" by (simp add: wfzf_def)
    from 
      regular_R[simplified regular_def, rule_format, OF False, simplified Sep] 
      Elem_Elem_Ext_ZF_hull[OF set_like_R]
    show ?thesis by blast
  qed
qed

lemma wfzf_implies_wf: "wfzf R \<Longrightarrow> wf R"
proof (subst wf_def, rule allI)
  assume wfzf: "wfzf R"
  fix P :: "ZF \<Rightarrow> bool"
  let ?C = "{x. P x}"
  {
    assume induct: "(\<forall>x. (\<forall>y. (y, x) \<in> R \<longrightarrow> P y) \<longrightarrow> P x)"
    let ?C = "{x. \<not> (P x)}"
    have "?C = {}"
    proof (rule ccontr)
      assume C: "?C \<noteq> {}"
      from
        wfzf_minimal[OF wfzf C]
      obtain x where x: "x \<in> ?C \<and> (\<forall>y. (y, x) \<in> R \<longrightarrow> y \<notin> ?C)" ..
      then have "P x"
        apply (rule_tac induct[rule_format])
        apply auto
        done
      with x show "False" by auto
    qed
    then have "\<forall> x. P x" by auto
  }
  then show "(\<forall>x. (\<forall>y. (y, x) \<in> R \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall> x. P x)" by blast
qed

lemma wf_is_Elem_of: "wf is_Elem_of"
  by (auto simp add: wfzf_is_Elem_of wfzf_implies_wf)

lemma in_Ext_RTrans_implies_Elem_Ext_ZF_hull:  
  "set_like R \<Longrightarrow> x \<in> (Ext (R^+) s) \<Longrightarrow> Elem x (Ext_ZF_hull R s)"
  apply (simp add: Ext_def Elem_Ext_ZF_hull)
  apply (erule converse_trancl_induct[where r="R"])
  apply (rule exI[where x=0])
  apply (simp add: Elem_Ext_ZF)
  apply auto
  apply (rule_tac x="Suc n" in exI)
  apply (simp add: Sum Replace)
  apply (rule_tac x="Ext_ZF R z" in exI)
  apply (auto simp add: Elem_Ext_ZF)
  done

lemma implodeable_Ext_trancl: "set_like R \<Longrightarrow> set_like (R^+)"
  apply (subst set_like_def)
  apply (auto simp add: image_def)
  apply (rule_tac x="Sep (Ext_ZF_hull R y) (\<lambda> z. z \<in> (Ext (R^+) y))" in exI)
  apply (auto simp add: explode_def Sep set_eqI 
    in_Ext_RTrans_implies_Elem_Ext_ZF_hull)
  done
 
lemma Elem_Ext_ZF_hull_implies_in_Ext_RTrans[rule_format]:
  "set_like R \<Longrightarrow> ! x. Elem x (Ext_ZF_n R s n) \<longrightarrow> x \<in> (Ext (R^+) s)"
  apply (induct_tac n)
  apply (auto simp add: Elem_Ext_ZF Ext_def Sum Replace)
  done

lemma "set_like R \<Longrightarrow> Ext_ZF (R^+) s = Ext_ZF_hull R s"
  apply (frule implodeable_Ext_trancl)
  apply (auto simp add: Ext)
  apply (erule in_Ext_RTrans_implies_Elem_Ext_ZF_hull)
  apply (simp add: Elem_Ext_ZF Ext_def)
  apply (auto simp add: Elem_Ext_ZF Elem_Ext_ZF_hull)
  apply (erule Elem_Ext_ZF_hull_implies_in_Ext_RTrans[simplified Ext_def, simplified], assumption)
  done

lemma wf_implies_regular: "wf R \<Longrightarrow> regular R"
proof (simp add: regular_def, rule allI)
  assume wf: "wf R"
  fix A
  show "A \<noteq> Empty \<longrightarrow> (\<exists>x. Elem x A \<and> (\<forall>y. (y, x) \<in> R \<longrightarrow> \<not> Elem y A))"
  proof
    assume A: "A \<noteq> Empty"
    then have "\<exists> x. x \<in> explode A" 
      by (auto simp add: explode_def Ext Empty)
    then obtain x where x:"x \<in> explode A" ..   
    from iffD1[OF wf_eq_minimal wf, rule_format, where Q="explode A", OF x]
    obtain z where "z \<in> explode A \<and> (\<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> explode A)" by auto    
    then show "\<exists>x. Elem x A \<and> (\<forall>y. (y, x) \<in> R \<longrightarrow> \<not> Elem y A)"      
      apply (rule_tac exI[where x = z])
      apply (simp add: explode_def)
      done
  qed
qed

lemma wf_eq_wfzf: "(wf R \<and> set_like R) = wfzf R"
  apply (auto simp add: wfzf_implies_wf)
  apply (auto simp add: wfzf_def wf_implies_regular)
  done

lemma wfzf_trancl: "wfzf R \<Longrightarrow> wfzf (R^+)"
  by (auto simp add: wf_eq_wfzf[symmetric] implodeable_Ext_trancl wf_trancl)

lemma Ext_subset_mono: "R \<subseteq> S \<Longrightarrow> Ext R y \<subseteq> Ext S y"
  by (auto simp add: Ext_def)

lemma set_like_subset: "set_like R \<Longrightarrow> S \<subseteq> R \<Longrightarrow> set_like S"
  apply (auto simp add: set_like_def)
  apply (erule_tac x=y in allE)
  apply (drule_tac y=y in Ext_subset_mono)
  apply (auto simp add: image_def)
  apply (rule_tac x="Sep x (\<lambda> z. z \<in> (Ext S y))" in exI) 
  apply (auto simp add: explode_def Sep)
  done

lemma wfzf_subset: "wfzf S \<Longrightarrow> R \<subseteq> S \<Longrightarrow> wfzf R"
  by (auto intro: set_like_subset wf_subset simp add: wf_eq_wfzf[symmetric])  

end

