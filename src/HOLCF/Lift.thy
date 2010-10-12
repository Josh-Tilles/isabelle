(*  Title:      HOLCF/Lift.thy
    Author:     Olaf Mueller
*)

header {* Lifting types of class type to flat pcpo's *}

theory Lift
imports Discrete Up Countable
begin

default_sort type

pcpodef 'a lift = "UNIV :: 'a discr u set"
by simp_all

instance lift :: (finite) finite_po
by (rule typedef_finite_po [OF type_definition_lift])

lemmas inst_lift_pcpo = Abs_lift_strict [symmetric]

definition
  Def :: "'a \<Rightarrow> 'a lift" where
  "Def x = Abs_lift (up\<cdot>(Discr x))"

subsection {* Lift as a datatype *}

lemma lift_induct: "\<lbrakk>P \<bottom>; \<And>x. P (Def x)\<rbrakk> \<Longrightarrow> P y"
apply (induct y)
apply (rule_tac p=y in upE)
apply (simp add: Abs_lift_strict)
apply (case_tac x)
apply (simp add: Def_def)
done

rep_datatype "\<bottom>\<Colon>'a lift" Def
  by (erule lift_induct) (simp_all add: Def_def Abs_lift_inject lift_def inst_lift_pcpo)

lemmas lift_distinct1 = lift.distinct(1)
lemmas lift_distinct2 = lift.distinct(2)
lemmas Def_not_UU = lift.distinct(2)
lemmas Def_inject = lift.inject


text {* @{term UU} and @{term Def} *}

lemma Lift_exhaust: "x = \<bottom> \<or> (\<exists>y. x = Def y)"
  by (induct x) simp_all

lemma Lift_cases: "\<lbrakk>x = \<bottom> \<Longrightarrow> P; \<exists>a. x = Def a \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (insert Lift_exhaust) blast

lemma not_Undef_is_Def: "(x \<noteq> \<bottom>) = (\<exists>y. x = Def y)"
  by (cases x) simp_all

lemma lift_definedE: "\<lbrakk>x \<noteq> \<bottom>; \<And>a. x = Def a \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (cases x) simp_all

text {*
  For @{term "x ~= UU"} in assumptions @{text defined} replaces @{text
  x} by @{text "Def a"} in conclusion. *}

method_setup defined = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD'
    (etac @{thm lift_definedE} THEN' asm_simp_tac (simpset_of ctxt)))
*} ""

lemma DefE: "Def x = \<bottom> \<Longrightarrow> R"
  by simp

lemma DefE2: "\<lbrakk>x = Def s; x = \<bottom>\<rbrakk> \<Longrightarrow> R"
  by simp

lemma Def_below_Def: "Def x \<sqsubseteq> Def y \<longleftrightarrow> x = y"
by (simp add: below_lift_def Def_def Abs_lift_inverse lift_def)

lemma Def_below_iff [simp]: "Def x \<sqsubseteq> y \<longleftrightarrow> Def x = y"
by (induct y, simp, simp add: Def_below_Def)


subsection {* Lift is flat *}

instance lift :: (type) flat
proof
  fix x y :: "'a lift"
  assume "x \<sqsubseteq> y" thus "x = \<bottom> \<or> x = y"
    by (induct x) auto
qed

subsection {* Further operations *}

definition
  flift1 :: "('a \<Rightarrow> 'b::pcpo) \<Rightarrow> ('a lift \<rightarrow> 'b)"  (binder "FLIFT " 10)  where
  "flift1 = (\<lambda>f. (\<Lambda> x. lift_case \<bottom> f x))"

definition
  flift2 :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a lift \<rightarrow> 'b lift)" where
  "flift2 f = (FLIFT x. Def (f x))"

subsection {* Continuity Proofs for flift1, flift2 *}

text {* Need the instance of @{text flat}. *}

lemma cont_lift_case1: "cont (\<lambda>f. lift_case a f x)"
apply (induct x)
apply simp
apply simp
apply (rule cont_id [THEN cont2cont_fun])
done

lemma cont_lift_case2: "cont (\<lambda>x. lift_case \<bottom> f x)"
apply (rule flatdom_strict2cont)
apply simp
done

lemma cont_flift1: "cont flift1"
unfolding flift1_def
apply (rule cont2cont_LAM)
apply (rule cont_lift_case2)
apply (rule cont_lift_case1)
done

lemma FLIFT_mono:
  "(\<And>x. f x \<sqsubseteq> g x) \<Longrightarrow> (FLIFT x. f x) \<sqsubseteq> (FLIFT x. g x)"
apply (rule monofunE [where f=flift1])
apply (rule cont2mono [OF cont_flift1])
apply (simp add: fun_below_iff)
done

lemma cont2cont_flift1 [simp, cont2cont]:
  "\<lbrakk>\<And>y. cont (\<lambda>x. f x y)\<rbrakk> \<Longrightarrow> cont (\<lambda>x. FLIFT y. f x y)"
apply (rule cont_flift1 [THEN cont_compose])
apply simp
done

lemma cont2cont_lift_case [simp]:
  "\<lbrakk>\<And>y. cont (\<lambda>x. f x y); cont g\<rbrakk> \<Longrightarrow> cont (\<lambda>x. lift_case UU (f x) (g x))"
apply (subgoal_tac "cont (\<lambda>x. (FLIFT y. f x y)\<cdot>(g x))")
apply (simp add: flift1_def cont_lift_case2)
apply simp
done

text {* rewrites for @{term flift1}, @{term flift2} *}

lemma flift1_Def [simp]: "flift1 f\<cdot>(Def x) = (f x)"
by (simp add: flift1_def cont_lift_case2)

lemma flift2_Def [simp]: "flift2 f\<cdot>(Def x) = Def (f x)"
by (simp add: flift2_def)

lemma flift1_strict [simp]: "flift1 f\<cdot>\<bottom> = \<bottom>"
by (simp add: flift1_def cont_lift_case2)

lemma flift2_strict [simp]: "flift2 f\<cdot>\<bottom> = \<bottom>"
by (simp add: flift2_def)

lemma flift2_defined [simp]: "x \<noteq> \<bottom> \<Longrightarrow> (flift2 f)\<cdot>x \<noteq> \<bottom>"
by (erule lift_definedE, simp)

lemma flift2_defined_iff [simp]: "(flift2 f\<cdot>x = \<bottom>) = (x = \<bottom>)"
by (cases x, simp_all)

end
