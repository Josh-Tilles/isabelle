(*  Title:      HOLCF/Pcpodef.thy
    Author:     Brian Huffman
*)

header {* Subtypes of pcpos *}

theory Pcpodef
imports Adm
uses ("Tools/pcpodef_package.ML")
begin

subsection {* Proving a subtype is a partial order *}

text {*
  A subtype of a partial order is itself a partial order,
  if the ordering is defined in the standard way.
*}

setup {* Sign.add_const_constraint (@{const_name Porder.sq_le}, NONE) *}

theorem typedef_po:
  fixes Abs :: "'a::po \<Rightarrow> 'b::type"
  assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
  shows "OFCLASS('b, po_class)"
 apply (intro_classes, unfold less)
   apply (rule refl_less)
  apply (erule (1) trans_less)
 apply (rule type_definition.Rep_inject [OF type, THEN iffD1])
 apply (erule (1) antisym_less)
done

setup {* Sign.add_const_constraint (@{const_name Porder.sq_le},
  SOME @{typ "'a::sq_ord \<Rightarrow> 'a::sq_ord \<Rightarrow> bool"}) *}

subsection {* Proving a subtype is finite *}

lemma typedef_finite_UNIV:
  fixes Abs :: "'a::type \<Rightarrow> 'b::type"
  assumes type: "type_definition Rep Abs A"
  shows "finite A \<Longrightarrow> finite (UNIV :: 'b set)"
proof -
  assume "finite A"
  hence "finite (Abs ` A)" by (rule finite_imageI)
  thus "finite (UNIV :: 'b set)"
    by (simp only: type_definition.Abs_image [OF type])
qed

theorem typedef_finite_po:
  fixes Abs :: "'a::finite_po \<Rightarrow> 'b::po"
  assumes type: "type_definition Rep Abs A"
  shows "OFCLASS('b, finite_po_class)"
 apply (intro_classes)
 apply (rule typedef_finite_UNIV [OF type])
 apply (rule finite)
done

subsection {* Proving a subtype is chain-finite *}

lemma monofun_Rep:
  assumes less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
  shows "monofun Rep"
by (rule monofunI, unfold less)

lemmas ch2ch_Rep = ch2ch_monofun [OF monofun_Rep]
lemmas ub2ub_Rep = ub2ub_monofun [OF monofun_Rep]

theorem typedef_chfin:
  fixes Abs :: "'a::chfin \<Rightarrow> 'b::po"
  assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
  shows "OFCLASS('b, chfin_class)"
 apply intro_classes
 apply (drule ch2ch_Rep [OF less])
 apply (drule chfin)
 apply (unfold max_in_chain_def)
 apply (simp add: type_definition.Rep_inject [OF type])
done

subsection {* Proving a subtype is complete *}

text {*
  A subtype of a cpo is itself a cpo if the ordering is
  defined in the standard way, and the defining subset
  is closed with respect to limits of chains.  A set is
  closed if and only if membership in the set is an
  admissible predicate.
*}

lemma Abs_inverse_lub_Rep:
  fixes Abs :: "'a::cpo \<Rightarrow> 'b::po"
  assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and adm:  "adm (\<lambda>x. x \<in> A)"
  shows "chain S \<Longrightarrow> Rep (Abs (\<Squnion>i. Rep (S i))) = (\<Squnion>i. Rep (S i))"
 apply (rule type_definition.Abs_inverse [OF type])
 apply (erule admD [OF adm ch2ch_Rep [OF less]])
 apply (rule type_definition.Rep [OF type])
done

theorem typedef_lub:
  fixes Abs :: "'a::cpo \<Rightarrow> 'b::po"
  assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and adm: "adm (\<lambda>x. x \<in> A)"
  shows "chain S \<Longrightarrow> range S <<| Abs (\<Squnion>i. Rep (S i))"
 apply (frule ch2ch_Rep [OF less])
 apply (rule is_lubI)
  apply (rule ub_rangeI)
  apply (simp only: less Abs_inverse_lub_Rep [OF type less adm])
  apply (erule is_ub_thelub)
 apply (simp only: less Abs_inverse_lub_Rep [OF type less adm])
 apply (erule is_lub_thelub)
 apply (erule ub2ub_Rep [OF less])
done

lemmas typedef_thelub = typedef_lub [THEN thelubI, standard]

theorem typedef_cpo:
  fixes Abs :: "'a::cpo \<Rightarrow> 'b::po"
  assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and adm: "adm (\<lambda>x. x \<in> A)"
  shows "OFCLASS('b, cpo_class)"
proof
  fix S::"nat \<Rightarrow> 'b" assume "chain S"
  hence "range S <<| Abs (\<Squnion>i. Rep (S i))"
    by (rule typedef_lub [OF type less adm])
  thus "\<exists>x. range S <<| x" ..
qed

subsubsection {* Continuity of @{term Rep} and @{term Abs} *}

text {* For any sub-cpo, the @{term Rep} function is continuous. *}

theorem typedef_cont_Rep:
  fixes Abs :: "'a::cpo \<Rightarrow> 'b::cpo"
  assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and adm: "adm (\<lambda>x. x \<in> A)"
  shows "cont Rep"
 apply (rule contI)
 apply (simp only: typedef_thelub [OF type less adm])
 apply (simp only: Abs_inverse_lub_Rep [OF type less adm])
 apply (rule cpo_lubI)
 apply (erule ch2ch_Rep [OF less])
done

text {*
  For a sub-cpo, we can make the @{term Abs} function continuous
  only if we restrict its domain to the defining subset by
  composing it with another continuous function.
*}

theorem typedef_is_lubI:
  assumes less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
  shows "range (\<lambda>i. Rep (S i)) <<| Rep x \<Longrightarrow> range S <<| x"
 apply (rule is_lubI)
  apply (rule ub_rangeI)
  apply (subst less)
  apply (erule is_ub_lub)
 apply (subst less)
 apply (erule is_lub_lub)
 apply (erule ub2ub_Rep [OF less])
done

theorem typedef_cont_Abs:
  fixes Abs :: "'a::cpo \<Rightarrow> 'b::cpo"
  fixes f :: "'c::cpo \<Rightarrow> 'a::cpo"
  assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and adm: "adm (\<lambda>x. x \<in> A)" (* not used *)
    and f_in_A: "\<And>x. f x \<in> A"
    and cont_f: "cont f"
  shows "cont (\<lambda>x. Abs (f x))"
 apply (rule contI)
 apply (rule typedef_is_lubI [OF less])
 apply (simp only: type_definition.Abs_inverse [OF type f_in_A])
 apply (erule cont_f [THEN contE])
done

subsection {* Proving subtype elements are compact *}

theorem typedef_compact:
  fixes Abs :: "'a::cpo \<Rightarrow> 'b::cpo"
  assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and adm: "adm (\<lambda>x. x \<in> A)"
  shows "compact (Rep k) \<Longrightarrow> compact k"
proof (unfold compact_def)
  have cont_Rep: "cont Rep"
    by (rule typedef_cont_Rep [OF type less adm])
  assume "adm (\<lambda>x. \<not> Rep k \<sqsubseteq> x)"
  with cont_Rep have "adm (\<lambda>x. \<not> Rep k \<sqsubseteq> Rep x)" by (rule adm_subst)
  thus "adm (\<lambda>x. \<not> k \<sqsubseteq> x)" by (unfold less)
qed

subsection {* Proving a subtype is pointed *}

text {*
  A subtype of a cpo has a least element if and only if
  the defining subset has a least element.
*}

theorem typedef_pcpo_generic:
  fixes Abs :: "'a::cpo \<Rightarrow> 'b::cpo"
  assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and z_in_A: "z \<in> A"
    and z_least: "\<And>x. x \<in> A \<Longrightarrow> z \<sqsubseteq> x"
  shows "OFCLASS('b, pcpo_class)"
 apply (intro_classes)
 apply (rule_tac x="Abs z" in exI, rule allI)
 apply (unfold less)
 apply (subst type_definition.Abs_inverse [OF type z_in_A])
 apply (rule z_least [OF type_definition.Rep [OF type]])
done

text {*
  As a special case, a subtype of a pcpo has a least element
  if the defining subset contains @{term \<bottom>}.
*}

theorem typedef_pcpo:
  fixes Abs :: "'a::pcpo \<Rightarrow> 'b::cpo"
  assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and UU_in_A: "\<bottom> \<in> A"
  shows "OFCLASS('b, pcpo_class)"
by (rule typedef_pcpo_generic [OF type less UU_in_A], rule minimal)

subsubsection {* Strictness of @{term Rep} and @{term Abs} *}

text {*
  For a sub-pcpo where @{term \<bottom>} is a member of the defining
  subset, @{term Rep} and @{term Abs} are both strict.
*}

theorem typedef_Abs_strict:
  assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and UU_in_A: "\<bottom> \<in> A"
  shows "Abs \<bottom> = \<bottom>"
 apply (rule UU_I, unfold less)
 apply (simp add: type_definition.Abs_inverse [OF type UU_in_A])
done

theorem typedef_Rep_strict:
  assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and UU_in_A: "\<bottom> \<in> A"
  shows "Rep \<bottom> = \<bottom>"
 apply (rule typedef_Abs_strict [OF type less UU_in_A, THEN subst])
 apply (rule type_definition.Abs_inverse [OF type UU_in_A])
done

theorem typedef_Abs_strict_iff:
  assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and UU_in_A: "\<bottom> \<in> A"
  shows "x \<in> A \<Longrightarrow> (Abs x = \<bottom>) = (x = \<bottom>)"
 apply (rule typedef_Abs_strict [OF type less UU_in_A, THEN subst])
 apply (simp add: type_definition.Abs_inject [OF type] UU_in_A)
done

theorem typedef_Rep_strict_iff:
  assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and UU_in_A: "\<bottom> \<in> A"
  shows "(Rep x = \<bottom>) = (x = \<bottom>)"
 apply (rule typedef_Rep_strict [OF type less UU_in_A, THEN subst])
 apply (simp add: type_definition.Rep_inject [OF type])
done

theorem typedef_Abs_defined:
  assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and UU_in_A: "\<bottom> \<in> A"
  shows "\<lbrakk>x \<noteq> \<bottom>; x \<in> A\<rbrakk> \<Longrightarrow> Abs x \<noteq> \<bottom>"
by (simp add: typedef_Abs_strict_iff [OF type less UU_in_A])

theorem typedef_Rep_defined:
  assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and UU_in_A: "\<bottom> \<in> A"
  shows "x \<noteq> \<bottom> \<Longrightarrow> Rep x \<noteq> \<bottom>"
by (simp add: typedef_Rep_strict_iff [OF type less UU_in_A])

subsection {* Proving a subtype is flat *}

theorem typedef_flat:
  fixes Abs :: "'a::flat \<Rightarrow> 'b::pcpo"
  assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and UU_in_A: "\<bottom> \<in> A"
  shows "OFCLASS('b, flat_class)"
 apply (intro_classes)
 apply (unfold less)
 apply (simp add: type_definition.Rep_inject [OF type, symmetric])
 apply (simp add: typedef_Rep_strict [OF type less UU_in_A])
 apply (simp add: ax_flat)
done

subsection {* HOLCF type definition package *}

use "Tools/pcpodef_package.ML"

end
