(*  Title:      HOL/Quotient_Examples/Lift_FSet.thy
    Author:     Brian Huffman, TU Munich
*)

header {* Lifting and transfer with a finite set type *}

theory Lift_FSet
imports "~~/src/HOL/Library/Quotient_List"
begin

subsection {* Equivalence relation and quotient type definition *}

definition list_eq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where [simp]: "list_eq xs ys \<longleftrightarrow> set xs = set ys"

lemma reflp_list_eq: "reflp list_eq"
  unfolding reflp_def by simp

lemma symp_list_eq: "symp list_eq"
  unfolding symp_def by simp

lemma transp_list_eq: "transp list_eq"
  unfolding transp_def by simp

lemma equivp_list_eq: "equivp list_eq"
  by (intro equivpI reflp_list_eq symp_list_eq transp_list_eq)

lemma list_eq_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(list_all2 A ===> list_all2 A ===> op =) list_eq list_eq"
  unfolding list_eq_def [abs_def] by transfer_prover

quotient_type 'a fset = "'a list" / "list_eq" parametric list_eq_transfer
  by (rule equivp_list_eq)

subsection {* Lifted constant definitions *}

lift_definition fnil :: "'a fset" ("{||}") is "[]" parametric Nil_transfer
  by simp

lift_definition fcons :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is Cons parametric Cons_transfer
  by simp

lift_definition fappend :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is append parametric append_transfer
  by simp

lift_definition fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b fset" is map parametric map_transfer
  by simp

lift_definition ffilter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is filter parametric filter_transfer
  by simp

lift_definition fset :: "'a fset \<Rightarrow> 'a set" is set parametric set_transfer
  by simp

text {* Constants with nested types (like concat) yield a more
  complicated proof obligation. *}

lemma list_all2_cr_fset:
  "list_all2 cr_fset xs ys \<longleftrightarrow> map abs_fset xs = ys"
  unfolding cr_fset_def
  apply safe
  apply (erule list_all2_induct, simp, simp)
  apply (simp add: list_all2_map2 List.list_all2_refl)
  done

lemma abs_fset_eq_iff: "abs_fset xs = abs_fset ys \<longleftrightarrow> list_eq xs ys"
  using Quotient_rel [OF Quotient_fset] by simp

lift_definition fconcat :: "'a fset fset \<Rightarrow> 'a fset" is concat parametric concat_transfer
proof -
  fix xss yss :: "'a list list"
  assume "(list_all2 cr_fset OO list_eq OO (list_all2 cr_fset)\<inverse>\<inverse>) xss yss"
  then obtain uss vss where
    "list_all2 cr_fset xss uss" and "list_eq uss vss" and
    "list_all2 cr_fset yss vss" by clarsimp
  hence "list_eq (map abs_fset xss) (map abs_fset yss)"
    unfolding list_all2_cr_fset by simp
  thus "list_eq (concat xss) (concat yss)"
    apply (simp add: set_eq_iff image_def)
    apply safe
    apply (rename_tac xs, drule_tac x="abs_fset xs" in spec)
    apply (drule iffD1, fast, clarsimp simp add: abs_fset_eq_iff, fast)
    apply (rename_tac xs, drule_tac x="abs_fset xs" in spec)
    apply (drule iffD2, fast, clarsimp simp add: abs_fset_eq_iff, fast)
    done
qed

syntax
  "_insert_fset"     :: "args => 'a fset"  ("{|(_)|}")

translations
  "{|x, xs|}" == "CONST fcons x {|xs|}"
  "{|x|}"     == "CONST fcons x {||}"

lift_definition fset_member :: "'a \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "|\<in>|" 50) is "\<lambda>x xs. x \<in> set xs"
   by simp

abbreviation notin_fset :: "'a \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "|\<notin>|" 50) where
  "x |\<notin>| S \<equiv> \<not> (x |\<in>| S)"

lemma fset_member_fmap[simp]: "a |\<in>| fmap f X = (\<exists>b. b |\<in>| X \<and> a = f b)"
  by transfer auto

text {* We can export code: *}

export_code fnil fcons fappend fmap ffilter fset in SML

subsection {* Using transfer with type @{text "fset"} *}

text {* The correspondence relation @{text "cr_fset"} can only relate
  @{text "list"} and @{text "fset"} types with the same element type.
  To relate nested types like @{text "'a list list"} and
  @{text "'a fset fset"}, we define a parameterized version of the
  correspondence relation, @{text "pcr_fset"}. *}

thm pcr_fset_def

subsection {* Transfer examples *}

text {* The @{text "transfer"} method replaces equality on @{text
  "fset"} with the @{text "list_eq"} relation on lists, which is
  logically equivalent. *}

lemma "fmap f (fmap g xs) = fmap (f \<circ> g) xs"
  apply transfer
  apply simp
  done

text {* The @{text "transfer'"} variant can replace equality on @{text
  "fset"} with equality on @{text "list"}, which is logically stronger
  but sometimes more convenient. *}

lemma "fmap f (fmap g xs) = fmap (f \<circ> g) xs"
  apply transfer'
  apply (rule map_map)
  done

lemma "ffilter p (fmap f xs) = fmap f (ffilter (p \<circ> f) xs)"
  apply transfer'
  apply (rule filter_map)
  done

lemma "ffilter p (ffilter q xs) = ffilter (\<lambda>x. q x \<and> p x) xs"
  apply transfer'
  apply (rule filter_filter)
  done

lemma "fset (fcons x xs) = insert x (fset xs)"
  apply transfer
  apply (rule set.simps)
  done

lemma "fset (fappend xs ys) = fset xs \<union> fset ys"
  apply transfer
  apply (rule set_append)
  done

lemma "fset (fconcat xss) = (\<Union>xs\<in>fset xss. fset xs)"
  apply transfer
  apply (rule set_concat)
  done

lemma "\<forall>x\<in>fset xs. f x = g x \<Longrightarrow> fmap f xs = fmap g xs"
  apply transfer
  apply (simp cong: map_cong del: set_map)
  done

lemma "fnil = fconcat xss \<longleftrightarrow> (\<forall>xs\<in>fset xss. xs = fnil)"
  apply transfer
  apply simp
  done

lemma "fconcat (fmap (\<lambda>x. fcons x fnil) xs) = xs"
  apply transfer'
  apply simp
  done

lemma concat_map_concat: "concat (map concat xsss) = concat (concat xsss)"
  by (induct xsss, simp_all)

lemma "fconcat (fmap fconcat xss) = fconcat (fconcat xss)"
  apply transfer'
  apply (rule concat_map_concat)
  done

end
