(*  Title:      HOL/Library/List_Prefix.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen
*)

header {* List prefixes and postfixes *}

theory List_Prefix
imports Main
begin

subsection {* Prefix order on lists *}

instance list :: (type) ord ..

defs (overloaded)
  prefix_def: "xs \<le> ys == \<exists>zs. ys = xs @ zs"
  strict_prefix_def: "xs < ys == xs \<le> ys \<and> xs \<noteq> (ys::'a list)"

instance list :: (type) order
  by intro_classes (auto simp add: prefix_def strict_prefix_def)

lemma prefixI [intro?]: "ys = xs @ zs ==> xs \<le> ys"
  by (unfold prefix_def) blast

lemma prefixE [elim?]: "xs \<le> ys ==> (!!zs. ys = xs @ zs ==> C) ==> C"
  by (unfold prefix_def) blast

lemma strict_prefixI' [intro?]: "ys = xs @ z # zs ==> xs < ys"
  by (unfold strict_prefix_def prefix_def) blast

lemma strict_prefixE' [elim?]:
  assumes lt: "xs < ys"
    and r: "!!z zs. ys = xs @ z # zs ==> C"
  shows C
proof -
  from lt obtain us where "ys = xs @ us" and "xs \<noteq> ys"
    by (unfold strict_prefix_def prefix_def) blast
  with r show ?thesis by (auto simp add: neq_Nil_conv)
qed

lemma strict_prefixI [intro?]: "xs \<le> ys ==> xs \<noteq> ys ==> xs < (ys::'a list)"
  by (unfold strict_prefix_def) blast

lemma strict_prefixE [elim?]:
    "xs < ys ==> (xs \<le> ys ==> xs \<noteq> (ys::'a list) ==> C) ==> C"
  by (unfold strict_prefix_def) blast


subsection {* Basic properties of prefixes *}

theorem Nil_prefix [iff]: "[] \<le> xs"
  by (simp add: prefix_def)

theorem prefix_Nil [simp]: "(xs \<le> []) = (xs = [])"
  by (induct xs) (simp_all add: prefix_def)

lemma prefix_snoc [simp]: "(xs \<le> ys @ [y]) = (xs = ys @ [y] \<or> xs \<le> ys)"
proof
  assume "xs \<le> ys @ [y]"
  then obtain zs where zs: "ys @ [y] = xs @ zs" ..
  show "xs = ys @ [y] \<or> xs \<le> ys"
  proof (cases zs rule: rev_cases)
    assume "zs = []"
    with zs have "xs = ys @ [y]" by simp
    thus ?thesis ..
  next
    fix z zs' assume "zs = zs' @ [z]"
    with zs have "ys = xs @ zs'" by simp
    hence "xs \<le> ys" ..
    thus ?thesis ..
  qed
next
  assume "xs = ys @ [y] \<or> xs \<le> ys"
  thus "xs \<le> ys @ [y]"
  proof
    assume "xs = ys @ [y]"
    thus ?thesis by simp
  next
    assume "xs \<le> ys"
    then obtain zs where "ys = xs @ zs" ..
    hence "ys @ [y] = xs @ (zs @ [y])" by simp
    thus ?thesis ..
  qed
qed

lemma Cons_prefix_Cons [simp]: "(x # xs \<le> y # ys) = (x = y \<and> xs \<le> ys)"
  by (auto simp add: prefix_def)

lemma same_prefix_prefix [simp]: "(xs @ ys \<le> xs @ zs) = (ys \<le> zs)"
  by (induct xs) simp_all

lemma same_prefix_nil [iff]: "(xs @ ys \<le> xs) = (ys = [])"
proof -
  have "(xs @ ys \<le> xs @ []) = (ys \<le> [])" by (rule same_prefix_prefix)
  thus ?thesis by simp
qed

lemma prefix_prefix [simp]: "xs \<le> ys ==> xs \<le> ys @ zs"
proof -
  assume "xs \<le> ys"
  then obtain us where "ys = xs @ us" ..
  hence "ys @ zs = xs @ (us @ zs)" by simp
  thus ?thesis ..
qed

lemma append_prefixD: "xs @ ys \<le> zs \<Longrightarrow> xs \<le> zs"
  by (auto simp add: prefix_def)

theorem prefix_Cons: "(xs \<le> y # ys) = (xs = [] \<or> (\<exists>zs. xs = y # zs \<and> zs \<le> ys))"
  by (cases xs) (auto simp add: prefix_def)

theorem prefix_append:
    "(xs \<le> ys @ zs) = (xs \<le> ys \<or> (\<exists>us. xs = ys @ us \<and> us \<le> zs))"
  apply (induct zs rule: rev_induct)
   apply force
  apply (simp del: append_assoc add: append_assoc [symmetric])
  apply simp
  apply blast
  done

lemma append_one_prefix:
    "xs \<le> ys ==> length xs < length ys ==> xs @ [ys ! length xs] \<le> ys"
  apply (unfold prefix_def)
  apply (auto simp add: nth_append)
  apply (case_tac zs)
   apply auto
  done

theorem prefix_length_le: "xs \<le> ys ==> length xs \<le> length ys"
  by (auto simp add: prefix_def)

lemma prefix_same_cases:
    "(xs\<^isub>1::'a list) \<le> ys \<Longrightarrow> xs\<^isub>2 \<le> ys \<Longrightarrow> xs\<^isub>1 \<le> xs\<^isub>2 \<or> xs\<^isub>2 \<le> xs\<^isub>1"
  apply (simp add: prefix_def)
  apply (erule exE)+
  apply (simp add: append_eq_append_conv_if split: if_splits)
   apply (rule disjI2)
   apply (rule_tac x = "drop (size xs\<^isub>2) xs\<^isub>1" in exI)
   apply clarify
   apply (drule sym)
   apply (insert append_take_drop_id [of "length xs\<^isub>2" xs\<^isub>1])
   apply simp
  apply (rule disjI1)
  apply (rule_tac x = "drop (size xs\<^isub>1) xs\<^isub>2" in exI)
  apply clarify
  apply (insert append_take_drop_id [of "length xs\<^isub>1" xs\<^isub>2])
  apply simp
  done

lemma set_mono_prefix:
    "xs \<le> ys \<Longrightarrow> set xs \<subseteq> set ys"
  by (auto simp add: prefix_def)


subsection {* Parallel lists *}

constdefs
  parallel :: "'a list => 'a list => bool"    (infixl "\<parallel>" 50)
  "xs \<parallel> ys == \<not> xs \<le> ys \<and> \<not> ys \<le> xs"

lemma parallelI [intro]: "\<not> xs \<le> ys ==> \<not> ys \<le> xs ==> xs \<parallel> ys"
  by (unfold parallel_def) blast

lemma parallelE [elim]:
    "xs \<parallel> ys ==> (\<not> xs \<le> ys ==> \<not> ys \<le> xs ==> C) ==> C"
  by (unfold parallel_def) blast

theorem prefix_cases:
  "(xs \<le> ys ==> C) ==>
    (ys < xs ==> C) ==>
    (xs \<parallel> ys ==> C) ==> C"
  by (unfold parallel_def strict_prefix_def) blast

theorem parallel_decomp:
  "xs \<parallel> ys ==> \<exists>as b bs c cs. b \<noteq> c \<and> xs = as @ b # bs \<and> ys = as @ c # cs"
proof (induct xs rule: rev_induct)
  case Nil
  hence False by auto
  thus ?case ..
next
  case (snoc x xs)
  show ?case
  proof (rule prefix_cases)
    assume le: "xs \<le> ys"
    then obtain ys' where ys: "ys = xs @ ys'" ..
    show ?thesis
    proof (cases ys')
      assume "ys' = []" with ys have "xs = ys" by simp
      with snoc have "[x] \<parallel> []" by auto
      hence False by blast
      thus ?thesis ..
    next
      fix c cs assume ys': "ys' = c # cs"
      with snoc ys have "xs @ [x] \<parallel> xs @ c # cs" by (simp only:)
      hence "x \<noteq> c" by auto
      moreover have "xs @ [x] = xs @ x # []" by simp
      moreover from ys ys' have "ys = xs @ c # cs" by (simp only:)
      ultimately show ?thesis by blast
    qed
  next
    assume "ys < xs" hence "ys \<le> xs @ [x]" by (simp add: strict_prefix_def)
    with snoc have False by blast
    thus ?thesis ..
  next
    assume "xs \<parallel> ys"
    with snoc obtain as b bs c cs where neq: "(b::'a) \<noteq> c"
      and xs: "xs = as @ b # bs" and ys: "ys = as @ c # cs"
      by blast
    from xs have "xs @ [x] = as @ b # (bs @ [x])" by simp
    with neq ys show ?thesis by blast
  qed
qed


subsection {* Postfix order on lists *}

constdefs
  postfix :: "'a list => 'a list => bool"  ("(_/ >>= _)" [51, 50] 50)
  "xs >>= ys == \<exists>zs. xs = zs @ ys"

lemma postfix_refl [simp, intro!]: "xs >>= xs"
  by (auto simp add: postfix_def)
lemma postfix_trans: "\<lbrakk>xs >>= ys; ys >>= zs\<rbrakk> \<Longrightarrow> xs >>= zs"
  by (auto simp add: postfix_def)
lemma postfix_antisym: "\<lbrakk>xs >>= ys; ys >>= xs\<rbrakk> \<Longrightarrow> xs = ys"
  by (auto simp add: postfix_def)

lemma Nil_postfix [iff]: "xs >>= []"
  by (simp add: postfix_def)
lemma postfix_Nil [simp]: "([] >>= xs) = (xs = [])"
  by (auto simp add:postfix_def)

lemma postfix_ConsI: "xs >>= ys \<Longrightarrow> x#xs >>= ys"
  by (auto simp add: postfix_def)
lemma postfix_ConsD: "xs >>= y#ys \<Longrightarrow> xs >>= ys"
  by (auto simp add: postfix_def)

lemma postfix_appendI: "xs >>= ys \<Longrightarrow> zs @ xs >>= ys"
  by (auto simp add: postfix_def)
lemma postfix_appendD: "xs >>= zs @ ys \<Longrightarrow> xs >>= ys"
  by(auto simp add: postfix_def)

lemma postfix_is_subset_lemma: "xs = zs @ ys \<Longrightarrow> set ys \<subseteq> set xs"
  by (induct zs) auto
lemma postfix_is_subset: "xs >>= ys \<Longrightarrow> set ys \<subseteq> set xs"
  by (unfold postfix_def, erule exE, erule postfix_is_subset_lemma)

lemma postfix_ConsD2_lemma: "x#xs = zs @ y#ys \<Longrightarrow> xs >>= ys"
  by (induct zs) (auto intro!: postfix_appendI postfix_ConsI)
lemma postfix_ConsD2: "x#xs >>= y#ys \<Longrightarrow> xs >>= ys"
  by (auto simp add: postfix_def dest!: postfix_ConsD2_lemma)

lemma postfix2prefix: "(xs >>= ys) = (rev ys <= rev xs)"
  apply (unfold prefix_def postfix_def, safe)
   apply (rule_tac x = "rev zs" in exI, simp)
  apply (rule_tac x = "rev zs" in exI)
  apply (rule rev_is_rev_conv [THEN iffD1], simp)
  done

end
