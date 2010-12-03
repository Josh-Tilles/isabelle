(* Author: Florian Haftmann, TU Muenchen *)

header {* Finite types as explicit enumerations *}

theory Enum
imports Map String
begin

subsection {* Class @{text enum} *}

class enum =
  fixes enum :: "'a list"
  assumes UNIV_enum: "UNIV = set enum"
    and enum_distinct: "distinct enum"
begin

subclass finite proof
qed (simp add: UNIV_enum)

lemma enum_all: "set enum = UNIV" unfolding UNIV_enum ..

lemma in_enum: "x \<in> set enum"
  unfolding enum_all by auto

lemma enum_eq_I:
  assumes "\<And>x. x \<in> set xs"
  shows "set enum = set xs"
proof -
  from assms UNIV_eq_I have "UNIV = set xs" by auto
  with enum_all show ?thesis by simp
qed

end


subsection {* Equality and order on functions *}

instantiation "fun" :: (enum, equal) equal
begin

definition
  "HOL.equal f g \<longleftrightarrow> (\<forall>x \<in> set enum. f x = g x)"

instance proof
qed (simp_all add: equal_fun_def enum_all fun_eq_iff)

end

lemma [code]:
  "HOL.equal f g \<longleftrightarrow>  list_all (%x. f x = g x) enum"
by (auto simp add: list_all_iff enum_all equal fun_eq_iff)

lemma [code nbe]:
  "HOL.equal (f :: _ \<Rightarrow> _) f \<longleftrightarrow> True"
  by (fact equal_refl)

lemma order_fun [code]:
  fixes f g :: "'a\<Colon>enum \<Rightarrow> 'b\<Colon>order"
  shows "f \<le> g \<longleftrightarrow> list_all (\<lambda>x. f x \<le> g x) enum"
    and "f < g \<longleftrightarrow> f \<le> g \<and> list_ex (\<lambda>x. f x \<noteq> g x) enum"
  by (simp_all add: list_all_iff list_ex_iff enum_all fun_eq_iff le_fun_def order_less_le)


subsection {* Quantifiers *}

lemma all_code [code]: "(\<forall>x. P x) \<longleftrightarrow> list_all P enum"
  by (simp add: list_all_iff enum_all)

lemma exists_code [code]: "(\<exists>x. P x) \<longleftrightarrow> list_ex P enum"
  by (simp add: list_ex_iff enum_all)

lemma exists1_code[code]: "(\<exists>!x. P x) \<longleftrightarrow> list_ex1 P enum"
unfolding list_ex1_iff enum_all by auto


subsection {* Default instances *}

primrec n_lists :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "n_lists 0 xs = [[]]"
  | "n_lists (Suc n) xs = concat (map (\<lambda>ys. map (\<lambda>y. y # ys) xs) (n_lists n xs))"

lemma n_lists_Nil [simp]: "n_lists n [] = (if n = 0 then [[]] else [])"
  by (induct n) simp_all

lemma length_n_lists: "length (n_lists n xs) = length xs ^ n"
  by (induct n) (auto simp add: length_concat o_def listsum_triv)

lemma length_n_lists_elem: "ys \<in> set (n_lists n xs) \<Longrightarrow> length ys = n"
  by (induct n arbitrary: ys) auto

lemma set_n_lists: "set (n_lists n xs) = {ys. length ys = n \<and> set ys \<subseteq> set xs}"
proof (rule set_eqI)
  fix ys :: "'a list"
  show "ys \<in> set (n_lists n xs) \<longleftrightarrow> ys \<in> {ys. length ys = n \<and> set ys \<subseteq> set xs}"
  proof -
    have "ys \<in> set (n_lists n xs) \<Longrightarrow> length ys = n"
      by (induct n arbitrary: ys) auto
    moreover have "\<And>x. ys \<in> set (n_lists n xs) \<Longrightarrow> x \<in> set ys \<Longrightarrow> x \<in> set xs"
      by (induct n arbitrary: ys) auto
    moreover have "set ys \<subseteq> set xs \<Longrightarrow> ys \<in> set (n_lists (length ys) xs)"
      by (induct ys) auto
    ultimately show ?thesis by auto
  qed
qed

lemma distinct_n_lists:
  assumes "distinct xs"
  shows "distinct (n_lists n xs)"
proof (rule card_distinct)
  from assms have card_length: "card (set xs) = length xs" by (rule distinct_card)
  have "card (set (n_lists n xs)) = card (set xs) ^ n"
  proof (induct n)
    case 0 then show ?case by simp
  next
    case (Suc n)
    moreover have "card (\<Union>ys\<in>set (n_lists n xs). (\<lambda>y. y # ys) ` set xs)
      = (\<Sum>ys\<in>set (n_lists n xs). card ((\<lambda>y. y # ys) ` set xs))"
      by (rule card_UN_disjoint) auto
    moreover have "\<And>ys. card ((\<lambda>y. y # ys) ` set xs) = card (set xs)"
      by (rule card_image) (simp add: inj_on_def)
    ultimately show ?case by auto
  qed
  also have "\<dots> = length xs ^ n" by (simp add: card_length)
  finally show "card (set (n_lists n xs)) = length (n_lists n xs)"
    by (simp add: length_n_lists)
qed

lemma map_of_zip_enum_is_Some:
  assumes "length ys = length (enum \<Colon> 'a\<Colon>enum list)"
  shows "\<exists>y. map_of (zip (enum \<Colon> 'a\<Colon>enum list) ys) x = Some y"
proof -
  from assms have "x \<in> set (enum \<Colon> 'a\<Colon>enum list) \<longleftrightarrow>
    (\<exists>y. map_of (zip (enum \<Colon> 'a\<Colon>enum list) ys) x = Some y)"
    by (auto intro!: map_of_zip_is_Some)
  then show ?thesis using enum_all by auto
qed

lemma map_of_zip_enum_inject:
  fixes xs ys :: "'b\<Colon>enum list"
  assumes length: "length xs = length (enum \<Colon> 'a\<Colon>enum list)"
      "length ys = length (enum \<Colon> 'a\<Colon>enum list)"
    and map_of: "the \<circ> map_of (zip (enum \<Colon> 'a\<Colon>enum list) xs) = the \<circ> map_of (zip (enum \<Colon> 'a\<Colon>enum list) ys)"
  shows "xs = ys"
proof -
  have "map_of (zip (enum \<Colon> 'a list) xs) = map_of (zip (enum \<Colon> 'a list) ys)"
  proof
    fix x :: 'a
    from length map_of_zip_enum_is_Some obtain y1 y2
      where "map_of (zip (enum \<Colon> 'a list) xs) x = Some y1"
        and "map_of (zip (enum \<Colon> 'a list) ys) x = Some y2" by blast
    moreover from map_of have "the (map_of (zip (enum \<Colon> 'a\<Colon>enum list) xs) x) = the (map_of (zip (enum \<Colon> 'a\<Colon>enum list) ys) x)"
      by (auto dest: fun_cong)
    ultimately show "map_of (zip (enum \<Colon> 'a\<Colon>enum list) xs) x = map_of (zip (enum \<Colon> 'a\<Colon>enum list) ys) x"
      by simp
  qed
  with length enum_distinct show "xs = ys" by (rule map_of_zip_inject)
qed

instantiation "fun" :: (enum, enum) enum
begin

definition
  "enum = map (\<lambda>ys. the o map_of (zip (enum\<Colon>'a list) ys)) (n_lists (length (enum\<Colon>'a\<Colon>enum list)) enum)"

instance proof
  show "UNIV = set (enum \<Colon> ('a \<Rightarrow> 'b) list)"
  proof (rule UNIV_eq_I)
    fix f :: "'a \<Rightarrow> 'b"
    have "f = the \<circ> map_of (zip (enum \<Colon> 'a\<Colon>enum list) (map f enum))"
      by (auto simp add: map_of_zip_map fun_eq_iff intro: in_enum)
    then show "f \<in> set enum"
      by (auto simp add: enum_fun_def set_n_lists intro: in_enum)
  qed
next
  from map_of_zip_enum_inject
  show "distinct (enum \<Colon> ('a \<Rightarrow> 'b) list)"
    by (auto intro!: inj_onI simp add: enum_fun_def
      distinct_map distinct_n_lists enum_distinct set_n_lists enum_all)
qed

end

lemma enum_fun_code [code]: "enum = (let enum_a = (enum \<Colon> 'a\<Colon>{enum, equal} list)
  in map (\<lambda>ys. the o map_of (zip enum_a ys)) (n_lists (length enum_a) enum))"
  by (simp add: enum_fun_def Let_def)

instantiation unit :: enum
begin

definition
  "enum = [()]"

instance proof
qed (simp_all add: enum_unit_def UNIV_unit)

end

instantiation bool :: enum
begin

definition
  "enum = [False, True]"

instance proof
qed (simp_all add: enum_bool_def UNIV_bool)

end

primrec product :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where
  "product [] _ = []"
  | "product (x#xs) ys = map (Pair x) ys @ product xs ys"

lemma product_list_set:
  "set (product xs ys) = set xs \<times> set ys"
  by (induct xs) auto

lemma distinct_product:
  assumes "distinct xs" and "distinct ys"
  shows "distinct (product xs ys)"
  using assms by (induct xs)
    (auto intro: inj_onI simp add: product_list_set distinct_map)

instantiation prod :: (enum, enum) enum
begin

definition
  "enum = product enum enum"

instance by default
  (simp_all add: enum_prod_def product_list_set distinct_product enum_all enum_distinct)

end

instantiation sum :: (enum, enum) enum
begin

definition
  "enum = map Inl enum @ map Inr enum"

instance by default
  (auto simp add: enum_all enum_sum_def, case_tac x, auto intro: inj_onI simp add: distinct_map enum_distinct)

end

primrec sublists :: "'a list \<Rightarrow> 'a list list" where
  "sublists [] = [[]]"
  | "sublists (x#xs) = (let xss = sublists xs in map (Cons x) xss @ xss)"

lemma length_sublists:
  "length (sublists xs) = Suc (Suc (0\<Colon>nat)) ^ length xs"
  by (induct xs) (simp_all add: Let_def)

lemma sublists_powset:
  "set ` set (sublists xs) = Pow (set xs)"
proof -
  have aux: "\<And>x A. set ` Cons x ` A = insert x ` set ` A"
    by (auto simp add: image_def)
  have "set (map set (sublists xs)) = Pow (set xs)"
    by (induct xs)
      (simp_all add: aux Let_def Pow_insert Un_commute comp_def del: map_map)
  then show ?thesis by simp
qed

lemma distinct_set_sublists:
  assumes "distinct xs"
  shows "distinct (map set (sublists xs))"
proof (rule card_distinct)
  have "finite (set xs)" by rule
  then have "card (Pow (set xs)) = Suc (Suc 0) ^ card (set xs)" by (rule card_Pow)
  with assms distinct_card [of xs]
    have "card (Pow (set xs)) = Suc (Suc 0) ^ length xs" by simp
  then show "card (set (map set (sublists xs))) = length (map set (sublists xs))"
    by (simp add: sublists_powset length_sublists)
qed

instantiation nibble :: enum
begin

definition
  "enum = [Nibble0, Nibble1, Nibble2, Nibble3, Nibble4, Nibble5, Nibble6, Nibble7,
    Nibble8, Nibble9, NibbleA, NibbleB, NibbleC, NibbleD, NibbleE, NibbleF]"

instance proof
qed (simp_all add: enum_nibble_def UNIV_nibble)

end

instantiation char :: enum
begin

definition
  "enum = map (split Char) (product enum enum)"

lemma enum_chars [code]:
  "enum = chars"
  unfolding enum_char_def chars_def enum_nibble_def by simp

instance proof
qed (auto intro: char.exhaust injI simp add: enum_char_def product_list_set enum_all full_SetCompr_eq [symmetric]
  distinct_map distinct_product enum_distinct)

end

instantiation option :: (enum) enum
begin

definition
  "enum = None # map Some enum"

instance proof
qed (auto simp add: enum_all enum_option_def, rule option.exhaust, auto intro: simp add: distinct_map enum_distinct)

end

subsection {* Small finite types *}

text {* We define small finite types for the use in Quickcheck *}

datatype finite_1 = a\<^isub>1

notation (output) a\<^isub>1  ("a\<^isub>1")

instantiation finite_1 :: enum
begin

definition
  "enum = [a\<^isub>1]"

instance proof
qed (auto simp add: enum_finite_1_def intro: finite_1.exhaust)

end

instantiation finite_1 :: linorder
begin

definition less_eq_finite_1 :: "finite_1 \<Rightarrow> finite_1 \<Rightarrow> bool"
where
  "less_eq_finite_1 x y = True"

definition less_finite_1 :: "finite_1 \<Rightarrow> finite_1 \<Rightarrow> bool"
where
  "less_finite_1 x y = False"

instance
apply (intro_classes)
apply (auto simp add: less_finite_1_def less_eq_finite_1_def)
apply (metis finite_1.exhaust)
done

end

hide_const a\<^isub>1

datatype finite_2 = a\<^isub>1 | a\<^isub>2

notation (output) a\<^isub>1  ("a\<^isub>1")
notation (output) a\<^isub>2  ("a\<^isub>2")

instantiation finite_2 :: enum
begin

definition
  "enum = [a\<^isub>1, a\<^isub>2]"

instance proof
qed (auto simp add: enum_finite_2_def intro: finite_2.exhaust)

end

instantiation finite_2 :: linorder
begin

definition less_finite_2 :: "finite_2 \<Rightarrow> finite_2 \<Rightarrow> bool"
where
  "less_finite_2 x y = ((x = a\<^isub>1) & (y = a\<^isub>2))"

definition less_eq_finite_2 :: "finite_2 \<Rightarrow> finite_2 \<Rightarrow> bool"
where
  "less_eq_finite_2 x y = ((x = y) \<or> (x < y))"


instance
apply (intro_classes)
apply (auto simp add: less_finite_2_def less_eq_finite_2_def)
apply (metis finite_2.distinct finite_2.nchotomy)+
done

end

hide_const a\<^isub>1 a\<^isub>2


datatype finite_3 = a\<^isub>1 | a\<^isub>2 | a\<^isub>3

notation (output) a\<^isub>1  ("a\<^isub>1")
notation (output) a\<^isub>2  ("a\<^isub>2")
notation (output) a\<^isub>3  ("a\<^isub>3")

instantiation finite_3 :: enum
begin

definition
  "enum = [a\<^isub>1, a\<^isub>2, a\<^isub>3]"

instance proof
qed (auto simp add: enum_finite_3_def intro: finite_3.exhaust)

end

instantiation finite_3 :: linorder
begin

definition less_finite_3 :: "finite_3 \<Rightarrow> finite_3 \<Rightarrow> bool"
where
  "less_finite_3 x y = (case x of a\<^isub>1 => (y \<noteq> a\<^isub>1)
     | a\<^isub>2 => (y = a\<^isub>3)| a\<^isub>3 => False)"

definition less_eq_finite_3 :: "finite_3 \<Rightarrow> finite_3 \<Rightarrow> bool"
where
  "less_eq_finite_3 x y = ((x = y) \<or> (x < y))"


instance proof (intro_classes)
qed (auto simp add: less_finite_3_def less_eq_finite_3_def split: finite_3.split_asm)

end

hide_const a\<^isub>1 a\<^isub>2 a\<^isub>3


datatype finite_4 = a\<^isub>1 | a\<^isub>2 | a\<^isub>3 | a\<^isub>4

notation (output) a\<^isub>1  ("a\<^isub>1")
notation (output) a\<^isub>2  ("a\<^isub>2")
notation (output) a\<^isub>3  ("a\<^isub>3")
notation (output) a\<^isub>4  ("a\<^isub>4")

instantiation finite_4 :: enum
begin

definition
  "enum = [a\<^isub>1, a\<^isub>2, a\<^isub>3, a\<^isub>4]"

instance proof
qed (auto simp add: enum_finite_4_def intro: finite_4.exhaust)

end

hide_const a\<^isub>1 a\<^isub>2 a\<^isub>3 a\<^isub>4


datatype finite_5 = a\<^isub>1 | a\<^isub>2 | a\<^isub>3 | a\<^isub>4 | a\<^isub>5

notation (output) a\<^isub>1  ("a\<^isub>1")
notation (output) a\<^isub>2  ("a\<^isub>2")
notation (output) a\<^isub>3  ("a\<^isub>3")
notation (output) a\<^isub>4  ("a\<^isub>4")
notation (output) a\<^isub>5  ("a\<^isub>5")

instantiation finite_5 :: enum
begin

definition
  "enum = [a\<^isub>1, a\<^isub>2, a\<^isub>3, a\<^isub>4, a\<^isub>5]"

instance proof
qed (auto simp add: enum_finite_5_def intro: finite_5.exhaust)

end

hide_const a\<^isub>1 a\<^isub>2 a\<^isub>3 a\<^isub>4 a\<^isub>5


hide_type finite_1 finite_2 finite_3 finite_4 finite_5
hide_const (open) enum n_lists product

end
