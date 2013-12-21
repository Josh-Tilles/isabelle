(*  Title:      HOL/Order_Relation.thy
    Author:     Tobias Nipkow
*)

header {* Orders as Relations *}

theory Order_Relation
imports Wellfounded
begin

subsection{* Orders on a set *}

definition "preorder_on A r \<equiv> refl_on A r \<and> trans r"

definition "partial_order_on A r \<equiv> preorder_on A r \<and> antisym r"

definition "linear_order_on A r \<equiv> partial_order_on A r \<and> total_on A r"

definition "strict_linear_order_on A r \<equiv> trans r \<and> irrefl r \<and> total_on A r"

definition "well_order_on A r \<equiv> linear_order_on A r \<and> wf(r - Id)"

lemmas order_on_defs =
  preorder_on_def partial_order_on_def linear_order_on_def
  strict_linear_order_on_def well_order_on_def


lemma preorder_on_empty[simp]: "preorder_on {} {}"
by(simp add:preorder_on_def trans_def)

lemma partial_order_on_empty[simp]: "partial_order_on {} {}"
by(simp add:partial_order_on_def)

lemma lnear_order_on_empty[simp]: "linear_order_on {} {}"
by(simp add:linear_order_on_def)

lemma well_order_on_empty[simp]: "well_order_on {} {}"
by(simp add:well_order_on_def)


lemma preorder_on_converse[simp]: "preorder_on A (r^-1) = preorder_on A r"
by (simp add:preorder_on_def)

lemma partial_order_on_converse[simp]:
  "partial_order_on A (r^-1) = partial_order_on A r"
by (simp add: partial_order_on_def)

lemma linear_order_on_converse[simp]:
  "linear_order_on A (r^-1) = linear_order_on A r"
by (simp add: linear_order_on_def)


lemma strict_linear_order_on_diff_Id:
  "linear_order_on A r \<Longrightarrow> strict_linear_order_on A (r-Id)"
by(simp add: order_on_defs trans_diff_Id)


subsection{* Orders on the field *}

abbreviation "Refl r \<equiv> refl_on (Field r) r"

abbreviation "Preorder r \<equiv> preorder_on (Field r) r"

abbreviation "Partial_order r \<equiv> partial_order_on (Field r) r"

abbreviation "Total r \<equiv> total_on (Field r) r"

abbreviation "Linear_order r \<equiv> linear_order_on (Field r) r"

abbreviation "Well_order r \<equiv> well_order_on (Field r) r"


lemma subset_Image_Image_iff:
  "\<lbrakk> Preorder r; A \<subseteq> Field r; B \<subseteq> Field r\<rbrakk> \<Longrightarrow>
   r `` A \<subseteq> r `` B \<longleftrightarrow> (\<forall>a\<in>A.\<exists>b\<in>B. (b,a):r)"
unfolding preorder_on_def refl_on_def Image_def
apply (simp add: subset_eq)
unfolding trans_def by fast

lemma subset_Image1_Image1_iff:
  "\<lbrakk> Preorder r; a : Field r; b : Field r\<rbrakk> \<Longrightarrow> r `` {a} \<subseteq> r `` {b} \<longleftrightarrow> (b,a):r"
by(simp add:subset_Image_Image_iff)

lemma Refl_antisym_eq_Image1_Image1_iff:
  assumes r: "Refl r" and as: "antisym r" and abf: "a \<in> Field r" "b \<in> Field r"
  shows "r `` {a} = r `` {b} \<longleftrightarrow> a = b"
proof
  assume "r `` {a} = r `` {b}"
  hence e: "\<And>x. (a, x) \<in> r \<longleftrightarrow> (b, x) \<in> r" by (simp add: set_eq_iff)
  have "(a, a) \<in> r" "(b, b) \<in> r" using r abf by (simp_all add: refl_on_def)
  hence "(a, b) \<in> r" "(b, a) \<in> r" using e[of a] e[of b] by simp_all
  thus "a = b" using as[unfolded antisym_def] by blast
qed fast

lemma Partial_order_eq_Image1_Image1_iff:
  "\<lbrakk>Partial_order r; a:Field r; b:Field r\<rbrakk> \<Longrightarrow> r `` {a} = r `` {b} \<longleftrightarrow> a=b"
by(auto simp:order_on_defs Refl_antisym_eq_Image1_Image1_iff)

lemma Total_Id_Field:
assumes TOT: "Total r" and NID: "\<not> (r <= Id)"
shows "Field r = Field(r - Id)"
using mono_Field[of "r - Id" r] Diff_subset[of r Id]
proof(auto)
  have "r \<noteq> {}" using NID by fast
  then obtain b and c where "b \<noteq> c \<and> (b,c) \<in> r" using NID by auto
  hence 1: "b \<noteq> c \<and> {b,c} \<le> Field r" by (auto simp: Field_def)

  fix a assume *: "a \<in> Field r"
  obtain d where 2: "d \<in> Field r" and 3: "d \<noteq> a"
  using * 1 by auto
  hence "(a,d) \<in> r \<or> (d,a) \<in> r" using * TOT
  by (simp add: total_on_def)
  thus "a \<in> Field(r - Id)" using 3 unfolding Field_def by blast
qed


subsection{* Orders on a type *}

abbreviation "strict_linear_order \<equiv> strict_linear_order_on UNIV"

abbreviation "linear_order \<equiv> linear_order_on UNIV"

abbreviation "well_order \<equiv> well_order_on UNIV"

end