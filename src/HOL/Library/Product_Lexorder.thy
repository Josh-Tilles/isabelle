(*  Title:      HOL/Library/Product_Lexorder.thy
    Author:     Norbert Voelker
*)

header {* Lexicographic order on product types *}

theory Product_Lexorder
imports Main
begin

instantiation prod :: (ord, ord) ord
begin

definition
  "x \<le> y \<longleftrightarrow> fst x < fst y \<or> fst x \<le> fst y \<and> snd x \<le> snd y"

definition
  "x < y \<longleftrightarrow> fst x < fst y \<or> fst x \<le> fst y \<and> snd x < snd y"

instance ..

end

lemma less_eq_prod_simp [simp, code]:
  "(x1, y1) \<le> (x2, y2) \<longleftrightarrow> x1 < x2 \<or> x1 \<le> x2 \<and> y1 \<le> y2"
  by (simp add: less_eq_prod_def)

lemma less_prod_simp [simp, code]:
  "(x1, y1) < (x2, y2) \<longleftrightarrow> x1 < x2 \<or> x1 \<le> x2 \<and> y1 < y2"
  by (simp add: less_prod_def)

text {* A stronger version for partial orders. *}

lemma less_prod_def':
  fixes x y :: "'a::order \<times> 'b::ord"
  shows "x < y \<longleftrightarrow> fst x < fst y \<or> fst x = fst y \<and> snd x < snd y"
  by (auto simp add: less_prod_def le_less)

instance prod :: (preorder, preorder) preorder
  by default (auto simp: less_eq_prod_def less_prod_def less_le_not_le intro: order_trans)

instance prod :: (order, order) order
  by default (auto simp add: less_eq_prod_def)

instance prod :: (linorder, linorder) linorder
  by default (auto simp: less_eq_prod_def)

instantiation prod :: (linorder, linorder) distrib_lattice
begin

definition
  "(inf :: 'a \<times> 'b \<Rightarrow> _ \<Rightarrow> _) = min"

definition
  "(sup :: 'a \<times> 'b \<Rightarrow> _ \<Rightarrow> _) = max"

instance
  by default (auto simp add: inf_prod_def sup_prod_def min_max.sup_inf_distrib1)

end

instantiation prod :: (bot, bot) bot
begin

definition
  "bot = (bot, bot)"

instance
  by default (auto simp add: bot_prod_def)

end

instantiation prod :: (top, top) top
begin

definition
  "top = (top, top)"

instance
  by default (auto simp add: top_prod_def)

end

instance prod :: (wellorder, wellorder) wellorder
proof
  fix P :: "'a \<times> 'b \<Rightarrow> bool" and z :: "'a \<times> 'b"
  assume P: "\<And>x. (\<And>y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x"
  show "P z"
  proof (induct z)
    case (Pair a b)
    show "P (a, b)"
    proof (induct a arbitrary: b rule: less_induct)
      case (less a\<^isub>1) note a\<^isub>1 = this
      show "P (a\<^isub>1, b)"
      proof (induct b rule: less_induct)
        case (less b\<^isub>1) note b\<^isub>1 = this
        show "P (a\<^isub>1, b\<^isub>1)"
        proof (rule P)
          fix p assume p: "p < (a\<^isub>1, b\<^isub>1)"
          show "P p"
          proof (cases "fst p < a\<^isub>1")
            case True
            then have "P (fst p, snd p)" by (rule a\<^isub>1)
            then show ?thesis by simp
          next
            case False
            with p have 1: "a\<^isub>1 = fst p" and 2: "snd p < b\<^isub>1"
              by (simp_all add: less_prod_def')
            from 2 have "P (a\<^isub>1, snd p)" by (rule b\<^isub>1)
            with 1 show ?thesis by simp
          qed
        qed
      qed
    qed
  qed
qed

text {* Legacy lemma bindings *}

lemmas prod_le_def = less_eq_prod_def
lemmas prod_less_def = less_prod_def
lemmas prod_less_eq = less_prod_def'

end

