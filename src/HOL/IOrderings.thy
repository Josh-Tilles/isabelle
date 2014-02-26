theory IOrderings
imports IHOL
begin

subsection {* Abstract ordering *}

locale ordering =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 50)
   and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<prec>" 50)
  assumes strict_iff_order: "a \<prec> b \<longleftrightarrow> a \<preceq> b \<and> a \<noteq> b"
  assumes refl: "a \<preceq> a" -- {* not @{text iff}: makes problems due to multiple (dual) interpretations *}
    and antisym: "a \<preceq> b \<Longrightarrow> b \<preceq> a \<Longrightarrow> a = b"
    and trans: "a \<preceq> b \<Longrightarrow> b \<preceq> c \<Longrightarrow> a \<preceq> c"

locale ordering_top = ordering +
  fixes top :: "'a"
  assumes extremum [simp]: "a \<preceq> top"

subsection {* Syntactic orders *}

locale ord =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

consts less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

context ord begin
notation
  less_eq  ("op <=") and
  less_eq  ("(_/ <= _)" [51, 51] 50) and
  less  ("op <") and
  less  ("(_/ < _)"  [51, 51] 50)
  
notation (xsymbols)
  less_eq  ("op \<le>") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50)

notation (HTML output)
  less_eq  ("op \<le>") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50)

abbreviation (input)
  greater_eq  (infix ">=" 50) where
  "x >= y \<equiv> y <= x"

notation (input)
  greater_eq  (infix "\<ge>" 50)

abbreviation (input)
  greater  (infix ">" 50) where
  "x > y \<equiv> y < x"

end

subsection {* Quasi orders *}

locale preorder = ord +
  assumes less_le_not_le: "x < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"
  and order_refl: "x \<le> x"
  and order_trans: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
begin

text {* Reflexivity. *}

lemma eq_refl: "x = y \<Longrightarrow> x \<le> y"
    -- {* This form is useful with the classical reasoner. *}
by (erule ssubst) (rule order_refl)

end

end
