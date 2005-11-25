(*  Title:      HOL/Lambda/ListOrder.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TU Muenchen
*)

header {* Lifting an order to lists of elements *}

theory ListOrder imports Accessible_Part begin

text {*
  Lifting an order to lists of elements, relating exactly one
  element.
*}

constdefs
  step1 :: "('a \<times> 'a) set => ('a list \<times> 'a list) set"
  "step1 r ==
    {(ys, xs). \<exists>us z z' vs. xs = us @ z # vs \<and> (z', z) \<in> r \<and> ys =
      us @ z' # vs}"


lemma step1_converse [simp]: "step1 (r^-1) = (step1 r)^-1"
  apply (unfold step1_def)
  apply blast
  done

lemma in_step1_converse [iff]: "(p \<in> step1 (r^-1)) = (p \<in> (step1 r)^-1)"
  apply auto
  done

lemma not_Nil_step1 [iff]: "([], xs) \<notin> step1 r"
  apply (unfold step1_def)
  apply blast
  done

lemma not_step1_Nil [iff]: "(xs, []) \<notin> step1 r"
  apply (unfold step1_def)
  apply blast
  done

lemma Cons_step1_Cons [iff]:
    "((y # ys, x # xs) \<in> step1 r) =
      ((y, x) \<in> r \<and> xs = ys \<or> x = y \<and> (ys, xs) \<in> step1 r)"
  apply (unfold step1_def)
  apply simp
  apply (rule iffI)
   apply (erule exE)
   apply (rename_tac ts)
   apply (case_tac ts)
    apply fastsimp
   apply force
  apply (erule disjE)
   apply blast
  apply (blast intro: Cons_eq_appendI)
  done

lemma append_step1I:
  "(ys, xs) \<in> step1 r \<and> vs = us \<or> ys = xs \<and> (vs, us) \<in> step1 r
    ==> (ys @ vs, xs @ us) : step1 r"
  apply (unfold step1_def)
  apply auto
   apply blast
  apply (blast intro: append_eq_appendI)
  done

lemma Cons_step1E [elim!]:
  assumes "(ys, x # xs) \<in> step1 r"
    and "!!y. ys = y # xs \<Longrightarrow> (y, x) \<in> r \<Longrightarrow> R"
    and "!!zs. ys = x # zs \<Longrightarrow> (zs, xs) \<in> step1 r \<Longrightarrow> R"
  shows R
  using prems
  apply (cases ys)
   apply (simp add: step1_def)
  apply blast
  done

lemma Snoc_step1_SnocD:
  "(ys @ [y], xs @ [x]) \<in> step1 r
    ==> ((ys, xs) \<in> step1 r \<and> y = x \<or> ys = xs \<and> (y, x) \<in> r)"
  apply (unfold step1_def)
  apply simp
  apply (clarify del: disjCI)
  apply (rename_tac vs)
  apply (rule_tac xs = vs in rev_exhaust)
   apply force
  apply simp
  apply blast
  done

lemma Cons_acc_step1I [intro!]:
    "x \<in> acc r ==> xs \<in> acc (step1 r) \<Longrightarrow> x # xs \<in> acc (step1 r)"
  apply (induct fixing: xs set: acc)
  apply (erule thin_rl)
  apply (erule acc_induct)
  apply (rule accI)
  apply blast
  done

lemma lists_accD: "xs \<in> lists (acc r) ==> xs \<in> acc (step1 r)"
  apply (induct set: lists)
   apply (rule accI)
   apply simp
  apply (rule accI)
  apply (fast dest: acc_downward)
  done

lemma ex_step1I:
  "[| x \<in> set xs; (y, x) \<in> r |]
    ==> \<exists>ys. (ys, xs) \<in> step1 r \<and> y \<in> set ys"
  apply (unfold step1_def)
  apply (drule in_set_conv_decomp [THEN iffD1])
  apply force
  done

lemma lists_accI: "xs \<in> acc (step1 r) ==> xs \<in> lists (acc r)"
  apply (induct set: acc)
  apply clarify
  apply (rule accI)
  apply (drule ex_step1I, assumption)
  apply blast
  done

end
