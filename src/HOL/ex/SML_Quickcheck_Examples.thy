(*  Title:      HOL/ex/SML_Quickcheck_Examples.thy
    Author:     Stefan Berghofer, Lukas Bulwahn
    Copyright   2011 TU Muenchen
*)

theory SML_Quickcheck_Examples
imports "~~/src/HOL/Library/SML_Quickcheck"
begin

text {*
This is a regression test for the 'quickcheck' counterexample generator based on the
SML code generator.

The counterexample generator has been superseded by counterexample generators based on
the generic code generator.
*}

declare [[quickcheck_finite_types = false]]

subsection {* Lists *}

theorem "map g (map f xs) = map (g o f) xs"
  quickcheck[SML, expect = no_counterexample]
  oops

theorem "map g (map f xs) = map (f o g) xs"
  quickcheck[SML, expect = counterexample]
  oops

theorem "rev (xs @ ys) = rev ys @ rev xs"
  quickcheck[SML, expect = no_counterexample]
  oops

theorem "rev (xs @ ys) = rev xs @ rev ys"
  quickcheck[SML, expect = counterexample]
  oops

theorem "rev (rev xs) = xs"
  quickcheck[SML, expect = no_counterexample]
  oops

theorem "rev xs = xs"
  quickcheck[tester = SML, expect = counterexample]
oops


text {* An example involving functions inside other data structures *}

primrec app :: "('a \<Rightarrow> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "app [] x = x"
  | "app (f # fs) x = app fs (f x)"

lemma "app (fs @ gs) x = app gs (app fs x)"
  quickcheck[SML, expect = no_counterexample]
  by (induct fs arbitrary: x) simp_all

lemma "app (fs @ gs) x = app fs (app gs x)"
  quickcheck[SML, expect = counterexample]
  oops

primrec occurs :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "occurs a [] = 0"
  | "occurs a (x#xs) = (if (x=a) then Suc(occurs a xs) else occurs a xs)"

primrec del1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "del1 a [] = []"
  | "del1 a (x#xs) = (if (x=a) then xs else (x#del1 a xs))"

text {* A lemma, you'd think to be true from our experience with delAll *}
lemma "Suc (occurs a (del1 a xs)) = occurs a xs"
  -- {* Wrong. Precondition needed.*}
  quickcheck[SML, expect = counterexample]
  oops

lemma "xs ~= [] \<longrightarrow> Suc (occurs a (del1 a xs)) = occurs a xs"
  quickcheck[SML, expect = counterexample]
    -- {* Also wrong.*}
  oops

lemma "0 < occurs a xs \<longrightarrow> Suc (occurs a (del1 a xs)) = occurs a xs"
  quickcheck[SML, expect = no_counterexample]
  by (induct xs) auto

primrec replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "replace a b [] = []"
  | "replace a b (x#xs) = (if (x=a) then (b#(replace a b xs)) 
                            else (x#(replace a b xs)))"

lemma "occurs a xs = occurs b (replace a b xs)"
  quickcheck[SML, expect = counterexample]
  -- {* Wrong. Precondition needed.*}
  oops

lemma "occurs b xs = 0 \<or> a=b \<longrightarrow> occurs a xs = occurs b (replace a b xs)"
  quickcheck[SML, expect = no_counterexample]
  by (induct xs) simp_all


subsection {* Trees *}

datatype 'a tree = Twig |  Leaf 'a | Branch "'a tree" "'a tree"

primrec leaves :: "'a tree \<Rightarrow> 'a list" where
  "leaves Twig = []"
  | "leaves (Leaf a) = [a]"
  | "leaves (Branch l r) = (leaves l) @ (leaves r)"

primrec plant :: "'a list \<Rightarrow> 'a tree" where
  "plant [] = Twig "
  | "plant (x#xs) = Branch (Leaf x) (plant xs)"

primrec mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror (Twig) = Twig "
  | "mirror (Leaf a) = Leaf a "
  | "mirror (Branch l r) = Branch (mirror r) (mirror l)"

theorem "plant (rev (leaves xt)) = mirror xt"
  quickcheck[SML, expect = counterexample]
    --{* Wrong! *} 
  oops

theorem "plant((leaves xt) @ (leaves yt)) = Branch xt yt"
  quickcheck[SML, expect = counterexample]
    --{* Wrong! *} 
  oops

datatype 'a ntree = Tip "'a" | Node "'a" "'a ntree" "'a ntree"

primrec inOrder :: "'a ntree \<Rightarrow> 'a list" where
  "inOrder (Tip a)= [a]"
  | "inOrder (Node f x y) = (inOrder x)@[f]@(inOrder y)"

primrec root :: "'a ntree \<Rightarrow> 'a" where
  "root (Tip a) = a"
  | "root (Node f x y) = f"

theorem "hd (inOrder xt) = root xt"
  quickcheck[SML, expect = counterexample]
  --{* Wrong! *} 
  oops

end