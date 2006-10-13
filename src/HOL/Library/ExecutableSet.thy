(*  Title:      HOL/Library/ExecutableSet.thy
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
*)

header {* Implementation of finite sets by lists *}

theory ExecutableSet
imports Main
begin

section {* Definitional equality rewrites *}

instance set :: (eq) eq ..

lemma [code target: Set]:
  "(A = B) = (A \<subseteq> B \<and> B \<subseteq> A)"
  by blast

lemma [code func]:
  "OperationalEquality.eq A B = (A \<subseteq> B \<and> B \<subseteq> A)"
  unfolding eq_def by blast

declare bex_triv_one_point1 [symmetric, standard, code]


section {* HOL definitions *}

subsection {* Basic definitions *}

definition
  flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c"
  "flip f a b = f b a"
  member :: "'a list \<Rightarrow> 'a \<Rightarrow> bool"
  "member xs x = (x \<in> set xs)"
  insertl :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  "insertl x xs = (if member xs x then xs else x#xs)"

lemma
  [code target: List]: "member [] y = False"
  and [code target: List]: "member (x#xs) y = (y = x \<or> member xs y)"
unfolding member_def by (induct xs) simp_all

consts
  drop_first :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"

primrec
  "drop_first f [] = []"
  "drop_first f (x#xs) = (if f x then xs else x # drop_first f xs)"
declare drop_first.simps [code del]
declare drop_first.simps [code target: List]

declare remove1.simps [code del]
lemma [code target: List]:
  "remove1 x xs = (if member xs x then drop_first (\<lambda>y. y = x) xs else xs)"
proof (cases "member xs x")
  case False thus ?thesis unfolding member_def by (induct xs) auto
next
  case True
  have "remove1 x xs = drop_first (\<lambda>y. y = x) xs" by (induct xs) simp_all
  with True show ?thesis by simp
qed

lemma member_nil [simp]:
  "member [] = (\<lambda>x. False)"
proof
  fix x
  show "member [] x = False" unfolding member_def by simp
qed

lemma member_insertl [simp]:
  "x \<in> set (insertl x xs)"
  unfolding insertl_def member_def mem_iff by simp

lemma insertl_member [simp]:
  fixes xs x
  assumes member: "member xs x"
  shows "insertl x xs = xs"
  using member unfolding insertl_def by simp

lemma insertl_not_member [simp]:
  fixes xs x
  assumes member: "\<not> (member xs x)"
  shows "insertl x xs = x # xs"
  using member unfolding insertl_def by simp

lemma foldr_remove1_empty [simp]:
  "foldr remove1 xs [] = []"
  by (induct xs) simp_all


subsection {* Derived definitions *}

function unionl :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "unionl [] ys = ys"
| "unionl xs ys = foldr insertl xs ys"
by pat_completeness auto
termination unionl by (auto_term "{}")
lemmas unionl_def = unionl.simps(2)
declare unionl.simps[code]

function intersect :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "intersect [] ys = []"
| "intersect xs [] = []"
| "intersect xs ys = filter (member xs) ys"
  by pat_completeness auto
termination intersect by (auto_term "{}")
lemmas intersect_def = intersect.simps(3)
declare intersect.simps[code]

function subtract :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "subtract [] ys = ys"
| "subtract xs [] = []"
| "subtract xs ys = foldr remove1 xs ys"
  by pat_completeness auto
termination subtract by (auto_term "{}")
lemmas subtract_def = subtract.simps(3)
declare subtract.simps[code]

function map_distinct :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list"
where
  "map_distinct f [] = []"
| "map_distinct f xs = foldr (insertl o f) xs []"
  by pat_completeness auto
termination map_distinct by (auto_term "{}")
lemmas map_distinct_def = map_distinct.simps(2)
declare map_distinct.simps[code]

function unions :: "'a list list \<Rightarrow> 'a list"
where
  "unions [] = []"
  "unions xs = foldr unionl xs []"
  by pat_completeness auto
termination unions by (auto_term "{}")
lemmas unions_def = unions.simps(2)
declare unions.simps[code]

consts intersects :: "'a list list \<Rightarrow> 'a list"
primrec
  "intersects (x#xs) = foldr intersect xs x"

definition
  map_union :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b list) \<Rightarrow> 'b list"
  "map_union xs f = unions (map f xs)"
  map_inter :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b list) \<Rightarrow> 'b list"
  "map_inter xs f = intersects (map f xs)"


section {* Isomorphism proofs *}

lemma iso_member:
  "member xs x = (x \<in> set xs)"
  unfolding member_def mem_iff ..

lemma iso_insert:
  "set (insertl x xs) = insert x (set xs)"
  unfolding insertl_def iso_member by (simp add: Set.insert_absorb)

lemma iso_remove1:
  assumes distnct: "distinct xs"
  shows "set (remove1 x xs) = set xs - {x}"
using distnct set_remove1_eq by auto

lemma iso_union:
  "set (unionl xs ys) = set xs \<union> set ys"
  unfolding unionl_def
 by (induct xs arbitrary: ys) (simp_all add: iso_insert)

lemma iso_intersect:
  "set (intersect xs ys) = set xs \<inter> set ys"
  unfolding intersect_def Int_def by (simp add: Int_def iso_member) auto

lemma iso_subtract:
  fixes ys
  assumes distnct: "distinct ys"
  shows "set (subtract xs ys) = set ys - set xs"
  and "distinct (subtract xs ys)"
unfolding subtract_def using distnct by (induct xs arbitrary: ys) (simp_all, auto)

corollary iso_subtract':
  fixes xs ys
  assumes distnct: "distinct xs"
  shows "set ((flip subtract) xs ys) = set xs - set ys"
proof -
  from distnct iso_subtract have "set (subtract ys xs) = set xs - set ys" by auto
  thus ?thesis unfolding flip_def by auto
qed

lemma iso_map_distinct:
  "set (map_distinct f xs) = image f (set xs)"
  unfolding map_distinct_def by (induct xs) (simp_all add: iso_insert)

lemma iso_unions:
  "set (unions xss) = \<Union> set (map set xss)"
unfolding unions_def proof (induct xss)
  case Nil show ?case by simp
next
  case (Cons xs xss) thus ?case by (induct xs) (simp_all add: iso_insert)
qed

lemma iso_intersects:
  "set (intersects (xs#xss)) = \<Inter> set (map set (xs#xss))"
  by (induct xss) (simp_all add: Int_def iso_member, auto)

lemma iso_UNION:
  "set (map_union xs f) = UNION (set xs) (set o f)"
  unfolding map_union_def iso_unions by simp

lemma iso_INTER:
  "set (map_inter (x#xs) f) = INTER (set (x#xs)) (set o f)"
  unfolding map_inter_def iso_intersects by (induct xs) (simp_all add: iso_member, auto)

definition
  Blall :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  "Blall = flip list_all"
  Blex :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  "Blex = flip list_ex"

lemma iso_Ball:
  "Blall xs f = Ball (set xs) f"
  unfolding Blall_def flip_def by (induct xs) simp_all

lemma iso_Bex:
  "Blex xs f = Bex (set xs) f"
  unfolding Blex_def flip_def by (induct xs) simp_all


section {* code generator setup *}

ML {*
nonfix inter;
nonfix union;
*}

code_constname
  "ExecutableSet.member" "List.member"
  "ExecutableSet.insertl" "List.insertl"
  "ExecutableSet.drop_first" "List.drop_first"

definition
  "empty_list = []"

declare empty_list_def [code inline]

lemma [code func]:
  "insert (x \<Colon> 'a\<Colon>eq) = insert x" ..

lemma [code func]:
  "(xs \<Colon> 'a\<Colon>eq set) \<union> ys = xs \<union> ys" ..

lemma [code func]:
  "(xs \<Colon> 'a\<Colon>eq set) \<inter> ys = xs \<inter> ys" ..

definition
  "subtract' = flip subtract"

lemma [code func]:
  "image (f \<Colon> 'a \<Rightarrow> 'b\<Colon>eq) = image f" ..

lemma [code func]:
  "UNION xs (f \<Colon> 'a \<Rightarrow> 'b\<Colon>eq set) = UNION xs f" ..

lemma [code func]:
  "INTER xs (f \<Colon> 'a \<Rightarrow> 'b\<Colon>eq set) = INTER xs f" ..

lemma [code func]:
  "Ball (xs \<Colon> 'a\<Colon>type set) = Ball xs" ..

lemma [code func]:
  "Bex (xs \<Colon> 'a\<Colon>type set) = Bex xs" ..

code_abstype "'a set" "'a list" where
  "{}" \<equiv> "empty_list"
  insert \<equiv> insertl
  "op \<union>" \<equiv> unionl
  "op \<inter>" \<equiv> intersect
  "op - \<Colon> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" \<equiv> subtract'
  image \<equiv> map_distinct
  Union \<equiv> unions
  Inter \<equiv> intersects
  UNION \<equiv> map_union
  INTER \<equiv> map_inter
  Ball \<equiv> Blall
  Bex \<equiv> Blex

code_gen "{}" insert "op \<union>" "op \<inter>" "op - \<Colon> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  image Union Inter UNION INTER Ball Bex (SML -)


subsection {* type serializations *}

types_code
  set ("_ list")
attach (term_of) {*
fun term_of_set f T [] = Const ("{}", Type ("set", [T]))
  | term_of_set f T (x :: xs) = Const ("insert",
      T --> Type ("set", [T]) --> Type ("set", [T])) $ f x $ term_of_set f T xs;
*}
attach (test) {*
fun gen_set' aG i j = frequency
  [(i, fn () => aG j :: gen_set' aG (i-1) j), (1, fn () => [])] ()
and gen_set aG i = gen_set' aG i i;
*}


subsection {* const serializations *}

consts_code
  "{}"      ("[]")
  "insert"  ("{*insertl*}")
  "op Un"   ("{*unionl*}")
  "op Int"  ("{*intersect*}")
  "HOL.minus" :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
            ("{*flip subtract*}")
  "image"   ("{*map_distinct*}")
  "Union"   ("{*unions*}")
  "Inter"   ("{*intersects*}")
  "UNION"   ("{*map_union*}")
  "INTER"   ("{*map_inter*}")
  "Ball"    ("{*Blall*}")
  "Bex"     ("{*Blex*}")

end
