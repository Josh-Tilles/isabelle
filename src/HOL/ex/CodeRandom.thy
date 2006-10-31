(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A simple random engine *}

theory CodeRandom
imports CodeRevappl
begin

section {* A simple random engine *}

consts
  pick :: "(nat \<times> 'a) list \<Rightarrow> nat \<Rightarrow> 'a"

primrec
  "pick (x#xs) n = (let (k, v) = x in
    if n < k then v else pick xs (n - k))"

lemma pick_def [code, simp]:
  "pick ((k, v)#xs) n = (if n < k then v else pick xs (n - k))" by simp
declare pick.simps [simp del, code del]

typedecl randseed

axiomatization
  random_shift :: "randseed \<Rightarrow> randseed"

axiomatization
  random_seed :: "randseed \<Rightarrow> nat"

definition
  random :: "nat \<Rightarrow> randseed \<Rightarrow> nat \<times> randseed"
  "random n s = (random_seed s mod n, random_shift s)"

lemma random_bound:
  assumes "0 < n"
  shows "fst (random n s) < n"
proof -
  from prems mod_less_divisor have "!!m .m mod n < n" by auto
  then show ?thesis unfolding random_def by simp 
qed

lemma random_random_seed [simp]:
  "snd (random n s) = random_shift s" unfolding random_def by simp

definition
  select :: "'a list \<Rightarrow> randseed \<Rightarrow> 'a \<times> randseed"
  [simp]: "select xs s =
    s
    \<triangleright> random (length xs)
    \<turnstile>\<triangleright> (\<lambda>n. Pair (nth xs n))"
  select_weight :: "(nat \<times> 'a) list \<Rightarrow> randseed \<Rightarrow> 'a \<times> randseed"
  [simp]: "select_weight xs s =
    s
    \<triangleright> random (foldl (op +) 0 (map fst xs))
    \<turnstile>\<triangleright> (\<lambda>n. Pair (pick xs n))"

lemma
  "select (x#xs) s = select_weight (map (Pair 1) (x#xs)) s"
proof (induct xs)
  case Nil show ?case by (simp add: revappl random_def)
next
  have map_fst_Pair: "!!xs y. map fst (map (Pair y) xs) = replicate (length xs) y"
  proof -
    fix xs
    fix y
    show "map fst (map (Pair y) xs) = replicate (length xs) y"
      by (induct xs) simp_all
  qed
  have pick_nth: "!!xs n. n < length xs \<Longrightarrow> pick (map (Pair 1) xs) n = nth xs n"
  proof -
    fix xs
    fix n
    assume "n < length xs"
    then show "pick (map (Pair 1) xs) n = nth xs n"
    proof (induct xs arbitrary: n)
      case Nil then show ?case by simp
    next
      case (Cons x xs) show ?case
      proof (cases n)
        case 0 then show ?thesis by simp
      next
        case (Suc _)
    from Cons have "n < length (x # xs)" by auto
        then have "n < Suc (length xs)" by simp
        with Suc have "n - 1 < Suc (length xs) - 1" by auto
        with Cons have "pick (map (Pair (1\<Colon>nat)) xs) (n - 1) = xs ! (n - 1)" by auto
        with Suc show ?thesis by auto
      qed
    qed
  qed
  have sum_length: "!!xs. foldl (op +) 0 (map fst (map (Pair 1) xs)) = length xs"
  proof -
    have replicate_append:
      "!!x xs y. replicate (length (x # xs)) y = replicate (length xs) y @ [y]"
      by (simp add: replicate_app_Cons_same)
    fix xs
    show "foldl (op +) 0 (map fst (map (Pair 1) xs)) = length xs"
    unfolding map_fst_Pair proof (induct xs)
      case Nil show ?case by simp
    next
      case (Cons x xs) then show ?case unfolding replicate_append by simp
    qed
  qed
  have pick_nth_random:
    "!!x xs s. pick (map (Pair 1) (x#xs)) (fst (random (length (x#xs)) s)) = nth (x#xs) (fst (random (length (x#xs)) s))"
  proof -
    fix s
    fix x
    fix xs
    have bound: "fst (random (length (x#xs)) s) < length (x#xs)" by (rule random_bound) simp
    from pick_nth [OF bound] show
      "pick (map (Pair 1) (x#xs)) (fst (random (length (x#xs)) s)) = nth (x#xs) (fst (random (length (x#xs)) s))" .
  qed
  case (Cons x xs) then show ?case
    unfolding select_weight_def sum_length revappl_split pick_nth_random
    by (simp add: revappl_split)
qed

definition
  random_int :: "int \<Rightarrow> randseed \<Rightarrow> int * randseed"
  "random_int k s = (let (l, s') = random (nat k) s in (int l, s'))"

lemma random_nat [code]:
  "random n s = (let (m, s') = random_int (int n) s in (nat m, s'))"
unfolding random_int_def Let_def split_def random_def by simp

axiomatization
  run_random :: "(randseed \<Rightarrow> 'a * randseed) \<Rightarrow> 'a"

ML {*
signature RANDOM =
sig
  type seed = IntInf.int;
  val seed: unit -> seed;
  val value: IntInf.int -> seed -> IntInf.int * seed;
end;

structure Random : RANDOM =
struct

open IntInf;

exception RANDOM;

type seed = int;

local
  val a = fromInt 16807;
    (*greetings to SML/NJ*)
  val m = (the o fromString) "2147483647";
in
  fun next s = (a * s) mod m;
end;

local
  val seed_ref = ref (fromInt 1);
in
  fun seed () =
    let
      val r = next (!seed_ref)
    in
      (seed_ref := r; r)
    end;
end;

fun value h s =
  if h < 1 then raise RANDOM
  else (s mod (h - 1), seed ());

end;
*}

code_type randseed
  (SML "Random.seed")

code_const random_int
  (SML "Random.value")

code_const run_random
  (SML "case _ (Random.seed ()) of (x, '_) => x")

code_gen select select_weight
  (SML -)

end