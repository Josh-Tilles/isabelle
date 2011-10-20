(* Author: Tobias Nipkow *)

header "Abstract Interpretation"

theory Abs_Int0_fun
imports "~~/src/HOL/ex/Interpretation_with_Defs" Big_Step
        "~~/src/HOL/Library/While_Combinator"
begin

subsection "Annotated Commands"

datatype 'a acom =
  SKIP   'a                           ("SKIP {_}") |
  Assign vname aexp 'a                ("(_ ::= _/ {_})" [1000, 61, 0] 61) |
  Semi   "('a acom)" "('a acom)"          ("_;//_"  [60, 61] 60) |
  If     bexp "('a acom)" "('a acom)" 'a
    ("(IF _/ THEN _/ ELSE _//{_})"  [0, 0, 61, 0] 61) |
  While  'a bexp "('a acom)" 'a
    ("({_}//WHILE _/ DO (_)//{_})"  [0, 0, 61, 0] 61)

fun post :: "'a acom \<Rightarrow>'a" where
"post (SKIP {P}) = P" |
"post (x ::= e {P}) = P" |
"post (c1; c2) = post c2" |
"post (IF b THEN c1 ELSE c2 {P}) = P" |
"post ({Inv} WHILE b DO c {P}) = P"

fun strip :: "'a acom \<Rightarrow> com" where
"strip (SKIP {a}) = com.SKIP" |
"strip (x ::= e {a}) = (x ::= e)" |
"strip (c1;c2) = (strip c1; strip c2)" |
"strip (IF b THEN c1 ELSE c2 {a}) = (IF b THEN strip c1 ELSE strip c2)" |
"strip ({a1} WHILE b DO c {a2}) = (WHILE b DO strip c)"

fun anno :: "'a \<Rightarrow> com \<Rightarrow> 'a acom" where
"anno a com.SKIP = SKIP {a}" |
"anno a (x ::= e) = (x ::= e {a})" |
"anno a (c1;c2) = (anno a c1; anno a c2)" |
"anno a (IF b THEN c1 ELSE c2) =
  (IF b THEN anno a c1 ELSE anno a c2 {a})" |
"anno a (WHILE b DO c) =
  ({a} WHILE b DO anno a c {a})"

lemma strip_anno[simp]: "strip (anno a c) = c"
by(induct c) simp_all

fun map_acom :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a acom \<Rightarrow> 'b acom" where
"map_acom f (SKIP {a}) = SKIP {f a}" |
"map_acom f (x ::= e {a}) = (x ::= e {f a})" |
"map_acom f (c1;c2) = (map_acom f c1; map_acom f c2)" |
"map_acom f (IF b THEN c1 ELSE c2 {a}) =
  (IF b THEN map_acom f c1 ELSE map_acom f c2 {f a})" |
"map_acom f ({a1} WHILE b DO c {a2}) =
  ({f a1} WHILE b DO map_acom f c {f a2})"


subsection "Orderings"

class preord =
fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
assumes le_refl[simp]: "x \<sqsubseteq> x"
and le_trans: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
begin

definition mono where "mono f = (\<forall>x y. x \<sqsubseteq> y \<longrightarrow> f x \<sqsubseteq> f y)"

lemma monoD: "mono f \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y" by(simp add: mono_def)

lemma mono_comp: "mono f \<Longrightarrow> mono g \<Longrightarrow> mono (g o f)"
by(simp add: mono_def)

declare le_trans[trans]

end

text{* Note: no antisymmetry. Allows implementations where some abstract
element is implemented by two different values @{prop "x \<noteq> y"}
such that @{prop"x \<sqsubseteq> y"} and @{prop"y \<sqsubseteq> x"}. Antisymmetry is not
needed because we never compare elements for equality but only for @{text"\<sqsubseteq>"}.
*}

class SL_top = preord +
fixes join :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)
fixes Top :: "'a" ("\<top>")
assumes join_ge1 [simp]: "x \<sqsubseteq> x \<squnion> y"
and join_ge2 [simp]: "y \<sqsubseteq> x \<squnion> y"
and join_least: "x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<squnion> y \<sqsubseteq> z"
and top[simp]: "x \<sqsubseteq> \<top>"
begin

lemma join_le_iff[simp]: "x \<squnion> y \<sqsubseteq> z \<longleftrightarrow> x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
by (metis join_ge1 join_ge2 join_least le_trans)

lemma le_join_disj: "x \<sqsubseteq> y \<or> x \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> y \<squnion> z"
by (metis join_ge1 join_ge2 le_trans)

end

instantiation "fun" :: (type, SL_top) SL_top
begin

definition "f \<sqsubseteq> g = (ALL x. f x \<sqsubseteq> g x)"
definition "f \<squnion> g = (\<lambda>x. f x \<squnion> g x)"
definition "\<top> = (\<lambda>x. \<top>)"

lemma join_apply[simp]: "(f \<squnion> g) x = f x \<squnion> g x"
by (simp add: join_fun_def)

instance
proof
  case goal2 thus ?case by (metis le_fun_def preord_class.le_trans)
qed (simp_all add: le_fun_def Top_fun_def)

end


instantiation acom :: (preord) preord
begin

fun le_acom :: "('a::preord)acom \<Rightarrow> 'a acom \<Rightarrow> bool" where
"le_acom (SKIP {S}) (SKIP {S'}) = (S \<sqsubseteq> S')" |
"le_acom (x ::= e {S}) (x' ::= e' {S'}) = (x=x' \<and> e=e' \<and> S \<sqsubseteq> S')" |
"le_acom (c1;c2) (c1';c2') = (le_acom c1 c1' \<and> le_acom c2 c2')" |
"le_acom (IF b THEN c1 ELSE c2 {S}) (IF b' THEN c1' ELSE c2' {S'}) =
  (b=b' \<and> le_acom c1 c1' \<and> le_acom c2 c2' \<and> S \<sqsubseteq> S')" |
"le_acom ({Inv} WHILE b DO c {P}) ({Inv'} WHILE b' DO c' {P'}) =
  (b=b' \<and> le_acom c c' \<and> Inv \<sqsubseteq> Inv' \<and> P \<sqsubseteq> P')" |
"le_acom _ _ = False"

lemma [simp]: "SKIP {S} \<sqsubseteq> c \<longleftrightarrow> (\<exists>S'. c = SKIP {S'} \<and> S \<sqsubseteq> S')"
by (cases c) auto

lemma [simp]: "x ::= e {S} \<sqsubseteq> c \<longleftrightarrow> (\<exists>S'. c = x ::= e {S'} \<and> S \<sqsubseteq> S')"
by (cases c) auto

lemma [simp]: "c1;c2 \<sqsubseteq> c \<longleftrightarrow> (\<exists>c1' c2'. c = c1';c2' \<and> c1 \<sqsubseteq> c1' \<and> c2 \<sqsubseteq> c2')"
by (cases c) auto

lemma [simp]: "IF b THEN c1 ELSE c2 {S} \<sqsubseteq> c \<longleftrightarrow>
  (\<exists>c1' c2' S'. c = IF b THEN c1' ELSE c2' {S'} \<and> c1 \<sqsubseteq> c1' \<and> c2 \<sqsubseteq> c2' \<and> S \<sqsubseteq> S')"
by (cases c) auto

lemma [simp]: "{Inv} WHILE b DO c {P} \<sqsubseteq> w \<longleftrightarrow>
  (\<exists>Inv' c' P'. w = {Inv'} WHILE b DO c' {P'} \<and> c \<sqsubseteq> c' \<and> Inv \<sqsubseteq> Inv' \<and> P \<sqsubseteq> P')"
by (cases w) auto

instance
proof
  case goal1 thus ?case by (induct x) auto
next
  case goal2 thus ?case
  apply(induct x y arbitrary: z rule: le_acom.induct)
  apply (auto intro: le_trans)
  done
qed

end


subsubsection "Lifting"

datatype 'a up = Bot | Up 'a

instantiation up :: (SL_top)SL_top
begin

fun le_up where
"Up x \<sqsubseteq> Up y = (x \<sqsubseteq> y)" |
"Bot \<sqsubseteq> y = True" |
"Up _ \<sqsubseteq> Bot = False"

lemma [simp]: "(x \<sqsubseteq> Bot) = (x = Bot)"
by (cases x) simp_all

lemma [simp]: "(Up x \<sqsubseteq> u) = (\<exists>y. u = Up y & x \<sqsubseteq> y)"
by (cases u) auto

fun join_up where
"Up x \<squnion> Up y = Up(x \<squnion> y)" |
"Bot \<squnion> y = y" |
"x \<squnion> Bot = x"

lemma [simp]: "x \<squnion> Bot = x"
by (cases x) simp_all

definition "\<top> = Up \<top>"

instance proof
  case goal1 show ?case by(cases x, simp_all)
next
  case goal2 thus ?case
    by(cases z, simp, cases y, simp, cases x, auto intro: le_trans)
next
  case goal3 thus ?case by(cases x, simp, cases y, simp_all)
next
  case goal4 thus ?case by(cases y, simp, cases x, simp_all)
next
  case goal5 thus ?case by(cases z, simp, cases y, simp, cases x, simp_all)
next
  case goal6 thus ?case by(cases x, simp_all add: Top_up_def)
qed

end

definition bot_acom :: "com \<Rightarrow> ('a::SL_top)up acom" ("\<bottom>\<^sub>c") where
"\<bottom>\<^sub>c = anno Bot"

lemma strip_bot_acom[simp]: "strip(\<bottom>\<^sub>c c) = c"
by(simp add: bot_acom_def)

lemma bot_acom[rule_format]: "strip c' = c \<longrightarrow> \<bottom>\<^sub>c c \<sqsubseteq> c'"
apply(induct c arbitrary: c')
apply (simp_all add: bot_acom_def)
 apply(induct_tac c')
  apply simp_all
 apply(induct_tac c')
  apply simp_all
 apply(induct_tac c')
  apply simp_all
 apply(induct_tac c')
  apply simp_all
 apply(induct_tac c')
  apply simp_all
done


subsubsection "Post-fixed point iteration"

definition
  pfp :: "(('a::preord) \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a option" where
"pfp f = while_option (\<lambda>x. \<not> f x \<sqsubseteq> x) f"

lemma pfp_pfp: assumes "pfp f x0 = Some x" shows "f x \<sqsubseteq> x"
using while_option_stop[OF assms[simplified pfp_def]] by simp

lemma pfp_least:
assumes mono: "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
and "f p \<sqsubseteq> p" and "x0 \<sqsubseteq> p" and "pfp f x0 = Some x" shows "x \<sqsubseteq> p"
proof-
  { fix x assume "x \<sqsubseteq> p"
    hence  "f x \<sqsubseteq> f p" by(rule mono)
    from this `f p \<sqsubseteq> p` have "f x \<sqsubseteq> p" by(rule le_trans)
  }
  thus "x \<sqsubseteq> p" using assms(2-) while_option_rule[where P = "%x. x \<sqsubseteq> p"]
    unfolding pfp_def by blast
qed

definition
 lpfp\<^isub>c :: "(('a::SL_top)up acom \<Rightarrow> 'a up acom) \<Rightarrow> com \<Rightarrow> 'a up acom option" where
"lpfp\<^isub>c f c = pfp f (\<bottom>\<^sub>c c)"

lemma lpfpc_pfp: "lpfp\<^isub>c f c0 = Some c \<Longrightarrow> f c \<sqsubseteq> c"
by(simp add: pfp_pfp lpfp\<^isub>c_def)

lemma strip_pfp:
assumes "\<And>x. g(f x) = g x" and "pfp f x0 = Some x" shows "g x = g x0"
using assms while_option_rule[where P = "%x. g x = g x0" and c = f]
unfolding pfp_def by metis

lemma strip_lpfpc: assumes "\<And>c. strip(f c) = strip c" and "lpfp\<^isub>c f c = Some c'"
shows "strip c' = c"
using assms(1) strip_pfp[OF _ assms(2)[simplified lpfp\<^isub>c_def]]
by(metis strip_bot_acom)

lemma lpfpc_least:
assumes mono: "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
and "strip p = c0" and "f p \<sqsubseteq> p" and lp: "lpfp\<^isub>c f c0 = Some c" shows "c \<sqsubseteq> p"
using pfp_least[OF _ _ bot_acom[OF `strip p = c0`] lp[simplified lpfp\<^isub>c_def]]
  mono `f p \<sqsubseteq> p`
by blast


subsection "Abstract Interpretation"

definition rep_fun :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'b)set" where
"rep_fun rep F = {f. \<forall>x. f x \<in> rep(F x)}"

fun rep_up :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a up \<Rightarrow> 'b set" where
"rep_up rep Bot = {}" |
"rep_up rep (Up a) = rep a"

text{* The interface for abstract values: *}

locale Val_abs =
fixes rep :: "'a::SL_top \<Rightarrow> val set"
  assumes le_rep: "a \<sqsubseteq> b \<Longrightarrow> rep a \<subseteq> rep b"
  and rep_Top: "rep \<top> = UNIV"
fixes num' :: "val \<Rightarrow> 'a"
and plus' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes rep_num': "n : rep(num' n)"
  and rep_plus':
 "n1 : rep a1 \<Longrightarrow> n2 : rep a2 \<Longrightarrow> n1+n2 : rep(plus' a1 a2)"
begin

abbreviation in_rep (infix "<:" 50)
 where "x <: a == x : rep a"

lemma in_rep_Top[simp]: "x <: \<top>"
by(simp add: rep_Top)

end

type_synonym 'a st = "(vname \<Rightarrow> 'a)"

locale Abs_Int_Fun = Val_abs
begin

fun aval' :: "aexp \<Rightarrow> 'a st \<Rightarrow> 'a" where
"aval' (N n) _ = num' n" |
"aval' (V x) S = S x" |
"aval' (Plus a1 a2) S = plus' (aval' a1 S) (aval' a2 S)"

fun step :: "'a st up \<Rightarrow> 'a st up acom \<Rightarrow> 'a st up acom"
 where
"step S (SKIP {P}) = (SKIP {S})" |
"step S (x ::= e {P}) =
  x ::= e {case S of Bot \<Rightarrow> Bot | Up S \<Rightarrow> Up(S(x := aval' e S))}" |
"step S (c1; c2) = step S c1; step (post c1) c2" |
"step S (IF b THEN c1 ELSE c2 {P}) =
   IF b THEN step S c1 ELSE step S c2 {post c1 \<squnion> post c2}" |
"step S ({Inv} WHILE b DO c {P}) =
  {S \<squnion> post c} WHILE b DO (step Inv c) {Inv}"

definition AI :: "com \<Rightarrow> 'a st up acom option" where
"AI = lpfp\<^isub>c (step \<top>)"


lemma strip_step[simp]: "strip(step S c) = strip c"
by(induct c arbitrary: S) (simp_all add: Let_def)


text{*Lifting @{text "<:"} to other types: *}

abbreviation fun_in_rep :: "state \<Rightarrow> 'a st \<Rightarrow> bool" (infix "<:f" 50) where
"s <:f S == s \<in> rep_fun rep S"

notation fun_in_rep (infix "<:\<^sub>f" 50)

lemma fun_in_rep_le: "s <:f S \<Longrightarrow> S \<sqsubseteq> T \<Longrightarrow> s <:f T"
by(auto simp add: rep_fun_def le_fun_def dest: le_rep)

abbreviation up_in_rep :: "state \<Rightarrow> 'a st up \<Rightarrow> bool"  (infix "<:up" 50) where
"s <:up S == s : rep_up (rep_fun rep) S"

notation (output) up_in_rep (infix "<:\<^sub>u\<^sub>p" 50)

lemma up_fun_in_rep_le: "s <:up S \<Longrightarrow> S \<sqsubseteq> T \<Longrightarrow> s <:up T"
by (cases S) (auto intro:fun_in_rep_le)

lemma in_rep_Top_fun: "s <:f Top"
by(simp add: Top_fun_def rep_fun_def)

lemma in_rep_Top_up: "s <:up Top"
by(simp add: Top_up_def in_rep_Top_fun)


text{* Soundness: *}

lemma aval'_sound: "s <:f S \<Longrightarrow> aval a s <: aval' a S"
by (induct a) (auto simp: rep_num' rep_plus' rep_fun_def)

lemma in_rep_update: "\<lbrakk> s <:f S; i <: a \<rbrakk> \<Longrightarrow> s(x := i) <:f S(x := a)"
by(simp add: rep_fun_def)

lemma step_sound:
  "\<lbrakk> step S c \<sqsubseteq> c; (strip c,s) \<Rightarrow> t; s <:up S \<rbrakk>
   \<Longrightarrow> t <:up post c"
proof(induction c arbitrary: S s t)
  case SKIP thus ?case
    by simp (metis skipE up_fun_in_rep_le)
next
  case Assign thus ?case
    apply (auto simp del: fun_upd_apply split: up.splits)
    by (metis aval'_sound fun_in_rep_le in_rep_update)
next
  case Semi thus ?case by simp blast
next
  case (If b c1 c2 S0) thus ?case
    apply(auto simp: Let_def)
    apply (metis up_fun_in_rep_le)+
    done
next
  case (While Inv b c P)
  from While.prems have inv: "step Inv c \<sqsubseteq> c"
    and "post c \<sqsubseteq> Inv" and "S \<sqsubseteq> Inv" and "Inv \<sqsubseteq> P" by(auto simp: Let_def)
  { fix s t have "(WHILE b DO strip c,s) \<Rightarrow> t \<Longrightarrow> s <:up Inv \<Longrightarrow> t <:up Inv"
    proof(induction "WHILE b DO strip c" s t rule: big_step_induct)
      case WhileFalse thus ?case by simp
    next
      case (WhileTrue s1 s2 s3)
      from WhileTrue.hyps(5)[OF up_fun_in_rep_le[OF While.IH[OF inv `(strip c, s1) \<Rightarrow> s2` `s1 <:up Inv`] `post c \<sqsubseteq> Inv`]]
      show ?case .
    qed
  }
  thus ?case using While.prems(2)
    by simp (metis `s <:up S` `S \<sqsubseteq> Inv` `Inv \<sqsubseteq> P` up_fun_in_rep_le)
qed

lemma AI_sound:
 "\<lbrakk> AI c = Some c';  (c,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> t <:up post c'"
by (metis AI_def in_rep_Top_up lpfpc_pfp step_sound strip_lpfpc strip_step)

end


subsubsection "Monotonicity"

locale Abs_Int_Fun_mono = Abs_Int_Fun +
assumes mono_plus': "a1 \<sqsubseteq> b1 \<Longrightarrow> a2 \<sqsubseteq> b2 \<Longrightarrow> plus' a1 a2 \<sqsubseteq> plus' b1 b2"
begin

lemma mono_aval': "S \<sqsubseteq> S' \<Longrightarrow> aval' e S \<sqsubseteq> aval' e S'"
by(induction e)(auto simp: le_fun_def mono_plus')

lemma mono_update: "a \<sqsubseteq> a' \<Longrightarrow> S \<sqsubseteq> S' \<Longrightarrow> S(x := a) \<sqsubseteq> S'(x := a')"
by(simp add: le_fun_def)

lemma step_mono: "S \<sqsubseteq> S' \<Longrightarrow> step S c \<sqsubseteq> step S' c"
apply(induction c arbitrary: S S')
apply (auto simp: Let_def mono_update mono_aval' le_join_disj split: up.split)
done

end

text{* Problem: not executable because of the comparison of abstract states,
i.e. functions, in the post-fixedpoint computation. *}

end
