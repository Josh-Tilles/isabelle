(*  Title:      HOL/Hoare/HoareAbort.thy
    Author:     Leonor Prensa Nieto & Tobias Nipkow
    Copyright   2003 TUM

Like Hoare.thy, but with an Abort statement for modelling run time errors.
*)

theory Hoare_Logic_Abort
imports Main
uses ("hoare_tac.ML")
begin

types
    'a bexp = "'a set"
    'a assn = "'a set"

datatype
 'a com = Basic "'a \<Rightarrow> 'a"
   | Abort
   | Seq "'a com" "'a com"               ("(_;/ _)"      [61,60] 60)
   | Cond "'a bexp" "'a com" "'a com"    ("(1IF _/ THEN _ / ELSE _/ FI)"  [0,0,0] 61)
   | While "'a bexp" "'a assn" "'a com"  ("(1WHILE _/ INV {_} //DO _ /OD)"  [0,0,0] 61)

abbreviation annskip ("SKIP") where "SKIP == Basic id"

types 'a sem = "'a option => 'a option => bool"

consts iter :: "nat => 'a bexp => 'a sem => 'a sem"
primrec
"iter 0 b S = (\<lambda>s s'. s \<notin> Some ` b \<and> s=s')"
"iter (Suc n) b S =
  (\<lambda>s s'. s \<in> Some ` b \<and> (\<exists>s''. S s s'' \<and> iter n b S s'' s'))"

consts Sem :: "'a com => 'a sem"
primrec
"Sem(Basic f) s s' = (case s of None \<Rightarrow> s' = None | Some t \<Rightarrow> s' = Some(f t))"
"Sem Abort s s' = (s' = None)"
"Sem(c1;c2) s s' = (\<exists>s''. Sem c1 s s'' \<and> Sem c2 s'' s')"
"Sem(IF b THEN c1 ELSE c2 FI) s s' =
 (case s of None \<Rightarrow> s' = None
  | Some t \<Rightarrow> ((t \<in> b \<longrightarrow> Sem c1 s s') \<and> (t \<notin> b \<longrightarrow> Sem c2 s s')))"
"Sem(While b x c) s s' =
 (if s = None then s' = None else \<exists>n. iter n b (Sem c) s s')"

definition Valid :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a bexp \<Rightarrow> bool" where
  "Valid p c q == \<forall>s s'. Sem c s s' \<longrightarrow> s : Some ` p \<longrightarrow> s' : Some ` q"



(** parse translations **)

syntax
  "_assign"  :: "id => 'b => 'a com"        ("(2_ :=/ _)" [70,65] 61)

syntax
  "_hoare_abort_vars" :: "[idts, 'a assn,'a com,'a assn] => bool"
                 ("VARS _// {_} // _ // {_}" [0,0,55,0] 50)
syntax ("" output)
  "_hoare_abort"      :: "['a assn,'a com,'a assn] => bool"
                 ("{_} // _ // {_}" [0,55,0] 50)
ML {*

local
fun free a = Free(a,dummyT)
fun abs((a,T),body) =
  let val a = absfree(a, dummyT, body)
  in if T = Bound 0 then a else Const(Syntax.constrainAbsC,dummyT) $ a $ T end
in

fun mk_abstuple [x] body = abs (x, body)
  | mk_abstuple (x::xs) body =
      Syntax.const @{const_syntax split} $ abs (x, mk_abstuple xs body);

fun mk_fbody a e [x as (b,_)] = if a=b then e else free b
  | mk_fbody a e ((b,_)::xs) =
      Syntax.const @{const_syntax Pair} $ (if a=b then e else free b) $ mk_fbody a e xs;

fun mk_fexp a e xs = mk_abstuple xs (mk_fbody a e xs)
end
*}

(* bexp_tr & assn_tr *)
(*all meta-variables for bexp except for TRUE are translated as if they
  were boolean expressions*)
ML{*
fun bexp_tr (Const ("TRUE", _)) xs = Syntax.const "TRUE"   (* FIXME !? *)
  | bexp_tr b xs = Syntax.const @{const_syntax Collect} $ mk_abstuple xs b;

fun assn_tr r xs = Syntax.const @{const_syntax Collect} $ mk_abstuple xs r;
*}
(* com_tr *)
ML{*
fun com_tr (Const (@{syntax_const "_assign"},_) $ Free (a,_) $ e) xs =
      Syntax.const @{const_syntax Basic} $ mk_fexp a e xs
  | com_tr (Const (@{const_syntax Basic},_) $ f) xs = Syntax.const @{const_syntax Basic} $ f
  | com_tr (Const (@{const_syntax Seq},_) $ c1 $ c2) xs =
      Syntax.const @{const_syntax Seq} $ com_tr c1 xs $ com_tr c2 xs
  | com_tr (Const (@{const_syntax Cond},_) $ b $ c1 $ c2) xs =
      Syntax.const @{const_syntax Cond} $ bexp_tr b xs $ com_tr c1 xs $ com_tr c2 xs
  | com_tr (Const (@{const_syntax While},_) $ b $ I $ c) xs =
      Syntax.const @{const_syntax While} $ bexp_tr b xs $ assn_tr I xs $ com_tr c xs
  | com_tr t _ = t (* if t is just a Free/Var *)
*}

(* triple_tr *)  (* FIXME does not handle "_idtdummy" *)
ML{*
local

fun var_tr (Free (a, _)) = (a, Bound 0) (* Bound 0 = dummy term *)
  | var_tr (Const (@{syntax_const "_constrain"}, _) $ Free (a, _) $ T) = (a, T);

fun vars_tr (Const (@{syntax_const "_idts"}, _) $ idt $ vars) = var_tr idt :: vars_tr vars
  | vars_tr t = [var_tr t]

in
fun hoare_vars_tr [vars, pre, prg, post] =
      let val xs = vars_tr vars
      in Syntax.const @{const_syntax Valid} $
         assn_tr pre xs $ com_tr prg xs $ assn_tr post xs
      end
  | hoare_vars_tr ts = raise TERM ("hoare_vars_tr", ts);
end
*}

parse_translation {* [(@{syntax_const "_hoare_abort_vars"}, hoare_vars_tr)] *}


(*****************************************************************************)

(*** print translations ***)
ML{*
fun dest_abstuple (Const (@{const_syntax split},_) $ (Abs(v,_, body))) =
      subst_bound (Syntax.free v, dest_abstuple body)
  | dest_abstuple (Abs(v,_, body)) = subst_bound (Syntax.free v, body)
  | dest_abstuple trm = trm;

fun abs2list (Const (@{const_syntax split},_) $ (Abs(x,T,t))) = Free (x, T)::abs2list t
  | abs2list (Abs(x,T,t)) = [Free (x, T)]
  | abs2list _ = [];

fun mk_ts (Const (@{const_syntax split},_) $ (Abs(x,_,t))) = mk_ts t
  | mk_ts (Abs(x,_,t)) = mk_ts t
  | mk_ts (Const (@{const_syntax Pair},_) $ a $ b) = a::(mk_ts b)
  | mk_ts t = [t];

fun mk_vts (Const (@{const_syntax split},_) $ (Abs(x,_,t))) =
           ((Syntax.free x)::(abs2list t), mk_ts t)
  | mk_vts (Abs(x,_,t)) = ([Syntax.free x], [t])
  | mk_vts t = raise Match;

fun find_ch [] i xs = (false, (Syntax.free "not_ch", Syntax.free "not_ch"))
  | find_ch ((v,t)::vts) i xs =
      if t = Bound i then find_ch vts (i-1) xs
      else (true, (v, subst_bounds (xs,t)));

fun is_f (Const (@{const_syntax split},_) $ (Abs(x,_,t))) = true
  | is_f (Abs(x,_,t)) = true
  | is_f t = false;
*}

(* assn_tr' & bexp_tr'*)
ML{*
fun assn_tr' (Const (@{const_syntax Collect},_) $ T) = dest_abstuple T
  | assn_tr' (Const (@{const_syntax inter},_) $ (Const (@{const_syntax Collect},_) $ T1) $
        (Const (@{const_syntax Collect},_) $ T2)) =
      Syntax.const @{const_syntax inter} $ dest_abstuple T1 $ dest_abstuple T2
  | assn_tr' t = t;

fun bexp_tr' (Const (@{const_syntax Collect},_) $ T) = dest_abstuple T
  | bexp_tr' t = t;
*}

(*com_tr' *)
ML{*
fun mk_assign f =
  let val (vs, ts) = mk_vts f;
      val (ch, which) = find_ch (vs~~ts) ((length vs)-1) (rev vs)
  in
    if ch then Syntax.const @{syntax_const "_assign"} $ fst which $ snd which
    else Syntax.const @{const_syntax annskip}
  end;

fun com_tr' (Const (@{const_syntax Basic},_) $ f) =
      if is_f f then mk_assign f else Syntax.const @{const_syntax Basic} $ f
  | com_tr' (Const (@{const_syntax Seq},_) $ c1 $ c2) =
      Syntax.const @{const_syntax Seq} $ com_tr' c1 $ com_tr' c2
  | com_tr' (Const (@{const_syntax Cond},_) $ b $ c1 $ c2) =
      Syntax.const @{const_syntax Cond} $ bexp_tr' b $ com_tr' c1 $ com_tr' c2
  | com_tr' (Const (@{const_syntax While},_) $ b $ I $ c) =
      Syntax.const @{const_syntax While} $ bexp_tr' b $ assn_tr' I $ com_tr' c
  | com_tr' t = t;

fun spec_tr' [p, c, q] =
  Syntax.const @{syntax_const "_hoare_abort"} $ assn_tr' p $ com_tr' c $ assn_tr' q
*}

print_translation {* [(@{const_syntax Valid}, spec_tr')] *}

(*** The proof rules ***)

lemma SkipRule: "p \<subseteq> q \<Longrightarrow> Valid p (Basic id) q"
by (auto simp:Valid_def)

lemma BasicRule: "p \<subseteq> {s. f s \<in> q} \<Longrightarrow> Valid p (Basic f) q"
by (auto simp:Valid_def)

lemma SeqRule: "Valid P c1 Q \<Longrightarrow> Valid Q c2 R \<Longrightarrow> Valid P (c1;c2) R"
by (auto simp:Valid_def)

lemma CondRule:
 "p \<subseteq> {s. (s \<in> b \<longrightarrow> s \<in> w) \<and> (s \<notin> b \<longrightarrow> s \<in> w')}
  \<Longrightarrow> Valid w c1 q \<Longrightarrow> Valid w' c2 q \<Longrightarrow> Valid p (Cond b c1 c2) q"
by (fastsimp simp:Valid_def image_def)

lemma iter_aux:
 "! s s'. Sem c s s' \<longrightarrow> s \<in> Some ` (I \<inter> b) \<longrightarrow> s' \<in> Some ` I \<Longrightarrow>
  (\<And>s s'. s \<in> Some ` I \<Longrightarrow> iter n b (Sem c) s s' \<Longrightarrow> s' \<in> Some ` (I \<inter> -b))";
apply(unfold image_def)
apply(induct n)
 apply clarsimp
apply(simp (no_asm_use))
apply blast
done

lemma WhileRule:
 "p \<subseteq> i \<Longrightarrow> Valid (i \<inter> b) c i \<Longrightarrow> i \<inter> (-b) \<subseteq> q \<Longrightarrow> Valid p (While b i c) q"
apply(simp add:Valid_def)
apply(simp (no_asm) add:image_def)
apply clarify
apply(drule iter_aux)
  prefer 2 apply assumption
 apply blast
apply blast
done

lemma AbortRule: "p \<subseteq> {s. False} \<Longrightarrow> Valid p Abort q"
by(auto simp:Valid_def)


subsection {* Derivation of the proof rules and, most importantly, the VCG tactic *}

lemma Compl_Collect: "-(Collect b) = {x. ~(b x)}"
  by blast

use "hoare_tac.ML"

method_setup vcg = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (hoare_tac ctxt (K all_tac))) *}
  "verification condition generator"

method_setup vcg_simp = {*
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (hoare_tac ctxt (asm_full_simp_tac (simpset_of ctxt)))) *}
  "verification condition generator plus simplification"

(* Special syntax for guarded statements and guarded array updates: *)

syntax
  "_guarded_com" :: "bool \<Rightarrow> 'a com \<Rightarrow> 'a com"  ("(2_ \<rightarrow>/ _)" 71)
  "_array_update" :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a com"  ("(2_[_] :=/ _)" [70, 65] 61)
translations
  "P \<rightarrow> c" == "IF P THEN c ELSE CONST Abort FI"
  "a[i] := v" => "(i < CONST length a) \<rightarrow> (a := CONST list_update a i v)"
  (* reverse translation not possible because of duplicate "a" *)

text{* Note: there is no special syntax for guarded array access. Thus
you must write @{text"j < length a \<rightarrow> a[i] := a!j"}. *}

end
