(*  Title:      HOL/Product_Type.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header {* Cartesian products *}

theory Product_Type
imports Fun
uses ("Tools/split_rule.ML")
begin

subsection {* Unit *}

typedef unit = "{True}"
proof
  show "True : ?unit" by blast
qed

constdefs
  Unity :: unit    ("'(')")
  "() == Abs_unit True"

lemma unit_eq: "u = ()"
  by (induct u) (simp add: unit_def Unity_def)

text {*
  Simplification procedure for @{thm [source] unit_eq}.  Cannot use
  this rule directly --- it loops!
*}

ML_setup {*
  val unit_eq_proc =
    let val unit_meta_eq = mk_meta_eq (thm "unit_eq") in
      Simplifier.simproc (Theory.sign_of (the_context ())) "unit_eq" ["x::unit"]
      (fn _ => fn _ => fn t => if HOLogic.is_unit t then NONE else SOME unit_meta_eq)
    end;

  Addsimprocs [unit_eq_proc];
*}

lemma unit_all_eq1: "(!!x::unit. PROP P x) == PROP P ()"
  by simp

lemma unit_all_eq2: "(!!x::unit. PROP P) == PROP P"
  by (rule triv_forall_equality)

lemma unit_induct [induct type: unit]: "P () ==> P x"
  by simp

text {*
  This rewrite counters the effect of @{text unit_eq_proc} on @{term
  [source] "%u::unit. f u"}, replacing it by @{term [source]
  f} rather than by @{term [source] "%u. f ()"}.
*}

lemma unit_abs_eta_conv [simp]: "(%u::unit. f ()) = f"
  by (rule ext) simp


subsection {* Pairs *}

subsubsection {* Type definition *}

constdefs
  Pair_Rep :: "['a, 'b] => ['a, 'b] => bool"
  "Pair_Rep == (%a b. %x y. x=a & y=b)"

global

typedef (Prod)
  ('a, 'b) "*"    (infixr 20)
    = "{f. EX a b. f = Pair_Rep (a::'a) (b::'b)}"
proof
  fix a b show "Pair_Rep a b : ?Prod"
    by blast
qed

syntax (xsymbols)
  "*"      :: "[type, type] => type"         ("(_ \<times>/ _)" [21, 20] 20)
syntax (HTML output)
  "*"      :: "[type, type] => type"         ("(_ \<times>/ _)" [21, 20] 20)

local


subsubsection {* Definitions *}

global

consts
  fst      :: "'a * 'b => 'a"
  snd      :: "'a * 'b => 'b"
  split    :: "[['a, 'b] => 'c, 'a * 'b] => 'c"
  curry    :: "['a * 'b => 'c, 'a, 'b] => 'c"
  prod_fun :: "['a => 'b, 'c => 'd, 'a * 'c] => 'b * 'd"
  Pair     :: "['a, 'b] => 'a * 'b"
  Sigma    :: "['a set, 'a => 'b set] => ('a * 'b) set"

local

defs
  Pair_def:     "Pair a b == Abs_Prod (Pair_Rep a b)"
  fst_def:      "fst p == THE a. EX b. p = Pair a b"
  snd_def:      "snd p == THE b. EX a. p = Pair a b"
  split_def:    "split == (%c p. c (fst p) (snd p))"
  curry_def:    "curry == (%c x y. c (Pair x y))"
  prod_fun_def: "prod_fun f g == split (%x y. Pair (f x) (g y))"
  Sigma_def:    "Sigma A B == UN x:A. UN y:B x. {Pair x y}"

abbreviation
  Times :: "['a set, 'b set] => ('a * 'b) set"  (infixr "<*>" 80)
  "A <*> B == Sigma A (%_. B)"

const_syntax (xsymbols)
  Times  (infixr "\<times>" 80)

const_syntax (HTML output)
  Times  (infixr "\<times>" 80)


subsubsection {* Concrete syntax *}

text {*
  Patterns -- extends pre-defined type @{typ pttrn} used in
  abstractions.
*}

nonterminals
  tuple_args patterns

syntax
  "_tuple"      :: "'a => tuple_args => 'a * 'b"        ("(1'(_,/ _'))")
  "_tuple_arg"  :: "'a => tuple_args"                   ("_")
  "_tuple_args" :: "'a => tuple_args => tuple_args"     ("_,/ _")
  "_pattern"    :: "[pttrn, patterns] => pttrn"         ("'(_,/ _')")
  ""            :: "pttrn => patterns"                  ("_")
  "_patterns"   :: "[pttrn, patterns] => patterns"      ("_,/ _")
  "@Sigma" ::"[pttrn, 'a set, 'b set] => ('a * 'b) set" ("(3SIGMA _:_./ _)" 10)

translations
  "(x, y)"       == "Pair x y"
  "_tuple x (_tuple_args y z)" == "_tuple x (_tuple_arg (_tuple y z))"
  "%(x,y,zs).b"  == "split(%x (y,zs).b)"
  "%(x,y).b"     == "split(%x y. b)"
  "_abs (Pair x y) t" => "%(x,y).t"
  (* The last rule accommodates tuples in `case C ... (x,y) ... => ...'
     The (x,y) is parsed as `Pair x y' because it is logic, not pttrn *)
  "SIGMA x:A. B" == "Sigma A (%x. B)"

(* reconstructs pattern from (nested) splits, avoiding eta-contraction of body*)
(* works best with enclosing "let", if "let" does not avoid eta-contraction   *)
print_translation {*
let fun split_tr' [Abs (x,T,t as (Abs abs))] =
      (* split (%x y. t) => %(x,y) t *)
      let val (y,t') = atomic_abs_tr' abs;
          val (x',t'') = atomic_abs_tr' (x,T,t');
    
      in Syntax.const "_abs" $ (Syntax.const "_pattern" $x'$y) $ t'' end
    | split_tr' [Abs (x,T,(s as Const ("split",_)$t))] =
       (* split (%x. (split (%y z. t))) => %(x,y,z). t *)
       let val (Const ("_abs",_)$(Const ("_pattern",_)$y$z)$t') = split_tr' [t];
           val (x',t'') = atomic_abs_tr' (x,T,t');
       in Syntax.const "_abs"$ 
           (Syntax.const "_pattern"$x'$(Syntax.const "_patterns"$y$z))$t'' end
    | split_tr' [Const ("split",_)$t] =
       (* split (split (%x y z. t)) => %((x,y),z). t *)   
       split_tr' [(split_tr' [t])] (* inner split_tr' creates next pattern *)
    | split_tr' [Const ("_abs",_)$x_y$(Abs abs)] =
       (* split (%pttrn z. t) => %(pttrn,z). t *)
       let val (z,t) = atomic_abs_tr' abs;
       in Syntax.const "_abs" $ (Syntax.const "_pattern" $x_y$z) $ t end
    | split_tr' _ =  raise Match;
in [("split", split_tr')]
end
*}

(* print "split f" as "\<lambda>(x,y). f x y" and "split (\<lambda>x. f x)" as "\<lambda>(x,y). f x y" *) 
typed_print_translation {*
let
  fun split_guess_names_tr' _ T [Abs (x,_,Abs _)] = raise Match
    | split_guess_names_tr' _ T  [Abs (x,xT,t)] =
        (case (head_of t) of
           Const ("split",_) => raise Match
         | _ => let 
                  val (_::yT::_) = binder_types (domain_type T) handle Bind => raise Match;
                  val (y,t') = atomic_abs_tr' ("y",yT,(incr_boundvars 1 t)$Bound 0); 
                  val (x',t'') = atomic_abs_tr' (x,xT,t');
                in Syntax.const "_abs" $ (Syntax.const "_pattern" $x'$y) $ t'' end)
    | split_guess_names_tr' _ T [t] =
       (case (head_of t) of
           Const ("split",_) => raise Match 
         | _ => let 
                  val (xT::yT::_) = binder_types (domain_type T) handle Bind => raise Match;
                  val (y,t') = 
                        atomic_abs_tr' ("y",yT,(incr_boundvars 2 t)$Bound 1$Bound 0); 
                  val (x',t'') = atomic_abs_tr' ("x",xT,t');
                in Syntax.const "_abs" $ (Syntax.const "_pattern" $x'$y) $ t'' end)
    | split_guess_names_tr' _ _ _ = raise Match;
in [("split", split_guess_names_tr')]
end 
*}


subsubsection {* Lemmas and proof tool setup *}

lemma ProdI: "Pair_Rep a b : Prod"
  unfolding Prod_def by blast

lemma Pair_Rep_inject: "Pair_Rep a b = Pair_Rep a' b' ==> a = a' & b = b'"
  apply (unfold Pair_Rep_def)
  apply (drule fun_cong [THEN fun_cong], blast)
  done

lemma inj_on_Abs_Prod: "inj_on Abs_Prod Prod"
  apply (rule inj_on_inverseI)
  apply (erule Abs_Prod_inverse)
  done

lemma Pair_inject:
  assumes "(a, b) = (a', b')"
    and "a = a' ==> b = b' ==> R"
  shows R
  apply (insert prems [unfolded Pair_def])
  apply (rule inj_on_Abs_Prod [THEN inj_onD, THEN Pair_Rep_inject, THEN conjE])
  apply (assumption | rule ProdI)+
  done

lemma Pair_eq [iff]: "((a, b) = (a', b')) = (a = a' & b = b')"
  by (blast elim!: Pair_inject)

lemma fst_conv [simp]: "fst (a, b) = a"
  unfolding fst_def by blast

lemma snd_conv [simp]: "snd (a, b) = b"
  unfolding snd_def by blast

lemma fst_eqD: "fst (x, y) = a ==> x = a"
  by simp

lemma snd_eqD: "snd (x, y) = a ==> y = a"
  by simp

lemma PairE_lemma: "EX x y. p = (x, y)"
  apply (unfold Pair_def)
  apply (rule Rep_Prod [unfolded Prod_def, THEN CollectE])
  apply (erule exE, erule exE, rule exI, rule exI)
  apply (rule Rep_Prod_inverse [symmetric, THEN trans])
  apply (erule arg_cong)
  done

lemma PairE [cases type: *]: "(!!x y. p = (x, y) ==> Q) ==> Q"
  using PairE_lemma [of p] by blast

ML {*
  local val PairE = thm "PairE" in
    fun pair_tac s =
      EVERY' [res_inst_tac [("p", s)] PairE, hyp_subst_tac, K prune_params_tac];
  end;
*}

lemma surjective_pairing: "p = (fst p, snd p)"
  -- {* Do not add as rewrite rule: invalidates some proofs in IMP *}
  by (cases p) simp

lemmas pair_collapse = surjective_pairing [symmetric]
declare pair_collapse [simp]

lemma surj_pair [simp]: "EX x y. z = (x, y)"
  apply (rule exI)
  apply (rule exI)
  apply (rule surjective_pairing)
  done

lemma split_paired_all: "(!!x. PROP P x) == (!!a b. PROP P (a, b))"
proof
  fix a b
  assume "!!x. PROP P x"
  then show "PROP P (a, b)" .
next
  fix x
  assume "!!a b. PROP P (a, b)"
  from `PROP P (fst x, snd x)` show "PROP P x" by simp
qed

lemmas split_tupled_all = split_paired_all unit_all_eq2

text {*
  The rule @{thm [source] split_paired_all} does not work with the
  Simplifier because it also affects premises in congrence rules,
  where this can lead to premises of the form @{text "!!a b. ... =
  ?P(a, b)"} which cannot be solved by reflexivity.
*}

ML_setup {*
  (* replace parameters of product type by individual component parameters *)
  val safe_full_simp_tac = generic_simp_tac true (true, false, false);
  local (* filtering with exists_paired_all is an essential optimization *)
    fun exists_paired_all (Const ("all", _) $ Abs (_, T, t)) =
          can HOLogic.dest_prodT T orelse exists_paired_all t
      | exists_paired_all (t $ u) = exists_paired_all t orelse exists_paired_all u
      | exists_paired_all (Abs (_, _, t)) = exists_paired_all t
      | exists_paired_all _ = false;
    val ss = HOL_basic_ss
      addsimps [thm "split_paired_all", thm "unit_all_eq2", thm "unit_abs_eta_conv"]
      addsimprocs [unit_eq_proc];
  in
    val split_all_tac = SUBGOAL (fn (t, i) =>
      if exists_paired_all t then safe_full_simp_tac ss i else no_tac);
    val unsafe_split_all_tac = SUBGOAL (fn (t, i) =>
      if exists_paired_all t then full_simp_tac ss i else no_tac);
    fun split_all th =
   if exists_paired_all (#prop (Thm.rep_thm th)) then full_simplify ss th else th;
  end;

change_claset (fn cs => cs addSbefore ("split_all_tac", split_all_tac));
*}

lemma split_paired_All [simp]: "(ALL x. P x) = (ALL a b. P (a, b))"
  -- {* @{text "[iff]"} is not a good idea because it makes @{text blast} loop *}
  by fast

lemma curry_split [simp]: "curry (split f) = f"
  by (simp add: curry_def split_def)

lemma split_curry [simp]: "split (curry f) = f"
  by (simp add: curry_def split_def)

lemma curryI [intro!]: "f (a,b) ==> curry f a b"
  by (simp add: curry_def)

lemma curryD [dest!]: "curry f a b ==> f (a,b)"
  by (simp add: curry_def)

lemma curryE: "[| curry f a b ; f (a,b) ==> Q |] ==> Q"
  by (simp add: curry_def)

lemma curry_conv [simp]: "curry f a b = f (a,b)"
  by (simp add: curry_def)

lemma prod_induct [induct type: *]: "!!x. (!!a b. P (a, b)) ==> P x"
  by fast

lemma split_paired_Ex [simp]: "(EX x. P x) = (EX a b. P (a, b))"
  by fast

lemma split_conv [simp]: "split c (a, b) = c a b"
  by (simp add: split_def)

lemmas split = split_conv  -- {* for backwards compatibility *}

lemmas splitI = split_conv [THEN iffD2, standard]
lemmas splitD = split_conv [THEN iffD1, standard]

lemma split_Pair_apply: "split (%x y. f (x, y)) = f"
  -- {* Subsumes the old @{text split_Pair} when @{term f} is the identity function. *}
  apply (rule ext)
  apply (tactic {* pair_tac "x" 1 *}, simp)
  done

lemma split_paired_The: "(THE x. P x) = (THE (a, b). P (a, b))"
  -- {* Can't be added to simpset: loops! *}
  by (simp add: split_Pair_apply)

lemma The_split: "The (split P) = (THE xy. P (fst xy) (snd xy))"
  by (simp add: split_def)

lemma Pair_fst_snd_eq: "!!s t. (s = t) = (fst s = fst t & snd s = snd t)"
by (simp only: split_tupled_all, simp)

lemma prod_eqI [intro?]: "fst p = fst q ==> snd p = snd q ==> p = q"
  by (simp add: Pair_fst_snd_eq)

lemma split_weak_cong: "p = q ==> split c p = split c q"
  -- {* Prevents simplification of @{term c}: much faster *}
  by (erule arg_cong)

lemma split_eta: "(%(x, y). f (x, y)) = f"
  apply (rule ext)
  apply (simp only: split_tupled_all)
  apply (rule split_conv)
  done

lemma cond_split_eta: "(!!x y. f x y = g (x, y)) ==> (%(x, y). f x y) = g"
  by (simp add: split_eta)

text {*
  Simplification procedure for @{thm [source] cond_split_eta}.  Using
  @{thm [source] split_eta} as a rewrite rule is not general enough,
  and using @{thm [source] cond_split_eta} directly would render some
  existing proofs very inefficient; similarly for @{text
  split_beta}. *}

ML_setup {*

local
  val cond_split_eta_ss = HOL_basic_ss addsimps [thm "cond_split_eta"]
  fun  Pair_pat k 0 (Bound m) = (m = k)
  |    Pair_pat k i (Const ("Pair",  _) $ Bound m $ t) = i > 0 andalso
                        m = k+i andalso Pair_pat k (i-1) t
  |    Pair_pat _ _ _ = false;
  fun no_args k i (Abs (_, _, t)) = no_args (k+1) i t
  |   no_args k i (t $ u) = no_args k i t andalso no_args k i u
  |   no_args k i (Bound m) = m < k orelse m > k+i
  |   no_args _ _ _ = true;
  fun split_pat tp i (Abs  (_,_,t)) = if tp 0 i t then SOME (i,t) else NONE
  |   split_pat tp i (Const ("split", _) $ Abs (_, _, t)) = split_pat tp (i+1) t
  |   split_pat tp i _ = NONE;
  fun metaeq ss lhs rhs = mk_meta_eq (Goal.prove (Simplifier.the_context ss) [] []
        (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs,rhs)))
        (K (simp_tac (Simplifier.inherit_context ss cond_split_eta_ss) 1)));

  fun beta_term_pat k i (Abs (_, _, t)) = beta_term_pat (k+1) i t
  |   beta_term_pat k i (t $ u) = Pair_pat k i (t $ u) orelse
                        (beta_term_pat k i t andalso beta_term_pat k i u)
  |   beta_term_pat k i t = no_args k i t;
  fun  eta_term_pat k i (f $ arg) = no_args k i f andalso Pair_pat k i arg
  |    eta_term_pat _ _ _ = false;
  fun subst arg k i (Abs (x, T, t)) = Abs (x, T, subst arg (k+1) i t)
  |   subst arg k i (t $ u) = if Pair_pat k i (t $ u) then incr_boundvars k arg
                              else (subst arg k i t $ subst arg k i u)
  |   subst arg k i t = t;
  fun beta_proc ss (s as Const ("split", _) $ Abs (_, _, t) $ arg) =
        (case split_pat beta_term_pat 1 t of
        SOME (i,f) => SOME (metaeq ss s (subst arg 0 i f))
        | NONE => NONE)
  |   beta_proc _ _ = NONE;
  fun eta_proc ss (s as Const ("split", _) $ Abs (_, _, t)) =
        (case split_pat eta_term_pat 1 t of
          SOME (_,ft) => SOME (metaeq ss s (let val (f $ arg) = ft in f end))
        | NONE => NONE)
  |   eta_proc _ _ = NONE;
in
  val split_beta_proc = Simplifier.simproc (Theory.sign_of (the_context ()))
    "split_beta" ["split f z"] (K beta_proc);
  val split_eta_proc = Simplifier.simproc (Theory.sign_of (the_context ()))
    "split_eta" ["split f"] (K eta_proc);
end;

Addsimprocs [split_beta_proc, split_eta_proc];
*}

lemma split_beta: "(%(x, y). P x y) z = P (fst z) (snd z)"
  by (subst surjective_pairing, rule split_conv)

lemma split_split: "R (split c p) = (ALL x y. p = (x, y) --> R (c x y))"
  -- {* For use with @{text split} and the Simplifier. *}
  by (insert surj_pair [of p], clarify, simp)

text {*
  @{thm [source] split_split} could be declared as @{text "[split]"}
  done after the Splitter has been speeded up significantly;
  precompute the constants involved and don't do anything unless the
  current goal contains one of those constants.
*}

lemma split_split_asm: "R (split c p) = (~(EX x y. p = (x, y) & (~R (c x y))))"
by (subst split_split, simp)


text {*
  \medskip @{term split} used as a logical connective or set former.

  \medskip These rules are for use with @{text blast}; could instead
  call @{text simp} using @{thm [source] split} as rewrite. *}

lemma splitI2: "!!p. [| !!a b. p = (a, b) ==> c a b |] ==> split c p"
  apply (simp only: split_tupled_all)
  apply (simp (no_asm_simp))
  done

lemma splitI2': "!!p. [| !!a b. (a, b) = p ==> c a b x |] ==> split c p x"
  apply (simp only: split_tupled_all)
  apply (simp (no_asm_simp))
  done

lemma splitE: "split c p ==> (!!x y. p = (x, y) ==> c x y ==> Q) ==> Q"
  by (induct p) (auto simp add: split_def)

lemma splitE': "split c p z ==> (!!x y. p = (x, y) ==> c x y z ==> Q) ==> Q"
  by (induct p) (auto simp add: split_def)

lemma splitE2:
  "[| Q (split P z);  !!x y. [|z = (x, y); Q (P x y)|] ==> R |] ==> R"
proof -
  assume q: "Q (split P z)"
  assume r: "!!x y. [|z = (x, y); Q (P x y)|] ==> R"
  show R
    apply (rule r surjective_pairing)+
    apply (rule split_beta [THEN subst], rule q)
    done
qed

lemma splitD': "split R (a,b) c ==> R a b c"
  by simp

lemma mem_splitI: "z: c a b ==> z: split c (a, b)"
  by simp

lemma mem_splitI2: "!!p. [| !!a b. p = (a, b) ==> z: c a b |] ==> z: split c p"
by (simp only: split_tupled_all, simp)

lemma mem_splitE:
  assumes major: "z: split c p"
    and cases: "!!x y. [| p = (x,y); z: c x y |] ==> Q"
  shows Q
  by (rule major [unfolded split_def] cases surjective_pairing)+

declare mem_splitI2 [intro!] mem_splitI [intro!] splitI2' [intro!] splitI2 [intro!] splitI [intro!]
declare mem_splitE [elim!] splitE' [elim!] splitE [elim!]

ML_setup {*
local (* filtering with exists_p_split is an essential optimization *)
  fun exists_p_split (Const ("split",_) $ _ $ (Const ("Pair",_)$_$_)) = true
    | exists_p_split (t $ u) = exists_p_split t orelse exists_p_split u
    | exists_p_split (Abs (_, _, t)) = exists_p_split t
    | exists_p_split _ = false;
  val ss = HOL_basic_ss addsimps [thm "split_conv"];
in
val split_conv_tac = SUBGOAL (fn (t, i) =>
    if exists_p_split t then safe_full_simp_tac ss i else no_tac);
end;
(* This prevents applications of splitE for already splitted arguments leading
   to quite time-consuming computations (in particular for nested tuples) *)
change_claset (fn cs => cs addSbefore ("split_conv_tac", split_conv_tac));
*}

lemma split_eta_SetCompr [simp]: "(%u. EX x y. u = (x, y) & P (x, y)) = P"
  by (rule ext) fast

lemma split_eta_SetCompr2 [simp]: "(%u. EX x y. u = (x, y) & P x y) = split P"
  by (rule ext) fast

lemma split_part [simp]: "(%(a,b). P & Q a b) = (%ab. P & split Q ab)"
  -- {* Allows simplifications of nested splits in case of independent predicates. *}
  by (rule ext) blast

(* Do NOT make this a simp rule as it
   a) only helps in special situations
   b) can lead to nontermination in the presence of split_def
*)
lemma split_comp_eq: 
  fixes f :: "'a => 'b => 'c" and g :: "'d => 'a"
  shows "(%u. f (g (fst u)) (snd u)) = (split (%x. f (g x)))"
  by (rule ext) auto

lemma The_split_eq [simp]: "(THE (x',y'). x = x' & y = y') = (x, y)"
  by blast

(*
the following  would be slightly more general,
but cannot be used as rewrite rule:
### Cannot add premise as rewrite rule because it contains (type) unknowns:
### ?y = .x
Goal "[| P y; !!x. P x ==> x = y |] ==> (@(x',y). x = x' & P y) = (x,y)"
by (rtac some_equality 1)
by ( Simp_tac 1)
by (split_all_tac 1)
by (Asm_full_simp_tac 1)
qed "The_split_eq";
*)

lemma injective_fst_snd: "!!x y. [|fst x = fst y; snd x = snd y|] ==> x = y"
  by auto


text {*
  \bigskip @{term prod_fun} --- action of the product functor upon
  functions.
*}

lemma prod_fun [simp]: "prod_fun f g (a, b) = (f a, g b)"
  by (simp add: prod_fun_def)

lemma prod_fun_compose: "prod_fun (f1 o f2) (g1 o g2) = (prod_fun f1 g1 o prod_fun f2 g2)"
  apply (rule ext)
  apply (tactic {* pair_tac "x" 1 *}, simp)
  done

lemma prod_fun_ident [simp]: "prod_fun (%x. x) (%y. y) = (%z. z)"
  apply (rule ext)
  apply (tactic {* pair_tac "z" 1 *}, simp)
  done

lemma prod_fun_imageI [intro]: "(a, b) : r ==> (f a, g b) : prod_fun f g ` r"
  apply (rule image_eqI)
  apply (rule prod_fun [symmetric], assumption)
  done

lemma prod_fun_imageE [elim!]:
  assumes major: "c: (prod_fun f g)`r"
    and cases: "!!x y. [| c=(f(x),g(y));  (x,y):r |] ==> P"
  shows P
  apply (rule major [THEN imageE])
  apply (rule_tac p = x in PairE)
  apply (rule cases)
   apply (blast intro: prod_fun)
  apply blast
  done


constdefs
  upd_fst :: "('a => 'c) => 'a * 'b => 'c * 'b"
 "upd_fst f == prod_fun f id"

  upd_snd :: "('b => 'c) => 'a * 'b => 'a * 'c"
 "upd_snd f == prod_fun id f"

lemma upd_fst_conv [simp]: "upd_fst f (x,y) = (f x,y)" 
  by (simp add: upd_fst_def)

lemma upd_snd_conv [simp]: "upd_snd f (x,y) = (x,f y)" 
  by (simp add: upd_snd_def)

text {*
  \bigskip Disjoint union of a family of sets -- Sigma.
*}

lemma SigmaI [intro!]: "[| a:A;  b:B(a) |] ==> (a,b) : Sigma A B"
  by (unfold Sigma_def) blast

lemma SigmaE [elim!]:
    "[| c: Sigma A B;
        !!x y.[| x:A;  y:B(x);  c=(x,y) |] ==> P
     |] ==> P"
  -- {* The general elimination rule. *}
  by (unfold Sigma_def) blast

text {*
  Elimination of @{term "(a, b) : A \<times> B"} -- introduces no
  eigenvariables.
*}

lemma SigmaD1: "(a, b) : Sigma A B ==> a : A"
  by blast

lemma SigmaD2: "(a, b) : Sigma A B ==> b : B a"
  by blast

lemma SigmaE2:
    "[| (a, b) : Sigma A B;
        [| a:A;  b:B(a) |] ==> P
     |] ==> P"
  by blast

lemma Sigma_cong:
     "\<lbrakk>A = B; !!x. x \<in> B \<Longrightarrow> C x = D x\<rbrakk>
      \<Longrightarrow> (SIGMA x: A. C x) = (SIGMA x: B. D x)"
  by auto

lemma Sigma_mono: "[| A <= C; !!x. x:A ==> B x <= D x |] ==> Sigma A B <= Sigma C D"
  by blast

lemma Sigma_empty1 [simp]: "Sigma {} B = {}"
  by blast

lemma Sigma_empty2 [simp]: "A <*> {} = {}"
  by blast

lemma UNIV_Times_UNIV [simp]: "UNIV <*> UNIV = UNIV"
  by auto

lemma Compl_Times_UNIV1 [simp]: "- (UNIV <*> A) = UNIV <*> (-A)"
  by auto

lemma Compl_Times_UNIV2 [simp]: "- (A <*> UNIV) = (-A) <*> UNIV"
  by auto

lemma mem_Sigma_iff [iff]: "((a,b): Sigma A B) = (a:A & b:B(a))"
  by blast

lemma Times_subset_cancel2: "x:C ==> (A <*> C <= B <*> C) = (A <= B)"
  by blast

lemma Times_eq_cancel2: "x:C ==> (A <*> C = B <*> C) = (A = B)"
  by (blast elim: equalityE)

lemma SetCompr_Sigma_eq:
    "Collect (split (%x y. P x & Q x y)) = (SIGMA x:Collect P. Collect (Q x))"
  by blast

text {*
  \bigskip Complex rules for Sigma.
*}

lemma Collect_split [simp]: "{(a,b). P a & Q b} = Collect P <*> Collect Q"
  by blast

lemma UN_Times_distrib:
  "(UN (a,b):(A <*> B). E a <*> F b) = (UNION A E) <*> (UNION B F)"
  -- {* Suggested by Pierre Chartier *}
  by blast

lemma split_paired_Ball_Sigma [simp]:
    "(ALL z: Sigma A B. P z) = (ALL x:A. ALL y: B x. P(x,y))"
  by blast

lemma split_paired_Bex_Sigma [simp]:
    "(EX z: Sigma A B. P z) = (EX x:A. EX y: B x. P(x,y))"
  by blast

lemma Sigma_Un_distrib1: "(SIGMA i:I Un J. C(i)) = (SIGMA i:I. C(i)) Un (SIGMA j:J. C(j))"
  by blast

lemma Sigma_Un_distrib2: "(SIGMA i:I. A(i) Un B(i)) = (SIGMA i:I. A(i)) Un (SIGMA i:I. B(i))"
  by blast

lemma Sigma_Int_distrib1: "(SIGMA i:I Int J. C(i)) = (SIGMA i:I. C(i)) Int (SIGMA j:J. C(j))"
  by blast

lemma Sigma_Int_distrib2: "(SIGMA i:I. A(i) Int B(i)) = (SIGMA i:I. A(i)) Int (SIGMA i:I. B(i))"
  by blast

lemma Sigma_Diff_distrib1: "(SIGMA i:I - J. C(i)) = (SIGMA i:I. C(i)) - (SIGMA j:J. C(j))"
  by blast

lemma Sigma_Diff_distrib2: "(SIGMA i:I. A(i) - B(i)) = (SIGMA i:I. A(i)) - (SIGMA i:I. B(i))"
  by blast

lemma Sigma_Union: "Sigma (Union X) B = (UN A:X. Sigma A B)"
  by blast

text {*
  Non-dependent versions are needed to avoid the need for higher-order
  matching, especially when the rules are re-oriented.
*}

lemma Times_Un_distrib1: "(A Un B) <*> C = (A <*> C) Un (B <*> C)"
  by blast

lemma Times_Int_distrib1: "(A Int B) <*> C = (A <*> C) Int (B <*> C)"
  by blast

lemma Times_Diff_distrib1: "(A - B) <*> C = (A <*> C) - (B <*> C)"
  by blast


lemma pair_imageI [intro]: "(a, b) : A ==> f a b : (%(a, b). f a b) ` A"
  apply (rule_tac x = "(a, b)" in image_eqI)
   apply auto
  done


text {*
  Setup of internal @{text split_rule}.
*}

constdefs
  internal_split :: "('a => 'b => 'c) => 'a * 'b => 'c"
  "internal_split == split"

lemma internal_split_conv: "internal_split c (a, b) = c a b"
  by (simp only: internal_split_def split_conv)

hide const internal_split

use "Tools/split_rule.ML"
setup SplitRule.setup


subsection {* Code generator setup *}

types_code
  "*"     ("(_ */ _)")
attach (term_of) {*
fun term_of_id_42 f T g U (x, y) = HOLogic.pair_const T U $ f x $ g y;
*}
attach (test) {*
fun gen_id_42 aG bG i = (aG i, bG i);
*}

consts_code
  "Pair"    ("(_,/ _)")

ML {*

fun strip_abs_split 0 t = ([], t)
  | strip_abs_split i (Abs (s, T, t)) =
      let
        val s' = Codegen.new_name t s;
        val v = Free (s', T)
      in apfst (cons v) (strip_abs_split (i-1) (subst_bound (v, t))) end
  | strip_abs_split i (u as Const ("split", _) $ t) = (case strip_abs_split (i+1) t of
        (v :: v' :: vs, u) => (HOLogic.mk_prod (v, v') :: vs, u)
      | _ => ([], u))
  | strip_abs_split i t = ([], t);

fun let_codegen thy defs gr dep thyname brack t = (case strip_comb t of
    (t1 as Const ("Let", _), t2 :: t3 :: ts) =>
    let
      fun dest_let (l as Const ("Let", _) $ t $ u) =
          (case strip_abs_split 1 u of
             ([p], u') => apfst (cons (p, t)) (dest_let u')
           | _ => ([], l))
        | dest_let t = ([], t);
      fun mk_code (gr, (l, r)) =
        let
          val (gr1, pl) = Codegen.invoke_codegen thy defs dep thyname false (gr, l);
          val (gr2, pr) = Codegen.invoke_codegen thy defs dep thyname false (gr1, r);
        in (gr2, (pl, pr)) end
    in case dest_let (t1 $ t2 $ t3) of
        ([], _) => NONE
      | (ps, u) =>
          let
            val (gr1, qs) = foldl_map mk_code (gr, ps);
            val (gr2, pu) = Codegen.invoke_codegen thy defs dep thyname false (gr1, u);
            val (gr3, pargs) = foldl_map
              (Codegen.invoke_codegen thy defs dep thyname true) (gr2, ts)
          in
            SOME (gr3, Codegen.mk_app brack
              (Pretty.blk (0, [Pretty.str "let ", Pretty.blk (0, List.concat
                  (separate [Pretty.str ";", Pretty.brk 1] (map (fn (pl, pr) =>
                    [Pretty.block [Pretty.str "val ", pl, Pretty.str " =",
                       Pretty.brk 1, pr]]) qs))),
                Pretty.brk 1, Pretty.str "in ", pu,
                Pretty.brk 1, Pretty.str "end"])) pargs)
          end
    end
  | _ => NONE);

fun split_codegen thy defs gr dep thyname brack t = (case strip_comb t of
    (t1 as Const ("split", _), t2 :: ts) =>
      (case strip_abs_split 1 (t1 $ t2) of
         ([p], u) =>
           let
             val (gr1, q) = Codegen.invoke_codegen thy defs dep thyname false (gr, p);
             val (gr2, pu) = Codegen.invoke_codegen thy defs dep thyname false (gr1, u);
             val (gr3, pargs) = foldl_map
               (Codegen.invoke_codegen thy defs dep thyname true) (gr2, ts)
           in
             SOME (gr2, Codegen.mk_app brack
               (Pretty.block [Pretty.str "(fn ", q, Pretty.str " =>",
                 Pretty.brk 1, pu, Pretty.str ")"]) pargs)
           end
       | _ => NONE)
  | _ => NONE);

val prod_codegen_setup =
  Codegen.add_codegen "let_codegen" let_codegen
  #> Codegen.add_codegen "split_codegen" split_codegen
  #> CodegenPackage.add_appconst
       ("Let", CodegenPackage.appgen_let)

*}

setup prod_codegen_setup

ML
{*
val Collect_split = thm "Collect_split";
val Compl_Times_UNIV1 = thm "Compl_Times_UNIV1";
val Compl_Times_UNIV2 = thm "Compl_Times_UNIV2";
val PairE = thm "PairE";
val PairE_lemma = thm "PairE_lemma";
val Pair_Rep_inject = thm "Pair_Rep_inject";
val Pair_def = thm "Pair_def";
val Pair_eq = thm "Pair_eq";
val Pair_fst_snd_eq = thm "Pair_fst_snd_eq";
val Pair_inject = thm "Pair_inject";
val ProdI = thm "ProdI";
val SetCompr_Sigma_eq = thm "SetCompr_Sigma_eq";
val SigmaD1 = thm "SigmaD1";
val SigmaD2 = thm "SigmaD2";
val SigmaE = thm "SigmaE";
val SigmaE2 = thm "SigmaE2";
val SigmaI = thm "SigmaI";
val Sigma_Diff_distrib1 = thm "Sigma_Diff_distrib1";
val Sigma_Diff_distrib2 = thm "Sigma_Diff_distrib2";
val Sigma_Int_distrib1 = thm "Sigma_Int_distrib1";
val Sigma_Int_distrib2 = thm "Sigma_Int_distrib2";
val Sigma_Un_distrib1 = thm "Sigma_Un_distrib1";
val Sigma_Un_distrib2 = thm "Sigma_Un_distrib2";
val Sigma_Union = thm "Sigma_Union";
val Sigma_def = thm "Sigma_def";
val Sigma_empty1 = thm "Sigma_empty1";
val Sigma_empty2 = thm "Sigma_empty2";
val Sigma_mono = thm "Sigma_mono";
val The_split = thm "The_split";
val The_split_eq = thm "The_split_eq";
val The_split_eq = thm "The_split_eq";
val Times_Diff_distrib1 = thm "Times_Diff_distrib1";
val Times_Int_distrib1 = thm "Times_Int_distrib1";
val Times_Un_distrib1 = thm "Times_Un_distrib1";
val Times_eq_cancel2 = thm "Times_eq_cancel2";
val Times_subset_cancel2 = thm "Times_subset_cancel2";
val UNIV_Times_UNIV = thm "UNIV_Times_UNIV";
val UN_Times_distrib = thm "UN_Times_distrib";
val Unity_def = thm "Unity_def";
val cond_split_eta = thm "cond_split_eta";
val fst_conv = thm "fst_conv";
val fst_def = thm "fst_def";
val fst_eqD = thm "fst_eqD";
val inj_on_Abs_Prod = thm "inj_on_Abs_Prod";
val injective_fst_snd = thm "injective_fst_snd";
val mem_Sigma_iff = thm "mem_Sigma_iff";
val mem_splitE = thm "mem_splitE";
val mem_splitI = thm "mem_splitI";
val mem_splitI2 = thm "mem_splitI2";
val prod_eqI = thm "prod_eqI";
val prod_fun = thm "prod_fun";
val prod_fun_compose = thm "prod_fun_compose";
val prod_fun_def = thm "prod_fun_def";
val prod_fun_ident = thm "prod_fun_ident";
val prod_fun_imageE = thm "prod_fun_imageE";
val prod_fun_imageI = thm "prod_fun_imageI";
val prod_induct = thm "prod_induct";
val snd_conv = thm "snd_conv";
val snd_def = thm "snd_def";
val snd_eqD = thm "snd_eqD";
val split = thm "split";
val splitD = thm "splitD";
val splitD' = thm "splitD'";
val splitE = thm "splitE";
val splitE' = thm "splitE'";
val splitE2 = thm "splitE2";
val splitI = thm "splitI";
val splitI2 = thm "splitI2";
val splitI2' = thm "splitI2'";
val split_Pair_apply = thm "split_Pair_apply";
val split_beta = thm "split_beta";
val split_conv = thm "split_conv";
val split_def = thm "split_def";
val split_eta = thm "split_eta";
val split_eta_SetCompr = thm "split_eta_SetCompr";
val split_eta_SetCompr2 = thm "split_eta_SetCompr2";
val split_paired_All = thm "split_paired_All";
val split_paired_Ball_Sigma = thm "split_paired_Ball_Sigma";
val split_paired_Bex_Sigma = thm "split_paired_Bex_Sigma";
val split_paired_Ex = thm "split_paired_Ex";
val split_paired_The = thm "split_paired_The";
val split_paired_all = thm "split_paired_all";
val split_part = thm "split_part";
val split_split = thm "split_split";
val split_split_asm = thm "split_split_asm";
val split_tupled_all = thms "split_tupled_all";
val split_weak_cong = thm "split_weak_cong";
val surj_pair = thm "surj_pair";
val surjective_pairing = thm "surjective_pairing";
val unit_abs_eta_conv = thm "unit_abs_eta_conv";
val unit_all_eq1 = thm "unit_all_eq1";
val unit_all_eq2 = thm "unit_all_eq2";
val unit_eq = thm "unit_eq";
val unit_induct = thm "unit_induct";
*}

end
