(*  Title:      Cube/Cube.thy
    Author:     Tobias Nipkow
*)

header {* Barendregt's Lambda-Cube *}

theory Cube
imports Pure
begin

setup Pure_Thy.old_appl_syntax_setup

typedecl "term"
typedecl "context"
typedecl typing

nonterminals
  context' typing'

consts
  Abs :: "[term, term => term] => term"
  Prod :: "[term, term => term] => term"
  Trueprop :: "[context, typing] => prop"
  MT_context :: "context"
  Context :: "[typing, context] => context"
  star :: "term"    ("*")
  box :: "term"    ("[]")
  app :: "[term, term] => term"    (infixl "^" 20)
  Has_type :: "[term, term] => typing"

syntax
  "\<^const>Cube.Trueprop" :: "[context', typing'] => prop"    ("(_/ |- _)")
  "_Trueprop1" :: "typing' => prop"    ("(_)")
  "" :: "id => context'"    ("_")
  "" :: "var => context'"    ("_")
  "\<^const>Cube.MT_context" :: "context'"    ("")
  "\<^const>Cube.Context" :: "[typing', context'] => context'"    ("_ _")
  "\<^const>Cube.Has_type" :: "[term, term] => typing'"    ("(_:/ _)" [0, 0] 5)
  "_Lam" :: "[idt, term, term] => term"    ("(3Lam _:_./ _)" [0, 0, 0] 10)
  "_Pi" :: "[idt, term, term] => term"    ("(3Pi _:_./ _)" [0, 0] 10)
  "_arrow" :: "[term, term] => term"    (infixr "->" 10)

translations
  ("prop") "x:X" == ("prop") "|- x:X"
  "Lam x:A. B" == "CONST Abs(A, %x. B)"
  "Pi x:A. B" => "CONST Prod(A, %x. B)"
  "A -> B" => "CONST Prod(A, %_. B)"

syntax (xsymbols)
  "\<^const>Cube.Trueprop" :: "[context', typing'] => prop"    ("(_/ \<turnstile> _)")
  "\<^const>Cube.box" :: "term"    ("\<box>")
  "_Lam" :: "[idt, term, term] => term"    ("(3\<Lambda> _:_./ _)" [0, 0, 0] 10)
  "_Pi" :: "[idt, term, term] => term"    ("(3\<Pi> _:_./ _)" [0, 0] 10)
  "_arrow" :: "[term, term] => term"    (infixr "\<rightarrow>" 10)

print_translation {*
  [(@{const_syntax Prod}, dependent_tr' (@{syntax_const "_Pi"}, @{syntax_const "_arrow"}))]
*}

axioms
  s_b:          "*: []"

  strip_s:      "[| A:*;  a:A ==> G |- x:X |] ==> a:A G |- x:X"
  strip_b:      "[| A:[]; a:A ==> G |- x:X |] ==> a:A G |- x:X"

  app:          "[| F:Prod(A, B); C:A |] ==> F^C: B(C)"

  pi_ss:        "[| A:*; !!x. x:A ==> B(x):* |] ==> Prod(A, B):*"

  lam_ss:       "[| A:*; !!x. x:A ==> f(x):B(x); !!x. x:A ==> B(x):* |]
                   ==> Abs(A, f) : Prod(A, B)"

  beta:          "Abs(A, f)^a == f(a)"

lemmas simple = s_b strip_s strip_b app lam_ss pi_ss
lemmas rules = simple

lemma imp_elim:
  assumes "f:A->B" and "a:A" and "f^a:B ==> PROP P"
  shows "PROP P" by (rule app prems)+

lemma pi_elim:
  assumes "F:Prod(A,B)" and "a:A" and "F^a:B(a) ==> PROP P"
  shows "PROP P" by (rule app prems)+


locale L2 =
  assumes pi_bs: "[| A:[]; !!x. x:A ==> B(x):* |] ==> Prod(A,B):*"
    and lam_bs: "[| A:[]; !!x. x:A ==> f(x):B(x); !!x. x:A ==> B(x):* |]
                   ==> Abs(A,f) : Prod(A,B)"

lemmas (in L2) rules = simple lam_bs pi_bs


locale Lomega =
  assumes
    pi_bb: "[| A:[]; !!x. x:A ==> B(x):[] |] ==> Prod(A,B):[]"
    and lam_bb: "[| A:[]; !!x. x:A ==> f(x):B(x); !!x. x:A ==> B(x):[] |]
                   ==> Abs(A,f) : Prod(A,B)"

lemmas (in Lomega) rules = simple lam_bb pi_bb


locale LP =
  assumes pi_sb: "[| A:*; !!x. x:A ==> B(x):[] |] ==> Prod(A,B):[]"
    and lam_sb: "[| A:*; !!x. x:A ==> f(x):B(x); !!x. x:A ==> B(x):[] |]
                   ==> Abs(A,f) : Prod(A,B)"

lemmas (in LP) rules = simple lam_sb pi_sb


locale LP2 = LP + L2

lemmas (in LP2) rules = simple lam_bs pi_bs lam_sb pi_sb


locale Lomega2 = L2 + Lomega

lemmas (in Lomega2) rules = simple lam_bs pi_bs lam_bb pi_bb


locale LPomega = LP + Lomega

lemmas (in LPomega) rules = simple lam_bb pi_bb lam_sb pi_sb


locale CC = L2 + LP + Lomega

lemmas (in CC) rules = simple lam_bs pi_bs lam_bb pi_bb lam_sb pi_sb

end
