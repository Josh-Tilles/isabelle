(*  Title:      CTT/Arith.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

header {* Arithmetic operators and their definitions *}

theory Arith
imports Bool
begin

text {*
  Proves about elementary arithmetic: addition, multiplication, etc.
  Tests definitions and simplifier.
*}

consts
  "#+"  :: "[i,i]=>i"   (infixr 65)
  "-"   :: "[i,i]=>i"   (infixr 65)
  "|-|" :: "[i,i]=>i"   (infixr 65)
  "#*"  :: "[i,i]=>i"   (infixr 70)
  div   :: "[i,i]=>i"   (infixr 70)
  mod   :: "[i,i]=>i"   (infixr 70)

syntax (xsymbols)
  "op #*"      :: "[i, i] => i"   (infixr "#\<times>" 70)

syntax (HTML output)
  "op #*"      :: "[i, i] => i"   (infixr "#\<times>" 70)

defs
  add_def:     "a#+b == rec(a, b, %u v. succ(v))"
  diff_def:    "a-b == rec(b, a, %u v. rec(v, 0, %x y. x))"
  absdiff_def: "a|-|b == (a-b) #+ (b-a)"
  mult_def:    "a#*b == rec(a, 0, %u v. b #+ v)"
  mod_def:     "a mod b == rec(a, 0, %u v. rec(succ(v) |-| b, 0, %x y. succ(v)))"
  div_def:     "a div b == rec(a, 0, %u v. rec(succ(u) mod b, succ(v), %x y. v))"

ML {* use_legacy_bindings (the_context ()) *}

end
