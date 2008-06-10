(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A huge set of executable constants *}

theory ExecutableContent
imports
  Main
  Eval
  Enum
  Code_Index
  "~~/src/HOL/ex/Records"
  AssocList
  Binomial
  Commutative_Ring
  "~~/src/HOL/ex/Commutative_Ring_Complete"
  "~~/src/HOL/Real/RealDef"
  GCD
  List_Prefix
  Nat_Infinity
  NatPair
  Nested_Environment
  Option_ord
  Permutation
  Primes
  Product_ord
  SetsAndFunctions
  State_Monad
  While_Combinator
  Word
begin

lemma [code func, code func del]: "(Eval.term_of \<Colon> index \<Rightarrow> term) = Eval.term_of" ..
declare fast_bv_to_nat_helper.simps [code func del]

setup {*
  Code.del_funcs
    (AxClass.param_of_inst @{theory} (@{const_name "Eval.term_of"}, @{type_name "env"}))
*}

end
