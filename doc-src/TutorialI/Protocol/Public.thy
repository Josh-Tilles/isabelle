(*  Title:      HOL/Auth/Public
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of Public Keys (common to all public-key protocols)

Private and public keys; initial states of agents
*)

theory Public imports Event
uses ("Public_lemmas.ML") begin

consts
  pubK    :: "agent => key"

syntax
  priK    :: "agent => key"

translations  (*BEWARE! expressions like  (inj priK)  will NOT work!*)
  "priK x"  == "invKey(pubK x)"

primrec
        (*Agents know their private key and all public keys*)
  initState_Server:  "initState Server     =    
 		         insert (Key (priK Server)) (Key ` range pubK)"
  initState_Friend:  "initState (Friend i) =    
 		         insert (Key (priK (Friend i))) (Key ` range pubK)"
  initState_Spy:     "initState Spy        =    
 		         (Key`invKey`pubK`bad) Un (Key ` range pubK)"


axioms
  (*Public keys are disjoint, and never clash with private keys*)
  inj_pubK:        "inj pubK"
  priK_neq_pubK:   "priK A ~= pubK B"

use "Public_lemmas.ML"

(*Specialized methods*)

method_setup possibility = {*
    Method.no_args (Method.METHOD (fn facts => possibility_tac)) *}
    "for proving possibility theorems"

end
