(*  Title:      TFL/tfl
    ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Main module
*)

signature TFL_sig =
sig
   datatype pattern = GIVEN of term * int
                    | OMITTED of term * int

   val mk_functional : theory -> term list
                       -> {functional:term,
                           pats: pattern list}

   val wfrec_definition0 : theory -> string -> term -> term -> thm * theory

   val post_definition : theory * (thm * pattern list)
                              -> {theory : theory,
                                  rules  : thm, 
                                    TCs  : term list list,
                          full_pats_TCs  : (term * term list) list, 
                               patterns  : pattern list}


   val wfrec_eqns : theory -> term list
                     -> {WFR : term, 
                         proto_def : term,
                         extracta :(thm * term list) list,
                         pats  : pattern list}


   val lazyR_def : theory
                   -> term list
                   -> {theory:theory,
                       rules :thm,
                           R :term,
                       full_pats_TCs :(term * term list) list, 
                       patterns: pattern list}

   val mk_induction : theory 
                       -> term -> term 
                         -> (term * term list) list
                           -> thm

   val postprocess: {WFtac:tactic, terminator:tactic, simplifier:cterm -> thm}
                     -> theory 
                      -> {rules:thm, induction:thm, TCs:term list list}
                       -> {rules:thm, induction:thm, nested_tcs:thm list}

   structure Context
     : sig
         val read : unit -> thm list
         val write : thm list -> unit
       end
end;
