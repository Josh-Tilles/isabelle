(*  Title:      HOL/Auth/Kerberos_BAN
    ID:         $Id$
    Author:     Giampaolo Bella, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Kerberos protocol, BAN version.

From page 251 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

Kerberos_BAN = Shared + 

(* Temporal modelization: session keys can be leaked 
                          ONLY when they have expired *)

syntax
    CT :: event list=>nat
    Expired :: [nat, event list] => bool
    RecentAuth :: [nat, event list] => bool

consts

    (*Duration of the session key*)
    SesKeyLife   :: nat

    (*Duration of the authenticator*)
    AutLife :: nat

rules
    (*The ticket should remain fresh for two journeys on the network at least*)
    SesKeyLife_LB    "2 <= SesKeyLife"

    (*The authenticator only for one journey*)
    AutLife_LB    "1 <= AutLife"

translations
   "CT" == "length"
  
   "Expired T evs" == "SesKeyLife + T < CT evs"

   "RecentAuth T evs" == "CT evs <= AutLife + T"

consts  kerberos_ban   :: event list set
inductive "kerberos_ban"
  intrs 

    Nil  "[]: kerberos_ban"

    Fake "[| evs: kerberos_ban;  X: synth (analz (spies evs)) |]
          ==> Says Spy B X # evs : kerberos_ban"


    Kb1  "[| evs1: kerberos_ban |]
          ==> Says A Server {|Agent A, Agent B|} # evs1
                :  kerberos_ban"


    Kb2  "[| evs2: kerberos_ban;  Key KAB ~: used evs2;
             Says A' Server {|Agent A, Agent B|} : set evs2 |]
          ==> Says Server A 
                (Crypt (shrK A)
                   {|Number (CT evs2), Agent B, Key KAB,  
                    (Crypt (shrK B) {|Number (CT evs2), Agent A, Key KAB|})|}) 
                # evs2 : kerberos_ban"


    Kb3  "[| evs3: kerberos_ban;  
             Says S A (Crypt (shrK A) {|Number Ts, Agent B, Key K, X|}) 
               : set evs3;
             Says A Server {|Agent A, Agent B|} : set evs3;
             ~ Expired Ts evs3 |]
          ==> Says A B {|X, Crypt K {|Agent A, Number (CT evs3)|} |} 
               # evs3 : kerberos_ban"


    Kb4  "[| evs4: kerberos_ban;  
             Says A' B {|(Crypt (shrK B) {|Number Ts, Agent A, Key K|}), 
		         (Crypt K {|Agent A, Number Ta|}) |}: set evs4;
             ~ Expired Ts evs4;  RecentAuth Ta evs4 |]
          ==> Says B A (Crypt K (Number Ta)) # evs4
                : kerberos_ban"

         (*Old session keys may become compromised*)
    Oops "[| evso: kerberos_ban;  
             Says Server A (Crypt (shrK A) {|Number Ts, Agent B, Key K, X|})
               : set evso;
             Expired Ts evso |]
          ==> Notes Spy {|Number Ts, Key K|} # evso : kerberos_ban"


end
