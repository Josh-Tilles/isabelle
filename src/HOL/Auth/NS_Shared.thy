(*  Title:      HOL/Auth/NS_Shared
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "ns_shared" for Needham-Schroeder Shared-Key protocol.

From page 247 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

NS_Shared = Shared + 

consts  ns_shared   :: event list set
inductive "ns_shared"
  intrs 
         (*Initial trace is empty*)
    Nil  "[]: ns_shared"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
    Fake "[| evs: ns_shared;  B ~= Spy;  
             X: synth (analz (sees Spy evs)) |]
          ==> Says Spy B X # evs : ns_shared"

         (*Alice initiates a protocol run, requesting to talk to any B*)
    NS1  "[| evs: ns_shared;  A ~= Server;  Nonce NA ~: used evs |]
          ==> Says A Server {|Agent A, Agent B, Nonce NA|} # evs
                :  ns_shared"

         (*Server's response to Alice's message.
           !! It may respond more than once to A's request !!
	   Server doesn't know who the true sender is, hence the A' in
               the sender field.*)
    NS2  "[| evs: ns_shared;  A ~= B;  A ~= Server;  Key KAB ~: used evs;
             Says A' Server {|Agent A, Agent B, Nonce NA|} : set evs |]
          ==> Says Server A 
                (Crypt (shrK A)
                   {|Nonce NA, Agent B, Key KAB,
                     (Crypt (shrK B) {|Key KAB, Agent A|})|}) 
                # evs : ns_shared"

          (*We can't assume S=Server.  Agent A "remembers" her nonce.
            Can inductively show A ~= Server*)
    NS3  "[| evs: ns_shared;  A ~= B;
             Says S A (Crypt (shrK A) {|Nonce NA, Agent B, Key K, X|}) 
               : set evs;
             Says A Server {|Agent A, Agent B, Nonce NA|} : set evs |]
          ==> Says A B X # evs : ns_shared"

         (*Bob's nonce exchange.  He does not know who the message came
           from, but responds to A because she is mentioned inside.*)
    NS4  "[| evs: ns_shared;  A ~= B;  Nonce NB ~: used evs;
             Says A' B (Crypt (shrK B) {|Key K, Agent A|}) : set evs |]
          ==> Says B A (Crypt K (Nonce NB)) # evs
                : ns_shared"

         (*Alice responds with Nonce NB if she has seen the key before.
           Maybe should somehow check Nonce NA again.
           We do NOT send NB-1 or similar as the Spy cannot spoof such things.
           Letting the Spy add or subtract 1 lets him send ALL nonces.
           Instead we distinguish the messages by sending the nonce twice.*)
    NS5  "[| evs: ns_shared;  A ~= B;  
             Says B' A (Crypt K (Nonce NB)) : set evs;
             Says S  A (Crypt (shrK A) {|Nonce NA, Agent B, Key K, X|})
               : set evs |]
          ==> Says A B (Crypt K {|Nonce NB, Nonce NB|}) # evs : ns_shared"
  
         (*This message models possible leaks of session keys.
           The two Nonces identify the protocol run: the rule insists upon
           the true senders in order to make them accurate.*)
    Oops "[| evs: ns_shared;  A ~= Spy;
             Says B A (Crypt K (Nonce NB)) : set evs;
             Says Server A (Crypt (shrK A) {|Nonce NA, Agent B, Key K, X|})
               : set evs |]
          ==> Says A Spy {|Nonce NA, Nonce NB, Key K|} # evs : ns_shared"

end
