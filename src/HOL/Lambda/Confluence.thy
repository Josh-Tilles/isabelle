(*  Title: 	HOL/Lambda/Confluence.thy
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1995  TU Muenchen

Abstract confluence notions.
*)

Confluence = Trancl +

consts
  confluent, confluent1, confluent2, diamond, Church_Rosser ::
  "('a*'a)set => bool"

defs
  diamond_def
  "diamond(R) == !x y z. (x,y):R --> (x,z):R --> (EX u. (y,u):R & (z,u):R)" 

  confluent_def "confluent(R) == diamond(R^*)"

  confluent1_def
  "confluent1(R) ==
   !x y z. (x,y):R --> (x,z):R^* --> (EX u. (y,u):R^* & (z,u):R^*)"

  confluent2_def
  "confluent2(R) ==
   !x y z. (x,y):R --> (x,z):R^* --> (EX u. (y,u):R^* & (z,u):R)"

  Church_Rosser_def "Church_Rosser(R) ==   
 !x y. (x,y) : (R Un converse(R))^* --> (? z. (x,z) : R^* & (y,z) : R^*)"
end
