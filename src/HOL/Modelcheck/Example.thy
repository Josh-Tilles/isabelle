(*  Title:      HOL/Modelcheck/Example.thy
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

Example = MCSyn + 


types
    state = "bool * bool * bool"

consts

  INIT :: "state pred"
  N    :: "[state,state] => bool"
  reach:: "state pred"

defs
  
  INIT_def "INIT x == ~(fst x)&~(fst (snd x))&~(snd (snd x))"

   N_def   "N      == % (x1,x2,x3) (y1,y2,y3).
                        (~x1 & ~x2 & ~x3 &   y1 & ~y2 & ~y3) |   
	                ( x1 & ~x2 & ~x3 &  ~y1 & ~y2 & ~y3) |   
	                ( x1 & ~x2 & ~x3 &   y1 &  y2 &  y3)    "
  
  reach_def "reach  == mu (%Q x. INIT x | (? y. Q y & N y x))"
  

end

