(*  Title:      HOLCF/ex/Fix2.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1995 Technische Universitaet Muenchen

 Show that fix is the unique least fixed-point operator. 
 From axioms gix1_def,gix2_def it follows that fix = gix

*)

Fix2 = Fix + 

consts

     gix     :: "('a->'a)->'a"

rules

gix1_def "F$(gix$F) = gix$F"
gix2_def "F$y=y ==> gix$F << y"

end
