(*  Title:      ZF/AC/AC18_AC19.thy
    ID:         $Id$
    Author:     Krzysztof Grabczewski

Additional definition used in the proof AC19 ==> AC1 which is a part
of the chain AC1 ==> AC18 ==> AC19 ==> AC1
*)

AC18_AC19 = AC_Equiv +

consts
  u_    :: i => i
  
defs

  u_def "u_(a) == {c Un {0}. c \\<in> a}"

end
