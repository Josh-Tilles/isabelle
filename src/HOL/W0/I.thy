(* Title:     HOL/W0/I.thy
   ID:        $Id$
   Author:    Thomas Stauner
   Copyright  1995 TU Muenchen

   Recursive definition of type inference algorithm I for Mini_ML.
*)

I = W +

consts
        I :: [expr, typ list, nat, subst] => result_W

primrec
        "I (Var i) a n s = (if i < length a then Ok(s, a!i, n)
                                    else Fail)"
        "I (Abs e) a n s = ( (s,t,m) := I e ((TVar n)#a) (Suc n) s;
                                     Ok(s, TVar n -> t, m) )"
        "I (App e1 e2) a n s =
                   ( (s1,t1,m1) := I e1 a n s;
                     (s2,t2,m2) := I e2 a m1 s1;
                     u := mgu ($s2 t1) ($s2 t2 -> TVar m2);
                     Ok($u o s2, TVar m2, Suc m2) )"
end
