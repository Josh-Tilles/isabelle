(*  Title:      HOL/MicroJava/JVM/Method.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen

Method invocation
*)

Method = JVMState +

(** method invocation and return instructions **)

datatype 
 meth_inv = 
   Invokevirtual   mname (ty list)      (** inv. instance meth of an object **)
 
consts
 exec_mi :: "[meth_inv,(nat \\<times> 'c)prog,aheap,opstack,p_count] 
		\\<Rightarrow> (xcpt option \\<times> frame list \\<times> opstack \\<times> p_count)" 
primrec
 "exec_mi (Invokevirtual mn ps) G hp stk pc =
	(let n		= length ps;
	     argsoref	= take (n+1) stk;
	     oref	= last argsoref;
	     xp'	= raise_xcpt (oref=Null) NullPointer;
	     dynT	= fst(hp \\<And> (the_Addr oref));
	     (dc,mh,mxl,c)= the (cmethd (G,dynT) (mn,ps));
	     frs'	= xcpt_update xp' [([],rev argsoref@replicate mxl arbitrary,dc,(mn,ps),0)] []
	 in
	 (xp' , frs' , drop (n+1) stk , pc+1))"


constdefs
 exec_mr :: "[opstack,frame list] \\<Rightarrow> frame list"
"exec_mr stk0 frs \\<equiv>
	 (let val			= hd stk0;
	      (stk,loc,cn,met,pc) = hd frs
	  in
	  (val#stk,loc,cn,met,pc)#tl frs)"

end
