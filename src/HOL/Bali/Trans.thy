(*  Title:      HOL/Bali/Trans.thy
    ID:         $Id$
    Author:     David von Oheimb
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Operational transition (small-step) semantics of the 
execution of Java expressions and statements

PRELIMINARY!!!!!!!!

improvements over Java Specification 1.0 (cf. 15.11.4.4):
* dynamic method lookup does not need to check the return type
* throw raises a NullPointer exception if a null reference is given, and each
  throw of a system exception yield a fresh exception object (was not specified)
* if there is not enough memory even to allocate an OutOfMemory exception,
  evaluation/execution fails, i.e. simply stops (was not specified)

design issues:
* Lit expressions and Skip statements are considered completely evaluated.
* the expr entry in rules is redundant in case of exceptions, but its full
  inclusion helps to make the rule structure independent of exception occurence.
* the rule format is such that the start state may contain an exception.
  ++ faciliates exception handling (to be added later)
  +  symmetry
* the rules are defined carefully in order to be applicable even in not
  type-correct situations (yielding undefined values),
  e.g. the_Adr (Val (Bool b)) = arbitrary.
  ++ fewer rules 
  -  less readable because of auxiliary functions like the_Adr
  Alternative: "defensive" evaluation throwing some InternalError exception
               in case of (impossible, for correct programs) type mismatches

simplifications:
* just simple handling (i.e. propagation) of exceptions so far
* dynamic method lookup does not check return type (should not be necessary)
*)

Trans = Eval +

consts
  texpr_tstmt	:: "prog � (((expr � state) � (expr � state)) +
		            ((stmt � state) � (stmt � state))) set"

syntax (symbols)
  texpr :: "[prog, expr � state, expr � state] � bool "("_�_ �1 _"[61,82,82] 81)
  tstmt :: "[prog, stmt � state, stmt � state] � bool "("_�_ �1 _"[61,82,82] 81)
  Ref   :: "loc � expr"

translations

  "G�e_s �1 ex_s'" == "Inl (e_s, ex_s') � texpr_tstmt G"
  "G�s_s �1 s'_s'" == "Inr (s_s, s'_s') � texpr_tstmt G"
  "Ref a" == "Lit (Addr a)"

constdefs
  
  sub_expr_expr :: "(expr � expr) � prop"
  "sub_expr_expr ef � (�G e s e' s'. G�(   e,s) �1 (   e',s') ��
				     G�(ef e,s) �1 (ef e',s'))"

inductive "texpr_tstmt G" intrs 

(* evaluation of expression *)
  (* cf. 15.5 *)
  XcptE	"��v. e � Lit v� ��
				  G�(e,Some xc,s) �1 (Lit arbitrary,Some xc,s)"

 CastXX "PROP sub_expr_expr (Cast T)"

(*
  (* cf. 15.8.1 *)
  NewC	"�new_Addr (heap s) = Some (a,x);
	  s' = assign (hupd[a�init_Obj G C]s) (x,s)� ��
				G�(NewC C,None,s) �1 (Ref a,s')"

  (* cf. 15.9.1 *)
(*NewA1	"sub_expr_expr (NewA T)"*)
  NewA1	"�G�(e,None,s) �1 (e',s')� ��
			      G�(New T[e],None,s) �1 (New T[e'],s')"
  NewA	"�i = the_Intg i'; new_Addr (heap s) = Some (a, x);
	  s' = assign (hupd[a�init_Arr T i]s)(raise_if (i<#0) NegArrSize x,s)� ��
			G�(New T[Lit i'],None,s) �1 (Ref a,s')"
  (* cf. 15.15 *)
  Cast1	"�G�(e,None,s) �1 (e',s')� ��
			      G�(Cast T e,None,s) �1 (Cast T e',s')"
  Cast	"�x'= raise_if (\<questiondown>G,s�v fits T) ClassCast None� ��
		        G�(Cast T (Lit v),None,s) �1 (Lit v,x',s)"

  (* cf. 15.7.1 *)
(*Lit				"G�(Lit v,None,s) �1 (Lit v,None,s)"*)

  (* cf. 15.13.1, 15.2 *)
  LAcc	"�v = the (locals s vn)� ��
			       G�(LAcc vn,None,s) �1 (Lit v,None,s)"

  (* cf. 15.25.1 *)
  LAss1	"�G�(e,None,s) �1 (e',s')� ��
				 G�(f vn:=e,None,s) �1 (vn:=e',s')"
  LAss			    "G�(f vn:=Lit v,None,s) �1 (Lit v,None,lupd[vn�v]s)"

  (* cf. 15.10.1, 15.2 *)
  FAcc1	"�G�(e,None,s) �1 (e',s')� ��
			       G�({T}e..fn,None,s) �1 ({T}e'..fn,s')"
  FAcc	"�v = the (snd (the_Obj (heap s (the_Addr a'))) (fn,T))� ��
			  G�({T}Lit a'..fn,None,s) �1 (Lit v,np a' None,s)"

  (* cf. 15.25.1 *)
  FAss1	"�G�(e1,None,s) �1 (e1',s')� ��
			  G�(f ({T}e1..fn):=e2,None,s) �1 (f({T}e1'..fn):=e2,s')"
  FAss2	"�G�(e2,np a' None,s) �1 (e2',s')� ��
		      G�(f({T}Lit a'..fn):=e2,None,s) �1 (f({T}Lit a'..fn):=e2',s')"
  FAss	"�a = the_Addr a'; (c,fs) = the_Obj (heap s a);
	  s'= assign (hupd[a�Obj c (fs[(fn,T)�v])]s) (None,s)� ��
		   G�(f({T}Lit a'..fn):=Lit v,None,s) �1 (Lit v,s')"





  (* cf. 15.12.1 *)
  AAcc1	"�G�(e1,None,s) �1 (e1',s')� ��
				G�(e1[e2],None,s) �1 (e1'[e2],s')"
  AAcc2	"�G�(e2,None,s) �1 (e2',s')� ��
			    G�(Lit a'[e2],None,s) �1 (Lit a'[e2'],s')"
  AAcc	"�vo = snd (the_Arr (heap s (the_Addr a'))) (the_Intg i');
	  x' = raise_if (vo = None) IndOutBound (np a' None)� ��
			G�(Lit a'[Lit i'],None,s) �1 (Lit (the vo),x',s)"


  (* cf. 15.11.4.1, 15.11.4.2, 15.11.4.4, 15.11.4.5, 14.15 *)
  Call1	"�G�(e,None,s) �1 (e',s')� ��
			  G�(e..mn({pT}p),None,s) �1 (e'..mn({pT}p),s')"
  Call2	"�G�(p,None,s) �1 (p',s')� ��
		     G�(Lit a'..mn({pT}p),None,s) �1 (Lit a'..mn({pT}p'),s')"
  Call	"�a = the_Addr a'; (md,(pn,rT),lvars,blk,res) = 
 			   the (cmethd G (fst (the_Obj (h a))) (mn,pT))� ��
	    G�(Lit a'..mn({pT}Lit pv),None,(h,l)) �1 
      (Body blk res l,np a' x,(h,init_vals lvars[This�a'][Super�a'][pn�pv]))"
  Body1	"�G�(s0,None,s) �1 (s0',s')� ��
		   G�(Body s0    e      l,None,s) �1 (Body s0'  e  l,s')"
  Body2	"�G�(e ,None,s) �1 (e',s')� ��
		   G�(Body Skip  e      l,None,s) �1 (Body Skip e' l,s')"
  Body		  "G�(Body Skip (Lit v) l,None,s) �1 (Lit v,None,(heap s,l))"

(* execution of statements *)

  (* cf. 14.1 *)
  XcptS	"�s0 � Skip� ��
				 G�(s0,Some xc,s) �1 (Skip,Some xc,s)"

  (* cf. 14.5 *)
(*Skip	 			 "G�(Skip,None,s) �1 (Skip,None,s)"*)

  (* cf. 14.2 *)
  Comp1	"�G�(s1,None,s) �1 (s1',s')� ��
			       G�(s1;; s2,None,s) �1 (s1';; s2,s')"
  Comp			    "G�(Skip;; s2,None,s) �1 (s2,None,s)"






  (* cf. 14.7 *)
  Expr1	"�G�(e ,None,s) �1 (e',s')� ��
				G�(Expr e,None,s) �1 (Expr e',s')"
  Expr			 "G�(Expr (Lit v),None,s) �1 (Skip,None,s)"

  (* cf. 14.8.2 *)
  If1	"�G�(e ,None,s) �1 (e',s')� ��
		      G�(If(e) s1 Else s2,None,s) �1 (If(e') s1 Else s2,s')"
  If		 "G�(If(Lit v) s1 Else s2,None,s) �1 
		    (if the_Bool v then s1 else s2,None,s)"

  (* cf. 14.10, 14.10.1 *)
  Loop			  "G�(While(e) s0,None,s) �1 
			     (If(e) (s0;; While(e) s0) Else Skip,None,s)"
*)
  con_defs "[sub_expr_expr_def]"

end
