(*  Title:      HOL/BCV/Kildall.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

Kildall's algorithm
*)

header "Kildall's Algorithm"

theory Kildall = DFA_Framework + While_Combinator:

constdefs
 pres_type :: "(nat => 's => 's) => nat => 's set => bool"
"pres_type step n A == !s:A. !p<n. step p s : A"

 mono :: "'s ord => (nat => 's => 's) => nat => 's set => bool"
"mono r step n A ==
 !s p t. s : A & p < n & s <=_r t --> step p s <=_r step p t"

consts
 iter :: "'s sl \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> (nat \<Rightarrow> nat list) \<Rightarrow>
          's list \<Rightarrow> nat set \<Rightarrow> 's list"
 propa :: "'s binop => nat list => 's => 's list => nat set => 's list * nat set"

primrec
"propa f []     t ss w = (ss,w)"
"propa f (q#qs) t ss w = (let u = t +_f ss!q;
                              w' = (if u = ss!q then w else insert q w)
                          in propa f qs t (ss[q := u]) w')"

defs iter_def:
"\<lbrakk> semilat Arf; acc(fst(snd Arf)); !p:w. p < size ss; bounded succs (size ss);
   set ss <= fst Arf; pres_type step (size ss) (fst Arf) \<rbrakk> \<Longrightarrow>
 iter Arf step succs ss w ==
 fst(while (%(ss,w). w \<noteq> {})
           (%(ss,w). let p = SOME p. p : w
                     in propa (snd(snd Arf)) (succs p) (step p (ss!p)) ss (w-{p}))
           (ss,w))"

constdefs
 unstables ::
 "'s binop => (nat => 's => 's) => (nat => nat list) => 's list => nat set"
"unstables f step succs ss ==
 {p. p < size ss & (? q:set(succs p). step p (ss!p) +_f ss!q ~= ss!q)}"

 kildall :: "'s sl => (nat => 's => 's) => (nat => nat list)
             => 's list => 's list"
"kildall Arf step succs ss ==
 iter Arf step succs ss (unstables (snd(snd Arf)) step succs ss)"

consts merges :: "'s binop => 's => nat list => 's list => 's list"
primrec
"merges f s []     ss = ss"
"merges f s (p#ps) ss = merges f s ps (ss[p := s +_f ss!p])"


lemmas [simp] = Let_def le_iff_plus_unchanged [symmetric]


lemma pres_typeD:
  "[| pres_type step n A; s:A; p<n |] ==> step p s : A"
  by (unfold pres_type_def, blast)

lemma boundedD:
  "[| bounded succs n; p < n; q : set(succs p) |] ==> q < n"
  by (unfold bounded_def, blast)

lemma monoD:
  "[| mono r step n A; p < n; s:A; s <=_r t |] ==> step p s <=_r step p t"
  by (unfold mono_def, blast)

(** merges **)

lemma length_merges [rule_format, simp]:
  "!ss. size(merges f t ps ss) = size ss"
  by (induct_tac ps, auto)

lemma merges_preserves_type [rule_format, simp]:
  "[| semilat(A,r,f) |] ==> 
     !xs. xs : list n A --> x : A --> (!p : set ps. p<n) 
          --> merges f x ps xs : list n A"
  apply (frule semilatDclosedI)
  apply (unfold closed_def)
  apply (induct_tac ps)
  apply auto
  done

lemma merges_incr [rule_format]:
  "[| semilat(A,r,f) |] ==> 
     !xs. xs : list n A --> x : A --> (!p:set ps. p<size xs) --> xs <=[r] merges f x ps xs"
  apply (induct_tac ps)
   apply simp
  apply simp
  apply clarify
  apply (rule order_trans)
    apply simp
   apply (erule list_update_incr)
     apply assumption
    apply simp
   apply simp
  apply (blast intro!: listE_set intro: closedD listE_length [THEN nth_in])
  done

lemma merges_same_conv [rule_format]:
  "[| semilat(A,r,f) |] ==> 
     (!xs. xs : list n A --> x:A --> (!p:set ps. p<size xs) --> 
     (merges f x ps xs = xs) = (!p:set ps. x <=_r xs!p))"
  apply (induct_tac ps)
   apply simp
  apply clarsimp
  apply (rename_tac p ps xs)
  apply (rule iffI)
   apply (rule context_conjI)
    apply (subgoal_tac "xs[p := x +_f xs!p] <=[r] xs")
     apply (force dest!: le_listD simp add: nth_list_update)
    apply (erule subst, rule merges_incr)
        apply assumption
       apply (blast intro!: listE_set intro: closedD listE_length [THEN nth_in])
     apply assumption
    apply simp
   apply clarify
   apply (rotate_tac -2)
   apply (erule allE)
   apply (erule impE)
    apply assumption
   apply (erule impE)
    apply assumption
   apply (drule bspec)
    apply assumption
   apply (simp add: le_iff_plus_unchanged [THEN iffD1] list_update_same_conv [THEN iffD2])
  apply clarify 
  apply (simp add: le_iff_plus_unchanged [THEN iffD1] list_update_same_conv [THEN iffD2])
  done


lemma list_update_le_listI [rule_format]:
  "set xs <= A --> set ys <= A --> xs <=[r] ys --> p < size xs -->  
   x <=_r ys!p --> semilat(A,r,f) --> x:A --> 
   xs[p := x +_f xs!p] <=[r] ys"
  apply (unfold Listn.le_def lesub_def semilat_def)
  apply (simp add: list_all2_conv_all_nth nth_list_update)
  done

lemma merges_pres_le_ub:
  "[| semilat(A,r,f); t:A; set ts <= A; set ss <= A; 
     !p. p:set ps --> t <=_r ts!p; 
     !p. p:set ps --> p<size ts; 
     ss <=[r] ts |] 
  ==> merges f t ps ss <=[r] ts"
proof -
  { fix A r f t ts ps
    have
    "!!qs. [| semilat(A,r,f); set ts <= A; t:A; 
       !p. p:set ps --> t <=_r ts!p; 
       !p. p:set ps --> p<size ts |] ==> 
    set qs <= set ps  --> 
    (!ss. set ss <= A --> ss <=[r] ts --> merges f t qs ss <=[r] ts)"
    apply (induct_tac qs)
     apply simp
    apply (simp (no_asm_simp))
    apply clarify
    apply (rotate_tac -2)
    apply simp
    apply (erule allE, erule impE, erule_tac [2] mp)
     apply (simp (no_asm_simp) add: closedD)
    apply (simp add: list_update_le_listI)
    done
  } note this [dest]
  
  case antecedent
  thus ?thesis by blast
qed


lemma nth_merges [rule_format]:
  "[| semilat (A, r, f); t:A; p < n |] ==> !ss. ss : list n A --> 
     (!p:set ps. p<n) --> 
     (merges f t ps ss)!p = (if p : set ps then t +_f ss!p else ss!p)"
  apply (induct_tac "ps")
   apply simp
  apply (simp add: nth_list_update closedD listE_nth_in) 
  done


(** propa **)

lemma decomp_propa [rule_format]:
  "!ss w. (!q:set qs. q < size ss) --> 
   propa f qs t ss w = 
   (merges f t qs ss, {q. q:set qs & t +_f ss!q ~= ss!q} Un w)"
  apply (induct_tac qs)
   apply simp
  apply (simp (no_asm))
  apply clarify
  apply (rule conjI)
   apply (simp add: nth_list_update)
   apply blast
  apply (simp add: nth_list_update)
  apply blast
  done 

(** iter **)

lemma stable_pres_lemma:
  "[| semilat (A,r,f); pres_type step n A; bounded succs n; 
     ss : list n A; p : w; ! q:w. q < n; 
     ! q. q < n --> q ~: w --> stable r step succs ss q; q < n; 
     q : set (succs p) --> step p (ss ! p) +_f ss ! q = ss ! q; 
     q ~: w | q = p  |] 
  ==> stable r step succs (merges f (step p (ss!p)) (succs p) ss) q"
  apply (unfold stable_def)
  apply (subgoal_tac "step p (ss!p) : A")
   defer
   apply (blast intro: listE_nth_in pres_typeD)     
  apply simp
  apply clarify
  apply (subst nth_merges)
       apply assumption
      apply assumption
     prefer 2
     apply assumption
    apply (blast dest: boundedD)
   apply (blast dest: boundedD)  
  apply (subst nth_merges)
       apply assumption
      apply assumption
     prefer 2
     apply assumption
    apply (blast dest: boundedD)
   apply (blast dest: boundedD)  
  apply simp
  apply (rule conjI)
   apply clarify
   apply (blast intro!: semilat_ub1 semilat_ub2 listE_nth_in
                intro: order_trans dest: boundedD)
  apply (blast intro!: semilat_ub1 semilat_ub2 listE_nth_in
               intro: order_trans dest: boundedD)
  done

lemma merges_bounded_lemma [rule_format]:
  "[| semilat (A,r,f); mono r step n A; bounded succs n; 
     step p (ss!p) : A; ss : list n A; ts : list n A; p < n; 
     ss <=[r] ts; ! p. p < n --> stable r step succs ts p |] 
  ==> merges f (step p (ss!p)) (succs p) ss <=[r] ts"
  apply (unfold stable_def)
  apply (blast intro!: listE_set monoD listE_nth_in le_listD less_lengthI
               intro: merges_pres_le_ub order_trans
               dest: pres_typeD boundedD)
  done

(*
ML_setup {*
Unify.trace_bound := 80;
Unify.search_bound := 90;
*}
*)

lemma termination_lemma:  
  "[| semilat(A,r,f); ss : list n A; t:A; ! q:set qs. q < n; p:w |] ==> 
      ss <[r] merges f t qs ss | 
  merges f t qs ss = ss & {q. q:set qs & t +_f ss!q ~= ss!q} Un (w-{p}) < w"
  apply (unfold lesssub_def)
  apply (simp (no_asm_simp) add: merges_incr)
  apply (rule impI)
  apply (rule merges_same_conv [THEN iffD1, elim_format]) 
  apply assumption+
    defer
    apply (rule sym, assumption)
   apply (simp cong add: conj_cong add: le_iff_plus_unchanged [symmetric])
   apply (blast intro!: psubsetI elim: equalityE)
  apply simp
  done

lemma while_properties:
  "\<lbrakk> semilat(A,r,f); acc r ; pres_type step n A; mono r step n A;
     bounded succs n; \<forall>p\<in>w0. p < n; ss0 \<in> list n A;
     \<forall>p<n. p \<notin> w0 \<longrightarrow> stable r step succs ss0 p \<rbrakk> \<Longrightarrow>
   ss' = fst(while (%(ss,w). w \<noteq> {})
         (%(ss,w). let p = SOME p. p \<in> w
                   in propa f (succs p) (step p (ss!p)) ss (w-{p})) (ss0,w0))
   \<longrightarrow>
   ss' \<in> list n A \<and> stables r step succs ss' \<and> ss0 <=[r] ss' \<and>
   (\<forall>ts\<in>list n A. ss0 <=[r] ts \<and> stables r step succs ts \<longrightarrow> ss' <=[r] ts)"
apply (unfold stables_def)
apply (rule_tac P = "%(ss,w).
 ss \<in> list n A \<and> (\<forall>p<n. p \<notin> w \<longrightarrow> stable r step succs ss p) \<and> ss0 <=[r] ss \<and>
 (\<forall>ts\<in>list n A. ss0 <=[r] ts \<and> stables r step succs ts \<longrightarrow> ss <=[r] ts) \<and>
 (\<forall>p\<in>w. p < n)" and
 r = "{(ss',ss) . ss <[r] ss'} <*lex*> finite_psubset"
       in while_rule)

(* Invariant holds initially: *)
apply (simp add:stables_def)
(* Invariant is preserved: *)
apply(simp add: stables_def split_paired_all)
apply(rename_tac ss w)
apply(subgoal_tac "(SOME p. p \<in> w) \<in> w")
 prefer 2; apply (fast intro: someI)
apply(subgoal_tac "step (SOME p. p \<in> w) (ss ! (SOME p. p \<in> w)) \<in> A")
 prefer 2; apply (blast intro: pres_typeD listE_nth_in dest: boundedD);
  apply (subgoal_tac "\<forall>q\<in>set(succs (SOME p. p \<in> w)). q < size ss")
 prefer 2;  apply(clarsimp, blast dest!: boundedD)
apply (subst decomp_propa)
 apply blast
apply simp
apply (rule conjI)
 apply (blast intro: merges_preserves_type dest: boundedD);
apply (rule conjI)
 apply (blast intro!: stable_pres_lemma)
apply (rule conjI)
 apply (blast intro!: merges_incr intro: le_list_trans)
apply (rule conjI)
 apply clarsimp
 apply (best intro!: merges_bounded_lemma)
apply (blast dest!: boundedD)

(* Postcondition holds upon termination: *)
apply(clarsimp simp add: stables_def split_paired_all)

(* Well-foundedness of the termination relation: *)
apply (rule wf_lex_prod)
 apply (drule (1) semilatDorderI [THEN acc_le_listI])
 apply (simp only: acc_def lesssub_def)
apply (rule wf_finite_psubset)

(* Loop decreases along termination relation: *)
apply(simp add: stables_def split_paired_all)
apply(rename_tac ss w)
apply(subgoal_tac "(SOME p. p \<in> w) \<in> w")
 prefer 2; apply (fast intro: someI)
apply(subgoal_tac "step (SOME p. p \<in> w) (ss ! (SOME p. p \<in> w)) \<in> A")
 prefer 2; apply (blast intro: pres_typeD listE_nth_in dest: boundedD);
  apply (subgoal_tac "\<forall>q\<in>set(succs (SOME p. p \<in> w)). q < n")
 prefer 2;  apply(clarsimp, blast dest!: boundedD)
apply (subst decomp_propa)
 apply clarsimp
apply clarify
apply (simp del: listE_length
    add: lex_prod_def finite_psubset_def decomp_propa termination_lemma
         bounded_nat_set_is_finite)
done

lemma iter_properties:
  "\<lbrakk> semilat(A,r,f); acc r ; pres_type step n A; mono r step n A;
     bounded succs n; \<forall>p\<in>w0. p < n; ss0 \<in> list n A;
     \<forall>p<n. p \<notin> w0 \<longrightarrow> stable r step succs ss0 p \<rbrakk> \<Longrightarrow>
  iter (A,r,f) step succs ss0 w0 : list n A \<and>
  stables r step succs (iter (A,r,f) step succs ss0 w0) \<and>
  ss0 <=[r] iter (A,r,f) step succs ss0 w0 \<and>
  (\<forall>ts\<in>list n A. ss0 <=[r] ts \<and> stables r step succs ts \<longrightarrow>
                 iter (A,r,f) step succs ss0 w0 <=[r] ts)"
apply(simp add:iter_def listE_set del:Let_def)
by(rule while_properties[THEN mp,OF _ _ _ _ _ _ _ _ refl])

lemma is_dfa_kildall:
  "[| semilat(A,r,f); acc r; pres_type step n A; 
     mono r step n A; bounded succs n|] 
  ==> is_dfa r (kildall (A,r,f) step succs) step succs n A"
  apply (unfold is_dfa_def kildall_def)
  apply clarify
  apply simp
  apply (rule iter_properties)
  apply (simp_all add: unstables_def stable_def)
  apply (blast intro!: le_iff_plus_unchanged [THEN iffD2] listE_nth_in
               dest: boundedD pres_typeD)
  done

lemma is_bcv_kildall:
  "[| semilat(A,r,f); acc r; top r T; 
      pres_type step n A; bounded succs n; 
      mono r step n A |]
  ==> is_bcv r T step succs n A (kildall (A,r,f) step succs)"
  apply (intro is_bcv_dfa is_dfa_kildall semilatDorderI)
  apply assumption+
  done

end
