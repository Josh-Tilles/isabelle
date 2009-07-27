theory Machines
imports Natural
begin

lemma converse_in_rel_pow_eq:
  "((x,z) \<in> R ^^ n) = (n=0 \<and> z=x \<or> (\<exists>m y. n = Suc m \<and> (x,y) \<in> R \<and> (y,z) \<in> R ^^ m))"
apply(rule iffI)
 apply(blast elim:rel_pow_E2)
apply (auto simp: rel_pow_commute[symmetric])
done

subsection "Instructions"

text {* There are only three instructions: *}
datatype instr = SET loc aexp | JMPF bexp nat | JMPB nat

types instrs = "instr list"

subsection "M0 with PC"

inductive_set
  exec01 :: "instr list \<Rightarrow> ((nat\<times>state) \<times> (nat\<times>state))set"
  and exec01' :: "[instrs, nat,state, nat,state] \<Rightarrow> bool"
    ("(_/ \<turnstile> (1\<langle>_,/_\<rangle>)/ -1\<rightarrow> (1\<langle>_,/_\<rangle>))" [50,0,0,0,0] 50)
  for P :: "instr list"
where
  "p \<turnstile> \<langle>i,s\<rangle> -1\<rightarrow> \<langle>j,t\<rangle> == ((i,s),j,t) : (exec01 p)"
| SET: "\<lbrakk> n<size P; P!n = SET x a \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>n,s\<rangle> -1\<rightarrow> \<langle>Suc n,s[x\<mapsto> a s]\<rangle>"
| JMPFT: "\<lbrakk> n<size P; P!n = JMPF b i;  b s \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>n,s\<rangle> -1\<rightarrow> \<langle>Suc n,s\<rangle>"
| JMPFF: "\<lbrakk> n<size P; P!n = JMPF b i; \<not>b s; m=n+i+1; m \<le> size P \<rbrakk>
        \<Longrightarrow> P \<turnstile> \<langle>n,s\<rangle> -1\<rightarrow> \<langle>m,s\<rangle>"
| JMPB:  "\<lbrakk> n<size P; P!n = JMPB i; i \<le> n; j = n-i \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>n,s\<rangle> -1\<rightarrow> \<langle>j,s\<rangle>"

abbreviation
  exec0s :: "[instrs, nat,state, nat,state] \<Rightarrow> bool"
    ("(_/ \<turnstile> (1\<langle>_,/_\<rangle>)/ -*\<rightarrow> (1\<langle>_,/_\<rangle>))" [50,0,0,0,0] 50)  where
  "p \<turnstile> \<langle>i,s\<rangle> -*\<rightarrow> \<langle>j,t\<rangle> == ((i,s),j,t) : (exec01 p)^*"

abbreviation
  exec0n :: "[instrs, nat,state, nat, nat,state] \<Rightarrow> bool"
    ("(_/ \<turnstile> (1\<langle>_,/_\<rangle>)/ -_\<rightarrow> (1\<langle>_,/_\<rangle>))" [50,0,0,0,0] 50)  where
  "p \<turnstile> \<langle>i,s\<rangle> -n\<rightarrow> \<langle>j,t\<rangle> == ((i,s),j,t) : (exec01 p)^^n"

subsection "M0 with lists"

text {* We describe execution of programs in the machine by
  an operational (small step) semantics:
*}

types config = "instrs \<times> instrs \<times> state"


inductive_set
  stepa1 :: "(config \<times> config)set"
  and stepa1' :: "[instrs,instrs,state, instrs,instrs,state] \<Rightarrow> bool"
    ("((1\<langle>_,/_,/_\<rangle>)/ -1\<rightarrow> (1\<langle>_,/_,/_\<rangle>))" 50)
where
  "\<langle>p,q,s\<rangle> -1\<rightarrow> \<langle>p',q',t\<rangle> == ((p,q,s),p',q',t) : stepa1"
| "\<langle>SET x a#p,q,s\<rangle> -1\<rightarrow> \<langle>p,SET x a#q,s[x\<mapsto> a s]\<rangle>"
| "b s \<Longrightarrow> \<langle>JMPF b i#p,q,s\<rangle> -1\<rightarrow> \<langle>p,JMPF b i#q,s\<rangle>"
| "\<lbrakk> \<not> b s; i \<le> size p \<rbrakk>
   \<Longrightarrow> \<langle>JMPF b i # p, q, s\<rangle> -1\<rightarrow> \<langle>drop i p, rev(take i p) @ JMPF b i # q, s\<rangle>"
| "i \<le> size q
   \<Longrightarrow> \<langle>JMPB i # p, q, s\<rangle> -1\<rightarrow> \<langle>rev(take i q) @ JMPB i # p, drop i q, s\<rangle>"

abbreviation
  stepa :: "[instrs,instrs,state, instrs,instrs,state] \<Rightarrow> bool"
    ("((1\<langle>_,/_,/_\<rangle>)/ -*\<rightarrow> (1\<langle>_,/_,/_\<rangle>))" 50)  where
  "\<langle>p,q,s\<rangle> -*\<rightarrow> \<langle>p',q',t\<rangle> == ((p,q,s),p',q',t) : (stepa1^*)"

abbreviation
  stepan :: "[instrs,instrs,state, nat, instrs,instrs,state] \<Rightarrow> bool"
    ("((1\<langle>_,/_,/_\<rangle>)/ -_\<rightarrow> (1\<langle>_,/_,/_\<rangle>))" 50) where
  "\<langle>p,q,s\<rangle> -i\<rightarrow> \<langle>p',q',t\<rangle> == ((p,q,s),p',q',t) : (stepa1^^i)"

inductive_cases execE: "((i#is,p,s), (is',p',s')) : stepa1"

lemma exec_simp[simp]:
 "(\<langle>i#p,q,s\<rangle> -1\<rightarrow> \<langle>p',q',t\<rangle>) = (case i of
 SET x a \<Rightarrow> t = s[x\<mapsto> a s] \<and> p' = p \<and> q' = i#q |
 JMPF b n \<Rightarrow> t=s \<and> (if b s then p' = p \<and> q' = i#q
            else n \<le> size p \<and> p' = drop n p \<and> q' = rev(take n p) @ i # q) |
 JMPB n \<Rightarrow> n \<le> size q \<and> t=s \<and> p' = rev(take n q) @ i # p \<and> q' = drop n q)"
apply(rule iffI)
defer
apply(clarsimp simp add: stepa1.intros split: instr.split_asm split_if_asm)
apply(erule execE)
apply(simp_all)
done

lemma execn_simp[simp]:
"(\<langle>i#p,q,s\<rangle> -n\<rightarrow> \<langle>p'',q'',u\<rangle>) =
 (n=0 \<and> p'' = i#p \<and> q'' = q \<and> u = s \<or>
  ((\<exists>m p' q' t. n = Suc m \<and>
                \<langle>i#p,q,s\<rangle> -1\<rightarrow> \<langle>p',q',t\<rangle> \<and> \<langle>p',q',t\<rangle> -m\<rightarrow> \<langle>p'',q'',u\<rangle>)))"
by(subst converse_in_rel_pow_eq, simp)


lemma exec_star_simp[simp]: "(\<langle>i#p,q,s\<rangle> -*\<rightarrow> \<langle>p'',q'',u\<rangle>) =
 (p'' = i#p & q''=q & u=s |
 (\<exists>p' q' t. \<langle>i#p,q,s\<rangle> -1\<rightarrow> \<langle>p',q',t\<rangle> \<and> \<langle>p',q',t\<rangle> -*\<rightarrow> \<langle>p'',q'',u\<rangle>))"
apply(simp add: rtrancl_is_UN_rel_pow del:exec_simp)
apply(blast)
done

declare nth_append[simp]

lemma rev_revD: "rev xs = rev ys \<Longrightarrow> xs = ys"
by simp

lemma [simp]: "(rev xs @ rev ys = rev zs) = (ys @ xs = zs)"
apply(rule iffI)
 apply(rule rev_revD, simp)
apply fastsimp
done

lemma direction1:
 "\<langle>q,p,s\<rangle> -1\<rightarrow> \<langle>q',p',t\<rangle> \<Longrightarrow>
  rev p' @ q' = rev p @ q \<and> rev p @ q \<turnstile> \<langle>size p,s\<rangle> -1\<rightarrow> \<langle>size p',t\<rangle>"
apply(induct set: stepa1)
   apply(simp add:exec01.SET)
  apply(fastsimp intro:exec01.JMPFT)
 apply simp
 apply(rule exec01.JMPFF)
     apply simp
    apply fastsimp
   apply simp
  apply simp
 apply simp
apply(fastsimp simp add:exec01.JMPB)
done

(*
lemma rev_take: "\<And>i. rev (take i xs) = drop (length xs - i) (rev xs)"
apply(induct xs)
 apply simp_all
apply(case_tac i)
apply simp_all
done

lemma rev_drop: "\<And>i. rev (drop i xs) = take (length xs - i) (rev xs)"
apply(induct xs)
 apply simp_all
apply(case_tac i)
apply simp_all
done
*)

lemma direction2:
 "rpq \<turnstile> \<langle>sp,s\<rangle> -1\<rightarrow> \<langle>sp',t\<rangle> \<Longrightarrow>
  rpq = rev p @ q & sp = size p & sp' = size p' \<longrightarrow>
          rev p' @ q' = rev p @ q \<longrightarrow> \<langle>q,p,s\<rangle> -1\<rightarrow> \<langle>q',p',t\<rangle>"
apply(induct arbitrary: p q p' q' set: exec01)
   apply(clarsimp simp add: neq_Nil_conv append_eq_conv_conj)
   apply(drule sym)
   apply simp
   apply(rule rev_revD)
   apply simp
  apply(clarsimp simp add: neq_Nil_conv append_eq_conv_conj)
  apply(drule sym)
  apply simp
  apply(rule rev_revD)
  apply simp
 apply(simp (no_asm_use) add: neq_Nil_conv append_eq_conv_conj, clarify)+
 apply(drule sym)
 apply simp
 apply(rule rev_revD)
 apply simp
apply(clarsimp simp add: neq_Nil_conv append_eq_conv_conj)
apply(drule sym)
apply(simp add:rev_take)
apply(rule rev_revD)
apply(simp add:rev_drop)
done


theorem M_eqiv:
"(\<langle>q,p,s\<rangle> -1\<rightarrow> \<langle>q',p',t\<rangle>) =
 (rev p' @ q' = rev p @ q \<and> rev p @ q \<turnstile> \<langle>size p,s\<rangle> -1\<rightarrow> \<langle>size p',t\<rangle>)"
  by (blast dest: direction1 direction2)

end
