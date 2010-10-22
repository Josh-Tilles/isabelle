(*  Title:      HOLCF/Discrete.thy
    Author:     Tobias Nipkow
*)

header {* Discrete cpo types *}

theory Discrete
imports Cont
begin

datatype 'a discr = Discr "'a :: type"

subsection {* Discrete ordering *}

instantiation discr :: (type) below
begin

definition
  below_discr_def:
    "(op \<sqsubseteq> :: 'a discr \<Rightarrow> 'a discr \<Rightarrow> bool) = (op =)"

instance ..
end

subsection {* Discrete cpo class instance *}

instance discr :: (type) discrete_cpo
by intro_classes (simp add: below_discr_def)

lemma discr_below_eq [iff]: "((x::('a::type)discr) << y) = (x = y)"
by simp (* FIXME: same discrete_cpo - remove? is [iff] important? *)

lemma discr_chain0: 
 "!!S::nat=>('a::type)discr. chain S ==> S i = S 0"
apply (unfold chain_def)
apply (induct_tac "i")
apply (rule refl)
apply (erule subst)
apply (rule sym)
apply fast
done

lemma discr_chain_range0 [simp]: 
 "!!S::nat=>('a::type)discr. chain(S) ==> range(S) = {S 0}"
by (fast elim: discr_chain0)

instance discr :: (type) chfin
apply intro_classes
apply (rule_tac x=0 in exI)
apply (unfold max_in_chain_def)
apply (clarify, erule discr_chain0 [symmetric])
done

subsection {* \emph{undiscr} *}

definition
  undiscr :: "('a::type)discr => 'a" where
  "undiscr x = (case x of Discr y => y)"

lemma undiscr_Discr [simp]: "undiscr (Discr x) = x"
by (simp add: undiscr_def)

lemma Discr_undiscr [simp]: "Discr (undiscr y) = y"
by (induct y) simp

lemma discr_chain_f_range0:
 "!!S::nat=>('a::type)discr. chain(S) ==> range(%i. f(S i)) = {f(S 0)}"
by (fast dest: discr_chain0 elim: arg_cong)

lemma cont_discr [iff]: "cont (%x::('a::type)discr. f x)"
by (rule cont_discrete_cpo)

end
