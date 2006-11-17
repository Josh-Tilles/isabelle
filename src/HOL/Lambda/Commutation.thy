(*  Title:      HOL/Lambda/Commutation.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995  TU Muenchen
*)

header {* Abstract commutation and confluence notions *}

theory Commutation imports Main begin

subsection {* Basic definitions *}

definition
  square :: "[('a \<times> 'a) set, ('a \<times> 'a) set, ('a \<times> 'a) set, ('a \<times> 'a) set] => bool" where
  "square R S T U =
    (\<forall>x y. (x, y) \<in> R --> (\<forall>z. (x, z) \<in> S --> (\<exists>u. (y, u) \<in> T \<and> (z, u) \<in> U)))"

definition
  commute :: "[('a \<times> 'a) set, ('a \<times> 'a) set] => bool" where
  "commute R S = square R S S R"

definition
  diamond :: "('a \<times> 'a) set => bool" where
  "diamond R = commute R R"

definition
  Church_Rosser :: "('a \<times> 'a) set => bool" where
  "Church_Rosser R =
    (\<forall>x y. (x, y) \<in> (R \<union> R^-1)^* --> (\<exists>z. (x, z) \<in> R^* \<and> (y, z) \<in> R^*))"

abbreviation
  confluent :: "('a \<times> 'a) set => bool" where
  "confluent R == diamond (R^*)"


subsection {* Basic lemmas *}

subsubsection {* square *}

lemma square_sym: "square R S T U ==> square S R U T"
  apply (unfold square_def)
  apply blast
  done

lemma square_subset:
    "[| square R S T U; T \<subseteq> T' |] ==> square R S T' U"
  apply (unfold square_def)
  apply blast
  done

lemma square_reflcl:
    "[| square R S T (R^=); S \<subseteq> T |] ==> square (R^=) S T (R^=)"
  apply (unfold square_def)
  apply blast
  done

lemma square_rtrancl:
    "square R S S T ==> square (R^*) S S (T^*)"
  apply (unfold square_def)
  apply (intro strip)
  apply (erule rtrancl_induct)
   apply blast
  apply (blast intro: rtrancl_into_rtrancl)
  done

lemma square_rtrancl_reflcl_commute:
    "square R S (S^*) (R^=) ==> commute (R^*) (S^*)"
  apply (unfold commute_def)
  apply (fastsimp dest: square_reflcl square_sym [THEN square_rtrancl]
    elim: r_into_rtrancl)
  done


subsubsection {* commute *}

lemma commute_sym: "commute R S ==> commute S R"
  apply (unfold commute_def)
  apply (blast intro: square_sym)
  done

lemma commute_rtrancl: "commute R S ==> commute (R^*) (S^*)"
  apply (unfold commute_def)
  apply (blast intro: square_rtrancl square_sym)
  done

lemma commute_Un:
    "[| commute R T; commute S T |] ==> commute (R \<union> S) T"
  apply (unfold commute_def square_def)
  apply blast
  done


subsubsection {* diamond, confluence, and union *}

lemma diamond_Un:
    "[| diamond R; diamond S; commute R S |] ==> diamond (R \<union> S)"
  apply (unfold diamond_def)
  apply (assumption | rule commute_Un commute_sym)+
  done

lemma diamond_confluent: "diamond R ==> confluent R"
  apply (unfold diamond_def)
  apply (erule commute_rtrancl)
  done

lemma square_reflcl_confluent:
    "square R R (R^=) (R^=) ==> confluent R"
  apply (unfold diamond_def)
  apply (fast intro: square_rtrancl_reflcl_commute r_into_rtrancl
    elim: square_subset)
  done

lemma confluent_Un:
    "[| confluent R; confluent S; commute (R^*) (S^*) |] ==> confluent (R \<union> S)"
  apply (rule rtrancl_Un_rtrancl [THEN subst])
  apply (blast dest: diamond_Un intro: diamond_confluent)
  done

lemma diamond_to_confluence:
    "[| diamond R; T \<subseteq> R; R \<subseteq> T^* |] ==> confluent T"
  apply (force intro: diamond_confluent
    dest: rtrancl_subset [symmetric])
  done


subsection {* Church-Rosser *}

lemma Church_Rosser_confluent: "Church_Rosser R = confluent R"
  apply (unfold square_def commute_def diamond_def Church_Rosser_def)
  apply (tactic {* safe_tac HOL_cs *})
   apply (tactic {*
     blast_tac (HOL_cs addIs
       [Un_upper2 RS rtrancl_mono RS subsetD RS rtrancl_trans,
       rtrancl_converseI, converseI, Un_upper1 RS rtrancl_mono RS subsetD]) 1 *})
  apply (erule rtrancl_induct)
   apply blast
  apply (blast del: rtrancl_refl intro: rtrancl_trans)
  done


subsection {* Newman's lemma *}

text {* Proof by Stefan Berghofer *}

theorem newman:
  assumes wf: "wf (R\<inverse>)"
  and lc: "\<And>a b c. (a, b) \<in> R \<Longrightarrow> (a, c) \<in> R \<Longrightarrow>
    \<exists>d. (b, d) \<in> R\<^sup>* \<and> (c, d) \<in> R\<^sup>*"
  shows "\<And>b c. (a, b) \<in> R\<^sup>* \<Longrightarrow> (a, c) \<in> R\<^sup>* \<Longrightarrow>
    \<exists>d. (b, d) \<in> R\<^sup>* \<and> (c, d) \<in> R\<^sup>*"
  using wf
proof induct
  case (less x b c)
  have xc: "(x, c) \<in> R\<^sup>*" .
  have xb: "(x, b) \<in> R\<^sup>*" . thus ?case
  proof (rule converse_rtranclE)
    assume "x = b"
    with xc have "(b, c) \<in> R\<^sup>*" by simp
    thus ?thesis by iprover
  next
    fix y
    assume xy: "(x, y) \<in> R"
    assume yb: "(y, b) \<in> R\<^sup>*"
    from xc show ?thesis
    proof (rule converse_rtranclE)
      assume "x = c"
      with xb have "(c, b) \<in> R\<^sup>*" by simp
      thus ?thesis by iprover
    next
      fix y'
      assume y'c: "(y', c) \<in> R\<^sup>*"
      assume xy': "(x, y') \<in> R"
      with xy have "\<exists>u. (y, u) \<in> R\<^sup>* \<and> (y', u) \<in> R\<^sup>*" by (rule lc)
      then obtain u where yu: "(y, u) \<in> R\<^sup>*" and y'u: "(y', u) \<in> R\<^sup>*" by iprover
      from xy have "(y, x) \<in> R\<inverse>" ..
      from this and yb yu have "\<exists>d. (b, d) \<in> R\<^sup>* \<and> (u, d) \<in> R\<^sup>*" by (rule less)
      then obtain v where bv: "(b, v) \<in> R\<^sup>*" and uv: "(u, v) \<in> R\<^sup>*" by iprover
      from xy' have "(y', x) \<in> R\<inverse>" ..
      moreover from y'u and uv have "(y', v) \<in> R\<^sup>*" by (rule rtrancl_trans)
      moreover note y'c
      ultimately have "\<exists>d. (v, d) \<in> R\<^sup>* \<and> (c, d) \<in> R\<^sup>*" by (rule less)
      then obtain w where vw: "(v, w) \<in> R\<^sup>*" and cw: "(c, w) \<in> R\<^sup>*" by iprover
      from bv vw have "(b, w) \<in> R\<^sup>*" by (rule rtrancl_trans)
      with cw show ?thesis by iprover
    qed
  qed
qed

text {*
  \medskip Alternative version.  Partly automated by Tobias
  Nipkow. Takes 2 minutes (2002).

  This is the maximal amount of automation possible at the moment.
*}

theorem newman':
  assumes wf: "wf (R\<inverse>)"
  and lc: "\<And>a b c. (a, b) \<in> R \<Longrightarrow> (a, c) \<in> R \<Longrightarrow>
    \<exists>d. (b, d) \<in> R\<^sup>* \<and> (c, d) \<in> R\<^sup>*"
  shows "\<And>b c. (a, b) \<in> R\<^sup>* \<Longrightarrow> (a, c) \<in> R\<^sup>* \<Longrightarrow>
    \<exists>d. (b, d) \<in> R\<^sup>* \<and> (c, d) \<in> R\<^sup>*"
  using wf
proof induct
  case (less x b c)
  note IH = `\<And>y b c. \<lbrakk>(y,x) \<in> R\<inverse>; (y,b) \<in> R\<^sup>*; (y,c) \<in> R\<^sup>*\<rbrakk>
                     \<Longrightarrow> \<exists>d. (b,d) \<in> R\<^sup>* \<and> (c,d) \<in> R\<^sup>*`
  have xc: "(x, c) \<in> R\<^sup>*" .
  have xb: "(x, b) \<in> R\<^sup>*" .
  thus ?case
  proof (rule converse_rtranclE)
    assume "x = b"
    with xc have "(b, c) \<in> R\<^sup>*" by simp
    thus ?thesis by iprover
  next
    fix y
    assume xy: "(x, y) \<in> R"
    assume yb: "(y, b) \<in> R\<^sup>*"
    from xc show ?thesis
    proof (rule converse_rtranclE)
      assume "x = c"
      with xb have "(c, b) \<in> R\<^sup>*" by simp
      thus ?thesis by iprover
    next
      fix y'
      assume y'c: "(y', c) \<in> R\<^sup>*"
      assume xy': "(x, y') \<in> R"
      with xy obtain u where u: "(y, u) \<in> R\<^sup>*" "(y', u) \<in> R\<^sup>*"
        by (blast dest: lc)
      from yb u y'c show ?thesis
        by (blast del: rtrancl_refl
            intro: rtrancl_trans
            dest: IH [OF xy [symmetric]] IH [OF xy' [symmetric]])
    qed
  qed
qed

end
