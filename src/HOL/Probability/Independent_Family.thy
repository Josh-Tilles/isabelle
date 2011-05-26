(*  Title:      HOL/Probability/Independent_Family.thy
    Author:     Johannes Hölzl, TU München
*)

header {* Independent families of events, event sets, and random variables *}

theory Independent_Family
  imports Probability_Measure
begin

definition (in prob_space)
  "indep_events A I \<longleftrightarrow> (A`I \<subseteq> events) \<and>
    (\<forall>J\<subseteq>I. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow> prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j)))"

definition (in prob_space)
  "indep_event A B \<longleftrightarrow> indep_events (bool_case A B) UNIV"

definition (in prob_space)
  "indep_sets F I \<longleftrightarrow> (\<forall>i\<in>I. F i \<subseteq> events) \<and>
    (\<forall>J\<subseteq>I. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow> (\<forall>A\<in>Pi J F. prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))))"

definition (in prob_space)
  "indep_set A B \<longleftrightarrow> indep_sets (bool_case A B) UNIV"

definition (in prob_space)
  "indep_rv M' X I \<longleftrightarrow>
    (\<forall>i\<in>I. random_variable (M' i) (X i)) \<and>
    indep_sets (\<lambda>i. sigma_sets (space M) { X i -` A \<inter> space M | A. A \<in> sets (M' i)}) I"

lemma (in prob_space) indep_sets_cong:
  "I = J \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> F i = G i) \<Longrightarrow> indep_sets F I \<longleftrightarrow> indep_sets G J"
  by (simp add: indep_sets_def, intro conj_cong all_cong imp_cong ball_cong) blast+

lemma (in prob_space) indep_events_finite_index_events:
  "indep_events F I \<longleftrightarrow> (\<forall>J\<subseteq>I. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow> indep_events F J)"
  by (auto simp: indep_events_def)

lemma (in prob_space) indep_sets_finite_index_sets:
  "indep_sets F I \<longleftrightarrow> (\<forall>J\<subseteq>I. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow> indep_sets F J)"
proof (intro iffI allI impI)
  assume *: "\<forall>J\<subseteq>I. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow> indep_sets F J"
  show "indep_sets F I" unfolding indep_sets_def
  proof (intro conjI ballI allI impI)
    fix i assume "i \<in> I"
    with *[THEN spec, of "{i}"] show "F i \<subseteq> events"
      by (auto simp: indep_sets_def)
  qed (insert *, auto simp: indep_sets_def)
qed (auto simp: indep_sets_def)

lemma (in prob_space) indep_sets_mono_index:
  "J \<subseteq> I \<Longrightarrow> indep_sets F I \<Longrightarrow> indep_sets F J"
  unfolding indep_sets_def by auto

lemma (in prob_space) indep_sets_mono_sets:
  assumes indep: "indep_sets F I"
  assumes mono: "\<And>i. i\<in>I \<Longrightarrow> G i \<subseteq> F i"
  shows "indep_sets G I"
proof -
  have "(\<forall>i\<in>I. F i \<subseteq> events) \<Longrightarrow> (\<forall>i\<in>I. G i \<subseteq> events)"
    using mono by auto
  moreover have "\<And>A J. J \<subseteq> I \<Longrightarrow> A \<in> (\<Pi> j\<in>J. G j) \<Longrightarrow> A \<in> (\<Pi> j\<in>J. F j)"
    using mono by (auto simp: Pi_iff)
  ultimately show ?thesis
    using indep by (auto simp: indep_sets_def)
qed

lemma (in prob_space) indep_setsI:
  assumes "\<And>i. i \<in> I \<Longrightarrow> F i \<subseteq> events"
    and "\<And>A J. J \<noteq> {} \<Longrightarrow> J \<subseteq> I \<Longrightarrow> finite J \<Longrightarrow> (\<forall>j\<in>J. A j \<in> F j) \<Longrightarrow> prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))"
  shows "indep_sets F I"
  using assms unfolding indep_sets_def by (auto simp: Pi_iff)

lemma (in prob_space) indep_setsD:
  assumes "indep_sets F I" and "J \<subseteq> I" "J \<noteq> {}" "finite J" "\<forall>j\<in>J. A j \<in> F j"
  shows "prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))"
  using assms unfolding indep_sets_def by auto

lemma (in prob_space) indep_setI:
  assumes ev: "A \<subseteq> events" "B \<subseteq> events"
    and indep: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> prob (a \<inter> b) = prob a * prob b"
  shows "indep_set A B"
  unfolding indep_set_def
proof (rule indep_setsI)
  fix F J assume "J \<noteq> {}" "J \<subseteq> UNIV"
    and F: "\<forall>j\<in>J. F j \<in> (case j of True \<Rightarrow> A | False \<Rightarrow> B)"
  have "J \<in> Pow UNIV" by auto
  with F `J \<noteq> {}` indep[of "F True" "F False"]
  show "prob (\<Inter>j\<in>J. F j) = (\<Prod>j\<in>J. prob (F j))"
    unfolding UNIV_bool Pow_insert by (auto simp: ac_simps)
qed (auto split: bool.split simp: ev)

lemma (in prob_space) indep_setD:
  assumes indep: "indep_set A B" and ev: "a \<in> A" "b \<in> B"
  shows "prob (a \<inter> b) = prob a * prob b"
  using indep[unfolded indep_set_def, THEN indep_setsD, of UNIV "bool_case a b"] ev
  by (simp add: ac_simps UNIV_bool)

lemma (in prob_space)
  assumes indep: "indep_set A B"
  shows indep_setD_ev1: "A \<subseteq> events"
    and indep_setD_ev2: "B \<subseteq> events"
  using indep unfolding indep_set_def indep_sets_def UNIV_bool by auto

lemma dynkin_systemI':
  assumes 1: "\<And> A. A \<in> sets M \<Longrightarrow> A \<subseteq> space M"
  assumes empty: "{} \<in> sets M"
  assumes Diff: "\<And> A. A \<in> sets M \<Longrightarrow> space M - A \<in> sets M"
  assumes 2: "\<And> A. disjoint_family A \<Longrightarrow> range A \<subseteq> sets M
          \<Longrightarrow> (\<Union>i::nat. A i) \<in> sets M"
  shows "dynkin_system M"
proof -
  from Diff[OF empty] have "space M \<in> sets M" by auto
  from 1 this Diff 2 show ?thesis
    by (intro dynkin_systemI) auto
qed

lemma (in prob_space) indep_sets_dynkin:
  assumes indep: "indep_sets F I"
  shows "indep_sets (\<lambda>i. sets (dynkin \<lparr> space = space M, sets = F i \<rparr>)) I"
    (is "indep_sets ?F I")
proof (subst indep_sets_finite_index_sets, intro allI impI ballI)
  fix J assume "finite J" "J \<subseteq> I" "J \<noteq> {}"
  with indep have "indep_sets F J"
    by (subst (asm) indep_sets_finite_index_sets) auto
  { fix J K assume "indep_sets F K"
    let "?G S i" = "if i \<in> S then ?F i else F i"
    assume "finite J" "J \<subseteq> K"
    then have "indep_sets (?G J) K"
    proof induct
      case (insert j J)
      moreover def G \<equiv> "?G J"
      ultimately have G: "indep_sets G K" "\<And>i. i \<in> K \<Longrightarrow> G i \<subseteq> events" and "j \<in> K"
        by (auto simp: indep_sets_def)
      let ?D = "{E\<in>events. indep_sets (G(j := {E})) K }"
      { fix X assume X: "X \<in> events"
        assume indep: "\<And>J A. J \<noteq> {} \<Longrightarrow> J \<subseteq> K \<Longrightarrow> finite J \<Longrightarrow> j \<notin> J \<Longrightarrow> (\<forall>i\<in>J. A i \<in> G i)
          \<Longrightarrow> prob ((\<Inter>i\<in>J. A i) \<inter> X) = prob X * (\<Prod>i\<in>J. prob (A i))"
        have "indep_sets (G(j := {X})) K"
        proof (rule indep_setsI)
          fix i assume "i \<in> K" then show "(G(j:={X})) i \<subseteq> events"
            using G X by auto
        next
          fix A J assume J: "J \<noteq> {}" "J \<subseteq> K" "finite J" "\<forall>i\<in>J. A i \<in> (G(j := {X})) i"
          show "prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))"
          proof cases
            assume "j \<in> J"
            with J have "A j = X" by auto
            show ?thesis
            proof cases
              assume "J = {j}" then show ?thesis by simp
            next
              assume "J \<noteq> {j}"
              have "prob (\<Inter>i\<in>J. A i) = prob ((\<Inter>i\<in>J-{j}. A i) \<inter> X)"
                using `j \<in> J` `A j = X` by (auto intro!: arg_cong[where f=prob] split: split_if_asm)
              also have "\<dots> = prob X * (\<Prod>i\<in>J-{j}. prob (A i))"
              proof (rule indep)
                show "J - {j} \<noteq> {}" "J - {j} \<subseteq> K" "finite (J - {j})" "j \<notin> J - {j}"
                  using J `J \<noteq> {j}` `j \<in> J` by auto
                show "\<forall>i\<in>J - {j}. A i \<in> G i"
                  using J by auto
              qed
              also have "\<dots> = prob (A j) * (\<Prod>i\<in>J-{j}. prob (A i))"
                using `A j = X` by simp
              also have "\<dots> = (\<Prod>i\<in>J. prob (A i))"
                unfolding setprod.insert_remove[OF `finite J`, symmetric, of "\<lambda>i. prob  (A i)"]
                using `j \<in> J` by (simp add: insert_absorb)
              finally show ?thesis .
            qed
          next
            assume "j \<notin> J"
            with J have "\<forall>i\<in>J. A i \<in> G i" by (auto split: split_if_asm)
            with J show ?thesis
              by (intro indep_setsD[OF G(1)]) auto
          qed
        qed }
      note indep_sets_insert = this
      have "dynkin_system \<lparr> space = space M, sets = ?D \<rparr>"
      proof (rule dynkin_systemI', simp_all, safe)
        show "indep_sets (G(j := {{}})) K"
          by (rule indep_sets_insert) auto
      next
        fix X assume X: "X \<in> events" and G': "indep_sets (G(j := {X})) K"
        show "indep_sets (G(j := {space M - X})) K"
        proof (rule indep_sets_insert)
          fix J A assume J: "J \<noteq> {}" "J \<subseteq> K" "finite J" "j \<notin> J" and A: "\<forall>i\<in>J. A i \<in> G i"
          then have A_sets: "\<And>i. i\<in>J \<Longrightarrow> A i \<in> events"
            using G by auto
          have "prob ((\<Inter>j\<in>J. A j) \<inter> (space M - X)) =
              prob ((\<Inter>j\<in>J. A j) - (\<Inter>i\<in>insert j J. (A(j := X)) i))"
            using A_sets sets_into_space X `J \<noteq> {}`
            by (auto intro!: arg_cong[where f=prob] split: split_if_asm)
          also have "\<dots> = prob (\<Inter>j\<in>J. A j) - prob (\<Inter>i\<in>insert j J. (A(j := X)) i)"
            using J `J \<noteq> {}` `j \<notin> J` A_sets X sets_into_space
            by (auto intro!: finite_measure_Diff finite_INT split: split_if_asm)
          finally have "prob ((\<Inter>j\<in>J. A j) \<inter> (space M - X)) =
              prob (\<Inter>j\<in>J. A j) - prob (\<Inter>i\<in>insert j J. (A(j := X)) i)" .
          moreover {
            have "prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))"
              using J A `finite J` by (intro indep_setsD[OF G(1)]) auto
            then have "prob (\<Inter>j\<in>J. A j) = prob (space M) * (\<Prod>i\<in>J. prob (A i))"
              using prob_space by simp }
          moreover {
            have "prob (\<Inter>i\<in>insert j J. (A(j := X)) i) = (\<Prod>i\<in>insert j J. prob ((A(j := X)) i))"
              using J A `j \<in> K` by (intro indep_setsD[OF G']) auto
            then have "prob (\<Inter>i\<in>insert j J. (A(j := X)) i) = prob X * (\<Prod>i\<in>J. prob (A i))"
              using `finite J` `j \<notin> J` by (auto intro!: setprod_cong) }
          ultimately have "prob ((\<Inter>j\<in>J. A j) \<inter> (space M - X)) = (prob (space M) - prob X) * (\<Prod>i\<in>J. prob (A i))"
            by (simp add: field_simps)
          also have "\<dots> = prob (space M - X) * (\<Prod>i\<in>J. prob (A i))"
            using X A by (simp add: finite_measure_compl)
          finally show "prob ((\<Inter>j\<in>J. A j) \<inter> (space M - X)) = prob (space M - X) * (\<Prod>i\<in>J. prob (A i))" .
        qed (insert X, auto)
      next
        fix F :: "nat \<Rightarrow> 'a set" assume disj: "disjoint_family F" and "range F \<subseteq> ?D"
        then have F: "\<And>i. F i \<in> events" "\<And>i. indep_sets (G(j:={F i})) K" by auto
        show "indep_sets (G(j := {\<Union>k. F k})) K"
        proof (rule indep_sets_insert)
          fix J A assume J: "j \<notin> J" "J \<noteq> {}" "J \<subseteq> K" "finite J" and A: "\<forall>i\<in>J. A i \<in> G i"
          then have A_sets: "\<And>i. i\<in>J \<Longrightarrow> A i \<in> events"
            using G by auto
          have "prob ((\<Inter>j\<in>J. A j) \<inter> (\<Union>k. F k)) = prob (\<Union>k. (\<Inter>i\<in>insert j J. (A(j := F k)) i))"
            using `J \<noteq> {}` `j \<notin> J` `j \<in> K` by (auto intro!: arg_cong[where f=prob] split: split_if_asm)
          moreover have "(\<lambda>k. prob (\<Inter>i\<in>insert j J. (A(j := F k)) i)) sums prob (\<Union>k. (\<Inter>i\<in>insert j J. (A(j := F k)) i))"
          proof (rule finite_measure_UNION)
            show "disjoint_family (\<lambda>k. \<Inter>i\<in>insert j J. (A(j := F k)) i)"
              using disj by (rule disjoint_family_on_bisimulation) auto
            show "range (\<lambda>k. \<Inter>i\<in>insert j J. (A(j := F k)) i) \<subseteq> events"
              using A_sets F `finite J` `J \<noteq> {}` `j \<notin> J` by (auto intro!: Int)
          qed
          moreover { fix k
            from J A `j \<in> K` have "prob (\<Inter>i\<in>insert j J. (A(j := F k)) i) = prob (F k) * (\<Prod>i\<in>J. prob (A i))"
              by (subst indep_setsD[OF F(2)]) (auto intro!: setprod_cong split: split_if_asm)
            also have "\<dots> = prob (F k) * prob (\<Inter>i\<in>J. A i)"
              using J A `j \<in> K` by (subst indep_setsD[OF G(1)]) auto
            finally have "prob (\<Inter>i\<in>insert j J. (A(j := F k)) i) = prob (F k) * prob (\<Inter>i\<in>J. A i)" . }
          ultimately have "(\<lambda>k. prob (F k) * prob (\<Inter>i\<in>J. A i)) sums (prob ((\<Inter>j\<in>J. A j) \<inter> (\<Union>k. F k)))"
            by simp
          moreover
          have "(\<lambda>k. prob (F k) * prob (\<Inter>i\<in>J. A i)) sums (prob (\<Union>k. F k) * prob (\<Inter>i\<in>J. A i))"
            using disj F(1) by (intro finite_measure_UNION sums_mult2) auto
          then have "(\<lambda>k. prob (F k) * prob (\<Inter>i\<in>J. A i)) sums (prob (\<Union>k. F k) * (\<Prod>i\<in>J. prob (A i)))"
            using J A `j \<in> K` by (subst indep_setsD[OF G(1), symmetric]) auto
          ultimately
          show "prob ((\<Inter>j\<in>J. A j) \<inter> (\<Union>k. F k)) = prob (\<Union>k. F k) * (\<Prod>j\<in>J. prob (A j))"
            by (auto dest!: sums_unique)
        qed (insert F, auto)
      qed (insert sets_into_space, auto)
      then have mono: "sets (dynkin \<lparr>space = space M, sets = G j\<rparr>) \<subseteq>
        sets \<lparr>space = space M, sets = {E \<in> events. indep_sets (G(j := {E})) K}\<rparr>"
      proof (rule dynkin_system.dynkin_subset, simp_all, safe)
        fix X assume "X \<in> G j"
        then show "X \<in> events" using G `j \<in> K` by auto
        from `indep_sets G K`
        show "indep_sets (G(j := {X})) K"
          by (rule indep_sets_mono_sets) (insert `X \<in> G j`, auto)
      qed
      have "indep_sets (G(j:=?D)) K"
      proof (rule indep_setsI)
        fix i assume "i \<in> K" then show "(G(j := ?D)) i \<subseteq> events"
          using G(2) by auto
      next
        fix A J assume J: "J\<noteq>{}" "J \<subseteq> K" "finite J" and A: "\<forall>i\<in>J. A i \<in> (G(j := ?D)) i"
        show "prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))"
        proof cases
          assume "j \<in> J"
          with A have indep: "indep_sets (G(j := {A j})) K" by auto
          from J A show ?thesis
            by (intro indep_setsD[OF indep]) auto
        next
          assume "j \<notin> J"
          with J A have "\<forall>i\<in>J. A i \<in> G i" by (auto split: split_if_asm)
          with J show ?thesis
            by (intro indep_setsD[OF G(1)]) auto
        qed
      qed
      then have "indep_sets (G(j:=sets (dynkin \<lparr>space = space M, sets = G j\<rparr>))) K"
        by (rule indep_sets_mono_sets) (insert mono, auto)
      then show ?case
        by (rule indep_sets_mono_sets) (insert `j \<in> K` `j \<notin> J`, auto simp: G_def)
    qed (insert `indep_sets F K`, simp) }
  from this[OF `indep_sets F J` `finite J` subset_refl]
  show "indep_sets (\<lambda>i. sets (dynkin \<lparr> space = space M, sets = F i \<rparr>)) J"
    by (rule indep_sets_mono_sets) auto
qed

lemma (in prob_space) indep_sets_sigma:
  assumes indep: "indep_sets F I"
  assumes stable: "\<And>i. i \<in> I \<Longrightarrow> Int_stable \<lparr> space = space M, sets = F i \<rparr>"
  shows "indep_sets (\<lambda>i. sets (sigma \<lparr> space = space M, sets = F i \<rparr>)) I"
proof -
  from indep_sets_dynkin[OF indep]
  show ?thesis
  proof (rule indep_sets_mono_sets, subst sigma_eq_dynkin, simp_all add: stable)
    fix i assume "i \<in> I"
    with indep have "F i \<subseteq> events" by (auto simp: indep_sets_def)
    with sets_into_space show "F i \<subseteq> Pow (space M)" by auto
  qed
qed

lemma (in prob_space) indep_sets_sigma_sets:
  assumes "indep_sets F I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> Int_stable \<lparr> space = space M, sets = F i \<rparr>"
  shows "indep_sets (\<lambda>i. sigma_sets (space M) (F i)) I"
  using indep_sets_sigma[OF assms] by (simp add: sets_sigma)

lemma (in prob_space) indep_sets2_eq:
  "indep_set A B \<longleftrightarrow> A \<subseteq> events \<and> B \<subseteq> events \<and> (\<forall>a\<in>A. \<forall>b\<in>B. prob (a \<inter> b) = prob a * prob b)"
  unfolding indep_set_def
proof (intro iffI ballI conjI)
  assume indep: "indep_sets (bool_case A B) UNIV"
  { fix a b assume "a \<in> A" "b \<in> B"
    with indep_setsD[OF indep, of UNIV "bool_case a b"]
    show "prob (a \<inter> b) = prob a * prob b"
      unfolding UNIV_bool by (simp add: ac_simps) }
  from indep show "A \<subseteq> events" "B \<subseteq> events"
    unfolding indep_sets_def UNIV_bool by auto
next
  assume *: "A \<subseteq> events \<and> B \<subseteq> events \<and> (\<forall>a\<in>A. \<forall>b\<in>B. prob (a \<inter> b) = prob a * prob b)"
  show "indep_sets (bool_case A B) UNIV"
  proof (rule indep_setsI)
    fix i show "(case i of True \<Rightarrow> A | False \<Rightarrow> B) \<subseteq> events"
      using * by (auto split: bool.split)
  next
    fix J X assume "J \<noteq> {}" "J \<subseteq> UNIV" and X: "\<forall>j\<in>J. X j \<in> (case j of True \<Rightarrow> A | False \<Rightarrow> B)"
    then have "J = {True} \<or> J = {False} \<or> J = {True,False}"
      by (auto simp: UNIV_bool)
    then show "prob (\<Inter>j\<in>J. X j) = (\<Prod>j\<in>J. prob (X j))"
      using X * by auto
  qed
qed

lemma (in prob_space) indep_set_sigma_sets:
  assumes "indep_set A B"
  assumes A: "Int_stable \<lparr> space = space M, sets = A \<rparr>"
  assumes B: "Int_stable \<lparr> space = space M, sets = B \<rparr>"
  shows "indep_set (sigma_sets (space M) A) (sigma_sets (space M) B)"
proof -
  have "indep_sets (\<lambda>i. sigma_sets (space M) (case i of True \<Rightarrow> A | False \<Rightarrow> B)) UNIV"
  proof (rule indep_sets_sigma_sets)
    show "indep_sets (bool_case A B) UNIV"
      by (rule `indep_set A B`[unfolded indep_set_def])
    fix i show "Int_stable \<lparr>space = space M, sets = case i of True \<Rightarrow> A | False \<Rightarrow> B\<rparr>"
      using A B by (cases i) auto
  qed
  then show ?thesis
    unfolding indep_set_def
    by (rule indep_sets_mono_sets) (auto split: bool.split)
qed

lemma (in prob_space) indep_sets_collect_sigma:
  fixes I :: "'j \<Rightarrow> 'i set" and J :: "'j set" and E :: "'i \<Rightarrow> 'a set set"
  assumes indep: "indep_sets E (\<Union>j\<in>J. I j)"
  assumes Int_stable: "\<And>i j. j \<in> J \<Longrightarrow> i \<in> I j \<Longrightarrow> Int_stable \<lparr>space = space M, sets = E i\<rparr>"
  assumes disjoint: "disjoint_family_on I J"
  shows "indep_sets (\<lambda>j. sigma_sets (space M) (\<Union>i\<in>I j. E i)) J"
proof -
  let "?E j" = "{\<Inter>k\<in>K. E' k| E' K. finite K \<and> K \<noteq> {} \<and> K \<subseteq> I j \<and> (\<forall>k\<in>K. E' k \<in> E k) }"

  from indep have E: "\<And>j i. j \<in> J \<Longrightarrow> i \<in> I j \<Longrightarrow> E i \<subseteq> events"
    unfolding indep_sets_def by auto
  { fix j
    let ?S = "sigma \<lparr> space = space M, sets = (\<Union>i\<in>I j. E i) \<rparr>"
    assume "j \<in> J"
    from E[OF this] interpret S: sigma_algebra ?S
      using sets_into_space by (intro sigma_algebra_sigma) auto

    have "sigma_sets (space M) (\<Union>i\<in>I j. E i) = sigma_sets (space M) (?E j)"
    proof (rule sigma_sets_eqI)
      fix A assume "A \<in> (\<Union>i\<in>I j. E i)"
      then guess i ..
      then show "A \<in> sigma_sets (space M) (?E j)"
        by (auto intro!: sigma_sets.intros exI[of _ "{i}"] exI[of _ "\<lambda>i. A"])
    next
      fix A assume "A \<in> ?E j"
      then obtain E' K where "finite K" "K \<noteq> {}" "K \<subseteq> I j" "\<And>k. k \<in> K \<Longrightarrow> E' k \<in> E k"
        and A: "A = (\<Inter>k\<in>K. E' k)"
        by auto
      then have "A \<in> sets ?S" unfolding A
        by (safe intro!: S.finite_INT)
           (auto simp: sets_sigma intro!: sigma_sets.Basic)
      then show "A \<in> sigma_sets (space M) (\<Union>i\<in>I j. E i)"
        by (simp add: sets_sigma)
    qed }
  moreover have "indep_sets (\<lambda>j. sigma_sets (space M) (?E j)) J"
  proof (rule indep_sets_sigma_sets)
    show "indep_sets ?E J"
    proof (intro indep_setsI)
      fix j assume "j \<in> J" with E show "?E j \<subseteq> events" by (force  intro!: finite_INT)
    next
      fix K A assume K: "K \<noteq> {}" "K \<subseteq> J" "finite K"
        and "\<forall>j\<in>K. A j \<in> ?E j"
      then have "\<forall>j\<in>K. \<exists>E' L. A j = (\<Inter>l\<in>L. E' l) \<and> finite L \<and> L \<noteq> {} \<and> L \<subseteq> I j \<and> (\<forall>l\<in>L. E' l \<in> E l)"
        by simp
      from bchoice[OF this] guess E' ..
      from bchoice[OF this] obtain L
        where A: "\<And>j. j\<in>K \<Longrightarrow> A j = (\<Inter>l\<in>L j. E' j l)"
        and L: "\<And>j. j\<in>K \<Longrightarrow> finite (L j)" "\<And>j. j\<in>K \<Longrightarrow> L j \<noteq> {}" "\<And>j. j\<in>K \<Longrightarrow> L j \<subseteq> I j"
        and E': "\<And>j l. j\<in>K \<Longrightarrow> l \<in> L j \<Longrightarrow> E' j l \<in> E l"
        by auto

      { fix k l j assume "k \<in> K" "j \<in> K" "l \<in> L j" "l \<in> L k"
        have "k = j"
        proof (rule ccontr)
          assume "k \<noteq> j"
          with disjoint `K \<subseteq> J` `k \<in> K` `j \<in> K` have "I k \<inter> I j = {}"
            unfolding disjoint_family_on_def by auto
          with L(2,3)[OF `j \<in> K`] L(2,3)[OF `k \<in> K`]
          show False using `l \<in> L k` `l \<in> L j` by auto
        qed }
      note L_inj = this

      def k \<equiv> "\<lambda>l. (SOME k. k \<in> K \<and> l \<in> L k)"
      { fix x j l assume *: "j \<in> K" "l \<in> L j"
        have "k l = j" unfolding k_def
        proof (rule some_equality)
          fix k assume "k \<in> K \<and> l \<in> L k"
          with * L_inj show "k = j" by auto
        qed (insert *, simp) }
      note k_simp[simp] = this
      let "?E' l" = "E' (k l) l"
      have "prob (\<Inter>j\<in>K. A j) = prob (\<Inter>l\<in>(\<Union>k\<in>K. L k). ?E' l)"
        by (auto simp: A intro!: arg_cong[where f=prob])
      also have "\<dots> = (\<Prod>l\<in>(\<Union>k\<in>K. L k). prob (?E' l))"
        using L K E' by (intro indep_setsD[OF indep]) (simp_all add: UN_mono)
      also have "\<dots> = (\<Prod>j\<in>K. \<Prod>l\<in>L j. prob (E' j l))"
        using K L L_inj by (subst setprod_UN_disjoint) auto
      also have "\<dots> = (\<Prod>j\<in>K. prob (A j))"
        using K L E' by (auto simp add: A intro!: setprod_cong indep_setsD[OF indep, symmetric]) blast
      finally show "prob (\<Inter>j\<in>K. A j) = (\<Prod>j\<in>K. prob (A j))" .
    qed
  next
    fix j assume "j \<in> J"
    show "Int_stable \<lparr> space = space M, sets = ?E j \<rparr>"
    proof (rule Int_stableI)
      fix a assume "a \<in> ?E j" then obtain Ka Ea
        where a: "a = (\<Inter>k\<in>Ka. Ea k)" "finite Ka" "Ka \<noteq> {}" "Ka \<subseteq> I j" "\<And>k. k\<in>Ka \<Longrightarrow> Ea k \<in> E k" by auto
      fix b assume "b \<in> ?E j" then obtain Kb Eb
        where b: "b = (\<Inter>k\<in>Kb. Eb k)" "finite Kb" "Kb \<noteq> {}" "Kb \<subseteq> I j" "\<And>k. k\<in>Kb \<Longrightarrow> Eb k \<in> E k" by auto
      let ?A = "\<lambda>k. (if k \<in> Ka \<inter> Kb then Ea k \<inter> Eb k else if k \<in> Kb then Eb k else if k \<in> Ka then Ea k else {})"
      have "a \<inter> b = INTER (Ka \<union> Kb) ?A"
        by (simp add: a b set_eq_iff) auto
      with a b `j \<in> J` Int_stableD[OF Int_stable] show "a \<inter> b \<in> ?E j"
        by (intro CollectI exI[of _ "Ka \<union> Kb"] exI[of _ ?A]) auto
    qed
  qed
  ultimately show ?thesis
    by (simp cong: indep_sets_cong)
qed

definition (in prob_space) terminal_events where
  "terminal_events A = (\<Inter>n. sigma_sets (space M) (UNION {n..} A))"

lemma (in prob_space) terminal_events_sets:
  assumes A: "\<And>i. A i \<subseteq> events"
  assumes "\<And>i::nat. sigma_algebra \<lparr>space = space M, sets = A i\<rparr>"
  assumes X: "X \<in> terminal_events A"
  shows "X \<in> events"
proof -
  let ?A = "(\<Inter>n. sigma_sets (space M) (UNION {n..} A))"
  interpret A: sigma_algebra "\<lparr>space = space M, sets = A i\<rparr>" for i by fact
  from X have "\<And>n. X \<in> sigma_sets (space M) (UNION {n..} A)" by (auto simp: terminal_events_def)
  from this[of 0] have "X \<in> sigma_sets (space M) (UNION UNIV A)" by simp
  then show "X \<in> events"
    by induct (insert A, auto)
qed

lemma (in prob_space) sigma_algebra_terminal_events:
  assumes "\<And>i::nat. sigma_algebra \<lparr>space = space M, sets = A i\<rparr>"
  shows "sigma_algebra \<lparr> space = space M, sets = terminal_events A \<rparr>"
  unfolding terminal_events_def
proof (simp add: sigma_algebra_iff2, safe)
  let ?A = "(\<Inter>n. sigma_sets (space M) (UNION {n..} A))"
  interpret A: sigma_algebra "\<lparr>space = space M, sets = A i\<rparr>" for i by fact
  { fix X x assume "X \<in> ?A" "x \<in> X" 
    then have "\<And>n. X \<in> sigma_sets (space M) (UNION {n..} A)" by auto
    from this[of 0] have "X \<in> sigma_sets (space M) (UNION UNIV A)" by simp
    then have "X \<subseteq> space M"
      by induct (insert A.sets_into_space, auto)
    with `x \<in> X` show "x \<in> space M" by auto }
  { fix F :: "nat \<Rightarrow> 'a set" and n assume "range F \<subseteq> ?A"
    then show "(UNION UNIV F) \<in> sigma_sets (space M) (UNION {n..} A)"
      by (intro sigma_sets.Union) auto }
qed (auto intro!: sigma_sets.Compl sigma_sets.Empty)

lemma (in prob_space) kolmogorov_0_1_law:
  fixes A :: "nat \<Rightarrow> 'a set set"
  assumes A: "\<And>i. A i \<subseteq> events"
  assumes "\<And>i::nat. sigma_algebra \<lparr>space = space M, sets = A i\<rparr>"
  assumes indep: "indep_sets A UNIV"
  and X: "X \<in> terminal_events A"
  shows "prob X = 0 \<or> prob X = 1"
proof -
  let ?D = "\<lparr> space = space M, sets = {D \<in> events. prob (X \<inter> D) = prob X * prob D} \<rparr>"
  interpret A: sigma_algebra "\<lparr>space = space M, sets = A i\<rparr>" for i by fact
  interpret T: sigma_algebra "\<lparr> space = space M, sets = terminal_events A \<rparr>"
    by (rule sigma_algebra_terminal_events) fact
  have "X \<subseteq> space M" using T.space_closed X by auto

  have X_in: "X \<in> events"
    by (rule terminal_events_sets) fact+

  interpret D: dynkin_system ?D
  proof (rule dynkin_systemI)
    fix D assume "D \<in> sets ?D" then show "D \<subseteq> space ?D"
      using sets_into_space by auto
  next
    show "space ?D \<in> sets ?D"
      using prob_space `X \<subseteq> space M` by (simp add: Int_absorb2)
  next
    fix A assume A: "A \<in> sets ?D"
    have "prob (X \<inter> (space M - A)) = prob (X - (X \<inter> A))"
      using `X \<subseteq> space M` by (auto intro!: arg_cong[where f=prob])
    also have "\<dots> = prob X - prob (X \<inter> A)"
      using X_in A by (intro finite_measure_Diff) auto
    also have "\<dots> = prob X * prob (space M) - prob X * prob A"
      using A prob_space by auto
    also have "\<dots> = prob X * prob (space M - A)"
      using X_in A sets_into_space
      by (subst finite_measure_Diff) (auto simp: field_simps)
    finally show "space ?D - A \<in> sets ?D"
      using A `X \<subseteq> space M` by auto
  next
    fix F :: "nat \<Rightarrow> 'a set" assume dis: "disjoint_family F" and "range F \<subseteq> sets ?D"
    then have F: "range F \<subseteq> events" "\<And>i. prob (X \<inter> F i) = prob X * prob (F i)"
      by auto
    have "(\<lambda>i. prob (X \<inter> F i)) sums prob (\<Union>i. X \<inter> F i)"
    proof (rule finite_measure_UNION)
      show "range (\<lambda>i. X \<inter> F i) \<subseteq> events"
        using F X_in by auto
      show "disjoint_family (\<lambda>i. X \<inter> F i)"
        using dis by (rule disjoint_family_on_bisimulation) auto
    qed
    with F have "(\<lambda>i. prob X * prob (F i)) sums prob (X \<inter> (\<Union>i. F i))"
      by simp
    moreover have "(\<lambda>i. prob X * prob (F i)) sums (prob X * prob (\<Union>i. F i))"
      by (intro mult_right.sums finite_measure_UNION F dis)
    ultimately have "prob (X \<inter> (\<Union>i. F i)) = prob X * prob (\<Union>i. F i)"
      by (auto dest!: sums_unique)
    with F show "(\<Union>i. F i) \<in> sets ?D"
      by auto
  qed

  { fix n
    have "indep_sets (\<lambda>b. sigma_sets (space M) (\<Union>m\<in>bool_case {..n} {Suc n..} b. A m)) UNIV"
    proof (rule indep_sets_collect_sigma)
      have *: "(\<Union>b. case b of True \<Rightarrow> {..n} | False \<Rightarrow> {Suc n..}) = UNIV" (is "?U = _")
        by (simp split: bool.split add: set_eq_iff) (metis not_less_eq_eq)
      with indep show "indep_sets A ?U" by simp
      show "disjoint_family (bool_case {..n} {Suc n..})"
        unfolding disjoint_family_on_def by (auto split: bool.split)
      fix m
      show "Int_stable \<lparr>space = space M, sets = A m\<rparr>"
        unfolding Int_stable_def using A.Int by auto
    qed
    also have "(\<lambda>b. sigma_sets (space M) (\<Union>m\<in>bool_case {..n} {Suc n..} b. A m)) = 
      bool_case (sigma_sets (space M) (\<Union>m\<in>{..n}. A m)) (sigma_sets (space M) (\<Union>m\<in>{Suc n..}. A m))"
      by (auto intro!: ext split: bool.split)
    finally have indep: "indep_set (sigma_sets (space M) (\<Union>m\<in>{..n}. A m)) (sigma_sets (space M) (\<Union>m\<in>{Suc n..}. A m))"
      unfolding indep_set_def by simp

    have "sigma_sets (space M) (\<Union>m\<in>{..n}. A m) \<subseteq> sets ?D"
    proof (simp add: subset_eq, rule)
      fix D assume D: "D \<in> sigma_sets (space M) (\<Union>m\<in>{..n}. A m)"
      have "X \<in> sigma_sets (space M) (\<Union>m\<in>{Suc n..}. A m)"
        using X unfolding terminal_events_def by simp
      from indep_setD[OF indep D this] indep_setD_ev1[OF indep] D
      show "D \<in> events \<and> prob (X \<inter> D) = prob X * prob D"
        by (auto simp add: ac_simps)
    qed }
  then have "(\<Union>n. sigma_sets (space M) (\<Union>m\<in>{..n}. A m)) \<subseteq> sets ?D" (is "?A \<subseteq> _")
    by auto

  have "sigma \<lparr> space = space M, sets = ?A \<rparr> =
    dynkin \<lparr> space = space M, sets = ?A \<rparr>" (is "sigma ?UA = dynkin ?UA")
  proof (rule sigma_eq_dynkin)
    { fix B n assume "B \<in> sigma_sets (space M) (\<Union>m\<in>{..n}. A m)"
      then have "B \<subseteq> space M"
        by induct (insert A sets_into_space, auto) }
    then show "sets ?UA \<subseteq> Pow (space ?UA)" by auto
    show "Int_stable ?UA"
    proof (rule Int_stableI)
      fix a assume "a \<in> ?A" then guess n .. note a = this
      fix b assume "b \<in> ?A" then guess m .. note b = this
      interpret Amn: sigma_algebra "sigma \<lparr>space = space M, sets = (\<Union>i\<in>{..max m n}. A i)\<rparr>"
        using A sets_into_space by (intro sigma_algebra_sigma) auto
      have "sigma_sets (space M) (\<Union>i\<in>{..n}. A i) \<subseteq> sigma_sets (space M) (\<Union>i\<in>{..max m n}. A i)"
        by (intro sigma_sets_subseteq UN_mono) auto
      with a have "a \<in> sigma_sets (space M) (\<Union>i\<in>{..max m n}. A i)" by auto
      moreover
      have "sigma_sets (space M) (\<Union>i\<in>{..m}. A i) \<subseteq> sigma_sets (space M) (\<Union>i\<in>{..max m n}. A i)"
        by (intro sigma_sets_subseteq UN_mono) auto
      with b have "b \<in> sigma_sets (space M) (\<Union>i\<in>{..max m n}. A i)" by auto
      ultimately have "a \<inter> b \<in> sigma_sets (space M) (\<Union>i\<in>{..max m n}. A i)"
        using Amn.Int[of a b] by (simp add: sets_sigma)
      then show "a \<inter> b \<in> (\<Union>n. sigma_sets (space M) (\<Union>i\<in>{..n}. A i))" by auto
    qed
  qed
  moreover have "sets (dynkin ?UA) \<subseteq> sets ?D"
  proof (rule D.dynkin_subset)
    show "sets ?UA \<subseteq> sets ?D" using `?A \<subseteq> sets ?D` by auto
  qed simp
  ultimately have "sets (sigma ?UA) \<subseteq> sets ?D" by simp
  moreover
  have "\<And>n. sigma_sets (space M) (\<Union>i\<in>{n..}. A i) \<subseteq> sigma_sets (space M) ?A"
    by (intro sigma_sets_subseteq UN_mono) (auto intro: sigma_sets.Basic)
  then have "terminal_events A \<subseteq> sets (sigma ?UA)"
    unfolding sets_sigma terminal_events_def by auto
  moreover note `X \<in> terminal_events A`
  ultimately have "X \<in> sets ?D" by auto
  then show ?thesis by auto
qed

end
