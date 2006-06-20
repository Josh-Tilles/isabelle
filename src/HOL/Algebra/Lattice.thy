(*
  Title:     HOL/Algebra/Lattice.thy
  Id:        $Id$
  Author:    Clemens Ballarin, started 7 November 2003
  Copyright: Clemens Ballarin
*)

header {* Orders and Lattices *}

theory Lattice imports Main begin

text {* Object with a carrier set. *}

record 'a partial_object =
  carrier :: "'a set"

subsection {* Partial Orders *}

record 'a order = "'a partial_object" +
  le :: "['a, 'a] => bool" (infixl "\<sqsubseteq>\<index>" 50)

locale partial_order =
  fixes L (structure)
  assumes refl [intro, simp]:
                  "x \<in> carrier L ==> x \<sqsubseteq> x"
    and anti_sym [intro]:
                  "[| x \<sqsubseteq> y; y \<sqsubseteq> x; x \<in> carrier L; y \<in> carrier L |] ==> x = y"
    and trans [trans]:
                  "[| x \<sqsubseteq> y; y \<sqsubseteq> z;
                   x \<in> carrier L; y \<in> carrier L; z \<in> carrier L |] ==> x \<sqsubseteq> z"

constdefs (structure L)
  lless :: "[_, 'a, 'a] => bool" (infixl "\<sqsubset>\<index>" 50)
  "x \<sqsubset> y == x \<sqsubseteq> y & x ~= y"

  -- {* Upper and lower bounds of a set. *}
  Upper :: "[_, 'a set] => 'a set"
  "Upper L A == {u. (ALL x. x \<in> A \<inter> carrier L --> x \<sqsubseteq> u)} \<inter>
                carrier L"

  Lower :: "[_, 'a set] => 'a set"
  "Lower L A == {l. (ALL x. x \<in> A \<inter> carrier L --> l \<sqsubseteq> x)} \<inter>
                carrier L"

  -- {* Least and greatest, as predicate. *}
  least :: "[_, 'a, 'a set] => bool"
  "least L l A == A \<subseteq> carrier L & l \<in> A & (ALL x : A. l \<sqsubseteq> x)"

  greatest :: "[_, 'a, 'a set] => bool"
  "greatest L g A == A \<subseteq> carrier L & g \<in> A & (ALL x : A. x \<sqsubseteq> g)"

  -- {* Supremum and infimum *}
  sup :: "[_, 'a set] => 'a" ("\<Squnion>\<index>_" [90] 90)
  "\<Squnion>A == THE x. least L x (Upper L A)"

  inf :: "[_, 'a set] => 'a" ("\<Sqinter>\<index>_" [90] 90)
  "\<Sqinter>A == THE x. greatest L x (Lower L A)"

  join :: "[_, 'a, 'a] => 'a" (infixl "\<squnion>\<index>" 65)
  "x \<squnion> y == sup L {x, y}"

  meet :: "[_, 'a, 'a] => 'a" (infixl "\<sqinter>\<index>" 70)
  "x \<sqinter> y == inf L {x, y}"


subsubsection {* Upper *}

lemma Upper_closed [intro, simp]:
  "Upper L A \<subseteq> carrier L"
  by (unfold Upper_def) clarify

lemma UpperD [dest]:
  fixes L (structure)
  shows "[| u \<in> Upper L A; x \<in> A; A \<subseteq> carrier L |] ==> x \<sqsubseteq> u"
  by (unfold Upper_def) blast

lemma Upper_memI:
  fixes L (structure)
  shows "[| !! y. y \<in> A ==> y \<sqsubseteq> x; x \<in> carrier L |] ==> x \<in> Upper L A"
  by (unfold Upper_def) blast

lemma Upper_antimono:
  "A \<subseteq> B ==> Upper L B \<subseteq> Upper L A"
  by (unfold Upper_def) blast


subsubsection {* Lower *}

lemma Lower_closed [intro, simp]:
  "Lower L A \<subseteq> carrier L"
  by (unfold Lower_def) clarify

lemma LowerD [dest]:
  fixes L (structure)
  shows "[| l \<in> Lower L A; x \<in> A; A \<subseteq> carrier L |] ==> l \<sqsubseteq> x"
  by (unfold Lower_def) blast

lemma Lower_memI:
  fixes L (structure)
  shows "[| !! y. y \<in> A ==> x \<sqsubseteq> y; x \<in> carrier L |] ==> x \<in> Lower L A"
  by (unfold Lower_def) blast

lemma Lower_antimono:
  "A \<subseteq> B ==> Lower L B \<subseteq> Lower L A"
  by (unfold Lower_def) blast


subsubsection {* least *}

lemma least_carrier [intro, simp]:
  shows "least L l A ==> l \<in> carrier L"
  by (unfold least_def) fast

lemma least_mem:
  "least L l A ==> l \<in> A"
  by (unfold least_def) fast

lemma (in partial_order) least_unique:
  "[| least L x A; least L y A |] ==> x = y"
  by (unfold least_def) blast

lemma least_le:
  fixes L (structure)
  shows "[| least L x A; a \<in> A |] ==> x \<sqsubseteq> a"
  by (unfold least_def) fast

lemma least_UpperI:
  fixes L (structure)
  assumes above: "!! x. x \<in> A ==> x \<sqsubseteq> s"
    and below: "!! y. y \<in> Upper L A ==> s \<sqsubseteq> y"
    and L: "A \<subseteq> carrier L"  "s \<in> carrier L"
  shows "least L s (Upper L A)"
proof -
  have "Upper L A \<subseteq> carrier L" by simp
  moreover from above L have "s \<in> Upper L A" by (simp add: Upper_def)
  moreover from below have "ALL x : Upper L A. s \<sqsubseteq> x" by fast
  ultimately show ?thesis by (simp add: least_def)
qed


subsubsection {* greatest *}

lemma greatest_carrier [intro, simp]:
  shows "greatest L l A ==> l \<in> carrier L"
  by (unfold greatest_def) fast

lemma greatest_mem:
  "greatest L l A ==> l \<in> A"
  by (unfold greatest_def) fast

lemma (in partial_order) greatest_unique:
  "[| greatest L x A; greatest L y A |] ==> x = y"
  by (unfold greatest_def) blast

lemma greatest_le:
  fixes L (structure)
  shows "[| greatest L x A; a \<in> A |] ==> a \<sqsubseteq> x"
  by (unfold greatest_def) fast

lemma greatest_LowerI:
  fixes L (structure)
  assumes below: "!! x. x \<in> A ==> i \<sqsubseteq> x"
    and above: "!! y. y \<in> Lower L A ==> y \<sqsubseteq> i"
    and L: "A \<subseteq> carrier L"  "i \<in> carrier L"
  shows "greatest L i (Lower L A)"
proof -
  have "Lower L A \<subseteq> carrier L" by simp
  moreover from below L have "i \<in> Lower L A" by (simp add: Lower_def)
  moreover from above have "ALL x : Lower L A. x \<sqsubseteq> i" by fast
  ultimately show ?thesis by (simp add: greatest_def)
qed


subsection {* Lattices *}

locale lattice = partial_order +
  assumes sup_of_two_exists:
    "[| x \<in> carrier L; y \<in> carrier L |] ==> EX s. least L s (Upper L {x, y})"
    and inf_of_two_exists:
    "[| x \<in> carrier L; y \<in> carrier L |] ==> EX s. greatest L s (Lower L {x, y})"

lemma least_Upper_above:
  fixes L (structure)
  shows "[| least L s (Upper L A); x \<in> A; A \<subseteq> carrier L |] ==> x \<sqsubseteq> s"
  by (unfold least_def) blast

lemma greatest_Lower_above:
  fixes L (structure)
  shows "[| greatest L i (Lower L A); x \<in> A; A \<subseteq> carrier L |] ==> i \<sqsubseteq> x"
  by (unfold greatest_def) blast


subsubsection {* Supremum *}

lemma (in lattice) joinI:
  "[| !!l. least L l (Upper L {x, y}) ==> P l; x \<in> carrier L; y \<in> carrier L |]
  ==> P (x \<squnion> y)"
proof (unfold join_def sup_def)
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
    and P: "!!l. least L l (Upper L {x, y}) ==> P l"
  with sup_of_two_exists obtain s where "least L s (Upper L {x, y})" by fast
  with L show "P (THE l. least L l (Upper L {x, y}))"
    by (fast intro: theI2 least_unique P)
qed

lemma (in lattice) join_closed [simp]:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<squnion> y \<in> carrier L"
  by (rule joinI) (rule least_carrier)

lemma (in partial_order) sup_of_singletonI:      (* only reflexivity needed ? *)
  "x \<in> carrier L ==> least L x (Upper L {x})"
  by (rule least_UpperI) fast+

lemma (in partial_order) sup_of_singleton [simp]:
  "x \<in> carrier L ==> \<Squnion>{x} = x"
  by (unfold sup_def) (blast intro: least_unique least_UpperI sup_of_singletonI)


text {* Condition on @{text A}: supremum exists. *}

lemma (in lattice) sup_insertI:
  "[| !!s. least L s (Upper L (insert x A)) ==> P s;
  least L a (Upper L A); x \<in> carrier L; A \<subseteq> carrier L |]
  ==> P (\<Squnion>(insert x A))"
proof (unfold sup_def)
  assume L: "x \<in> carrier L"  "A \<subseteq> carrier L"
    and P: "!!l. least L l (Upper L (insert x A)) ==> P l"
    and least_a: "least L a (Upper L A)"
  from L least_a have La: "a \<in> carrier L" by simp
  from L sup_of_two_exists least_a
  obtain s where least_s: "least L s (Upper L {a, x})" by blast
  show "P (THE l. least L l (Upper L (insert x A)))"
  proof (rule theI2)
    show "least L s (Upper L (insert x A))"
    proof (rule least_UpperI)
      fix z
      assume "z \<in> insert x A"
      then show "z \<sqsubseteq> s"
      proof
        assume "z = x" then show ?thesis
          by (simp add: least_Upper_above [OF least_s] L La)
      next
        assume "z \<in> A"
        with L least_s least_a show ?thesis
          by (rule_tac trans [where y = a]) (auto dest: least_Upper_above)
      qed
    next
      fix y
      assume y: "y \<in> Upper L (insert x A)"
      show "s \<sqsubseteq> y"
      proof (rule least_le [OF least_s], rule Upper_memI)
	fix z
	assume z: "z \<in> {a, x}"
	then show "z \<sqsubseteq> y"
	proof
          have y': "y \<in> Upper L A"
            apply (rule subsetD [where A = "Upper L (insert x A)"])
            apply (rule Upper_antimono) apply clarify apply assumption
            done
          assume "z = a"
          with y' least_a show ?thesis by (fast dest: least_le)
	next
	  assume "z \<in> {x}"  (* FIXME "z = x"; declare specific elim rule for "insert x {}" (!?) *)
          with y L show ?thesis by blast
	qed
      qed (rule Upper_closed [THEN subsetD])
    next
      from L show "insert x A \<subseteq> carrier L" by simp
      from least_s show "s \<in> carrier L" by simp
    qed
  next
    fix l
    assume least_l: "least L l (Upper L (insert x A))"
    show "l = s"
    proof (rule least_unique)
      show "least L s (Upper L (insert x A))"
      proof (rule least_UpperI)
        fix z
        assume "z \<in> insert x A"
        then show "z \<sqsubseteq> s"
	proof
          assume "z = x" then show ?thesis
            by (simp add: least_Upper_above [OF least_s] L La)
	next
          assume "z \<in> A"
          with L least_s least_a show ?thesis
            by (rule_tac trans [where y = a]) (auto dest: least_Upper_above)
	qed
      next
        fix y
        assume y: "y \<in> Upper L (insert x A)"
        show "s \<sqsubseteq> y"
        proof (rule least_le [OF least_s], rule Upper_memI)
          fix z
          assume z: "z \<in> {a, x}"
          then show "z \<sqsubseteq> y"
          proof
            have y': "y \<in> Upper L A"
	      apply (rule subsetD [where A = "Upper L (insert x A)"])
	      apply (rule Upper_antimono) apply clarify apply assumption
	      done
            assume "z = a"
            with y' least_a show ?thesis by (fast dest: least_le)
	  next
            assume "z \<in> {x}"
            with y L show ?thesis by blast
          qed
        qed (rule Upper_closed [THEN subsetD])
      next
        from L show "insert x A \<subseteq> carrier L" by simp
        from least_s show "s \<in> carrier L" by simp
      qed
    qed
  qed
qed

lemma (in lattice) finite_sup_least:
  "[| finite A; A \<subseteq> carrier L; A ~= {} |] ==> least L (\<Squnion>A) (Upper L A)"
proof (induct set: Finites)
  case empty
  then show ?case by simp
next
  case (insert x A)
  show ?case
  proof (cases "A = {}")
    case True
    with insert show ?thesis by (simp add: sup_of_singletonI)
  next
    case False
    with insert have "least L (\<Squnion>A) (Upper L A)" by simp
    with _ show ?thesis
      by (rule sup_insertI) (simp_all add: insert [simplified])
  qed
qed

lemma (in lattice) finite_sup_insertI:
  assumes P: "!!l. least L l (Upper L (insert x A)) ==> P l"
    and xA: "finite A"  "x \<in> carrier L"  "A \<subseteq> carrier L"
  shows "P (\<Squnion> (insert x A))"
proof (cases "A = {}")
  case True with P and xA show ?thesis
    by (simp add: sup_of_singletonI)
next
  case False with P and xA show ?thesis
    by (simp add: sup_insertI finite_sup_least)
qed

lemma (in lattice) finite_sup_closed:
  "[| finite A; A \<subseteq> carrier L; A ~= {} |] ==> \<Squnion>A \<in> carrier L"
proof (induct set: Finites)
  case empty then show ?case by simp
next
  case insert then show ?case
    by - (rule finite_sup_insertI, simp_all)
qed

lemma (in lattice) join_left:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqsubseteq> x \<squnion> y"
  by (rule joinI [folded join_def]) (blast dest: least_mem)

lemma (in lattice) join_right:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> y \<sqsubseteq> x \<squnion> y"
  by (rule joinI [folded join_def]) (blast dest: least_mem)

lemma (in lattice) sup_of_two_least:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> least L (\<Squnion>{x, y}) (Upper L {x, y})"
proof (unfold sup_def)
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
  with sup_of_two_exists obtain s where "least L s (Upper L {x, y})" by fast
  with L show "least L (THE xa. least L xa (Upper L {x, y})) (Upper L {x, y})"
  by (fast intro: theI2 least_unique)  (* blast fails *)
qed

lemma (in lattice) join_le:
  assumes sub: "x \<sqsubseteq> z"  "y \<sqsubseteq> z"
    and L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "x \<squnion> y \<sqsubseteq> z"
proof (rule joinI)
  fix s
  assume "least L s (Upper L {x, y})"
  with sub L show "s \<sqsubseteq> z" by (fast elim: least_le intro: Upper_memI)
qed

lemma (in lattice) join_assoc_lemma:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "x \<squnion> (y \<squnion> z) = \<Squnion>{x, y, z}"
proof (rule finite_sup_insertI)
  -- {* The textbook argument in Jacobson I, p 457 *}
  fix s
  assume sup: "least L s (Upper L {x, y, z})"
  show "x \<squnion> (y \<squnion> z) = s"
  proof (rule anti_sym)
    from sup L show "x \<squnion> (y \<squnion> z) \<sqsubseteq> s"
      by (fastsimp intro!: join_le elim: least_Upper_above)
  next
    from sup L show "s \<sqsubseteq> x \<squnion> (y \<squnion> z)"
    by (erule_tac least_le)
      (blast intro!: Upper_memI intro: trans join_left join_right join_closed)
  qed (simp_all add: L least_carrier [OF sup])
qed (simp_all add: L)

lemma join_comm:
  fixes L (structure)
  shows "x \<squnion> y = y \<squnion> x"
  by (unfold join_def) (simp add: insert_commute)

lemma (in lattice) join_assoc:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
proof -
  have "(x \<squnion> y) \<squnion> z = z \<squnion> (x \<squnion> y)" by (simp only: join_comm)
  also from L have "... = \<Squnion>{z, x, y}" by (simp add: join_assoc_lemma)
  also from L have "... = \<Squnion>{x, y, z}" by (simp add: insert_commute)
  also from L have "... = x \<squnion> (y \<squnion> z)" by (simp add: join_assoc_lemma)
  finally show ?thesis .
qed


subsubsection {* Infimum *}

lemma (in lattice) meetI:
  "[| !!i. greatest L i (Lower L {x, y}) ==> P i;
  x \<in> carrier L; y \<in> carrier L |]
  ==> P (x \<sqinter> y)"
proof (unfold meet_def inf_def)
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
    and P: "!!g. greatest L g (Lower L {x, y}) ==> P g"
  with inf_of_two_exists obtain i where "greatest L i (Lower L {x, y})" by fast
  with L show "P (THE g. greatest L g (Lower L {x, y}))"
  by (fast intro: theI2 greatest_unique P)
qed

lemma (in lattice) meet_closed [simp]:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqinter> y \<in> carrier L"
  by (rule meetI) (rule greatest_carrier)

lemma (in partial_order) inf_of_singletonI:      (* only reflexivity needed ? *)
  "x \<in> carrier L ==> greatest L x (Lower L {x})"
  by (rule greatest_LowerI) fast+

lemma (in partial_order) inf_of_singleton [simp]:
  "x \<in> carrier L ==> \<Sqinter> {x} = x"
  by (unfold inf_def) (blast intro: greatest_unique greatest_LowerI inf_of_singletonI)

text {* Condition on A: infimum exists. *}

lemma (in lattice) inf_insertI:
  "[| !!i. greatest L i (Lower L (insert x A)) ==> P i;
  greatest L a (Lower L A); x \<in> carrier L; A \<subseteq> carrier L |]
  ==> P (\<Sqinter>(insert x A))"
proof (unfold inf_def)
  assume L: "x \<in> carrier L"  "A \<subseteq> carrier L"
    and P: "!!g. greatest L g (Lower L (insert x A)) ==> P g"
    and greatest_a: "greatest L a (Lower L A)"
  from L greatest_a have La: "a \<in> carrier L" by simp
  from L inf_of_two_exists greatest_a
  obtain i where greatest_i: "greatest L i (Lower L {a, x})" by blast
  show "P (THE g. greatest L g (Lower L (insert x A)))"
  proof (rule theI2)
    show "greatest L i (Lower L (insert x A))"
    proof (rule greatest_LowerI)
      fix z
      assume "z \<in> insert x A"
      then show "i \<sqsubseteq> z"
      proof
        assume "z = x" then show ?thesis
          by (simp add: greatest_Lower_above [OF greatest_i] L La)
      next
        assume "z \<in> A"
        with L greatest_i greatest_a show ?thesis
          by (rule_tac trans [where y = a]) (auto dest: greatest_Lower_above)
      qed
    next
      fix y
      assume y: "y \<in> Lower L (insert x A)"
      show "y \<sqsubseteq> i"
      proof (rule greatest_le [OF greatest_i], rule Lower_memI)
	fix z
	assume z: "z \<in> {a, x}"
	then show "y \<sqsubseteq> z"
	proof
          have y': "y \<in> Lower L A"
            apply (rule subsetD [where A = "Lower L (insert x A)"])
            apply (rule Lower_antimono) apply clarify apply assumption
            done
          assume "z = a"
          with y' greatest_a show ?thesis by (fast dest: greatest_le)
	next
          assume "z \<in> {x}"
          with y L show ?thesis by blast
	qed
      qed (rule Lower_closed [THEN subsetD])
    next
      from L show "insert x A \<subseteq> carrier L" by simp
      from greatest_i show "i \<in> carrier L" by simp
    qed
  next
    fix g
    assume greatest_g: "greatest L g (Lower L (insert x A))"
    show "g = i"
    proof (rule greatest_unique)
      show "greatest L i (Lower L (insert x A))"
      proof (rule greatest_LowerI)
        fix z
        assume "z \<in> insert x A"
        then show "i \<sqsubseteq> z"
	proof
          assume "z = x" then show ?thesis
            by (simp add: greatest_Lower_above [OF greatest_i] L La)
	next
          assume "z \<in> A"
          with L greatest_i greatest_a show ?thesis
            by (rule_tac trans [where y = a]) (auto dest: greatest_Lower_above)
        qed
      next
        fix y
        assume y: "y \<in> Lower L (insert x A)"
        show "y \<sqsubseteq> i"
        proof (rule greatest_le [OF greatest_i], rule Lower_memI)
          fix z
          assume z: "z \<in> {a, x}"
          then show "y \<sqsubseteq> z"
          proof
            have y': "y \<in> Lower L A"
	      apply (rule subsetD [where A = "Lower L (insert x A)"])
	      apply (rule Lower_antimono) apply clarify apply assumption
	      done
            assume "z = a"
            with y' greatest_a show ?thesis by (fast dest: greatest_le)
	  next
            assume "z \<in> {x}"
            with y L show ?thesis by blast
	  qed
        qed (rule Lower_closed [THEN subsetD])
      next
        from L show "insert x A \<subseteq> carrier L" by simp
        from greatest_i show "i \<in> carrier L" by simp
      qed
    qed
  qed
qed

lemma (in lattice) finite_inf_greatest:
  "[| finite A; A \<subseteq> carrier L; A ~= {} |] ==> greatest L (\<Sqinter>A) (Lower L A)"
proof (induct set: Finites)
  case empty then show ?case by simp
next
  case (insert x A)
  show ?case
  proof (cases "A = {}")
    case True
    with insert show ?thesis by (simp add: inf_of_singletonI)
  next
    case False
    from insert show ?thesis
    proof (rule_tac inf_insertI)
      from False insert show "greatest L (\<Sqinter>A) (Lower L A)" by simp
    qed simp_all
  qed
qed

lemma (in lattice) finite_inf_insertI:
  assumes P: "!!i. greatest L i (Lower L (insert x A)) ==> P i"
    and xA: "finite A"  "x \<in> carrier L"  "A \<subseteq> carrier L"
  shows "P (\<Sqinter> (insert x A))"
proof (cases "A = {}")
  case True with P and xA show ?thesis
    by (simp add: inf_of_singletonI)
next
  case False with P and xA show ?thesis
    by (simp add: inf_insertI finite_inf_greatest)
qed

lemma (in lattice) finite_inf_closed:
  "[| finite A; A \<subseteq> carrier L; A ~= {} |] ==> \<Sqinter>A \<in> carrier L"
proof (induct set: Finites)
  case empty then show ?case by simp
next
  case insert then show ?case
    by (rule_tac finite_inf_insertI) (simp_all)
qed

lemma (in lattice) meet_left:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqinter> y \<sqsubseteq> x"
  by (rule meetI [folded meet_def]) (blast dest: greatest_mem)

lemma (in lattice) meet_right:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqinter> y \<sqsubseteq> y"
  by (rule meetI [folded meet_def]) (blast dest: greatest_mem)

lemma (in lattice) inf_of_two_greatest:
  "[| x \<in> carrier L; y \<in> carrier L |] ==>
  greatest L (\<Sqinter> {x, y}) (Lower L {x, y})"
proof (unfold inf_def)
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
  with inf_of_two_exists obtain s where "greatest L s (Lower L {x, y})" by fast
  with L
  show "greatest L (THE xa. greatest L xa (Lower L {x, y})) (Lower L {x, y})"
  by (fast intro: theI2 greatest_unique)  (* blast fails *)
qed

lemma (in lattice) meet_le:
  assumes sub: "z \<sqsubseteq> x"  "z \<sqsubseteq> y"
    and L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "z \<sqsubseteq> x \<sqinter> y"
proof (rule meetI)
  fix i
  assume "greatest L i (Lower L {x, y})"
  with sub L show "z \<sqsubseteq> i" by (fast elim: greatest_le intro: Lower_memI)
qed

lemma (in lattice) meet_assoc_lemma:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "x \<sqinter> (y \<sqinter> z) = \<Sqinter>{x, y, z}"
proof (rule finite_inf_insertI)
  txt {* The textbook argument in Jacobson I, p 457 *}
  fix i
  assume inf: "greatest L i (Lower L {x, y, z})"
  show "x \<sqinter> (y \<sqinter> z) = i"
  proof (rule anti_sym)
    from inf L show "i \<sqsubseteq> x \<sqinter> (y \<sqinter> z)"
      by (fastsimp intro!: meet_le elim: greatest_Lower_above)
  next
    from inf L show "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> i"
    by (erule_tac greatest_le)
      (blast intro!: Lower_memI intro: trans meet_left meet_right meet_closed)
  qed (simp_all add: L greatest_carrier [OF inf])
qed (simp_all add: L)

lemma meet_comm:
  fixes L (structure)
  shows "x \<sqinter> y = y \<sqinter> x"
  by (unfold meet_def) (simp add: insert_commute)

lemma (in lattice) meet_assoc:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
proof -
  have "(x \<sqinter> y) \<sqinter> z = z \<sqinter> (x \<sqinter> y)" by (simp only: meet_comm)
  also from L have "... = \<Sqinter> {z, x, y}" by (simp add: meet_assoc_lemma)
  also from L have "... = \<Sqinter> {x, y, z}" by (simp add: insert_commute)
  also from L have "... = x \<sqinter> (y \<sqinter> z)" by (simp add: meet_assoc_lemma)
  finally show ?thesis .
qed


subsection {* Total Orders *}

locale total_order = lattice +
  assumes total: "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqsubseteq> y | y \<sqsubseteq> x"

text {* Introduction rule: the usual definition of total order *}

lemma (in partial_order) total_orderI:
  assumes total: "!!x y. [| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqsubseteq> y | y \<sqsubseteq> x"
  shows "total_order L"
proof (intro_locales!)
  show "lattice_axioms L"
  proof (rule lattice_axioms.intro)
    fix x y
    assume L: "x \<in> carrier L"  "y \<in> carrier L"
    show "EX s. least L s (Upper L {x, y})"
    proof -
      note total L
      moreover
      {
        assume "x \<sqsubseteq> y"
        with L have "least L y (Upper L {x, y})"
          by (rule_tac least_UpperI) auto
      }
      moreover
      {
        assume "y \<sqsubseteq> x"
        with L have "least L x (Upper L {x, y})"
          by (rule_tac least_UpperI) auto
      }
      ultimately show ?thesis by blast
    qed
  next
    fix x y
    assume L: "x \<in> carrier L"  "y \<in> carrier L"
    show "EX i. greatest L i (Lower L {x, y})"
    proof -
      note total L
      moreover
      {
        assume "y \<sqsubseteq> x"
        with L have "greatest L y (Lower L {x, y})"
          by (rule_tac greatest_LowerI) auto
      }
      moreover
      {
        assume "x \<sqsubseteq> y"
        with L have "greatest L x (Lower L {x, y})"
          by (rule_tac greatest_LowerI) auto
      }
      ultimately show ?thesis by blast
    qed
  qed
qed (assumption | rule total_order_axioms.intro)+


subsection {* Complete lattices *}

locale complete_lattice = lattice +
  assumes sup_exists:
    "[| A \<subseteq> carrier L |] ==> EX s. least L s (Upper L A)"
    and inf_exists:
    "[| A \<subseteq> carrier L |] ==> EX i. greatest L i (Lower L A)"

text {* Introduction rule: the usual definition of complete lattice *}

lemma (in partial_order) complete_latticeI:
  assumes sup_exists:
    "!!A. [| A \<subseteq> carrier L |] ==> EX s. least L s (Upper L A)"
    and inf_exists:
    "!!A. [| A \<subseteq> carrier L |] ==> EX i. greatest L i (Lower L A)"
  shows "complete_lattice L"
proof (intro_locales!)
  show "lattice_axioms L"
    by (rule lattice_axioms.intro) (blast intro: sup_exists inf_exists)+
qed (assumption | rule complete_lattice_axioms.intro)+

constdefs (structure L)
  top :: "_ => 'a" ("\<top>\<index>")
  "\<top> == sup L (carrier L)"

  bottom :: "_ => 'a" ("\<bottom>\<index>")
  "\<bottom> == inf L (carrier L)"


lemma (in complete_lattice) supI:
  "[| !!l. least L l (Upper L A) ==> P l; A \<subseteq> carrier L |]
  ==> P (\<Squnion>A)"
proof (unfold sup_def)
  assume L: "A \<subseteq> carrier L"
    and P: "!!l. least L l (Upper L A) ==> P l"
  with sup_exists obtain s where "least L s (Upper L A)" by blast
  with L show "P (THE l. least L l (Upper L A))"
  by (fast intro: theI2 least_unique P)
qed

lemma (in complete_lattice) sup_closed [simp]:
  "A \<subseteq> carrier L ==> \<Squnion>A \<in> carrier L"
  by (rule supI) simp_all

lemma (in complete_lattice) top_closed [simp, intro]:
  "\<top> \<in> carrier L"
  by (unfold top_def) simp

lemma (in complete_lattice) infI:
  "[| !!i. greatest L i (Lower L A) ==> P i; A \<subseteq> carrier L |]
  ==> P (\<Sqinter>A)"
proof (unfold inf_def)
  assume L: "A \<subseteq> carrier L"
    and P: "!!l. greatest L l (Lower L A) ==> P l"
  with inf_exists obtain s where "greatest L s (Lower L A)" by blast
  with L show "P (THE l. greatest L l (Lower L A))"
  by (fast intro: theI2 greatest_unique P)
qed

lemma (in complete_lattice) inf_closed [simp]:
  "A \<subseteq> carrier L ==> \<Sqinter>A \<in> carrier L"
  by (rule infI) simp_all

lemma (in complete_lattice) bottom_closed [simp, intro]:
  "\<bottom> \<in> carrier L"
  by (unfold bottom_def) simp

text {* Jacobson: Theorem 8.1 *}

lemma Lower_empty [simp]:
  "Lower L {} = carrier L"
  by (unfold Lower_def) simp

lemma Upper_empty [simp]:
  "Upper L {} = carrier L"
  by (unfold Upper_def) simp

theorem (in partial_order) complete_lattice_criterion1:
  assumes top_exists: "EX g. greatest L g (carrier L)"
    and inf_exists:
      "!!A. [| A \<subseteq> carrier L; A ~= {} |] ==> EX i. greatest L i (Lower L A)"
  shows "complete_lattice L"
proof (rule complete_latticeI)
  from top_exists obtain top where top: "greatest L top (carrier L)" ..
  fix A
  assume L: "A \<subseteq> carrier L"
  let ?B = "Upper L A"
  from L top have "top \<in> ?B" by (fast intro!: Upper_memI intro: greatest_le)
  then have B_non_empty: "?B ~= {}" by fast
  have B_L: "?B \<subseteq> carrier L" by simp
  from inf_exists [OF B_L B_non_empty]
  obtain b where b_inf_B: "greatest L b (Lower L ?B)" ..
  have "least L b (Upper L A)"
apply (rule least_UpperI)
   apply (rule greatest_le [where A = "Lower L ?B"])
    apply (rule b_inf_B)
   apply (rule Lower_memI)
    apply (erule UpperD)
     apply assumption
    apply (rule L)
   apply (fast intro: L [THEN subsetD])
  apply (erule greatest_Lower_above [OF b_inf_B])
  apply simp
 apply (rule L)
apply (rule greatest_carrier [OF b_inf_B]) (* rename rule: _closed *)
done
  then show "EX s. least L s (Upper L A)" ..
next
  fix A
  assume L: "A \<subseteq> carrier L"
  show "EX i. greatest L i (Lower L A)"
  proof (cases "A = {}")
    case True then show ?thesis
      by (simp add: top_exists)
  next
    case False with L show ?thesis
      by (rule inf_exists)
  qed
qed

(* TODO: prove dual version *)

subsection {* Examples *}

subsubsection {* Powerset of a set is a complete lattice *}

theorem powerset_is_complete_lattice:
  "complete_lattice (| carrier = Pow A, le = op \<subseteq> |)"
  (is "complete_lattice ?L")
proof (rule partial_order.complete_latticeI)
  show "partial_order ?L"
    by (rule partial_order.intro) auto
next
  fix B
  assume "B \<subseteq> carrier ?L"
  then have "least ?L (\<Union> B) (Upper ?L B)"
    by (fastsimp intro!: least_UpperI simp: Upper_def)
  then show "EX s. least ?L s (Upper ?L B)" ..
next
  fix B
  assume "B \<subseteq> carrier ?L"
  then have "greatest ?L (\<Inter> B \<inter> A) (Lower ?L B)"
    txt {* @{term "\<Inter> B"} is not the infimum of @{term B}:
      @{term "\<Inter> {} = UNIV"} which is in general bigger than @{term "A"}! *}
    by (fastsimp intro!: greatest_LowerI simp: Lower_def)
  then show "EX i. greatest ?L i (Lower ?L B)" ..
qed

text {* An other example, that of the lattice of subgroups of a group,
  can be found in Group theory (Section~\ref{sec:subgroup-lattice}). *}

end
