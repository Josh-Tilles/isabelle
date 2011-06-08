(*  Title:      HOL/Multivariate_Analysis/Extended_Real_Limits.thy
    Author:     Johannes Hölzl, TU München
    Author:     Robert Himmelmann, TU München
    Author:     Armin Heller, TU München
    Author:     Bogdan Grechuk, University of Edinburgh
*)

header {* Limits on the Extended real number line *}

theory Extended_Real_Limits
  imports Topology_Euclidean_Space "~~/src/HOL/Library/Extended_Reals"
begin

lemma continuous_on_extreal[intro, simp]: "continuous_on A extreal"
  unfolding continuous_on_topological open_extreal_def by auto

lemma continuous_at_extreal[intro, simp]: "continuous (at x) extreal"
  using continuous_on_eq_continuous_at[of UNIV] by auto

lemma continuous_within_extreal[intro, simp]: "x \<in> A \<Longrightarrow> continuous (at x within A) extreal"
  using continuous_on_eq_continuous_within[of A] by auto

lemma extreal_open_uminus:
  fixes S :: "extreal set"
  assumes "open S"
  shows "open (uminus ` S)"
  unfolding open_extreal_def
proof (intro conjI impI)
  obtain x y where S: "open (extreal -` S)"
    "\<infinity> \<in> S \<Longrightarrow> {extreal x<..} \<subseteq> S" "-\<infinity> \<in> S \<Longrightarrow> {..< extreal y} \<subseteq> S"
    using `open S` unfolding open_extreal_def by auto
  have "extreal -` uminus ` S = uminus ` (extreal -` S)"
  proof safe
    fix x y assume "extreal x = - y" "y \<in> S"
    then show "x \<in> uminus ` extreal -` S" by (cases y) auto
  next
    fix x assume "extreal x \<in> S"
    then show "- x \<in> extreal -` uminus ` S"
      by (auto intro: image_eqI[of _ _ "extreal x"])
  qed
  then show "open (extreal -` uminus ` S)"
    using S by (auto intro: open_negations)
  { assume "\<infinity> \<in> uminus ` S"
    then have "-\<infinity> \<in> S" by (metis image_iff extreal_uminus_uminus)
    then have "uminus ` {..<extreal y} \<subseteq> uminus ` S" using S by (intro image_mono) auto
    then show "\<exists>x. {extreal x<..} \<subseteq> uminus ` S" using extreal_uminus_lessThan by auto }
  { assume "-\<infinity> \<in> uminus ` S"
    then have "\<infinity> : S" by (metis image_iff extreal_uminus_uminus)
    then have "uminus ` {extreal x<..} <= uminus ` S" using S by (intro image_mono) auto
    then show "\<exists>y. {..<extreal y} <= uminus ` S" using extreal_uminus_greaterThan by auto }
qed

lemma extreal_uminus_complement:
  fixes S :: "extreal set"
  shows "uminus ` (- S) = - uminus ` S"
  by (auto intro!: bij_image_Compl_eq surjI[of _ uminus] simp: bij_betw_def)

lemma extreal_closed_uminus:
  fixes S :: "extreal set"
  assumes "closed S"
  shows "closed (uminus ` S)"
using assms unfolding closed_def
using extreal_open_uminus[of "- S"] extreal_uminus_complement by auto

lemma not_open_extreal_singleton:
  "\<not> (open {a :: extreal})"
proof(rule ccontr)
  assume "\<not> \<not> open {a}" hence a: "open {a}" by auto
  show False
  proof (cases a)
    case MInf
    then obtain y where "{..<extreal y} <= {a}" using a open_MInfty2[of "{a}"] by auto
    hence "extreal(y - 1):{a}" apply (subst subsetD[of "{..<extreal y}"]) by auto
    then show False using `a=(-\<infinity>)` by auto
  next
    case PInf
    then obtain y where "{extreal y<..} <= {a}" using a open_PInfty2[of "{a}"] by auto
    hence "extreal(y+1):{a}" apply (subst subsetD[of "{extreal y<..}"]) by auto
    then show False using `a=\<infinity>` by auto
  next
    case (real r) then have fin: "\<bar>a\<bar> \<noteq> \<infinity>" by simp
    from extreal_open_cont_interval[OF a singletonI this] guess e . note e = this
    then obtain b where b_def: "a<b & b<a+e"
      using fin extreal_between extreal_dense[of a "a+e"] by auto
    then have "b: {a-e <..< a+e}" using fin extreal_between[of a e] e by auto
    then show False using b_def e by auto
  qed
qed

lemma extreal_closed_contains_Inf:
  fixes S :: "extreal set"
  assumes "closed S" "S ~= {}"
  shows "Inf S : S"
proof(rule ccontr)
  assume "Inf S \<notin> S" hence a: "open (-S)" "Inf S:(- S)" using assms by auto
  show False
  proof (cases "Inf S")
    case MInf hence "(-\<infinity>) : - S" using a by auto
    then obtain y where "{..<extreal y} <= (-S)" using a open_MInfty2[of "- S"] by auto
    hence "extreal y <= Inf S" by (metis Compl_anti_mono Compl_lessThan atLeast_iff
      complete_lattice_class.Inf_greatest double_complement set_rev_mp)
    then show False using MInf by auto
  next
    case PInf then have "S={\<infinity>}" by (metis Inf_eq_PInfty assms(2))
    then show False by (metis `Inf S ~: S` insert_code mem_def PInf)
  next
    case (real r) then have fin: "\<bar>Inf S\<bar> \<noteq> \<infinity>" by simp
    from extreal_open_cont_interval[OF a this] guess e . note e = this
    { fix x assume "x:S" hence "x>=Inf S" by (rule complete_lattice_class.Inf_lower)
      hence *: "x>Inf S-e" using e by (metis fin extreal_between(1) order_less_le_trans)
      { assume "x<Inf S+e" hence "x:{Inf S-e <..< Inf S+e}" using * by auto
        hence False using e `x:S` by auto
      } hence "x>=Inf S+e" by (metis linorder_le_less_linear)
    } hence "Inf S + e <= Inf S" by (metis le_Inf_iff)
    then show False using real e by (cases e) auto
  qed
qed

lemma extreal_closed_contains_Sup:
  fixes S :: "extreal set"
  assumes "closed S" "S ~= {}"
  shows "Sup S : S"
proof-
  have "closed (uminus ` S)" by (metis assms(1) extreal_closed_uminus)
  hence "Inf (uminus ` S) : uminus ` S" using assms extreal_closed_contains_Inf[of "uminus ` S"] by auto
  hence "- Sup S : uminus ` S" using extreal_Sup_uminus_image_eq[of "uminus ` S"] by (auto simp: image_image)
  thus ?thesis by (metis imageI extreal_uminus_uminus extreal_minus_minus_image)
qed

lemma extreal_open_closed_aux:
  fixes S :: "extreal set"
  assumes "open S" "closed S"
  assumes S: "(-\<infinity>) ~: S"
  shows "S = {}"
proof(rule ccontr)
  assume "S ~= {}"
  hence *: "(Inf S):S" by (metis assms(2) extreal_closed_contains_Inf)
  { assume "Inf S=(-\<infinity>)" hence False using * assms(3) by auto }
  moreover
  { assume "Inf S=\<infinity>" hence "S={\<infinity>}" by (metis Inf_eq_PInfty `S ~= {}`)
    hence False by (metis assms(1) not_open_extreal_singleton) }
  moreover
  { assume fin: "\<bar>Inf S\<bar> \<noteq> \<infinity>"
    from extreal_open_cont_interval[OF assms(1) * fin] guess e . note e = this
    then obtain b where b_def: "Inf S-e<b & b<Inf S"
      using fin extreal_between[of "Inf S" e] extreal_dense[of "Inf S-e"] by auto
    hence "b: {Inf S-e <..< Inf S+e}" using e fin extreal_between[of "Inf S" e] by auto
    hence "b:S" using e by auto
    hence False using b_def by (metis complete_lattice_class.Inf_lower leD)
  } ultimately show False by auto
qed

lemma extreal_open_closed:
  fixes S :: "extreal set"
  shows "(open S & closed S) <-> (S = {} | S = UNIV)"
proof-
{ assume lhs: "open S & closed S"
  { assume "(-\<infinity>) ~: S" hence "S={}" using lhs extreal_open_closed_aux by auto }
  moreover
  { assume "(-\<infinity>) : S" hence "(- S)={}" using lhs extreal_open_closed_aux[of "-S"] by auto }
  ultimately have "S = {} | S = UNIV" by auto
} thus ?thesis by auto
qed

lemma extreal_open_affinity_pos:
  assumes "open S" and m: "m \<noteq> \<infinity>" "0 < m" and t: "\<bar>t\<bar> \<noteq> \<infinity>"
  shows "open ((\<lambda>x. m * x + t) ` S)"
proof -
  obtain r where r[simp]: "m = extreal r" using m by (cases m) auto
  obtain p where p[simp]: "t = extreal p" using t by auto
  have "r \<noteq> 0" "0 < r" and m': "m \<noteq> \<infinity>" "m \<noteq> -\<infinity>" "m \<noteq> 0" using m by auto
  from `open S`[THEN extreal_openE] guess l u . note T = this
  let ?f = "(\<lambda>x. m * x + t)"
  show ?thesis unfolding open_extreal_def
  proof (intro conjI impI exI subsetI)
    have "extreal -` ?f ` S = (\<lambda>x. r * x + p) ` (extreal -` S)"
    proof safe
      fix x y assume "extreal y = m * x + t" "x \<in> S"
      then show "y \<in> (\<lambda>x. r * x + p) ` extreal -` S"
        using `r \<noteq> 0` by (cases x) (auto intro!: image_eqI[of _ _ "real x"] split: split_if_asm)
    qed force
    then show "open (extreal -` ?f ` S)"
      using open_affinity[OF T(1) `r \<noteq> 0`] by (auto simp: ac_simps)
  next
    assume "\<infinity> \<in> ?f`S" with `0 < r` have "\<infinity> \<in> S" by auto
    fix x assume "x \<in> {extreal (r * l + p)<..}"
    then have [simp]: "extreal (r * l + p) < x" by auto
    show "x \<in> ?f`S"
    proof (rule image_eqI)
      show "x = m * ((x - t) / m) + t"
        using m t by (cases rule: extreal3_cases[of m x t]) auto
      have "extreal l < (x - t)/m"
        using m t by (simp add: extreal_less_divide_pos extreal_less_minus)
      then show "(x - t)/m \<in> S" using T(2)[OF `\<infinity> \<in> S`] by auto
    qed
  next
    assume "-\<infinity> \<in> ?f`S" with `0 < r` have "-\<infinity> \<in> S" by auto
    fix x assume "x \<in> {..<extreal (r * u + p)}"
    then have [simp]: "x < extreal (r * u + p)" by auto
    show "x \<in> ?f`S"
    proof (rule image_eqI)
      show "x = m * ((x - t) / m) + t"
        using m t by (cases rule: extreal3_cases[of m x t]) auto
      have "(x - t)/m < extreal u"
        using m t by (simp add: extreal_divide_less_pos extreal_minus_less)
      then show "(x - t)/m \<in> S" using T(3)[OF `-\<infinity> \<in> S`] by auto
    qed
  qed
qed

lemma extreal_open_affinity:
  assumes "open S" and m: "\<bar>m\<bar> \<noteq> \<infinity>" "m \<noteq> 0" and t: "\<bar>t\<bar> \<noteq> \<infinity>"
  shows "open ((\<lambda>x. m * x + t) ` S)"
proof cases
  assume "0 < m" then show ?thesis
    using extreal_open_affinity_pos[OF `open S` _ _ t, of m] m by auto
next
  assume "\<not> 0 < m" then
  have "0 < -m" using `m \<noteq> 0` by (cases m) auto
  then have m: "-m \<noteq> \<infinity>" "0 < -m" using `\<bar>m\<bar> \<noteq> \<infinity>`
    by (auto simp: extreal_uminus_eq_reorder)
  from extreal_open_affinity_pos[OF extreal_open_uminus[OF `open S`] m t]
  show ?thesis unfolding image_image by simp
qed

lemma extreal_lim_mult:
  fixes X :: "'a \<Rightarrow> extreal"
  assumes lim: "(X ---> L) net" and a: "\<bar>a\<bar> \<noteq> \<infinity>"
  shows "((\<lambda>i. a * X i) ---> a * L) net"
proof cases
  assume "a \<noteq> 0"
  show ?thesis
  proof (rule topological_tendstoI)
    fix S assume "open S" "a * L \<in> S"
    have "a * L / a = L"
      using `a \<noteq> 0` a by (cases rule: extreal2_cases[of a L]) auto
    then have L: "L \<in> ((\<lambda>x. x / a) ` S)"
      using `a * L \<in> S` by (force simp: image_iff)
    moreover have "open ((\<lambda>x. x / a) ` S)"
      using extreal_open_affinity[OF `open S`, of "inverse a" 0] `a \<noteq> 0` a
      by (auto simp: extreal_divide_eq extreal_inverse_eq_0 divide_extreal_def ac_simps)
    note * = lim[THEN topological_tendstoD, OF this L]
    { fix x from a `a \<noteq> 0` have "a * (x / a) = x"
        by (cases rule: extreal2_cases[of a x]) auto }
    note this[simp]
    show "eventually (\<lambda>x. a * X x \<in> S) net"
      by (rule eventually_mono[OF _ *]) auto
  qed
qed auto

lemma extreal_lim_uminus:
  fixes X :: "'a \<Rightarrow> extreal" shows "((\<lambda>i. - X i) ---> -L) net \<longleftrightarrow> (X ---> L) net"
  using extreal_lim_mult[of X L net "extreal (-1)"]
        extreal_lim_mult[of "(\<lambda>i. - X i)" "-L" net "extreal (-1)"]
  by (auto simp add: algebra_simps)

lemma Lim_bounded2_extreal:
  assumes lim:"f ----> (l :: extreal)"
  and ge: "ALL n>=N. f n >= C"
  shows "l>=C"
proof-
def g == "(%i. -(f i))"
{ fix n assume "n>=N" hence "g n <= -C" using assms extreal_minus_le_minus g_def by auto }
hence "ALL n>=N. g n <= -C" by auto
moreover have limg: "g ----> (-l)" using g_def extreal_lim_uminus lim by auto
ultimately have "-l <= -C" using Lim_bounded_extreal[of g "-l" _ "-C"] by auto
from this show ?thesis using extreal_minus_le_minus by auto
qed


lemma extreal_open_atLeast: "open {x..} \<longleftrightarrow> x = -\<infinity>"
proof
  assume "x = -\<infinity>" then have "{x..} = UNIV" by auto
  then show "open {x..}" by auto
next
  assume "open {x..}"
  then have "open {x..} \<and> closed {x..}" by auto
  then have "{x..} = UNIV" unfolding extreal_open_closed by auto
  then show "x = -\<infinity>" by (simp add: bot_extreal_def atLeast_eq_UNIV_iff)
qed

lemma extreal_open_mono_set:
  fixes S :: "extreal set"
  defines "a \<equiv> Inf S"
  shows "(open S \<and> mono S) \<longleftrightarrow> (S = UNIV \<or> S = {a <..})"
  by (metis Inf_UNIV a_def atLeast_eq_UNIV_iff extreal_open_atLeast
            extreal_open_closed mono_set_iff open_extreal_greaterThan)

lemma extreal_closed_mono_set:
  fixes S :: "extreal set"
  shows "(closed S \<and> mono S) \<longleftrightarrow> (S = {} \<or> S = {Inf S ..})"
  by (metis Inf_UNIV atLeast_eq_UNIV_iff closed_extreal_atLeast
            extreal_open_closed mono_empty mono_set_iff open_extreal_greaterThan)

lemma extreal_Liminf_Sup_monoset:
  fixes f :: "'a => extreal"
  shows "Liminf net f = Sup {l. \<forall>S. open S \<longrightarrow> mono S \<longrightarrow> l \<in> S \<longrightarrow> eventually (\<lambda>x. f x \<in> S) net}"
  unfolding Liminf_Sup
proof (intro arg_cong[where f="\<lambda>P. Sup (Collect P)"] ext iffI allI impI)
  fix l S assume ev: "\<forall>y<l. eventually (\<lambda>x. y < f x) net" and "open S" "mono S" "l \<in> S"
  then have "S = UNIV \<or> S = {Inf S <..}"
    using extreal_open_mono_set[of S] by auto
  then show "eventually (\<lambda>x. f x \<in> S) net"
  proof
    assume S: "S = {Inf S<..}"
    then have "Inf S < l" using `l \<in> S` by auto
    then have "eventually (\<lambda>x. Inf S < f x) net" using ev by auto
    then show "eventually (\<lambda>x. f x \<in> S) net"  by (subst S) auto
  qed auto
next
  fix l y assume S: "\<forall>S. open S \<longrightarrow> mono S \<longrightarrow> l \<in> S \<longrightarrow> eventually  (\<lambda>x. f x \<in> S) net" "y < l"
  have "eventually  (\<lambda>x. f x \<in> {y <..}) net"
    using `y < l` by (intro S[rule_format]) auto
  then show "eventually (\<lambda>x. y < f x) net" by auto
qed

lemma extreal_Limsup_Inf_monoset:
  fixes f :: "'a => extreal"
  shows "Limsup net f = Inf {l. \<forall>S. open S \<longrightarrow> mono (uminus ` S) \<longrightarrow> l \<in> S \<longrightarrow> eventually (\<lambda>x. f x \<in> S) net}"
  unfolding Limsup_Inf
proof (intro arg_cong[where f="\<lambda>P. Inf (Collect P)"] ext iffI allI impI)
  fix l S assume ev: "\<forall>y>l. eventually (\<lambda>x. f x < y) net" and "open S" "mono (uminus`S)" "l \<in> S"
  then have "open (uminus`S) \<and> mono (uminus`S)" by (simp add: extreal_open_uminus)
  then have "S = UNIV \<or> S = {..< Sup S}"
    unfolding extreal_open_mono_set extreal_Inf_uminus_image_eq extreal_image_uminus_shift by simp
  then show "eventually (\<lambda>x. f x \<in> S) net"
  proof
    assume S: "S = {..< Sup S}"
    then have "l < Sup S" using `l \<in> S` by auto
    then have "eventually (\<lambda>x. f x < Sup S) net" using ev by auto
    then show "eventually (\<lambda>x. f x \<in> S) net"  by (subst S) auto
  qed auto
next
  fix l y assume S: "\<forall>S. open S \<longrightarrow> mono (uminus`S) \<longrightarrow> l \<in> S \<longrightarrow> eventually  (\<lambda>x. f x \<in> S) net" "l < y"
  have "eventually  (\<lambda>x. f x \<in> {..< y}) net"
    using `l < y` by (intro S[rule_format]) auto
  then show "eventually (\<lambda>x. f x < y) net" by auto
qed


lemma open_uminus_iff: "open (uminus ` S) \<longleftrightarrow> open (S::extreal set)"
  using extreal_open_uminus[of S] extreal_open_uminus[of "uminus`S"] by auto

lemma extreal_Limsup_uminus:
  fixes f :: "'a => extreal"
  shows "Limsup net (\<lambda>x. - (f x)) = -(Liminf net f)"
proof -
  { fix P l have "(\<exists>x. (l::extreal) = -x \<and> P x) \<longleftrightarrow> P (-l)" by (auto intro!: exI[of _ "-l"]) }
  note Ex_cancel = this
  { fix P :: "extreal set \<Rightarrow> bool" have "(\<forall>S. P S) \<longleftrightarrow> (\<forall>S. P (uminus`S))"
      apply auto by (erule_tac x="uminus`S" in allE) (auto simp: image_image) }
  note add_uminus_image = this
  { fix x S have "(x::extreal) \<in> uminus`S \<longleftrightarrow> -x\<in>S" by (auto intro!: image_eqI[of _ _ "-x"]) }
  note remove_uminus_image = this
  show ?thesis
    unfolding extreal_Limsup_Inf_monoset extreal_Liminf_Sup_monoset
    unfolding extreal_Inf_uminus_image_eq[symmetric] image_Collect Ex_cancel
    by (subst add_uminus_image) (simp add: open_uminus_iff remove_uminus_image)
qed

lemma extreal_Liminf_uminus:
  fixes f :: "'a => extreal"
  shows "Liminf net (\<lambda>x. - (f x)) = -(Limsup net f)"
  using extreal_Limsup_uminus[of _ "(\<lambda>x. - (f x))"] by auto

lemma extreal_Lim_uminus:
  fixes f :: "'a \<Rightarrow> extreal" shows "(f ---> f0) net \<longleftrightarrow> ((\<lambda>x. - f x) ---> - f0) net"
  using
    extreal_lim_mult[of f f0 net "- 1"]
    extreal_lim_mult[of "\<lambda>x. - (f x)" "-f0" net "- 1"]
  by (auto simp: extreal_uminus_reorder)

lemma lim_imp_Limsup:
  fixes f :: "'a => extreal"
  assumes "\<not> trivial_limit net"
  assumes lim: "(f ---> f0) net"
  shows "Limsup net f = f0"
  using extreal_Lim_uminus[of f f0] lim_imp_Liminf[of net "(%x. -(f x))" "-f0"]
     extreal_Liminf_uminus[of net f] assms by simp

lemma Liminf_PInfty:
  fixes f :: "'a \<Rightarrow> extreal"
  assumes "\<not> trivial_limit net"
  shows "(f ---> \<infinity>) net \<longleftrightarrow> Liminf net f = \<infinity>"
proof (intro lim_imp_Liminf iffI assms)
  assume rhs: "Liminf net f = \<infinity>"
  { fix S assume "open S & \<infinity> : S"
    then obtain m where "{extreal m<..} <= S" using open_PInfty2 by auto
    moreover have "eventually (\<lambda>x. f x \<in> {extreal m<..}) net"
      using rhs unfolding Liminf_Sup top_extreal_def[symmetric] Sup_eq_top_iff
      by (auto elim!: allE[where x="extreal m"] simp: top_extreal_def)
    ultimately have "eventually (%x. f x : S) net" apply (subst eventually_mono) by auto
  } then show "(f ---> \<infinity>) net" unfolding tendsto_def by auto
qed

lemma Limsup_MInfty:
  fixes f :: "'a \<Rightarrow> extreal"
  assumes "\<not> trivial_limit net"
  shows "(f ---> -\<infinity>) net \<longleftrightarrow> Limsup net f = -\<infinity>"
  using assms extreal_Lim_uminus[of f "-\<infinity>"] Liminf_PInfty[of _ "\<lambda>x. - (f x)"]
        extreal_Liminf_uminus[of _ f] by (auto simp: extreal_uminus_eq_reorder)

lemma extreal_Liminf_eq_Limsup:
  fixes f :: "'a \<Rightarrow> extreal"
  assumes ntriv: "\<not> trivial_limit net"
  assumes lim: "Liminf net f = f0" "Limsup net f = f0"
  shows "(f ---> f0) net"
proof (cases f0)
  case PInf then show ?thesis using Liminf_PInfty[OF ntriv] lim by auto
next
  case MInf then show ?thesis using Limsup_MInfty[OF ntriv] lim by auto
next
  case (real r)
  show "(f ---> f0) net"
  proof (rule topological_tendstoI)
    fix S assume "open S""f0 \<in> S"
    then obtain a b where "a < Liminf net f" "Limsup net f < b" "{a<..<b} \<subseteq> S"
      using extreal_open_cont_interval2[of S f0] real lim by auto
    then have "eventually (\<lambda>x. f x \<in> {a<..<b}) net"
      unfolding Liminf_Sup Limsup_Inf less_Sup_iff Inf_less_iff
      by (auto intro!: eventually_conj simp add: greaterThanLessThan_iff)
    with `{a<..<b} \<subseteq> S` show "eventually (%x. f x : S) net"
      by (rule_tac eventually_mono) auto
  qed
qed

lemma extreal_Liminf_eq_Limsup_iff:
  fixes f :: "'a \<Rightarrow> extreal"
  assumes "\<not> trivial_limit net"
  shows "(f ---> f0) net \<longleftrightarrow> Liminf net f = f0 \<and> Limsup net f = f0"
  by (metis assms extreal_Liminf_eq_Limsup lim_imp_Liminf lim_imp_Limsup)

lemma limsup_INFI_SUPR:
  fixes f :: "nat \<Rightarrow> extreal"
  shows "limsup f = (INF n. SUP m:{n..}. f m)"
  using extreal_Limsup_uminus[of sequentially "\<lambda>x. - f x"]
  by (simp add: liminf_SUPR_INFI extreal_INFI_uminus extreal_SUPR_uminus)

lemma liminf_PInfty:
  fixes X :: "nat => extreal"
  shows "X ----> \<infinity> <-> liminf X = \<infinity>"
by (metis Liminf_PInfty trivial_limit_sequentially)

lemma limsup_MInfty:
  fixes X :: "nat => extreal"
  shows "X ----> (-\<infinity>) <-> limsup X = (-\<infinity>)"
by (metis Limsup_MInfty trivial_limit_sequentially)

lemma extreal_lim_mono:
  fixes X Y :: "nat => extreal"
  assumes "\<And>n. N \<le> n \<Longrightarrow> X n <= Y n"
  assumes "X ----> x" "Y ----> y"
  shows "x <= y"
  by (metis extreal_Liminf_eq_Limsup_iff[OF trivial_limit_sequentially] assms liminf_mono)

lemma incseq_le_extreal:
  fixes X :: "nat \<Rightarrow> extreal"
  assumes inc: "incseq X" and lim: "X ----> L"
  shows "X N \<le> L"
  using inc
  by (intro extreal_lim_mono[of N, OF _ Lim_const lim]) (simp add: incseq_def)

lemma decseq_ge_extreal: assumes dec: "decseq X"
  and lim: "X ----> (L::extreal)" shows "X N >= L"
  using dec
  by (intro extreal_lim_mono[of N, OF _ lim Lim_const]) (simp add: decseq_def)

lemma liminf_bounded_open:
  fixes x :: "nat \<Rightarrow> extreal"
  shows "x0 \<le> liminf x \<longleftrightarrow> (\<forall>S. open S \<longrightarrow> mono S \<longrightarrow> x0 \<in> S \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. x n \<in> S))" 
  (is "_ \<longleftrightarrow> ?P x0")
proof
  assume "?P x0" then show "x0 \<le> liminf x"
    unfolding extreal_Liminf_Sup_monoset eventually_sequentially
    by (intro complete_lattice_class.Sup_upper) auto
next
  assume "x0 \<le> liminf x"
  { fix S :: "extreal set" assume om: "open S & mono S & x0:S"
    { assume "S = UNIV" hence "EX N. (ALL n>=N. x n : S)" by auto }
    moreover
    { assume "~(S=UNIV)"
      then obtain B where B_def: "S = {B<..}" using om extreal_open_mono_set by auto
      hence "B<x0" using om by auto
      hence "EX N. ALL n>=N. x n : S" unfolding B_def using `x0 \<le> liminf x` liminf_bounded_iff by auto
    } ultimately have "EX N. (ALL n>=N. x n : S)" by auto
  } then show "?P x0" by auto
qed

lemma limsup_subseq_mono:
  fixes X :: "nat \<Rightarrow> extreal"
  assumes "subseq r"
  shows "limsup (X \<circ> r) \<le> limsup X"
proof-
  have "(\<lambda>n. - X n) \<circ> r = (\<lambda>n. - (X \<circ> r) n)" by (simp add: fun_eq_iff)
  then have "- limsup X \<le> - limsup (X \<circ> r)"
     using liminf_subseq_mono[of r "(%n. - X n)"]
       extreal_Liminf_uminus[of sequentially X]
       extreal_Liminf_uminus[of sequentially "X o r"] assms by auto
  then show ?thesis by auto
qed

lemma bounded_abs:
  assumes "(a::real)<=x" "x<=b"
  shows "abs x <= max (abs a) (abs b)"
by (metis abs_less_iff assms leI le_max_iff_disj less_eq_real_def less_le_not_le less_minus_iff minus_minus)

lemma bounded_increasing_convergent2: fixes f::"nat => real"
  assumes "ALL n. f n <= B"  "ALL n m. n>=m --> f n >= f m"
  shows "EX l. (f ---> l) sequentially"
proof-
def N == "max (abs (f 0)) (abs B)"
{ fix n have "abs (f n) <= N" unfolding N_def apply (subst bounded_abs) using assms by auto }
hence "bounded {f n| n::nat. True}" unfolding bounded_real by auto
from this show ?thesis apply(rule Topology_Euclidean_Space.bounded_increasing_convergent)
   using assms by auto
qed
lemma lim_extreal_increasing: assumes "\<And>n m. n >= m \<Longrightarrow> f n >= f m"
  obtains l where "f ----> (l::extreal)"
proof(cases "f = (\<lambda>x. - \<infinity>)")
  case True then show thesis using Lim_const[of "- \<infinity>" sequentially] by (intro that[of "-\<infinity>"]) auto
next
  case False
  from this obtain N where N_def: "f N > (-\<infinity>)" by (auto simp: fun_eq_iff)
  have "ALL n>=N. f n >= f N" using assms by auto
  hence minf: "ALL n>=N. f n > (-\<infinity>)" using N_def by auto
  def Y == "(%n. (if n>=N then f n else f N))"
  hence incy: "!!n m. n>=m ==> Y n >= Y m" using assms by auto
  from minf have minfy: "ALL n. Y n ~= (-\<infinity>)" using Y_def by auto
  show thesis
  proof(cases "EX B. ALL n. f n < extreal B")
    case False thus thesis apply- apply(rule that[of \<infinity>]) unfolding Lim_PInfty not_ex not_all
    apply safe apply(erule_tac x=B in allE,safe) apply(rule_tac x=x in exI,safe)
    apply(rule order_trans[OF _ assms[rule_format]]) by auto
  next case True then guess B ..
    hence "ALL n. Y n < extreal B" using Y_def by auto note B = this[rule_format]
    { fix n have "Y n < \<infinity>" using B[of n] apply (subst less_le_trans) by auto
      hence "Y n ~= \<infinity> & Y n ~= (-\<infinity>)" using minfy by auto
    } hence *: "ALL n. \<bar>Y n\<bar> \<noteq> \<infinity>" by auto
    { fix n have "real (Y n) < B" proof- case goal1 thus ?case
        using B[of n] apply-apply(subst(asm) extreal_real'[THEN sym]) defer defer
        unfolding extreal_less using * by auto
      qed
    }
    hence B': "ALL n. (real (Y n) <= B)" using less_imp_le by auto
    have "EX l. (%n. real (Y n)) ----> l"
      apply(rule bounded_increasing_convergent2)
    proof safe show "!!n. real (Y n) <= B" using B' by auto
      fix n m::nat assume "n<=m"
      hence "extreal (real (Y n)) <= extreal (real (Y m))"
        using incy[rule_format,of n m] apply(subst extreal_real)+
        using *[rule_format, of n] *[rule_format, of m] by auto
      thus "real (Y n) <= real (Y m)" by auto
    qed then guess l .. note l=this
    have "Y ----> extreal l" using l apply-apply(subst(asm) lim_extreal[THEN sym])
    unfolding extreal_real using * by auto
    thus thesis apply-apply(rule that[of "extreal l"])
       apply (subst tail_same_limit[of Y _ N]) using Y_def by auto
  qed
qed

lemma lim_extreal_decreasing: assumes "\<And>n m. n >= m \<Longrightarrow> f n <= f m"
  obtains l where "f ----> (l::extreal)"
proof -
  from lim_extreal_increasing[of "\<lambda>x. - f x"] assms
  obtain l where "(\<lambda>x. - f x) ----> l" by auto
  from extreal_lim_mult[OF this, of "- 1"] show thesis
    by (intro that[of "-l"]) (simp add: extreal_uminus_eq_reorder)
qed

lemma compact_extreal:
  fixes X :: "nat \<Rightarrow> extreal"
  shows "\<exists>l r. subseq r \<and> (X \<circ> r) ----> l"
proof -
  obtain r where "subseq r" and mono: "monoseq (X \<circ> r)"
    using seq_monosub[of X] unfolding comp_def by auto
  then have "(\<forall>n m. m \<le> n \<longrightarrow> (X \<circ> r) m \<le> (X \<circ> r) n) \<or> (\<forall>n m. m \<le> n \<longrightarrow> (X \<circ> r) n \<le> (X \<circ> r) m)"
    by (auto simp add: monoseq_def)
  then obtain l where "(X\<circ>r) ----> l"
     using lim_extreal_increasing[of "X \<circ> r"] lim_extreal_decreasing[of "X \<circ> r"] by auto
  then show ?thesis using `subseq r` by auto
qed

lemma extreal_Sup_lim:
  assumes "\<And>n. b n \<in> s" "b ----> (a::extreal)"
  shows "a \<le> Sup s"
by (metis Lim_bounded_extreal assms complete_lattice_class.Sup_upper)

lemma extreal_Inf_lim:
  assumes "\<And>n. b n \<in> s" "b ----> (a::extreal)"
  shows "Inf s \<le> a"
by (metis Lim_bounded2_extreal assms complete_lattice_class.Inf_lower)

lemma SUP_Lim_extreal:
  fixes X :: "nat \<Rightarrow> extreal" assumes "incseq X" "X ----> l" shows "(SUP n. X n) = l"
proof (rule extreal_SUPI)
  fix n from assms show "X n \<le> l"
    by (intro incseq_le_extreal) (simp add: incseq_def)
next
  fix y assume "\<And>n. n \<in> UNIV \<Longrightarrow> X n \<le> y"
  with extreal_Sup_lim[OF _ `X ----> l`, of "{..y}"]
  show "l \<le> y" by auto
qed

lemma LIMSEQ_extreal_SUPR:
  fixes X :: "nat \<Rightarrow> extreal" assumes "incseq X" shows "X ----> (SUP n. X n)"
proof (rule lim_extreal_increasing)
  fix n m :: nat assume "m \<le> n" then show "X m \<le> X n"
    using `incseq X` by (simp add: incseq_def)
next
  fix l assume "X ----> l"
  with SUP_Lim_extreal[of X, OF assms this] show ?thesis by simp
qed

lemma INF_Lim_extreal: "decseq X \<Longrightarrow> X ----> l \<Longrightarrow> (INF n. X n) = (l::extreal)"
  using SUP_Lim_extreal[of "\<lambda>i. - X i" "- l"]
  by (simp add: extreal_SUPR_uminus extreal_lim_uminus)

lemma LIMSEQ_extreal_INFI: "decseq X \<Longrightarrow> X ----> (INF n. X n :: extreal)"
  using LIMSEQ_extreal_SUPR[of "\<lambda>i. - X i"]
  by (simp add: extreal_SUPR_uminus extreal_lim_uminus)

lemma SUP_eq_LIMSEQ:
  assumes "mono f"
  shows "(SUP n. extreal (f n)) = extreal x \<longleftrightarrow> f ----> x"
proof
  have inc: "incseq (\<lambda>i. extreal (f i))"
    using `mono f` unfolding mono_def incseq_def by auto
  { assume "f ----> x"
   then have "(\<lambda>i. extreal (f i)) ----> extreal x" by auto
   from SUP_Lim_extreal[OF inc this]
   show "(SUP n. extreal (f n)) = extreal x" . }
  { assume "(SUP n. extreal (f n)) = extreal x"
    with LIMSEQ_extreal_SUPR[OF inc]
    show "f ----> x" by auto }
qed

lemma Liminf_within:
  fixes f :: "'a::metric_space => extreal"
  shows "Liminf (at x within S) f = (SUP e:{0<..}. INF y:(S Int ball x e - {x}). f y)"
proof-
let ?l="(SUP e:{0<..}. INF y:(S Int ball x e - {x}). f y)"
{ fix T assume T_def: "open T & mono T & ?l:T"
  have "EX d>0. ALL y:S. 0 < dist y x & dist y x < d --> f y : T"
  proof-
  { assume "T=UNIV" hence ?thesis by (simp add: gt_ex) }
  moreover
  { assume "~(T=UNIV)"
    then obtain B where "T={B<..}" using T_def extreal_open_mono_set[of T] by auto
    hence "B<?l" using T_def by auto
    then obtain d where d_def: "0<d & B<(INF y:(S Int ball x d - {x}). f y)"
      unfolding less_SUP_iff by auto
    { fix y assume "y:S & 0 < dist y x & dist y x < d"
      hence "y:(S Int ball x d - {x})" unfolding ball_def by (auto simp add: dist_commute)
      hence "f y:T" using d_def INF_leI[of y "S Int ball x d - {x}" f] `T={B<..}` by auto
    } hence ?thesis apply(rule_tac x="d" in exI) using d_def by auto
  } ultimately show ?thesis by auto
  qed
}
moreover
{ fix z
  assume a: "ALL T. open T --> mono T --> z : T -->
     (EX d>0. ALL y:S. 0 < dist y x & dist y x < d --> f y : T)"
  { fix B assume "B<z"
    then obtain d where d_def: "d>0 & (ALL y:S. 0 < dist y x & dist y x < d --> B < f y)"
       using a[rule_format, of "{B<..}"] mono_greaterThan by auto
    { fix y assume "y:(S Int ball x d - {x})"
      hence "y:S & 0 < dist y x & dist y x < d" unfolding ball_def apply (simp add: dist_commute)
         by (metis dist_eq_0_iff real_less_def zero_le_dist)
      hence "B <= f y" using d_def by auto
    } hence "B <= INFI (S Int ball x d - {x}) f" apply (subst le_INFI) by auto
    also have "...<=?l" apply (subst le_SUPI) using d_def by auto
    finally have "B<=?l" by auto
  } hence "z <= ?l" using extreal_le_extreal[of z "?l"] by auto
}
ultimately show ?thesis unfolding extreal_Liminf_Sup_monoset eventually_within
   apply (subst extreal_SupI[of _ "(SUP e:{0<..}. INFI (S Int ball x e - {x}) f)"]) by auto
qed

lemma Limsup_within:
  fixes f :: "'a::metric_space => extreal"
  shows "Limsup (at x within S) f = (INF e:{0<..}. SUP y:(S Int ball x e - {x}). f y)"
proof-
let ?l="(INF e:{0<..}. SUP y:(S Int ball x e - {x}). f y)"
{ fix T assume T_def: "open T & mono (uminus ` T) & ?l:T"
  have "EX d>0. ALL y:S. 0 < dist y x & dist y x < d --> f y : T"
  proof-
  { assume "T=UNIV" hence ?thesis by (simp add: gt_ex) }
  moreover
  { assume "~(T=UNIV)" hence "~(uminus ` T = UNIV)"
       by (metis Int_UNIV_right Int_absorb1 image_mono extreal_minus_minus_image subset_UNIV)
    hence "uminus ` T = {Inf (uminus ` T)<..}" using T_def extreal_open_mono_set[of "uminus ` T"]
       extreal_open_uminus[of T] by auto
    then obtain B where "T={..<B}"
      unfolding extreal_Inf_uminus_image_eq extreal_uminus_lessThan[symmetric]
      unfolding inj_image_eq_iff[OF extreal_inj_on_uminus] by simp
    hence "?l<B" using T_def by auto
    then obtain d where d_def: "0<d & (SUP y:(S Int ball x d - {x}). f y)<B"
      unfolding INF_less_iff by auto
    { fix y assume "y:S & 0 < dist y x & dist y x < d"
      hence "y:(S Int ball x d - {x})" unfolding ball_def by (auto simp add: dist_commute)
      hence "f y:T" using d_def le_SUPI[of y "S Int ball x d - {x}" f] `T={..<B}` by auto
    } hence ?thesis apply(rule_tac x="d" in exI) using d_def by auto
  } ultimately show ?thesis by auto
  qed
}
moreover
{ fix z
  assume a: "ALL T. open T --> mono (uminus ` T) --> z : T -->
     (EX d>0. ALL y:S. 0 < dist y x & dist y x < d --> f y : T)"
  { fix B assume "z<B"
    then obtain d where d_def: "d>0 & (ALL y:S. 0 < dist y x & dist y x < d --> f y<B)"
       using a[rule_format, of "{..<B}"] by auto
    { fix y assume "y:(S Int ball x d - {x})"
      hence "y:S & 0 < dist y x & dist y x < d" unfolding ball_def apply (simp add: dist_commute)
         by (metis dist_eq_0_iff real_less_def zero_le_dist)
      hence "f y <= B" using d_def by auto
    } hence "SUPR (S Int ball x d - {x}) f <= B" apply (subst SUP_leI) by auto
    moreover have "?l<=SUPR (S Int ball x d - {x}) f" apply (subst INF_leI) using d_def by auto
    ultimately have "?l<=B" by auto
  } hence "?l <= z" using extreal_ge_extreal[of z "?l"] by auto
}
ultimately show ?thesis unfolding extreal_Limsup_Inf_monoset eventually_within
   apply (subst extreal_InfI) by auto
qed


lemma Liminf_within_UNIV:
  fixes f :: "'a::metric_space => extreal"
  shows "Liminf (at x) f = Liminf (at x within UNIV) f"
by (metis within_UNIV)


lemma Liminf_at:
  fixes f :: "'a::metric_space => extreal"
  shows "Liminf (at x) f = (SUP e:{0<..}. INF y:(ball x e - {x}). f y)"
using Liminf_within[of x UNIV f] Liminf_within_UNIV[of x f] by auto


lemma Limsup_within_UNIV:
  fixes f :: "'a::metric_space => extreal"
  shows "Limsup (at x) f = Limsup (at x within UNIV) f"
by (metis within_UNIV)


lemma Limsup_at:
  fixes f :: "'a::metric_space => extreal"
  shows "Limsup (at x) f = (INF e:{0<..}. SUP y:(ball x e - {x}). f y)"
using Limsup_within[of x UNIV f] Limsup_within_UNIV[of x f] by auto

lemma Lim_within_constant:
  fixes f :: "'a::metric_space => 'b::topological_space"
  assumes "ALL y:S. f y = C"
  shows "(f ---> C) (at x within S)"
unfolding tendsto_def eventually_within
by (metis assms(1) linorder_le_less_linear n_not_Suc_n real_of_nat_le_zero_cancel_iff)

lemma Liminf_within_constant:
  fixes f :: "'a::metric_space => extreal"
  assumes "ALL y:S. f y = C"
  assumes "~trivial_limit (at x within S)"
  shows "Liminf (at x within S) f = C"
by (metis Lim_within_constant assms lim_imp_Liminf)

lemma Limsup_within_constant:
  fixes f :: "'a::metric_space => extreal"
  assumes "ALL y:S. f y = C"
  assumes "~trivial_limit (at x within S)"
  shows "Limsup (at x within S) f = C"
by (metis Lim_within_constant assms lim_imp_Limsup)

lemma islimpt_punctured:
"x islimpt S = x islimpt (S-{x})"
unfolding islimpt_def by blast


lemma islimpt_in_closure:
"(x islimpt S) = (x:closure(S-{x}))"
unfolding closure_def using islimpt_punctured by blast


lemma not_trivial_limit_within:
  "~trivial_limit (at x within S) = (x:closure(S-{x}))"
using islimpt_in_closure by (metis trivial_limit_within)


lemma not_trivial_limit_within_ball:
  "(~trivial_limit (at x within S)) = (ALL e>0. S Int ball x e - {x} ~= {})"
  (is "?lhs = ?rhs")
proof-
{ assume "?lhs"
  { fix e :: real assume "e>0"
    then obtain y where "y:(S-{x}) & dist y x < e"
       using `?lhs` not_trivial_limit_within[of x S] closure_approachable[of x "S - {x}"] by auto
    hence "y : (S Int ball x e - {x})" unfolding ball_def by (simp add: dist_commute)
    hence "S Int ball x e - {x} ~= {}" by blast
  } hence "?rhs" by auto
}
moreover
{ assume "?rhs"
  { fix e :: real assume "e>0"
    then obtain y where "y : (S Int ball x e - {x})" using `?rhs` by blast
    hence "y:(S-{x}) & dist y x < e" unfolding ball_def by (simp add: dist_commute)
    hence "EX y:(S-{x}). dist y x < e" by auto
  } hence "?lhs" using not_trivial_limit_within[of x S] closure_approachable[of x "S - {x}"] by auto
} ultimately show ?thesis by auto
qed

lemma liminf_extreal_cminus:
  fixes f :: "nat \<Rightarrow> extreal" assumes "c \<noteq> -\<infinity>"
  shows "liminf (\<lambda>x. c - f x) = c - limsup f"
proof (cases c)
  case PInf then show ?thesis by (simp add: Liminf_const)
next
  case (real r) then show ?thesis
    unfolding liminf_SUPR_INFI limsup_INFI_SUPR
    apply (subst INFI_extreal_cminus)
    apply auto
    apply (subst SUPR_extreal_cminus)
    apply auto
    done
qed (insert `c \<noteq> -\<infinity>`, simp)

subsubsection {* Continuity *}

lemma continuous_imp_tendsto:
  assumes "continuous (at x0) f"
  assumes "x ----> x0"
  shows "(f o x) ----> (f x0)"
proof-
{ fix S assume "open S & (f x0):S"
  from this obtain T where T_def: "open T & x0 : T & (ALL x:T. f x : S)"
     using assms continuous_at_open by metis
  hence "(EX N. ALL n>=N. x n : T)" using assms tendsto_explicit T_def by auto
  hence "(EX N. ALL n>=N. f(x n) : S)" using T_def by auto
} from this show ?thesis using tendsto_explicit[of "f o x" "f x0"] by auto
qed


lemma continuous_at_sequentially2:
fixes f :: "'a::metric_space => 'b:: topological_space"
shows "continuous (at x0) f <-> (ALL x. (x ----> x0) --> (f o x) ----> (f x0))"
proof-
{ assume "~(continuous (at x0) f)"
  from this obtain T where T_def:
     "open T & f x0 : T & (ALL S. (open S & x0 : S) --> (EX x':S. f x' ~: T))"
     using continuous_at_open[of x0 f] by metis
  def X == "{x'. f x' ~: T}" hence "x0 islimpt X" unfolding islimpt_def using T_def by auto
  from this obtain x where x_def: "(ALL n. x n : X) & x ----> x0"
     using islimpt_sequential[of x0 X] by auto
  hence "~(f o x) ----> (f x0)" unfolding tendsto_explicit using X_def T_def by auto
  hence "EX x. x ----> x0 & (~(f o x) ----> (f x0))" using x_def by auto
}
from this show ?thesis using continuous_imp_tendsto by auto
qed

lemma continuous_at_of_extreal:
  fixes x0 :: extreal
  assumes "\<bar>x0\<bar> \<noteq> \<infinity>"
  shows "continuous (at x0) real"
proof-
{ fix T assume T_def: "open T & real x0 : T"
  def S == "extreal ` T"
  hence "extreal (real x0) : S" using T_def by auto
  hence "x0 : S" using assms extreal_real by auto
  moreover have "open S" using open_extreal S_def T_def by auto
  moreover have "ALL y:S. real y : T" using S_def T_def by auto
  ultimately have "EX S. x0 : S & open S & (ALL y:S. real y : T)" by auto
} from this show ?thesis unfolding continuous_at_open by blast
qed


lemma continuous_at_iff_extreal:
fixes f :: "'a::t2_space => real"
shows "continuous (at x0) f <-> continuous (at x0) (extreal o f)"
proof-
{ assume "continuous (at x0) f" hence "continuous (at x0) (extreal o f)"
     using continuous_at_extreal continuous_at_compose[of x0 f extreal] by auto
}
moreover
{ assume "continuous (at x0) (extreal o f)"
  hence "continuous (at x0) (real o (extreal o f))"
     using continuous_at_of_extreal by (intro continuous_at_compose[of x0 "extreal o f"]) auto
  moreover have "real o (extreal o f) = f" using real_extreal_id by (simp add: o_assoc)
  ultimately have "continuous (at x0) f" by auto
} ultimately show ?thesis by auto
qed


lemma continuous_on_iff_extreal:
fixes f :: "'a::t2_space => real"
fixes A assumes "open A"
shows "continuous_on A f <-> continuous_on A (extreal o f)"
   using continuous_at_iff_extreal assms by (auto simp add: continuous_on_eq_continuous_at)


lemma continuous_on_real: "continuous_on (UNIV-{\<infinity>,(-\<infinity>)}) real"
   using continuous_at_of_extreal continuous_on_eq_continuous_at open_image_extreal by auto


lemma continuous_on_iff_real:
  fixes f :: "'a::t2_space => extreal"
  assumes "\<And>x. x \<in> A \<Longrightarrow> \<bar>f x\<bar> \<noteq> \<infinity>"
  shows "continuous_on A f \<longleftrightarrow> continuous_on A (real \<circ> f)"
proof-
  have "f ` A <= UNIV-{\<infinity>,(-\<infinity>)}" using assms by force
  hence *: "continuous_on (f ` A) real"
     using continuous_on_real by (simp add: continuous_on_subset)
have **: "continuous_on ((real o f) ` A) extreal"
   using continuous_on_extreal continuous_on_subset[of "UNIV" "extreal" "(real o f) ` A"] by blast
{ assume "continuous_on A f" hence "continuous_on A (real o f)"
  apply (subst continuous_on_compose) using * by auto
}
moreover
{ assume "continuous_on A (real o f)"
  hence "continuous_on A (extreal o (real o f))"
     apply (subst continuous_on_compose) using ** by auto
  hence "continuous_on A f"
     apply (subst continuous_on_eq[of A "extreal o (real o f)" f])
     using assms extreal_real by auto
}
ultimately show ?thesis by auto
qed


lemma continuous_at_const:
  fixes f :: "'a::t2_space => extreal"
  assumes "ALL x. (f x = C)"
  shows "ALL x. continuous (at x) f"
unfolding continuous_at_open using assms t1_space by auto


lemma closure_contains_Inf:
  fixes S :: "real set"
  assumes "S ~= {}" "EX B. ALL x:S. B<=x"
  shows "Inf S : closure S"
proof-
have *: "ALL x:S. Inf S <= x" using Inf_lower_EX[of _ S] assms by metis
{ fix e assume "e>(0 :: real)"
  from this obtain x where x_def: "x:S & x < Inf S + e" using Inf_close `S ~= {}` by auto
  moreover hence "x > Inf S - e" using * by auto
  ultimately have "abs (x - Inf S) < e" by (simp add: abs_diff_less_iff)
  hence "EX x:S. abs (x - Inf S) < e" using x_def by auto
} from this show ?thesis apply (subst closure_approachable) unfolding dist_norm by auto
qed


lemma closed_contains_Inf:
  fixes S :: "real set"
  assumes "S ~= {}" "EX B. ALL x:S. B<=x"
  assumes "closed S"
  shows "Inf S : S"
by (metis closure_contains_Inf closure_closed assms)


lemma mono_closed_real:
  fixes S :: "real set"
  assumes mono: "ALL y z. y:S & y<=z --> z:S"
  assumes "closed S"
  shows "S = {} | S = UNIV | (EX a. S = {a ..})"
proof-
{ assume "S ~= {}"
  { assume ex: "EX B. ALL x:S. B<=x"
    hence *: "ALL x:S. Inf S <= x" using Inf_lower_EX[of _ S] ex by metis
    hence "Inf S : S" apply (subst closed_contains_Inf) using ex `S ~= {}` `closed S` by auto
    hence "ALL x. (Inf S <= x <-> x:S)" using mono[rule_format, of "Inf S"] * by auto
    hence "S = {Inf S ..}" by auto
    hence "EX a. S = {a ..}" by auto
  }
  moreover
  { assume "~(EX B. ALL x:S. B<=x)"
    hence nex: "ALL B. EX x:S. x<B" by (simp add: not_le)
    { fix y obtain x where "x:S & x < y" using nex by auto
      hence "y:S" using mono[rule_format, of x y] by auto
    } hence "S = UNIV" by auto
  } ultimately have "S = UNIV | (EX a. S = {a ..})" by blast
} from this show ?thesis by blast
qed


lemma mono_closed_extreal:
  fixes S :: "real set"
  assumes mono: "ALL y z. y:S & y<=z --> z:S"
  assumes "closed S"
  shows "EX a. S = {x. a <= extreal x}"
proof-
{ assume "S = {}" hence ?thesis apply(rule_tac x=PInfty in exI) by auto }
moreover
{ assume "S = UNIV" hence ?thesis apply(rule_tac x="-\<infinity>" in exI) by auto }
moreover
{ assume "EX a. S = {a ..}"
  from this obtain a where "S={a ..}" by auto
  hence ?thesis apply(rule_tac x="extreal a" in exI) by auto
} ultimately show ?thesis using mono_closed_real[of S] assms by auto
qed

subsection {* Sums *}

lemma setsum_extreal[simp]:
  "(\<Sum>x\<in>A. extreal (f x)) = extreal (\<Sum>x\<in>A. f x)"
proof cases
  assume "finite A" then show ?thesis by induct auto
qed simp

lemma setsum_Pinfty: "(\<Sum>x\<in>P. f x) = \<infinity> \<longleftrightarrow> (finite P \<and> (\<exists>i\<in>P. f i = \<infinity>))"
proof safe
  assume *: "setsum f P = \<infinity>"
  show "finite P"
  proof (rule ccontr) assume "infinite P" with * show False by auto qed
  show "\<exists>i\<in>P. f i = \<infinity>"
  proof (rule ccontr)
    assume "\<not> ?thesis" then have "\<And>i. i \<in> P \<Longrightarrow> f i \<noteq> \<infinity>" by auto
    from `finite P` this have "setsum f P \<noteq> \<infinity>"
      by induct auto
    with * show False by auto
  qed
next
  fix i assume "finite P" "i \<in> P" "f i = \<infinity>"
  thus "setsum f P = \<infinity>"
  proof induct
    case (insert x A)
    show ?case using insert by (cases "x = i") auto
  qed simp
qed

lemma setsum_Inf:
  shows "\<bar>setsum f A\<bar> = \<infinity> \<longleftrightarrow> (finite A \<and> (\<exists>i\<in>A. \<bar>f i\<bar> = \<infinity>))"
proof
  assume *: "\<bar>setsum f A\<bar> = \<infinity>"
  have "finite A" by (rule ccontr) (insert *, auto)
  moreover have "\<exists>i\<in>A. \<bar>f i\<bar> = \<infinity>"
  proof (rule ccontr)
    assume "\<not> ?thesis" then have "\<forall>i\<in>A. \<exists>r. f i = extreal r" by auto
    from bchoice[OF this] guess r ..
    with * show False by (auto simp: setsum_extreal)
  qed
  ultimately show "finite A \<and> (\<exists>i\<in>A. \<bar>f i\<bar> = \<infinity>)" by auto
next
  assume "finite A \<and> (\<exists>i\<in>A. \<bar>f i\<bar> = \<infinity>)"
  then obtain i where "finite A" "i \<in> A" "\<bar>f i\<bar> = \<infinity>" by auto
  then show "\<bar>setsum f A\<bar> = \<infinity>"
  proof induct
    case (insert j A) then show ?case
      by (cases rule: extreal3_cases[of "f i" "f j" "setsum f A"]) auto
  qed simp
qed

lemma setsum_real_of_extreal:
  assumes "\<And>x. x \<in> S \<Longrightarrow> \<bar>f x\<bar> \<noteq> \<infinity>"
  shows "(\<Sum>x\<in>S. real (f x)) = real (setsum f S)"
proof -
  have "\<forall>x\<in>S. \<exists>r. f x = extreal r"
  proof
    fix x assume "x \<in> S"
    from assms[OF this] show "\<exists>r. f x = extreal r" by (cases "f x") auto
  qed
  from bchoice[OF this] guess r ..
  then show ?thesis by simp
qed

lemma setsum_extreal_0:
  fixes f :: "'a \<Rightarrow> extreal" assumes "finite A" "\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i"
  shows "(\<Sum>x\<in>A. f x) = 0 \<longleftrightarrow> (\<forall>i\<in>A. f i = 0)"
proof
  assume *: "(\<Sum>x\<in>A. f x) = 0"
  then have "(\<Sum>x\<in>A. f x) \<noteq> \<infinity>" by auto
  then have "\<forall>i\<in>A. \<bar>f i\<bar> \<noteq> \<infinity>" using assms by (force simp: setsum_Pinfty)
  then have "\<forall>i\<in>A. \<exists>r. f i = extreal r" by auto
  from bchoice[OF this] * assms show "\<forall>i\<in>A. f i = 0"
    using setsum_nonneg_eq_0_iff[of A "\<lambda>i. real (f i)"] by auto
qed (rule setsum_0')


lemma setsum_extreal_right_distrib:
  fixes f :: "'a \<Rightarrow> extreal" assumes "\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i"
  shows "r * setsum f A = (\<Sum>n\<in>A. r * f n)"
proof cases
  assume "finite A" then show ?thesis using assms
    by induct (auto simp: extreal_right_distrib setsum_nonneg)
qed simp

lemma sums_extreal_positive:
  fixes f :: "nat \<Rightarrow> extreal" assumes "\<And>i. 0 \<le> f i" shows "f sums (SUP n. \<Sum>i<n. f i)"
proof -
  have "incseq (\<lambda>i. \<Sum>j=0..<i. f j)"
    using extreal_add_mono[OF _ assms] by (auto intro!: incseq_SucI)
  from LIMSEQ_extreal_SUPR[OF this]
  show ?thesis unfolding sums_def by (simp add: atLeast0LessThan)
qed

lemma summable_extreal_pos:
  fixes f :: "nat \<Rightarrow> extreal" assumes "\<And>i. 0 \<le> f i" shows "summable f"
  using sums_extreal_positive[of f, OF assms] unfolding summable_def by auto

lemma suminf_extreal_eq_SUPR:
  fixes f :: "nat \<Rightarrow> extreal" assumes "\<And>i. 0 \<le> f i"
  shows "(\<Sum>x. f x) = (SUP n. \<Sum>i<n. f i)"
  using sums_extreal_positive[of f, OF assms, THEN sums_unique] by simp

lemma sums_extreal:
  "(\<lambda>x. extreal (f x)) sums extreal x \<longleftrightarrow> f sums x"
  unfolding sums_def by simp

lemma suminf_bound:
  fixes f :: "nat \<Rightarrow> extreal"
  assumes "\<forall>N. (\<Sum>n<N. f n) \<le> x" and pos: "\<And>n. 0 \<le> f n"
  shows "suminf f \<le> x"
proof (rule Lim_bounded_extreal)
  have "summable f" using pos[THEN summable_extreal_pos] .
  then show "(\<lambda>N. \<Sum>n<N. f n) ----> suminf f"
    by (auto dest!: summable_sums simp: sums_def atLeast0LessThan)
  show "\<forall>n\<ge>0. setsum f {..<n} \<le> x"
    using assms by auto
qed

lemma suminf_bound_add:
  fixes f :: "nat \<Rightarrow> extreal"
  assumes "\<forall>N. (\<Sum>n<N. f n) + y \<le> x" and pos: "\<And>n. 0 \<le> f n" and "y \<noteq> -\<infinity>"
  shows "suminf f + y \<le> x"
proof (cases y)
  case (real r) then have "\<forall>N. (\<Sum>n<N. f n) \<le> x - y"
    using assms by (simp add: extreal_le_minus)
  then have "(\<Sum> n. f n) \<le> x - y" using pos by (rule suminf_bound)
  then show "(\<Sum> n. f n) + y \<le> x"
    using assms real by (simp add: extreal_le_minus)
qed (insert assms, auto)

lemma sums_finite:
  assumes "\<forall>N\<ge>n. f N = 0"
  shows "f sums (\<Sum>N<n. f N)"
proof -
  { fix i have "(\<Sum>N<i + n. f N) = (\<Sum>N<n. f N)"
      by (induct i) (insert assms, auto) }
  note this[simp]
  show ?thesis unfolding sums_def
    by (rule LIMSEQ_offset[of _ n]) (auto simp add: atLeast0LessThan)
qed

lemma suminf_finite:
  fixes f :: "nat \<Rightarrow> 'a::{comm_monoid_add,t2_space}" assumes "\<forall>N\<ge>n. f N = 0"
  shows "suminf f = (\<Sum>N<n. f N)"
  using sums_finite[OF assms, THEN sums_unique] by simp

lemma suminf_extreal_0[simp]: "(\<Sum>i. 0) = (0::'a::{comm_monoid_add,t2_space})"
  using suminf_finite[of 0 "\<lambda>x. 0"] by simp

lemma suminf_upper:
  fixes f :: "nat \<Rightarrow> extreal" assumes "\<And>n. 0 \<le> f n"
  shows "(\<Sum>n<N. f n) \<le> (\<Sum>n. f n)"
  unfolding suminf_extreal_eq_SUPR[OF assms] SUPR_def
  by (auto intro: complete_lattice_class.Sup_upper image_eqI)

lemma suminf_0_le:
  fixes f :: "nat \<Rightarrow> extreal" assumes "\<And>n. 0 \<le> f n"
  shows "0 \<le> (\<Sum>n. f n)"
  using suminf_upper[of f 0, OF assms] by simp

lemma suminf_le_pos:
  fixes f g :: "nat \<Rightarrow> extreal"
  assumes "\<And>N. f N \<le> g N" "\<And>N. 0 \<le> f N"
  shows "suminf f \<le> suminf g"
proof (safe intro!: suminf_bound)
  fix n { fix N have "0 \<le> g N" using assms(2,1)[of N] by auto }
  have "setsum f {..<n} \<le> setsum g {..<n}" using assms by (auto intro: setsum_mono)
  also have "... \<le> suminf g" using `\<And>N. 0 \<le> g N` by (rule suminf_upper)
  finally show "setsum f {..<n} \<le> suminf g" .
qed (rule assms(2))

lemma suminf_half_series_extreal: "(\<Sum>n. (1/2 :: extreal)^Suc n) = 1"
  using sums_extreal[THEN iffD2, OF power_half_series, THEN sums_unique, symmetric]
  by (simp add: one_extreal_def)

lemma suminf_add_extreal:
  fixes f g :: "nat \<Rightarrow> extreal"
  assumes "\<And>i. 0 \<le> f i" "\<And>i. 0 \<le> g i"
  shows "(\<Sum>i. f i + g i) = suminf f + suminf g"
  apply (subst (1 2 3) suminf_extreal_eq_SUPR)
  unfolding setsum_addf
  by (intro assms extreal_add_nonneg_nonneg SUPR_extreal_add_pos incseq_setsumI setsum_nonneg ballI)+

lemma suminf_cmult_extreal:
  fixes f g :: "nat \<Rightarrow> extreal"
  assumes "\<And>i. 0 \<le> f i" "0 \<le> a"
  shows "(\<Sum>i. a * f i) = a * suminf f"
  by (auto simp: setsum_extreal_right_distrib[symmetric] assms
                 extreal_zero_le_0_iff setsum_nonneg suminf_extreal_eq_SUPR
           intro!: SUPR_extreal_cmult )

lemma suminf_PInfty:
  assumes "\<And>i. 0 \<le> f i" "suminf f \<noteq> \<infinity>"
  shows "f i \<noteq> \<infinity>"
proof -
  from suminf_upper[of f "Suc i", OF assms(1)] assms(2)
  have "(\<Sum>i<Suc i. f i) \<noteq> \<infinity>" by auto
  then show ?thesis
    unfolding setsum_Pinfty by simp
qed

lemma suminf_PInfty_fun:
  assumes "\<And>i. 0 \<le> f i" "suminf f \<noteq> \<infinity>"
  shows "\<exists>f'. f = (\<lambda>x. extreal (f' x))"
proof -
  have "\<forall>i. \<exists>r. f i = extreal r"
  proof
    fix i show "\<exists>r. f i = extreal r"
      using suminf_PInfty[OF assms] assms(1)[of i] by (cases "f i") auto
  qed
  from choice[OF this] show ?thesis by auto
qed

lemma summable_extreal:
  assumes "\<And>i. 0 \<le> f i" "(\<Sum>i. extreal (f i)) \<noteq> \<infinity>"
  shows "summable f"
proof -
  have "0 \<le> (\<Sum>i. extreal (f i))"
    using assms by (intro suminf_0_le) auto
  with assms obtain r where r: "(\<Sum>i. extreal (f i)) = extreal r"
    by (cases "\<Sum>i. extreal (f i)") auto
  from summable_extreal_pos[of "\<lambda>x. extreal (f x)"]
  have "summable (\<lambda>x. extreal (f x))" using assms by auto
  from summable_sums[OF this]
  have "(\<lambda>x. extreal (f x)) sums (\<Sum>x. extreal (f x))" by auto
  then show "summable f"
    unfolding r sums_extreal summable_def ..
qed

lemma suminf_extreal:
  assumes "\<And>i. 0 \<le> f i" "(\<Sum>i. extreal (f i)) \<noteq> \<infinity>"
  shows "(\<Sum>i. extreal (f i)) = extreal (suminf f)"
proof (rule sums_unique[symmetric])
  from summable_extreal[OF assms]
  show "(\<lambda>x. extreal (f x)) sums (extreal (suminf f))"
    unfolding sums_extreal using assms by (intro summable_sums summable_extreal)
qed

lemma suminf_extreal_minus:
  fixes f g :: "nat \<Rightarrow> extreal"
  assumes ord: "\<And>i. g i \<le> f i" "\<And>i. 0 \<le> g i" and fin: "suminf f \<noteq> \<infinity>" "suminf g \<noteq> \<infinity>"
  shows "(\<Sum>i. f i - g i) = suminf f - suminf g"
proof -
  { fix i have "0 \<le> f i" using ord[of i] by auto }
  moreover
  from suminf_PInfty_fun[OF `\<And>i. 0 \<le> f i` fin(1)] guess f' .. note this[simp]
  from suminf_PInfty_fun[OF `\<And>i. 0 \<le> g i` fin(2)] guess g' .. note this[simp]
  { fix i have "0 \<le> f i - g i" using ord[of i] by (auto simp: extreal_le_minus_iff) }
  moreover
  have "suminf (\<lambda>i. f i - g i) \<le> suminf f"
    using assms by (auto intro!: suminf_le_pos simp: field_simps)
  then have "suminf (\<lambda>i. f i - g i) \<noteq> \<infinity>" using fin by auto
  ultimately show ?thesis using assms `\<And>i. 0 \<le> f i`
    apply simp
    by (subst (1 2 3) suminf_extreal)
       (auto intro!: suminf_diff[symmetric] summable_extreal)
qed

lemma suminf_extreal_PInf[simp]:
  "(\<Sum>x. \<infinity>) = \<infinity>"
proof -
  have "(\<Sum>i<Suc 0. \<infinity>) \<le> (\<Sum>x. \<infinity>)" by (rule suminf_upper) auto
  then show ?thesis by simp
qed

lemma summable_real_of_extreal:
  assumes f: "\<And>i. 0 \<le> f i" and fin: "(\<Sum>i. f i) \<noteq> \<infinity>"
  shows "summable (\<lambda>i. real (f i))"
proof (rule summable_def[THEN iffD2])
  have "0 \<le> (\<Sum>i. f i)" using assms by (auto intro: suminf_0_le)
  with fin obtain r where r: "extreal r = (\<Sum>i. f i)" by (cases "(\<Sum>i. f i)") auto
  { fix i have "f i \<noteq> \<infinity>" using f by (intro suminf_PInfty[OF _ fin]) auto
    then have "\<bar>f i\<bar> \<noteq> \<infinity>" using f[of i] by auto }
  note fin = this
  have "(\<lambda>i. extreal (real (f i))) sums (\<Sum>i. extreal (real (f i)))"
    using f by (auto intro!: summable_extreal_pos summable_sums simp: extreal_le_real_iff zero_extreal_def)
  also have "\<dots> = extreal r" using fin r by (auto simp: extreal_real)
  finally show "\<exists>r. (\<lambda>i. real (f i)) sums r" by (auto simp: sums_extreal)
qed

lemma suminf_SUP_eq:
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> extreal"
  assumes "\<And>i. incseq (\<lambda>n. f n i)" "\<And>n i. 0 \<le> f n i"
  shows "(\<Sum>i. SUP n. f n i) = (SUP n. \<Sum>i. f n i)"
proof -
  { fix n :: nat
    have "(\<Sum>i<n. SUP k. f k i) = (SUP k. \<Sum>i<n. f k i)"
      using assms by (auto intro!: SUPR_extreal_setsum[symmetric]) }
  note * = this
  show ?thesis using assms
    apply (subst (1 2) suminf_extreal_eq_SUPR)
    unfolding *
    apply (auto intro!: le_SUPI2)
    apply (subst SUP_commute) ..
qed

end