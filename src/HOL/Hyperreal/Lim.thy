(*  Title       : Lim.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header{* Limits and Continuity *}

theory Lim
imports SEQ
begin

text{*Standard and Nonstandard Definitions*}

definition
  LIM :: "['a::real_normed_vector => 'b::real_normed_vector, 'a, 'b] => bool"
        ("((_)/ -- (_)/ --> (_))" [60, 0, 60] 60)
  "f -- a --> L =
     (\<forall>r > 0. \<exists>s > 0. \<forall>x. x \<noteq> a & norm (x - a) < s
        --> norm (f x - L) < r)"

  NSLIM :: "['a::real_normed_vector => 'b::real_normed_vector, 'a, 'b] => bool"
            ("((_)/ -- (_)/ --NS> (_))" [60, 0, 60] 60)
  "f -- a --NS> L =
    (\<forall>x. (x \<noteq> star_of a & x @= star_of a --> ( *f* f) x @= star_of L))"

  isCont :: "['a::real_normed_vector => 'b::real_normed_vector, 'a] => bool"
  "isCont f a = (f -- a --> (f a))"

  isNSCont :: "['a::real_normed_vector => 'b::real_normed_vector, 'a] => bool"
    --{*NS definition dispenses with limit notions*}
  "isNSCont f a = (\<forall>y. y @= star_of a -->
         ( *f* f) y @= star_of (f a))"

  isUCont :: "['a::real_normed_vector => 'b::real_normed_vector] => bool"
  "isUCont f = (\<forall>r>0. \<exists>s>0. \<forall>x y. norm (x - y) < s \<longrightarrow> norm (f x - f y) < r)"

  isNSUCont :: "['a::real_normed_vector => 'b::real_normed_vector] => bool"
  "isNSUCont f = (\<forall>x y. x @= y --> ( *f* f) x @= ( *f* f) y)"


subsection {* Limits of Functions *}

subsubsection {* Purely standard proofs *}

lemma LIM_eq:
     "f -- a --> L =
     (\<forall>r>0.\<exists>s>0.\<forall>x. x \<noteq> a & norm (x-a) < s --> norm (f x - L) < r)"
by (simp add: LIM_def diff_minus)

lemma LIM_I:
     "(!!r. 0<r ==> \<exists>s>0.\<forall>x. x \<noteq> a & norm (x-a) < s --> norm (f x - L) < r)
      ==> f -- a --> L"
by (simp add: LIM_eq)

lemma LIM_D:
     "[| f -- a --> L; 0<r |]
      ==> \<exists>s>0.\<forall>x. x \<noteq> a & norm (x-a) < s --> norm (f x - L) < r"
by (simp add: LIM_eq)

lemma LIM_offset: "f -- a --> L \<Longrightarrow> (\<lambda>x. f (x + k)) -- a - k --> L"
apply (rule LIM_I)
apply (drule_tac r="r" in LIM_D, safe)
apply (rule_tac x="s" in exI, safe)
apply (drule_tac x="x + k" in spec)
apply (simp add: compare_rls)
done

lemma LIM_offset_zero: "f -- a --> L \<Longrightarrow> (\<lambda>h. f (a + h)) -- 0 --> L"
by (drule_tac k="a" in LIM_offset, simp add: add_commute)

lemma LIM_offset_zero_cancel: "(\<lambda>h. f (a + h)) -- 0 --> L \<Longrightarrow> f -- a --> L"
by (drule_tac k="- a" in LIM_offset, simp)

lemma LIM_const [simp]: "(%x. k) -- x --> k"
by (simp add: LIM_def)

lemma LIM_add:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes f: "f -- a --> L" and g: "g -- a --> M"
  shows "(%x. f x + g(x)) -- a --> (L + M)"
proof (rule LIM_I)
  fix r :: real
  assume r: "0 < r"
  from LIM_D [OF f half_gt_zero [OF r]]
  obtain fs
    where fs:    "0 < fs"
      and fs_lt: "\<forall>x. x \<noteq> a & norm (x-a) < fs --> norm (f x - L) < r/2"
  by blast
  from LIM_D [OF g half_gt_zero [OF r]]
  obtain gs
    where gs:    "0 < gs"
      and gs_lt: "\<forall>x. x \<noteq> a & norm (x-a) < gs --> norm (g x - M) < r/2"
  by blast
  show "\<exists>s>0.\<forall>x. x \<noteq> a \<and> norm (x-a) < s \<longrightarrow> norm (f x + g x - (L + M)) < r"
  proof (intro exI conjI strip)
    show "0 < min fs gs"  by (simp add: fs gs)
    fix x :: 'a
    assume "x \<noteq> a \<and> norm (x-a) < min fs gs"
    hence "x \<noteq> a \<and> norm (x-a) < fs \<and> norm (x-a) < gs" by simp
    with fs_lt gs_lt
    have "norm (f x - L) < r/2" and "norm (g x - M) < r/2" by blast+
    hence "norm (f x - L) + norm (g x - M) < r" by arith
    thus "norm (f x + g x - (L + M)) < r"
      by (blast intro: norm_diff_triangle_ineq order_le_less_trans)
  qed
qed

lemma minus_diff_minus:
  fixes a b :: "'a::ab_group_add"
  shows "(- a) - (- b) = - (a - b)"
by simp

lemma LIM_minus: "f -- a --> L ==> (%x. -f(x)) -- a --> -L"
by (simp only: LIM_eq minus_diff_minus norm_minus_cancel)

lemma LIM_add_minus:
    "[| f -- x --> l; g -- x --> m |] ==> (%x. f(x) + -g(x)) -- x --> (l + -m)"
by (intro LIM_add LIM_minus)

lemma LIM_diff:
    "[| f -- x --> l; g -- x --> m |] ==> (%x. f(x) - g(x)) -- x --> l-m"
by (simp only: diff_minus LIM_add LIM_minus)

lemma LIM_zero: "f -- a --> l \<Longrightarrow> (\<lambda>x. f x - l) -- a --> 0"
by (simp add: LIM_def)

lemma LIM_zero_cancel: "(\<lambda>x. f x - l) -- a --> 0 \<Longrightarrow> f -- a --> l"
by (simp add: LIM_def)

lemma LIM_const_not_eq:
  fixes a :: "'a::real_normed_div_algebra"
  shows "k \<noteq> L ==> ~ ((%x. k) -- a --> L)"
apply (simp add: LIM_eq)
apply (rule_tac x="norm (k - L)" in exI, simp, safe)
apply (rule_tac x="a + of_real (s/2)" in exI, simp add: norm_of_real)
done

lemma LIM_const_eq:
  fixes a :: "'a::real_normed_div_algebra"
  shows "(%x. k) -- a --> L ==> k = L"
apply (rule ccontr)
apply (blast dest: LIM_const_not_eq)
done

lemma LIM_unique:
  fixes a :: "'a::real_normed_div_algebra"
  shows "[| f -- a --> L; f -- a --> M |] ==> L = M"
apply (drule LIM_diff, assumption)
apply (auto dest!: LIM_const_eq)
done

lemma LIM_mult_zero:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  assumes f: "f -- a --> 0" and g: "g -- a --> 0"
  shows "(%x. f(x) * g(x)) -- a --> 0"
proof (rule LIM_I, simp)
  fix r :: real
  assume r: "0<r"
  from LIM_D [OF f zero_less_one]
  obtain fs
    where fs:    "0 < fs"
      and fs_lt: "\<forall>x. x \<noteq> a & norm (x-a) < fs --> norm (f x) < 1"
  by auto
  from LIM_D [OF g r]
  obtain gs
    where gs:    "0 < gs"
      and gs_lt: "\<forall>x. x \<noteq> a & norm (x-a) < gs --> norm (g x) < r"
  by auto
  show "\<exists>s. 0 < s \<and> (\<forall>x. x \<noteq> a \<and> norm (x-a) < s \<longrightarrow> norm (f x * g x) < r)"
  proof (intro exI conjI strip)
    show "0 < min fs gs"  by (simp add: fs gs)
    fix x :: 'a
    assume "x \<noteq> a \<and> norm (x-a) < min fs gs"
    hence  "x \<noteq> a \<and> norm (x-a) < fs \<and> norm (x-a) < gs" by simp
    with fs_lt gs_lt
    have "norm (f x) < 1" and "norm (g x) < r" by blast+
    hence "norm (f x) * norm (g x) < 1*r"
      by (rule mult_strict_mono' [OF _ _ norm_ge_zero norm_ge_zero])
    thus "norm (f x * g x) < r"
      by (simp add: order_le_less_trans [OF norm_mult_ineq])
  qed
qed

lemma LIM_self: "(%x. x) -- a --> a"
by (auto simp add: LIM_def)

text{*Limits are equal for functions equal except at limit point*}
lemma LIM_equal:
     "[| \<forall>x. x \<noteq> a --> (f x = g x) |] ==> (f -- a --> l) = (g -- a --> l)"
by (simp add: LIM_def)

lemma LIM_cong:
  "\<lbrakk>a = b; \<And>x. x \<noteq> b \<Longrightarrow> f x = g x; l = m\<rbrakk>
   \<Longrightarrow> (f -- a --> l) = (g -- b --> m)"
by (simp add: LIM_def)

text{*Two uses in Hyperreal/Transcendental.ML*}
lemma LIM_trans:
     "[| (%x. f(x) + -g(x)) -- a --> 0;  g -- a --> l |] ==> f -- a --> l"
apply (drule LIM_add, assumption)
apply (auto simp add: add_assoc)
done

lemma LIM_compose:
  assumes g: "g -- l --> g l"
  assumes f: "f -- a --> l"
  shows "(\<lambda>x. g (f x)) -- a --> g l"
proof (rule LIM_I)
  fix r::real assume r: "0 < r"
  obtain s where s: "0 < s"
    and less_r: "\<And>y. \<lbrakk>y \<noteq> l; norm (y - l) < s\<rbrakk> \<Longrightarrow> norm (g y - g l) < r"
    using LIM_D [OF g r] by fast
  obtain t where t: "0 < t"
    and less_s: "\<And>x. \<lbrakk>x \<noteq> a; norm (x - a) < t\<rbrakk> \<Longrightarrow> norm (f x - l) < s"
    using LIM_D [OF f s] by fast

  show "\<exists>t>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < t \<longrightarrow> norm (g (f x) - g l) < r"
  proof (rule exI, safe)
    show "0 < t" using t .
  next
    fix x assume "x \<noteq> a" and "norm (x - a) < t"
    hence "norm (f x - l) < s" by (rule less_s)
    thus "norm (g (f x) - g l) < r"
      using r less_r by (case_tac "f x = l", simp_all)
  qed
qed

lemma LIM_o: "\<lbrakk>g -- l --> g l; f -- a --> l\<rbrakk> \<Longrightarrow> (g \<circ> f) -- a --> g l"
unfolding o_def by (rule LIM_compose)

subsubsection {* Purely nonstandard proofs *}

lemma NSLIM_I:
  "(\<And>x. \<lbrakk>x \<noteq> star_of a; x \<approx> star_of a\<rbrakk> \<Longrightarrow> starfun f x \<approx> star_of L)
   \<Longrightarrow> f -- a --NS> L"
by (simp add: NSLIM_def)

lemma NSLIM_D:
  "\<lbrakk>f -- a --NS> L; x \<noteq> star_of a; x \<approx> star_of a\<rbrakk>
   \<Longrightarrow> starfun f x \<approx> star_of L"
by (simp add: NSLIM_def)

text{*Proving properties of limits using nonstandard definition.
      The properties hold for standard limits as well!*}

lemma NSLIM_mult:
  fixes l m :: "'a::real_normed_algebra"
  shows "[| f -- x --NS> l; g -- x --NS> m |]
      ==> (%x. f(x) * g(x)) -- x --NS> (l * m)"
by (auto simp add: NSLIM_def intro!: approx_mult_HFinite)

lemma starfun_scaleR [simp]:
  "starfun (\<lambda>x. f x *# g x) = (\<lambda>x. scaleHR (starfun f x) (starfun g x))"
by transfer (rule refl)

lemma NSLIM_scaleR:
  "[| f -- x --NS> l; g -- x --NS> m |]
      ==> (%x. f(x) *# g(x)) -- x --NS> (l *# m)"
by (auto simp add: NSLIM_def intro!: approx_scaleR_HFinite)

lemma NSLIM_add:
     "[| f -- x --NS> l; g -- x --NS> m |]
      ==> (%x. f(x) + g(x)) -- x --NS> (l + m)"
by (auto simp add: NSLIM_def intro!: approx_add)

lemma NSLIM_const [simp]: "(%x. k) -- x --NS> k"
by (simp add: NSLIM_def)

lemma NSLIM_minus: "f -- a --NS> L ==> (%x. -f(x)) -- a --NS> -L"
by (simp add: NSLIM_def)

lemma NSLIM_add_minus: "[| f -- x --NS> l; g -- x --NS> m |] ==> (%x. f(x) + -g(x)) -- x --NS> (l + -m)"
by (simp only: NSLIM_add NSLIM_minus)

lemma NSLIM_inverse:
  fixes L :: "'a::real_normed_div_algebra"
  shows "[| f -- a --NS> L;  L \<noteq> 0 |]
      ==> (%x. inverse(f(x))) -- a --NS> (inverse L)"
apply (simp add: NSLIM_def, clarify)
apply (drule spec)
apply (auto simp add: star_of_approx_inverse)
done

lemma NSLIM_zero:
  assumes f: "f -- a --NS> l" shows "(%x. f(x) + -l) -- a --NS> 0"
proof -
  have "(\<lambda>x. f x + - l) -- a --NS> l + -l"
    by (rule NSLIM_add_minus [OF f NSLIM_const])
  thus ?thesis by simp
qed

lemma NSLIM_zero_cancel: "(%x. f(x) - l) -- x --NS> 0 ==> f -- x --NS> l"
apply (drule_tac g = "%x. l" and m = l in NSLIM_add)
apply (auto simp add: diff_minus add_assoc)
done

lemma NSLIM_const_not_eq:
  fixes a :: real (* TODO: generalize to real_normed_div_algebra *)
  shows "k \<noteq> L ==> ~ ((%x. k) -- a --NS> L)"
apply (simp add: NSLIM_def)
apply (rule_tac x="star_of a + epsilon" in exI)
apply (auto intro: Infinitesimal_add_approx_self [THEN approx_sym]
            simp add: hypreal_epsilon_not_zero)
done

lemma NSLIM_not_zero:
  fixes a :: real
  shows "k \<noteq> 0 ==> ~ ((%x. k) -- a --NS> 0)"
by (rule NSLIM_const_not_eq)

lemma NSLIM_const_eq:
  fixes a :: real
  shows "(%x. k) -- a --NS> L ==> k = L"
apply (rule ccontr)
apply (blast dest: NSLIM_const_not_eq)
done

text{* can actually be proved more easily by unfolding the definition!*}
lemma NSLIM_unique:
  fixes a :: real
  shows "[| f -- a --NS> L; f -- a --NS> M |] ==> L = M"
apply (drule NSLIM_minus)
apply (drule NSLIM_add, assumption)
apply (auto dest!: NSLIM_const_eq [symmetric])
apply (simp add: diff_def [symmetric])
done

lemma NSLIM_mult_zero:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  shows "[| f -- x --NS> 0; g -- x --NS> 0 |] ==> (%x. f(x)*g(x)) -- x --NS> 0"
by (drule NSLIM_mult, auto)

lemma NSLIM_self: "(%x. x) -- a --NS> a"
by (simp add: NSLIM_def)

subsubsection {* Equivalence of @{term LIM} and @{term NSLIM} *}

lemma LIM_NSLIM:
  assumes f: "f -- a --> L" shows "f -- a --NS> L"
proof (rule NSLIM_I)
  fix x
  assume neq: "x \<noteq> star_of a"
  assume approx: "x \<approx> star_of a"
  have "starfun f x - star_of L \<in> Infinitesimal"
  proof (rule InfinitesimalI2)
    fix r::real assume r: "0 < r"
    from LIM_D [OF f r]
    obtain s where s: "0 < s" and
      less_r: "\<And>x. \<lbrakk>x \<noteq> a; norm (x - a) < s\<rbrakk> \<Longrightarrow> norm (f x - L) < r"
      by fast
    from less_r have less_r':
       "\<And>x. \<lbrakk>x \<noteq> star_of a; hnorm (x - star_of a) < star_of s\<rbrakk>
        \<Longrightarrow> hnorm (starfun f x - star_of L) < star_of r"
      by transfer
    from approx have "x - star_of a \<in> Infinitesimal"
      by (unfold approx_def)
    hence "hnorm (x - star_of a) < star_of s"
      using s by (rule InfinitesimalD2)
    with neq show "hnorm (starfun f x - star_of L) < star_of r"
      by (rule less_r')
  qed
  thus "starfun f x \<approx> star_of L"
    by (unfold approx_def)
qed

lemma NSLIM_LIM:
  assumes f: "f -- a --NS> L" shows "f -- a --> L"
proof (rule LIM_I)
  fix r::real assume r: "0 < r"
  have "\<exists>s>0. \<forall>x. x \<noteq> star_of a \<and> hnorm (x - star_of a) < s
        \<longrightarrow> hnorm (starfun f x - star_of L) < star_of r"
  proof (rule exI, safe)
    show "0 < epsilon" by (rule hypreal_epsilon_gt_zero)
  next
    fix x assume neq: "x \<noteq> star_of a"
    assume "hnorm (x - star_of a) < epsilon"
    with Infinitesimal_epsilon
    have "x - star_of a \<in> Infinitesimal"
      by (rule hnorm_less_Infinitesimal)
    hence "x \<approx> star_of a"
      by (unfold approx_def)
    with f neq have "starfun f x \<approx> star_of L"
      by (rule NSLIM_D)
    hence "starfun f x - star_of L \<in> Infinitesimal"
      by (unfold approx_def)
    thus "hnorm (starfun f x - star_of L) < star_of r"
      using r by (rule InfinitesimalD2)
  qed
  thus "\<exists>s>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < s \<longrightarrow> norm (f x - L) < r"
    by transfer
qed

theorem LIM_NSLIM_iff: "(f -- x --> L) = (f -- x --NS> L)"
by (blast intro: LIM_NSLIM NSLIM_LIM)

subsubsection {* Derived theorems about @{term LIM} *}

lemma LIM_mult2:
  fixes l m :: "'a::real_normed_algebra"
  shows "[| f -- x --> l; g -- x --> m |]
      ==> (%x. f(x) * g(x)) -- x --> (l * m)"
by (simp add: LIM_NSLIM_iff NSLIM_mult)

lemma LIM_scaleR:
  "[| f -- x --> l; g -- x --> m |]
      ==> (%x. f(x) *# g(x)) -- x --> (l *# m)"
by (simp add: LIM_NSLIM_iff NSLIM_scaleR)

lemma LIM_add2:
     "[| f -- x --> l; g -- x --> m |] ==> (%x. f(x) + g(x)) -- x --> (l + m)"
by (simp add: LIM_NSLIM_iff NSLIM_add)

lemma LIM_const2: "(%x. k) -- x --> k"
by (simp add: LIM_NSLIM_iff)

lemma LIM_minus2: "f -- a --> L ==> (%x. -f(x)) -- a --> -L"
by (simp add: LIM_NSLIM_iff NSLIM_minus)

lemma LIM_add_minus2: "[| f -- x --> l; g -- x --> m |] ==> (%x. f(x) + -g(x)) -- x --> (l + -m)"
by (simp add: LIM_NSLIM_iff NSLIM_add_minus)

lemma LIM_inverse:
  fixes L :: "'a::real_normed_div_algebra"
  shows "[| f -- a --> L; L \<noteq> 0 |]
      ==> (%x. inverse(f(x))) -- a --> (inverse L)"
by (simp add: LIM_NSLIM_iff NSLIM_inverse)

lemma LIM_zero2: "f -- a --> l ==> (%x. f(x) + -l) -- a --> 0"
by (simp add: LIM_NSLIM_iff NSLIM_zero)

lemma LIM_unique2:
  fixes a :: real
  shows "[| f -- a --> L; f -- a --> M |] ==> L = M"
by (simp add: LIM_NSLIM_iff NSLIM_unique)

(* we can use the corresponding thm LIM_mult2 *)
(* for standard definition of limit           *)

lemma LIM_mult_zero2:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  shows "[| f -- x --> 0; g -- x --> 0 |] ==> (%x. f(x)*g(x)) -- x --> 0"
by (drule LIM_mult2, auto)


subsection {* Continuity *}

subsubsection {* Purely standard proofs *}

lemma LIM_isCont_iff: "(f -- a --> f a) = ((\<lambda>h. f (a + h)) -- 0 --> f a)"
by (rule iffI [OF LIM_offset_zero LIM_offset_zero_cancel])

lemma isCont_iff: "isCont f x = (\<lambda>h. f (x + h)) -- 0 --> f x"
by (simp add: isCont_def LIM_isCont_iff)

lemma isCont_Id: "isCont (\<lambda>x. x) a"
unfolding isCont_def by (rule LIM_self)

lemma isCont_const [simp]: "isCont (%x. k) a"
unfolding isCont_def by (rule LIM_const)

lemma isCont_add: "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. f x + g x) a"
unfolding isCont_def by (rule LIM_add)

lemma isCont_minus: "isCont f a \<Longrightarrow> isCont (\<lambda>x. - f x) a"
unfolding isCont_def by (rule LIM_minus)

lemma isCont_diff: "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. f x - g x) a"
unfolding isCont_def by (rule LIM_diff)

lemma isCont_mult:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  shows "[| isCont f a; isCont g a |] ==> isCont (%x. f(x) * g(x)) a"
unfolding isCont_def by (rule LIM_mult2)

lemma isCont_inverse:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_div_algebra"
  shows "[| isCont f x; f x \<noteq> 0 |] ==> isCont (%x. inverse (f x)) x"
unfolding isCont_def by (rule LIM_inverse)

lemma isCont_LIM_compose:
  "\<lbrakk>isCont g l; f -- a --> l\<rbrakk> \<Longrightarrow> (\<lambda>x. g (f x)) -- a --> g l"
unfolding isCont_def by (rule LIM_compose)

lemma isCont_o2: "\<lbrakk>isCont f a; isCont g (f a)\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. g (f x)) a"
unfolding isCont_def by (rule LIM_compose)

lemma isCont_o: "\<lbrakk>isCont f a; isCont g (f a)\<rbrakk> \<Longrightarrow> isCont (g o f) a"
unfolding o_def by (rule isCont_o2)

subsubsection {* Nonstandard proofs *}

lemma isNSContD: "[| isNSCont f a; y \<approx> hypreal_of_real a |] ==> ( *f* f) y \<approx> hypreal_of_real (f a)"
by (simp add: isNSCont_def)

lemma isNSCont_NSLIM: "isNSCont f a ==> f -- a --NS> (f a) "
by (simp add: isNSCont_def NSLIM_def)

lemma NSLIM_isNSCont: "f -- a --NS> (f a) ==> isNSCont f a"
apply (simp add: isNSCont_def NSLIM_def, auto)
apply (case_tac "y = star_of a", auto)
done

text{*NS continuity can be defined using NS Limit in
    similar fashion to standard def of continuity*}
lemma isNSCont_NSLIM_iff: "(isNSCont f a) = (f -- a --NS> (f a))"
by (blast intro: isNSCont_NSLIM NSLIM_isNSCont)

text{*Hence, NS continuity can be given
  in terms of standard limit*}
lemma isNSCont_LIM_iff: "(isNSCont f a) = (f -- a --> (f a))"
by (simp add: LIM_NSLIM_iff isNSCont_NSLIM_iff)

text{*Moreover, it's trivial now that NS continuity
  is equivalent to standard continuity*}
lemma isNSCont_isCont_iff: "(isNSCont f a) = (isCont f a)"
apply (simp add: isCont_def)
apply (rule isNSCont_LIM_iff)
done

text{*Standard continuity ==> NS continuity*}
lemma isCont_isNSCont: "isCont f a ==> isNSCont f a"
by (erule isNSCont_isCont_iff [THEN iffD2])

text{*NS continuity ==> Standard continuity*}
lemma isNSCont_isCont: "isNSCont f a ==> isCont f a"
by (erule isNSCont_isCont_iff [THEN iffD1])

text{*Alternative definition of continuity*}
(* Prove equivalence between NS limits - *)
(* seems easier than using standard def  *)
lemma NSLIM_h_iff: "(f -- a --NS> L) = ((%h. f(a + h)) -- 0 --NS> L)"
apply (simp add: NSLIM_def, auto)
apply (drule_tac x = "star_of a + x" in spec)
apply (drule_tac [2] x = "- star_of a + x" in spec, safe, simp)
apply (erule mem_infmal_iff [THEN iffD2, THEN Infinitesimal_add_approx_self [THEN approx_sym]])
apply (erule_tac [3] approx_minus_iff2 [THEN iffD1])
 prefer 2 apply (simp add: add_commute diff_def [symmetric])
apply (rule_tac x = x in star_cases)
apply (rule_tac [2] x = x in star_cases)
apply (auto simp add: starfun star_of_def star_n_minus star_n_add add_assoc approx_refl star_n_zero_num)
done

lemma NSLIM_isCont_iff: "(f -- a --NS> f a) = ((%h. f(a + h)) -- 0 --NS> f a)"
by (rule NSLIM_h_iff)

lemma isNSCont_minus: "isNSCont f a ==> isNSCont (%x. - f x) a"
by (simp add: isNSCont_def)

lemma isNSCont_inverse:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_div_algebra"
  shows "[| isNSCont f x; f x \<noteq> 0 |] ==> isNSCont (%x. inverse (f x)) x"
by (auto intro: isCont_inverse simp add: isNSCont_isCont_iff)

lemma isNSCont_const [simp]: "isNSCont (%x. k) a"
by (simp add: isNSCont_def)

lemma isNSCont_abs [simp]: "isNSCont abs (a::real)"
apply (simp add: isNSCont_def)
apply (auto intro: approx_hrabs simp add: hypreal_of_real_hrabs [symmetric] starfun_rabs_hrabs)
done

lemma isCont_abs [simp]: "isCont abs (a::real)"
by (auto simp add: isNSCont_isCont_iff [symmetric])


(****************************************************************
(%* Leave as commented until I add topology theory or remove? *%)
(%*------------------------------------------------------------
  Elementary topology proof for a characterisation of
  continuity now: a function f is continuous if and only
  if the inverse image, {x. f(x) \<in> A}, of any open set A
  is always an open set
 ------------------------------------------------------------*%)
Goal "[| isNSopen A; \<forall>x. isNSCont f x |]
               ==> isNSopen {x. f x \<in> A}"
by (auto_tac (claset(),simpset() addsimps [isNSopen_iff1]));
by (dtac (mem_monad_approx RS approx_sym);
by (dres_inst_tac [("x","a")] spec 1);
by (dtac isNSContD 1 THEN assume_tac 1)
by (dtac bspec 1 THEN assume_tac 1)
by (dres_inst_tac [("x","( *f* f) x")] approx_mem_monad2 1);
by (blast_tac (claset() addIs [starfun_mem_starset]);
qed "isNSCont_isNSopen";

Goalw [isNSCont_def]
          "\<forall>A. isNSopen A --> isNSopen {x. f x \<in> A} \
\              ==> isNSCont f x";
by (auto_tac (claset() addSIs [(mem_infmal_iff RS iffD1) RS
     (approx_minus_iff RS iffD2)],simpset() addsimps
      [Infinitesimal_def,SReal_iff]));
by (dres_inst_tac [("x","{z. abs(z + -f(x)) < ya}")] spec 1);
by (etac (isNSopen_open_interval RSN (2,impE));
by (auto_tac (claset(),simpset() addsimps [isNSopen_def,isNSnbhd_def]));
by (dres_inst_tac [("x","x")] spec 1);
by (auto_tac (claset() addDs [approx_sym RS approx_mem_monad],
    simpset() addsimps [hypreal_of_real_zero RS sym,STAR_starfun_rabs_add_minus]));
qed "isNSopen_isNSCont";

Goal "(\<forall>x. isNSCont f x) = \
\     (\<forall>A. isNSopen A --> isNSopen {x. f(x) \<in> A})";
by (blast_tac (claset() addIs [isNSCont_isNSopen,
    isNSopen_isNSCont]);
qed "isNSCont_isNSopen_iff";

(%*------- Standard version of same theorem --------*%)
Goal "(\<forall>x. isCont f x) = \
\         (\<forall>A. isopen A --> isopen {x. f(x) \<in> A})";
by (auto_tac (claset() addSIs [isNSCont_isNSopen_iff],
              simpset() addsimps [isNSopen_isopen_iff RS sym,
              isNSCont_isCont_iff RS sym]));
qed "isCont_isopen_iff";
*******************************************************************)

subsection {* Uniform Continuity *}

lemma isNSUContD: "[| isNSUCont f; x \<approx> y|] ==> ( *f* f) x \<approx> ( *f* f) y"
by (simp add: isNSUCont_def)

lemma isUCont_isCont: "isUCont f ==> isCont f x"
by (simp add: isUCont_def isCont_def LIM_def, meson)

lemma isUCont_isNSUCont:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes f: "isUCont f" shows "isNSUCont f"
proof (unfold isNSUCont_def, safe)
  fix x y :: "'a star"
  assume approx: "x \<approx> y"
  have "starfun f x - starfun f y \<in> Infinitesimal"
  proof (rule InfinitesimalI2)
    fix r::real assume r: "0 < r"
    with f obtain s where s: "0 < s" and
      less_r: "\<And>x y. norm (x - y) < s \<Longrightarrow> norm (f x - f y) < r"
      by (auto simp add: isUCont_def)
    from less_r have less_r':
       "\<And>x y. hnorm (x - y) < star_of s
        \<Longrightarrow> hnorm (starfun f x - starfun f y) < star_of r"
      by transfer
    from approx have "x - y \<in> Infinitesimal"
      by (unfold approx_def)
    hence "hnorm (x - y) < star_of s"
      using s by (rule InfinitesimalD2)
    thus "hnorm (starfun f x - starfun f y) < star_of r"
      by (rule less_r')
  qed
  thus "starfun f x \<approx> starfun f y"
    by (unfold approx_def)
qed

lemma isNSUCont_isUCont:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes f: "isNSUCont f" shows "isUCont f"
proof (unfold isUCont_def, safe)
  fix r::real assume r: "0 < r"
  have "\<exists>s>0. \<forall>x y. hnorm (x - y) < s
        \<longrightarrow> hnorm (starfun f x - starfun f y) < star_of r"
  proof (rule exI, safe)
    show "0 < epsilon" by (rule hypreal_epsilon_gt_zero)
  next
    fix x y :: "'a star"
    assume "hnorm (x - y) < epsilon"
    with Infinitesimal_epsilon
    have "x - y \<in> Infinitesimal"
      by (rule hnorm_less_Infinitesimal)
    hence "x \<approx> y"
      by (unfold approx_def)
    with f have "starfun f x \<approx> starfun f y"
      by (simp add: isNSUCont_def)
    hence "starfun f x - starfun f y \<in> Infinitesimal"
      by (unfold approx_def)
    thus "hnorm (starfun f x - starfun f y) < star_of r"
      using r by (rule InfinitesimalD2)
  qed
  thus "\<exists>s>0. \<forall>x y. norm (x - y) < s \<longrightarrow> norm (f x - f y) < r"
    by transfer
qed

subsection {* Relation of LIM and LIMSEQ *}

lemma LIMSEQ_SEQ_conv1:
  fixes a :: "'a::real_normed_vector"
  assumes X: "X -- a --> L"
  shows "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L"
proof (safe intro!: LIMSEQ_I)
  fix S :: "nat \<Rightarrow> 'a"
  fix r :: real
  assume rgz: "0 < r"
  assume as: "\<forall>n. S n \<noteq> a"
  assume S: "S ----> a"
  from LIM_D [OF X rgz] obtain s
    where sgz: "0 < s"
    and aux: "\<And>x. \<lbrakk>x \<noteq> a; norm (x - a) < s\<rbrakk> \<Longrightarrow> norm (X x - L) < r"
    by fast
  from LIMSEQ_D [OF S sgz]
  obtain no where "\<forall>n\<ge>no. norm (S n - a) < s" by fast
  hence "\<forall>n\<ge>no. norm (X (S n) - L) < r" by (simp add: aux as)
  thus "\<exists>no. \<forall>n\<ge>no. norm (X (S n) - L) < r" ..
qed

lemma LIMSEQ_SEQ_conv2:
  fixes a :: real
  assumes "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L"
  shows "X -- a --> L"
proof (rule ccontr)
  assume "\<not> (X -- a --> L)"
  hence "\<not> (\<forall>r > 0. \<exists>s > 0. \<forall>x. x \<noteq> a & norm (x - a) < s --> norm (X x - L) < r)" by (unfold LIM_def)
  hence "\<exists>r > 0. \<forall>s > 0. \<exists>x. \<not>(x \<noteq> a \<and> \<bar>x - a\<bar> < s --> norm (X x - L) < r)" by simp
  hence "\<exists>r > 0. \<forall>s > 0. \<exists>x. (x \<noteq> a \<and> \<bar>x - a\<bar> < s \<and> norm (X x - L) \<ge> r)" by (simp add: linorder_not_less)
  then obtain r where rdef: "r > 0 \<and> (\<forall>s > 0. \<exists>x. (x \<noteq> a \<and> \<bar>x - a\<bar> < s \<and> norm (X x - L) \<ge> r))" by auto

  let ?F = "\<lambda>n::nat. SOME x. x\<noteq>a \<and> \<bar>x - a\<bar> < inverse (real (Suc n)) \<and> norm (X x - L) \<ge> r"
  have "\<And>n. \<exists>x. x\<noteq>a \<and> \<bar>x - a\<bar> < inverse (real (Suc n)) \<and> norm (X x - L) \<ge> r"
    using rdef by simp
  hence F: "\<And>n. ?F n \<noteq> a \<and> \<bar>?F n - a\<bar> < inverse (real (Suc n)) \<and> norm (X (?F n) - L) \<ge> r"
    by (rule someI_ex)
  hence F1: "\<And>n. ?F n \<noteq> a"
    and F2: "\<And>n. \<bar>?F n - a\<bar> < inverse (real (Suc n))"
    and F3: "\<And>n. norm (X (?F n) - L) \<ge> r"
    by fast+

  have "?F ----> a"
  proof (rule LIMSEQ_I, unfold real_norm_def)
      fix e::real
      assume "0 < e"
        (* choose no such that inverse (real (Suc n)) < e *)
      have "\<exists>no. inverse (real (Suc no)) < e" by (rule reals_Archimedean)
      then obtain m where nodef: "inverse (real (Suc m)) < e" by auto
      show "\<exists>no. \<forall>n. no \<le> n --> \<bar>?F n - a\<bar> < e"
      proof (intro exI allI impI)
        fix n
        assume mlen: "m \<le> n"
        have "\<bar>?F n - a\<bar> < inverse (real (Suc n))"
          by (rule F2)
        also have "inverse (real (Suc n)) \<le> inverse (real (Suc m))"
          by auto
        also from nodef have
          "inverse (real (Suc m)) < e" .
        finally show "\<bar>?F n - a\<bar> < e" .
      qed
  qed
  
  moreover have "\<forall>n. ?F n \<noteq> a"
    by (rule allI) (rule F1)

  moreover from prems have "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L" by simp
  ultimately have "(\<lambda>n. X (?F n)) ----> L" by simp
  
  moreover have "\<not> ((\<lambda>n. X (?F n)) ----> L)"
  proof -
    {
      fix no::nat
      obtain n where "n = no + 1" by simp
      then have nolen: "no \<le> n" by simp
        (* We prove this by showing that for any m there is an n\<ge>m such that |X (?F n) - L| \<ge> r *)
      have "norm (X (?F n) - L) \<ge> r"
        by (rule F3)
      with nolen have "\<exists>n. no \<le> n \<and> norm (X (?F n) - L) \<ge> r" by fast
    }
    then have "(\<forall>no. \<exists>n. no \<le> n \<and> norm (X (?F n) - L) \<ge> r)" by simp
    with rdef have "\<exists>e>0. (\<forall>no. \<exists>n. no \<le> n \<and> norm (X (?F n) - L) \<ge> e)" by auto
    thus ?thesis by (unfold LIMSEQ_def, auto simp add: linorder_not_less)
  qed
  ultimately show False by simp
qed

lemma LIMSEQ_SEQ_conv:
  "(\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> (a::real) \<longrightarrow> (\<lambda>n. X (S n)) ----> L) =
   (X -- a --> L)"
proof
  assume "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L"
  show "X -- a --> L" by (rule LIMSEQ_SEQ_conv2)
next
  assume "(X -- a --> L)"
  show "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L" by (rule LIMSEQ_SEQ_conv1)
qed

end
