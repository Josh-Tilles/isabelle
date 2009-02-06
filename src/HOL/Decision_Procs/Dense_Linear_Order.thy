(*  Title       : HOL/Dense_Linear_Order.thy
    Author      : Amine Chaieb, TU Muenchen
*)

header {* Dense linear order without endpoints
  and a quantifier elimination procedure in Ferrante and Rackoff style *}

theory Dense_Linear_Order
imports Plain Groebner_Basis Main
uses
  "~~/src/HOL/Tools/Qelim/langford_data.ML"
  "~~/src/HOL/Tools/Qelim/ferrante_rackoff_data.ML"
  ("~~/src/HOL/Tools/Qelim/langford.ML")
  ("~~/src/HOL/Tools/Qelim/ferrante_rackoff.ML")
begin

setup {* Langford_Data.setup #> Ferrante_Rackoff_Data.setup *}

context linorder
begin

lemma less_not_permute[noatp]: "\<not> (x < y \<and> y < x)" by (simp add: not_less linear)

lemma gather_simps[noatp]: 
  shows 
  "(\<exists>x. (\<forall>y \<in> L. y < x) \<and> (\<forall>y \<in> U. x < y) \<and> x < u \<and> P x) \<longleftrightarrow> (\<exists>x. (\<forall>y \<in> L. y < x) \<and> (\<forall>y \<in> (insert u U). x < y) \<and> P x)"
  and "(\<exists>x. (\<forall>y \<in> L. y < x) \<and> (\<forall>y \<in> U. x < y) \<and> l < x \<and> P x) \<longleftrightarrow> (\<exists>x. (\<forall>y \<in> (insert l L). y < x) \<and> (\<forall>y \<in> U. x < y) \<and> P x)"
  "(\<exists>x. (\<forall>y \<in> L. y < x) \<and> (\<forall>y \<in> U. x < y) \<and> x < u) \<longleftrightarrow> (\<exists>x. (\<forall>y \<in> L. y < x) \<and> (\<forall>y \<in> (insert u U). x < y))"
  and "(\<exists>x. (\<forall>y \<in> L. y < x) \<and> (\<forall>y \<in> U. x < y) \<and> l < x) \<longleftrightarrow> (\<exists>x. (\<forall>y \<in> (insert l L). y < x) \<and> (\<forall>y \<in> U. x < y))"  by auto

lemma 
  gather_start[noatp]: "(\<exists>x. P x) \<equiv> (\<exists>x. (\<forall>y \<in> {}. y < x) \<and> (\<forall>y\<in> {}. x < y) \<and> P x)" 
  by simp

text{* Theorems for @{text "\<exists>z. \<forall>x. x < z \<longrightarrow> (P x \<longleftrightarrow> P\<^bsub>-\<infinity>\<^esub>)"}*}
lemma minf_lt[noatp]:  "\<exists>z . \<forall>x. x < z \<longrightarrow> (x < t \<longleftrightarrow> True)" by auto
lemma minf_gt[noatp]: "\<exists>z . \<forall>x. x < z \<longrightarrow>  (t < x \<longleftrightarrow>  False)"
  by (simp add: not_less) (rule exI[where x="t"], auto simp add: less_le)

lemma minf_le[noatp]: "\<exists>z. \<forall>x. x < z \<longrightarrow> (x \<le> t \<longleftrightarrow> True)" by (auto simp add: less_le)
lemma minf_ge[noatp]: "\<exists>z. \<forall>x. x < z \<longrightarrow> (t \<le> x \<longleftrightarrow> False)"
  by (auto simp add: less_le not_less not_le)
lemma minf_eq[noatp]: "\<exists>z. \<forall>x. x < z \<longrightarrow> (x = t \<longleftrightarrow> False)" by auto
lemma minf_neq[noatp]: "\<exists>z. \<forall>x. x < z \<longrightarrow> (x \<noteq> t \<longleftrightarrow> True)" by auto
lemma minf_P[noatp]: "\<exists>z. \<forall>x. x < z \<longrightarrow> (P \<longleftrightarrow> P)" by blast

text{* Theorems for @{text "\<exists>z. \<forall>x. x < z \<longrightarrow> (P x \<longleftrightarrow> P\<^bsub>+\<infinity>\<^esub>)"}*}
lemma pinf_gt[noatp]:  "\<exists>z . \<forall>x. z < x \<longrightarrow> (t < x \<longleftrightarrow> True)" by auto
lemma pinf_lt[noatp]: "\<exists>z . \<forall>x. z < x \<longrightarrow>  (x < t \<longleftrightarrow>  False)"
  by (simp add: not_less) (rule exI[where x="t"], auto simp add: less_le)

lemma pinf_ge[noatp]: "\<exists>z. \<forall>x. z < x \<longrightarrow> (t \<le> x \<longleftrightarrow> True)" by (auto simp add: less_le)
lemma pinf_le[noatp]: "\<exists>z. \<forall>x. z < x \<longrightarrow> (x \<le> t \<longleftrightarrow> False)"
  by (auto simp add: less_le not_less not_le)
lemma pinf_eq[noatp]: "\<exists>z. \<forall>x. z < x \<longrightarrow> (x = t \<longleftrightarrow> False)" by auto
lemma pinf_neq[noatp]: "\<exists>z. \<forall>x. z < x \<longrightarrow> (x \<noteq> t \<longleftrightarrow> True)" by auto
lemma pinf_P[noatp]: "\<exists>z. \<forall>x. z < x \<longrightarrow> (P \<longleftrightarrow> P)" by blast

lemma nmi_lt[noatp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> x < t \<longrightarrow>  (\<exists> u\<in> U. u \<le> x)" by auto
lemma nmi_gt[noatp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and> t < x \<longrightarrow>  (\<exists> u\<in> U. u \<le> x)"
  by (auto simp add: le_less)
lemma  nmi_le[noatp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> x\<le> t \<longrightarrow>  (\<exists> u\<in> U. u \<le> x)" by auto
lemma  nmi_ge[noatp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and> t\<le> x \<longrightarrow>  (\<exists> u\<in> U. u \<le> x)" by auto
lemma  nmi_eq[noatp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and>  x = t \<longrightarrow>  (\<exists> u\<in> U. u \<le> x)" by auto
lemma  nmi_neq[noatp]: "t \<in> U \<Longrightarrow>\<forall>x. \<not>True \<and> x \<noteq> t \<longrightarrow>  (\<exists> u\<in> U. u \<le> x)" by auto
lemma  nmi_P[noatp]: "\<forall> x. ~P \<and> P \<longrightarrow>  (\<exists> u\<in> U. u \<le> x)" by auto
lemma  nmi_conj[noatp]: "\<lbrakk>\<forall>x. \<not>P1' \<and> P1 x \<longrightarrow>  (\<exists> u\<in> U. u \<le> x) ;
  \<forall>x. \<not>P2' \<and> P2 x \<longrightarrow>  (\<exists> u\<in> U. u \<le> x)\<rbrakk> \<Longrightarrow>
  \<forall>x. \<not>(P1' \<and> P2') \<and> (P1 x \<and> P2 x) \<longrightarrow>  (\<exists> u\<in> U. u \<le> x)" by auto
lemma  nmi_disj[noatp]: "\<lbrakk>\<forall>x. \<not>P1' \<and> P1 x \<longrightarrow>  (\<exists> u\<in> U. u \<le> x) ;
  \<forall>x. \<not>P2' \<and> P2 x \<longrightarrow>  (\<exists> u\<in> U. u \<le> x)\<rbrakk> \<Longrightarrow>
  \<forall>x. \<not>(P1' \<or> P2') \<and> (P1 x \<or> P2 x) \<longrightarrow>  (\<exists> u\<in> U. u \<le> x)" by auto

lemma  npi_lt[noatp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and>  x < t \<longrightarrow>  (\<exists> u\<in> U. x \<le> u)" by (auto simp add: le_less)
lemma  npi_gt[noatp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> t < x \<longrightarrow>  (\<exists> u\<in> U. x \<le> u)" by auto
lemma  npi_le[noatp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and>  x \<le> t \<longrightarrow>  (\<exists> u\<in> U. x \<le> u)" by auto
lemma  npi_ge[noatp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> t \<le> x \<longrightarrow>  (\<exists> u\<in> U. x \<le> u)" by auto
lemma  npi_eq[noatp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and>  x = t \<longrightarrow>  (\<exists> u\<in> U. x \<le> u)" by auto
lemma  npi_neq[noatp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> x \<noteq> t \<longrightarrow>  (\<exists> u\<in> U. x \<le> u )" by auto
lemma  npi_P[noatp]: "\<forall> x. ~P \<and> P \<longrightarrow>  (\<exists> u\<in> U. x \<le> u)" by auto
lemma  npi_conj[noatp]: "\<lbrakk>\<forall>x. \<not>P1' \<and> P1 x \<longrightarrow>  (\<exists> u\<in> U. x \<le> u) ;  \<forall>x. \<not>P2' \<and> P2 x \<longrightarrow>  (\<exists> u\<in> U. x \<le> u)\<rbrakk>
  \<Longrightarrow>  \<forall>x. \<not>(P1' \<and> P2') \<and> (P1 x \<and> P2 x) \<longrightarrow>  (\<exists> u\<in> U. x \<le> u)" by auto
lemma  npi_disj[noatp]: "\<lbrakk>\<forall>x. \<not>P1' \<and> P1 x \<longrightarrow>  (\<exists> u\<in> U. x \<le> u) ; \<forall>x. \<not>P2' \<and> P2 x \<longrightarrow>  (\<exists> u\<in> U. x \<le> u)\<rbrakk>
  \<Longrightarrow> \<forall>x. \<not>(P1' \<or> P2') \<and> (P1 x \<or> P2 x) \<longrightarrow>  (\<exists> u\<in> U. x \<le> u)" by auto

lemma lin_dense_lt[noatp]: "t \<in> U \<Longrightarrow> \<forall>x l u. (\<forall> t. l < t \<and> t < u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> x < t \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> y < t)"
proof(clarsimp)
  fix x l u y  assume tU: "t \<in> U" and noU: "\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U" and lx: "l < x"
    and xu: "x<u"  and px: "x < t" and ly: "l<y" and yu:"y < u"
  from tU noU ly yu have tny: "t\<noteq>y" by auto
  {assume H: "t < y"
    from less_trans[OF lx px] less_trans[OF H yu]
    have "l < t \<and> t < u"  by simp
    with tU noU have "False" by auto}
  hence "\<not> t < y"  by auto hence "y \<le> t" by (simp add: not_less)
  thus "y < t" using tny by (simp add: less_le)
qed

lemma lin_dense_gt[noatp]: "t \<in> U \<Longrightarrow> \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l < x \<and> x < u \<and> t < x \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> t < y)"
proof(clarsimp)
  fix x l u y
  assume tU: "t \<in> U" and noU: "\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U" and lx: "l < x" and xu: "x<u"
  and px: "t < x" and ly: "l<y" and yu:"y < u"
  from tU noU ly yu have tny: "t\<noteq>y" by auto
  {assume H: "y< t"
    from less_trans[OF ly H] less_trans[OF px xu] have "l < t \<and> t < u" by simp
    with tU noU have "False" by auto}
  hence "\<not> y<t"  by auto hence "t \<le> y" by (auto simp add: not_less)
  thus "t < y" using tny by (simp add:less_le)
qed

lemma lin_dense_le[noatp]: "t \<in> U \<Longrightarrow> \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> x \<le> t \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> y\<le> t)"
proof(clarsimp)
  fix x l u y
  assume tU: "t \<in> U" and noU: "\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U" and lx: "l < x" and xu: "x<u"
  and px: "x \<le> t" and ly: "l<y" and yu:"y < u"
  from tU noU ly yu have tny: "t\<noteq>y" by auto
  {assume H: "t < y"
    from less_le_trans[OF lx px] less_trans[OF H yu]
    have "l < t \<and> t < u" by simp
    with tU noU have "False" by auto}
  hence "\<not> t < y"  by auto thus "y \<le> t" by (simp add: not_less)
qed

lemma lin_dense_ge[noatp]: "t \<in> U \<Longrightarrow> \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> t \<le> x \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> t \<le> y)"
proof(clarsimp)
  fix x l u y
  assume tU: "t \<in> U" and noU: "\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U" and lx: "l < x" and xu: "x<u"
  and px: "t \<le> x" and ly: "l<y" and yu:"y < u"
  from tU noU ly yu have tny: "t\<noteq>y" by auto
  {assume H: "y< t"
    from less_trans[OF ly H] le_less_trans[OF px xu]
    have "l < t \<and> t < u" by simp
    with tU noU have "False" by auto}
  hence "\<not> y<t"  by auto thus "t \<le> y" by (simp add: not_less)
qed
lemma lin_dense_eq[noatp]: "t \<in> U \<Longrightarrow> \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> x = t   \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> y= t)"  by auto
lemma lin_dense_neq[noatp]: "t \<in> U \<Longrightarrow> \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> x \<noteq> t   \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> y\<noteq> t)"  by auto
lemma lin_dense_P[noatp]: "\<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> P   \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> P)"  by auto

lemma lin_dense_conj[noatp]:
  "\<lbrakk>\<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> P1 x
  \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> P1 y) ;
  \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> P2 x
  \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> P2 y)\<rbrakk> \<Longrightarrow>
  \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> (P1 x \<and> P2 x)
  \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> (P1 y \<and> P2 y))"
  by blast
lemma lin_dense_disj[noatp]:
  "\<lbrakk>\<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> P1 x
  \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> P1 y) ;
  \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> P2 x
  \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> P2 y)\<rbrakk> \<Longrightarrow>
  \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> (P1 x \<or> P2 x)
  \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> (P1 y \<or> P2 y))"
  by blast

lemma npmibnd[noatp]: "\<lbrakk>\<forall>x. \<not> MP \<and> P x \<longrightarrow> (\<exists> u\<in> U. u \<le> x); \<forall>x. \<not>PP \<and> P x \<longrightarrow> (\<exists> u\<in> U. x \<le> u)\<rbrakk>
  \<Longrightarrow> \<forall>x. \<not> MP \<and> \<not>PP \<and> P x \<longrightarrow> (\<exists> u\<in> U. \<exists> u' \<in> U. u \<le> x \<and> x \<le> u')"
by auto

lemma finite_set_intervals[noatp]:
  assumes px: "P x" and lx: "l \<le> x" and xu: "x \<le> u" and linS: "l\<in> S"
  and uinS: "u \<in> S" and fS:"finite S" and lS: "\<forall> x\<in> S. l \<le> x" and Su: "\<forall> x\<in> S. x \<le> u"
  shows "\<exists> a \<in> S. \<exists> b \<in> S. (\<forall> y. a < y \<and> y < b \<longrightarrow> y \<notin> S) \<and> a \<le> x \<and> x \<le> b \<and> P x"
proof-
  let ?Mx = "{y. y\<in> S \<and> y \<le> x}"
  let ?xM = "{y. y\<in> S \<and> x \<le> y}"
  let ?a = "Max ?Mx"
  let ?b = "Min ?xM"
  have MxS: "?Mx \<subseteq> S" by blast
  hence fMx: "finite ?Mx" using fS finite_subset by auto
  from lx linS have linMx: "l \<in> ?Mx" by blast
  hence Mxne: "?Mx \<noteq> {}" by blast
  have xMS: "?xM \<subseteq> S" by blast
  hence fxM: "finite ?xM" using fS finite_subset by auto
  from xu uinS have linxM: "u \<in> ?xM" by blast
  hence xMne: "?xM \<noteq> {}" by blast
  have ax:"?a \<le> x" using Mxne fMx by auto
  have xb:"x \<le> ?b" using xMne fxM by auto
  have "?a \<in> ?Mx" using Max_in[OF fMx Mxne] by simp hence ainS: "?a \<in> S" using MxS by blast
  have "?b \<in> ?xM" using Min_in[OF fxM xMne] by simp hence binS: "?b \<in> S" using xMS by blast
  have noy:"\<forall> y. ?a < y \<and> y < ?b \<longrightarrow> y \<notin> S"
  proof(clarsimp)
    fix y   assume ay: "?a < y" and yb: "y < ?b" and yS: "y \<in> S"
    from yS have "y\<in> ?Mx \<or> y\<in> ?xM" by (auto simp add: linear)
    moreover {assume "y \<in> ?Mx" hence "y \<le> ?a" using Mxne fMx by auto with ay have "False" by (simp add: not_le[symmetric])}
    moreover {assume "y \<in> ?xM" hence "?b \<le> y" using xMne fxM by auto with yb have "False" by (simp add: not_le[symmetric])}
    ultimately show "False" by blast
  qed
  from ainS binS noy ax xb px show ?thesis by blast
qed

lemma finite_set_intervals2[noatp]:
  assumes px: "P x" and lx: "l \<le> x" and xu: "x \<le> u" and linS: "l\<in> S"
  and uinS: "u \<in> S" and fS:"finite S" and lS: "\<forall> x\<in> S. l \<le> x" and Su: "\<forall> x\<in> S. x \<le> u"
  shows "(\<exists> s\<in> S. P s) \<or> (\<exists> a \<in> S. \<exists> b \<in> S. (\<forall> y. a < y \<and> y < b \<longrightarrow> y \<notin> S) \<and> a < x \<and> x < b \<and> P x)"
proof-
  from finite_set_intervals[where P="P", OF px lx xu linS uinS fS lS Su]
  obtain a and b where
    as: "a\<in> S" and bs: "b\<in> S" and noS:"\<forall>y. a < y \<and> y < b \<longrightarrow> y \<notin> S"
    and axb: "a \<le> x \<and> x \<le> b \<and> P x"  by auto
  from axb have "x= a \<or> x= b \<or> (a < x \<and> x < b)" by (auto simp add: le_less)
  thus ?thesis using px as bs noS by blast
qed

end

section {* The classical QE after Langford for dense linear orders *}

context dense_linear_order
begin

lemma interval_empty_iff:
  "{y. x < y \<and> y < z} = {} \<longleftrightarrow> \<not> x < z"
  by (auto dest: dense)

lemma dlo_qe_bnds[noatp]: 
  assumes ne: "L \<noteq> {}" and neU: "U \<noteq> {}" and fL: "finite L" and fU: "finite U"
  shows "(\<exists>x. (\<forall>y \<in> L. y < x) \<and> (\<forall>y \<in> U. x < y)) \<equiv> (\<forall> l \<in> L. \<forall>u \<in> U. l < u)"
proof (simp only: atomize_eq, rule iffI)
  assume H: "\<exists>x. (\<forall>y\<in>L. y < x) \<and> (\<forall>y\<in>U. x < y)"
  then obtain x where xL: "\<forall>y\<in>L. y < x" and xU: "\<forall>y\<in>U. x < y" by blast
  {fix l u assume l: "l \<in> L" and u: "u \<in> U"
    have "l < x" using xL l by blast
    also have "x < u" using xU u by blast
    finally (less_trans) have "l < u" .}
  thus "\<forall>l\<in>L. \<forall>u\<in>U. l < u" by blast
next
  assume H: "\<forall>l\<in>L. \<forall>u\<in>U. l < u"
  let ?ML = "Max L"
  let ?MU = "Min U"  
  from fL ne have th1: "?ML \<in> L" and th1': "\<forall>l\<in>L. l \<le> ?ML" by auto
  from fU neU have th2: "?MU \<in> U" and th2': "\<forall>u\<in>U. ?MU \<le> u" by auto
  from th1 th2 H have "?ML < ?MU" by auto
  with dense obtain w where th3: "?ML < w" and th4: "w < ?MU" by blast
  from th3 th1' have "\<forall>l \<in> L. l < w" by auto
  moreover from th4 th2' have "\<forall>u \<in> U. w < u" by auto
  ultimately show "\<exists>x. (\<forall>y\<in>L. y < x) \<and> (\<forall>y\<in>U. x < y)" by auto
qed

lemma dlo_qe_noub[noatp]: 
  assumes ne: "L \<noteq> {}" and fL: "finite L"
  shows "(\<exists>x. (\<forall>y \<in> L. y < x) \<and> (\<forall>y \<in> {}. x < y)) \<equiv> True"
proof(simp add: atomize_eq)
  from gt_ex[of "Max L"] obtain M where M: "Max L < M" by blast
  from ne fL have "\<forall>x \<in> L. x \<le> Max L" by simp
  with M have "\<forall>x\<in>L. x < M" by (auto intro: le_less_trans)
  thus "\<exists>x. \<forall>y\<in>L. y < x" by blast
qed

lemma dlo_qe_nolb[noatp]: 
  assumes ne: "U \<noteq> {}" and fU: "finite U"
  shows "(\<exists>x. (\<forall>y \<in> {}. y < x) \<and> (\<forall>y \<in> U. x < y)) \<equiv> True"
proof(simp add: atomize_eq)
  from lt_ex[of "Min U"] obtain M where M: "M < Min U" by blast
  from ne fU have "\<forall>x \<in> U. Min U \<le> x" by simp
  with M have "\<forall>x\<in>U. M < x" by (auto intro: less_le_trans)
  thus "\<exists>x. \<forall>y\<in>U. x < y" by blast
qed

lemma exists_neq[noatp]: "\<exists>(x::'a). x \<noteq> t" "\<exists>(x::'a). t \<noteq> x" 
  using gt_ex[of t] by auto

lemmas dlo_simps[noatp] = order_refl less_irrefl not_less not_le exists_neq 
  le_less neq_iff linear less_not_permute

lemma axiom[noatp]: "dense_linear_order (op \<le>) (op <)" by (rule dense_linear_order_axioms)
lemma atoms[noatp]:
  shows "TERM (less :: 'a \<Rightarrow> _)"
    and "TERM (less_eq :: 'a \<Rightarrow> _)"
    and "TERM (op = :: 'a \<Rightarrow> _)" .

declare axiom[langford qe: dlo_qe_bnds dlo_qe_nolb dlo_qe_noub gather: gather_start gather_simps atoms: atoms]
declare dlo_simps[langfordsimp]

end

(* FIXME: Move to HOL -- together with the conj_aci_rule in langford.ML *)
lemma dnf[noatp]:
  "(P & (Q | R)) = ((P&Q) | (P&R))" 
  "((Q | R) & P) = ((Q&P) | (R&P))"
  by blast+

lemmas weak_dnf_simps[noatp] = simp_thms dnf

lemma nnf_simps[noatp]:
    "(\<not>(P \<and> Q)) = (\<not>P \<or> \<not>Q)" "(\<not>(P \<or> Q)) = (\<not>P \<and> \<not>Q)" "(P \<longrightarrow> Q) = (\<not>P \<or> Q)"
    "(P = Q) = ((P \<and> Q) \<or> (\<not>P \<and> \<not> Q))" "(\<not> \<not>(P)) = P"
  by blast+

lemma ex_distrib[noatp]: "(\<exists>x. P x \<or> Q x) \<longleftrightarrow> ((\<exists>x. P x) \<or> (\<exists>x. Q x))" by blast

lemmas dnf_simps[noatp] = weak_dnf_simps nnf_simps ex_distrib

use "~~/src/HOL/Tools/Qelim/langford.ML"
method_setup dlo = {*
  Method.ctxt_args (Method.SIMPLE_METHOD' o LangfordQE.dlo_tac)
*} "Langford's algorithm for quantifier elimination in dense linear orders"


section {* Contructive dense linear orders yield QE for linear arithmetic over ordered Fields -- see @{text "Arith_Tools.thy"} *}

text {* Linear order without upper bounds *}

locale linorder_stupid_syntax = linorder
begin
notation
  less_eq  ("op \<sqsubseteq>") and
  less_eq  ("(_/ \<sqsubseteq> _)" [51, 51] 50) and
  less  ("op \<sqsubset>") and
  less  ("(_/ \<sqsubset> _)"  [51, 51] 50)

end

locale linorder_no_ub = linorder_stupid_syntax +
  assumes gt_ex: "\<exists>y. less x y"
begin
lemma ge_ex[noatp]: "\<exists>y. x \<sqsubseteq> y" using gt_ex by auto

text {* Theorems for @{text "\<exists>z. \<forall>x. z \<sqsubset> x \<longrightarrow> (P x \<longleftrightarrow> P\<^bsub>+\<infinity>\<^esub>)"} *}
lemma pinf_conj[noatp]:
  assumes ex1: "\<exists>z1. \<forall>x. z1 \<sqsubset> x \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
  and ex2: "\<exists>z2. \<forall>x. z2 \<sqsubset> x \<longrightarrow> (P2 x \<longleftrightarrow> P2')"
  shows "\<exists>z. \<forall>x. z \<sqsubset>  x \<longrightarrow> ((P1 x \<and> P2 x) \<longleftrightarrow> (P1' \<and> P2'))"
proof-
  from ex1 ex2 obtain z1 and z2 where z1: "\<forall>x. z1 \<sqsubset> x \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
     and z2: "\<forall>x. z2 \<sqsubset> x \<longrightarrow> (P2 x \<longleftrightarrow> P2')" by blast
  from gt_ex obtain z where z:"ord.max less_eq z1 z2 \<sqsubset> z" by blast
  from z have zz1: "z1 \<sqsubset> z" and zz2: "z2 \<sqsubset> z" by simp_all
  {fix x assume H: "z \<sqsubset> x"
    from less_trans[OF zz1 H] less_trans[OF zz2 H]
    have "(P1 x \<and> P2 x) \<longleftrightarrow> (P1' \<and> P2')"  using z1 zz1 z2 zz2 by auto
  }
  thus ?thesis by blast
qed

lemma pinf_disj[noatp]:
  assumes ex1: "\<exists>z1. \<forall>x. z1 \<sqsubset> x \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
  and ex2: "\<exists>z2. \<forall>x. z2 \<sqsubset> x \<longrightarrow> (P2 x \<longleftrightarrow> P2')"
  shows "\<exists>z. \<forall>x. z \<sqsubset>  x \<longrightarrow> ((P1 x \<or> P2 x) \<longleftrightarrow> (P1' \<or> P2'))"
proof-
  from ex1 ex2 obtain z1 and z2 where z1: "\<forall>x. z1 \<sqsubset> x \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
     and z2: "\<forall>x. z2 \<sqsubset> x \<longrightarrow> (P2 x \<longleftrightarrow> P2')" by blast
  from gt_ex obtain z where z:"ord.max less_eq z1 z2 \<sqsubset> z" by blast
  from z have zz1: "z1 \<sqsubset> z" and zz2: "z2 \<sqsubset> z" by simp_all
  {fix x assume H: "z \<sqsubset> x"
    from less_trans[OF zz1 H] less_trans[OF zz2 H]
    have "(P1 x \<or> P2 x) \<longleftrightarrow> (P1' \<or> P2')"  using z1 zz1 z2 zz2 by auto
  }
  thus ?thesis by blast
qed

lemma pinf_ex[noatp]: assumes ex:"\<exists>z. \<forall>x. z \<sqsubset> x \<longrightarrow> (P x \<longleftrightarrow> P1)" and p1: P1 shows "\<exists> x. P x"
proof-
  from ex obtain z where z: "\<forall>x. z \<sqsubset> x \<longrightarrow> (P x \<longleftrightarrow> P1)" by blast
  from gt_ex obtain x where x: "z \<sqsubset> x" by blast
  from z x p1 show ?thesis by blast
qed

end

text {* Linear order without upper bounds *}

locale linorder_no_lb = linorder_stupid_syntax +
  assumes lt_ex: "\<exists>y. less y x"
begin
lemma le_ex[noatp]: "\<exists>y. y \<sqsubseteq> x" using lt_ex by auto


text {* Theorems for @{text "\<exists>z. \<forall>x. x \<sqsubset> z \<longrightarrow> (P x \<longleftrightarrow> P\<^bsub>-\<infinity>\<^esub>)"} *}
lemma minf_conj[noatp]:
  assumes ex1: "\<exists>z1. \<forall>x. x \<sqsubset> z1 \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
  and ex2: "\<exists>z2. \<forall>x. x \<sqsubset> z2 \<longrightarrow> (P2 x \<longleftrightarrow> P2')"
  shows "\<exists>z. \<forall>x. x \<sqsubset>  z \<longrightarrow> ((P1 x \<and> P2 x) \<longleftrightarrow> (P1' \<and> P2'))"
proof-
  from ex1 ex2 obtain z1 and z2 where z1: "\<forall>x. x \<sqsubset> z1 \<longrightarrow> (P1 x \<longleftrightarrow> P1')"and z2: "\<forall>x. x \<sqsubset> z2 \<longrightarrow> (P2 x \<longleftrightarrow> P2')" by blast
  from lt_ex obtain z where z:"z \<sqsubset> ord.min less_eq z1 z2" by blast
  from z have zz1: "z \<sqsubset> z1" and zz2: "z \<sqsubset> z2" by simp_all
  {fix x assume H: "x \<sqsubset> z"
    from less_trans[OF H zz1] less_trans[OF H zz2]
    have "(P1 x \<and> P2 x) \<longleftrightarrow> (P1' \<and> P2')"  using z1 zz1 z2 zz2 by auto
  }
  thus ?thesis by blast
qed

lemma minf_disj[noatp]:
  assumes ex1: "\<exists>z1. \<forall>x. x \<sqsubset> z1 \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
  and ex2: "\<exists>z2. \<forall>x. x \<sqsubset> z2 \<longrightarrow> (P2 x \<longleftrightarrow> P2')"
  shows "\<exists>z. \<forall>x. x \<sqsubset>  z \<longrightarrow> ((P1 x \<or> P2 x) \<longleftrightarrow> (P1' \<or> P2'))"
proof-
  from ex1 ex2 obtain z1 and z2 where z1: "\<forall>x. x \<sqsubset> z1 \<longrightarrow> (P1 x \<longleftrightarrow> P1')"and z2: "\<forall>x. x \<sqsubset> z2 \<longrightarrow> (P2 x \<longleftrightarrow> P2')" by blast
  from lt_ex obtain z where z:"z \<sqsubset> ord.min less_eq z1 z2" by blast
  from z have zz1: "z \<sqsubset> z1" and zz2: "z \<sqsubset> z2" by simp_all
  {fix x assume H: "x \<sqsubset> z"
    from less_trans[OF H zz1] less_trans[OF H zz2]
    have "(P1 x \<or> P2 x) \<longleftrightarrow> (P1' \<or> P2')"  using z1 zz1 z2 zz2 by auto
  }
  thus ?thesis by blast
qed

lemma minf_ex[noatp]: assumes ex:"\<exists>z. \<forall>x. x \<sqsubset> z \<longrightarrow> (P x \<longleftrightarrow> P1)" and p1: P1 shows "\<exists> x. P x"
proof-
  from ex obtain z where z: "\<forall>x. x \<sqsubset> z \<longrightarrow> (P x \<longleftrightarrow> P1)" by blast
  from lt_ex obtain x where x: "x \<sqsubset> z" by blast
  from z x p1 show ?thesis by blast
qed

end


locale constr_dense_linear_order = linorder_no_lb + linorder_no_ub +
  fixes between
  assumes between_less: "less x y \<Longrightarrow> less x (between x y) \<and> less (between x y) y"
     and  between_same: "between x x = x"

sublocale  constr_dense_linear_order < dense_linear_order 
  apply unfold_locales
  using gt_ex lt_ex between_less
    by (auto, rule_tac x="between x y" in exI, simp)

context  constr_dense_linear_order
begin

lemma rinf_U[noatp]:
  assumes fU: "finite U"
  and lin_dense: "\<forall>x l u. (\<forall> t. l \<sqsubset> t \<and> t\<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l\<sqsubset> x \<and> x \<sqsubset> u \<and> P x
  \<longrightarrow> (\<forall> y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> P y )"
  and nmpiU: "\<forall>x. \<not> MP \<and> \<not>PP \<and> P x \<longrightarrow> (\<exists> u\<in> U. \<exists> u' \<in> U. u \<sqsubseteq> x \<and> x \<sqsubseteq> u')"
  and nmi: "\<not> MP"  and npi: "\<not> PP"  and ex: "\<exists> x.  P x"
  shows "\<exists> u\<in> U. \<exists> u' \<in> U. P (between u u')"
proof-
  from ex obtain x where px: "P x" by blast
  from px nmi npi nmpiU have "\<exists> u\<in> U. \<exists> u' \<in> U. u \<sqsubseteq> x \<and> x \<sqsubseteq> u'" by auto
  then obtain u and u' where uU:"u\<in> U" and uU': "u' \<in> U" and ux:"u \<sqsubseteq> x" and xu':"x \<sqsubseteq> u'" by auto
  from uU have Une: "U \<noteq> {}" by auto
  term "linorder.Min less_eq"
  let ?l = "linorder.Min less_eq U"
  let ?u = "linorder.Max less_eq U"
  have linM: "?l \<in> U" using fU Une by simp
  have uinM: "?u \<in> U" using fU Une by simp
  have lM: "\<forall> t\<in> U. ?l \<sqsubseteq> t" using Une fU by auto
  have Mu: "\<forall> t\<in> U. t \<sqsubseteq> ?u" using Une fU by auto
  have th:"?l \<sqsubseteq> u" using uU Une lM by auto
  from order_trans[OF th ux] have lx: "?l \<sqsubseteq> x" .
  have th: "u' \<sqsubseteq> ?u" using uU' Une Mu by simp
  from order_trans[OF xu' th] have xu: "x \<sqsubseteq> ?u" .
  from finite_set_intervals2[where P="P",OF px lx xu linM uinM fU lM Mu]
  have "(\<exists> s\<in> U. P s) \<or>
      (\<exists> t1\<in> U. \<exists> t2 \<in> U. (\<forall> y. t1 \<sqsubset> y \<and> y \<sqsubset> t2 \<longrightarrow> y \<notin> U) \<and> t1 \<sqsubset> x \<and> x \<sqsubset> t2 \<and> P x)" .
  moreover { fix u assume um: "u\<in>U" and pu: "P u"
    have "between u u = u" by (simp add: between_same)
    with um pu have "P (between u u)" by simp
    with um have ?thesis by blast}
  moreover{
    assume "\<exists> t1\<in> U. \<exists> t2 \<in> U. (\<forall> y. t1 \<sqsubset> y \<and> y \<sqsubset> t2 \<longrightarrow> y \<notin> U) \<and> t1 \<sqsubset> x \<and> x \<sqsubset> t2 \<and> P x"
      then obtain t1 and t2 where t1M: "t1 \<in> U" and t2M: "t2\<in> U"
        and noM: "\<forall> y. t1 \<sqsubset> y \<and> y \<sqsubset> t2 \<longrightarrow> y \<notin> U" and t1x: "t1 \<sqsubset> x" and xt2: "x \<sqsubset> t2" and px: "P x"
        by blast
      from less_trans[OF t1x xt2] have t1t2: "t1 \<sqsubset> t2" .
      let ?u = "between t1 t2"
      from between_less t1t2 have t1lu: "t1 \<sqsubset> ?u" and ut2: "?u \<sqsubset> t2" by auto
      from lin_dense noM t1x xt2 px t1lu ut2 have "P ?u" by blast
      with t1M t2M have ?thesis by blast}
    ultimately show ?thesis by blast
  qed

theorem fr_eq[noatp]:
  assumes fU: "finite U"
  and lin_dense: "\<forall>x l u. (\<forall> t. l \<sqsubset> t \<and> t\<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l\<sqsubset> x \<and> x \<sqsubset> u \<and> P x
   \<longrightarrow> (\<forall> y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> P y )"
  and nmibnd: "\<forall>x. \<not> MP \<and> P x \<longrightarrow> (\<exists> u\<in> U. u \<sqsubseteq> x)"
  and npibnd: "\<forall>x. \<not>PP \<and> P x \<longrightarrow> (\<exists> u\<in> U. x \<sqsubseteq> u)"
  and mi: "\<exists>z. \<forall>x. x \<sqsubset> z \<longrightarrow> (P x = MP)"  and pi: "\<exists>z. \<forall>x. z \<sqsubset> x \<longrightarrow> (P x = PP)"
  shows "(\<exists> x. P x) \<equiv> (MP \<or> PP \<or> (\<exists> u \<in> U. \<exists> u'\<in> U. P (between u u')))"
  (is "_ \<equiv> (_ \<or> _ \<or> ?F)" is "?E \<equiv> ?D")
proof-
 {
   assume px: "\<exists> x. P x"
   have "MP \<or> PP \<or> (\<not> MP \<and> \<not> PP)" by blast
   moreover {assume "MP \<or> PP" hence "?D" by blast}
   moreover {assume nmi: "\<not> MP" and npi: "\<not> PP"
     from npmibnd[OF nmibnd npibnd]
     have nmpiU: "\<forall>x. \<not> MP \<and> \<not>PP \<and> P x \<longrightarrow> (\<exists> u\<in> U. \<exists> u' \<in> U. u \<sqsubseteq> x \<and> x \<sqsubseteq> u')" .
     from rinf_U[OF fU lin_dense nmpiU nmi npi px] have "?D" by blast}
   ultimately have "?D" by blast}
 moreover
 { assume "?D"
   moreover {assume m:"MP" from minf_ex[OF mi m] have "?E" .}
   moreover {assume p: "PP" from pinf_ex[OF pi p] have "?E" . }
   moreover {assume f:"?F" hence "?E" by blast}
   ultimately have "?E" by blast}
 ultimately have "?E = ?D" by blast thus "?E \<equiv> ?D" by simp
qed

lemmas minf_thms[noatp] = minf_conj minf_disj minf_eq minf_neq minf_lt minf_le minf_gt minf_ge minf_P
lemmas pinf_thms[noatp] = pinf_conj pinf_disj pinf_eq pinf_neq pinf_lt pinf_le pinf_gt pinf_ge pinf_P

lemmas nmi_thms[noatp] = nmi_conj nmi_disj nmi_eq nmi_neq nmi_lt nmi_le nmi_gt nmi_ge nmi_P
lemmas npi_thms[noatp] = npi_conj npi_disj npi_eq npi_neq npi_lt npi_le npi_gt npi_ge npi_P
lemmas lin_dense_thms[noatp] = lin_dense_conj lin_dense_disj lin_dense_eq lin_dense_neq lin_dense_lt lin_dense_le lin_dense_gt lin_dense_ge lin_dense_P

lemma ferrack_axiom[noatp]: "constr_dense_linear_order less_eq less between"
  by (rule constr_dense_linear_order_axioms)
lemma atoms[noatp]:
  shows "TERM (less :: 'a \<Rightarrow> _)"
    and "TERM (less_eq :: 'a \<Rightarrow> _)"
    and "TERM (op = :: 'a \<Rightarrow> _)" .

declare ferrack_axiom [ferrack minf: minf_thms pinf: pinf_thms
    nmi: nmi_thms npi: npi_thms lindense:
    lin_dense_thms qe: fr_eq atoms: atoms]

declaration {*
let
fun simps phi = map (Morphism.thm phi) [@{thm "not_less"}, @{thm "not_le"}]
fun generic_whatis phi =
 let
  val [lt, le] = map (Morphism.term phi) [@{term "op \<sqsubset>"}, @{term "op \<sqsubseteq>"}]
  fun h x t =
   case term_of t of
     Const("op =", _)$y$z => if term_of x aconv y then Ferrante_Rackoff_Data.Eq
                            else Ferrante_Rackoff_Data.Nox
   | @{term "Not"}$(Const("op =", _)$y$z) => if term_of x aconv y then Ferrante_Rackoff_Data.NEq
                            else Ferrante_Rackoff_Data.Nox
   | b$y$z => if Term.could_unify (b, lt) then
                 if term_of x aconv y then Ferrante_Rackoff_Data.Lt
                 else if term_of x aconv z then Ferrante_Rackoff_Data.Gt
                 else Ferrante_Rackoff_Data.Nox
             else if Term.could_unify (b, le) then
                 if term_of x aconv y then Ferrante_Rackoff_Data.Le
                 else if term_of x aconv z then Ferrante_Rackoff_Data.Ge
                 else Ferrante_Rackoff_Data.Nox
             else Ferrante_Rackoff_Data.Nox
   | _ => Ferrante_Rackoff_Data.Nox
 in h end
 fun ss phi = HOL_ss addsimps (simps phi)
in
 Ferrante_Rackoff_Data.funs  @{thm "ferrack_axiom"}
  {isolate_conv = K (K (K Thm.reflexive)), whatis = generic_whatis, simpset = ss}
end
*}

end

use "~~/src/HOL/Tools/Qelim/ferrante_rackoff.ML"

method_setup ferrack = {*
  Method.ctxt_args (Method.SIMPLE_METHOD' o FerranteRackoff.dlo_tac)
*} "Ferrante and Rackoff's algorithm for quantifier elimination in dense linear orders"

subsection {* Ferrante and Rackoff algorithm over ordered fields *}

lemma neg_prod_lt:"(c\<Colon>'a\<Colon>ordered_field) < 0 \<Longrightarrow> ((c*x < 0) == (x > 0))"
proof-
  assume H: "c < 0"
  have "c*x < 0 = (0/c < x)" by (simp only: neg_divide_less_eq[OF H] algebra_simps)
  also have "\<dots> = (0 < x)" by simp
  finally show  "(c*x < 0) == (x > 0)" by simp
qed

lemma pos_prod_lt:"(c\<Colon>'a\<Colon>ordered_field) > 0 \<Longrightarrow> ((c*x < 0) == (x < 0))"
proof-
  assume H: "c > 0"
  hence "c*x < 0 = (0/c > x)" by (simp only: pos_less_divide_eq[OF H] algebra_simps)
  also have "\<dots> = (0 > x)" by simp
  finally show  "(c*x < 0) == (x < 0)" by simp
qed

lemma neg_prod_sum_lt: "(c\<Colon>'a\<Colon>ordered_field) < 0 \<Longrightarrow> ((c*x + t< 0) == (x > (- 1/c)*t))"
proof-
  assume H: "c < 0"
  have "c*x + t< 0 = (c*x < -t)" by (subst less_iff_diff_less_0 [of "c*x" "-t"], simp)
  also have "\<dots> = (-t/c < x)" by (simp only: neg_divide_less_eq[OF H] algebra_simps)
  also have "\<dots> = ((- 1/c)*t < x)" by simp
  finally show  "(c*x + t < 0) == (x > (- 1/c)*t)" by simp
qed

lemma pos_prod_sum_lt:"(c\<Colon>'a\<Colon>ordered_field) > 0 \<Longrightarrow> ((c*x + t < 0) == (x < (- 1/c)*t))"
proof-
  assume H: "c > 0"
  have "c*x + t< 0 = (c*x < -t)"  by (subst less_iff_diff_less_0 [of "c*x" "-t"], simp)
  also have "\<dots> = (-t/c > x)" by (simp only: pos_less_divide_eq[OF H] algebra_simps)
  also have "\<dots> = ((- 1/c)*t > x)" by simp
  finally show  "(c*x + t < 0) == (x < (- 1/c)*t)" by simp
qed

lemma sum_lt:"((x::'a::pordered_ab_group_add) + t < 0) == (x < - t)"
  using less_diff_eq[where a= x and b=t and c=0] by simp

lemma neg_prod_le:"(c\<Colon>'a\<Colon>ordered_field) < 0 \<Longrightarrow> ((c*x <= 0) == (x >= 0))"
proof-
  assume H: "c < 0"
  have "c*x <= 0 = (0/c <= x)" by (simp only: neg_divide_le_eq[OF H] algebra_simps)
  also have "\<dots> = (0 <= x)" by simp
  finally show  "(c*x <= 0) == (x >= 0)" by simp
qed

lemma pos_prod_le:"(c\<Colon>'a\<Colon>ordered_field) > 0 \<Longrightarrow> ((c*x <= 0) == (x <= 0))"
proof-
  assume H: "c > 0"
  hence "c*x <= 0 = (0/c >= x)" by (simp only: pos_le_divide_eq[OF H] algebra_simps)
  also have "\<dots> = (0 >= x)" by simp
  finally show  "(c*x <= 0) == (x <= 0)" by simp
qed

lemma neg_prod_sum_le: "(c\<Colon>'a\<Colon>ordered_field) < 0 \<Longrightarrow> ((c*x + t <= 0) == (x >= (- 1/c)*t))"
proof-
  assume H: "c < 0"
  have "c*x + t <= 0 = (c*x <= -t)"  by (subst le_iff_diff_le_0 [of "c*x" "-t"], simp)
  also have "\<dots> = (-t/c <= x)" by (simp only: neg_divide_le_eq[OF H] algebra_simps)
  also have "\<dots> = ((- 1/c)*t <= x)" by simp
  finally show  "(c*x + t <= 0) == (x >= (- 1/c)*t)" by simp
qed

lemma pos_prod_sum_le:"(c\<Colon>'a\<Colon>ordered_field) > 0 \<Longrightarrow> ((c*x + t <= 0) == (x <= (- 1/c)*t))"
proof-
  assume H: "c > 0"
  have "c*x + t <= 0 = (c*x <= -t)" by (subst le_iff_diff_le_0 [of "c*x" "-t"], simp)
  also have "\<dots> = (-t/c >= x)" by (simp only: pos_le_divide_eq[OF H] algebra_simps)
  also have "\<dots> = ((- 1/c)*t >= x)" by simp
  finally show  "(c*x + t <= 0) == (x <= (- 1/c)*t)" by simp
qed

lemma sum_le:"((x::'a::pordered_ab_group_add) + t <= 0) == (x <= - t)"
  using le_diff_eq[where a= x and b=t and c=0] by simp

lemma nz_prod_eq:"(c\<Colon>'a\<Colon>ordered_field) \<noteq> 0 \<Longrightarrow> ((c*x = 0) == (x = 0))" by simp
lemma nz_prod_sum_eq: "(c\<Colon>'a\<Colon>ordered_field) \<noteq> 0 \<Longrightarrow> ((c*x + t = 0) == (x = (- 1/c)*t))"
proof-
  assume H: "c \<noteq> 0"
  have "c*x + t = 0 = (c*x = -t)" by (subst eq_iff_diff_eq_0 [of "c*x" "-t"], simp)
  also have "\<dots> = (x = -t/c)" by (simp only: nonzero_eq_divide_eq[OF H] algebra_simps)
  finally show  "(c*x + t = 0) == (x = (- 1/c)*t)" by simp
qed
lemma sum_eq:"((x::'a::pordered_ab_group_add) + t = 0) == (x = - t)"
  using eq_diff_eq[where a= x and b=t and c=0] by simp


interpretation class_ordered_field_dense_linear_order!: constr_dense_linear_order
 "op <=" "op <"
   "\<lambda> x y. 1/2 * ((x::'a::{ordered_field,recpower,number_ring}) + y)"
proof (unfold_locales, dlo, dlo, auto)
  fix x y::'a assume lt: "x < y"
  from  less_half_sum[OF lt] show "x < (x + y) /2" by simp
next
  fix x y::'a assume lt: "x < y"
  from  gt_half_sum[OF lt] show "(x + y) /2 < y" by simp
qed

declaration{*
let
fun earlier [] x y = false
        | earlier (h::t) x y =
    if h aconvc y then false else if h aconvc x then true else earlier t x y;

fun dest_frac ct = case term_of ct of
   Const (@{const_name "HOL.divide"},_) $ a $ b=>
    Rat.rat_of_quotient (snd (HOLogic.dest_number a), snd (HOLogic.dest_number b))
 | t => Rat.rat_of_int (snd (HOLogic.dest_number t))

fun mk_frac phi cT x =
 let val (a, b) = Rat.quotient_of_rat x
 in if b = 1 then Numeral.mk_cnumber cT a
    else Thm.capply
         (Thm.capply (Drule.cterm_rule (instantiate' [SOME cT] []) @{cpat "op /"})
                     (Numeral.mk_cnumber cT a))
         (Numeral.mk_cnumber cT b)
 end

fun whatis x ct = case term_of ct of
  Const(@{const_name "HOL.plus"}, _)$(Const(@{const_name "HOL.times"},_)$_$y)$_ =>
     if y aconv term_of x then ("c*x+t",[(funpow 2 Thm.dest_arg1) ct, Thm.dest_arg ct])
     else ("Nox",[])
| Const(@{const_name "HOL.plus"}, _)$y$_ =>
     if y aconv term_of x then ("x+t",[Thm.dest_arg ct])
     else ("Nox",[])
| Const(@{const_name "HOL.times"}, _)$_$y =>
     if y aconv term_of x then ("c*x",[Thm.dest_arg1 ct])
     else ("Nox",[])
| t => if t aconv term_of x then ("x",[]) else ("Nox",[]);

fun xnormalize_conv ctxt [] ct = reflexive ct
| xnormalize_conv ctxt (vs as (x::_)) ct =
   case term_of ct of
   Const(@{const_name HOL.less},_)$_$Const(@{const_name "HOL.zero"},_) =>
    (case whatis x (Thm.dest_arg1 ct) of
    ("c*x+t",[c,t]) =>
       let
        val cr = dest_frac c
        val clt = Thm.dest_fun2 ct
        val cz = Thm.dest_arg ct
        val neg = cr </ Rat.zero
        val cthp = Simplifier.rewrite (local_simpset_of ctxt)
               (Thm.capply @{cterm "Trueprop"}
                  (if neg then Thm.capply (Thm.capply clt c) cz
                    else Thm.capply (Thm.capply clt cz) c))
        val cth = equal_elim (symmetric cthp) TrueI
        val th = implies_elim (instantiate' [SOME (ctyp_of_term x)] (map SOME [c,x,t])
             (if neg then @{thm neg_prod_sum_lt} else @{thm pos_prod_sum_lt})) cth
        val rth = Conv.fconv_rule (Conv.arg_conv (Conv.binop_conv
                   (Normalizer.semiring_normalize_ord_conv ctxt (earlier vs)))) th
      in rth end
    | ("x+t",[t]) =>
       let
        val T = ctyp_of_term x
        val th = instantiate' [SOME T] [SOME x, SOME t] @{thm "sum_lt"}
        val rth = Conv.fconv_rule (Conv.arg_conv (Conv.binop_conv
              (Normalizer.semiring_normalize_ord_conv ctxt (earlier vs)))) th
       in  rth end
    | ("c*x",[c]) =>
       let
        val cr = dest_frac c
        val clt = Thm.dest_fun2 ct
        val cz = Thm.dest_arg ct
        val neg = cr </ Rat.zero
        val cthp = Simplifier.rewrite (local_simpset_of ctxt)
               (Thm.capply @{cterm "Trueprop"}
                  (if neg then Thm.capply (Thm.capply clt c) cz
                    else Thm.capply (Thm.capply clt cz) c))
        val cth = equal_elim (symmetric cthp) TrueI
        val th = implies_elim (instantiate' [SOME (ctyp_of_term x)] (map SOME [c,x])
             (if neg then @{thm neg_prod_lt} else @{thm pos_prod_lt})) cth
        val rth = th
      in rth end
    | _ => reflexive ct)


|  Const(@{const_name HOL.less_eq},_)$_$Const(@{const_name "HOL.zero"},_) =>
   (case whatis x (Thm.dest_arg1 ct) of
    ("c*x+t",[c,t]) =>
       let
        val T = ctyp_of_term x
        val cr = dest_frac c
        val clt = Drule.cterm_rule (instantiate' [SOME T] []) @{cpat "op <"}
        val cz = Thm.dest_arg ct
        val neg = cr </ Rat.zero
        val cthp = Simplifier.rewrite (local_simpset_of ctxt)
               (Thm.capply @{cterm "Trueprop"}
                  (if neg then Thm.capply (Thm.capply clt c) cz
                    else Thm.capply (Thm.capply clt cz) c))
        val cth = equal_elim (symmetric cthp) TrueI
        val th = implies_elim (instantiate' [SOME T] (map SOME [c,x,t])
             (if neg then @{thm neg_prod_sum_le} else @{thm pos_prod_sum_le})) cth
        val rth = Conv.fconv_rule (Conv.arg_conv (Conv.binop_conv
                   (Normalizer.semiring_normalize_ord_conv ctxt (earlier vs)))) th
      in rth end
    | ("x+t",[t]) =>
       let
        val T = ctyp_of_term x
        val th = instantiate' [SOME T] [SOME x, SOME t] @{thm "sum_le"}
        val rth = Conv.fconv_rule (Conv.arg_conv (Conv.binop_conv
              (Normalizer.semiring_normalize_ord_conv ctxt (earlier vs)))) th
       in  rth end
    | ("c*x",[c]) =>
       let
        val T = ctyp_of_term x
        val cr = dest_frac c
        val clt = Drule.cterm_rule (instantiate' [SOME T] []) @{cpat "op <"}
        val cz = Thm.dest_arg ct
        val neg = cr </ Rat.zero
        val cthp = Simplifier.rewrite (local_simpset_of ctxt)
               (Thm.capply @{cterm "Trueprop"}
                  (if neg then Thm.capply (Thm.capply clt c) cz
                    else Thm.capply (Thm.capply clt cz) c))
        val cth = equal_elim (symmetric cthp) TrueI
        val th = implies_elim (instantiate' [SOME (ctyp_of_term x)] (map SOME [c,x])
             (if neg then @{thm neg_prod_le} else @{thm pos_prod_le})) cth
        val rth = th
      in rth end
    | _ => reflexive ct)

|  Const("op =",_)$_$Const(@{const_name "HOL.zero"},_) =>
   (case whatis x (Thm.dest_arg1 ct) of
    ("c*x+t",[c,t]) =>
       let
        val T = ctyp_of_term x
        val cr = dest_frac c
        val ceq = Thm.dest_fun2 ct
        val cz = Thm.dest_arg ct
        val cthp = Simplifier.rewrite (local_simpset_of ctxt)
            (Thm.capply @{cterm "Trueprop"}
             (Thm.capply @{cterm "Not"} (Thm.capply (Thm.capply ceq c) cz)))
        val cth = equal_elim (symmetric cthp) TrueI
        val th = implies_elim
                 (instantiate' [SOME T] (map SOME [c,x,t]) @{thm nz_prod_sum_eq}) cth
        val rth = Conv.fconv_rule (Conv.arg_conv (Conv.binop_conv
                   (Normalizer.semiring_normalize_ord_conv ctxt (earlier vs)))) th
      in rth end
    | ("x+t",[t]) =>
       let
        val T = ctyp_of_term x
        val th = instantiate' [SOME T] [SOME x, SOME t] @{thm "sum_eq"}
        val rth = Conv.fconv_rule (Conv.arg_conv (Conv.binop_conv
              (Normalizer.semiring_normalize_ord_conv ctxt (earlier vs)))) th
       in  rth end
    | ("c*x",[c]) =>
       let
        val T = ctyp_of_term x
        val cr = dest_frac c
        val ceq = Thm.dest_fun2 ct
        val cz = Thm.dest_arg ct
        val cthp = Simplifier.rewrite (local_simpset_of ctxt)
            (Thm.capply @{cterm "Trueprop"}
             (Thm.capply @{cterm "Not"} (Thm.capply (Thm.capply ceq c) cz)))
        val cth = equal_elim (symmetric cthp) TrueI
        val rth = implies_elim
                 (instantiate' [SOME T] (map SOME [c,x]) @{thm nz_prod_eq}) cth
      in rth end
    | _ => reflexive ct);

local
  val less_iff_diff_less_0 = mk_meta_eq @{thm "less_iff_diff_less_0"}
  val le_iff_diff_le_0 = mk_meta_eq @{thm "le_iff_diff_le_0"}
  val eq_iff_diff_eq_0 = mk_meta_eq @{thm "eq_iff_diff_eq_0"}
in
fun field_isolate_conv phi ctxt vs ct = case term_of ct of
  Const(@{const_name HOL.less},_)$a$b =>
   let val (ca,cb) = Thm.dest_binop ct
       val T = ctyp_of_term ca
       val th = instantiate' [SOME T] [SOME ca, SOME cb] less_iff_diff_less_0
       val nth = Conv.fconv_rule
         (Conv.arg_conv (Conv.arg1_conv
              (Normalizer.semiring_normalize_ord_conv @{context} (earlier vs)))) th
       val rth = transitive nth (xnormalize_conv ctxt vs (Thm.rhs_of nth))
   in rth end
| Const(@{const_name HOL.less_eq},_)$a$b =>
   let val (ca,cb) = Thm.dest_binop ct
       val T = ctyp_of_term ca
       val th = instantiate' [SOME T] [SOME ca, SOME cb] le_iff_diff_le_0
       val nth = Conv.fconv_rule
         (Conv.arg_conv (Conv.arg1_conv
              (Normalizer.semiring_normalize_ord_conv @{context} (earlier vs)))) th
       val rth = transitive nth (xnormalize_conv ctxt vs (Thm.rhs_of nth))
   in rth end

| Const("op =",_)$a$b =>
   let val (ca,cb) = Thm.dest_binop ct
       val T = ctyp_of_term ca
       val th = instantiate' [SOME T] [SOME ca, SOME cb] eq_iff_diff_eq_0
       val nth = Conv.fconv_rule
         (Conv.arg_conv (Conv.arg1_conv
              (Normalizer.semiring_normalize_ord_conv @{context} (earlier vs)))) th
       val rth = transitive nth (xnormalize_conv ctxt vs (Thm.rhs_of nth))
   in rth end
| @{term "Not"} $(Const("op =",_)$a$b) => Conv.arg_conv (field_isolate_conv phi ctxt vs) ct
| _ => reflexive ct
end;

fun classfield_whatis phi =
 let
  fun h x t =
   case term_of t of
     Const("op =", _)$y$z => if term_of x aconv y then Ferrante_Rackoff_Data.Eq
                            else Ferrante_Rackoff_Data.Nox
   | @{term "Not"}$(Const("op =", _)$y$z) => if term_of x aconv y then Ferrante_Rackoff_Data.NEq
                            else Ferrante_Rackoff_Data.Nox
   | Const(@{const_name HOL.less},_)$y$z =>
       if term_of x aconv y then Ferrante_Rackoff_Data.Lt
        else if term_of x aconv z then Ferrante_Rackoff_Data.Gt
        else Ferrante_Rackoff_Data.Nox
   | Const (@{const_name HOL.less_eq},_)$y$z =>
         if term_of x aconv y then Ferrante_Rackoff_Data.Le
         else if term_of x aconv z then Ferrante_Rackoff_Data.Ge
         else Ferrante_Rackoff_Data.Nox
   | _ => Ferrante_Rackoff_Data.Nox
 in h end;
fun class_field_ss phi =
   HOL_basic_ss addsimps ([@{thm "linorder_not_less"}, @{thm "linorder_not_le"}])
   addsplits [@{thm "abs_split"},@{thm "split_max"}, @{thm "split_min"}]

in
Ferrante_Rackoff_Data.funs @{thm "class_ordered_field_dense_linear_order.ferrack_axiom"}
  {isolate_conv = field_isolate_conv, whatis = classfield_whatis, simpset = class_field_ss}
end
*}


end 
