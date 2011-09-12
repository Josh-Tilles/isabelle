(* Author: Tobias Nipkow *)

theory AbsInt1
imports AbsInt0_const
begin

subsection "Backward Analysis of Expressions"

class L_top_bot = SL_top +
fixes meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 65)
and Bot :: "'a"
assumes meet_le1 [simp]: "x \<sqinter> y \<sqsubseteq> x"
and meet_le2 [simp]: "x \<sqinter> y \<sqsubseteq> y"
and meet_greatest: "x \<sqsubseteq> y \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> y \<sqinter> z"
assumes bot[simp]: "Bot \<sqsubseteq> x"

locale Rep1 = Rep rep for rep :: "'a::L_top_bot \<Rightarrow> 'b set" +
assumes inter_rep_subset_rep_meet: "rep a1 \<inter> rep a2 \<subseteq> rep(a1 \<sqinter> a2)"
and rep_Bot: "rep Bot = {}"
begin

lemma in_rep_meet: "x <: a1 \<Longrightarrow> x <: a2 \<Longrightarrow> x <: a1 \<sqinter> a2"
by (metis IntI inter_rep_subset_rep_meet set_mp)

lemma rep_meet[simp]: "rep(a1 \<sqinter> a2) = rep a1 \<inter> rep a2"
by (metis equalityI inter_rep_subset_rep_meet le_inf_iff le_rep meet_le1 meet_le2)

end


locale Val_abs1 = Val_abs rep num' plus' + Rep1 rep
  for rep :: "'a::L_top_bot \<Rightarrow> int set" and num' plus' +
fixes inv_plus' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a * 'a"
and inv_less' :: "'a \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'a * 'a"
assumes inv_plus': "inv_plus' a1 a2 a = (a1',a2') \<Longrightarrow>
  n1 <: a1 \<Longrightarrow> n2 <: a2 \<Longrightarrow> n1+n2 <: a \<Longrightarrow> n1 <: a1' \<and> n2 <: a2'"
and inv_less': "inv_less' a1 a2 (n1<n2) = (a1',a2') \<Longrightarrow>
  n1 <: a1 \<Longrightarrow> n2 <: a2 \<Longrightarrow> n1 <: a1' \<and> n2 <: a2'"

datatype 'a up = bot | Up 'a

instantiation up :: (SL_top)SL_top
begin

fun le_up where
"Up x \<sqsubseteq> Up y = (x \<sqsubseteq> y)" |
"bot \<sqsubseteq> y = True" |
"Up _ \<sqsubseteq> bot = False"

lemma [simp]: "(x \<sqsubseteq> bot) = (x = bot)"
by (cases x) simp_all

lemma [simp]: "(Up x \<sqsubseteq> u) = (EX y. u = Up y & x \<sqsubseteq> y)"
by (cases u) auto

fun join_up where
"Up x \<squnion> Up y = Up(x \<squnion> y)" |
"bot \<squnion> y = y" |
"x \<squnion> bot = x"

lemma [simp]: "x \<squnion> bot = x"
by (cases x) simp_all


definition "Top = Up Top"

(* register <= as transitive - see orderings *)

instance proof
  case goal1 show ?case by(cases x, simp_all)
next
  case goal2 thus ?case
    by(cases z, simp, cases y, simp, cases x, auto intro: le_trans)
next
  case goal3 thus ?case by(cases x, simp, cases y, simp_all)
next
  case goal4 thus ?case by(cases y, simp, cases x, simp_all)
next
  case goal5 thus ?case by(cases z, simp, cases y, simp, cases x, simp_all)
next
  case goal6 thus ?case by(cases x, simp_all add: Top_up_def)
qed

end


locale Abs_Int1 = Val_abs1
begin

(* FIXME avoid duplicating this defn *)
abbreviation astate_in_rep (infix "<:" 50) where
"s <: S == ALL x. s x <: lookup S x"

abbreviation in_rep_up :: "state \<Rightarrow> 'a astate up \<Rightarrow> bool"  (infix "<::" 50) where
"s <:: S == EX S0. S = Up S0 \<and> s <: S0"

lemma in_rep_up_trans: "(s::state) <:: S \<Longrightarrow> S \<sqsubseteq> T \<Longrightarrow> s <:: T"
apply auto
by (metis in_mono le_astate_def le_rep lookup_def top)

lemma in_rep_join_UpI: "s <:: S1 | s <:: S2 \<Longrightarrow> s <:: S1 \<squnion> S2"
by (metis in_rep_up_trans SL_top_class.join_ge1 SL_top_class.join_ge2)

fun aval' :: "aexp \<Rightarrow> 'a astate up \<Rightarrow> 'a" ("aval\<^isup>#") where
"aval' _ bot = Bot" |
"aval' (N n) _ = num' n" |
"aval' (V x) (Up S) = lookup S x" |
"aval' (Plus a1 a2) S = plus' (aval' a1 S) (aval' a2 S)"

lemma aval'_sound: "s <:: S \<Longrightarrow> aval a s <: aval' a S"
by (induct a) (auto simp: rep_num' rep_plus')

fun afilter :: "aexp \<Rightarrow> 'a \<Rightarrow> 'a astate up \<Rightarrow> 'a astate up" where
"afilter (N n) a S = (if n <: a then S else bot)" |
"afilter (V x) a S = (case S of bot \<Rightarrow> bot | Up S \<Rightarrow>
  let a' = lookup S x \<sqinter> a in
  if a'\<sqsubseteq> Bot then bot else Up(update S x a'))" |
"afilter (Plus e1 e2) a S =
 (let (a1,a2) = inv_plus' (aval' e1 S) (aval' e2 S) a
  in afilter e1 a1 (afilter e2 a2 S))"

fun bfilter :: "bexp \<Rightarrow> bool \<Rightarrow> 'a astate up \<Rightarrow> 'a astate up" where
"bfilter (B bv) res S = (if bv=res then S else bot)" |
"bfilter (Not b) res S = bfilter b (\<not> res) S" |
"bfilter (And b1 b2) res S =
  (if res then bfilter b1 True (bfilter b2 True S)
   else bfilter b1 False S \<squnion> bfilter b2 False S)" |
"bfilter (Less e1 e2) res S =
  (let (res1,res2) = inv_less' (aval' e1 S) (aval' e2 S) res
   in afilter e1 res1 (afilter e2 res2 S))"

lemma afilter_sound: "s <:: S \<Longrightarrow> aval e s <: a \<Longrightarrow> s <:: afilter e a S"
proof(induct e arbitrary: a S)
  case N thus ?case by simp
next
  case (V x)
  obtain S' where "S = Up S'" and "s <: S'" using `s <:: S` by auto
  moreover hence "s x <: lookup S' x" by(simp)
  moreover have "s x <: a" using V by simp
  ultimately show ?case using V(1)
    by(simp add: lookup_update Let_def)
       (metis le_rep emptyE in_rep_meet rep_Bot subset_empty)
next
  case (Plus e1 e2) thus ?case
    using inv_plus'[OF _ aval'_sound[OF Plus(3)] aval'_sound[OF Plus(3)]]
    by (auto split: prod.split)
qed

lemma bfilter_sound: "s <:: S \<Longrightarrow> bv = bval b s \<Longrightarrow> s <:: bfilter b bv S"
proof(induct b arbitrary: S bv)
  case B thus ?case by simp
next
  case (Not b) thus ?case by simp
next
  case (And b1 b2) thus ?case by (auto simp: in_rep_join_UpI)
next
  case (Less e1 e2) thus ?case
    by (auto split: prod.split)
       (metis afilter_sound inv_less' aval'_sound Less)
qed

fun AI :: "com \<Rightarrow> 'a astate up \<Rightarrow> 'a astate up" where
"AI SKIP S = S" |
"AI (x ::= a) S =
  (case S of bot \<Rightarrow> bot | Up S \<Rightarrow> Up(update S x (aval' a (Up S))))" |
"AI (c1;c2) S = AI c2 (AI c1 S)" |
"AI (IF b THEN c1 ELSE c2) S =
  AI c1 (bfilter b True S) \<squnion> AI c2 (bfilter b False S)" |
"AI (WHILE b DO c) S =
  bfilter b False (pfp_above (%S. AI c (bfilter b True S)) S)"

lemma AI_sound: "(c,s) \<Rightarrow> t \<Longrightarrow> s <:: S \<Longrightarrow> t <:: AI c S"
proof(induct c arbitrary: s t S)
  case SKIP thus ?case by fastforce
next
  case Assign thus ?case
    by (auto simp: lookup_update aval'_sound)
next
  case Semi thus ?case by fastforce
next
  case If thus ?case by (auto simp: in_rep_join_UpI bfilter_sound)
next
  case (While b c)
  let ?P = "pfp_above (%S. AI c (bfilter b True S)) S"
  have pfp: "AI c (bfilter b True ?P) \<sqsubseteq> ?P" and "S \<sqsubseteq> ?P"
    by (rule pfp_above_pfp(1), rule pfp_above_pfp(2))
  { fix s t
    have "(WHILE b DO c,s) \<Rightarrow> t \<Longrightarrow> s <:: ?P \<Longrightarrow>
          t <:: bfilter b False ?P"
    proof(induct "WHILE b DO c" s t rule: big_step_induct)
      case WhileFalse thus ?case by(metis bfilter_sound)
    next
      case WhileTrue show ?case
        by(rule WhileTrue, rule in_rep_up_trans[OF _ pfp],
           rule While.hyps[OF WhileTrue(2)],
           rule bfilter_sound[OF WhileTrue.prems], simp add: WhileTrue(1))
    qed
  }
  with in_rep_up_trans[OF `s <:: S` `S \<sqsubseteq> ?P`] While(2,3) AI.simps(5)
  show ?case by simp
qed

text{* Exercise: *}

lemma afilter_strict: "afilter e res bot = bot"
by (induct e arbitrary: res) simp_all

lemma bfilter_strict: "bfilter b res bot = bot"
by (induct b arbitrary: res) (simp_all add: afilter_strict)

lemma pfp_strict: "f bot = bot \<Longrightarrow> pfp_above f bot = bot"
by(simp add: pfp_above_def pfp_def eval_nat_numeral)

lemma AI_strict: "AI c bot = bot"
by(induct c) (simp_all add: bfilter_strict pfp_strict)

end

end
