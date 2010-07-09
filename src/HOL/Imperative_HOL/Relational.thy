theory Relational 
imports Array Ref
begin

section{* Definition of the Relational framework *}

text {* The crel predicate states that when a computation c runs with the heap h
  will result in return value r and a heap h' (if no exception occurs). *}  

definition crel :: "'a Heap \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> 'a \<Rightarrow> bool"
where
  crel_def': "crel c h h' r \<longleftrightarrow> Heap_Monad.execute c h = Some (r, h')"

lemma crel_def: -- FIXME
  "crel c h h' r \<longleftrightarrow> Some (r, h') = Heap_Monad.execute c h"
  unfolding crel_def' by auto

lemma crel_deterministic: "\<lbrakk> crel f h h' a; crel f h h'' b \<rbrakk> \<Longrightarrow> (a = b) \<and> (h' = h'')"
unfolding crel_def' by auto

section {* Elimination rules *}

text {* For all commands, we define simple elimination rules. *}
(* FIXME: consumes 1 necessary ?? *)

lemma crel_heap:
  assumes "crel (Heap_Monad.heap f) h h' r"
  obtains "h' = snd (f h)" "r = fst (f h)"
  using assms by (cases "f h") (simp add: crel_def)

lemma crel_guard:
  assumes "crel (Heap_Monad.guard P f) h h' r"
  obtains "h' = snd (f h)" "r = fst (f h)" "P h"
  using assms by (cases "f h", cases "P h") (simp_all add: crel_def)


subsection {* Elimination rules for basic monadic commands *}

lemma crelE[consumes 1]:
  assumes "crel (f >>= g) h h'' r'"
  obtains h' r where "crel f h h' r" "crel (g r) h' h'' r'"
  using assms by (auto simp add: crel_def bind_def split: option.split_asm)

lemma crelE'[consumes 1]:
  assumes "crel (f >> g) h h'' r'"
  obtains h' r where "crel f h h' r" "crel g h' h'' r'"
  using assms
  by (elim crelE) auto

lemma crel_return[consumes 1]:
  assumes "crel (return x) h h' r"
  obtains "r = x" "h = h'"
  using assms
  unfolding crel_def return_def by simp

lemma crel_raise[consumes 1]:
  assumes "crel (raise x) h h' r"
  obtains "False"
  using assms
  unfolding crel_def raise_def by simp

lemma crel_if:
  assumes "crel (if c then t else e) h h' r"
  obtains "c" "crel t h h' r"
        | "\<not>c" "crel e h h' r"
  using assms
  unfolding crel_def by auto

lemma crel_option_case:
  assumes "crel (case x of None \<Rightarrow> n | Some y \<Rightarrow> s y) h h' r"
  obtains "x = None" "crel n h h' r"
        | y where "x = Some y" "crel (s y) h h' r" 
  using assms
  unfolding crel_def by auto

lemma crel_fold_map:
  assumes "crel (Heap_Monad.fold_map f xs) h h' r"
  assumes "\<And>h h'. P f [] h h' []"
  assumes "\<And>h h1 h' x xs y ys. \<lbrakk> crel (f x) h h1 y; crel (Heap_Monad.fold_map f xs) h1 h' ys; P f xs h1 h' ys \<rbrakk> \<Longrightarrow> P f (x#xs) h h' (y#ys)"
  shows "P f xs h h' r"
using assms(1)
proof (induct xs arbitrary: h h' r)
  case Nil  with assms(2) show ?case
    by (auto elim: crel_return)
next
  case (Cons x xs)
  from Cons(2) obtain h1 y ys where crel_f: "crel (f x) h h1 y"
    and crel_fold_map: "crel (Heap_Monad.fold_map f xs) h1 h' ys"
    and r_def: "r = y#ys"
    unfolding fold_map.simps
    by (auto elim!: crelE crel_return)
  from Cons(1)[OF crel_fold_map] crel_fold_map crel_f assms(3) r_def
  show ?case by auto
qed


subsection {* Elimination rules for array commands *}

(* Strong version of the lemma for this operation is missing *) 
lemma crel_new_weak:
  assumes "crel (Array.new n v) h h' r"
  obtains "get_array r h' = List.replicate n v"
  using assms unfolding Array.new_def
  by (elim crel_heap) (auto simp: array_def Let_def split_def)

(* Strong version of the lemma for this operation is missing *)
lemma crel_of_list_weak:
  assumes "crel (Array.of_list xs) h h' r"
  obtains "get_array r h' = xs"
  using assms unfolding of_list_def 
  by (elim crel_heap) (simp add: get_array_init_array_list)

(* Strong version of the lemma for this operation is missing *)
lemma crel_make_weak:
  assumes "crel (Array.make n f) h h' r"
  obtains "i < n \<Longrightarrow> get_array r h' ! i = f i"
  using assms unfolding Array.make_def
  by (elim crel_heap) (auto simp: array_def Let_def split_def)

lemma crel_length:
  assumes "crel (len a) h h' r"
  obtains "h = h'" "r = Array.length a h'"
  using assms unfolding Array.len_def
  by (elim crel_heap) simp

lemma crel_nth[consumes 1]:
  assumes "crel (nth a i) h h' r"
  obtains "r = get_array a h ! i" "h = h'" "i < Array.length a h"
  using assms unfolding nth_def
  by (elim crel_guard) (clarify, simp)

lemma crel_upd[consumes 1]:
  assumes "crel (upd i v a) h h' r"
  obtains "r = a" "h' = Array.change a i v h" "i < Array.length a h"
  using assms unfolding upd_def
  by (elim crel_guard) simp

lemma crel_map_entry:
  assumes "crel (Array.map_entry i f a) h h' r"
  obtains "r = a" "h' = Array.change a i (f (get_array a h ! i)) h" "i < Array.length a h"
  using assms unfolding Array.map_entry_def
  by (elim crel_guard) simp

lemma crel_swap:
  assumes "crel (Array.swap i x a) h h' r"
  obtains "r = get_array a h ! i" "h' = Array.change a i x h"
  using assms unfolding Array.swap_def
  by (elim crel_guard) simp

lemma upt_conv_Cons': (*FIXME move*)
  assumes "Suc a \<le> b"
  shows "[b - Suc a..<b] = (b - Suc a)#[b - a..<b]"
proof -
  from assms have l: "b - Suc a < b" by arith
  from assms have "Suc (b - Suc a) = b - a" by arith
  with l show ?thesis by (simp add: upt_conv_Cons)
qed

lemma crel_fold_map_nth:
  assumes
  "crel (Heap_Monad.fold_map (Array.nth a) [Array.length a h - n..<Array.length a h]) h h' xs"
  assumes "n \<le> Array.length a h"
  shows "h = h' \<and> xs = drop (Array.length a h - n) (get_array a h)"
using assms
proof (induct n arbitrary: xs h h')
  case 0 thus ?case
    by (auto elim!: crel_return simp add: Array.length_def)
next
  case (Suc n)
  from Suc(3) have "[Array.length a h - Suc n..<Array.length a h] = (Array.length a h - Suc n)#[Array.length a h - n..<Array.length a h]"
    by (simp add: upt_conv_Cons')
  with Suc(2) obtain r where
    crel_fold_map: "crel (Heap_Monad.fold_map (Array.nth a) [Array.length a h - n..<Array.length a h]) h h' r"
    and xs_def: "xs = get_array a h ! (Array.length a h - Suc n) # r"
    by (auto elim!: crelE crel_nth crel_return)
  from Suc(3) have "Array.length a h - n = Suc (Array.length a h - Suc n)" 
    by arith
  with Suc.hyps[OF crel_fold_map] xs_def show ?case
    unfolding Array.length_def
    by (auto simp add: nth_drop')
qed

lemma crel_freeze:
  assumes "crel (Array.freeze a) h h' xs"
  obtains "h = h'" "xs = get_array a h"
  using assms unfolding freeze_def
  by (elim crel_heap) simp

lemma crel_fold_map_map_entry_remains:
  assumes "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a h - n..<Array.length a h]) h h' r"
  assumes "i < Array.length a h - n"
  shows "get_array a h ! i = get_array a h' ! i"
using assms
proof (induct n arbitrary: h h' r)
  case 0
  thus ?case
    by (auto elim: crel_return)
next
  case (Suc n)
  let ?h1 = "Array.change a (Array.length a h - Suc n) (f (get_array a h ! (Array.length a h - Suc n))) h"
  from Suc(3) have "[Array.length a h - Suc n..<Array.length a h] = (Array.length a h - Suc n)#[Array.length a h - n..<Array.length a h]"
    by (simp add: upt_conv_Cons')
  from Suc(2) this obtain r where
    crel_fold_map: "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a h - n..<Array.length a h]) ?h1 h' r"
    by (auto simp add: elim!: crelE crel_map_entry crel_return)
  have length_remains: "Array.length a ?h1 = Array.length a h" by simp
  from crel_fold_map have crel_fold_map': "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a ?h1 - n..<Array.length a ?h1]) ?h1 h' r"
    by simp
  from Suc(1)[OF this] length_remains Suc(3) show ?case by simp
qed

lemma crel_fold_map_map_entry_changes:
  assumes "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a h - n..<Array.length a h]) h h' r"
  assumes "n \<le> Array.length a h"  
  assumes "i \<ge> Array.length a h - n"
  assumes "i < Array.length a h"
  shows "get_array a h' ! i = f (get_array a h ! i)"
using assms
proof (induct n arbitrary: h h' r)
  case 0
  thus ?case
    by (auto elim!: crel_return)
next
  case (Suc n)
  let ?h1 = "Array.change a (Array.length a h - Suc n) (f (get_array a h ! (Array.length a h - Suc n))) h"
  from Suc(3) have "[Array.length a h - Suc n..<Array.length a h] = (Array.length a h - Suc n)#[Array.length a h - n..<Array.length a h]"
    by (simp add: upt_conv_Cons')
  from Suc(2) this obtain r where
    crel_fold_map: "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a h - n..<Array.length a h]) ?h1 h' r"
    by (auto simp add: elim!: crelE crel_map_entry crel_return)
  have length_remains: "Array.length a ?h1 = Array.length a h" by simp
  from Suc(3) have less: "Array.length a h - Suc n < Array.length a h - n" by arith
  from Suc(3) have less2: "Array.length a h - Suc n < Array.length a h" by arith
  from Suc(4) length_remains have cases: "i = Array.length a ?h1 - Suc n \<or> i \<ge> Array.length a ?h1 - n" by arith
  from crel_fold_map have crel_fold_map': "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a ?h1 - n..<Array.length a ?h1]) ?h1 h' r"
    by simp
  from Suc(1)[OF this] cases Suc(3) Suc(5) length_remains
    crel_fold_map_map_entry_remains[OF this, of "Array.length a h - Suc n", symmetric] less less2
  show ?case
    by (auto simp add: nth_list_update_eq Array.length_def)
qed

lemma crel_fold_map_map_entry_length:
  assumes "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a h - n..<Array.length a h]) h h' r"
  assumes "n \<le> Array.length a h"
  shows "Array.length a h' = Array.length a h"
using assms
proof (induct n arbitrary: h h' r)
  case 0
  thus ?case by (auto elim!: crel_return)
next
  case (Suc n)
  let ?h1 = "Array.change a (Array.length a h - Suc n) (f (get_array a h ! (Array.length a h - Suc n))) h"
  from Suc(3) have "[Array.length a h - Suc n..<Array.length a h] = (Array.length a h - Suc n)#[Array.length a h - n..<Array.length a h]"
    by (simp add: upt_conv_Cons')
  from Suc(2) this obtain r where 
    crel_fold_map: "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a h - n..<Array.length a h]) ?h1 h' r"
    by (auto elim!: crelE crel_map_entry crel_return)
  have length_remains: "Array.length a ?h1 = Array.length a h" by simp
  from crel_fold_map have crel_fold_map': "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a ?h1 - n..<Array.length a ?h1]) ?h1 h' r"
    by simp
  from Suc(1)[OF this] length_remains Suc(3) show ?case by simp
qed

lemma crel_fold_map_map_entry:
assumes "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [0..<Array.length a h]) h h' r"
  shows "get_array a h' = List.map f (get_array a h)"
proof -
  from assms have "crel (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a h - Array.length a h..<Array.length a h]) h h' r" by simp
  from crel_fold_map_map_entry_length[OF this]
  crel_fold_map_map_entry_changes[OF this] show ?thesis
    unfolding Array.length_def
    by (auto intro: nth_equalityI)
qed


subsection {* Elimination rules for reference commands *}

(* TODO:
maybe introduce a new predicate "extends h' h x"
which means h' extends h with a new reference x.
Then crel_new: would be
assumes "crel (Ref.new v) h h' x"
obtains "get_ref x h' = v"
and "extends h' h x"

and we would need further rules for extends:
extends h' h x \<Longrightarrow> \<not> ref_present x h
extends h' h x \<Longrightarrow>  ref_present x h'
extends h' h x \<Longrightarrow> ref_present y h \<Longrightarrow> ref_present y h'
extends h' h x \<Longrightarrow> ref_present y h \<Longrightarrow> get_ref y h = get_ref y h'
extends h' h x \<Longrightarrow> lim h' = Suc (lim h)
*)

lemma crel_ref:
  assumes "crel (ref v) h h' x"
  obtains "Ref.get h' x = v"
  and "\<not> Ref.present h x"
  and "Ref.present h' x"
  and "\<forall>y. Ref.present h y \<longrightarrow> Ref.get h y = Ref.get h' y"
 (* and "lim h' = Suc (lim h)" *)
  and "\<forall>y. Ref.present h y \<longrightarrow> Ref.present h' y"
  using assms
  unfolding Ref.ref_def
  apply (elim crel_heap)
  unfolding Ref.alloc_def
  apply (simp add: Let_def)
  unfolding Ref.present_def
  apply auto
  unfolding Ref.get_def Ref.set_def
  apply auto
  done

lemma crel_lookup:
  assumes "crel (!r') h h' r"
  obtains "h = h'" "r = Ref.get h r'"
using assms
unfolding Ref.lookup_def
by (auto elim: crel_heap)

lemma crel_update:
  assumes "crel (r' := v) h h' r"
  obtains "h' = Ref.set r' v h" "r = ()"
using assms
unfolding Ref.update_def
by (auto elim: crel_heap)

lemma crel_change:
  assumes "crel (Ref.change f r') h h' r"
  obtains "h' = Ref.set r' (f (Ref.get h r')) h" "r = f (Ref.get h r')"
using assms
unfolding Ref.change_def Let_def
by (auto elim!: crelE crel_lookup crel_update crel_return)

subsection {* Elimination rules for the assert command *}

lemma crel_assert[consumes 1]:
  assumes "crel (assert P x) h h' r"
  obtains "P x" "r = x" "h = h'"
  using assms
  unfolding assert_def
  by (elim crel_if crel_return crel_raise) auto

lemma crel_assert_eq: "(\<And>h h' r. crel f h h' r \<Longrightarrow> P r) \<Longrightarrow> f \<guillemotright>= assert P = f"
unfolding crel_def bind_def Let_def assert_def
  raise_def return_def prod_case_beta
apply (cases f)
apply simp
apply (simp add: expand_fun_eq split_def)
apply (auto split: option.split)
apply (erule_tac x="x" in meta_allE)
apply auto
done

section {* Introduction rules *}

subsection {* Introduction rules for basic monadic commands *}

lemma crelI:
  assumes "crel f h h' r" "crel (g r) h' h'' r'"
  shows "crel (f >>= g) h h'' r'"
  using assms by (simp add: crel_def' bind_def)

lemma crelI':
  assumes "crel f h h' r" "crel g h' h'' r'"
  shows "crel (f >> g) h h'' r'"
  using assms by (intro crelI) auto

lemma crel_returnI:
  shows "crel (return x) h h x"
  unfolding crel_def return_def by simp

lemma crel_raiseI:
  shows "\<not> (crel (raise x) h h' r)"
  unfolding crel_def raise_def by simp

lemma crel_ifI:
  assumes "c \<longrightarrow> crel t h h' r"
  "\<not>c \<longrightarrow> crel e h h' r"
  shows "crel (if c then t else e) h h' r"
  using assms
  unfolding crel_def by auto

lemma crel_option_caseI:
  assumes "\<And>y. x = Some y \<Longrightarrow> crel (s y) h h' r"
  assumes "x = None \<Longrightarrow> crel n h h' r"
  shows "crel (case x of None \<Rightarrow> n | Some y \<Rightarrow> s y) h h' r"
using assms
by (auto split: option.split)

lemma crel_heapI:
  shows "crel (Heap_Monad.heap f) h (snd (f h)) (fst (f h))"
  by (simp add: crel_def apfst_def split_def prod_fun_def)

lemma crel_heapI': (*FIXME keep only this version*)
  assumes "h' = snd (f h)" "r = fst (f h)"
  shows "crel (Heap_Monad.heap f) h h' r"
  using assms
  by (simp add: crel_def split_def apfst_def prod_fun_def)

lemma crel_guardI:
  assumes "P h" "h' = snd (f h)" "r = fst (f h)"
  shows "crel (Heap_Monad.guard P f) h h' r"
  using assms by (simp add: crel_def)

lemma crelI2:
  assumes "\<exists>h' rs'. crel f h h' rs' \<and> (\<exists>h'' rs. crel (g rs') h' h'' rs)"
  shows "\<exists>h'' rs. crel (f\<guillemotright>= g) h h'' rs"
  oops

lemma crel_ifI2:
  assumes "c \<Longrightarrow> \<exists>h' r. crel t h h' r"
  "\<not> c \<Longrightarrow> \<exists>h' r. crel e h h' r"
  shows "\<exists> h' r. crel (if c then t else e) h h' r"
  oops

subsection {* Introduction rules for array commands *}

lemma crel_lengthI:
  shows "crel (Array.len a) h h (Array.length a h)"
  unfolding len_def
  by (rule crel_heapI') auto

(* thm crel_newI for Array.new is missing *)

lemma crel_nthI:
  assumes "i < Array.length a h"
  shows "crel (nth a i) h h ((get_array a h) ! i)"
  using assms unfolding nth_def by (auto intro: crel_guardI)

lemma crel_updI:
  assumes "i < Array.length a h"
  shows "crel (upd i v a) h (Array.change a i v h) a"
  using assms unfolding upd_def by (auto intro: crel_guardI)

(* thm crel_of_listI is missing *)

(* thm crel_map_entryI is missing *)

(* thm crel_swapI is missing *)

(* thm crel_makeI is missing *)

(* thm crel_freezeI is missing *)

(* thm crel_mapI is missing *)

subsubsection {* Introduction rules for reference commands *}

lemma crel_lookupI:
  shows "crel (!r) h h (Ref.get h r)"
  unfolding lookup_def by (auto intro!: crel_heapI')

lemma crel_updateI:
  shows "crel (r := v) h (Ref.set r v h) ()"
  unfolding update_def by (auto intro!: crel_heapI')

lemma crel_changeI: 
  shows "crel (Ref.change f r) h (Ref.set r (f (Ref.get h r)) h) (f (Ref.get h r))"
unfolding change_def Let_def by (auto intro!: crelI crel_returnI crel_lookupI crel_updateI)

subsubsection {* Introduction rules for the assert command *}

lemma crel_assertI:
  assumes "P x"
  shows "crel (assert P x) h h x"
  using assms
  unfolding assert_def
  by (auto intro!: crel_ifI crel_returnI crel_raiseI)
 
subsection {* Induction rule for the MREC combinator *}

lemma MREC_induct:
  assumes "crel (MREC f g x) h h' r"
  assumes "\<And> x h h' r. crel (f x) h h' (Inl r) \<Longrightarrow> P x h h' r"
  assumes "\<And> x h h1 h2 h' s z r. crel (f x) h h1 (Inr s) \<Longrightarrow> crel (MREC f g s) h1 h2 z \<Longrightarrow> P s h1 h2 z
    \<Longrightarrow> crel (g x s z) h2 h' r \<Longrightarrow> P x h h' r"
  shows "P x h h' r"
proof (rule MREC_pinduct[OF assms(1)[unfolded crel_def, symmetric]])
  fix x h h1 h2 h' s z r
  assume "Heap_Monad.execute (f x) h = Some (Inr s, h1)"
    "Heap_Monad.execute (MREC f g s) h1 = Some (z, h2)"
    "P s h1 h2 z"
    "Heap_Monad.execute (g x s z) h2 = Some (r, h')"
  from assms(3)[unfolded crel_def, OF this(1)[symmetric] this(2)[symmetric] this(3) this(4)[symmetric]]
  show "P x h h' r" .
next
qed (auto simp add: assms(2)[unfolded crel_def])

section {* Definition of the noError predicate *}

text {* We add a simple definitional setting for crel intro rules
  where we only would like to show that the computation does not result in a exception for heap h,
  but we do not care about statements about the resulting heap and return value.*}

definition noError :: "'a Heap \<Rightarrow> heap \<Rightarrow> bool"
where
  "noError c h \<longleftrightarrow> (\<exists>r h'. Some (r, h') = Heap_Monad.execute c h)"

lemma noError_def': -- FIXME
  "noError c h \<longleftrightarrow> (\<exists>r h'. Heap_Monad.execute c h = Some (r, h'))"
  unfolding noError_def apply auto proof -
  fix r h'
  assume "Some (r, h') = Heap_Monad.execute c h"
  then have "Heap_Monad.execute c h = Some (r, h')" ..
  then show "\<exists>r h'. Heap_Monad.execute c h = Some (r, h')" by blast
qed

subsection {* Introduction rules for basic monadic commands *}

lemma noErrorI:
  assumes "noError f h"
  assumes "\<And>h' r. crel f h h' r \<Longrightarrow> noError (g r) h'"
  shows "noError (f \<guillemotright>= g) h"
  using assms
  by (auto simp add: noError_def' crel_def' bind_def)

lemma noErrorI':
  assumes "noError f h"
  assumes "\<And>h' r. crel f h h' r \<Longrightarrow> noError g h'"
  shows "noError (f \<guillemotright> g) h"
  using assms
  by (auto simp add: noError_def' crel_def' bind_def)

lemma noErrorI2:
"\<lbrakk>crel f h h' r ; noError f h; noError (g r) h'\<rbrakk>
\<Longrightarrow> noError (f \<guillemotright>= g) h"
by (auto simp add: noError_def' crel_def' bind_def)

lemma noError_return: 
  shows "noError (return x) h"
  unfolding noError_def return_def
  by auto

lemma noError_if:
  assumes "c \<Longrightarrow> noError t h" "\<not> c \<Longrightarrow> noError e h"
  shows "noError (if c then t else e) h"
  using assms
  unfolding noError_def
  by auto

lemma noError_option_case:
  assumes "\<And>y. x = Some y \<Longrightarrow> noError (s y) h"
  assumes "noError n h"
  shows "noError (case x of None \<Rightarrow> n | Some y \<Rightarrow> s y) h"
using assms
by (auto split: option.split)

lemma noError_fold_map: 
assumes "\<forall>x \<in> set xs. noError (f x) h \<and> crel (f x) h h (r x)" 
shows "noError (Heap_Monad.fold_map f xs) h"
using assms
proof (induct xs)
  case Nil
  thus ?case
    unfolding fold_map.simps by (intro noError_return)
next
  case (Cons x xs)
  thus ?case
    unfolding fold_map.simps
    by (auto intro: noErrorI2[of "f x"] noErrorI noError_return)
qed

lemma noError_heap [simp]:
  "noError (Heap_Monad.heap f) h"
  by (simp add: noError_def')

lemma noError_guard [simp]:
  "P h \<Longrightarrow> noError (Heap_Monad.guard P f) h"
  by (simp add: noError_def')

subsection {* Introduction rules for array commands *}

lemma noError_length:
  shows "noError (Array.len a) h"
  by (simp add: len_def)

lemma noError_new:
  shows "noError (Array.new n v) h"
  by (simp add: Array.new_def)

lemma noError_upd:
  assumes "i < Array.length a h"
  shows "noError (Array.upd i v a) h"
  using assms by (simp add: upd_def)

lemma noError_nth:
  assumes "i < Array.length a h"
  shows "noError (Array.nth a i) h"
  using assms by (simp add: nth_def)

lemma noError_of_list:
  "noError (of_list ls) h"
  by (simp add: of_list_def)

lemma noError_map_entry:
  assumes "i < Array.length a h"
  shows "noError (map_entry i f a) h"
  using assms by (simp add: map_entry_def)

lemma noError_swap:
  assumes "i < Array.length a h"
  shows "noError (swap i x a) h"
  using assms by (simp add: swap_def)

lemma noError_make:
  "noError (make n f) h"
  by (simp add: make_def)

lemma noError_freeze:
  "noError (freeze a) h"
  by (simp add: freeze_def)

lemma noError_fold_map_map_entry:
  assumes "n \<le> Array.length a h"
  shows "noError (Heap_Monad.fold_map (\<lambda>n. map_entry n f a) [Array.length a h - n..<Array.length a h]) h"
using assms
proof (induct n arbitrary: h)
  case 0
  thus ?case by (auto intro: noError_return)
next
  case (Suc n)
  from Suc.prems have "[Array.length a h - Suc n..<Array.length a h] = (Array.length a h - Suc n)#[Array.length a h - n..<Array.length a h]"
    by (simp add: upt_conv_Cons')
  with Suc.hyps[of "(Array.change a (Array.length a h - Suc n) (f (get_array a h ! (Array.length a h - Suc n))) h)"] Suc.prems show ?case
    by (auto simp add: intro!: noErrorI noError_return noError_map_entry elim: crel_map_entry)
qed


subsection {* Introduction rules for the reference commands *}

lemma noError_Ref_new:
  shows "noError (ref v) h"
  by (simp add: Ref.ref_def)

lemma noError_lookup:
  shows "noError (!r) h"
  by (simp add: lookup_def)

lemma noError_update:
  shows "noError (r := v) h"
  by (simp add: update_def)

lemma noError_change:
  shows "noError (Ref.change f r) h"
  by (simp add: change_def)
    (auto intro!: noErrorI2 noError_lookup noError_update noError_return crel_lookupI crel_updateI simp add: Let_def)

subsection {* Introduction rules for the assert command *}

lemma noError_assert:
  assumes "P x"
  shows "noError (assert P x) h"
  using assms unfolding assert_def
  by (auto intro: noError_if noError_return)

section {* Cumulative lemmas *}

lemmas crel_elim_all =
  crelE crelE' crel_return crel_raise crel_if crel_option_case
  crel_length crel_new_weak crel_nth crel_upd crel_of_list_weak crel_map_entry crel_swap crel_make_weak crel_freeze
  crel_ref crel_lookup crel_update crel_change
  crel_assert

lemmas crel_intro_all =
  crelI crelI' crel_returnI crel_raiseI crel_ifI crel_option_caseI
  crel_lengthI (* crel_newI *) crel_nthI crel_updI (* crel_of_listI crel_map_entryI crel_swapI crel_makeI crel_freezeI crel_mapI *)
  (* crel_Ref_newI *) crel_lookupI crel_updateI crel_changeI
  crel_assert

lemmas noError_intro_all = 
  noErrorI noErrorI' noError_return noError_if noError_option_case
  noError_length noError_new noError_nth noError_upd noError_of_list noError_map_entry noError_swap noError_make noError_freeze
  noError_Ref_new noError_lookup noError_update noError_change
  noError_assert

end