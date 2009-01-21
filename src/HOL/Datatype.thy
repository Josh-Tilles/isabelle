(*  Title:      HOL/Datatype.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen

Could <*> be generalized to a general summation (Sigma)?
*)

header {* Analogues of the Cartesian Product and Disjoint Sum for Datatypes *}

theory Datatype
imports Nat Relation
begin

typedef (Node)
  ('a,'b) node = "{p. EX f x k. p = (f::nat=>'b+nat, x::'a+nat) & f k = Inr 0}"
    --{*it is a subtype of @{text "(nat=>'b+nat) * ('a+nat)"}*}
  by auto

text{*Datatypes will be represented by sets of type @{text node}*}

types 'a item        = "('a, unit) node set"
      ('a, 'b) dtree = "('a, 'b) node set"

consts
  Push      :: "[('b + nat), nat => ('b + nat)] => (nat => ('b + nat))"

  Push_Node :: "[('b + nat), ('a, 'b) node] => ('a, 'b) node"
  ndepth    :: "('a, 'b) node => nat"

  Atom      :: "('a + nat) => ('a, 'b) dtree"
  Leaf      :: "'a => ('a, 'b) dtree"
  Numb      :: "nat => ('a, 'b) dtree"
  Scons     :: "[('a, 'b) dtree, ('a, 'b) dtree] => ('a, 'b) dtree"
  In0       :: "('a, 'b) dtree => ('a, 'b) dtree"
  In1       :: "('a, 'b) dtree => ('a, 'b) dtree"
  Lim       :: "('b => ('a, 'b) dtree) => ('a, 'b) dtree"

  ntrunc    :: "[nat, ('a, 'b) dtree] => ('a, 'b) dtree"

  uprod     :: "[('a, 'b) dtree set, ('a, 'b) dtree set]=> ('a, 'b) dtree set"
  usum      :: "[('a, 'b) dtree set, ('a, 'b) dtree set]=> ('a, 'b) dtree set"

  Split     :: "[[('a, 'b) dtree, ('a, 'b) dtree]=>'c, ('a, 'b) dtree] => 'c"
  Case      :: "[[('a, 'b) dtree]=>'c, [('a, 'b) dtree]=>'c, ('a, 'b) dtree] => 'c"

  dprod     :: "[(('a, 'b) dtree * ('a, 'b) dtree)set, (('a, 'b) dtree * ('a, 'b) dtree)set]
                => (('a, 'b) dtree * ('a, 'b) dtree)set"
  dsum      :: "[(('a, 'b) dtree * ('a, 'b) dtree)set, (('a, 'b) dtree * ('a, 'b) dtree)set]
                => (('a, 'b) dtree * ('a, 'b) dtree)set"


defs

  Push_Node_def:  "Push_Node == (%n x. Abs_Node (apfst (Push n) (Rep_Node x)))"

  (*crude "lists" of nats -- needed for the constructions*)
  Push_def:   "Push == (%b h. nat_case b h)"

  (** operations on S-expressions -- sets of nodes **)

  (*S-expression constructors*)
  Atom_def:   "Atom == (%x. {Abs_Node((%k. Inr 0, x))})"
  Scons_def:  "Scons M N == (Push_Node (Inr 1) ` M) Un (Push_Node (Inr (Suc 1)) ` N)"

  (*Leaf nodes, with arbitrary or nat labels*)
  Leaf_def:   "Leaf == Atom o Inl"
  Numb_def:   "Numb == Atom o Inr"

  (*Injections of the "disjoint sum"*)
  In0_def:    "In0(M) == Scons (Numb 0) M"
  In1_def:    "In1(M) == Scons (Numb 1) M"

  (*Function spaces*)
  Lim_def: "Lim f == Union {z. ? x. z = Push_Node (Inl x) ` (f x)}"

  (*the set of nodes with depth less than k*)
  ndepth_def: "ndepth(n) == (%(f,x). LEAST k. f k = Inr 0) (Rep_Node n)"
  ntrunc_def: "ntrunc k N == {n. n:N & ndepth(n)<k}"

  (*products and sums for the "universe"*)
  uprod_def:  "uprod A B == UN x:A. UN y:B. { Scons x y }"
  usum_def:   "usum A B == In0`A Un In1`B"

  (*the corresponding eliminators*)
  Split_def:  "Split c M == THE u. EX x y. M = Scons x y & u = c x y"

  Case_def:   "Case c d M == THE u.  (EX x . M = In0(x) & u = c(x))
                                  | (EX y . M = In1(y) & u = d(y))"


  (** equality for the "universe" **)

  dprod_def:  "dprod r s == UN (x,x'):r. UN (y,y'):s. {(Scons x y, Scons x' y')}"

  dsum_def:   "dsum r s == (UN (x,x'):r. {(In0(x),In0(x'))}) Un
                          (UN (y,y'):s. {(In1(y),In1(y'))})"



lemma apfst_convE: 
    "[| q = apfst f p;  !!x y. [| p = (x,y);  q = (f(x),y) |] ==> R  
     |] ==> R"
by (force simp add: apfst_def)

(** Push -- an injection, analogous to Cons on lists **)

lemma Push_inject1: "Push i f = Push j g  ==> i=j"
apply (simp add: Push_def expand_fun_eq) 
apply (drule_tac x=0 in spec, simp) 
done

lemma Push_inject2: "Push i f = Push j g  ==> f=g"
apply (auto simp add: Push_def expand_fun_eq) 
apply (drule_tac x="Suc x" in spec, simp) 
done

lemma Push_inject:
    "[| Push i f =Push j g;  [| i=j;  f=g |] ==> P |] ==> P"
by (blast dest: Push_inject1 Push_inject2) 

lemma Push_neq_K0: "Push (Inr (Suc k)) f = (%z. Inr 0) ==> P"
by (auto simp add: Push_def expand_fun_eq split: nat.split_asm)

lemmas Abs_Node_inj = Abs_Node_inject [THEN [2] rev_iffD1, standard]


(*** Introduction rules for Node ***)

lemma Node_K0_I: "(%k. Inr 0, a) : Node"
by (simp add: Node_def)

lemma Node_Push_I: "p: Node ==> apfst (Push i) p : Node"
apply (simp add: Node_def Push_def) 
apply (fast intro!: apfst_conv nat_case_Suc [THEN trans])
done


subsection{*Freeness: Distinctness of Constructors*}

(** Scons vs Atom **)

lemma Scons_not_Atom [iff]: "Scons M N \<noteq> Atom(a)"
apply (simp add: Atom_def Scons_def Push_Node_def One_nat_def)
apply (blast intro: Node_K0_I Rep_Node [THEN Node_Push_I] 
         dest!: Abs_Node_inj 
         elim!: apfst_convE sym [THEN Push_neq_K0])  
done

lemmas Atom_not_Scons [iff] = Scons_not_Atom [THEN not_sym, standard]


(*** Injectiveness ***)

(** Atomic nodes **)

lemma inj_Atom: "inj(Atom)"
apply (simp add: Atom_def)
apply (blast intro!: inj_onI Node_K0_I dest!: Abs_Node_inj)
done
lemmas Atom_inject = inj_Atom [THEN injD, standard]

lemma Atom_Atom_eq [iff]: "(Atom(a)=Atom(b)) = (a=b)"
by (blast dest!: Atom_inject)

lemma inj_Leaf: "inj(Leaf)"
apply (simp add: Leaf_def o_def)
apply (rule inj_onI)
apply (erule Atom_inject [THEN Inl_inject])
done

lemmas Leaf_inject [dest!] = inj_Leaf [THEN injD, standard]

lemma inj_Numb: "inj(Numb)"
apply (simp add: Numb_def o_def)
apply (rule inj_onI)
apply (erule Atom_inject [THEN Inr_inject])
done

lemmas Numb_inject [dest!] = inj_Numb [THEN injD, standard]


(** Injectiveness of Push_Node **)

lemma Push_Node_inject:
    "[| Push_Node i m =Push_Node j n;  [| i=j;  m=n |] ==> P  
     |] ==> P"
apply (simp add: Push_Node_def)
apply (erule Abs_Node_inj [THEN apfst_convE])
apply (rule Rep_Node [THEN Node_Push_I])+
apply (erule sym [THEN apfst_convE]) 
apply (blast intro: Rep_Node_inject [THEN iffD1] trans sym elim!: Push_inject)
done


(** Injectiveness of Scons **)

lemma Scons_inject_lemma1: "Scons M N <= Scons M' N' ==> M<=M'"
apply (simp add: Scons_def One_nat_def)
apply (blast dest!: Push_Node_inject)
done

lemma Scons_inject_lemma2: "Scons M N <= Scons M' N' ==> N<=N'"
apply (simp add: Scons_def One_nat_def)
apply (blast dest!: Push_Node_inject)
done

lemma Scons_inject1: "Scons M N = Scons M' N' ==> M=M'"
apply (erule equalityE)
apply (iprover intro: equalityI Scons_inject_lemma1)
done

lemma Scons_inject2: "Scons M N = Scons M' N' ==> N=N'"
apply (erule equalityE)
apply (iprover intro: equalityI Scons_inject_lemma2)
done

lemma Scons_inject:
    "[| Scons M N = Scons M' N';  [| M=M';  N=N' |] ==> P |] ==> P"
by (iprover dest: Scons_inject1 Scons_inject2)

lemma Scons_Scons_eq [iff]: "(Scons M N = Scons M' N') = (M=M' & N=N')"
by (blast elim!: Scons_inject)

(*** Distinctness involving Leaf and Numb ***)

(** Scons vs Leaf **)

lemma Scons_not_Leaf [iff]: "Scons M N \<noteq> Leaf(a)"
by (simp add: Leaf_def o_def Scons_not_Atom)

lemmas Leaf_not_Scons  [iff] = Scons_not_Leaf [THEN not_sym, standard]

(** Scons vs Numb **)

lemma Scons_not_Numb [iff]: "Scons M N \<noteq> Numb(k)"
by (simp add: Numb_def o_def Scons_not_Atom)

lemmas Numb_not_Scons [iff] = Scons_not_Numb [THEN not_sym, standard]


(** Leaf vs Numb **)

lemma Leaf_not_Numb [iff]: "Leaf(a) \<noteq> Numb(k)"
by (simp add: Leaf_def Numb_def)

lemmas Numb_not_Leaf [iff] = Leaf_not_Numb [THEN not_sym, standard]


(*** ndepth -- the depth of a node ***)

lemma ndepth_K0: "ndepth (Abs_Node(%k. Inr 0, x)) = 0"
by (simp add: ndepth_def  Node_K0_I [THEN Abs_Node_inverse] Least_equality)

lemma ndepth_Push_Node_aux:
     "nat_case (Inr (Suc i)) f k = Inr 0 --> Suc(LEAST x. f x = Inr 0) <= k"
apply (induct_tac "k", auto)
apply (erule Least_le)
done

lemma ndepth_Push_Node: 
    "ndepth (Push_Node (Inr (Suc i)) n) = Suc(ndepth(n))"
apply (insert Rep_Node [of n, unfolded Node_def])
apply (auto simp add: ndepth_def Push_Node_def
                 Rep_Node [THEN Node_Push_I, THEN Abs_Node_inverse])
apply (rule Least_equality)
apply (auto simp add: Push_def ndepth_Push_Node_aux)
apply (erule LeastI)
done


(*** ntrunc applied to the various node sets ***)

lemma ntrunc_0 [simp]: "ntrunc 0 M = {}"
by (simp add: ntrunc_def)

lemma ntrunc_Atom [simp]: "ntrunc (Suc k) (Atom a) = Atom(a)"
by (auto simp add: Atom_def ntrunc_def ndepth_K0)

lemma ntrunc_Leaf [simp]: "ntrunc (Suc k) (Leaf a) = Leaf(a)"
by (simp add: Leaf_def o_def ntrunc_Atom)

lemma ntrunc_Numb [simp]: "ntrunc (Suc k) (Numb i) = Numb(i)"
by (simp add: Numb_def o_def ntrunc_Atom)

lemma ntrunc_Scons [simp]: 
    "ntrunc (Suc k) (Scons M N) = Scons (ntrunc k M) (ntrunc k N)"
by (auto simp add: Scons_def ntrunc_def One_nat_def ndepth_Push_Node) 



(** Injection nodes **)

lemma ntrunc_one_In0 [simp]: "ntrunc (Suc 0) (In0 M) = {}"
apply (simp add: In0_def)
apply (simp add: Scons_def)
done

lemma ntrunc_In0 [simp]: "ntrunc (Suc(Suc k)) (In0 M) = In0 (ntrunc (Suc k) M)"
by (simp add: In0_def)

lemma ntrunc_one_In1 [simp]: "ntrunc (Suc 0) (In1 M) = {}"
apply (simp add: In1_def)
apply (simp add: Scons_def)
done

lemma ntrunc_In1 [simp]: "ntrunc (Suc(Suc k)) (In1 M) = In1 (ntrunc (Suc k) M)"
by (simp add: In1_def)


subsection{*Set Constructions*}


(*** Cartesian Product ***)

lemma uprodI [intro!]: "[| M:A;  N:B |] ==> Scons M N : uprod A B"
by (simp add: uprod_def)

(*The general elimination rule*)
lemma uprodE [elim!]:
    "[| c : uprod A B;   
        !!x y. [| x:A;  y:B;  c = Scons x y |] ==> P  
     |] ==> P"
by (auto simp add: uprod_def) 


(*Elimination of a pair -- introduces no eigenvariables*)
lemma uprodE2: "[| Scons M N : uprod A B;  [| M:A;  N:B |] ==> P |] ==> P"
by (auto simp add: uprod_def)


(*** Disjoint Sum ***)

lemma usum_In0I [intro]: "M:A ==> In0(M) : usum A B"
by (simp add: usum_def)

lemma usum_In1I [intro]: "N:B ==> In1(N) : usum A B"
by (simp add: usum_def)

lemma usumE [elim!]: 
    "[| u : usum A B;   
        !!x. [| x:A;  u=In0(x) |] ==> P;  
        !!y. [| y:B;  u=In1(y) |] ==> P  
     |] ==> P"
by (auto simp add: usum_def)


(** Injection **)

lemma In0_not_In1 [iff]: "In0(M) \<noteq> In1(N)"
by (auto simp add: In0_def In1_def One_nat_def)

lemmas In1_not_In0 [iff] = In0_not_In1 [THEN not_sym, standard]

lemma In0_inject: "In0(M) = In0(N) ==>  M=N"
by (simp add: In0_def)

lemma In1_inject: "In1(M) = In1(N) ==>  M=N"
by (simp add: In1_def)

lemma In0_eq [iff]: "(In0 M = In0 N) = (M=N)"
by (blast dest!: In0_inject)

lemma In1_eq [iff]: "(In1 M = In1 N) = (M=N)"
by (blast dest!: In1_inject)

lemma inj_In0: "inj In0"
by (blast intro!: inj_onI)

lemma inj_In1: "inj In1"
by (blast intro!: inj_onI)


(*** Function spaces ***)

lemma Lim_inject: "Lim f = Lim g ==> f = g"
apply (simp add: Lim_def)
apply (rule ext)
apply (blast elim!: Push_Node_inject)
done


(*** proving equality of sets and functions using ntrunc ***)

lemma ntrunc_subsetI: "ntrunc k M <= M"
by (auto simp add: ntrunc_def)

lemma ntrunc_subsetD: "(!!k. ntrunc k M <= N) ==> M<=N"
by (auto simp add: ntrunc_def)

(*A generalized form of the take-lemma*)
lemma ntrunc_equality: "(!!k. ntrunc k M = ntrunc k N) ==> M=N"
apply (rule equalityI)
apply (rule_tac [!] ntrunc_subsetD)
apply (rule_tac [!] ntrunc_subsetI [THEN [2] subset_trans], auto) 
done

lemma ntrunc_o_equality: 
    "[| !!k. (ntrunc(k) o h1) = (ntrunc(k) o h2) |] ==> h1=h2"
apply (rule ntrunc_equality [THEN ext])
apply (simp add: expand_fun_eq) 
done


(*** Monotonicity ***)

lemma uprod_mono: "[| A<=A';  B<=B' |] ==> uprod A B <= uprod A' B'"
by (simp add: uprod_def, blast)

lemma usum_mono: "[| A<=A';  B<=B' |] ==> usum A B <= usum A' B'"
by (simp add: usum_def, blast)

lemma Scons_mono: "[| M<=M';  N<=N' |] ==> Scons M N <= Scons M' N'"
by (simp add: Scons_def, blast)

lemma In0_mono: "M<=N ==> In0(M) <= In0(N)"
by (simp add: In0_def subset_refl Scons_mono)

lemma In1_mono: "M<=N ==> In1(M) <= In1(N)"
by (simp add: In1_def subset_refl Scons_mono)


(*** Split and Case ***)

lemma Split [simp]: "Split c (Scons M N) = c M N"
by (simp add: Split_def)

lemma Case_In0 [simp]: "Case c d (In0 M) = c(M)"
by (simp add: Case_def)

lemma Case_In1 [simp]: "Case c d (In1 N) = d(N)"
by (simp add: Case_def)



(**** UN x. B(x) rules ****)

lemma ntrunc_UN1: "ntrunc k (UN x. f(x)) = (UN x. ntrunc k (f x))"
by (simp add: ntrunc_def, blast)

lemma Scons_UN1_x: "Scons (UN x. f x) M = (UN x. Scons (f x) M)"
by (simp add: Scons_def, blast)

lemma Scons_UN1_y: "Scons M (UN x. f x) = (UN x. Scons M (f x))"
by (simp add: Scons_def, blast)

lemma In0_UN1: "In0(UN x. f(x)) = (UN x. In0(f(x)))"
by (simp add: In0_def Scons_UN1_y)

lemma In1_UN1: "In1(UN x. f(x)) = (UN x. In1(f(x)))"
by (simp add: In1_def Scons_UN1_y)


(*** Equality for Cartesian Product ***)

lemma dprodI [intro!]: 
    "[| (M,M'):r;  (N,N'):s |] ==> (Scons M N, Scons M' N') : dprod r s"
by (auto simp add: dprod_def)

(*The general elimination rule*)
lemma dprodE [elim!]: 
    "[| c : dprod r s;   
        !!x y x' y'. [| (x,x') : r;  (y,y') : s;  
                        c = (Scons x y, Scons x' y') |] ==> P  
     |] ==> P"
by (auto simp add: dprod_def)


(*** Equality for Disjoint Sum ***)

lemma dsum_In0I [intro]: "(M,M'):r ==> (In0(M), In0(M')) : dsum r s"
by (auto simp add: dsum_def)

lemma dsum_In1I [intro]: "(N,N'):s ==> (In1(N), In1(N')) : dsum r s"
by (auto simp add: dsum_def)

lemma dsumE [elim!]: 
    "[| w : dsum r s;   
        !!x x'. [| (x,x') : r;  w = (In0(x), In0(x')) |] ==> P;  
        !!y y'. [| (y,y') : s;  w = (In1(y), In1(y')) |] ==> P  
     |] ==> P"
by (auto simp add: dsum_def)


(*** Monotonicity ***)

lemma dprod_mono: "[| r<=r';  s<=s' |] ==> dprod r s <= dprod r' s'"
by blast

lemma dsum_mono: "[| r<=r';  s<=s' |] ==> dsum r s <= dsum r' s'"
by blast


(*** Bounding theorems ***)

lemma dprod_Sigma: "(dprod (A <*> B) (C <*> D)) <= (uprod A C) <*> (uprod B D)"
by blast

lemmas dprod_subset_Sigma = subset_trans [OF dprod_mono dprod_Sigma, standard]

(*Dependent version*)
lemma dprod_subset_Sigma2:
     "(dprod (Sigma A B) (Sigma C D)) <= 
      Sigma (uprod A C) (Split (%x y. uprod (B x) (D y)))"
by auto

lemma dsum_Sigma: "(dsum (A <*> B) (C <*> D)) <= (usum A C) <*> (usum B D)"
by blast

lemmas dsum_subset_Sigma = subset_trans [OF dsum_mono dsum_Sigma, standard]


(*** Domain ***)

lemma Domain_dprod [simp]: "Domain (dprod r s) = uprod (Domain r) (Domain s)"
by auto

lemma Domain_dsum [simp]: "Domain (dsum r s) = usum (Domain r) (Domain s)"
by auto


text {* hides popular names *}
hide (open) type node item
hide (open) const Push Node Atom Leaf Numb Lim Split Case


section {* Datatypes *}

subsection {* Representing sums *}

rep_datatype (sum) Inl Inr
proof -
  fix P
  fix s :: "'a + 'b"
  assume x: "\<And>x\<Colon>'a. P (Inl x)" and y: "\<And>y\<Colon>'b. P (Inr y)"
  then show "P s" by (auto intro: sumE [of s])
qed simp_all

lemma sum_case_KK[simp]: "sum_case (%x. a) (%x. a) = (%x. a)"
  by (rule ext) (simp split: sum.split)

lemma surjective_sum: "sum_case (%x::'a. f (Inl x)) (%y::'b. f (Inr y)) s = f(s)"
  apply (rule_tac s = s in sumE)
   apply (erule ssubst)
   apply (rule sum.cases(1))
  apply (erule ssubst)
  apply (rule sum.cases(2))
  done

lemma sum_case_weak_cong: "s = t ==> sum_case f g s = sum_case f g t"
  -- {* Prevents simplification of @{text f} and @{text g}: much faster. *}
  by simp

lemma sum_case_inject:
  "sum_case f1 f2 = sum_case g1 g2 ==> (f1 = g1 ==> f2 = g2 ==> P) ==> P"
proof -
  assume a: "sum_case f1 f2 = sum_case g1 g2"
  assume r: "f1 = g1 ==> f2 = g2 ==> P"
  show P
    apply (rule r)
     apply (rule ext)
     apply (cut_tac x = "Inl x" in a [THEN fun_cong], simp)
    apply (rule ext)
    apply (cut_tac x = "Inr x" in a [THEN fun_cong], simp)
    done
qed

constdefs
  Suml :: "('a => 'c) => 'a + 'b => 'c"
  "Suml == (%f. sum_case f undefined)"

  Sumr :: "('b => 'c) => 'a + 'b => 'c"
  "Sumr == sum_case undefined"

lemma Suml_inject: "Suml f = Suml g ==> f = g"
  by (unfold Suml_def) (erule sum_case_inject)

lemma Sumr_inject: "Sumr f = Sumr g ==> f = g"
  by (unfold Sumr_def) (erule sum_case_inject)

primrec Projl :: "'a + 'b => 'a"
where Projl_Inl: "Projl (Inl x) = x"

primrec Projr :: "'a + 'b => 'b"
where Projr_Inr: "Projr (Inr x) = x"

hide (open) const Suml Sumr Projl Projr


subsection {* The option datatype *}

datatype 'a option = None | Some 'a

lemma not_None_eq [iff]: "(x ~= None) = (EX y. x = Some y)"
  by (induct x) auto

lemma not_Some_eq [iff]: "(ALL y. x ~= Some y) = (x = None)"
  by (induct x) auto

text{*Although it may appear that both of these equalities are helpful
only when applied to assumptions, in practice it seems better to give
them the uniform iff attribute. *}

lemma option_caseE:
  assumes c: "(case x of None => P | Some y => Q y)"
  obtains
    (None) "x = None" and P
  | (Some) y where "x = Some y" and "Q y"
  using c by (cases x) simp_all

lemma insert_None_conv_UNIV: "insert None (range Some) = UNIV"
  by (rule set_ext, case_tac x) auto

lemma inj_Some [simp]: "inj_on Some A"
  by (rule inj_onI) simp


subsubsection {* Operations *}

consts
  the :: "'a option => 'a"
primrec
  "the (Some x) = x"

consts
  o2s :: "'a option => 'a set"
primrec
  "o2s None = {}"
  "o2s (Some x) = {x}"

lemma ospec [dest]: "(ALL x:o2s A. P x) ==> A = Some x ==> P x"
  by simp

declaration {* fn _ =>
  Classical.map_cs (fn cs => cs addSD2 ("ospec", thm "ospec"))
*}

lemma elem_o2s [iff]: "(x : o2s xo) = (xo = Some x)"
  by (cases xo) auto

lemma o2s_empty_eq [simp]: "(o2s xo = {}) = (xo = None)"
  by (cases xo) auto

definition
  option_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b option"
where
  [code del]: "option_map = (%f y. case y of None => None | Some x => Some (f x))"

lemma option_map_None [simp, code]: "option_map f None = None"
  by (simp add: option_map_def)

lemma option_map_Some [simp, code]: "option_map f (Some x) = Some (f x)"
  by (simp add: option_map_def)

lemma option_map_is_None [iff]:
    "(option_map f opt = None) = (opt = None)"
  by (simp add: option_map_def split add: option.split)

lemma option_map_eq_Some [iff]:
    "(option_map f xo = Some y) = (EX z. xo = Some z & f z = y)"
  by (simp add: option_map_def split add: option.split)

lemma option_map_comp:
    "option_map f (option_map g opt) = option_map (f o g) opt"
  by (simp add: option_map_def split add: option.split)

lemma option_map_o_sum_case [simp]:
    "option_map f o sum_case g h = sum_case (option_map f o g) (option_map f o h)"
  by (rule ext) (simp split: sum.split)


subsubsection {* Code generator setup *}

definition
  is_none :: "'a option \<Rightarrow> bool" where
  is_none_none [code post, symmetric, code inline]: "is_none x \<longleftrightarrow> x = None"

lemma is_none_code [code]:
  shows "is_none None \<longleftrightarrow> True"
    and "is_none (Some x) \<longleftrightarrow> False"
  unfolding is_none_none [symmetric] by simp_all

hide (open) const is_none

code_type option
  (SML "_ option")
  (OCaml "_ option")
  (Haskell "Maybe _")

code_const None and Some
  (SML "NONE" and "SOME")
  (OCaml "None" and "Some _")
  (Haskell "Nothing" and "Just")

code_instance option :: eq
  (Haskell -)

code_const "eq_class.eq \<Colon> 'a\<Colon>eq option \<Rightarrow> 'a option \<Rightarrow> bool"
  (Haskell infixl 4 "==")

code_reserved SML
  option NONE SOME

code_reserved OCaml
  option None Some

end
