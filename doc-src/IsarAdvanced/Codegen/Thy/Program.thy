theory Program
imports Introduction
begin

section {* Turning Theories into Programs \label{sec:program} *}

subsection {* The @{text "Isabelle/HOL"} default setup *}

text {*
  We have already seen how by default equations stemming from
  @{command definition}/@{command primrec}/@{command fun}
  statements are used for code generation.  This default behaviour
  can be changed, e.g. by providing different code equations.
  All kinds of customisation shown in this section is \emph{safe}
  in the sense that the user does not have to worry about
  correctness -- all programs generatable that way are partially
  correct.
*}

subsection {* Selecting code equations *}

text {*
  Coming back to our introductory example, we
  could provide an alternative code equations for @{const dequeue}
  explicitly:
*}

lemma %quote [code]:
  "dequeue (Queue xs []) =
     (if xs = [] then (None, Queue [] [])
       else dequeue (Queue [] (rev xs)))"
  "dequeue (Queue xs (y # ys)) =
     (Some y, Queue xs ys)"
  by (cases xs, simp_all) (cases "rev xs", simp_all)

text {*
  \noindent The annotation @{text "[code]"} is an @{text Isar}
  @{text attribute} which states that the given theorems should be
  considered as code equations for a @{text fun} statement --
  the corresponding constant is determined syntactically.  The resulting code:
*}

text %quote {*@{code_stmts dequeue (consts) dequeue (Haskell)}*}

text {*
  \noindent You may note that the equality test @{term "xs = []"} has been
  replaced by the predicate @{term "null xs"}.  This is due to the default
  setup in the \qn{preprocessor} to be discussed further below (\secref{sec:preproc}).

  Changing the default constructor set of datatypes is also
  possible.  See \secref{sec:datatypes} for an example.

  As told in \secref{sec:concept}, code generation is based
  on a structured collection of code theorems.
  For explorative purpose, this collection
  may be inspected using the @{command code_thms} command:
*}

code_thms %quote dequeue

text {*
  \noindent prints a table with \emph{all} code equations
  for @{const dequeue}, including
  \emph{all} code equations those equations depend
  on recursively.
  
  Similarly, the @{command code_deps} command shows a graph
  visualising dependencies between code equations.
*}

subsection {* @{text class} and @{text instantiation} *}

text {*
  Concerning type classes and code generation, let us examine an example
  from abstract algebra:
*}

class %quote semigroup =
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
  assumes assoc: "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"

class %quote monoid = semigroup +
  fixes neutral :: 'a ("\<one>")
  assumes neutl: "\<one> \<otimes> x = x"
    and neutr: "x \<otimes> \<one> = x"

instantiation %quote nat :: monoid
begin

primrec %quote mult_nat where
    "0 \<otimes> n = (0\<Colon>nat)"
  | "Suc m \<otimes> n = n + m \<otimes> n"

definition %quote neutral_nat where
  "\<one> = Suc 0"

lemma %quote add_mult_distrib:
  fixes n m q :: nat
  shows "(n + m) \<otimes> q = n \<otimes> q + m \<otimes> q"
  by (induct n) simp_all

instance %quote proof
  fix m n q :: nat
  show "m \<otimes> n \<otimes> q = m \<otimes> (n \<otimes> q)"
    by (induct m) (simp_all add: add_mult_distrib)
  show "\<one> \<otimes> n = n"
    by (simp add: neutral_nat_def)
  show "m \<otimes> \<one> = m"
    by (induct m) (simp_all add: neutral_nat_def)
qed

end %quote

text {*
  \noindent We define the natural operation of the natural numbers
  on monoids:
*}

primrec %quote (in monoid) pow :: "nat \<Rightarrow> 'a \<Rightarrow> 'a" where
    "pow 0 a = \<one>"
  | "pow (Suc n) a = a \<otimes> pow n a"

text {*
  \noindent This we use to define the discrete exponentiation function:
*}

definition %quote bexp :: "nat \<Rightarrow> nat" where
  "bexp n = pow n (Suc (Suc 0))"

text {*
  \noindent The corresponding code:
*}

text %quote {*@{code_stmts bexp (Haskell)}*}

text {*
  \noindent This is a convenient place to show how explicit dictionary construction
  manifests in generated code (here, the same example in @{text SML}):
*}

text %quote {*@{code_stmts bexp (SML)}*}

text {*
  \noindent Note the parameters with trailing underscore (@{verbatim "A_"})
    which are the dictionary parameters.
*}

subsection {* The preprocessor \label{sec:preproc} *}

text {*
  Before selected function theorems are turned into abstract
  code, a chain of definitional transformation steps is carried
  out: \emph{preprocessing}.  In essence, the preprocessor
  consists of two components: a \emph{simpset} and \emph{function transformers}.

  The \emph{simpset} allows to employ the full generality of the Isabelle
  simplifier.  Due to the interpretation of theorems
  as code equations, rewrites are applied to the right
  hand side and the arguments of the left hand side of an
  equation, but never to the constant heading the left hand side.
  An important special case are \emph{inline theorems} which may be
  declared and undeclared using the
  \emph{code inline} or \emph{code inline del} attribute respectively.

  Some common applications:
*}

text_raw {*
  \begin{itemize}
*}

text {*
     \item replacing non-executable constructs by executable ones:
*}     

lemma %quote [code inline]:
  "x \<in> set xs \<longleftrightarrow> x mem xs" by (induct xs) simp_all

text {*
     \item eliminating superfluous constants:
*}

lemma %quote [code inline]:
  "1 = Suc 0" by simp

text {*
     \item replacing executable but inconvenient constructs:
*}

lemma %quote [code inline]:
  "xs = [] \<longleftrightarrow> List.null xs" by (induct xs) simp_all

text_raw {*
  \end{itemize}
*}

text {*
  \noindent \emph{Function transformers} provide a very general interface,
  transforming a list of function theorems to another
  list of function theorems, provided that neither the heading
  constant nor its type change.  The @{term "0\<Colon>nat"} / @{const Suc}
  pattern elimination implemented in
  theory @{text Efficient_Nat} (see \secref{eff_nat}) uses this
  interface.

  \noindent The current setup of the preprocessor may be inspected using
  the @{command print_codesetup} command.
  @{command code_thms} provides a convenient
  mechanism to inspect the impact of a preprocessor setup
  on code equations.

  \begin{warn}
    The attribute \emph{code unfold}
    associated with the @{text "SML code generator"} also applies to
    the @{text "generic code generator"}:
    \emph{code unfold} implies \emph{code inline}.
  \end{warn}
*}

subsection {* Datatypes \label{sec:datatypes} *}

text {*
  Conceptually, any datatype is spanned by a set of
  \emph{constructors} of type @{text "\<tau> = \<dots> \<Rightarrow> \<kappa> \<alpha>\<^isub>1 \<dots> \<alpha>\<^isub>n"} where @{text
  "{\<alpha>\<^isub>1, \<dots>, \<alpha>\<^isub>n}"} is exactly the set of \emph{all} type variables in
  @{text "\<tau>"}.  The HOL datatype package by default registers any new
  datatype in the table of datatypes, which may be inspected using the
  @{command print_codesetup} command.

  In some cases, it is appropriate to alter or extend this table.  As
  an example, we will develop an alternative representation of the
  queue example given in \secref{sec:intro}.  The amortised
  representation is convenient for generating code but exposes its
  \qt{implementation} details, which may be cumbersome when proving
  theorems about it.  Therefore, here a simple, straightforward
  representation of queues:
*}

datatype %quote 'a queue = Queue "'a list"

definition %quote empty :: "'a queue" where
  "empty = Queue []"

primrec %quote enqueue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "enqueue x (Queue xs) = Queue (xs @ [x])"

fun %quote dequeue :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" where
    "dequeue (Queue []) = (None, Queue [])"
  | "dequeue (Queue (x # xs)) = (Some x, Queue xs)"

text {*
  \noindent This we can use directly for proving;  for executing,
  we provide an alternative characterisation:
*}

definition %quote AQueue :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a queue" where
  "AQueue xs ys = Queue (ys @ rev xs)"

code_datatype %quote AQueue

text {* *}

lemma %quote empty_AQueue [code]:
  "empty = AQueue [] []"
  unfolding AQueue_def empty_def by simp

lemma %quote enqueue_AQueue [code]:
  "enqueue x (AQueue xs ys) = AQueue (x # xs) ys"
  unfolding AQueue_def by simp

lemma %quote dequeue_AQueue [code]:
  "dequeue (AQueue xs []) =
    (if xs = [] then (None, AQueue [] []) else dequeue (AQueue [] (rev xs)))"
  "dequeue (AQueue xs (y # ys)) = (Some y, AQueue xs ys)"
  unfolding AQueue_def by simp_all

text {* *}

definition %quote aqueue_case [code inline]:
  "aqueue_case = queue_case"

lemma %quote case_AQueue1 [code]:
  "queue_case f (AQueue xs ys) = f (ys @ rev xs)"
  unfolding AQueue_def by simp

lemma %quote case_AQueue2 [code]:
  "aqueue_case f (AQueue xs ys) = f (ys @ rev xs)"
  unfolding aqueue_case case_AQueue1 ..

text {* *}

text %quote {*@{code_stmts empty enqueue dequeue (SML)}*}

text {*
  \noindent From this example, it can be glimpsed that using own
  constructor sets is a little delicate since it changes the set of
  valid patterns for values of that type.  Without going into much
  detail, here some practical hints:

  \begin{itemize}

    \item When changing the constructor set for datatypes, take care
      to provide an alternative for the @{text case} combinator
      (e.g.~by replacing it using the preprocessor).

    \item Values in the target language need not to be normalised --
      different values in the target language may represent the same
      value in the logic.

    \item Usually, a good methodology to deal with the subtleties of
      pattern matching is to see the type as an abstract type: provide
      a set of operations which operate on the concrete representation
      of the type, and derive further operations by combinations of
      these primitive ones, without relying on a particular
      representation.

  \end{itemize}
*}

code_datatype %invisible "0::nat" Suc
declare %invisible plus_Dig [code del]
declare %invisible One_nat_def [code inline]
declare %invisible add_Suc_shift [code] 
lemma %invisible [code]: "0 + n = (n \<Colon> nat)" by simp


subsection {* Equality and wellsortedness *}

text {*
  Surely you have already noticed how equality is treated
  by the code generator:
*}

primrec %quote collect_duplicates :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "collect_duplicates xs ys [] = xs"
  | "collect_duplicates xs ys (z#zs) = (if z \<in> set xs
      then if z \<in> set ys
        then collect_duplicates xs ys zs
        else collect_duplicates xs (z#ys) zs
      else collect_duplicates (z#xs) (z#ys) zs)"

text {*
  \noindent The membership test during preprocessing is rewritten,
  resulting in @{const List.member}, which itself
  performs an explicit equality check.
*}

text %quote {*@{code_stmts collect_duplicates (SML)}*}

text {*
  \noindent Obviously, polymorphic equality is implemented the Haskell
  way using a type class.  How is this achieved?  HOL introduces
  an explicit class @{class eq} with a corresponding operation
  @{const eq_class.eq} such that @{thm eq [no_vars]}.
  The preprocessing framework does the rest by propagating the
  @{class eq} constraints through all dependent code equations.
  For datatypes, instances of @{class eq} are implicitly derived
  when possible.  For other types, you may instantiate @{text eq}
  manually like any other type class.

  Though this @{text eq} class is designed to get rarely in
  the way, a subtlety
  enters the stage when definitions of overloaded constants
  are dependent on operational equality.  For example, let
  us define a lexicographic ordering on tuples
  (also see theory @{theory Product_ord}):
*}

instantiation %quote "*" :: (order, order) order
begin

definition %quote [code del]:
  "x \<le> y \<longleftrightarrow> fst x < fst y \<or> fst x = fst y \<and> snd x \<le> snd y"

definition %quote [code del]:
  "x < y \<longleftrightarrow> fst x < fst y \<or> fst x = fst y \<and> snd x < snd y"

instance %quote proof
qed (auto simp: less_eq_prod_def less_prod_def intro: order_less_trans)

end %quote

lemma %quote order_prod [code]:
  "(x1 \<Colon> 'a\<Colon>order, y1 \<Colon> 'b\<Colon>order) < (x2, y2) \<longleftrightarrow>
     x1 < x2 \<or> x1 = x2 \<and> y1 < y2"
  "(x1 \<Colon> 'a\<Colon>order, y1 \<Colon> 'b\<Colon>order) \<le> (x2, y2) \<longleftrightarrow>
     x1 < x2 \<or> x1 = x2 \<and> y1 \<le> y2"
  by (simp_all add: less_prod_def less_eq_prod_def)

text {*
  \noindent Then code generation will fail.  Why?  The definition
  of @{term "op \<le>"} depends on equality on both arguments,
  which are polymorphic and impose an additional @{class eq}
  class constraint, which the preprocessor does not propagate
  (for technical reasons).

  The solution is to add @{class eq} explicitly to the first sort arguments in the
  code theorems:
*}

lemma %quote order_prod_code [code]:
  "(x1 \<Colon> 'a\<Colon>{order, eq}, y1 \<Colon> 'b\<Colon>order) < (x2, y2) \<longleftrightarrow>
     x1 < x2 \<or> x1 = x2 \<and> y1 < y2"
  "(x1 \<Colon> 'a\<Colon>{order, eq}, y1 \<Colon> 'b\<Colon>order) \<le> (x2, y2) \<longleftrightarrow>
     x1 < x2 \<or> x1 = x2 \<and> y1 \<le> y2"
  by (simp_all add: less_prod_def less_eq_prod_def)

text {*
  \noindent Then code generation succeeds:
*}

text %quote {*@{code_stmts "op \<le> \<Colon> _ \<times> _ \<Rightarrow> _ \<times> _ \<Rightarrow> bool" (SML)}*}

text {*
  In some cases, the automatically derived code equations
  for equality on a particular type may not be appropriate.
  As example, watch the following datatype representing
  monomorphic parametric types (where type constructors
  are referred to by natural numbers):
*}

datatype %quote monotype = Mono nat "monotype list"
(*<*)
lemma monotype_eq:
  "eq_class.eq (Mono tyco1 typargs1) (Mono tyco2 typargs2) \<equiv> 
     eq_class.eq tyco1 tyco2 \<and> eq_class.eq typargs1 typargs2" by (simp add: eq)
(*>*)

text {*
  \noindent Then code generation for SML would fail with a message
  that the generated code contains illegal mutual dependencies:
  the theorem @{thm monotype_eq [no_vars]} already requires the
  instance @{text "monotype \<Colon> eq"}, which itself requires
  @{thm monotype_eq [no_vars]};  Haskell has no problem with mutually
  recursive @{text instance} and @{text function} definitions,
  but the SML serialiser does not support this.

  In such cases, you have to provide your own equality equations
  involving auxiliary constants.  In our case,
  @{const [show_types] list_all2} can do the job:
*}

lemma %quote monotype_eq_list_all2 [code]:
  "eq_class.eq (Mono tyco1 typargs1) (Mono tyco2 typargs2) \<longleftrightarrow>
     eq_class.eq tyco1 tyco2 \<and> list_all2 eq_class.eq typargs1 typargs2"
  by (simp add: eq list_all2_eq [symmetric])

text {*
  \noindent does not depend on instance @{text "monotype \<Colon> eq"}:
*}

text %quote {*@{code_stmts "eq_class.eq :: monotype \<Rightarrow> monotype \<Rightarrow> bool" (SML)}*}


subsection {* Explicit partiality *}

text {*
  Partiality usually enters the game by partial patterns, as
  in the following example, again for amortised queues:
*}

fun %quote strict_dequeue :: "'a queue \<Rightarrow> 'a \<times> 'a queue" where
  "strict_dequeue (Queue xs (y # ys)) = (y, Queue xs ys)"
  | "strict_dequeue (Queue xs []) =
      (case rev xs of y # ys \<Rightarrow> (y, Queue [] ys))"

text {*
  \noindent In the corresponding code, there is no equation
  for the pattern @{term "Queue [] []"}:
*}

text %quote {*@{code_stmts strict_dequeue (consts) strict_dequeue (Haskell)}*}

text {*
  \noindent In some cases it is desirable to have this
  pseudo-\qt{partiality} more explicitly, e.g.~as follows:
*}

axiomatization %quote empty_queue :: 'a

function %quote strict_dequeue' :: "'a queue \<Rightarrow> 'a \<times> 'a queue" where
  "strict_dequeue' (Queue xs []) = (if xs = [] then empty_queue
     else strict_dequeue' (Queue [] (rev xs)))"
  | "strict_dequeue' (Queue xs (y # ys)) =
       (y, Queue xs ys)"
by pat_completeness auto

termination %quote strict_dequeue'
by (relation "measure (\<lambda>q::'a queue. case q of Queue xs ys \<Rightarrow> length xs)") simp_all

text {*
  \noindent For technical reasons the definition of
  @{const strict_dequeue'} is more involved since it requires
  a manual termination proof.  Apart from that observe that
  on the right hand side of its first equation the constant
  @{const empty_queue} occurs which is unspecified.

  Normally, if constants without any code equations occur in
  a program, the code generator complains (since in most cases
  this is not what the user expects).  But such constants can also
  be thought of as function definitions with no equations which
  always fail, since there is never a successful pattern match
  on the left hand side.  In order to categorise a constant into
  that category explicitly, use @{command "code_abort"}:
*}

code_abort %quote empty_queue

text {*
  \noindent Then the code generator will just insert an error or
  exception at the appropriate position:
*}

text %quote {*@{code_stmts strict_dequeue' (consts) empty_queue strict_dequeue' (Haskell)}*}

text {*
  \noindent This feature however is rarely needed in practice.
  Note also that the @{text HOL} default setup already declares
  @{const undefined} as @{command "code_abort"}, which is most
  likely to be used in such situations.
*}

end
 