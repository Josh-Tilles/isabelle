theory Classes
imports Main Setup
begin

chapter {* Haskell-style classes with Isabelle/Isar *}

section {* Introduction *}

text {*
  Type classes were introduces by Wadler and Blott \cite{wadler89how}
  into the Haskell language, to allow for a reasonable implementation
  of overloading\footnote{throughout this tutorial, we are referring
  to classical Haskell 1.0 type classes, not considering
  later additions in expressiveness}.
  As a canonical example, a polymorphic equality function
  @{text "eq \<Colon> \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool"} which is overloaded on different
  types for @{text "\<alpha>"}, which is achieved by splitting introduction
  of the @{text eq} function from its overloaded definitions by means
  of @{text class} and @{text instance} declarations:

  \begin{quote}

  \noindent@{text "class eq where"}\footnote{syntax here is a kind of isabellized Haskell} \\
  \hspace*{2ex}@{text "eq \<Colon> \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool"}

  \medskip\noindent@{text "instance nat \<Colon> eq where"} \\
  \hspace*{2ex}@{text "eq 0 0 = True"} \\
  \hspace*{2ex}@{text "eq 0 _ = False"} \\
  \hspace*{2ex}@{text "eq _ 0 = False"} \\
  \hspace*{2ex}@{text "eq (Suc n) (Suc m) = eq n m"}

  \medskip\noindent@{text "instance (\<alpha>\<Colon>eq, \<beta>\<Colon>eq) pair \<Colon> eq where"} \\
  \hspace*{2ex}@{text "eq (x1, y1) (x2, y2) = eq x1 x2 \<and> eq y1 y2"}

  \medskip\noindent@{text "class ord extends eq where"} \\
  \hspace*{2ex}@{text "less_eq \<Colon> \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool"} \\
  \hspace*{2ex}@{text "less \<Colon> \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool"}

  \end{quote}

  \noindent Type variables are annotated with (finitely many) classes;
  these annotations are assertions that a particular polymorphic type
  provides definitions for overloaded functions.

  Indeed, type classes not only allow for simple overloading
  but form a generic calculus, an instance of order-sorted
  algebra \cite{Nipkow-Prehofer:1993,nipkow-sorts93,Wenzel:1997:TPHOL}.

  From a software engeneering point of view, type classes
  roughly correspond to interfaces in object-oriented languages like Java;
  so, it is naturally desirable that type classes do not only
  provide functions (class parameters) but also state specifications
  implementations must obey.  For example, the @{text "class eq"}
  above could be given the following specification, demanding that
  @{text "class eq"} is an equivalence relation obeying reflexivity,
  symmetry and transitivity:

  \begin{quote}

  \noindent@{text "class eq where"} \\
  \hspace*{2ex}@{text "eq \<Colon> \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool"} \\
  @{text "satisfying"} \\
  \hspace*{2ex}@{text "refl: eq x x"} \\
  \hspace*{2ex}@{text "sym: eq x y \<longleftrightarrow> eq x y"} \\
  \hspace*{2ex}@{text "trans: eq x y \<and> eq y z \<longrightarrow> eq x z"}

  \end{quote}

  \noindent From a theoretic point of view, type classes are lightweight
  modules; Haskell type classes may be emulated by
  SML functors \cite{classes_modules}. 
  Isabelle/Isar offers a discipline of type classes which brings
  all those aspects together:

  \begin{enumerate}
    \item specifying abstract parameters together with
       corresponding specifications,
    \item instantiating those abstract parameters by a particular
       type
    \item in connection with a ``less ad-hoc'' approach to overloading,
    \item with a direct link to the Isabelle module system
      (aka locales \cite{kammueller-locales}).
  \end{enumerate}

  \noindent Isar type classes also directly support code generation
  in a Haskell like fashion.

  This tutorial demonstrates common elements of structured specifications
  and abstract reasoning with type classes by the algebraic hierarchy of
  semigroups, monoids and groups.  Our background theory is that of
  Isabelle/HOL \cite{isa-tutorial}, for which some
  familiarity is assumed.

  Here we merely present the look-and-feel for end users.
  Internally, those are mapped to more primitive Isabelle concepts.
  See \cite{Haftmann-Wenzel:2006:classes} for more detail.
*}

section {* A simple algebra example \label{sec:example} *}

subsection {* Class definition *}

text {*
  Depending on an arbitrary type @{text "\<alpha>"}, class @{text
  "semigroup"} introduces a binary operator @{text "(\<otimes>)"} that is
  assumed to be associative:
*}

class %quote semigroup = type +
  fixes mult :: "\<alpha> \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>"    (infixl "\<otimes>" 70)
  assumes assoc: "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"

text {*
  \noindent This @{command class} specification consists of two
  parts: the \qn{operational} part names the class parameter
  (@{element "fixes"}), the \qn{logical} part specifies properties on them
  (@{element "assumes"}).  The local @{element "fixes"} and
  @{element "assumes"} are lifted to the theory toplevel,
  yielding the global
  parameter @{term [source] "mult \<Colon> \<alpha>\<Colon>semigroup \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>"} and the
  global theorem @{fact "semigroup.assoc:"}~@{prop [source] "\<And>x y
  z \<Colon> \<alpha>\<Colon>semigroup. (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"}.
*}


subsection {* Class instantiation \label{sec:class_inst} *}

text {*
  The concrete type @{typ int} is made a @{class semigroup}
  instance by providing a suitable definition for the class parameter
  @{text "(\<otimes>)"} and a proof for the specification of @{fact assoc}.
  This is accomplished by the @{command instantiation} target:
*}

instantiation %quote int :: semigroup
begin

definition %quote
  mult_int_def: "i \<otimes> j = i + (j\<Colon>int)"

instance %quote proof
  fix i j k :: int have "(i + j) + k = i + (j + k)" by simp
  then show "(i \<otimes> j) \<otimes> k = i \<otimes> (j \<otimes> k)"
    unfolding mult_int_def .
qed

end %quote

text {*
  \noindent @{command instantiation} allows to define class parameters
  at a particular instance using common specification tools (here,
  @{command definition}).  The concluding @{command instance}
  opens a proof that the given parameters actually conform
  to the class specification.  Note that the first proof step
  is the @{method default} method,
  which for such instance proofs maps to the @{method intro_classes} method.
  This boils down an instance judgement to the relevant primitive
  proof goals and should conveniently always be the first method applied
  in an instantiation proof.

  From now on, the type-checker will consider @{typ int}
  as a @{class semigroup} automatically, i.e.\ any general results
  are immediately available on concrete instances.

  \medskip Another instance of @{class semigroup} are the natural numbers:
*}

instantiation %quote nat :: semigroup
begin

primrec %quote mult_nat where
  "(0\<Colon>nat) \<otimes> n = n"
  | "Suc m \<otimes> n = Suc (m \<otimes> n)"

instance %quote proof
  fix m n q :: nat 
  show "m \<otimes> n \<otimes> q = m \<otimes> (n \<otimes> q)"
    by (induct m) auto
qed

end %quote

text {*
  \noindent Note the occurence of the name @{text mult_nat}
  in the primrec declaration;  by default, the local name of
  a class operation @{text f} to instantiate on type constructor
  @{text \<kappa>} are mangled as @{text f_\<kappa>}.  In case of uncertainty,
  these names may be inspected using the @{command "print_context"} command
  or the corresponding ProofGeneral button.
*}

subsection {* Lifting and parametric types *}

text {*
  Overloaded definitions giving on class instantiation
  may include recursion over the syntactic structure of types.
  As a canonical example, we model product semigroups
  using our simple algebra:
*}

instantiation %quote * :: (semigroup, semigroup) semigroup
begin

definition %quote
  mult_prod_def: "p\<^isub>1 \<otimes> p\<^isub>2 = (fst p\<^isub>1 \<otimes> fst p\<^isub>2, snd p\<^isub>1 \<otimes> snd p\<^isub>2)"

instance %quote proof
  fix p\<^isub>1 p\<^isub>2 p\<^isub>3 :: "\<alpha>\<Colon>semigroup \<times> \<beta>\<Colon>semigroup"
  show "p\<^isub>1 \<otimes> p\<^isub>2 \<otimes> p\<^isub>3 = p\<^isub>1 \<otimes> (p\<^isub>2 \<otimes> p\<^isub>3)"
    unfolding mult_prod_def by (simp add: assoc)
qed      

end %quote

text {*
  \noindent Associativity from product semigroups is
  established using
  the definition of @{text "(\<otimes>)"} on products and the hypothetical
  associativity of the type components;  these hypotheses
  are facts due to the @{class semigroup} constraints imposed
  on the type components by the @{command instance} proposition.
  Indeed, this pattern often occurs with parametric types
  and type classes.
*}


subsection {* Subclassing *}

text {*
  We define a subclass @{text monoidl} (a semigroup with a left-hand neutral)
  by extending @{class semigroup}
  with one additional parameter @{text neutral} together
  with its property:
*}

class %quote monoidl = semigroup +
  fixes neutral :: "\<alpha>" ("\<one>")
  assumes neutl: "\<one> \<otimes> x = x"

text {*
  \noindent Again, we prove some instances, by
  providing suitable parameter definitions and proofs for the
  additional specifications.  Observe that instantiations
  for types with the same arity may be simultaneous:
*}

instantiation %quote nat and int :: monoidl
begin

definition %quote
  neutral_nat_def: "\<one> = (0\<Colon>nat)"

definition %quote
  neutral_int_def: "\<one> = (0\<Colon>int)"

instance %quote proof
  fix n :: nat
  show "\<one> \<otimes> n = n"
    unfolding neutral_nat_def by simp
next
  fix k :: int
  show "\<one> \<otimes> k = k"
    unfolding neutral_int_def mult_int_def by simp
qed

end %quote

instantiation %quote * :: (monoidl, monoidl) monoidl
begin

definition %quote
  neutral_prod_def: "\<one> = (\<one>, \<one>)"

instance %quote proof
  fix p :: "\<alpha>\<Colon>monoidl \<times> \<beta>\<Colon>monoidl"
  show "\<one> \<otimes> p = p"
    unfolding neutral_prod_def mult_prod_def by (simp add: neutl)
qed

end %quote

text {*
  \noindent Fully-fledged monoids are modelled by another subclass
  which does not add new parameters but tightens the specification:
*}

class %quote monoid = monoidl +
  assumes neutr: "x \<otimes> \<one> = x"

instantiation %quote nat and int :: monoid 
begin

instance %quote proof
  fix n :: nat
  show "n \<otimes> \<one> = n"
    unfolding neutral_nat_def by (induct n) simp_all
next
  fix k :: int
  show "k \<otimes> \<one> = k"
    unfolding neutral_int_def mult_int_def by simp
qed

end %quote

instantiation %quote * :: (monoid, monoid) monoid
begin

instance %quote proof 
  fix p :: "\<alpha>\<Colon>monoid \<times> \<beta>\<Colon>monoid"
  show "p \<otimes> \<one> = p"
    unfolding neutral_prod_def mult_prod_def by (simp add: neutr)
qed

end %quote

text {*
  \noindent To finish our small algebra example, we add a @{text group} class
  with a corresponding instance:
*}

class %quote group = monoidl +
  fixes inverse :: "\<alpha> \<Rightarrow> \<alpha>"    ("(_\<div>)" [1000] 999)
  assumes invl: "x\<div> \<otimes> x = \<one>"

instantiation %quote int :: group
begin

definition %quote
  inverse_int_def: "i\<div> = - (i\<Colon>int)"

instance %quote proof
  fix i :: int
  have "-i + i = 0" by simp
  then show "i\<div> \<otimes> i = \<one>"
    unfolding mult_int_def neutral_int_def inverse_int_def .
qed

end %quote


section {* Type classes as locales *}

subsection {* A look behind the scene *}

text {*
  The example above gives an impression how Isar type classes work
  in practice.  As stated in the introduction, classes also provide
  a link to Isar's locale system.  Indeed, the logical core of a class
  is nothing else than a locale:
*}

class %quote idem = type +
  fixes f :: "\<alpha> \<Rightarrow> \<alpha>"
  assumes idem: "f (f x) = f x"

text {*
  \noindent essentially introduces the locale
*} setup %invisible {* Sign.add_path "foo" *}

locale %quote idem =
  fixes f :: "\<alpha> \<Rightarrow> \<alpha>"
  assumes idem: "f (f x) = f x"

text {* \noindent together with corresponding constant(s): *}

consts %quote f :: "\<alpha> \<Rightarrow> \<alpha>"

text {*
  \noindent The connection to the type system is done by means
  of a primitive axclass
*}

axclass %quote idem < type
  idem: "f (f x) = f x"

text {* \noindent together with a corresponding interpretation: *}

interpretation %quote idem_class:
  idem ["f \<Colon> (\<alpha>\<Colon>idem) \<Rightarrow> \<alpha>"]
proof qed (rule idem)

text {*
  \noindent This gives you at hand the full power of the Isabelle module system;
  conclusions in locale @{text idem} are implicitly propagated
  to class @{text idem}.
*} setup %invisible {* Sign.parent_path *}

subsection {* Abstract reasoning *}

text {*
  Isabelle locales enable reasoning at a general level, while results
  are implicitly transferred to all instances.  For example, we can
  now establish the @{text "left_cancel"} lemma for groups, which
  states that the function @{text "(x \<otimes>)"} is injective:
*}

lemma %quote (in group) left_cancel: "x \<otimes> y = x \<otimes> z \<longleftrightarrow> y = z"
proof
  assume "x \<otimes> y = x \<otimes> z"
  then have "x\<div> \<otimes> (x \<otimes> y) = x\<div> \<otimes> (x \<otimes> z)" by simp
  then have "(x\<div> \<otimes> x) \<otimes> y = (x\<div> \<otimes> x) \<otimes> z" using assoc by simp
  then show "y = z" using neutl and invl by simp
next
  assume "y = z"
  then show "x \<otimes> y = x \<otimes> z" by simp
qed

text {*
  \noindent Here the \qt{@{keyword "in"} @{class group}} target specification
  indicates that the result is recorded within that context for later
  use.  This local theorem is also lifted to the global one @{fact
  "group.left_cancel:"} @{prop [source] "\<And>x y z \<Colon> \<alpha>\<Colon>group. x \<otimes> y = x \<otimes>
  z \<longleftrightarrow> y = z"}.  Since type @{text "int"} has been made an instance of
  @{text "group"} before, we may refer to that fact as well: @{prop
  [source] "\<And>x y z \<Colon> int. x \<otimes> y = x \<otimes> z \<longleftrightarrow> y = z"}.
*}


subsection {* Derived definitions *}

text {*
  Isabelle locales support a concept of local definitions
  in locales:
*}

primrec %quote (in monoid) pow_nat :: "nat \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>" where
  "pow_nat 0 x = \<one>"
  | "pow_nat (Suc n) x = x \<otimes> pow_nat n x"

text {*
  \noindent If the locale @{text group} is also a class, this local
  definition is propagated onto a global definition of
  @{term [source] "pow_nat \<Colon> nat \<Rightarrow> \<alpha>\<Colon>monoid \<Rightarrow> \<alpha>\<Colon>monoid"}
  with corresponding theorems

  @{thm pow_nat.simps [no_vars]}.

  \noindent As you can see from this example, for local
  definitions you may use any specification tool
  which works together with locales (e.g. \cite{krauss2006}).
*}


subsection {* A functor analogy *}

text {*
  We introduced Isar classes by analogy to type classes
  functional programming;  if we reconsider this in the
  context of what has been said about type classes and locales,
  we can drive this analogy further by stating that type
  classes essentially correspond to functors which have
  a canonical interpretation as type classes.
  Anyway, there is also the possibility of other interpretations.
  For example, also @{text list}s form a monoid with
  @{text append} and @{term "[]"} as operations, but it
  seems inappropriate to apply to lists
  the same operations as for genuinely algebraic types.
  In such a case, we simply can do a particular interpretation
  of monoids for lists:
*}

interpretation %quote list_monoid: monoid [append "[]"]
  proof qed auto

text {*
  \noindent This enables us to apply facts on monoids
  to lists, e.g. @{thm list_monoid.neutl [no_vars]}.

  When using this interpretation pattern, it may also
  be appropriate to map derived definitions accordingly:
*}

primrec %quote replicate :: "nat \<Rightarrow> \<alpha> list \<Rightarrow> \<alpha> list" where
  "replicate 0 _ = []"
  | "replicate (Suc n) xs = xs @ replicate n xs"

interpretation %quote list_monoid: monoid [append "[]"] where
  "monoid.pow_nat append [] = replicate"
proof -
  interpret monoid [append "[]"] ..
  show "monoid.pow_nat append [] = replicate"
  proof
    fix n
    show "monoid.pow_nat append [] n = replicate n"
      by (induct n) auto
  qed
qed intro_locales


subsection {* Additional subclass relations *}

text {*
  Any @{text "group"} is also a @{text "monoid"};  this
  can be made explicit by claiming an additional
  subclass relation,
  together with a proof of the logical difference:
*}

subclass %quote (in group) monoid
proof
  fix x
  from invl have "x\<div> \<otimes> x = \<one>" by simp
  with assoc [symmetric] neutl invl have "x\<div> \<otimes> (x \<otimes> \<one>) = x\<div> \<otimes> x" by simp
  with left_cancel show "x \<otimes> \<one> = x" by simp
qed

text {*
  \noindent The logical proof is carried out on the locale level.
  Afterwards it is propagated
  to the type system, making @{text group} an instance of
  @{text monoid} by adding an additional edge
  to the graph of subclass relations
  (cf.\ \figref{fig:subclass}).

  \begin{figure}[htbp]
   \begin{center}
     \small
     \unitlength 0.6mm
     \begin{picture}(40,60)(0,0)
       \put(20,60){\makebox(0,0){@{text semigroup}}}
       \put(20,40){\makebox(0,0){@{text monoidl}}}
       \put(00,20){\makebox(0,0){@{text monoid}}}
       \put(40,00){\makebox(0,0){@{text group}}}
       \put(20,55){\vector(0,-1){10}}
       \put(15,35){\vector(-1,-1){10}}
       \put(25,35){\vector(1,-3){10}}
     \end{picture}
     \hspace{8em}
     \begin{picture}(40,60)(0,0)
       \put(20,60){\makebox(0,0){@{text semigroup}}}
       \put(20,40){\makebox(0,0){@{text monoidl}}}
       \put(00,20){\makebox(0,0){@{text monoid}}}
       \put(40,00){\makebox(0,0){@{text group}}}
       \put(20,55){\vector(0,-1){10}}
       \put(15,35){\vector(-1,-1){10}}
       \put(05,15){\vector(3,-1){30}}
     \end{picture}
     \caption{Subclass relationship of monoids and groups:
        before and after establishing the relationship
        @{text "group \<subseteq> monoid"};  transitive edges left out.}
     \label{fig:subclass}
   \end{center}
  \end{figure}

  For illustration, a derived definition
  in @{text group} which uses @{text pow_nat}:
*}

definition %quote (in group) pow_int :: "int \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>" where
  "pow_int k x = (if k >= 0
    then pow_nat (nat k) x
    else (pow_nat (nat (- k)) x)\<div>)"

text {*
  \noindent yields the global definition of
  @{term [source] "pow_int \<Colon> int \<Rightarrow> \<alpha>\<Colon>group \<Rightarrow> \<alpha>\<Colon>group"}
  with the corresponding theorem @{thm pow_int_def [no_vars]}.
*}

subsection {* A note on syntax *}

text {*
  As a commodity, class context syntax allows to refer
  to local class operations and their global counterparts
  uniformly;  type inference resolves ambiguities.  For example:
*}

context %quote semigroup
begin

term %quote "x \<otimes> y" -- {* example 1 *}
term %quote "(x\<Colon>nat) \<otimes> y" -- {* example 2 *}

end  %quote

term %quote "x \<otimes> y" -- {* example 3 *}

text {*
  \noindent Here in example 1, the term refers to the local class operation
  @{text "mult [\<alpha>]"}, whereas in example 2 the type constraint
  enforces the global class operation @{text "mult [nat]"}.
  In the global context in example 3, the reference is
  to the polymorphic global class operation @{text "mult [?\<alpha> \<Colon> semigroup]"}.
*}

section {* Type classes and code generation *}

text {*
  Turning back to the first motivation for type classes,
  namely overloading, it is obvious that overloading
  stemming from @{command class} statements and
  @{command instantiation}
  targets naturally maps to Haskell type classes.
  The code generator framework \cite{isabelle-codegen} 
  takes this into account.  Concerning target languages
  lacking type classes (e.g.~SML), type classes
  are implemented by explicit dictionary construction.
  As example, let's go back to the power function:
*}

definition %quote example :: int where
  "example = pow_int 10 (-2)"

text {*
  \noindent This maps to Haskell as:
*}

text %quote {*@{code_stmts example (Haskell)}*}

text {*
  \noindent The whole code in SML with explicit dictionary passing:
*}

text %quote {*@{code_stmts example (SML)}*}

end
