(*  Title:      Doc/Datatypes/Datatypes.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Lorenz Panny, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Author:     Dmitriy Traytel, TU Muenchen

Tutorial for (co)datatype definitions with the new package.
*)

theory Datatypes
imports Setup
keywords
  "primcorec_notyet" :: thy_decl
begin

(*<*)
(* FIXME: Temporary setup until "primcorec" and "primcorecursive" are fully implemented. *)
ML_command {*
fun add_dummy_cmd _ _ lthy = lthy;

val _ = Outer_Syntax.local_theory @{command_spec "primcorec_notyet"} ""
  (Parse.fixes -- Parse_Spec.where_alt_specs >> uncurry add_dummy_cmd);
*}
(*>*)


section {* Introduction
  \label{sec:introduction} *}

text {*
The 2013 edition of Isabelle introduced a new definitional package for freely
generated datatypes and codatatypes. The datatype support is similar to that
provided by the earlier package due to Berghofer and Wenzel
\cite{Berghofer-Wenzel:1999:TPHOL}, documented in the Isar reference manual
\cite{isabelle-isar-ref}; indeed, replacing the keyword \keyw{datatype} by
@{command datatype_new} is usually all that is needed to port existing theories
to use the new package.

Perhaps the main advantage of the new package is that it supports recursion
through a large class of non-datatypes, such as finite sets:
*}

    datatype_new 'a tree\<^sub>f\<^sub>s = Node\<^sub>f\<^sub>s (lbl\<^sub>f\<^sub>s: 'a) (sub\<^sub>f\<^sub>s: "'a tree\<^sub>f\<^sub>s fset")

text {*
\noindent
Another strong point is the support for local definitions:
*}

    context linorder
    begin
    datatype_new flag = Less | Eq | Greater
    end

text {*
\noindent
The package also provides some convenience, notably automatically generated
discriminators and selectors.

In addition to plain inductive datatypes, the new package supports coinductive
datatypes, or \emph{codatatypes}, which may have infinite values. For example,
the following command introduces the type of lazy lists, which comprises both
finite and infinite values:
*}

(*<*)
    locale early
(*>*)
    codatatype (*<*)(in early) (*>*)'a llist = LNil | LCons 'a "'a llist"

text {*
\noindent
Mixed inductive--coinductive recursion is possible via nesting. Compare the
following four Rose tree examples:
*}

    datatype_new (*<*)(in early) (*>*)'a tree\<^sub>f\<^sub>f = Node\<^sub>f\<^sub>f 'a "'a tree\<^sub>f\<^sub>f list"
    datatype_new (*<*)(in early) (*>*)'a tree\<^sub>f\<^sub>i = Node\<^sub>f\<^sub>i 'a "'a tree\<^sub>f\<^sub>i llist"
    codatatype (*<*)(in early) (*>*)'a tree\<^sub>i\<^sub>f = Node\<^sub>i\<^sub>f 'a "'a tree\<^sub>i\<^sub>f list"
    codatatype (*<*)(in early) (*>*)'a tree\<^sub>i\<^sub>i = Node\<^sub>i\<^sub>i 'a "'a tree\<^sub>i\<^sub>i llist"

text {*
The first two tree types allow only finite branches, whereas the last two allow
branches of infinite length. Orthogonally, the nodes in the first and third
types have finite branching, whereas those of the second and fourth may have
infinitely many direct subtrees.

To use the package, it is necessary to import the @{theory BNF} theory, which
can be precompiled into the \texttt{HOL-BNF} image. The following commands show
how to launch jEdit/PIDE with the image loaded and how to build the image
without launching jEdit:
*}

text {*
\noindent
\ \ \ \ \texttt{isabelle jedit -l HOL-BNF} \\
\noindent
\hbox{}\ \ \ \ \texttt{isabelle build -b HOL-BNF}
*}

text {*
The package, like its predecessor, fully adheres to the LCF philosophy
\cite{mgordon79}: The characteristic theorems associated with the specified
(co)datatypes are derived rather than introduced axiomatically.%
\footnote{If the @{text quick_and_dirty} option is enabled, some of the
internal constructions and most of the internal proof obligations are skipped.}
The package's metatheory is described in a pair of papers
\cite{traytel-et-al-2012,blanchette-et-al-wit}. The central notion is that of a
\emph{bounded natural functor} (BNF)---a well-behaved type constructor for which
nested (co)recursion is supported.

This tutorial is organized as follows:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item Section \ref{sec:defining-datatypes}, ``Defining Datatypes,''
describes how to specify datatypes using the @{command datatype_new} command.

\item Section \ref{sec:defining-recursive-functions}, ``Defining Recursive
Functions,'' describes how to specify recursive functions using
@{command primrec_new}, \keyw{fun}, and \keyw{function}.

\item Section \ref{sec:defining-codatatypes}, ``Defining Codatatypes,''
describes how to specify codatatypes using the @{command codatatype} command.

\item Section \ref{sec:defining-corecursive-functions}, ``Defining Corecursive
Functions,'' describes how to specify corecursive functions using the
@{command primcorec} and @{command primcorecursive} commands.

\item Section \ref{sec:registering-bounded-natural-functors}, ``Registering
Bounded Natural Functors,'' explains how to use the @{command bnf} command
to register arbitrary type constructors as BNFs.

\item Section
\ref{sec:deriving-destructors-and-theorems-for-free-constructors},
``Deriving Destructors and Theorems for Free Constructors,'' explains how to
use the command @{command wrap_free_constructors} to derive destructor constants
and theorems for freely generated types, as performed internally by @{command
datatype_new} and @{command codatatype}.

%\item Section \ref{sec:standard-ml-interface}, ``Standard ML Interface,''
%describes the package's programmatic interface.

%\item Section \ref{sec:interoperability}, ``Interoperability,''
%is concerned with the packages' interaction with other Isabelle packages and
%tools, such as the code generator and the counterexample generators.

%\item Section \ref{sec:known-bugs-and-limitations}, ``Known Bugs and
%Limitations,'' concludes with known open issues at the time of writing.
\end{itemize}


\newbox\boxA
\setbox\boxA=\hbox{\texttt{nospam}}

\newcommand\authoremaili{\texttt{blan{\color{white}nospam}\kern-\wd\boxA{}chette@\allowbreak
in.\allowbreak tum.\allowbreak de}}
\newcommand\authoremailii{\texttt{lore{\color{white}nospam}\kern-\wd\boxA{}nz.panny@\allowbreak
\allowbreak tum.\allowbreak de}}
\newcommand\authoremailiii{\texttt{pope{\color{white}nospam}\kern-\wd\boxA{}scua@\allowbreak
in.\allowbreak tum.\allowbreak de}}
\newcommand\authoremailiv{\texttt{tray{\color{white}nospam}\kern-\wd\boxA{}tel@\allowbreak
in.\allowbreak tum.\allowbreak de}}

The commands @{command datatype_new} and @{command primrec_new} are expected to
displace \keyw{datatype} and \keyw{primrec} in a future release. Authors of new
theories are encouraged to use the new commands, and maintainers of older
theories may want to consider upgrading.

Comments and bug reports concerning either the tool or this tutorial should be
directed to the authors at \authoremaili, \authoremailii, \authoremailiii,
and \authoremailiv.

\begin{framed}
\noindent
\textbf{Warning:}\enskip This tutorial and the package it describes are under
construction. Please apologise for their appearance. Should you have suggestions
or comments regarding either, please let the authors know.
\end{framed}
*}


section {* Defining Datatypes
  \label{sec:defining-datatypes} *}

text {*
Datatypes can be specified using the @{command datatype_new} command.
*}


subsection {* Introductory Examples
  \label{ssec:datatype-introductory-examples} *}

text {*
Datatypes are illustrated through concrete examples featuring different flavors
of recursion. More examples can be found in the directory
\verb|~~/src/HOL/BNF/Examples|.
*}

subsubsection {* Nonrecursive Types
  \label{sssec:datatype-nonrecursive-types} *}

text {*
Datatypes are introduced by specifying the desired names and argument types for
their constructors. \emph{Enumeration} types are the simplest form of datatype.
All their constructors are nullary:
*}

    datatype_new trool = Truue | Faalse | Perhaaps

text {*
\noindent
Here, @{const Truue}, @{const Faalse}, and @{const Perhaaps} have the type @{typ trool}.

Polymorphic types are possible, such as the following option type, modeled after
its homologue from the @{theory Option} theory:
*}

(*<*)
    hide_const None Some
(*>*)
    datatype_new 'a option = None | Some 'a

text {*
\noindent
The constructors are @{text "None :: 'a option"} and
@{text "Some :: 'a \<Rightarrow> 'a option"}.

The next example has three type parameters:
*}

    datatype_new ('a, 'b, 'c) triple = Triple 'a 'b 'c

text {*
\noindent
The constructor is
@{text "Triple :: 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> ('a, 'b, 'c) triple"}.
Unlike in Standard ML, curried constructors are supported. The uncurried variant
is also possible:
*}

    datatype_new ('a, 'b, 'c) triple\<^sub>u = Triple\<^sub>u "'a * 'b * 'c"


subsubsection {* Simple Recursion
  \label{sssec:datatype-simple-recursion} *}

text {*
Natural numbers are the simplest example of a recursive type:
*}

    datatype_new nat = Zero | Suc nat

text {*
\noindent
Lists were shown in the introduction. Terminated lists are a variant:
*}

    datatype_new (*<*)(in early) (*>*)('a, 'b) tlist = TNil 'b | TCons 'a "('a, 'b) tlist"

text {*
\noindent
Occurrences of nonatomic types on the right-hand side of the equal sign must be
enclosed in double quotes, as is customary in Isabelle.
*}


subsubsection {* Mutual Recursion
  \label{sssec:datatype-mutual-recursion} *}

text {*
\emph{Mutually recursive} types are introduced simultaneously and may refer to
each other. The example below introduces a pair of types for even and odd
natural numbers:
*}

    datatype_new even_nat = Even_Zero | Even_Suc odd_nat
    and odd_nat = Odd_Suc even_nat

text {*
\noindent
Arithmetic expressions are defined via terms, terms via factors, and factors via
expressions:
*}

    datatype_new ('a, 'b) exp =
      Term "('a, 'b) trm" | Sum "('a, 'b) trm" "('a, 'b) exp"
    and ('a, 'b) trm =
      Factor "('a, 'b) fct" | Prod "('a, 'b) fct" "('a, 'b) trm"
    and ('a, 'b) fct =
      Const 'a | Var 'b | Expr "('a, 'b) exp"


subsubsection {* Nested Recursion
  \label{sssec:datatype-nested-recursion} *}

text {*
\emph{Nested recursion} occurs when recursive occurrences of a type appear under
a type constructor. The introduction showed some examples of trees with nesting
through lists. A more complex example, that reuses our @{type option} type,
follows:
*}

    datatype_new 'a btree =
      BNode 'a "'a btree option" "'a btree option"

text {*
\noindent
Not all nestings are admissible. For example, this command will fail:
*}

    datatype_new 'a wrong = Wrong (*<*)'a
    typ (*>*)"'a wrong \<Rightarrow> 'a"

text {*
\noindent
The issue is that the function arrow @{text "\<Rightarrow>"} allows recursion
only through its right-hand side. This issue is inherited by polymorphic
datatypes defined in terms of~@{text "\<Rightarrow>"}:
*}

    datatype_new ('a, 'b) fn = Fn "'a \<Rightarrow> 'b"
    datatype_new 'a also_wrong = Also_Wrong (*<*)'a
    typ (*>*)"('a also_wrong, 'a) fn"

text {*
\noindent
This is legal:
*}

    datatype_new 'a ftree = FTLeaf 'a | FTNode "'a \<Rightarrow> 'a ftree"

text {*
\noindent
In general, type constructors @{text "('a\<^sub>1, \<dots>, 'a\<^sub>m) t"}
allow recursion on a subset of their type arguments @{text 'a\<^sub>1}, \ldots,
@{text 'a\<^sub>m}. These type arguments are called \emph{live}; the remaining
type arguments are called \emph{dead}. In @{typ "'a \<Rightarrow> 'b"} and
@{typ "('a, 'b) fn"}, the type variable @{typ 'a} is dead and @{typ 'b} is live.

Type constructors must be registered as BNFs to have live arguments. This is
done automatically for datatypes and codatatypes introduced by the @{command
datatype_new} and @{command codatatype} commands.
Section~\ref{sec:registering-bounded-natural-functors} explains how to register
arbitrary type constructors as BNFs.
*}


subsubsection {* Custom Names and Syntaxes
  \label{sssec:datatype-custom-names-and-syntaxes} *}

text {*
The @{command datatype_new} command introduces various constants in addition to
the constructors. With each datatype are associated set functions, a map
function, a relator, discriminators, and selectors, all of which can be given
custom names. In the example below, the traditional names
@{text set}, @{text map}, @{text list_all2}, @{text null}, @{text hd}, and
@{text tl} override the default names @{text list_set}, @{text list_map}, @{text
list_rel}, @{text is_Nil}, @{text un_Cons1}, and @{text un_Cons2}:
*}

(*<*)
    no_translations
      "[x, xs]" == "x # [xs]"
      "[x]" == "x # []"

    no_notation
      Nil ("[]") and
      Cons (infixr "#" 65)

    hide_type list
    hide_const Nil Cons hd tl set map list_all2 list_case list_rec

    context early begin
(*>*)
    datatype_new (set: 'a) list (map: map rel: list_all2) =
      null: Nil (defaults tl: Nil)
    | Cons (hd: 'a) (tl: "'a list")

text {*
\noindent
The command introduces a discriminator @{const null} and a pair of selectors
@{const hd} and @{const tl} characterized as follows:
%
\[@{thm list.collapse(1)[of xs, no_vars]}
  \qquad @{thm list.collapse(2)[of xs, no_vars]}\]
%
For two-constructor datatypes, a single discriminator constant suffices. The
discriminator associated with @{const Cons} is simply
@{term "\<lambda>xs. \<not> null xs"}.

The @{text defaults} clause following the @{const Nil} constructor specifies a
default value for selectors associated with other constructors. Here, it is used
to ensure that the tail of the empty list is itself (instead of being left
unspecified).

Because @{const Nil} is nullary, it is also possible to use
@{term "\<lambda>xs. xs = Nil"} as a discriminator. This is specified by
entering ``@{text "="}'' instead of the identifier @{const null}. Although this
may look appealing, the mixture of constructors and selectors in the
characteristic theorems can lead Isabelle's automation to switch between the
constructor and the destructor view in surprising ways.

The usual mixfix syntaxes are available for both types and constructors. For
example:
*}

(*<*)
    end
(*>*)
    datatype_new ('a, 'b) prod (infixr "*" 20) = Pair 'a 'b

text {* \blankline *}

    datatype_new (set: 'a) list (map: map rel: list_all2) =
      null: Nil ("[]")
    | Cons (hd: 'a) (tl: "'a list") (infixr "#" 65)

text {*
\noindent
Incidentally, this is how the traditional syntaxes can be set up:
*}

    syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]")

text {* \blankline *}

    translations
      "[x, xs]" == "x # [xs]"
      "[x]" == "x # []"


subsection {* Command Syntax
  \label{ssec:datatype-command-syntax} *}


subsubsection {* \keyw{datatype\_new}
  \label{sssec:datatype-new} *}

text {*
\begin{matharray}{rcl}
  @{command_def "datatype_new"} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail "
  @@{command datatype_new} target? @{syntax dt_options}? \\
    (@{syntax dt_name} '=' (@{syntax ctor} + '|') + @'and')
  ;
  @{syntax_def dt_options}: '(' (('no_discs_sels' | 'rep_compat') + ',') ')'
"}

The syntactic quantity \synt{target} can be used to specify a local
context---e.g., @{text "(in linorder)"}. It is documented in the Isar reference
manual \cite{isabelle-isar-ref}.
%
The optional target is optionally followed by datatype-specific options:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item
The @{text "no_discs_sels"} option indicates that no discriminators or selectors
should be generated.

\item
The @{text "rep_compat"} option indicates that the generated names should
contain optional (and normally not displayed) ``@{text "new."}'' components to
prevent clashes with a later call to \keyw{rep\_datatype}. See
Section~\ref{ssec:datatype-compatibility-issues} for details.
\end{itemize}

The left-hand sides of the datatype equations specify the name of the type to
define, its type parameters, and additional information:

@{rail "
  @{syntax_def dt_name}: @{syntax tyargs}? name @{syntax map_rel}? mixfix?
  ;
  @{syntax_def tyargs}: typefree | '(' ((name ':')? typefree + ',') ')'
  ;
  @{syntax_def map_rel}: '(' ((('map' | 'rel') ':' name) +) ')'
"}

\noindent
The syntactic quantity \synt{name} denotes an identifier, \synt{typefree}
denotes fixed type variable (@{typ 'a}, @{typ 'b}, \ldots), and \synt{mixfix}
denotes the usual parenthesized mixfix notation. They are documented in the Isar
reference manual \cite{isabelle-isar-ref}.

The optional names preceding the type variables allow to override the default
names of the set functions (@{text t_set1}, \ldots, @{text t_setM}).
Inside a mutually recursive specification, all defined datatypes must
mention exactly the same type variables in the same order.

@{rail "
  @{syntax_def ctor}: (name ':')? name (@{syntax ctor_arg} * ) \\
    @{syntax dt_sel_defaults}? mixfix?
"}

\medskip

\noindent
The main constituents of a constructor specification is the name of the
constructor and the list of its argument types. An optional discriminator name
can be supplied at the front to override the default name
(@{text t.is_C\<^sub>j}).

@{rail "
  @{syntax_def ctor_arg}: type | '(' name ':' type ')'
"}

\medskip

\noindent
In addition to the type of a constructor argument, it is possible to specify a
name for the corresponding selector to override the default name
(@{text un_C\<^sub>ji}). The same selector names can be reused for several
constructors as long as they share the same type.

@{rail "
  @{syntax_def dt_sel_defaults}: '(' 'defaults' (name ':' term +) ')'
"}

\noindent
Given a constructor
@{text "C \<Colon> \<sigma>\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> \<sigma>\<^sub>p \<Rightarrow> \<sigma>"},
default values can be specified for any selector
@{text "un_D \<Colon> \<sigma> \<Rightarrow> \<tau>"}
associated with other constructors. The specified default value must be of type
@{text "\<sigma>\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> \<sigma>\<^sub>p \<Rightarrow> \<tau>"}
(i.e., it may depends on @{text C}'s arguments).
*}


subsubsection {* \keyw{datatype\_new\_compat}
  \label{sssec:datatype-new-compat} *}

text {*
\begin{matharray}{rcl}
  @{command_def "datatype_new_compat"} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail "
  @@{command datatype_new_compat} names
"}

\noindent
The old datatype package provides some functionality that is not yet replicated
in the new package:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item It is integrated with \keyw{fun} and \keyw{function}
\cite{isabelle-function}, Nitpick \cite{isabelle-nitpick}, Quickcheck,
and other packages.

\item It is extended by various add-ons, notably to produce instances of the
@{const size} function.
\end{itemize}

\noindent
New-style datatypes can in most case be registered as old-style datatypes using
@{command datatype_new_compat}. The \textit{names} argument is a space-separated
list of type names that are mutually recursive. For example:
*}

    datatype_new_compat even_nat odd_nat

text {* \blankline *}

    thm even_nat_odd_nat.size

text {* \blankline *}

    ML {* Datatype_Data.get_info @{theory} @{type_name even_nat} *}

text {*
A few remarks concern nested recursive datatypes only:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item The old-style, nested-as-mutual induction rule, iterator theorems, and
recursor theorems are generated under their usual names but with ``@{text
"compat_"}'' prefixed (e.g., @{text compat_tree.induct}).

\item All types through which recursion takes place must be new-style datatypes
or the function type. In principle, it should be possible to support old-style
datatypes as well, but the command does not support this yet (and there is
currently no way to register old-style datatypes as new-style datatypes).
\end{itemize}

An alternative to @{command datatype_new_compat} is to use the old package's
\keyw{rep\_datatype} command. The associated proof obligations must then be
discharged manually.
*}


subsection {* Generated Constants
  \label{ssec:datatype-generated-constants} *}

text {*
Given a datatype @{text "('a\<^sub>1, \<dots>, 'a\<^sub>m) t"}
with $m > 0$ live type variables and $n$ constructors
@{text "t.C\<^sub>1"}, \ldots, @{text "t.C\<^sub>n"}, the
following auxiliary constants are introduced:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item \relax{Case combinator}: @{text t_case} (rendered using the familiar
@{text case}--@{text of} syntax)

\item \relax{Discriminators}: @{text "t.is_C\<^sub>1"}, \ldots,
@{text "t.is_C\<^sub>n"}

\item \relax{Selectors}:
@{text t.un_C\<^sub>11}$, \ldots, @{text t.un_C\<^sub>1k\<^sub>1}, \\
\phantom{\relax{Selectors:}} \quad\vdots \\
\phantom{\relax{Selectors:}} @{text t.un_C\<^sub>n1}$, \ldots, @{text t.un_C\<^sub>nk\<^sub>n}.

\item \relax{Set functions} (or \relax{natural transformations}):
@{text t_set1}, \ldots, @{text t_setm}

\item \relax{Map function} (or \relax{functorial action}): @{text t_map}

\item \relax{Relator}: @{text t_rel}

\item \relax{Iterator}: @{text t_fold}

\item \relax{Recursor}: @{text t_rec}

\end{itemize}

\noindent
The case combinator, discriminators, and selectors are collectively called
\emph{destructors}. The prefix ``@{text "t."}'' is an optional component of the
name and is normally hidden. 
*}


subsection {* Generated Theorems
  \label{ssec:datatype-generated-theorems} *}

text {*
The characteristic theorems generated by @{command datatype_new} are grouped in
three broad categories:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item The \emph{free constructor theorems} are properties about the constructors
and destructors that can be derived for any freely generated type. Internally,
the derivation is performed by @{command wrap_free_constructors}.

\item The \emph{functorial theorems} are properties of datatypes related to
their BNF nature.

\item The \emph{inductive theorems} are properties of datatypes related to
their inductive nature.

\end{itemize}

\noindent
The full list of named theorems can be obtained as usual by entering the
command \keyw{print\_theorems} immediately after the datatype definition.
This list normally excludes low-level theorems that reveal internal
constructions. To make these accessible, add the line
*}

    declare [[bnf_note_all]]
(*<*)
    declare [[bnf_note_all = false]]
(*>*)

text {*
\noindent
to the top of the theory file.
*}

subsubsection {* Free Constructor Theorems
  \label{sssec:free-constructor-theorems} *}

(*<*)
    consts is_Cons :: 'a
(*>*)

text {*
The first subgroup of properties are concerned with the constructors.
They are listed below for @{typ "'a list"}:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{inject} @{text "[iff, induct_simp]"}\rm:] ~ \\
@{thm list.inject[no_vars]}

\item[@{text "t."}\hthm{distinct} @{text "[simp, induct_simp]"}\rm:] ~ \\
@{thm list.distinct(1)[no_vars]} \\
@{thm list.distinct(2)[no_vars]}

\item[@{text "t."}\hthm{exhaust} @{text "[cases t, case_names C\<^sub>1 \<dots> C\<^sub>n]"}\rm:] ~ \\
@{thm list.exhaust[no_vars]}

\item[@{text "t."}\hthm{nchotomy}\rm:] ~ \\
@{thm list.nchotomy[no_vars]}

\end{description}
\end{indentblock}

\noindent
In addition, these nameless theorems are registered as safe elimination rules:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{list.distinct {\upshape[}THEN notE}@{text ", elim!"}\hthm{\upshape]}\rm:] ~ \\
@{thm list.distinct(1)[THEN notE, elim!, no_vars]} \\
@{thm list.distinct(2)[THEN notE, elim!, no_vars]}

\end{description}
\end{indentblock}

\noindent
The next subgroup is concerned with the case combinator:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{case} @{text "[simp, code]"}\rm:] ~ \\
@{thm list.case(1)[no_vars]} \\
@{thm list.case(2)[no_vars]}

\item[@{text "t."}\hthm{case\_cong}\rm:] ~ \\
@{thm list.case_cong[no_vars]}

\item[@{text "t."}\hthm{weak\_case\_cong} @{text "[cong]"}\rm:] ~ \\
@{thm list.weak_case_cong[no_vars]}

\item[@{text "t."}\hthm{split}\rm:] ~ \\
@{thm list.split[no_vars]}

\item[@{text "t."}\hthm{split\_asm}\rm:] ~ \\
@{thm list.split_asm[no_vars]}

\item[@{text "t."}\hthm{splits} = @{text "split split_asm"}]

\end{description}
\end{indentblock}

\noindent
The third and last subgroup revolves around discriminators and selectors:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{disc} @{text "[simp]"}\rm:] ~ \\
@{thm list.disc(1)[no_vars]} \\
@{thm list.disc(2)[no_vars]}

\item[@{text "t."}\hthm{discI}\rm:] ~ \\
@{thm list.discI(1)[no_vars]} \\
@{thm list.discI(2)[no_vars]}

\item[@{text "t."}\hthm{sel} @{text "[simp, code]"}\rm:] ~ \\
@{thm list.sel(1)[no_vars]} \\
@{thm list.sel(2)[no_vars]}

\item[@{text "t."}\hthm{collapse} @{text "[simp]"}\rm:] ~ \\
@{thm list.collapse(1)[no_vars]} \\
@{thm list.collapse(2)[no_vars]}

\item[@{text "t."}\hthm{disc\_exclude}\rm:] ~ \\
These properties are missing for @{typ "'a list"} because there is only one
proper discriminator. Had the datatype been introduced with a second
discriminator called @{const is_Cons}, they would have read thusly: \\[\jot]
@{prop "null list \<Longrightarrow> \<not> is_Cons list"} \\
@{prop "is_Cons list \<Longrightarrow> \<not> null list"}

\item[@{text "t."}\hthm{disc\_exhaust} @{text "[case_names C\<^sub>1 \<dots> C\<^sub>n]"}\rm:] ~ \\
@{thm list.disc_exhaust[no_vars]}

\item[@{text "t."}\hthm{expand}\rm:] ~ \\
@{thm list.expand[no_vars]}

\item[@{text "t."}\hthm{case\_conv}\rm:] ~ \\
@{thm list.case_conv[no_vars]}

\end{description}
\end{indentblock}
*}


subsubsection {* Functorial Theorems
  \label{sssec:functorial-theorems} *}

text {*
The BNF-related theorem are as follows:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{set} @{text "[simp, code]"}\rm:] ~ \\
@{thm list.set(1)[no_vars]} \\
@{thm list.set(2)[no_vars]}

\item[@{text "t."}\hthm{map} @{text "[simp, code]"}\rm:] ~ \\
@{thm list.map(1)[no_vars]} \\
@{thm list.map(2)[no_vars]}

\item[@{text "t."}\hthm{rel\_inject} @{text "[simp, code]"}\rm:] ~ \\
@{thm list.rel_inject(1)[no_vars]} \\
@{thm list.rel_inject(2)[no_vars]}

\item[@{text "t."}\hthm{rel\_distinct} @{text "[simp, code]"}\rm:] ~ \\
@{thm list.rel_distinct(1)[no_vars]} \\
@{thm list.rel_distinct(2)[no_vars]}

\end{description}
\end{indentblock}
*}


subsubsection {* Inductive Theorems
  \label{sssec:inductive-theorems} *}

text {*
The inductive theorems are as follows:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{induct} @{text "[induct t, case_names C\<^sub>1 \<dots> C\<^sub>n]"}\rm:] ~ \\
@{thm list.induct[no_vars]}

\item[@{text "t\<^sub>1_\<dots>_t\<^sub>m."}\hthm{induct} @{text "[case_names C\<^sub>1 \<dots> C\<^sub>n]"}\rm:] ~ \\
Given $m > 1$ mutually recursive datatypes, this induction rule can be used to
prove $m$ properties simultaneously.

\item[@{text "t."}\hthm{fold} @{text "[simp, code]"}\rm:] ~ \\
@{thm list.fold(1)[no_vars]} \\
@{thm list.fold(2)[no_vars]}

\item[@{text "t."}\hthm{rec} @{text "[simp, code]"}\rm:] ~ \\
@{thm list.rec(1)[no_vars]} \\
@{thm list.rec(2)[no_vars]}

\end{description}
\end{indentblock}

\noindent
For convenience, @{command datatype_new} also provides the following collection:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{simps} = @{text t.inject} @{text t.distinct} @{text t.case} @{text t.rec} @{text t.fold} @{text t.map} @{text t.rel_inject}] ~ \\
@{text t.rel_distinct} @{text t.set}

\end{description}
\end{indentblock}
*}


subsection {* Compatibility Issues
  \label{ssec:datatype-compatibility-issues} *}

text {*
The command @{command datatype_new} was designed to be highly compatible with
\keyw{datatype}, to ease migration. There are nonetheless a number of
incompatibilities that may arise when porting to the new package:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item \emph{The Standard ML interfaces are different.} Tools and extensions
written to call the old ML interfaces will need to be adapted to the new
interfaces. Little has been done so far in this direction. Whenever possible, it
is recommended to use @{command datatype_new_compat} or \keyw{rep\_datatype}
to register new-style datatypes as old-style datatypes.

\item \emph{The recursor @{text "t_rec"} has a different signature for nested
recursive datatypes.} In the old package, nested recursion was internally
reduced to mutual recursion. This reduction was visible in the type of the
recursor, used by \keyw{primrec}. In the new package, nested recursion is
handled in a more modular fashion. The old-style recursor can be generated on
demand using @{command primrec_new}, as explained in
Section~\ref{sssec:primrec-nested-as-mutual-recursion}, if the recursion is via
new-style datatypes.

\item \emph{Accordingly, the induction principle is different for nested
recursive datatypes.} Again, the old-style induction principle can be generated
on demand using @{command primrec_new}, as explained in
Section~\ref{sssec:primrec-nested-as-mutual-recursion}, if the recursion is via
new-style datatypes.

\item \emph{The internal constructions are completely different.} Proofs texts
that unfold the definition of constants introduced by \keyw{datatype} will be
difficult to port.

\item \emph{A few theorems have different names.}
The properties @{text t.cases} and @{text t.recs} have been renamed to
@{text t.case} and @{text t.rec}. For non-mutually recursive datatypes,
@{text t.inducts} is available as @{text t.induct}.
For $m > 1$ mutually recursive datatypes,
@{text "t\<^sub>1_\<dots>_t\<^sub>m.inducts(i)"} has been renamed to
@{text "t\<^sub>i.induct"}.

\item \emph{The @{text t.simps} collection has been extended.}
Previously available theorems are available at the same index.

\item \emph{Variables in generated properties have different names.} This is
rarely an issue, except in proof texts that refer to variable names in the
@{text "[where \<dots>]"} attribute. The solution is to use the more robust
@{text "[of \<dots>]"} syntax.
\end{itemize}

In the other direction, there is currently no way to register old-style
datatypes as new-style datatypes. If the goal is to define new-style datatypes
with nested recursion through old-style datatypes, the old-style
datatypes can be registered as a BNF
(Section~\ref{sec:registering-bounded-natural-functors}). If the goal is
to derive discriminators and selectors, this can be achieved using @{command
wrap_free_constructors}
(Section~\ref{sec:deriving-destructors-and-theorems-for-free-constructors}).
*}


section {* Defining Recursive Functions
  \label{sec:defining-recursive-functions} *}

text {*
Recursive functions over datatypes can be specified using @{command
primrec_new}, which supports primitive recursion, or using the more general
\keyw{fun} and \keyw{function} commands. Here, the focus is on @{command
primrec_new}; the other two commands are described in a separate tutorial
\cite{isabelle-function}.

%%% TODO: partial_function
*}


subsection {* Introductory Examples
  \label{ssec:primrec-introductory-examples} *}

text {*
Primitive recursion is illustrated through concrete examples based on the
datatypes defined in Section~\ref{ssec:datatype-introductory-examples}. More
examples can be found in the directory \verb|~~/src/HOL/BNF/Examples|.
*}


subsubsection {* Nonrecursive Types
  \label{sssec:primrec-nonrecursive-types} *}

text {*
Primitive recursion removes one layer of constructors on the left-hand side in
each equation. For example:
*}

    primrec_new bool_of_trool :: "trool \<Rightarrow> bool" where
      "bool_of_trool Faalse \<longleftrightarrow> False" |
      "bool_of_trool Truue \<longleftrightarrow> True"

text {* \blankline *}

    primrec_new the_list :: "'a option \<Rightarrow> 'a list" where
      "the_list None = []" |
      "the_list (Some a) = [a]"

text {* \blankline *}

    primrec_new the_default :: "'a \<Rightarrow> 'a option \<Rightarrow> 'a" where
      "the_default d None = d" |
      "the_default _ (Some a) = a"

text {* \blankline *}

    primrec_new mirrror :: "('a, 'b, 'c) triple \<Rightarrow> ('c, 'b, 'a) triple" where
      "mirrror (Triple a b c) = Triple c b a"

text {*
\noindent
The equations can be specified in any order, and it is acceptable to leave out
some cases, which are then unspecified. Pattern matching on the left-hand side
is restricted to a single datatype, which must correspond to the same argument
in all equations.
*}


subsubsection {* Simple Recursion
  \label{sssec:primrec-simple-recursion} *}

text {*
For simple recursive types, recursive calls on a constructor argument are
allowed on the right-hand side:
*}

    primrec_new replicate :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
      "replicate Zero _ = []" |
      "replicate (Suc n) x = x # replicate n x"

text {* \blankline *}

    primrec_new at :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" where
      "at (x # xs) j =
         (case j of
            Zero \<Rightarrow> x
          | Suc j' \<Rightarrow> at xs j')"

text {* \blankline *}

    primrec_new (*<*)(in early) (*>*)tfold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) tlist \<Rightarrow> 'b" where
      "tfold _ (TNil y) = y" |
      "tfold f (TCons x xs) = f x (tfold f xs)"

text {*
\noindent
The next example is not primitive recursive, but it can be defined easily using
\keyw{fun}. The @{command datatype_new_compat} command is needed to register
new-style datatypes for use with \keyw{fun} and \keyw{function}
(Section~\ref{sssec:datatype-new-compat}):
*}

    datatype_new_compat nat

text {* \blankline *}

    fun at_least_two :: "nat \<Rightarrow> bool" where
      "at_least_two (Suc (Suc _)) \<longleftrightarrow> True" |
      "at_least_two _ \<longleftrightarrow> False"


subsubsection {* Mutual Recursion
  \label{sssec:primrec-mutual-recursion} *}

text {*
The syntax for mutually recursive functions over mutually recursive datatypes
is straightforward:
*}

    primrec_new
      nat_of_even_nat :: "even_nat \<Rightarrow> nat" and
      nat_of_odd_nat :: "odd_nat \<Rightarrow> nat"
    where
      "nat_of_even_nat Even_Zero = Zero" |
      "nat_of_even_nat (Even_Suc n) = Suc (nat_of_odd_nat n)" |
      "nat_of_odd_nat (Odd_Suc n) = Suc (nat_of_even_nat n)"

text {* \blankline *}

    primrec_new
      eval\<^sub>e :: "('a \<Rightarrow> int) \<Rightarrow> ('b \<Rightarrow> int) \<Rightarrow> ('a, 'b) exp \<Rightarrow> int" and
      eval\<^sub>t :: "('a \<Rightarrow> int) \<Rightarrow> ('b \<Rightarrow> int) \<Rightarrow> ('a, 'b) trm \<Rightarrow> int" and
      eval\<^sub>f :: "('a \<Rightarrow> int) \<Rightarrow> ('b \<Rightarrow> int) \<Rightarrow> ('a, 'b) fct \<Rightarrow> int"
    where
      "eval\<^sub>e \<gamma> \<xi> (Term t) = eval\<^sub>t \<gamma> \<xi> t" |
      "eval\<^sub>e \<gamma> \<xi> (Sum t e) = eval\<^sub>t \<gamma> \<xi> t + eval\<^sub>e \<gamma> \<xi> e" |
      "eval\<^sub>t \<gamma> \<xi> (Factor f) = eval\<^sub>f \<gamma> \<xi> f" |
      "eval\<^sub>t \<gamma> \<xi> (Prod f t) = eval\<^sub>f \<gamma> \<xi> f + eval\<^sub>t \<gamma> \<xi> t" |
      "eval\<^sub>f \<gamma> _ (Const a) = \<gamma> a" |
      "eval\<^sub>f _ \<xi> (Var b) = \<xi> b" |
      "eval\<^sub>f \<gamma> \<xi> (Expr e) = eval\<^sub>e \<gamma> \<xi> e"

text {*
\noindent
Mutual recursion is possible within a single type, using \keyw{fun}:
*}

    fun
      even :: "nat \<Rightarrow> bool" and
      odd :: "nat \<Rightarrow> bool"
    where
      "even Zero = True" |
      "even (Suc n) = odd n" |
      "odd Zero = False" |
      "odd (Suc n) = even n"


subsubsection {* Nested Recursion
  \label{sssec:primrec-nested-recursion} *}

text {*
In a departure from the old datatype package, nested recursion is normally
handled via the map functions of the nesting type constructors. For example,
recursive calls are lifted to lists using @{const map}:
*}

(*<*)
    datatype_new 'a tree\<^sub>f\<^sub>f = Node\<^sub>f\<^sub>f (lbl\<^sub>f\<^sub>f: 'a) (sub\<^sub>f\<^sub>f: "'a tree\<^sub>f\<^sub>f list")
(*>*)
    primrec_new at\<^sub>f\<^sub>f :: "'a tree\<^sub>f\<^sub>f \<Rightarrow> nat list \<Rightarrow> 'a" where
      "at\<^sub>f\<^sub>f (Node\<^sub>f\<^sub>f a ts) js =
         (case js of
            [] \<Rightarrow> a
          | j # js' \<Rightarrow> at (map (\<lambda>t. at\<^sub>f\<^sub>f t js') ts) j)"

text {*
\noindent
The next example features recursion through the @{text option} type. Although
@{text option} is not a new-style datatype, it is registered as a BNF with the
map function @{const option_map}:
*}

    primrec_new (*<*)(in early) (*>*)sum_btree :: "('a\<Colon>{zero,plus}) btree \<Rightarrow> 'a" where
      "sum_btree (BNode a lt rt) =
         a + the_default 0 (option_map sum_btree lt) +
           the_default 0 (option_map sum_btree rt)"

text {*
\noindent
The same principle applies for arbitrary type constructors through which
recursion is possible. Notably, the map function for the function type
(@{text \<Rightarrow>}) is simply composition (@{text "op \<circ>"}):
*}

    primrec_new ftree_map :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a ftree \<Rightarrow> 'a ftree" where
      "ftree_map f (FTLeaf x) = FTLeaf (f x)" |
      "ftree_map f (FTNode g) = FTNode (ftree_map f \<circ> g)"

text {*
\noindent
(No such function is defined by the package because @{typ 'a} is dead in
@{typ "'a ftree"}, but we can easily do it ourselves.)
*}


subsubsection {* Nested-as-Mutual Recursion
  \label{sssec:primrec-nested-as-mutual-recursion} *}

(*<*)
    locale n2m begin
(*>*)

text {*
For compatibility with the old package, but also because it is sometimes
convenient in its own right, it is possible to treat nested recursive datatypes
as mutually recursive ones if the recursion takes place though new-style
datatypes. For example:
*}

    primrec_new
      at\<^sub>f\<^sub>f :: "'a tree\<^sub>f\<^sub>f \<Rightarrow> nat list \<Rightarrow> 'a" and
      ats\<^sub>f\<^sub>f :: "'a tree\<^sub>f\<^sub>f list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a"
    where
      "at\<^sub>f\<^sub>f (Node\<^sub>f\<^sub>f a ts) js =
         (case js of
            [] \<Rightarrow> a
          | j # js' \<Rightarrow> ats\<^sub>f\<^sub>f ts j js')" |
      "ats\<^sub>f\<^sub>f (t # ts) j =
         (case j of
            Zero \<Rightarrow> at\<^sub>f\<^sub>f t
          | Suc j' \<Rightarrow> ats\<^sub>f\<^sub>f ts j')"

text {*
\noindent
Appropriate induction principles are generated under the names
@{thm [source] "at\<^sub>f\<^sub>f.induct"},
@{thm [source] "ats\<^sub>f\<^sub>f.induct"}, and
@{thm [source] "at\<^sub>f\<^sub>f_ats\<^sub>f\<^sub>f.induct"}.

%%% TODO: Add recursors.

Here is a second example:
*}

    primrec_new
      sum_btree :: "('a\<Colon>{zero,plus}) btree \<Rightarrow> 'a" and
      sum_btree_option :: "'a btree option \<Rightarrow> 'a"
    where
      "sum_btree (BNode a lt rt) =
         a + sum_btree_option lt + sum_btree_option rt" |
      "sum_btree_option None = 0" |
      "sum_btree_option (Some t) = sum_btree t"

text {*
%  * can pretend a nested type is mutually recursive (if purely inductive)
%  * avoids the higher-order map
%  * e.g.

%  * this can always be avoided;
%     * e.g. in our previous example, we first mapped the recursive
%       calls, then we used a generic at function to retrieve the result
%
%  * there's no hard-and-fast rule of when to use one or the other,
%    just like there's no rule when to use fold and when to use
%    primrec_new
%
%  * higher-order approach, considering nesting as nesting, is more
%    compositional -- e.g. we saw how we could reuse an existing polymorphic
%    at or the_default, whereas @{const ats\<^sub>f\<^sub>f} is much more specific
%
%  * but:
%     * is perhaps less intuitive, because it requires higher-order thinking
%     * may seem inefficient, and indeed with the code generator the
%       mutually recursive version might be nicer
%     * is somewhat indirect -- must apply a map first, then compute a result
%       (cannot mix)
%     * the auxiliary functions like @{const ats\<^sub>f\<^sub>f} are sometimes useful in own right
%
%  * impact on automation unclear
%
*}
(*<*)
    end
(*>*)


subsection {* Command Syntax
  \label{ssec:primrec-command-syntax} *}


subsubsection {* \keyw{primrec\_new}
  \label{sssec:primrec-new} *}

text {*
\begin{matharray}{rcl}
  @{command_def "primrec_new"} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail "
  @@{command primrec_new} target? fixes \\ @'where' (@{syntax pr_equation} + '|')
  ;
  @{syntax_def pr_equation}: thmdecl? prop
"}
*}


(*
subsection {* Generated Theorems
  \label{ssec:primrec-generated-theorems} *}

text {*
%  * synthesized nonrecursive definition
%  * user specification is rederived from it, exactly as entered
%
%  * induct
%    * mutualized
%    * without some needless induction hypotheses if not used
%  * fold, rec
%    * mutualized
*}
*)


subsection {* Recursive Default Values for Selectors
  \label{ssec:primrec-recursive-default-values-for-selectors} *}

text {*
A datatype selector @{text un_D} can have a default value for each constructor
on which it is not otherwise specified. Occasionally, it is useful to have the
default value be defined recursively. This produces a chicken-and-egg situation
that may seem unsolvable, because the datatype is not introduced yet at the
moment when the selectors are introduced. Of course, we can always define the
selectors manually afterward, but we then have to state and prove all the
characteristic theorems ourselves instead of letting the package do it.

Fortunately, there is a fairly elegant workaround that relies on overloading and
that avoids the tedium of manual derivations:

\begin{enumerate}
\setlength{\itemsep}{0pt}

\item
Introduce a fully unspecified constant @{text "un_D\<^sub>0 \<Colon> 'a"} using
@{keyword consts}.

\item
Define the datatype, specifying @{text "un_D\<^sub>0"} as the selector's default
value.

\item
Define the behavior of @{text "un_D\<^sub>0"} on values of the newly introduced
datatype using the \keyw{overloading} command.

\item
Derive the desired equation on @{text un_D} from the characteristic equations
for @{text "un_D\<^sub>0"}.
\end{enumerate}

\noindent
The following example illustrates this procedure:
*}

    consts termi\<^sub>0 :: 'a

text {* \blankline *}

    datatype_new ('a, 'b) tlist =
      TNil (termi: 'b) (defaults ttl: TNil)
    | TCons (thd: 'a) (ttl : "('a, 'b) tlist") (defaults termi: "\<lambda>_ xs. termi\<^sub>0 xs")

text {* \blankline *}

    overloading
      termi\<^sub>0 \<equiv> "termi\<^sub>0 \<Colon> ('a, 'b) tlist \<Rightarrow> 'b"
    begin
    primrec_new termi\<^sub>0 :: "('a, 'b) tlist \<Rightarrow> 'b" where
      "termi\<^sub>0 (TNil y) = y" |
      "termi\<^sub>0 (TCons x xs) = termi\<^sub>0 xs"
    end

text {* \blankline *}

    lemma terminal_TCons[simp]: "termi (TCons x xs) = termi xs"
    by (cases xs) auto


(*
subsection {* Compatibility Issues
  \label{ssec:primrec-compatibility-issues} *}

text {*
%  * different induction in nested case
%    * solution: define nested-as-mutual functions with primrec,
%      and look at .induct
%
%  * different induction and recursor in nested case
%    * only matters to low-level users; they can define a dummy function to force
%      generation of mutualized recursor
*}
*)


section {* Defining Codatatypes
  \label{sec:defining-codatatypes} *}

text {*
Codatatypes can be specified using the @{command codatatype} command. The
command is first illustrated through concrete examples featuring different
flavors of corecursion. More examples can be found in the directory
\verb|~~/src/HOL/BNF/Examples|. The \emph{Archive of Formal Proofs} also
includes some useful codatatypes, notably for lazy lists \cite{lochbihler-2010}.
*}


subsection {* Introductory Examples
  \label{ssec:codatatype-introductory-examples} *}


subsubsection {* Simple Corecursion
  \label{sssec:codatatype-simple-corecursion} *}

text {*
Noncorecursive codatatypes coincide with the corresponding datatypes, so
they have no practical uses. \emph{Corecursive codatatypes} have the same syntax
as recursive datatypes, except for the command name. For example, here is the
definition of lazy lists:
*}

    codatatype (lset: 'a) llist (map: lmap rel: llist_all2) =
      lnull: LNil (defaults ltl: LNil)
    | LCons (lhd: 'a) (ltl: "'a llist")

text {*
\noindent
Lazy lists can be infinite, such as @{text "LCons 0 (LCons 0 (\<dots>))"} and
@{text "LCons 0 (LCons 1 (LCons 2 (\<dots>)))"}. Here is a related type, that of
infinite streams:
*}

    codatatype (sset: 'a) stream (map: smap rel: stream_all2) =
      SCons (shd: 'a) (stl: "'a stream")

text {*
\noindent
Another interesting type that can
be defined as a codatatype is that of the extended natural numbers:
*}

    codatatype enat = EZero | ESuc enat

text {*
\noindent
This type has exactly one infinite element, @{text "ESuc (ESuc (ESuc (\<dots>)))"},
that represents $\infty$. In addition, it has finite values of the form
@{text "ESuc (\<dots> (ESuc EZero)\<dots>)"}.

Here is an example with many constructors:
*}

    codatatype 'a process =
      Fail
    | Skip (cont: "'a process")
    | Action (prefix: 'a) (cont: "'a process")
    | Choice (left: "'a process") (right: "'a process")

text {*
\noindent
Notice that the @{const cont} selector is associated with both @{const Skip}
and @{const Choice}.
*}


subsubsection {* Mutual Corecursion
  \label{sssec:codatatype-mutual-corecursion} *}

text {*
\noindent
The example below introduces a pair of \emph{mutually corecursive} types:
*}

    codatatype even_enat = Even_EZero | Even_ESuc odd_enat
    and odd_enat = Odd_ESuc even_enat


subsubsection {* Nested Corecursion
  \label{sssec:codatatype-nested-corecursion} *}

text {*
\noindent
The next examples feature \emph{nested corecursion}:
*}

    codatatype 'a tree\<^sub>i\<^sub>i = Node\<^sub>i\<^sub>i (lbl\<^sub>i\<^sub>i: 'a) (sub\<^sub>i\<^sub>i: "'a tree\<^sub>i\<^sub>i llist")

text {* \blankline *}

    codatatype 'a tree\<^sub>i\<^sub>s = Node\<^sub>i\<^sub>s (lbl\<^sub>i\<^sub>s: 'a) (sub\<^sub>i\<^sub>s: "'a tree\<^sub>i\<^sub>s fset")

text {* \blankline *}

    codatatype 'a state_machine =
      State_Machine (accept: bool) (trans: "'a \<Rightarrow> 'a state_machine")


subsection {* Command Syntax
  \label{ssec:codatatype-command-syntax} *}


subsubsection {* \keyw{codatatype}
  \label{sssec:codatatype} *}

text {*
\begin{matharray}{rcl}
  @{command_def "codatatype"} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail "
  @@{command codatatype} target? \\
    (@{syntax dt_name} '=' (@{syntax ctor} + '|') + @'and')
"}

\noindent
Definitions of codatatypes have almost exactly the same syntax as for datatypes
(Section~\ref{ssec:datatype-command-syntax}). The @{text "no_discs_sels"} option
is not available, because destructors are a crucial notion for codatatypes.
*}


subsection {* Generated Constants
  \label{ssec:codatatype-generated-constants} *}

text {*
Given a codatatype @{text "('a\<^sub>1, \<dots>, 'a\<^sub>m) t"}
with $m > 0$ live type variables and $n$ constructors @{text "t.C\<^sub>1"},
\ldots, @{text "t.C\<^sub>n"}, the same auxiliary constants are generated as for
datatypes (Section~\ref{ssec:datatype-generated-constants}), except that the
iterator and the recursor are replaced by dual concepts:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item \relax{Coiterator}: @{text t_unfold}

\item \relax{Corecursor}: @{text t_corec}

\end{itemize}
*}


subsection {* Generated Theorems
  \label{ssec:codatatype-generated-theorems} *}

text {*
The characteristic theorems generated by @{command codatatype} are grouped in
three broad categories:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item The \emph{free constructor theorems} are properties about the constructors
and destructors that can be derived for any freely generated type.

\item The \emph{functorial theorems} are properties of datatypes related to
their BNF nature.

\item The \emph{coinductive theorems} are properties of datatypes related to
their coinductive nature.
\end{itemize}

\noindent
The first two categories are exactly as for datatypes and are described in
Sections
\ref{sssec:free-constructor-theorems}~and~\ref{sssec:functorial-theorems}.
*}


subsubsection {* Coinductive Theorems
  \label{sssec:coinductive-theorems} *}

text {*
The coinductive theorems are as follows:

\begin{indentblock}
\begin{description}

\item[\begin{tabular}{@ {}l@ {}}
  @{text "t."}\hthm{coinduct} @{text "[coinduct t, consumes m, case_names t\<^sub>1 \<dots> t\<^sub>m,"} \\
  \phantom{@{text "t."}\hthm{coinduct} @{text "["}}@{text "case_conclusion D\<^sub>1 \<dots> D\<^sub>n]"}\rm:
\end{tabular}] ~ \\
@{thm llist.coinduct[no_vars]}

\item[\begin{tabular}{@ {}l@ {}}
  @{text "t."}\hthm{strong\_coinduct} @{text "[consumes m, case_names t\<^sub>1 \<dots> t\<^sub>m,"} \\
  \phantom{@{text "t."}\hthm{strong\_coinduct} @{text "["}}@{text "case_conclusion D\<^sub>1 \<dots> D\<^sub>n]"}\rm:
\end{tabular}] ~ \\
@{thm llist.strong_coinduct[no_vars]}

\item[\begin{tabular}{@ {}l@ {}}
  @{text "t\<^sub>1_\<dots>_t\<^sub>m."}\hthm{coinduct} @{text "[case_names t\<^sub>1 \<dots> t\<^sub>m, case_conclusion D\<^sub>1 \<dots> D\<^sub>n]"} \\
  @{text "t\<^sub>1_\<dots>_t\<^sub>m."}\hthm{strong\_coinduct} @{text "[case_names t\<^sub>1 \<dots> t\<^sub>m,"} \\
  \phantom{@{text "t\<^sub>1_\<dots>_t\<^sub>m."}\hthm{strong\_coinduct} @{text "["}}@{text "case_conclusion D\<^sub>1 \<dots> D\<^sub>n]"}\rm:
\end{tabular}] ~ \\
Given $m > 1$ mutually corecursive codatatypes, these coinduction rules can be
used to prove $m$ properties simultaneously.

\item[@{text "t."}\hthm{unfold} \rm(@{text "[simp]"})\rm:] ~ \\
@{thm llist.unfold(1)[no_vars]} \\
@{thm llist.unfold(2)[no_vars]}

\item[@{text "t."}\hthm{corec} (@{text "[simp]"})\rm:] ~ \\
@{thm llist.corec(1)[no_vars]} \\
@{thm llist.corec(2)[no_vars]}

\item[@{text "t."}\hthm{disc\_unfold}\rm:] ~ \\
@{thm llist.disc_unfold(1)[no_vars]} \\
@{thm llist.disc_unfold(2)[no_vars]}

\item[@{text "t."}\hthm{disc\_corec}\rm:] ~ \\
@{thm llist.disc_corec(1)[no_vars]} \\
@{thm llist.disc_corec(2)[no_vars]}

\item[@{text "t."}\hthm{disc\_unfold\_iff} @{text "[simp]"}\rm:] ~ \\
@{thm llist.disc_unfold_iff(1)[no_vars]} \\
@{thm llist.disc_unfold_iff(2)[no_vars]}

\item[@{text "t."}\hthm{disc\_corec\_iff} @{text "[simp]"}\rm:] ~ \\
@{thm llist.disc_corec_iff(1)[no_vars]} \\
@{thm llist.disc_corec_iff(2)[no_vars]}

\item[@{text "t."}\hthm{sel\_unfold} @{text "[simp]"}\rm:] ~ \\
@{thm llist.sel_unfold(1)[no_vars]} \\
@{thm llist.sel_unfold(2)[no_vars]}

\item[@{text "t."}\hthm{sel\_corec} @{text "[simp]"}\rm:] ~ \\
@{thm llist.sel_corec(1)[no_vars]} \\
@{thm llist.sel_corec(2)[no_vars]}

\end{description}
\end{indentblock}

\noindent
For convenience, @{command codatatype} also provides the following collection:

\begin{indentblock}
\begin{description}

\item[@{text "t."}\hthm{simps} = @{text t.inject} @{text t.distinct} @{text t.case} @{text t.corec}$^*$ @{text t.disc_corec}] ~ \\
@{text t.disc_corec_iff} @{text t.sel_corec} @{text t.unfold}$^*$ @{text t.disc_unfold} @{text t.disc_unfold_iff} ~ \\
@{text t.sel_unfold} @{text t.map} @{text t.rel_inject} @{text t.rel_distinct} @{text t.set}

\end{description}
\end{indentblock}
*}


section {* Defining Corecursive Functions
  \label{sec:defining-corecursive-functions} *}

text {*
Corecursive functions can be specified using @{command primcorec} and
@{command primcorecursive}, which support primitive corecursion, or using the
more general \keyw{partial\_function} command. Here, the focus is on
the former two. More examples can be found in the directory
\verb|~~/src/HOL/BNF/Examples|.

Whereas recursive functions consume datatypes one constructor at a time,
corecursive functions construct codatatypes one constructor at a time.
Partly reflecting a lack of agreement among proponents of coalgebraic methods,
Isabelle supports three competing syntaxes for specifying a function $f$:

\begin{itemize}
\setlength{\itemsep}{0pt}

\abovedisplayskip=.5\abovedisplayskip
\belowdisplayskip=.5\belowdisplayskip

\item The \emph{destructor view} specifies $f$ by implications of the form
\[@{text "\<dots> \<Longrightarrow> is_C\<^sub>j (f x\<^sub>1 \<dots> x\<^sub>n)"}\] and
equations of the form
\[@{text "un_C\<^sub>ji (f x\<^sub>1 \<dots> x\<^sub>n) = \<dots>"}\]
This style is popular in the coalgebraic literature.

\item The \emph{constructor view} specifies $f$ by equations of the form
\[@{text "\<dots> \<Longrightarrow> f x\<^sub>1 \<dots> x\<^sub>n = C \<dots>"}\]
This style is often more concise than the previous one.

\item The \emph{code view} specifies $f$ by a single equation of the form
\[@{text "f x\<^sub>1 \<dots> x\<^sub>n = \<dots>"}\]
with restrictions on the format of the right-hand side. Lazy functional
programming languages such as Haskell support a generalized version of this
style.
\end{itemize}

All three styles are available as input syntax. Whichever syntax is chosen,
characteristic theorems for all three styles are generated.

\begin{framed}
\noindent
\textbf{Warning:}\enskip The @{command primcorec} and @{command primcorecursive}
commands are under development. Some of the functionality described here is
vaporware. An alternative is to define corecursive functions directly using the
generated @{text t_unfold} or @{text t_corec} combinators.
\end{framed}

%%% TODO: partial_function? E.g. for defining tail recursive function on lazy
%%% lists (cf. terminal0 in TLList.thy)
*}


subsection {* Introductory Examples
  \label{ssec:primcorec-introductory-examples} *}

text {*
Primitive corecursion is illustrated through concrete examples based on the
codatatypes defined in Section~\ref{ssec:codatatype-introductory-examples}. More
examples can be found in the directory \verb|~~/src/HOL/BNF/Examples|. The code
view is favored in the examples below. Sections
\ref{ssec:primrec-constructor-view} and \ref{ssec:primrec-destructor-view}
present the same examples expressed using the constructor and destructor views.
*}

(*<*)
    locale code_view
    begin
(*>*)

subsubsection {* Simple Corecursion
  \label{sssec:primcorec-simple-corecursion} *}

text {*
Following the code view, corecursive calls are allowed on the right-hand side as
long as they occur under a constructor, which itself appears either directly to
the right of the equal sign or in a conditional expression:
*}

    primcorec literate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a llist" where
      "literate f x = LCons x (literate f (f x))"

text {* \blankline *}

    primcorec siterate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a stream" where
      "siterate f x = SCons x (siterate f (f x))"

text {*
\noindent
The constructor ensures that progress is made---i.e., the function is
\emph{productive}. The above functions compute the infinite lazy list or stream
@{text "[x, f x, f (f x), \<dots>]"}. Productivity guarantees that prefixes
@{text "[x, f x, f (f x), \<dots>, (f ^^ k) x]"} of arbitrary finite length
@{text k} can be computed by unfolding the code equation a finite number of
times. The period (\keyw{.}) at the end of the commands discharge the zero proof
obligations.

Corecursive functions construct codatatype values, but nothing prevents them
from also consuming such values. The following function drops ever second
element in a stream:
*}

    primcorec every_snd :: "'a stream \<Rightarrow> 'a stream" where
      "every_snd s = SCons (shd s) (stl (stl s))"

text {*
\noindent
Constructs such as @{text "let"}---@{text "in"}, @{text
"if"}---@{text "then"}---@{text "else"}, and @{text "case"}---@{text "of"} may
appear around constructors that guard corecursive calls:
*}

    primcorec_notyet lappend :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
      "lappend xs ys =
         (case xs of
            LNil \<Rightarrow> ys
          | LCons x xs' \<Rightarrow> LCons x (lappend xs' ys))"

text {*
\noindent
Corecursion is useful to specify not only functions but also infinite objects:
*}

    primcorec infty :: enat where
      "infty = ESuc infty"

text {*
\noindent
The example below constructs a pseudorandom process value. It takes a stream of
actions (@{text s}), a pseudorandom function generator (@{text f}), and a
pseudorandom seed (@{text n}):
*}

    primcorec_notyet
      random_process :: "'a stream \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> 'a process"
    where
      "random_process s f n =
         (if n mod 4 = 0 then
            Fail
          else if n mod 4 = 1 then
            Skip (random_process s f (f n))
          else if n mod 4 = 2 then
            Action (shd s) (random_process (stl s) f (f n))
          else
            Choice (random_process (every_snd s) (f \<circ> f) (f n))
              (random_process (every_snd (stl s)) (f \<circ> f) (f (f n))))"

text {*
\noindent
The main disadvantage of the code view is that the conditions are tested
sequentially. This is visible in the generated theorems. The constructor and
destructor views offer nonsequential alternatives.
*}


subsubsection {* Mutual Corecursion
  \label{sssec:primcorec-mutual-corecursion} *}

text {*
The syntax for mutually corecursive functions over mutually corecursive
datatypes is unsurprising:
*}

    primcorec
      even_infty :: even_enat and
      odd_infty :: odd_enat
    where
      "even_infty = Even_ESuc odd_infty" |
      "odd_infty = Odd_ESuc even_infty"


subsubsection {* Nested Corecursion
  \label{sssec:primcorec-nested-corecursion} *}

text {*
The next pair of examples generalize the @{const literate} and @{const siterate}
functions (Section~\ref{sssec:primcorec-nested-corecursion}) to possibly
infinite trees in which subnodes are organized either as a lazy list (@{text
tree\<^sub>i\<^sub>i}) or as a finite set (@{text tree\<^sub>i\<^sub>s}):
*}

    primcorec iterate\<^sub>i\<^sub>i :: "('a \<Rightarrow> 'a llist) \<Rightarrow> 'a \<Rightarrow> 'a tree\<^sub>i\<^sub>i" where
      "iterate\<^sub>i\<^sub>i f x = Node\<^sub>i\<^sub>i x (lmap (iterate\<^sub>i\<^sub>i f) (f x))"

text {* \blankline *}

    primcorec iterate\<^sub>i\<^sub>s :: "('a \<Rightarrow> 'a fset) \<Rightarrow> 'a \<Rightarrow> 'a tree\<^sub>i\<^sub>s" where
      "iterate\<^sub>i\<^sub>s f x = Node\<^sub>i\<^sub>s x (fmap (iterate\<^sub>i\<^sub>s f) (f x))"

text {*
\noindent
Deterministic finite automata (DFAs) are usually defined as 5-tuples
@{text "(Q, \<Sigma>, \<delta>, q\<^sub>0, F)"}, where @{text Q} is a finite set of states,
@{text \<Sigma>} is a finite alphabet, @{text \<delta>} is a transition function, @{text q\<^sub>0}
is an initial state, and @{text F} is a set of final states. The following
function translates a DFA into a @{type state_machine}:
*}

    primcorec (*<*)(in early) (*>*)
      sm_of_dfa :: "('q \<Rightarrow> 'a \<Rightarrow> 'q) \<Rightarrow> 'q set \<Rightarrow> 'q \<Rightarrow> 'a state_machine"
    where
      "sm_of_dfa \<delta> F q = State_Machine (q \<in> F) (sm_of_dfa \<delta> F o \<delta> q)"

text {*
\noindent
The map function for the function type (@{text \<Rightarrow>}) is composition
(@{text "op \<circ>"}). For convenience, corecursion through functions can be
expressed using @{text \<lambda>}-expressions and function application rather
than composition. For example:
*}

    primcorec
      sm_of_dfa :: "('q \<Rightarrow> 'a \<Rightarrow> 'q) \<Rightarrow> 'q set \<Rightarrow> 'q \<Rightarrow> 'a state_machine"
    where
      "sm_of_dfa \<delta> F q = State_Machine (q \<in> F) (sm_of_dfa \<delta> F o \<delta> q)"

text {* \blankline *}

    primcorec empty_sm :: "'a state_machine" where
      "empty_sm = State_Machine False (\<lambda>_. empty_sm)"

text {* \blankline *}

    primcorec not_sm :: "'a state_machine \<Rightarrow> 'a state_machine" where
      "not_sm M = State_Machine (\<not> accept M) (\<lambda>a. not_sm (trans M a))"

text {* \blankline *}

    primcorec
      or_sm :: "'a state_machine \<Rightarrow> 'a state_machine \<Rightarrow> 'a state_machine"
    where
      "or_sm M N =
         State_Machine (accept M \<or> accept N)
           (\<lambda>a. or_sm (trans M a) (trans N a))"


subsubsection {* Nested-as-Mutual Corecursion
  \label{sssec:primcorec-nested-as-mutual-corecursion} *}

text {*
Just as it is possible to recurse over nested recursive datatypes as if they
were mutually recursive
(Section~\ref{sssec:primrec-nested-as-mutual-recursion}), it is possible to
pretend that nested codatatypes are mutually corecursive. For example:
*}

    primcorec_notyet
      iterate\<^sub>i\<^sub>i :: "('a \<Rightarrow> 'a llist) \<Rightarrow> 'a \<Rightarrow> 'a tree\<^sub>i\<^sub>i" and
      iterates\<^sub>i\<^sub>i :: "('a \<Rightarrow> 'a llist) \<Rightarrow> 'a llist \<Rightarrow> 'a tree\<^sub>i\<^sub>i llist"
    where
      "iterate\<^sub>i\<^sub>i f x = Node\<^sub>i\<^sub>i x (iterates\<^sub>i\<^sub>i f (f x))" |
      "iterates\<^sub>i\<^sub>i f xs =
         (case xs of
            LNil \<Rightarrow> LNil
          | LCons x xs' \<Rightarrow> LCons (iterate\<^sub>i\<^sub>i f x) (iterates\<^sub>i\<^sub>i f xs'))"
(*<*)
    end
(*>*)


subsubsection {* Constructor View
  \label{ssec:primrec-constructor-view} *}

(*<*)
    locale ctr_view = code_view
    begin
(*>*)

text {*
The constructor view is similar to the code view, but there is one separate
conditional equation per constructor rather than a single unconditional
equation. Examples that rely on a single constructor, such as @{const literate}
and @{const siterate}, are identical in both styles.

Here is an example where there is a difference:
*}

    primcorec lappend :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
      "lnull xs \<Longrightarrow> lnull ys \<Longrightarrow> lappend xs ys = LNil" |
      "_ \<Longrightarrow> lappend xs ys = LCons (lhd (if lnull xs then ys else xs))
         (if xs = LNil then ltl ys else lappend (ltl xs) ys)"

text {*
\noindent
With the constructor view, we must distinguish between the @{const LNil} and
the @{const LCons} case. The condition for @{const LCons} is
left implicit, as the negation of that for @{const LNil}.

For this example, the constructor view is slighlty more involved than the
code equation. Recall the code view version presented in
Section~\ref{sssec:primcorec-simple-corecursion}.
% TODO: \[{thm code_view.lappend.code}\]
The constructor view requires us to analyze the second argument (@{term ys}).
The code equation generated from the constructor view also suffers from this.
% TODO: \[{thm lappend.code}\]

In contrast, the next example is arguably more naturally expressed in the
constructor view:
*}

    primcorec_notyet
      random_process :: "'a stream \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> 'a process"
    where
      "n mod 4 = 0 \<Longrightarrow> random_process s f n = Fail" |
      "n mod 4 = 1 \<Longrightarrow>
         random_process s f n = Skip (random_process s f (f n))" |
      "n mod 4 = 2 \<Longrightarrow>
         random_process s f n = Action (shd s) (random_process (stl s) f (f n))" |
      "n mod 4 = 3 \<Longrightarrow>
         random_process s f n = Choice (random_process (every_snd s) f (f n))
           (random_process (every_snd (stl s)) f (f n))"
(*<*)
    end
(*>*)

text {*
\noindent
Since there is no sequentiality, we can apply the equation for @{const Choice}
without having first to discharge @{term "n mod (4\<Colon>int) \<noteq> 0"},
@{term "n mod (4\<Colon>int) \<noteq> 1"}, and
@{term "n mod (4\<Colon>int) \<noteq> 2"}.
The price to pay for this elegance is that we must discharge exclusivity proof
obligations, one for each pair of conditions
@{term "(n mod (4\<Colon>int) = i, n mod (4\<Colon>int) = j)"}
with @{term "i < j"}. If we prefer not to discharge any obligations, we can
enable the @{text "sequential"} option. This pushes the problem to the users of
the generated properties.
%Here are more examples to conclude:
*}


subsubsection {* Destructor View
  \label{ssec:primrec-destructor-view} *}

(*<*)
    locale dest_view
    begin
(*>*)

text {*
The destructor view is in many respects dual to the constructor view. Conditions
determine which constructor to choose, and these conditions are interpreted
sequentially or not depending on the @{text "sequential"} option.
Consider the following examples:
*}

    primcorec literate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a llist" where
      "\<not> lnull (literate _ x)" |
      "lhd (literate _ x) = x" |
      "ltl (literate f x) = literate f (f x)"

text {* \blankline *}

    primcorec siterate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a stream" where
      "shd (siterate _ x) = x" |
      "stl (siterate f x) = siterate f (f x)"

text {* \blankline *}

    primcorec every_snd :: "'a stream \<Rightarrow> 'a stream" where
      "shd (every_snd s) = shd s" |
      "stl (every_snd s) = stl (stl s)"

text {*
\noindent
The first formula in the @{const literate} specification indicates which
constructor to choose. For @{const siterate} and @{const every_snd}, no such
formula is necessary, since the type has only one constructor. The last two
formulas are equations specifying the value of the result for the relevant
selectors. Corecursive calls appear directly to the right of the equal sign.
Their arguments are unrestricted.

The next example shows how to specify functions that rely on more than one
constructor:
*}

    primcorec lappend :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
      "lnull xs \<Longrightarrow> lnull ys \<Longrightarrow> lnull (lappend xs ys)" |
      "lhd (lappend xs ys) = lhd (if lnull xs then ys else xs)" |
      "ltl (lappend xs ys) = (if xs = LNil then ltl ys else lappend (ltl xs) ys)"

text {*
\noindent
For a codatatype with $n$ constructors, it is sufficient to specify $n - 1$
discriminator formulas. The command will then assume that the remaining
constructor should be taken otherwise. This can be made explicit by adding
*}

(*<*)
    end

    primcorec lappend :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
      "lnull xs \<Longrightarrow> lnull ys \<Longrightarrow> lnull (lappend xs ys)" |
(*>*)
      "_ \<Longrightarrow> \<not> lnull (lappend xs ys)"
(*<*) |
      "lhd (lappend xs ys) = lhd (if lnull xs then ys else xs)" |
      "ltl (lappend xs ys) = (if xs = LNil then ltl ys else lappend (ltl xs) ys)"

    context dest_view begin
(*>*)

text {*
\noindent
to the specification. The generated selector theorems are conditional.

The next example illustrates how to cope with selectors defined for several
constructors:
*}

    primcorec_notyet
      random_process :: "'a stream \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> 'a process"
    where
      "n mod 4 = 0 \<Longrightarrow> is_Fail (random_process s f n)" |
      "n mod 4 = 1 \<Longrightarrow> is_Skip (random_process s f n)" |
      "n mod 4 = 2 \<Longrightarrow> is_Action (random_process s f n)" |
      "n mod 4 = 3 \<Longrightarrow> is_Choice (random_process s f n)" |
      "cont (random_process s f n) = random_process s f (f n)" (* of Skip FIXME *) |
      "prefix (random_process s f n) = shd s" |
      "cont (random_process s f n) = random_process (stl s) f (f n)" (* of Action FIXME *) |
      "left (random_process s f n) = random_process (every_snd s) f (f n)" |
      "right (random_process s f n) = random_process (every_snd (stl s)) f (f n)" (*<*)
(*>*)

text {*
\noindent
Using the @{text "of"} keyword, different equations are specified for @{const
cont} depending on which constructor is selected.

Here are more examples to conclude:
*}

    primcorec
      even_infty :: even_enat and
      odd_infty :: odd_enat
    where
      "\<not> is_Even_EZero even_infty" |
      "un_Even_ESuc even_infty = odd_infty" |
      "un_Odd_ESuc odd_infty = even_infty"

text {* \blankline *}

    primcorec iterate\<^sub>i\<^sub>i :: "('a \<Rightarrow> 'a llist) \<Rightarrow> 'a \<Rightarrow> 'a tree\<^sub>i\<^sub>i" where
      "lbl\<^sub>i\<^sub>i (iterate\<^sub>i\<^sub>i f x) = x" |
      "sub\<^sub>i\<^sub>i (iterate\<^sub>i\<^sub>i f x) = lmap (iterate\<^sub>i\<^sub>i f) (f x)"
(*<*)
    end
(*>*)


subsection {* Command Syntax
  \label{ssec:primcorec-command-syntax} *}


subsubsection {* \keyw{primcorec} and \keyw{primcorecursive}
  \label{sssec:primcorecursive-and-primcorec} *}

text {*
\begin{matharray}{rcl}
  @{command_def "primcorec"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  @{command_def "primcorecursive"} & : & @{text "local_theory \<rightarrow> proof(prove)"}
\end{matharray}

@{rail "
  (@@{command primcorec} | @@{command primcorecursive}) target? \\ @{syntax pcr_option}? fixes @'where'
    (@{syntax pcr_formula} + '|')
  ;
  @{syntax_def pcr_option}: '(' ('sequential' | 'exhaustive') ')'
  ;
  @{syntax_def pcr_formula}: thmdecl? prop (@'of' (term * ))?
"}

The optional target is optionally followed by a corecursion-specific option:

\begin{itemize}
\setlength{\itemsep}{0pt}

\item
The @{text "sequential"} option indicates that the conditions in specifications
expressed using the constructor or destructor view are to be interpreted
sequentially.

\item
The @{text "exhaustive"} option indicates that the conditions in specifications
expressed using the constructor or destructor view cover all possible cases.
\end{itemize}

\noindent
The @{command primcorec} command is an abbreviation for @{command primcorecursive} with
@{text "by auto?"} to discharge any emerging proof obligations.
*}


(*
subsection {* Generated Theorems
  \label{ssec:primcorec-generated-theorems} *}
*)


(*
subsection {* Recursive Default Values for Selectors
  \label{ssec:primcorec-recursive-default-values-for-selectors} *}

text {*
partial_function to the rescue
*}
*)


section {* Registering Bounded Natural Functors
  \label{sec:registering-bounded-natural-functors} *}

text {*
The (co)datatype package can be set up to allow nested recursion through
arbitrary type constructors, as long as they adhere to the BNF requirements and
are registered as BNFs.
*}


(*
subsection {* Introductory Example
  \label{ssec:bnf-introductory-example} *}

text {*
More examples in \verb|~~/src/HOL/BNF/Basic_BNFs.thy| and
\verb|~~/src/HOL/BNF/More_BNFs.thy|.

%Mention distinction between live and dead type arguments;
%  * and existence of map, set for those
%mention =>.
*}
*)


subsection {* Command Syntax
  \label{ssec:bnf-command-syntax} *}


subsubsection {* \keyw{bnf}
  \label{sssec:bnf} *}

text {*
\begin{matharray}{rcl}
  @{command_def "bnf"} & : & @{text "local_theory \<rightarrow> proof(prove)"}
\end{matharray}

@{rail "
  @@{command bnf} target? (name ':')? term \\
    term_list term term_list term?
  ;
  X_list: '[' (X + ',') ']'
"}
*}


subsubsection {* \keyw{print\_bnfs}
  \label{sssec:print-bnfs} *}

text {*
\begin{matharray}{rcl}
  @{command_def "print_bnfs"} & : & @{text "local_theory \<rightarrow>"}
\end{matharray}

@{rail "
  @@{command print_bnfs}
"}
*}


section {* Deriving Destructors and Theorems for Free Constructors
  \label{sec:deriving-destructors-and-theorems-for-free-constructors} *}

text {*
The derivation of convenience theorems for types equipped with free constructors,
as performed internally by @{command datatype_new} and @{command codatatype},
is available as a stand-alone command called @{command wrap_free_constructors}.

%  * need for this is rare but may arise if you want e.g. to add destructors to
%    a type not introduced by ...
%
%  * also useful for compatibility with old package, e.g. add destructors to
%    old \keyw{datatype}
%
%  * @{command wrap_free_constructors}
%    * @{text "no_discs_sels"}, @{text "rep_compat"}
%    * hack to have both co and nonco view via locale (cf. ext nats)
*}


(*
subsection {* Introductory Example
  \label{ssec:ctors-introductory-example} *}
*)


subsection {* Command Syntax
  \label{ssec:ctors-command-syntax} *}


subsubsection {* \keyw{wrap\_free\_constructors}
  \label{sssec:wrap-free-constructors} *}

text {*
\begin{matharray}{rcl}
  @{command_def "wrap_free_constructors"} & : & @{text "local_theory \<rightarrow> proof(prove)"}
\end{matharray}

@{rail "
  @@{command wrap_free_constructors} target? @{syntax dt_options} \\
    term_list name @{syntax fc_discs_sels}?
  ;
  @{syntax_def fc_discs_sels}: name_list (name_list_list name_term_list_list? )?
  ;
  @{syntax_def name_term}: (name ':' term)
"}

% options: no_discs_sels rep_compat

% X_list is as for BNF

\noindent
Section~\ref{ssec:datatype-generated-theorems} lists the generated theorems.
*}


(*
section {* Standard ML Interface
  \label{sec:standard-ml-interface} *}

text {*
The package's programmatic interface.
*}
*)


(*
section {* Interoperability
  \label{sec:interoperability} *}

text {*
The package's interaction with other Isabelle packages and tools, such as the
code generator and the counterexample generators.
*}


subsection {* Transfer and Lifting
  \label{ssec:transfer-and-lifting} *}


subsection {* Code Generator
  \label{ssec:code-generator} *}


subsection {* Quickcheck
  \label{ssec:quickcheck} *}


subsection {* Nitpick
  \label{ssec:nitpick} *}


subsection {* Nominal Isabelle
  \label{ssec:nominal-isabelle} *}
*)


(*
section {* Known Bugs and Limitations
  \label{sec:known-bugs-and-limitations} *}

text {*
Known open issues of the package.
*}

text {*
%* primcorecursive and primcorec is unfinished
%
%* slow n-ary mutual (co)datatype, avoid as much as possible (e.g. using nesting)
%
%* issues with HOL-Proofs?
%
%* partial documentation
%
%* no way to register "sum" and "prod" as (co)datatypes to enable N2M reduction for them
%  (for @{command datatype_new_compat} and prim(co)rec)
%
%    * a fortiori, no way to register same type as both data- and codatatype
%
%* no recursion through unused arguments (unlike with the old package)
%
%* in a locale, cannot use locally fixed types (because of limitation in typedef)?
%
% *names of variables suboptimal
*}
*)


section {* Acknowledgments
  \label{sec:acknowledgments} *}

text {*
Tobias Nipkow and Makarius Wenzel encouraged us to implement the new
(co)datatype package. Andreas Lochbihler provided lots of comments on earlier
versions of the package, especially for the coinductive part. Brian Huffman
suggested major simplifications to the internal constructions, much of which has
yet to be implemented. Florian Haftmann and Christian Urban provided general
advice on Isabelle and package writing. Stefan Milius and Lutz Schr\"oder
suggested an elegant proof to eliminate one of the BNF assumptions.
*}

end
