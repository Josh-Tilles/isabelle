
(* $Id$ *)

theory prelim imports base begin

chapter {* Preliminaries *}

section {* Named entities *}

text {* Named entities of different kinds (logical constant, type,
type class, theorem, method etc.) live in separate name spaces.  It is
usually clear from the occurrence of a name which kind of entity it
refers to.  For example, proof method @{text "foo"} vs.\ theorem
@{text "foo"} vs.\ logical constant @{text "foo"} are easily
distinguished by means of the syntactic context.  A notable exception
are logical identifiers within a term (\secref{sec:terms}): constants,
fixed variables, and bound variables all share the same identifier
syntax, but are distinguished by their scope.

Each name space is organized as a collection of \emph{qualified
names}, which consist of a sequence of basic name components separated
by dots: @{text "Bar.bar.foo"}, @{text "Bar.foo"}, and @{text "foo"}
are examples for valid qualified names.  Name components are
subdivided into \emph{symbols}, which constitute the smallest textual
unit in Isabelle --- raw characters are normally not encountered
directly. *}


subsection {* Strings of symbols *}

text {* Isabelle strings consist of a sequence of
symbols\glossary{Symbol}{The smalles unit of text in Isabelle,
subsumes plain ASCII characters as well as an infinite collection of
named symbols (for greek, math etc.).}, which are either packed as an
actual @{text "string"}, or represented as a list.  Each symbol is in
itself a small string of the following form:

\begin{enumerate}

\item either a singleton ASCII character ``@{text "c"}'' (with
character code 0--127), for example ``\verb,a,'',

\item or a regular symbol ``\verb,\,\verb,<,@{text "ident"}\verb,>,'',
for example ``\verb,\,\verb,<alpha>,'',

\item or a control symbol ``\verb,\,\verb,<^,@{text
"ident"}\verb,>,'', for example ``\verb,\,\verb,<^bold>,'',

\item or a raw control symbol ``\verb,\,\verb,<^raw:,@{text
"\<dots>"}\verb,>,'' where ``@{text "\<dots>"}'' refers to any
printable ASCII character (excluding ``\verb,.,'' and ``\verb,>,'') or
non-ASCII character, for example ``\verb,\,\verb,<^raw:$\sum_{i =
1}^n$>,'',

\item or a numbered raw control symbol ``\verb,\,\verb,<^raw,@{text
"nnn"}\verb,>, where @{text "nnn"} are digits, for example
``\verb,\,\verb,<^raw42>,''.

\end{enumerate}

The @{text "ident"} syntax for symbol names is @{text "letter (letter
| digit)\<^sup>*"}, where @{text "letter = A..Za..Z"} and @{text
"digit = 0..9"}.  There are infinitely many regular symbols and
control symbols available, but a certain collection of standard
symbols is treated specifically.  For example,
``\verb,\,\verb,<alpha>,'' is classified as a (non-ASCII) letter,
which means it may occur within regular Isabelle identifier syntax.

Output of symbols depends on the print mode (\secref{sec:print-mode}).
For example, the standard {\LaTeX} setup of the Isabelle document
preparation system would present ``\verb,\,\verb,<alpha>,'' as @{text
"\<alpha>"}, and ``\verb,\,\verb,<^bold>,\verb,\,\verb,<alpha>,'' as @{text
"\<^bold>\<alpha>"}.

\medskip It is important to note that the character set underlying
Isabelle symbols is plain 7-bit ASCII.  Since 8-bit characters are
passed through transparently, Isabelle may easily process actual
Unicode/UCS data (using the well-known UTF-8 encoding, for example).
Unicode provides its own collection of mathematical symbols, but there
is presently no link to Isabelle's named ones; both kinds of symbols
coexist independently. *}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type "Symbol.symbol"} \\
  @{index_ML Symbol.explode: "string -> Symbol.symbol list"} \\
  @{index_ML Symbol.is_letter: "Symbol.symbol -> bool"} \\
  @{index_ML Symbol.is_digit: "Symbol.symbol -> bool"} \\
  @{index_ML Symbol.is_quasi: "Symbol.symbol -> bool"} \\
  @{index_ML Symbol.is_blank: "Symbol.symbol -> bool"} \\
  @{index_ML_type "Symbol.sym"} \\
  @{index_ML Symbol.decode: "Symbol.symbol -> Symbol.sym"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_type "Symbol.symbol"} represents Isabelle symbols; this type
  is merely an alias for @{ML_type "string"}, but emphasizes the
  specific format encountered here.

  \item @{ML "Symbol.explode"}~@{text "s"} produces an actual symbol
  list from the packed form usually encountered as user input.  This
  function replaces @{ML "String.explode"} for virtually all purposes
  of manipulating text in Isabelle!  Plain @{text "implode"} may be
  used for the reverse operation.

  \item @{ML "Symbol.is_letter"}, @{ML "Symbol.is_digit"}, @{ML
  "Symbol.is_quasi"}, @{ML "Symbol.is_blank"} classify certain symbols
  (both ASCII and several named ones) according to fixed syntactic
  convections of Isabelle, e.g.\ see \cite{isabelle-isar-ref}.

  \item @{ML_type "Symbol.sym"} is a concrete datatype that represents
  the different kinds of symbols explicitly as @{ML "Symbol.Char"},
  @{ML "Symbol.Sym"}, @{ML "Symbol.Ctrl"}, or @{ML "Symbol.Raw"}.

  \item @{ML "Symbol.decode"} converts the string representation of a
  symbol into the explicit datatype version.

  \end{description}
*}


subsection {* Qualified names and name spaces *}

text %FIXME {* Qualified names are constructed according to implicit naming
principles of the present context.


The last component is called \emph{base name}; the remaining prefix of
qualification may be empty.

Some practical conventions help to organize named entities more
systematically:

\begin{itemize}

\item Names are qualified first by the theory name, second by an
optional ``structure''.  For example, a constant @{text "c"} declared
as part of a certain structure @{text "b"} (say a type definition) in
theory @{text "A"} will be named @{text "A.b.c"} internally.

\item

\item

\item

\item

\end{itemize}

Names of different kinds of entities are basically independent, but
some practical naming conventions relate them to each other.  For
example, a constant @{text "foo"} may be accompanied with theorems
@{text "foo.intro"}, @{text "foo.elim"}, @{text "foo.simps"} etc.  The
same may happen for a type @{text "foo"}, which is then apt to cause
clashes in the theorem name space!  To avoid this, we occasionally
follow an additional convention of suffixes that determine the
original kind of entity that a name has been derived.  For example,
constant @{text "foo"} is associated with theorem @{text "foo.intro"},
type @{text "foo"} with theorem @{text "foo_type.intro"}, and type
class @{text "foo"} with @{text "foo_class.intro"}.

*}


section {* Structured output *}

subsection {* Pretty printing *}

text FIXME

subsection {* Output channels *}

text FIXME

subsection {* Print modes *}

text FIXME


section {* Context \label{sec:context} *}

text %FIXME {* What is a context anyway?  A highly advanced
technological and cultural achievement, which took humanity several
thousands of years to be develop, is writing with pen-and-paper.  Here
the paper is the context, or medium.  It accommodates a certain range
of different kinds of pens, but also has some inherent limitations.
For example, carved inscriptions are better done on solid material
like wood or stone.

Isabelle/Isar distinguishes two key notions of context: \emph{theory
context} and \emph{proof context}.  To motivate this fundamental
division consider the very idea of logical reasoning which is about
judgments $\Gamma \Drv{\Theta} \phi$, where $\Theta$ is the background
theory with declarations of operators and axioms stating their
properties, and $\Gamma$ a collection of hypotheses emerging
temporarily during proof.  For example, the rule of
implication-introduction \[ \infer{\Gamma \Drv{\Theta} A \Imp
B}{\Gamma, A \Drv{\Theta} B} \] can be read as ``to show $A \Imp B$ we
may assume $A$ as hypothesis and need to show $B$''.  It is
characteristic that $\Theta$ is unchanged and $\Gamma$ is only
modified according to some general patterns of ``assuming'' and
``discharging'' hypotheses.  This admits the following abbreviated
notation, where the fixed $\Theta$ and locally changed $\Gamma$ are
left implicit: \[ \infer{A \Imp B}{\infer*{B}{[A]}} \]

In some logical traditions (e.g.\ Type Theory) there is a tendency to
unify all kinds of declarations within a single notion of context.
This is theoretically very nice, but also more demanding, because
everything is internalized into the logical calculus itself.
Isabelle/Pure is a very simple logic, but achieves many practically
useful concepts by differentiating various basic elements.

Take polymorphism, for example.  Instead of embarking on the
adventurous enterprise of full higher-order logic with full
type-quantification and polymorphic entities, Isabelle/Pure merely
takes a stripped-down version of Church's Simple Type Theory
\cite{church40}.  Then after the tradition of Gordon's HOL
\cite{mgordon-hol} it is fairly easy to introduce syntactic notions of
type variables and type-constructors, and require every theory
$\Theta$ being closed by type instantiation.  Whenever we wish to
reason with a polymorphic constant or axiom scheme at a particular
type, we may assume that it has been referenced initially at that very
instance (due to the Deduction Theorem).  Thus we achieve the
following \emph{admissible
  rule}\glossary{Admissible rule}{FIXME} of schematic type-instantiation:

\[
\infer{\phi(\tau)}{\infer*{\phi(\alpha)}{[\alpha]}}
\]

Using this approach, the structured Isar proof language offers
schematic polymorphism within nested sub-proofs -- similar to that of
polymorphic let-bindings according to Hindley-Milner.\
\cite{milner78}.  All of this is achieved without disintegrating the
rather simplistic logical core.  On the other hand, the succinct rule
presented above already involves rather delicate interaction of the
theory and proof context (with side-conditions not mentioned here),
and unwinding an admissible rule involves induction over derivations.
All of this diversity needs to be accomodated by the system
architecture and actual implementation.

\medskip Despite these important observations, Isabelle/Isar is not just a
logical calculus, there are further extra-logical aspects to be considered.
Practical experience over the years suggests two context data structures which
are used in rather dissimilar manners, even though there is a considerable
overlap of underlying ideas.

From the system's perspective the mode of use of theory vs.\ proof context is
the key distinction.  The actual content is merely a generic slot for
\emph{theory data} and \emph{proof data}, respectively.  There are generic
interfaces to declare data entries at any time.  Even the core logic of
Isabelle/Pure registers its very own notion of theory context data (types,
constants, axioms etc.) like any other Isabelle tool out there.  Likewise, the
essentials of Isar proof contexts are one proof data slot among many others,
notably those of derived Isar concepts (e.g.\ calculational reasoning rules).

In that respect, a theory is more like a stone tablet to carve long-lasting
inscriptions -- but take care not to break it!  While a proof context is like
a block of paper to scribble and dispose quickly.  More recently Isabelle has
started to cultivate the paper-based craftsmanship a bit further, by
maintaining small collections of paper booklets, better known as locales.

Thus we achive ``thick'' augmented versions of {\boldmath$\Theta$} and
{\boldmath$\Gamma$} to support realistic structured reasoning within a
practically usable system.
*}


subsection {* Theory context \label{sec:context-theory} *}

text %FIXME {* A theory context consists of management information plus the
actual data, which may be declared by other software modules later on.
The management part is surprisingly complex, we illustrate it by the
following typical situation of incremental theory development.

\begin{tabular}{rcccl}
        &            & $Pure$ \\
        &            & $\downarrow$ \\
        &            & $FOL$ \\
        & $\swarrow$ &              & $\searrow$ & \\
  $Nat$ &            &              &            & $List$ \\
        & $\searrow$ &              & $\swarrow$ \\
        &            & $Length$ \\
        &            & \multicolumn{3}{l}{~~$\isarkeyword{imports}$} \\
        &            & \multicolumn{3}{l}{~~$\isarkeyword{begin}$} \\
        &            & $\vdots$~~ \\
        &            & $\bullet$~~ \\
        &            & $\vdots$~~ \\
        &            & $\bullet$~~ \\
        &            & $\vdots$~~ \\
        &            & \multicolumn{3}{l}{~~$\isarkeyword{end}$} \\
\end{tabular}

\begin{itemize}
\item \emph{name}, \emph{parents} and \emph{ancestors}
\item \emph{identity}
\item \emph{intermediate versions}
\end{itemize}

\begin{description}
\item [draft]
\item [intermediate]
\item [finished]
\end{description}

\emph{theory reference}
*}


subsection {* Proof context \label{sec:context-proof} *}

text {*
  FIXME

\glossary{Proof context}{The static context of a structured proof,
acts like a local ``theory'' of the current portion of Isar proof
text, generalizes the idea of local hypotheses @{text "\<Gamma>"} in
judgments @{text "\<Gamma> \<turnstile> \<phi>"} of natural deduction calculi.  There is a
generic notion of introducing and discharging hypotheses.  Arbritrary
auxiliary context data may be adjoined.}

*}

end
