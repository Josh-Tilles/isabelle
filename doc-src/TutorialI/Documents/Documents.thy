(*<*)
theory Documents = Main:
(*>*)

(* FIXME exercises? *)

section {* Concrete Syntax \label{sec:concrete-syntax} *}

text {*
  Concerning Isabelle's ``inner'' language of simply-typed @{text
  \<lambda>}-calculus, the core concept of Isabelle's elaborate
  infrastructure for concrete syntax is that of general
  \bfindex{mixfix annotations}.  Associated with any kind of constant
  declaration, mixfixes affect both the grammar productions for the
  parser and output templates for the pretty printer.

  In full generality, the whole affair of parser and pretty printer
  configuration is rather subtle, see \cite{isabelle-ref} for further
  details.  Any syntax specifications given by end-users need to
  interact properly with the existing setup of Isabelle/Pure and
  Isabelle/HOL.  It is particularly important to get the precedence of
  new syntactic constructs right, avoiding ambiguities with existing
  elements.

  \medskip Subsequently we introduce a few simple declaration forms
  that already cover the most common situations fairly well.
*}


subsection {* Infix Annotations *}

text {*
  Syntax annotations may be included wherever constants are declared
  directly or indirectly, including \isacommand{consts},
  \isacommand{constdefs}, or \isacommand{datatype} (for the
  constructor operations).  Type-constructors may be annotated as
  well, although this is less frequently encountered in practice
  (@{text "*"} and @{text "+"} types may come to mind).

  Infix declarations\index{infix annotations} provide a useful special
  case of mixfixes, where users need not care about the full details
  of priorities, nesting, spacing, etc.  The subsequent example of the
  exclusive-or operation on boolean values illustrates typical infix
  declarations arising in practice.
*}

constdefs
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"    (infixl "[+]" 60)
  "A [+] B \<equiv> (A \<and> \<not> B) \<or> (\<not> A \<and> B)"

text {*
  \noindent Now @{text "xor A B"} and @{text "A [+] B"} refer to the
  same expression internally.  Any curried function with at least two
  arguments may be associated with infix syntax.  For partial
  applications with less than two operands there is a special notation
  with \isa{op} prefix: @{text xor} without arguments is represented
  as @{text "op [+]"}; together with plain prefix application this
  turns @{text "xor A"} into @{text "op [+] A"}.

  \medskip The string @{text [source] "[+]"} in the above annotation
  refers to the bit of concrete syntax to represent the operator,
  while the number @{text 60} determines the precedence of the
  construct (i.e.\ the syntactic priorities of the arguments and
  result).

  As it happens, Isabelle/HOL already spends many popular combinations
  of ASCII symbols for its own use, including both @{text "+"} and
  @{text "++"}.  Slightly more awkward combinations like the present
  @{text "[+]"} tend to be available for user extensions.  The current
  arrangement of inner syntax may be inspected via
  \commdx{print\protect\_syntax}, albeit its output is enormous.

  Operator precedence also needs some special considerations.  The
  admissible range is 0--1000.  Very low or high priorities are
  basically reserved for the meta-logic.  Syntax of Isabelle/HOL
  mainly uses the range of 10--100: the equality infix @{text "="} is
  centered at 50, logical connectives (like @{text "\<or>"} and @{text
  "\<and>"}) are below 50, and algebraic ones (like @{text "+"} and @{text
  "*"}) above 50.  User syntax should strive to coexist with common
  HOL forms, or use the mostly unused range 100--900.

  \medskip The keyword \isakeyword{infixl} specifies an operator that
  is nested to the \emph{left}: in iterated applications the more
  complex expression appears on the left-hand side: @{term "A [+] B
  [+] C"} stands for @{text "(A [+] B) [+] C"}.  Similarly,
  \isakeyword{infixr} specifies to nesting to the \emph{right},
  reading @{term "A [+] B [+] C"} as @{text "A [+] (B [+] C)"}.  In
  contrast, a \emph{non-oriented} declaration via \isakeyword{infix}
  would have rendered @{term "A [+] B [+] C"} illegal, but demand
  explicit parentheses about the intended grouping.
*}


subsection {* Mathematical Symbols *}

text {*
  Concrete syntax based on plain ASCII characters has its inherent
  limitations.  Rich mathematical notation demands a larger repertoire
  of symbols.  Several standards of extended character sets have been
  proposed over decades, but none has become universally available so
  far, not even Unicode\index{Unicode}.  Isabelle supports a generic
  notion of \bfindex{symbols} as the smallest entities of source text,
  without referring to internal encodings.

  There are three kinds of such ``generalized characters'' available:

  \begin{enumerate}

  \item 7-bit ASCII characters

  \item named symbols: \verb,\,\verb,<,$ident$\verb,>,

  \item named control symbols: \verb,\,\verb,<^,$ident$\verb,>,

  \end{enumerate}

  Here $ident$ may be any identifier according to the usual Isabelle
  conventions.  This results in an infinite store of symbols, whose
  interpretation is left to further front-end tools.  For example,
  both by the user-interface of Proof~General + X-Symbol and the
  Isabelle document processor (see \S\ref{sec:document-preparation})
  display the \verb,\,\verb,<forall>, symbol really as ``$\forall$''.

  A list of standard Isabelle symbols is given in
  \cite[appendix~A]{isabelle-sys}.  Users may introduce their own
  interpretation of further symbols by configuring the appropriate
  front-end tool accordingly, e.g.\ by defining certain {\LaTeX}
  macros (see also \S\ref{sec:doc-prep-symbols}).  There are also a
  few predefined control symbols, such as \verb,\,\verb,<^sub>, and
  \verb,\,\verb,<^sup>, for sub- and superscript of the subsequent
  (printable) symbol, respectively.  For example, \verb,A\<^sup>\<star>, is
  shown as ``@{text "A\<^sup>\<star>"}''.

  \medskip The following version of our @{text xor} definition uses a
  standard Isabelle symbol to achieve typographically pleasing output.
*}

(*<*)
hide const xor
ML_setup {* Context.>> (Theory.add_path "1") *}
(*>*)
constdefs
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"    (infixl "\<oplus>" 60)
  "A \<oplus> B \<equiv> (A \<and> \<not> B) \<or> (\<not> A \<and> B)"
(*<*)
local
(*>*)

text {*
  \noindent The X-Symbol package within Proof~General provides several
  input methods to enter @{text \<oplus>} in the text.  If all fails one may
  just type \verb,\,\verb,<oplus>, by hand; the display will be
  adapted immediately after continuing input.

  \medskip A slightly more refined scheme is to provide alternative
  syntax via the \bfindex{print mode} concept of Isabelle (see also
  \cite{isabelle-ref}).  By convention, the mode of ``$xsymbols$'' is
  enabled whenever Proof~General's X-Symbol mode (or {\LaTeX} output)
  is active.  Consider the following hybrid declaration of @{text
  xor}.
*}

(*<*)
hide const xor
ML_setup {* Context.>> (Theory.add_path "2") *}
(*>*)
constdefs
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"    (infixl "[+]\<ignore>" 60)
  "A [+]\<ignore> B \<equiv> (A \<and> \<not> B) \<or> (\<not> A \<and> B)"

syntax (xsymbols)
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"    (infixl "\<oplus>\<ignore>" 60)
(*<*)
local
(*>*)

text {*
  The \commdx{syntax} command introduced here acts like
  \isakeyword{consts}, but without declaring a logical constant; an
  optional print mode specification may be given, too.  Note that the
  type declaration given here merely serves for syntactic purposes,
  and is not checked for consistency with the real constant.

  \medskip We may now write either @{text "[+]"} or @{text "\<oplus>"} in
  input, while output uses the nicer syntax of $xsymbols$, provided
  that print mode is presently active.  Such an arrangement is
  particularly useful for interactive development, where users may
  type plain ASCII text, but gain improved visual feedback from the
  system (say in current goal output).

  \begin{warn}
  Alternative syntax declarations are apt to result in varying
  occurrences of concrete syntax in the input sources.  Isabelle
  provides no systematic way to convert alternative syntax expressions
  back and forth; print modes only affect situations where formal
  entities are pretty printed by the Isabelle process (e.g.\ output of
  terms and types), but not the original theory text.
  \end{warn}

  \medskip The following variant makes the alternative @{text \<oplus>}
  notation only available for output.  Thus we may enforce input
  sources to refer to plain ASCII only, but effectively disable
  cut-and-paste from output as well.
*}

syntax (xsymbols output)
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"    (infixl "\<oplus>\<ignore>" 60)


subsection {* Prefix Annotations *}

text {*
  Prefix syntax annotations\index{prefix annotation} are just another
  degenerate form of general mixfixes \cite{isabelle-ref}, without any
  template arguments or priorities --- just some bits of literal
  syntax.  The following example illustrates this idea idea by
  associating common symbols with the constructors of a datatype.
*}

datatype currency =
    Euro nat    ("\<euro>")
  | Pounds nat  ("\<pounds>")
  | Yen nat     ("\<yen>")
  | Dollar nat  ("$")

text {*
  \noindent Here the mixfix annotations on the rightmost column happen
  to consist of a single Isabelle symbol each: \verb,\,\verb,<euro>,,
  \verb,\,\verb,<pounds>,, \verb,\,\verb,<yen>,, and \verb,$,.  Recall
  that a constructor like @{text Euro} actually is a function @{typ
  "nat \<Rightarrow> currency"}.  An expression like @{text "Euro 10"} will be
  printed as @{term "\<euro> 10"}; only the head of the application is
  subject to our concrete syntax.  This simple form already achieves
  conformance with notational standards of the European Commission.

  \medskip Certainly, the same idea of prefix syntax also works for
  \isakeyword{consts}, \isakeyword{constdefs} etc.  The slightly
  unusual syntax declaration below decorates the existing @{typ
  currency} type with the international currency symbol @{text \<currency>}
  (\verb,\,\verb,<currency>,).
*}

syntax
  currency :: type    ("\<currency>")

text {*
  \noindent Here @{typ type} refers to the builtin syntactic category
  of Isabelle types.  We may now write down funny things like @{text
  "\<euro> :: nat \<Rightarrow> \<currency>"}, for example.
*}


subsection {* Syntax Translations \label{sec:syntax-translations} *}

text{*
  Mixfix syntax annotations work well for those situations where a
  particular constant application forms need to be decorated by
  concrete syntax; just reconsider @{text "xor A B"} versus @{text "A
  \<oplus> B"} covered before.  Occasionally, the relationship between some
  piece of notation and its internal form is slightly more involved.
  Here the concept of \bfindex{syntax translations} enters the scene.

  Using the raw \isakeyword{syntax}\index{syntax (command)} command we
  may introduce uninterpreted notational elements, while
  \commdx{translations} relates the input forms with more complex
  logical expressions.  This essentially provides a simple mechanism
  for for syntactic macros; even heavier transformations may be
  programmed in ML \cite{isabelle-ref}.

  \medskip A typical example of syntax translations is to decorate
  relational expressions (set membership of tuples) with nice symbolic
  notation, such as @{text "(x, y) \<in> sim"} versus @{text "x \<approx> y"}.
*}

consts
  sim :: "('a \<times> 'a) set"

syntax
  "_sim" :: "'a \<Rightarrow> 'a \<Rightarrow> bool"    (infix "\<approx>" 50)
translations
  "x \<approx> y" \<rightleftharpoons> "(x, y) \<in> sim"

text {*
  \noindent Here the name of the dummy constant @{text "_sim"} does
  not really matter, as long as it is not used elsewhere.  Prefixing
  an underscore is a common convention.  The \isakeyword{translations}
  declaration already uses concrete syntax on the left-hand side;
  internally we relate a raw application @{text "_sim x y"} with
  @{text "(x, y) \<in> sim"}.

  \medskip Another common application of syntax translations is to
  provide variant versions of fundamental relational expressions, such
  as @{text \<noteq>} for negated equalities.  The following declaration
  stems from Isabelle/HOL itself:
*}

syntax "_not_equal" :: "'a \<Rightarrow> 'a \<Rightarrow> bool"    (infixl "\<noteq>\<ignore>" 50)
translations "x \<noteq>\<ignore> y" \<rightleftharpoons> "\<not> (x = y)"

text {*
  \noindent Normally one would introduce derived concepts like this
  within the logic, using \isakeyword{consts} + \isakeyword{defs}
  instead of \isakeyword{syntax} + \isakeyword{translations}.  The
  present formulation has the virtue that expressions are immediately
  replaced by its ``definition'' upon parsing; the effect is reversed
  upon printing.  Internally, @{text"\<noteq>"} never appears.

  Simulating definitions via translations is adequate for very basic
  logical concepts, where a new representation is a trivial variation
  on an existing one.  On the other hand, syntax translations do not
  scale up well to large hierarchies of concepts built on each other.
*}


section {* Document Preparation \label{sec:document-preparation} *}

text {*
  Isabelle/Isar is centered around the concept of \bfindex{formal
  proof documents}\index{documents|bold}.  Ultimately the result of
  the user's theory development efforts is meant to be a
  human-readable record, presented as a browsable PDF file or printed
  on paper.  The overall document structure follows traditional
  mathematical articles, with sectioning, intermediate explanations,
  definitions, theorem statements and proofs.

  The Isar proof language \cite{Wenzel-PhD}, which is not covered in
  this book, admits to write formal proof texts that are acceptable
  both to the machine and human readers at the same time.  Thus
  marginal comments and explanations may be kept at a minimum.  Even
  without proper coverage of human-readable proofs, Isabelle document
  is very useful to produce formally derived texts (elaborating on the
  specifications etc.).  Unstructured proof scripts given here may be
  just ignored by readers, or intentionally suppressed from the text
  by the writer (see also \S\ref{sec:doc-prep-suppress}).

  \medskip The Isabelle document preparation system essentially acts
  like a formal front-end to {\LaTeX}.  After checking specifications
  and proofs, the theory sources are turned into typesetting
  instructions in a well-defined manner.  This enables users to write
  authentic reports on formal theory developments with little
  additional effort, the most tedious consistency checks are handled
  by the system.
*}


subsection {* Isabelle Sessions *}

text {*
  In contrast to the highly interactive mode of Isabelle/Isar theory
  development, the document preparation stage essentially works in
  batch-mode.  An Isabelle \bfindex{session} essentially consists of a
  collection of theory source files that contribute to a single output
  document eventually.  Session is derived from a single parent each
  (usually an object-logic image like \texttt{HOL}), resulting in an
  overall tree structure that is reflected in the output location
  within the file system (usually rooted at
  \verb,~/isabelle/browser_info,).

  Here is the canonical arrangement of sources of a session called
  \texttt{MySession}:

  \begin{itemize}

  \item Directory \texttt{MySession} contains the required theory
  files ($A@1$\texttt{.thy}, \dots, $A@n$\texttt{.thy}).

  \item File \texttt{MySession/ROOT.ML} holds appropriate ML commands
  for loading all wanted theories, usually just
  ``\texttt{use_thy~"$A@i$";}'' for any $A@i$ in leaf position of the
  theory dependency graph.

  \item Directory \texttt{MySession/document} contains everything
  required for the {\LaTeX} stage; only \texttt{root.tex} needs to be
  provided initially.

  The latter file holds appropriate {\LaTeX} code to commence a
  document (\verb,\documentclass, etc.), and to include the generated
  files $A@i$\texttt{.tex} for each theory.  The generated
  \texttt{session.tex} will hold {\LaTeX} commands to include all
  theory output files in topologically sorted order, so
  \verb,\input{session}, in \texttt{root.tex} will do it in most
  situations.

  \item In addition, \texttt{IsaMakefile} outside of the directory
  \texttt{MySession} holds appropriate dependencies and invocations of
  Isabelle tools to control the batch job.  In fact, several sessions
  may be controlled by the same \texttt{IsaMakefile}.  See also
  \cite{isabelle-sys} for further details, especially on
  \texttt{isatool usedir} and \texttt{isatool make}.

  \end{itemize}

  With everything put in its proper place, \texttt{isatool make}
  should be sufficient to process the Isabelle session completely,
  with the generated document appearing in its proper place.

  \medskip In practice, users may want to have \texttt{isatool mkdir}
  generate an initial working setup without further ado.  For example,
  an empty session \texttt{MySession} derived from \texttt{HOL} may be
  produced as follows:

\begin{verbatim}
  isatool mkdir HOL MySession
  isatool make
\end{verbatim}

  This processes the session with sensible default options, including
  verbose mode to tell the user where the ultimate results will
  appear.  The above dry run should produce should already be able to
  produce a single page of output (with a dummy title, empty table of
  contents etc.).  Any failure at that stage is likely to indicate
  technical problems with the user's {\LaTeX}
  installation.\footnote{Especially make sure that \texttt{pdflatex}
  is present; if all fails one may fall back on DVI output by changing
  \texttt{usedir} options \cite{isabelle-sys}.}

  \medskip One may now start to populate the directory
  \texttt{MySession}, and the file \texttt{MySession/ROOT.ML}
  accordingly.  \texttt{MySession/document/root.tex} should be also
  adapted at some point; the default version is mostly
  self-explanatory.

  Especially note the standard inclusion of {\LaTeX} packages
  \texttt{isabelle} (mandatory), and \texttt{isabellesym} (required
  for mathematical symbols), and the final \texttt{pdfsetup} (provides
  handsome defaults for \texttt{hyperref}, including URL markup).
  Further {\LaTeX} packages further packages may required in
  particular applications, e.g.\ for unusual Isabelle symbols.

  \medskip Further auxiliary files for the {\LaTeX} stage should be
  included in the \texttt{MySession/document} directory, e.g.\
  additional {\TeX} sources or graphics.  In particular, adding
  \texttt{root.bib} here (with that specific name) causes an automatic
  run of \texttt{bibtex} to process a bibliographic database; see for
  further commodities \texttt{isatool document} covered in
  \cite{isabelle-sys}.

  \medskip Any failure of the document preparation phase in an
  Isabelle batch session leaves the generated sources in there target
  location (as pointed out by the accompanied error message).  In case
  of {\LaTeX} errors, users may trace error messages at the file
  position of the generated text.
*}


subsection {* Structure Markup *}

text {*
  The large-scale structure of Isabelle documents follows existing
  {\LaTeX} conventions, with chapters, sections, subsubsections etc.
  The Isar language includes separate \bfindex{markup commands}, which
  do not effect the formal content of a theory (or proof), but result
  in corresponding {\LaTeX} elements issued to the output.

  There are separate markup commands for different formal contexts: in
  header position (just before a \isakeyword{theory} command), within
  the theory body, or within a proof.  Note that the header needs to
  be treated specially, since ordinary theory and proof commands may
  only occur \emph{after} the initial \isakeyword{theory}
  specification.

  \smallskip

  \begin{tabular}{llll}
  header & theory & proof & default meaning \\\hline
    & \commdx{chapter} & & \verb,\chapter, \\
  \commdx{header} & \commdx{section} & \commdx{sect} & \verb,\section, \\
    & \commdx{subsection} & \commdx{subsect} & \verb,\subsection, \\
    & \commdx{subsubsection} & \commdx{subsubsect} & \verb,\subsubsection, \\
  \end{tabular}

  \medskip

  From the Isabelle perspective, each markup command takes a single
  text argument (delimited by \verb,",\dots\verb,", or
  \verb,{,\verb,*,~\dots~\verb,*,\verb,},).  After stripping any
  surrounding white space, the argument is passed to a {\LaTeX} macro
  \verb,\isamarkupXYZ, for any command \isakeyword{XYZ}.  These macros
  are defined in \verb,isabelle.sty, according to the meaning given in
  the rightmost column above.

  \medskip The following source fragment illustrates structure markup
  of a theory.  Note that {\LaTeX} labels may be included inside of
  section headings as well.

  \begin{ttbox}
  header {\ttlbrace}* Some properties of Foo Bar elements *{\ttrbrace}

  theory Foo_Bar = Main:

  subsection {\ttlbrace}* Basic definitions *{\ttrbrace}

  consts
    foo :: \dots
    bar :: \dots

  defs \dots

  subsection {\ttlbrace}* Derived rules *{\ttrbrace}

  lemma fooI: \dots
  lemma fooE: \dots

  subsection {\ttlbrace}* Main theorem {\ttback}label{\ttlbrace}sec:main-theorem{\ttrbrace} *{\ttrbrace}

  theorem main: \dots

  end
  \end{ttbox}

  Users may occasionally want to change the meaning of markup
  commands, say via \verb,\renewcommand, in \texttt{root.tex}.  The
  \verb,\isamarkupheader, is a good candidate for some adaption, e.g.\
  moving it up in the hierarchy to become \verb,\chapter,.

\begin{verbatim}
  \renewcommand{\isamarkupheader}[1]{\chapter{#1}}
\end{verbatim}

  \noindent Certainly, this requires to change the default
  \verb,\documentclass{article}, in \texttt{root.tex} to something
  that supports the notion of chapters in the first place, e.g.\
  \verb,\documentclass{report},.

  \medskip The {\LaTeX} macro \verb,\isabellecontext, is maintained to
  hold the name of the current theory context.  This is particularly
  useful for document headings:

\begin{verbatim}
  \renewcommand{\isamarkupheader}[1]
  {\chapter{#1}\markright{THEORY~\isabellecontext}}
\end{verbatim}

  \noindent Make sure to include something like
  \verb,\pagestyle{headings}, in \texttt{root.tex}; the document
  should have more than 2 pages to show the effect.
*}


subsection {* Formal Comments and Antiquotations *}

text {*
  Comments of the form \verb,(,\verb,*,~\dots~\verb,*,\verb,),

  FIXME

*}


subsection {* Symbols and Characters \label{sec:doc-prep-symbols} *}

text {*
  FIXME \verb,\isabellestyle,
*}


subsection {* Suppressing Output \label{sec:doc-prep-suppress} *}

text {*
  By default Isabelle's document system generates a {\LaTeX} source
  file for each theory that happens to get loaded during the session.
  The generated \texttt{session.tex} will include all of these in
  order of appearance, which in turn gets included by the standard
  \texttt{root.tex}.  Certainly one may change the order of appearance
  or suppress unwanted theories by ignoring \texttt{session.tex} and
  include individual files in \texttt{root.tex} by hand.  On the other
  hand, such an arrangement requires additional maintenance chores
  whenever the collection of theories changes.

  Alternatively, one may tune the theory loading process in
  \texttt{ROOT.ML} itself: traversal of the theory dependency graph
  may be fine-tuned by adding further \verb,use_thy, invocations,
  although topological sorting still has to be observed.  Moreover,
  the ML operator \verb,no_document, temporarily disables document
  generation while executing a theory loader command; its usage is
  like this:

\begin{verbatim}
  no_document use_thy "A";
\end{verbatim}

  \medskip Theory output may be also suppressed in smaller portions as
  well.  For example, research papers or slides usually do not include
  the formal content in full.  In order to delimit \bfindex{ignored
  material} special source comments
  \verb,(,\verb,*,\verb,<,\verb,*,\verb,), and
  \verb,(,\verb,*,\verb,>,\verb,*,\verb,), may be included in the
  text.  Only the document preparation system is affected, the formal
  checking the theory is performed as before.

  In the following example we suppress the slightly formalistic
  \isakeyword{theory} + \isakeyword{end} surroundings a theory.

  \medskip

  \begin{tabular}{l}
  \verb,(,\verb,*,\verb,<,\verb,*,\verb,), \\
  \texttt{theory A = Main:} \\
  \verb,(,\verb,*,\verb,>,\verb,*,\verb,), \\
  ~~$\vdots$ \\
  \verb,(,\verb,*,\verb,<,\verb,*,\verb,), \\
  \texttt{end} \\
  \verb,(,\verb,*,\verb,>,\verb,*,\verb,), \\
  \end{tabular}

  \medskip

  Text may be suppressed in a fine grained manner.  For example, we
  may even drop vital parts of a formal proof, pretending that things
  have been simpler than in reality.  For example, the following
  ``fully automatic'' proof is actually a fake:
*}

lemma "x \<noteq> (0::int) \<Longrightarrow> 0 < x * x"
  by (auto(*<*)simp add: int_less_le(*>*))

text {*
  \noindent Here the real source of the proof has been as follows:

\begin{verbatim}
  by (auto(*<*)simp add: int_less_le(*>*))
\end{verbatim} %(*

  \medskip Ignoring portions of printed does demand some care by the
  user.  First of all, the writer is responsible not to obfuscate the
  underlying formal development in an unduly manner.  It is fairly
  easy to invalidate the remaining visible text, e.g.\ by referencing
  questionable formal items (strange definitions, arbitrary axioms
  etc.) that have been hidden from sight beforehand.

  Some minor technical subtleties of the
  \verb,(,\verb,*,\verb,<,\verb,*,\verb,),-\verb,(,\verb,*,\verb,>,\verb,*,\verb,),
  elements need to be kept in mind as well, since the system performs
  little sanity checks here.  Arguments of markup commands and formal
  comments must not be hidden, otherwise presentation fails.  Open and
  close parentheses need to be inserted carefully; it is fairly easy
  to hide the wrong parts, especially after rearranging the sources.

  \medskip Authentic reports of formal theories, say as part of a
  library, usually should refrain from suppressing parts of the text
  at all.  Other users may need the full information for their own
  derivative work.  If a particular formalization appears inadequate
  for general public coverage, it is often more appropriate to think
  of a better way in the first place.
*}

(*<*)
end
(*>*)
