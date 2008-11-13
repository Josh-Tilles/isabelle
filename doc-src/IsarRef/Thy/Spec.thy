(* $Id$ *)

theory Spec
imports Main
begin

chapter {* Theory specifications *}

section {* Defining theories \label{sec:begin-thy} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "theory"} & : & @{text "toplevel \<rightarrow> theory"} \\
    @{command_def (global) "end"} & : & @{text "theory \<rightarrow> toplevel"} \\
  \end{matharray}

  Isabelle/Isar theories are defined via theory files, which may
  contain both specifications and proofs; occasionally definitional
  mechanisms also require some explicit proof.  The theory body may be
  sub-structured by means of \emph{local theory targets}, such as
  @{command "locale"} and @{command "class"}.

  The first proper command of a theory is @{command "theory"}, which
  indicates imports of previous theories and optional dependencies on
  other source files (usually in ML).  Just preceding the initial
  @{command "theory"} command there may be an optional @{command
  "header"} declaration, which is only relevant to document
  preparation: see also the other section markup commands in
  \secref{sec:markup}.

  A theory is concluded by a final @{command (global) "end"} command,
  one that does not belong to a local theory target.  No further
  commands may follow such a global @{command (global) "end"},
  although some user-interfaces might pretend that trailing input is
  admissible.

  \begin{rail}
    'theory' name 'imports' (name +) uses? 'begin'
    ;

    uses: 'uses' ((name | parname) +);
  \end{rail}

  \begin{description}

  \item @{command "theory"}~@{text "A \<IMPORTS> B\<^sub>1 \<dots> B\<^sub>n \<BEGIN>"}
  starts a new theory @{text A} based on the merge of existing
  theories @{text "B\<^sub>1 \<dots> B\<^sub>n"}.
  
  Due to the possibility to import more than one ancestor, the
  resulting theory structure of an Isabelle session forms a directed
  acyclic graph (DAG).  Isabelle's theory loader ensures that the
  sources contributing to the development graph are always up-to-date:
  changed files are automatically reloaded whenever a theory header
  specification is processed.
  
  The optional @{keyword_def "uses"} specification declares additional
  dependencies on extra files (usually ML sources).  Files will be
  loaded immediately (as ML), unless the name is parenthesized.  The
  latter case records a dependency that needs to be resolved later in
  the text, usually via explicit @{command_ref "use"} for ML files;
  other file formats require specific load commands defined by the
  corresponding tools or packages.
  
  \item @{command (global) "end"} concludes the current theory
  definition.  Note that local theory targets involve a local
  @{command (local) "end"}, which is clear from the nesting.

  \end{description}
*}


section {* Local theory targets \label{sec:target} *}

text {*
  A local theory target is a context managed separately within the
  enclosing theory.  Contexts may introduce parameters (fixed
  variables) and assumptions (hypotheses).  Definitions and theorems
  depending on the context may be added incrementally later on.  Named
  contexts refer to locales (cf.\ \secref{sec:locale}) or type classes
  (cf.\ \secref{sec:class}); the name ``@{text "-"}'' signifies the
  global theory context.

  \begin{matharray}{rcll}
    @{command_def "context"} & : & @{text "theory \<rightarrow> local_theory"} \\
    @{command_def (local) "end"} & : & @{text "local_theory \<rightarrow> theory"} \\
  \end{matharray}

  \indexouternonterm{target}
  \begin{rail}
    'context' name 'begin'
    ;

    target: '(' 'in' name ')'
    ;
  \end{rail}

  \begin{description}
  
  \item @{command "context"}~@{text "c \<BEGIN>"} recommences an
  existing locale or class context @{text c}.  Note that locale and
  class definitions allow to include the @{keyword "begin"} keyword as
  well, in order to continue the local theory immediately after the
  initial specification.
  
  \item @{command (local) "end"} concludes the current local theory
  and continues the enclosing global theory.  Note that a global
  @{command (global) "end"} has a different meaning: it concludes the
  theory itself (\secref{sec:begin-thy}).
  
  \item @{text "(\<IN> c)"} given after any local theory command
  specifies an immediate target, e.g.\ ``@{command
  "definition"}~@{text "(\<IN> c) \<dots>"}'' or ``@{command
  "theorem"}~@{text "(\<IN> c) \<dots>"}''.  This works both in a local or
  global theory context; the current target context will be suspended
  for this command only.  Note that ``@{text "(\<IN> -)"}'' will
  always produce a global result independently of the current target
  context.

  \end{description}

  The exact meaning of results produced within a local theory context
  depends on the underlying target infrastructure (locale, type class
  etc.).  The general idea is as follows, considering a context named
  @{text c} with parameter @{text x} and assumption @{text "A[x]"}.
  
  Definitions are exported by introducing a global version with
  additional arguments; a syntactic abbreviation links the long form
  with the abstract version of the target context.  For example,
  @{text "a \<equiv> t[x]"} becomes @{text "c.a ?x \<equiv> t[?x]"} at the theory
  level (for arbitrary @{text "?x"}), together with a local
  abbreviation @{text "c \<equiv> c.a x"} in the target context (for the
  fixed parameter @{text x}).

  Theorems are exported by discharging the assumptions and
  generalizing the parameters of the context.  For example, @{text "a:
  B[x]"} becomes @{text "c.a: A[?x] \<Longrightarrow> B[?x]"}, again for arbitrary
  @{text "?x"}.
*}


section {* Basic specification elements *}

text {*
  \begin{matharray}{rcll}
    @{command_def "axiomatization"} & : & @{text "theory \<rightarrow> theory"} & (axiomatic!)\\
    @{command_def "definition"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{attribute_def "defn"} & : & @{text attribute} \\
    @{command_def "abbreviation"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "print_abbrevs"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow> "} \\
    @{command_def "notation"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "no_notation"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  \end{matharray}

  These specification mechanisms provide a slightly more abstract view
  than the underlying primitives of @{command "consts"}, @{command
  "defs"} (see \secref{sec:consts}), and @{command "axioms"} (see
  \secref{sec:axms-thms}).  In particular, type-inference is commonly
  available, and result names need not be given.

  \begin{rail}
    'axiomatization' target? fixes? ('where' specs)?
    ;
    'definition' target? (decl 'where')? thmdecl? prop
    ;
    'abbreviation' target? mode? (decl 'where')? prop
    ;
    ('notation' | 'no\_notation') target? mode? (nameref structmixfix + 'and')
    ;

    fixes: ((name ('::' type)? mixfix? | vars) + 'and')
    ;
    specs: (thmdecl? props + 'and')
    ;
    decl: name ('::' type)? mixfix?
    ;
  \end{rail}

  \begin{description}
  
  \item @{command "axiomatization"}~@{text "c\<^sub>1 \<dots> c\<^sub>m \<WHERE> \<phi>\<^sub>1 \<dots> \<phi>\<^sub>n"}
  introduces several constants simultaneously and states axiomatic
  properties for these.  The constants are marked as being specified
  once and for all, which prevents additional specifications being
  issued later on.
  
  Note that axiomatic specifications are only appropriate when
  declaring a new logical system; axiomatic specifications are
  restricted to global theory contexts.  Normal applications should
  only use definitional mechanisms!

  \item @{command "definition"}~@{text "c \<WHERE> eq"} produces an
  internal definition @{text "c \<equiv> t"} according to the specification
  given as @{text eq}, which is then turned into a proven fact.  The
  given proposition may deviate from internal meta-level equality
  according to the rewrite rules declared as @{attribute defn} by the
  object-logic.  This usually covers object-level equality @{text "x =
  y"} and equivalence @{text "A \<leftrightarrow> B"}.  End-users normally need not
  change the @{attribute defn} setup.
  
  Definitions may be presented with explicit arguments on the LHS, as
  well as additional conditions, e.g.\ @{text "f x y = t"} instead of
  @{text "f \<equiv> \<lambda>x y. t"} and @{text "y \<noteq> 0 \<Longrightarrow> g x y = u"} instead of an
  unrestricted @{text "g \<equiv> \<lambda>x y. u"}.
  
  \item @{command "abbreviation"}~@{text "c \<WHERE> eq"} introduces a
  syntactic constant which is associated with a certain term according
  to the meta-level equality @{text eq}.
  
  Abbreviations participate in the usual type-inference process, but
  are expanded before the logic ever sees them.  Pretty printing of
  terms involves higher-order rewriting with rules stemming from
  reverted abbreviations.  This needs some care to avoid overlapping
  or looping syntactic replacements!
  
  The optional @{text mode} specification restricts output to a
  particular print mode; using ``@{text input}'' here achieves the
  effect of one-way abbreviations.  The mode may also include an
  ``@{keyword "output"}'' qualifier that affects the concrete syntax
  declared for abbreviations, cf.\ @{command "syntax"} in
  \secref{sec:syn-trans}.
  
  \item @{command "print_abbrevs"} prints all constant abbreviations
  of the current context.
  
  \item @{command "notation"}~@{text "c (mx)"} associates mixfix
  syntax with an existing constant or fixed variable.  This is a
  robust interface to the underlying @{command "syntax"} primitive
  (\secref{sec:syn-trans}).  Type declaration and internal syntactic
  representation of the given entity is retrieved from the context.
  
  \item @{command "no_notation"} is similar to @{command "notation"},
  but removes the specified syntax annotation from the present
  context.

  \end{description}

  All of these specifications support local theory targets (cf.\
  \secref{sec:target}).
*}


section {* Generic declarations *}

text {*
  Arbitrary operations on the background context may be wrapped-up as
  generic declaration elements.  Since the underlying concept of local
  theories may be subject to later re-interpretation, there is an
  additional dependency on a morphism that tells the difference of the
  original declaration context wrt.\ the application context
  encountered later on.  A fact declaration is an important special
  case: it consists of a theorem which is applied to the context by
  means of an attribute.

  \begin{matharray}{rcl}
    @{command_def "declaration"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "declare"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  \end{matharray}

  \begin{rail}
    'declaration' target? text
    ;
    'declare' target? (thmrefs + 'and')
    ;
  \end{rail}

  \begin{description}

  \item @{command "declaration"}~@{text d} adds the declaration
  function @{text d} of ML type @{ML_type declaration}, to the current
  local theory under construction.  In later application contexts, the
  function is transformed according to the morphisms being involved in
  the interpretation hierarchy.

  \item @{command "declare"}~@{text thms} declares theorems to the
  current local theory context.  No theorem binding is involved here,
  unlike @{command "theorems"} or @{command "lemmas"} (cf.\
  \secref{sec:axms-thms}), so @{command "declare"} only has the effect
  of applying attributes as included in the theorem specification.

  \end{description}
*}


section {* Locales \label{sec:locale} *}

text {*
  Locales are named local contexts, consisting of a list of
  declaration elements that are modeled after the Isar proof context
  commands (cf.\ \secref{sec:proof-context}).
*}


subsection {* Locale specifications *}

text {*
  \begin{matharray}{rcl}
    @{command_def "locale"} & : & @{text "theory \<rightarrow> local_theory"} \\
    @{command_def "print_locale"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "print_locales"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{method_def intro_locales} & : & @{text method} \\
    @{method_def unfold_locales} & : & @{text method} \\
  \end{matharray}

  \indexouternonterm{contextexpr}\indexouternonterm{contextelem}
  \indexisarelem{fixes}\indexisarelem{constrains}\indexisarelem{assumes}
  \indexisarelem{defines}\indexisarelem{notes}\indexisarelem{includes}
  \begin{rail}
    'locale' name ('=' localeexpr)? 'begin'?
    ;
    'print\_locale' '!'? localeexpr
    ;
    localeexpr: ((contextexpr '+' (contextelem+)) | contextexpr | (contextelem+))
    ;

    contextexpr: nameref | '(' contextexpr ')' |
    (contextexpr (name mixfix? +)) | (contextexpr + '+')
    ;
    contextelem: fixes | constrains | assumes | defines | notes
    ;
    fixes: 'fixes' ((name ('::' type)? structmixfix? | vars) + 'and')
    ;
    constrains: 'constrains' (name '::' type + 'and')
    ;
    assumes: 'assumes' (thmdecl? props + 'and')
    ;
    defines: 'defines' (thmdecl? prop proppat? + 'and')
    ;
    notes: 'notes' (thmdef? thmrefs + 'and')
    ;
    includes: 'includes' contextexpr
    ;
  \end{rail}

  \begin{description}
  
  \item @{command "locale"}~@{text "loc = import + body"} defines a
  new locale @{text loc} as a context consisting of a certain view of
  existing locales (@{text import}) plus some additional elements
  (@{text body}).  Both @{text import} and @{text body} are optional;
  the degenerate form @{command "locale"}~@{text loc} defines an empty
  locale, which may still be useful to collect declarations of facts
  later on.  Type-inference on locale expressions automatically takes
  care of the most general typing that the combined context elements
  may acquire.

  The @{text import} consists of a structured context expression,
  consisting of references to existing locales, renamed contexts, or
  merged contexts.  Renaming uses positional notation: @{text "c
  x\<^sub>1 \<dots> x\<^sub>n"} means that (a prefix of) the fixed
  parameters of context @{text c} are named @{text "x\<^sub>1, \<dots>,
  x\<^sub>n"}; a ``@{text _}'' (underscore) means to skip that
  position.  Renaming by default deletes concrete syntax, but new
  syntax may by specified with a mixfix annotation.  An exeption of
  this rule is the special syntax declared with ``@{text
  "(\<STRUCTURE>)"}'' (see below), which is neither deleted nor can it
  be changed.  Merging proceeds from left-to-right, suppressing any
  duplicates stemming from different paths through the import
  hierarchy.

  The @{text body} consists of basic context elements, further context
  expressions may be included as well.

  \begin{description}

  \item @{element "fixes"}~@{text "x :: \<tau> (mx)"} declares a local
  parameter of type @{text \<tau>} and mixfix annotation @{text mx} (both
  are optional).  The special syntax declaration ``@{text
  "(\<STRUCTURE>)"}'' means that @{text x} may be referenced
  implicitly in this context.

  \item @{element "constrains"}~@{text "x :: \<tau>"} introduces a type
  constraint @{text \<tau>} on the local parameter @{text x}.

  \item @{element "assumes"}~@{text "a: \<phi>\<^sub>1 \<dots> \<phi>\<^sub>n"}
  introduces local premises, similar to @{command "assume"} within a
  proof (cf.\ \secref{sec:proof-context}).

  \item @{element "defines"}~@{text "a: x \<equiv> t"} defines a previously
  declared parameter.  This is similar to @{command "def"} within a
  proof (cf.\ \secref{sec:proof-context}), but @{element "defines"}
  takes an equational proposition instead of variable-term pair.  The
  left-hand side of the equation may have additional arguments, e.g.\
  ``@{element "defines"}~@{text "f x\<^sub>1 \<dots> x\<^sub>n \<equiv> t"}''.

  \item @{element "notes"}~@{text "a = b\<^sub>1 \<dots> b\<^sub>n"}
  reconsiders facts within a local context.  Most notably, this may
  include arbitrary declarations in any attribute specifications
  included here, e.g.\ a local @{attribute simp} rule.

  \item @{element "includes"}~@{text c} copies the specified context
  in a statically scoped manner.  Only available in the long goal
  format of \secref{sec:goals}.

  In contrast, the initial @{text import} specification of a locale
  expression maintains a dynamic relation to the locales being
  referenced (benefiting from any later fact declarations in the
  obvious manner).

  \end{description}
  
  Note that ``@{text "(\<IS> p\<^sub>1 \<dots> p\<^sub>n)"}'' patterns given
  in the syntax of @{element "assumes"} and @{element "defines"} above
  are illegal in locale definitions.  In the long goal format of
  \secref{sec:goals}, term bindings may be included as expected,
  though.
  
  \medskip By default, locale specifications are ``closed up'' by
  turning the given text into a predicate definition @{text
  loc_axioms} and deriving the original assumptions as local lemmas
  (modulo local definitions).  The predicate statement covers only the
  newly specified assumptions, omitting the content of included locale
  expressions.  The full cumulative view is only provided on export,
  involving another predicate @{text loc} that refers to the complete
  specification text.
  
  In any case, the predicate arguments are those locale parameters
  that actually occur in the respective piece of text.  Also note that
  these predicates operate at the meta-level in theory, but the locale
  packages attempts to internalize statements according to the
  object-logic setup (e.g.\ replacing @{text \<And>} by @{text \<forall>}, and
  @{text "\<Longrightarrow>"} by @{text "\<longrightarrow>"} in HOL; see also
  \secref{sec:object-logic}).  Separate introduction rules @{text
  loc_axioms.intro} and @{text loc.intro} are provided as well.
  
  \item @{command "print_locale"}~@{text "import + body"} prints the
  specified locale expression in a flattened form.  The notable
  special case @{command "print_locale"}~@{text loc} just prints the
  contents of the named locale, but keep in mind that type-inference
  will normalize type variables according to the usual alphabetical
  order.  The command omits @{element "notes"} elements by default.
  Use @{command "print_locale"}@{text "!"} to get them included.

  \item @{command "print_locales"} prints the names of all locales
  of the current theory.

  \item @{method intro_locales} and @{method unfold_locales}
  repeatedly expand all introduction rules of locale predicates of the
  theory.  While @{method intro_locales} only applies the @{text
  loc.intro} introduction rules and therefore does not decend to
  assumptions, @{method unfold_locales} is more aggressive and applies
  @{text loc_axioms.intro} as well.  Both methods are aware of locale
  specifications entailed by the context, both from target and
  @{element "includes"} statements, and from interpretations (see
  below).  New goals that are entailed by the current context are
  discharged automatically.

  \end{description}
*}


subsection {* Interpretation of locales *}

text {*
  Locale expressions (more precisely, \emph{context expressions}) may
  be instantiated, and the instantiated facts added to the current
  context.  This requires a proof of the instantiated specification
  and is called \emph{locale interpretation}.  Interpretation is
  possible in theories and locales (command @{command
  "interpretation"}) and also within a proof body (command @{command
  "interpret"}).

  \begin{matharray}{rcl}
    @{command_def "interpretation"} & : & @{text "theory \<rightarrow> proof(prove)"} \\
    @{command_def "interpret"} & : & @{text "proof(state) | proof(chain \<rightarrow> proof(prove)"} \\
    @{command_def "print_interps"}@{text "\<^sup>*"} & : &  @{text "context \<rightarrow>"} \\
  \end{matharray}

  \indexouternonterm{interp}
  \begin{rail}
    'interpretation' (interp | name ('<' | subseteq) contextexpr)
    ;
    'interpret' interp
    ;
    'print\_interps' '!'? name
    ;
    instantiation: ('[' (inst+) ']')?
    ;
    interp: (name ':')? \\ (contextexpr instantiation |
      name instantiation 'where' (thmdecl? prop + 'and'))
    ;
  \end{rail}

  \begin{description}

  \item @{command "interpretation"}~@{text "expr insts \<WHERE> eqns"}

  The first form of @{command "interpretation"} interprets @{text
  expr} in the theory.  The instantiation is given as a list of terms
  @{text insts} and is positional.  All parameters must receive an
  instantiation term --- with the exception of defined parameters.
  These are, if omitted, derived from the defining equation and other
  instantiations.  Use ``@{text _}'' to omit an instantiation term.

  The command generates proof obligations for the instantiated
  specifications (assumes and defines elements).  Once these are
  discharged by the user, instantiated facts are added to the theory
  in a post-processing phase.

  Additional equations, which are unfolded in facts during
  post-processing, may be given after the keyword @{keyword "where"}.
  This is useful for interpreting concepts introduced through
  definition specification elements.  The equations must be proved.
  Note that if equations are present, the context expression is
  restricted to a locale name.

  The command is aware of interpretations already active in the
  theory, but does not simplify the goal automatically.  In order to
  simplify the proof obligations use methods @{method intro_locales}
  or @{method unfold_locales}.  Post-processing is not applied to
  facts of interpretations that are already active.  This avoids
  duplication of interpreted facts, in particular.  Note that, in the
  case of a locale with import, parts of the interpretation may
  already be active.  The command will only process facts for new
  parts.

  The context expression may be preceded by a name, which takes effect
  in the post-processing of facts.  It is used to prefix fact names,
  for example to avoid accidental hiding of other facts.

  Adding facts to locales has the effect of adding interpreted facts
  to the theory for all active interpretations also.  That is,
  interpretations dynamically participate in any facts added to
  locales.

  \item @{command "interpretation"}~@{text "name \<subseteq> expr"}

  This form of the command interprets @{text expr} in the locale
  @{text name}.  It requires a proof that the specification of @{text
  name} implies the specification of @{text expr}.  As in the
  localized version of the theorem command, the proof is in the
  context of @{text name}.  After the proof obligation has been
  dischared, the facts of @{text expr} become part of locale @{text
  name} as \emph{derived} context elements and are available when the
  context @{text name} is subsequently entered.  Note that, like
  import, this is dynamic: facts added to a locale part of @{text
  expr} after interpretation become also available in @{text name}.
  Like facts of renamed context elements, facts obtained by
  interpretation may be accessed by prefixing with the parameter
  renaming (where the parameters are separated by ``@{text _}'').

  Unlike interpretation in theories, instantiation is confined to the
  renaming of parameters, which may be specified as part of the
  context expression @{text expr}.  Using defined parameters in @{text
  name} one may achieve an effect similar to instantiation, though.

  Only specification fragments of @{text expr} that are not already
  part of @{text name} (be it imported, derived or a derived fragment
  of the import) are considered by interpretation.  This enables
  circular interpretations.

  If interpretations of @{text name} exist in the current theory, the
  command adds interpretations for @{text expr} as well, with the same
  prefix and attributes, although only for fragments of @{text expr}
  that are not interpreted in the theory already.

  \item @{command "interpret"}~@{text "expr insts \<WHERE> eqns"}
  interprets @{text expr} in the proof context and is otherwise
  similar to interpretation in theories.

  \item @{command "print_interps"}~@{text loc} prints the
  interpretations of a particular locale @{text loc} that are active
  in the current context, either theory or proof context.  The
  exclamation point argument triggers printing of \emph{witness}
  theorems justifying interpretations.  These are normally omitted
  from the output.
  
  \end{description}

  \begin{warn}
    Since attributes are applied to interpreted theorems,
    interpretation may modify the context of common proof tools, e.g.\
    the Simplifier or Classical Reasoner.  Since the behavior of such
    automated reasoning tools is \emph{not} stable under
    interpretation morphisms, manual declarations might have to be
    issued.
  \end{warn}

  \begin{warn}
    An interpretation in a theory may subsume previous
    interpretations.  This happens if the same specification fragment
    is interpreted twice and the instantiation of the second
    interpretation is more general than the interpretation of the
    first.  A warning is issued, since it is likely that these could
    have been generalized in the first place.  The locale package does
    not attempt to remove subsumed interpretations.
  \end{warn}
*}


section {* Classes \label{sec:class} *}

text {*
  A class is a particular locale with \emph{exactly one} type variable
  @{text \<alpha>}.  Beyond the underlying locale, a corresponding type class
  is established which is interpreted logically as axiomatic type
  class \cite{Wenzel:1997:TPHOL} whose logical content are the
  assumptions of the locale.  Thus, classes provide the full
  generality of locales combined with the commodity of type classes
  (notably type-inference).  See \cite{isabelle-classes} for a short
  tutorial.

  \begin{matharray}{rcl}
    @{command_def "class"} & : & @{text "theory \<rightarrow> local_theory"} \\
    @{command_def "instantiation"} & : & @{text "theory \<rightarrow> local_theory"} \\
    @{command_def "instance"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "subclass"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "print_classes"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{method_def intro_classes} & : & @{text method} \\
  \end{matharray}

  \begin{rail}
    'class' name '=' ((superclassexpr '+' (contextelem+)) | superclassexpr | (contextelem+)) \\
      'begin'?
    ;
    'instantiation' (nameref + 'and') '::' arity 'begin'
    ;
    'instance'
    ;
    'subclass' target? nameref
    ;
    'print\_classes'
    ;

    superclassexpr: nameref | (nameref '+' superclassexpr)
    ;
  \end{rail}

  \begin{description}

  \item @{command "class"}~@{text "c = superclasses + body"} defines
  a new class @{text c}, inheriting from @{text superclasses}.  This
  introduces a locale @{text c} with import of all locales @{text
  superclasses}.

  Any @{element "fixes"} in @{text body} are lifted to the global
  theory level (\emph{class operations} @{text "f\<^sub>1, \<dots>,
  f\<^sub>n"} of class @{text c}), mapping the local type parameter
  @{text \<alpha>} to a schematic type variable @{text "?\<alpha> :: c"}.

  Likewise, @{element "assumes"} in @{text body} are also lifted,
  mapping each local parameter @{text "f :: \<tau>[\<alpha>]"} to its
  corresponding global constant @{text "f :: \<tau>[?\<alpha> :: c]"}.  The
  corresponding introduction rule is provided as @{text
  c_class_axioms.intro}.  This rule should be rarely needed directly
  --- the @{method intro_classes} method takes care of the details of
  class membership proofs.

  \item @{command "instantiation"}~@{text "t :: (s\<^sub>1, \<dots>, s\<^sub>n) s
  \<BEGIN>"} opens a theory target (cf.\ \secref{sec:target}) which
  allows to specify class operations @{text "f\<^sub>1, \<dots>, f\<^sub>n"} corresponding
  to sort @{text s} at the particular type instance @{text "(\<alpha>\<^sub>1 :: s\<^sub>1,
  \<dots>, \<alpha>\<^sub>n :: s\<^sub>n) t"}.  A plain @{command "instance"} command in the
  target body poses a goal stating these type arities.  The target is
  concluded by an @{command_ref (local) "end"} command.

  Note that a list of simultaneous type constructors may be given;
  this corresponds nicely to mutual recursive type definitions, e.g.\
  in Isabelle/HOL.

  \item @{command "instance"} in an instantiation target body sets
  up a goal stating the type arities claimed at the opening @{command
  "instantiation"}.  The proof would usually proceed by @{method
  intro_classes}, and then establish the characteristic theorems of
  the type classes involved.  After finishing the proof, the
  background theory will be augmented by the proven type arities.

  \item @{command "subclass"}~@{text c} in a class context for class
  @{text d} sets up a goal stating that class @{text c} is logically
  contained in class @{text d}.  After finishing the proof, class
  @{text d} is proven to be subclass @{text c} and the locale @{text
  c} is interpreted into @{text d} simultaneously.

  \item @{command "print_classes"} prints all classes in the current
  theory.

  \item @{method intro_classes} repeatedly expands all class
  introduction rules of this theory.  Note that this method usually
  needs not be named explicitly, as it is already included in the
  default proof step (e.g.\ of @{command "proof"}).  In particular,
  instantiation of trivial (syntactic) classes may be performed by a
  single ``@{command ".."}'' proof step.

  \end{description}
*}


subsection {* The class target *}

text {*
  %FIXME check

  A named context may refer to a locale (cf.\ \secref{sec:target}).
  If this locale is also a class @{text c}, apart from the common
  locale target behaviour the following happens.

  \begin{itemize}

  \item Local constant declarations @{text "g[\<alpha>]"} referring to the
  local type parameter @{text \<alpha>} and local parameters @{text "f[\<alpha>]"}
  are accompanied by theory-level constants @{text "g[?\<alpha> :: c]"}
  referring to theory-level class operations @{text "f[?\<alpha> :: c]"}.

  \item Local theorem bindings are lifted as are assumptions.

  \item Local syntax refers to local operations @{text "g[\<alpha>]"} and
  global operations @{text "g[?\<alpha> :: c]"} uniformly.  Type inference
  resolves ambiguities.  In rare cases, manual type annotations are
  needed.
  
  \end{itemize}
*}


subsection {* Old-style axiomatic type classes \label{sec:axclass} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "axclass"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "instance"} & : & @{text "theory \<rightarrow> proof(prove)"} \\
  \end{matharray}

  Axiomatic type classes are Isabelle/Pure's primitive
  \emph{definitional} interface to type classes.  For practical
  applications, you should consider using classes
  (cf.~\secref{sec:classes}) which provide high level interface.

  \begin{rail}
    'axclass' classdecl (axmdecl prop +)
    ;
    'instance' (nameref ('<' | subseteq) nameref | nameref '::' arity)
    ;
  \end{rail}

  \begin{description}
  
  \item @{command "axclass"}~@{text "c \<subseteq> c\<^sub>1, \<dots>, c\<^sub>n axms"} defines an
  axiomatic type class as the intersection of existing classes, with
  additional axioms holding.  Class axioms may not contain more than
  one type variable.  The class axioms (with implicit sort constraints
  added) are bound to the given names.  Furthermore a class
  introduction rule is generated (being bound as @{text
  c_class.intro}); this rule is employed by method @{method
  intro_classes} to support instantiation proofs of this class.
  
  The ``class axioms'' are stored as theorems according to the given
  name specifications, adding @{text "c_class"} as name space prefix;
  the same facts are also stored collectively as @{text
  c_class.axioms}.
  
  \item @{command "instance"}~@{text "c\<^sub>1 \<subseteq> c\<^sub>2"} and @{command
  "instance"}~@{text "t :: (s\<^sub>1, \<dots>, s\<^sub>n) s"} setup a goal stating a
  class relation or type arity.  The proof would usually proceed by
  @{method intro_classes}, and then establish the characteristic
  theorems of the type classes involved.  After finishing the proof,
  the theory will be augmented by a type signature declaration
  corresponding to the resulting theorem.

  \end{description}
*}


section {* Unrestricted overloading *}

text {*
  Isabelle/Pure's definitional schemes support certain forms of
  overloading (see \secref{sec:consts}).  At most occassions
  overloading will be used in a Haskell-like fashion together with
  type classes by means of @{command "instantiation"} (see
  \secref{sec:class}).  Sometimes low-level overloading is desirable.
  The @{command "overloading"} target provides a convenient view for
  end-users.

  \begin{matharray}{rcl}
    @{command_def "overloading"} & : & @{text "theory \<rightarrow> local_theory"} \\
  \end{matharray}

  \begin{rail}
    'overloading' \\
    ( string ( '==' | equiv ) term ( '(' 'unchecked' ')' )? + ) 'begin'
  \end{rail}

  \begin{description}

  \item @{command "overloading"}~@{text "x\<^sub>1 \<equiv> c\<^sub>1 :: \<tau>\<^sub>1 \<AND> \<dots> x\<^sub>n \<equiv> c\<^sub>n :: \<tau>\<^sub>n \<BEGIN>"}
  opens a theory target (cf.\ \secref{sec:target}) which allows to
  specify constants with overloaded definitions.  These are identified
  by an explicitly given mapping from variable names @{text "x\<^sub>i"} to
  constants @{text "c\<^sub>i"} at particular type instances.  The
  definitions themselves are established using common specification
  tools, using the names @{text "x\<^sub>i"} as reference to the
  corresponding constants.  The target is concluded by @{command
  (local) "end"}.

  A @{text "(unchecked)"} option disables global dependency checks for
  the corresponding definition, which is occasionally useful for
  exotic overloading.  It is at the discretion of the user to avoid
  malformed theory specifications!

  \end{description}
*}


section {* Incorporating ML code \label{sec:ML} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "use"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "ML"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "ML_prf"} & : & @{text "proof \<rightarrow> proof"} \\
    @{command_def "ML_val"} & : & @{text "any \<rightarrow>"} \\
    @{command_def "ML_command"} & : & @{text "any \<rightarrow>"} \\
    @{command_def "setup"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  \begin{mldecls}
    @{index_ML bind_thms: "string * thm list -> unit"} \\
    @{index_ML bind_thm: "string * thm -> unit"} \\
  \end{mldecls}

  \begin{rail}
    'use' name
    ;
    ('ML' | 'ML\_prf' | 'ML\_val' | 'ML\_command' | 'setup') text
    ;
  \end{rail}

  \begin{description}

  \item @{command "use"}~@{text "file"} reads and executes ML
  commands from @{text "file"}.  The current theory context is passed
  down to the ML toplevel and may be modified, using @{ML [source=false]
  "Context.>>"} or derived ML commands.  The file name is checked with
  the @{keyword_ref "uses"} dependency declaration given in the theory
  header (see also \secref{sec:begin-thy}).

  Top-level ML bindings are stored within the (global or local) theory
  context.
  
  \item @{command "ML"}~@{text "text"} is similar to @{command "use"},
  but executes ML commands directly from the given @{text "text"}.
  Top-level ML bindings are stored within the (global or local) theory
  context.

  \item @{command "ML_prf"} is analogous to @{command "ML"} but works
  within a proof context.

  Top-level ML bindings are stored within the proof context in a
  purely sequential fashion, disregarding the nested proof structure.
  ML bindings introduced by @{command "ML_prf"} are discarded at the
  end of the proof.

  \item @{command "ML_val"} and @{command "ML_command"} are diagnostic
  versions of @{command "ML"}, which means that the context may not be
  updated.  @{command "ML_val"} echos the bindings produced at the ML
  toplevel, but @{command "ML_command"} is silent.
  
  \item @{command "setup"}~@{text "text"} changes the current theory
  context by applying @{text "text"}, which refers to an ML expression
  of type @{ML_type [source=false] "theory -> theory"}.  This enables
  to initialize any object-logic specific tools and packages written
  in ML, for example.

  \item @{ML bind_thms}~@{text "(name, thms)"} stores a list of
  theorems produced in ML both in the theory context and the ML
  toplevel, associating it with the provided name.  Theorems are put
  into a global ``standard'' format before being stored.

  \item @{ML bind_thm} is similar to @{ML bind_thms} but refers to a
  singleton theorem.
  
  \end{description}
*}


section {* Primitive specification elements *}

subsection {* Type classes and sorts \label{sec:classes} *}

text {*
  \begin{matharray}{rcll}
    @{command_def "classes"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "classrel"} & : & @{text "theory \<rightarrow> theory"} & (axiomatic!) \\
    @{command_def "defaultsort"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "class_deps"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
  \end{matharray}

  \begin{rail}
    'classes' (classdecl +)
    ;
    'classrel' (nameref ('<' | subseteq) nameref + 'and')
    ;
    'defaultsort' sort
    ;
  \end{rail}

  \begin{description}

  \item @{command "classes"}~@{text "c \<subseteq> c\<^sub>1, \<dots>, c\<^sub>n"} declares class
  @{text c} to be a subclass of existing classes @{text "c\<^sub>1, \<dots>, c\<^sub>n"}.
  Cyclic class structures are not permitted.

  \item @{command "classrel"}~@{text "c\<^sub>1 \<subseteq> c\<^sub>2"} states subclass
  relations between existing classes @{text "c\<^sub>1"} and @{text "c\<^sub>2"}.
  This is done axiomatically!  The @{command_ref "instance"} command
  (see \secref{sec:axclass}) provides a way to introduce proven class
  relations.

  \item @{command "defaultsort"}~@{text s} makes sort @{text s} the
  new default sort for any type variables given without sort
  constraints.  Usually, the default sort would be only changed when
  defining a new object-logic.

  \item @{command "class_deps"} visualizes the subclass relation,
  using Isabelle's graph browser tool (see also \cite{isabelle-sys}).

  \end{description}
*}


subsection {* Types and type abbreviations \label{sec:types-pure} *}

text {*
  \begin{matharray}{rcll}
    @{command_def "types"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "typedecl"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "nonterminals"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "arities"} & : & @{text "theory \<rightarrow> theory"} & (axiomatic!) \\
  \end{matharray}

  \begin{rail}
    'types' (typespec '=' type infix? +)
    ;
    'typedecl' typespec infix?
    ;
    'nonterminals' (name +)
    ;
    'arities' (nameref '::' arity +)
    ;
  \end{rail}

  \begin{description}

  \item @{command "types"}~@{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t = \<tau>"} introduces
  \emph{type synonym} @{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t"} for existing type @{text
  "\<tau>"}.  Unlike actual type definitions, as are available in
  Isabelle/HOL for example, type synonyms are just purely syntactic
  abbreviations without any logical significance.  Internally, type
  synonyms are fully expanded.
  
  \item @{command "typedecl"}~@{text "(\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n) t"} declares a new
  type constructor @{text t}, intended as an actual logical type (of
  the object-logic, if available).

  \item @{command "nonterminals"}~@{text c} declares type constructors
  @{text c} (without arguments) to act as purely syntactic types,
  i.e.\ nonterminal symbols of Isabelle's inner syntax of terms or
  types.

  \item @{command "arities"}~@{text "t :: (s\<^sub>1, \<dots>, s\<^sub>n) s"} augments
  Isabelle's order-sorted signature of types by new type constructor
  arities.  This is done axiomatically!  The @{command_ref "instance"}
  command (see \S\ref{sec:axclass}) provides a way to introduce proven
  type arities.

  \end{description}
*}


subsection {* Constants and definitions \label{sec:consts} *}

text {*
  Definitions essentially express abbreviations within the logic.  The
  simplest form of a definition is @{text "c :: \<sigma> \<equiv> t"}, where @{text
  c} is a newly declared constant.  Isabelle also allows derived forms
  where the arguments of @{text c} appear on the left, abbreviating a
  prefix of @{text \<lambda>}-abstractions, e.g.\ @{text "c \<equiv> \<lambda>x y. t"} may be
  written more conveniently as @{text "c x y \<equiv> t"}.  Moreover,
  definitions may be weakened by adding arbitrary pre-conditions:
  @{text "A \<Longrightarrow> c x y \<equiv> t"}.

  \medskip The built-in well-formedness conditions for definitional
  specifications are:

  \begin{itemize}

  \item Arguments (on the left-hand side) must be distinct variables.

  \item All variables on the right-hand side must also appear on the
  left-hand side.

  \item All type variables on the right-hand side must also appear on
  the left-hand side; this prohibits @{text "0 :: nat \<equiv> length ([] ::
  \<alpha> list)"} for example.

  \item The definition must not be recursive.  Most object-logics
  provide definitional principles that can be used to express
  recursion safely.

  \end{itemize}

  Overloading means that a constant being declared as @{text "c :: \<alpha>
  decl"} may be defined separately on type instances @{text "c ::
  (\<beta>\<^sub>1, \<dots>, \<beta>\<^sub>n) t decl"} for each type constructor @{text
  t}.  The right-hand side may mention overloaded constants
  recursively at type instances corresponding to the immediate
  argument types @{text "\<beta>\<^sub>1, \<dots>, \<beta>\<^sub>n"}.  Incomplete
  specification patterns impose global constraints on all occurrences,
  e.g.\ @{text "d :: \<alpha> \<times> \<alpha>"} on the left-hand side means that all
  corresponding occurrences on some right-hand side need to be an
  instance of this, general @{text "d :: \<alpha> \<times> \<beta>"} will be disallowed.

  \begin{matharray}{rcl}
    @{command_def "consts"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "defs"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "constdefs"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  \begin{rail}
    'consts' ((name '::' type mixfix?) +)
    ;
    'defs' ('(' 'unchecked'? 'overloaded'? ')')? \\ (axmdecl prop +)
    ;
  \end{rail}

  \begin{rail}
    'constdefs' structs? (constdecl? constdef +)
    ;

    structs: '(' 'structure' (vars + 'and') ')'
    ;
    constdecl:  ((name '::' type mixfix | name '::' type | name mixfix) 'where'?) | name 'where'
    ;
    constdef: thmdecl? prop
    ;
  \end{rail}

  \begin{description}

  \item @{command "consts"}~@{text "c :: \<sigma>"} declares constant @{text
  c} to have any instance of type scheme @{text \<sigma>}.  The optional
  mixfix annotations may attach concrete syntax to the constants
  declared.
  
  \item @{command "defs"}~@{text "name: eqn"} introduces @{text eqn}
  as a definitional axiom for some existing constant.
  
  The @{text "(unchecked)"} option disables global dependency checks
  for this definition, which is occasionally useful for exotic
  overloading.  It is at the discretion of the user to avoid malformed
  theory specifications!
  
  The @{text "(overloaded)"} option declares definitions to be
  potentially overloaded.  Unless this option is given, a warning
  message would be issued for any definitional equation with a more
  special type than that of the corresponding constant declaration.
  
  \item @{command "constdefs"} provides a streamlined combination of
  constants declarations and definitions: type-inference takes care of
  the most general typing of the given specification (the optional
  type constraint may refer to type-inference dummies ``@{text _}'' as
  usual).  The resulting type declaration needs to agree with that of
  the specification; overloading is \emph{not} supported here!
  
  The constant name may be omitted altogether, if neither type nor
  syntax declarations are given.  The canonical name of the
  definitional axiom for constant @{text c} will be @{text c_def},
  unless specified otherwise.  Also note that the given list of
  specifications is processed in a strictly sequential manner, with
  type-checking being performed independently.
  
  An optional initial context of @{text "(structure)"} declarations
  admits use of indexed syntax, using the special symbol @{verbatim
  "\<index>"} (printed as ``@{text "\<index>"}'').  The latter concept is
  particularly useful with locales (see also \S\ref{sec:locale}).

  \end{description}
*}


section {* Axioms and theorems \label{sec:axms-thms} *}

text {*
  \begin{matharray}{rcll}
    @{command_def "axioms"} & : & @{text "theory \<rightarrow> theory"} & (axiomatic!) \\
    @{command_def "lemmas"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
    @{command_def "theorems"} & : & @{text "local_theory \<rightarrow> local_theory"} \\
  \end{matharray}

  \begin{rail}
    'axioms' (axmdecl prop +)
    ;
    ('lemmas' | 'theorems') target? (thmdef? thmrefs + 'and')
    ;
  \end{rail}

  \begin{description}
  
  \item @{command "axioms"}~@{text "a: \<phi>"} introduces arbitrary
  statements as axioms of the meta-logic.  In fact, axioms are
  ``axiomatic theorems'', and may be referred later just as any other
  theorem.
  
  Axioms are usually only introduced when declaring new logical
  systems.  Everyday work is typically done the hard way, with proper
  definitions and proven theorems.
  
  \item @{command "lemmas"}~@{text "a = b\<^sub>1 \<dots> b\<^sub>n"} retrieves and stores
  existing facts in the theory context, or the specified target
  context (see also \secref{sec:target}).  Typical applications would
  also involve attributes, to declare Simplifier rules, for example.
  
  \item @{command "theorems"} is essentially the same as @{command
  "lemmas"}, but marks the result as a different kind of facts.

  \end{description}
*}


section {* Oracles *}

text {* Oracles allow Isabelle to take advantage of external reasoners
  such as arithmetic decision procedures, model checkers, fast
  tautology checkers or computer algebra systems.  Invoked as an
  oracle, an external reasoner can create arbitrary Isabelle theorems.

  It is the responsibility of the user to ensure that the external
  reasoner is as trustworthy as the application requires.  Another
  typical source of errors is the linkup between Isabelle and the
  external tool, not just its concrete implementation, but also the
  required translation between two different logical environments.

  Isabelle merely guarantees well-formedness of the propositions being
  asserted, and records within the internal derivation object how
  presumed theorems depend on unproven suppositions.

  \begin{matharray}{rcl}
    @{command_def "oracle"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  \begin{rail}
    'oracle' name '=' text
    ;
  \end{rail}

  \begin{description}

  \item @{command "oracle"}~@{text "name = text"} turns the given ML
  expression @{text "text"} of type @{ML_text "'a -> cterm"} into an
  ML function of type @{ML_text "'a -> thm"}, which is bound to the
  global identifier @{ML_text name}.  This acts like an infinitary
  specification of axioms!  Invoking the oracle only works within the
  scope of the resulting theory.

  \end{description}

  See @{"file" "~~/src/FOL/ex/IffOracle.thy"} for a worked example of
  defining a new primitive rule as oracle, and turning it into a proof
  method.
*}


section {* Name spaces *}

text {*
  \begin{matharray}{rcl}
    @{command_def "global"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "local"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "hide"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  \begin{rail}
    'hide' ('(open)')? name (nameref + )
    ;
  \end{rail}

  Isabelle organizes any kind of name declarations (of types,
  constants, theorems etc.) by separate hierarchically structured name
  spaces.  Normally the user does not have to control the behavior of
  name spaces by hand, yet the following commands provide some way to
  do so.

  \begin{description}

  \item @{command "global"} and @{command "local"} change the current
  name declaration mode.  Initially, theories start in @{command
  "local"} mode, causing all names to be automatically qualified by
  the theory name.  Changing this to @{command "global"} causes all
  names to be declared without the theory prefix, until @{command
  "local"} is declared again.
  
  Note that global names are prone to get hidden accidently later,
  when qualified names of the same base name are introduced.
  
  \item @{command "hide"}~@{text "space names"} fully removes
  declarations from a given name space (which may be @{text "class"},
  @{text "type"}, @{text "const"}, or @{text "fact"}); with the @{text
  "(open)"} option, only the base name is hidden.  Global
  (unqualified) names may never be hidden.
  
  Note that hiding name space accesses has no impact on logical
  declarations --- they remain valid internally.  Entities that are no
  longer accessible to the user are printed with the special qualifier
  ``@{text "??"}'' prefixed to the full internal name.

  \end{description}
*}


section {* Syntax and translations \label{sec:syn-trans} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "syntax"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "no_syntax"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "translations"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "no_translations"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  \begin{rail}
    ('syntax' | 'no\_syntax') mode? (constdecl +)
    ;
    ('translations' | 'no\_translations') (transpat ('==' | '=>' | '<=' | rightleftharpoons | rightharpoonup | leftharpoondown) transpat +)
    ;

    mode: ('(' ( name | 'output' | name 'output' ) ')')
    ;
    transpat: ('(' nameref ')')? string
    ;
  \end{rail}

  \begin{description}
  
  \item @{command "syntax"}~@{text "(mode) decls"} is similar to
  @{command "consts"}~@{text decls}, except that the actual logical
  signature extension is omitted.  Thus the context free grammar of
  Isabelle's inner syntax may be augmented in arbitrary ways,
  independently of the logic.  The @{text mode} argument refers to the
  print mode that the grammar rules belong; unless the @{keyword_ref
  "output"} indicator is given, all productions are added both to the
  input and output grammar.
  
  \item @{command "no_syntax"}~@{text "(mode) decls"} removes grammar
  declarations (and translations) resulting from @{text decls}, which
  are interpreted in the same manner as for @{command "syntax"} above.
  
  \item @{command "translations"}~@{text rules} specifies syntactic
  translation rules (i.e.\ macros): parse~/ print rules (@{text "\<rightleftharpoons>"}),
  parse rules (@{text "\<rightharpoonup>"}), or print rules (@{text "\<leftharpoondown>"}).
  Translation patterns may be prefixed by the syntactic category to be
  used for parsing; the default is @{text logic}.
  
  \item @{command "no_translations"}~@{text rules} removes syntactic
  translation rules, which are interpreted in the same manner as for
  @{command "translations"} above.

  \end{description}
*}


section {* Syntax translation functions *}

text {*
  \begin{matharray}{rcl}
    @{command_def "parse_ast_translation"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "parse_translation"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "print_translation"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "typed_print_translation"} & : & @{text "theory \<rightarrow> theory"} \\
    @{command_def "print_ast_translation"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  \begin{rail}
  ( 'parse\_ast\_translation' | 'parse\_translation' | 'print\_translation' |
    'typed\_print\_translation' | 'print\_ast\_translation' ) ('(advanced)')? text
  ;
  \end{rail}

  Syntax translation functions written in ML admit almost arbitrary
  manipulations of Isabelle's inner syntax.  Any of the above commands
  have a single \railqtok{text} argument that refers to an ML
  expression of appropriate type, which are as follows by default:

%FIXME proper antiquotations
\begin{ttbox}
val parse_ast_translation   : (string * (ast list -> ast)) list
val parse_translation       : (string * (term list -> term)) list
val print_translation       : (string * (term list -> term)) list
val typed_print_translation :
  (string * (bool -> typ -> term list -> term)) list
val print_ast_translation   : (string * (ast list -> ast)) list
\end{ttbox}

  If the @{text "(advanced)"} option is given, the corresponding
  translation functions may depend on the current theory or proof
  context.  This allows to implement advanced syntax mechanisms, as
  translations functions may refer to specific theory declarations or
  auxiliary proof data.

  See also \cite[\S8]{isabelle-ref} for more information on the
  general concept of syntax transformations in Isabelle.

%FIXME proper antiquotations
\begin{ttbox}
val parse_ast_translation:
  (string * (Proof.context -> ast list -> ast)) list
val parse_translation:
  (string * (Proof.context -> term list -> term)) list
val print_translation:
  (string * (Proof.context -> term list -> term)) list
val typed_print_translation:
  (string * (Proof.context -> bool -> typ -> term list -> term)) list
val print_ast_translation:
  (string * (Proof.context -> ast list -> ast)) list
\end{ttbox}
*}

end
