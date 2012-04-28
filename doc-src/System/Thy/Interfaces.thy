theory Interfaces
imports Base
begin

chapter {* User interfaces *}

section {* Plain TTY interaction \label{sec:tool-tty} *}

text {*
  The @{tool_def tty} tool runs the Isabelle process interactively
  within a plain terminal session:
\begin{ttbox}
Usage: tty [OPTIONS]

  Options are:
    -l NAME      logic image name (default ISABELLE_LOGIC)
    -m MODE      add print mode for output
    -p NAME      line editor program name (default ISABELLE_LINE_EDITOR)

  Run Isabelle process with plain tty interaction, and optional line editor.
\end{ttbox}

  The @{verbatim "-l"} option specifies the logic image.  The
  @{verbatim "-m"} option specifies additional print modes.  The
  @{verbatim "-p"} option specifies an alternative line editor (such
  as the @{executable_def rlwrap} wrapper for GNU readline); the
  fall-back is to use raw standard input.

  Regular interaction is via the standard Isabelle/Isar toplevel loop.
  The Isar command @{command exit} drops out into the raw ML system,
  which is occasionally useful for low-level debugging.  Invoking @{ML
  Isar.loop}~@{verbatim "();"} in ML will return to the Isar toplevel.
*}


section {* Proof General / Emacs *}

text {*
  The @{tool_def emacs} tool invokes a version of Emacs and Proof
  General within the regular Isabelle settings environment
  (\secref{sec:settings}).  This is more robust than starting Emacs
  separately, loading the Proof General lisp files, and then
  attempting to start Isabelle with dynamic @{setting PATH} lookup
  etc.

  The actual interface script is part of the Proof General
  distribution~\cite{proofgeneral}; its usage depends on the
  particular version.  There are some options available, such as
  @{verbatim "-l"} for passing the logic image to be used by default,
  or @{verbatim "-m"} to tune the standard print mode.  The following
  Isabelle settings are particularly important for Proof General:

  \begin{description}

  \item[@{setting_def PROOFGENERAL_HOME}] points to the main
  installation directory of the Proof General distribution.  The
  default settings try to locate this in a number of standard places,
  notably @{verbatim "$ISABELLE_HOME/contrib/ProofGeneral"}.

  \item[@{setting_def PROOFGENERAL_OPTIONS}] is implicitly prefixed to
  the command line of any invocation of the Proof General @{verbatim
  interface} script.

  \item[@{setting_def XSYMBOL_INSTALLFONTS}] may contain a small shell
  script to install the X11 fonts required for the old X-Symbols mode
  of Proof General.  This is only relevant if the X11 display server
  runs on a different machine than the Emacs application, with a
  different file-system view on the Proof General installation.  Under
  most circumstances Proof General 3.x is able to refer to the font
  files that are part of its distribution, and Proof General 4.x finds
  its fonts by different means.

  \end{description}
*}


section {* Isabelle/jEdit Prover IDE \label{sec:tool-jedit} *}

text {* The @{tool_def jedit} tool invokes a version of jEdit that has
  been augmented with some components to provide a fully-featured
  Prover IDE (based on Isabelle/Scala):
\begin{ttbox}
Usage: isabelle jedit [OPTIONS] [FILES ...]

  Options are:
    -J OPTION    add JVM runtime option (default JEDIT_JAVA_OPTIONS)
    -b           build only
    -d           enable debugger
    -f           fresh build
    -j OPTION    add jEdit runtime option (default JEDIT_OPTIONS)
    -l NAME      logic image name (default ISABELLE_LOGIC)
    -m MODE      add print mode for output

Start jEdit with Isabelle plugin setup and opens theory FILES
(default Scratch.thy).
\end{ttbox}

The @{verbatim "-l"} option specifies the logic image.  The
@{verbatim "-m"} option specifies additional print modes.

The @{verbatim "-J"} and @{verbatim "-j"} options allow to pass
additional low-level options to the JVM or jEdit, respectively.  The
defaults are provided by the Isabelle settings environment.

The @{verbatim "-d"} option allows to connect to the runtime debugger
of the JVM.  Note that the Scala Console of Isabelle/jEdit is more
convenient in most practical situations.

The @{verbatim "-b"} and @{verbatim "-f"} options control the
self-build mechanism of Isabelle/jEdit.  This is only relevant for
building from sources, which also requires an auxiliary @{verbatim
jedit_build} component.  Official Isabelle releases already include a
version of Isabelle/jEdit that is built properly.
*}

end