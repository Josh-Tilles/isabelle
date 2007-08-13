;;
;; Keyword classification tables for Isabelle/Isar.
;; This file was generated by Isabelle/ZF -- DO NOT EDIT!
;;
;; $Id$
;;

(defconst isar-keywords-major
  '("\\."
    "\\.\\."
    "ML"
    "ML_command"
    "ML_setup"
    "ProofGeneral\\.inform_file_processed"
    "ProofGeneral\\.inform_file_retracted"
    "ProofGeneral\\.kill_proof"
    "ProofGeneral\\.process_pgip"
    "ProofGeneral\\.restart"
    "ProofGeneral\\.undo"
    "abbreviation"
    "also"
    "apply"
    "apply_end"
    "arities"
    "assume"
    "axclass"
    "axiomatization"
    "axioms"
    "back"
    "by"
    "cannot_undo"
    "case"
    "cd"
    "chapter"
    "class"
    "class_deps"
    "classes"
    "classrel"
    "codatatype"
    "code_abstype"
    "code_axioms"
    "code_class"
    "code_const"
    "code_datatype"
    "code_deps"
    "code_gen"
    "code_instance"
    "code_library"
    "code_module"
    "code_modulename"
    "code_moduleprolog"
    "code_monad"
    "code_reserved"
    "code_thms"
    "code_type"
    "coinductive"
    "commit"
    "constdefs"
    "consts"
    "consts_code"
    "context"
    "corollary"
    "datatype"
    "declaration"
    "declare"
    "def"
    "defaultsort"
    "defer"
    "definition"
    "defs"
    "disable_pr"
    "display_drafts"
    "done"
    "enable_pr"
    "end"
    "exit"
    "extract"
    "extract_type"
    "finalconsts"
    "finally"
    "find_theorems"
    "fix"
    "from"
    "full_prf"
    "global"
    "guess"
    "have"
    "header"
    "help"
    "hence"
    "hide"
    "inductive"
    "inductive_cases"
    "init_toplevel"
    "instance"
    "interpret"
    "interpretation"
    "invoke"
    "judgment"
    "kill"
    "kill_thy"
    "lemma"
    "lemmas"
    "let"
    "local"
    "locale"
    "method_setup"
    "moreover"
    "next"
    "no_syntax"
    "no_translations"
    "nonterminals"
    "notation"
    "note"
    "obtain"
    "oops"
    "oracle"
    "parse_ast_translation"
    "parse_translation"
    "pr"
    "prefer"
    "presume"
    "pretty_setmargin"
    "prf"
    "primrec"
    "print_abbrevs"
    "print_antiquotations"
    "print_ast_translation"
    "print_attributes"
    "print_binds"
    "print_cases"
    "print_claset"
    "print_classes"
    "print_codesetup"
    "print_commands"
    "print_configs"
    "print_context"
    "print_drafts"
    "print_facts"
    "print_induct_rules"
    "print_interps"
    "print_locale"
    "print_locales"
    "print_methods"
    "print_rules"
    "print_simpset"
    "print_statement"
    "print_syntax"
    "print_tcset"
    "print_theorems"
    "print_theory"
    "print_trans_rules"
    "print_translation"
    "proof"
    "prop"
    "pwd"
    "qed"
    "quickcheck"
    "quickcheck_params"
    "quit"
    "realizability"
    "realizers"
    "redo"
    "remove_thy"
    "rep_datatype"
    "sect"
    "section"
    "setup"
    "show"
    "simproc_setup"
    "sorry"
    "subsect"
    "subsection"
    "subsubsect"
    "subsubsection"
    "syntax"
    "term"
    "text"
    "text_raw"
    "then"
    "theorem"
    "theorems"
    "theory"
    "thm"
    "thm_deps"
    "thus"
    "thy_deps"
    "token_translation"
    "touch_all_thys"
    "touch_child_thys"
    "touch_thy"
    "translations"
    "txt"
    "txt_raw"
    "typ"
    "typed_print_translation"
    "typedecl"
    "types"
    "types_code"
    "ultimately"
    "undo"
    "undos_proof"
    "unfolding"
    "use"
    "use_thy"
    "using"
    "value"
    "welcome"
    "with"
    "{"
    "}"))

(defconst isar-keywords-minor
  '("advanced"
    "and"
    "assumes"
    "attach"
    "begin"
    "binder"
    "case_eqns"
    "con_defs"
    "concl"
    "constrains"
    "contains"
    "defines"
    "domains"
    "elimination"
    "file"
    "fixes"
    "for"
    "identifier"
    "if"
    "imports"
    "in"
    "includes"
    "induction"
    "infix"
    "infixl"
    "infixr"
    "intros"
    "is"
    "module_name"
    "monos"
    "notes"
    "obtains"
    "open"
    "output"
    "overloaded"
    "recursor_eqns"
    "shows"
    "structure"
    "type_elims"
    "type_intros"
    "unchecked"
    "uses"
    "where"))

(defconst isar-keywords-control
  '("ProofGeneral\\.inform_file_processed"
    "ProofGeneral\\.inform_file_retracted"
    "ProofGeneral\\.kill_proof"
    "ProofGeneral\\.process_pgip"
    "ProofGeneral\\.restart"
    "ProofGeneral\\.undo"
    "cannot_undo"
    "exit"
    "init_toplevel"
    "kill"
    "quit"
    "redo"
    "undo"
    "undos_proof"))

(defconst isar-keywords-diag
  '("ML"
    "ML_command"
    "cd"
    "class_deps"
    "code_deps"
    "code_gen"
    "code_thms"
    "commit"
    "disable_pr"
    "display_drafts"
    "enable_pr"
    "find_theorems"
    "full_prf"
    "header"
    "help"
    "kill_thy"
    "pr"
    "pretty_setmargin"
    "prf"
    "print_abbrevs"
    "print_antiquotations"
    "print_attributes"
    "print_binds"
    "print_cases"
    "print_claset"
    "print_classes"
    "print_codesetup"
    "print_commands"
    "print_configs"
    "print_context"
    "print_drafts"
    "print_facts"
    "print_induct_rules"
    "print_interps"
    "print_locale"
    "print_locales"
    "print_methods"
    "print_rules"
    "print_simpset"
    "print_statement"
    "print_syntax"
    "print_tcset"
    "print_theorems"
    "print_theory"
    "print_trans_rules"
    "prop"
    "pwd"
    "quickcheck"
    "remove_thy"
    "term"
    "thm"
    "thm_deps"
    "thy_deps"
    "touch_all_thys"
    "touch_child_thys"
    "touch_thy"
    "typ"
    "use"
    "use_thy"
    "value"
    "welcome"))

(defconst isar-keywords-theory-begin
  '("theory"))

(defconst isar-keywords-theory-switch
  '())

(defconst isar-keywords-theory-end
  '("end"))

(defconst isar-keywords-theory-heading
  '("chapter"
    "section"
    "subsection"
    "subsubsection"))

(defconst isar-keywords-theory-decl
  '("ML_setup"
    "abbreviation"
    "arities"
    "axclass"
    "axiomatization"
    "axioms"
    "class"
    "classes"
    "classrel"
    "codatatype"
    "code_abstype"
    "code_axioms"
    "code_class"
    "code_const"
    "code_datatype"
    "code_instance"
    "code_library"
    "code_module"
    "code_modulename"
    "code_moduleprolog"
    "code_monad"
    "code_reserved"
    "code_type"
    "coinductive"
    "constdefs"
    "consts"
    "consts_code"
    "context"
    "datatype"
    "declaration"
    "declare"
    "defaultsort"
    "definition"
    "defs"
    "extract"
    "extract_type"
    "finalconsts"
    "global"
    "hide"
    "inductive"
    "judgment"
    "lemmas"
    "local"
    "locale"
    "method_setup"
    "no_syntax"
    "no_translations"
    "nonterminals"
    "notation"
    "oracle"
    "parse_ast_translation"
    "parse_translation"
    "primrec"
    "print_ast_translation"
    "print_translation"
    "quickcheck_params"
    "realizability"
    "realizers"
    "rep_datatype"
    "setup"
    "simproc_setup"
    "syntax"
    "text"
    "text_raw"
    "theorems"
    "token_translation"
    "translations"
    "typed_print_translation"
    "typedecl"
    "types"
    "types_code"))

(defconst isar-keywords-theory-script
  '("inductive_cases"))

(defconst isar-keywords-theory-goal
  '("corollary"
    "instance"
    "interpretation"
    "lemma"
    "theorem"))

(defconst isar-keywords-qed
  '("\\."
    "\\.\\."
    "by"
    "done"
    "sorry"))

(defconst isar-keywords-qed-block
  '("qed"))

(defconst isar-keywords-qed-global
  '("oops"))

(defconst isar-keywords-proof-heading
  '("sect"
    "subsect"
    "subsubsect"))

(defconst isar-keywords-proof-goal
  '("have"
    "hence"
    "interpret"
    "invoke"))

(defconst isar-keywords-proof-block
  '("next"
    "proof"))

(defconst isar-keywords-proof-open
  '("{"))

(defconst isar-keywords-proof-close
  '("}"))

(defconst isar-keywords-proof-chain
  '("finally"
    "from"
    "then"
    "ultimately"
    "with"))

(defconst isar-keywords-proof-decl
  '("also"
    "let"
    "moreover"
    "note"
    "txt"
    "txt_raw"
    "unfolding"
    "using"))

(defconst isar-keywords-proof-asm
  '("assume"
    "case"
    "def"
    "fix"
    "presume"))

(defconst isar-keywords-proof-asm-goal
  '("guess"
    "obtain"
    "show"
    "thus"))

(defconst isar-keywords-proof-script
  '("apply"
    "apply_end"
    "back"
    "defer"
    "prefer"))

(provide 'isar-keywords)
