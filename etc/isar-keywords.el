;;
;; Keyword classification tables for Isabelle/Isar.
;; Generated from Pure + HOL + HOLCF + HOL-Boogie + HOL-Nominal + HOL-Statespace.
;; *** DO NOT EDIT *** DO NOT EDIT *** DO NOT EDIT ***
;;

(defconst isar-keywords-major
  '("\\."
    "\\.\\."
    "Isabelle\\.command"
    "ML"
    "ML_command"
    "ML_prf"
    "ML_val"
    "ProofGeneral\\.inform_file_processed"
    "ProofGeneral\\.inform_file_retracted"
    "ProofGeneral\\.kill_proof"
    "ProofGeneral\\.pr"
    "ProofGeneral\\.process_pgip"
    "ProofGeneral\\.restart"
    "ProofGeneral\\.undo"
    "abbreviation"
    "also"
    "apply"
    "apply_end"
    "arities"
    "assume"
    "atom_decl"
    "attribute_setup"
    "ax_specification"
    "axiomatization"
    "axioms"
    "back"
    "boogie_end"
    "boogie_open"
    "boogie_status"
    "boogie_vc"
    "by"
    "cannot_undo"
    "case"
    "cd"
    "chapter"
    "class"
    "class_deps"
    "classes"
    "classrel"
    "code_abort"
    "code_class"
    "code_const"
    "code_datatype"
    "code_deps"
    "code_include"
    "code_instance"
    "code_library"
    "code_module"
    "code_modulename"
    "code_monad"
    "code_pred"
    "code_reflect"
    "code_reserved"
    "code_thms"
    "code_type"
    "coinductive"
    "coinductive_set"
    "commit"
    "consts"
    "consts_code"
    "context"
    "corollary"
    "cpodef"
    "datatype"
    "declaration"
    "declare"
    "def"
    "default_sort"
    "defer"
    "defer_recdef"
    "definition"
    "defs"
    "disable_pr"
    "display_drafts"
    "domain"
    "domain_isomorphism"
    "done"
    "enable_pr"
    "end"
    "equivariance"
    "example_proof"
    "exit"
    "export_code"
    "extract"
    "extract_type"
    "finalconsts"
    "finally"
    "find_consts"
    "find_theorems"
    "fix"
    "fixrec"
    "from"
    "full_prf"
    "fun"
    "function"
    "guess"
    "have"
    "header"
    "help"
    "hence"
    "hide_class"
    "hide_const"
    "hide_fact"
    "hide_type"
    "inductive"
    "inductive_cases"
    "inductive_set"
    "inductive_simps"
    "init_toplevel"
    "instance"
    "instantiation"
    "interpret"
    "interpretation"
    "judgment"
    "kill"
    "kill_thy"
    "lemma"
    "lemmas"
    "let"
    "linear_undo"
    "local_setup"
    "locale"
    "method_setup"
    "moreover"
    "next"
    "nitpick"
    "nitpick_params"
    "no_notation"
    "no_syntax"
    "no_translations"
    "no_type_notation"
    "nominal_datatype"
    "nominal_inductive"
    "nominal_inductive2"
    "nominal_primrec"
    "nonterminals"
    "notation"
    "note"
    "obtain"
    "oops"
    "oracle"
    "overloading"
    "parse_ast_translation"
    "parse_translation"
    "partial_function"
    "pcpodef"
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
    "print_codeproc"
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
    "print_orders"
    "print_quotconsts"
    "print_quotients"
    "print_quotmaps"
    "print_rules"
    "print_simpset"
    "print_statement"
    "print_syntax"
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
    "quotient_definition"
    "quotient_type"
    "realizability"
    "realizers"
    "recdef"
    "recdef_tc"
    "record"
    "refute"
    "refute_params"
    "remove_thy"
    "rep_datatype"
    "repdef"
    "schematic_corollary"
    "schematic_lemma"
    "schematic_theorem"
    "sect"
    "section"
    "setup"
    "show"
    "simproc_setup"
    "sledgehammer"
    "sledgehammer_params"
    "smt_status"
    "solve_direct"
    "sorry"
    "specification"
    "statespace"
    "subclass"
    "sublocale"
    "subsect"
    "subsection"
    "subsubsect"
    "subsubsection"
    "syntax"
    "term"
    "termination"
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
    "translations"
    "try"
    "txt"
    "txt_raw"
    "typ"
    "type_notation"
    "typed_print_translation"
    "typedecl"
    "typedef"
    "types"
    "types_code"
    "ultimately"
    "undo"
    "undos_proof"
    "unfolding"
    "unused_thms"
    "use"
    "use_thy"
    "using"
    "value"
    "values"
    "welcome"
    "with"
    "write"
    "{"
    "}"))

(defconst isar-keywords-minor
  '("advanced"
    "and"
    "assumes"
    "attach"
    "avoids"
    "begin"
    "binder"
    "checking"
    "congs"
    "constrains"
    "contains"
    "datatypes"
    "defines"
    "file"
    "fixes"
    "for"
    "functions"
    "hints"
    "identifier"
    "if"
    "imports"
    "in"
    "infix"
    "infixl"
    "infixr"
    "is"
    "lazy"
    "module_name"
    "monos"
    "morphisms"
    "notes"
    "obtains"
    "open"
    "output"
    "overloaded"
    "permissive"
    "pervasive"
    "shows"
    "structure"
    "unchecked"
    "unsafe"
    "uses"
    "where"))

(defconst isar-keywords-control
  '("Isabelle\\.command"
    "ProofGeneral\\.inform_file_processed"
    "ProofGeneral\\.inform_file_retracted"
    "ProofGeneral\\.kill_proof"
    "ProofGeneral\\.process_pgip"
    "ProofGeneral\\.restart"
    "ProofGeneral\\.undo"
    "cannot_undo"
    "disable_pr"
    "enable_pr"
    "exit"
    "init_toplevel"
    "kill"
    "kill_thy"
    "linear_undo"
    "quit"
    "remove_thy"
    "undo"
    "undos_proof"
    "use_thy"))

(defconst isar-keywords-diag
  '("ML_command"
    "ML_val"
    "ProofGeneral\\.pr"
    "boogie_status"
    "cd"
    "class_deps"
    "code_deps"
    "code_thms"
    "commit"
    "display_drafts"
    "export_code"
    "find_consts"
    "find_theorems"
    "full_prf"
    "header"
    "help"
    "nitpick"
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
    "print_codeproc"
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
    "print_orders"
    "print_quotconsts"
    "print_quotients"
    "print_quotmaps"
    "print_rules"
    "print_simpset"
    "print_statement"
    "print_syntax"
    "print_theorems"
    "print_theory"
    "print_trans_rules"
    "prop"
    "pwd"
    "quickcheck"
    "refute"
    "sledgehammer"
    "smt_status"
    "solve_direct"
    "term"
    "thm"
    "thm_deps"
    "thy_deps"
    "try"
    "typ"
    "unused_thms"
    "value"
    "values"
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
  '("ML"
    "abbreviation"
    "arities"
    "atom_decl"
    "attribute_setup"
    "axiomatization"
    "axioms"
    "boogie_end"
    "boogie_open"
    "class"
    "classes"
    "classrel"
    "code_abort"
    "code_class"
    "code_const"
    "code_datatype"
    "code_include"
    "code_instance"
    "code_library"
    "code_module"
    "code_modulename"
    "code_monad"
    "code_reflect"
    "code_reserved"
    "code_type"
    "coinductive"
    "coinductive_set"
    "consts"
    "consts_code"
    "context"
    "datatype"
    "declaration"
    "declare"
    "default_sort"
    "defer_recdef"
    "definition"
    "defs"
    "domain"
    "domain_isomorphism"
    "equivariance"
    "extract"
    "extract_type"
    "finalconsts"
    "fixrec"
    "fun"
    "hide_class"
    "hide_const"
    "hide_fact"
    "hide_type"
    "inductive"
    "inductive_set"
    "instantiation"
    "judgment"
    "lemmas"
    "local_setup"
    "locale"
    "method_setup"
    "nitpick_params"
    "no_notation"
    "no_syntax"
    "no_translations"
    "no_type_notation"
    "nominal_datatype"
    "nonterminals"
    "notation"
    "oracle"
    "overloading"
    "parse_ast_translation"
    "parse_translation"
    "partial_function"
    "primrec"
    "print_ast_translation"
    "print_translation"
    "quickcheck_params"
    "quotient_definition"
    "realizability"
    "realizers"
    "recdef"
    "record"
    "refute_params"
    "repdef"
    "setup"
    "simproc_setup"
    "sledgehammer_params"
    "statespace"
    "syntax"
    "text"
    "text_raw"
    "theorems"
    "translations"
    "type_notation"
    "typed_print_translation"
    "typedecl"
    "types"
    "types_code"
    "use"))

(defconst isar-keywords-theory-script
  '("inductive_cases"
    "inductive_simps"))

(defconst isar-keywords-theory-goal
  '("ax_specification"
    "boogie_vc"
    "code_pred"
    "corollary"
    "cpodef"
    "example_proof"
    "function"
    "instance"
    "interpretation"
    "lemma"
    "nominal_inductive"
    "nominal_inductive2"
    "nominal_primrec"
    "pcpodef"
    "quotient_type"
    "recdef_tc"
    "rep_datatype"
    "schematic_corollary"
    "schematic_lemma"
    "schematic_theorem"
    "specification"
    "subclass"
    "sublocale"
    "termination"
    "theorem"
    "typedef"))

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
    "interpret"))

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
  '("ML_prf"
    "also"
    "let"
    "moreover"
    "note"
    "txt"
    "txt_raw"
    "unfolding"
    "using"
    "write"))

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
