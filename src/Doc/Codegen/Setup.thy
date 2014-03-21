theory Setup
imports
  Complex_Main
  "~~/src/HOL/Library/Dlist"
  "~~/src/HOL/Library/RBT"
  "~~/src/HOL/Library/Mapping"
  "~~/src/HOL/Library/IArray"
begin

(* FIXME avoid writing into source directory *)
ML {*
  Isabelle_System.mkdirs (Path.append (Resources.master_directory @{theory}) (Path.basic "examples"))
*}

ML_file "../antiquote_setup.ML"
ML_file "../more_antiquote.ML"

setup {*
let
  val typ = Simple_Syntax.read_typ;
in
  Sign.del_modesyntax (Symbol.xsymbolsN, false)
   [("_constrain", typ "logic => type => logic", Mixfix ("_\<Colon>_", [4, 0], 3)),
    ("_constrain", typ "prop' => type => prop'", Mixfix ("_\<Colon>_", [4, 0], 3))] #>
  Sign.add_modesyntax (Symbol.xsymbolsN, false)
   [("_constrain", typ "logic => type => logic", Mixfix ("_ \<Colon>  _", [4, 0], 3)),
    ("_constrain", typ "prop' => type => prop'", Mixfix ("_ \<Colon> _", [4, 0], 3))]
end
*}

setup {* Code_Target.set_default_code_width 74 *}

declare [[names_unique = false]]

end

