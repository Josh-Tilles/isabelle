header {* Plain HOL *}

theory Plain
imports Datatype FunDef Extraction Meson
begin

text {*
  Plain bootstrap of fundamental HOL tools and packages; does not
  include @{text Hilbert_Choice}.
*}

ML {* path_add "~~/src/HOL/Library" *}

end
