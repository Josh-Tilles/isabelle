(*  Title:      HOL/AxClasses/Semigroups.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

theory Semigroups imports Main begin

consts
  times :: "'a => 'a => 'a"    (infixl "[*]" 70)

axclass semigroup < type
  assoc: "(x [*] y) [*] z = x [*] (y [*] z)"


consts
  plus :: "'a => 'a => 'a"    (infixl "[+]" 70)

axclass plus_semigroup < type
  assoc: "(x [+] y) [+] z = x [+] (y [+] z)"

end
