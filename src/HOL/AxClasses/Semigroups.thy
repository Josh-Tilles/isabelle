(*  Title:      HOL/AxClasses/Semigroups.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

theory Semigroups = Main:

consts
  times :: "'a => 'a => 'a"    (infixl "[*]" 70)

axclass semigroup < "term"
  assoc: "(x [*] y) [*] z = x [*] (y [*] z)"


consts
  plus :: "'a => 'a => 'a"    (infixl "[+]" 70)

axclass plus_semigroup < "term"
  assoc: "(x [+] y) [+] z = x [+] (y [+] z)"

end
