(*  Title:      HOL/AxClasses/Product.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

theory Product imports Main begin

axclass product < type

consts
  product :: "'a::product => 'a => 'a"    (infixl "[*]" 70)


instance bool :: product
  by intro_classes

defs (overloaded)
  product_bool_def: "x [*] y == x & y"

end
