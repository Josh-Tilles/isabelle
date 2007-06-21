(*
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen
*)

header {* Examples for Ferrante and Rackoff's quantifier elimination procedure *}

theory Dense_Linear_Order_Ex
imports Main
begin

lemma
  "\<exists>(y::'a::{ordered_field,recpower,number_ring, division_by_zero}) <2. x + 3* y < 0 \<and> x - y >0"
  by dlo

lemma "~ (ALL x (y::'a::{ordered_field,recpower,number_ring, division_by_zero}). x < y --> 10*x < 11*y)"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y. x < y --> (10*(x + 5*y + -1) < 60*y)"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y. x ~= y --> x < y"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y. (x ~= y & 10*x ~= 9*y & 10*x < y) --> x < y"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y. (x ~= y & 5*x <= y) --> 500*x <= 100*y"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}). (EX (y::'a::{ordered_field,recpower,number_ring, division_by_zero}). 4*x + 3*y <= 0 & 4*x + 3*y >= -1)"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) < 0. (EX (y::'a::{ordered_field,recpower,number_ring, division_by_zero}) > 0. 7*x + y > 0 & x - y <= 9)"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero}). (0 < x & x < 1) --> (ALL y > 1. x + y ~= 1)"
  by dlo

lemma "EX x. (ALL (y::'a::{ordered_field,recpower,number_ring, division_by_zero}). y < 2 -->  2*(y - x) \<le> 0 )"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}). x < 10 | x > 20 | (EX y. y>= 0 & y <= 10 & x+y = 20)"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y z. x + y < z --> y >= z --> x < 0"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y z. x + 7*y < 5* z & 5*y >= 7*z & x < 0"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y z. abs (x + y) <= z --> (abs z = z)"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y z. x + 7*y - 5* z < 0 & 5*y + 7*z + 3*x < 0"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y z. (abs (5*x+3*y+z) <= 5*x+3*y+z & abs (5*x+3*y+z) >= - (5*x+3*y+z)) | (abs (5*x+3*y+z) >= 5*x+3*y+z & abs (5*x+3*y+z) <= - (5*x+3*y+z))"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y. x < y --> (EX z>0. x+z = y)"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y. x < y --> (EX z>0. x+z = y)"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y. (EX z>0. abs (x - y) <= z )"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y. (ALL z<0. (z < x --> z <= y) & (z > y --> z >= x))"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y. (ALL z>=0. abs (3*x+7*y) <= 2*z + 1)"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y. (ALL z<0. (z < x --> z <= y) & (z > y --> z >= x))"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero})>0. (ALL y. (EX z. 13* abs z \<noteq> abs (12*y - x) & 5*x - 3*(abs y) <= 7*z))"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero}). abs (4*x + 17) < 4 & (ALL y . abs (x*34 - 34*y - 9) \<noteq> 0 \<longrightarrow> (EX z. 5*x - 3*abs y <= 7*z))"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}). (EX y > abs (23*x - 9). (ALL z > abs (3*y - 19* abs x). x+z > 2*y))"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}). (EX y< abs (3*x - 1). (ALL z >= (3*abs x - 1). abs (12*x - 13*y + 19*z) > abs (23*x) ))"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero}). abs x < 100 & (ALL y > x. (EX z<2*y - x. 5*x - 3*y <= 7*z))"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y z w. 7*x<3*y --> 5*y < 7*z --> z < 2*w --> 7*(2*w-x) > 2*y"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y z w. 5*x + 3*z - 17*w + abs (y - 8*x + z) <= 89"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y z w. 5*x + 3*z - 17*w + 7* (y - 8*x + z) <= max y (7*z - x + w)"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y z w. min (5*x + 3*z) (17*w) + 5* abs (y - 8*x + z) <= max y (7*z - x + w)"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y z. (EX w >= (x+y+z). w <= abs x + abs y + abs z)"
  by dlo

lemma "~(ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}). (EX y z w. 3* x + z*4 = 3*y & x + y < z & x> w & 3*x < w + y))"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y. (EX z w. abs (x-y) = (z-w) & z*1234 < 233*x & w ~= y)"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}). (EX y z w. min (5*x + 3*z) (17*w) + 5* abs (y - 8*x + z) <= max y (7*z - x + w))"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y z. (ALL w >= abs (x+y+z). w >= abs x + abs y + abs z)"
  by dlo

lemma "EX z. (ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y. (EX w >= (x+y+z). w <= abs x + abs y + abs z))"
  by dlo

lemma "EX z. (ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) < abs z. (EX y w. x< y & x < z & x> w & 3*x < w + y))"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y. (EX z. (ALL w. abs (x-y) = abs (z-w) --> z < x & w ~= y))"
  by dlo

lemma "EX y. (ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}). (EX z w. min (5*x + 3*z) (17*w) + 5* abs (y - 8*x + z) <= max y (7*z - x + w)))"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) z. (ALL w >= 13*x - 4*z. (EX y. w >= abs x + abs y + z))"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero}). (ALL y < x. (EX z > (x+y).
  (ALL w. 5*w + 10*x - z >= y --> w + 7*x + 3*z >= 2*y)))"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero}). (ALL y. (EX z > y.
  (ALL w . w < 13 --> w + 10*x - z >= y --> 5*w + 7*x + 13*z >= 2*y)))"
  by dlo

lemma "EX (x::'a::{ordered_field,recpower,number_ring, division_by_zero}) y z w. min (5*x + 3*z) (17*w) + 5* abs (y - 8*x + z) <= max y (7*z - x + w)"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}). (EX y. (ALL z>19. y <= x + z & (EX w. abs (y - x) < w)))"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}). (EX y. (ALL z>19. y <= x + z & (EX w. abs (x + z) < w - y)))"
  by dlo

lemma "ALL (x::'a::{ordered_field,recpower,number_ring, division_by_zero}). (EX y. abs y ~= abs x & (ALL z> max x y. (EX w. w ~= y & w ~= z & 3*w - z >= x + y)))"
  by dlo

end
