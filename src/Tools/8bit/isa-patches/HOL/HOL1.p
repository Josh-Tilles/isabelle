types
('a, 'b) "�"          (infixr 5)

syntax
  "�"		:: "['a::{}, 'a] => prop"       ("(_ �/ _)"         [3, 2] 2)
  "��"		:: "[prop, prop] => prop"	("(_ ��/ _)"        [2, 1] 1)
  "Gbigimpl"	:: "[asms, prop] => prop"	("((3� _ �) ��/ _)" [0, 1] 1)
  "Gall"	:: "('a => prop) => prop"	(binder "�"                0)

  "Glam"         :: "[idts, 'a::logic] => 'b::logic"  ("(3�_./ _)" 10)
  "�"           :: "['a, 'a] => bool"                 (infixl 50)
  "Gnot"        :: "bool => bool"                     ("� _" [40] 40)
  "GEps"        :: "[pttrn, bool] => 'a"               ("(3�_./ _)" 10)
  "GAll"        :: "[idts, bool] => bool"             ("(3�_./ _)" 10)
  "GEx"         :: "[idts, bool] => bool"             ("(3�_./ _)" 10)
  "GEx1"        :: "[idts, bool] => bool"             ("(3�!_./ _)" 10)
  "�"           :: "[bool, bool] => bool"             (infixr 35)
  "�"           :: "[bool, bool] => bool"             (infixr 30)
  "��"          :: "[bool, bool] => bool"             (infixr 25)

translations
(type)  "x � y"	== (type) "x => y" 

(*  "�x.t"	=> "%x.t" *)

  "x � y"	== "x ~= y"
  "� y"		== "~y"
  "�x.P"	== "@x.P"
  "�x.P"	== "! x. P"
  "�x.P"	== "? x. P"
  "�!x.P"	== "?! x. P"
  "x � y"	== "x & y"
  "x � y"	== "x | y"
  "x �� y"	== "x --> y"
