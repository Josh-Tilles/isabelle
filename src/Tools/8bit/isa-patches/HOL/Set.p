syntax
  "�"		:: "['a set, 'a set] => 'a set"       (infixl 70)
  "�"		:: "['a set, 'a set] => 'a set"       (infixl 65)
  "�"		:: "['a, 'a set] => bool"             (infixl 50)
  "�"		:: "['a, 'a set] => bool"             (infixl 50)
  GUnion	:: "(('a set)set) => 'a set"          ("�_" [90] 90)
  GInter	:: "(('a set)set) => 'a set"          ("�_" [90] 90)
  GUNION1       :: "['a => 'b set] => 'b set"         (binder "� " 10)
  GINTER1       :: "['a => 'b set] => 'b set"         (binder "� " 10)
  GINTER	:: "[pttrn, 'a set, 'b set] => 'b set"  ("(3� _�_./ _)" 10)
  GUNION	:: "[pttrn, 'a set, 'b set] => 'b set"  ("(3� _�_./ _)" 10)
  GBall		:: "[pttrn, 'a set, bool] => bool"      ("(3� _�_./ _)" 10)
  GBex		:: "[pttrn, 'a set, bool] => bool"      ("(3� _�_./ _)" 10)

translations
  "x � y"      == "�(x : y)"
  "x � y"      == "(x : y)"
  "x � y"      == "x Int y"
  "x � y"      == "x Un  y"
  "�X"        == "Inter X" 
  "�X"        == "Union X"
  "�x.A"      == "INT x.A"
  "�x.A"      == "UN x.A"
  "�x�A. B"   == "INT x:A. B"
  "�x�A. B"   == "UN x:A. B"
  "�x�A. P"    == "! x:A. P"
  "�x�A. P"    == "? x:A. P"
