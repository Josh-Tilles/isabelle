types

('a, 'b) "�"          (infixr 20)

translations

(type)  "x � y"	== (type) "x * y" 

  "�(x,y,zs).b"   == "split(�x.�(y,zs).b)"
  "�(x,y).b"      == "split(�x y.b)"

