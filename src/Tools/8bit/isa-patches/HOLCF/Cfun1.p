types

('a, 'b) "�"          (infixr 5)

syntax
	Gfabs	:: "('a => 'b)=>('a -> 'b)"	(binder "�" 10)

translations

(type)  "x � y"	== (type) "x -> y" 

