ToyList = Datatype +

datatype 'a list = Nil                        ("[]")
                 | Cons 'a ('a list)          (infixr "#" 65)

consts app :: 'a list => 'a list => 'a list   (infixr "@" 65)
       rev :: 'a list => 'a list

primrec
"[] @ ys       = ys"
"(x # xs) @ ys = x # (xs @ ys)"

primrec
"rev []        = []"
"rev (x # xs)  = (rev xs) @ (x # [])"

end
