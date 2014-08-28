(*  Title:      Code_Test_OCaml.thy
    Author:     Andreas Lochbihler, ETH Zurich

Test case for test_code on OCaml
*)

theory Code_Test_OCaml imports Code_Test begin

test_code "14 + 7 * -12 = (140 div -2 :: integer)" in OCaml

eval_term "14 + 7 * -12 :: integer" in OCaml

end