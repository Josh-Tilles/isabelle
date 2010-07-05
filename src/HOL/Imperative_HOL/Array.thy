(*  Title:      HOL/Imperative_HOL/Array.thy
    Author:     John Matthews, Galois Connections; Alexander Krauss, Lukas Bulwahn & Florian Haftmann, TU Muenchen
*)

header {* Monadic arrays *}

theory Array
imports Heap_Monad
begin

subsection {* Primitives *}

definition
  new :: "nat \<Rightarrow> 'a\<Colon>heap \<Rightarrow> 'a array Heap" where
  [code del]: "new n x = Heap_Monad.heap (Heap.array n x)"

definition
  of_list :: "'a\<Colon>heap list \<Rightarrow> 'a array Heap" where
  [code del]: "of_list xs = Heap_Monad.heap (Heap.array_of_list xs)"

definition
  length :: "'a\<Colon>heap array \<Rightarrow> nat Heap" where
  [code del]: "length arr = Heap_Monad.heap (\<lambda>h. (Heap.length arr h, h))"

definition
  nth :: "'a\<Colon>heap array \<Rightarrow> nat \<Rightarrow> 'a Heap"
where
  [code del]: "nth a i = (do len \<leftarrow> length a;
                 (if i < len
                     then Heap_Monad.heap (\<lambda>h. (get_array a h ! i, h))
                     else raise ''array lookup: index out of range'')
              done)"

definition
  upd :: "nat \<Rightarrow> 'a \<Rightarrow> 'a\<Colon>heap array \<Rightarrow> 'a\<Colon>heap array Heap"
where
  [code del]: "upd i x a = (do len \<leftarrow> length a;
                      (if i < len
                           then Heap_Monad.heap (\<lambda>h. (a, Heap.upd a i x h))
                           else raise ''array update: index out of range'')
                   done)" 

lemma upd_return:
  "upd i x a \<guillemotright> return a = upd i x a"
  by (rule Heap_eqI) (simp add: upd_def bindM_def split: option.split) 


subsection {* Derivates *}

definition
  map_entry :: "nat \<Rightarrow> ('a\<Colon>heap \<Rightarrow> 'a) \<Rightarrow> 'a array \<Rightarrow> 'a array Heap"
where
  "map_entry i f a = (do
     x \<leftarrow> nth a i;
     upd i (f x) a
   done)"

definition
  swap :: "nat \<Rightarrow> 'a \<Rightarrow> 'a\<Colon>heap array \<Rightarrow> 'a Heap"
where
  "swap i x a = (do
     y \<leftarrow> nth a i;
     upd i x a;
     return y
   done)"

definition
  make :: "nat \<Rightarrow> (nat \<Rightarrow> 'a\<Colon>heap) \<Rightarrow> 'a array Heap"
where
  "make n f = of_list (map f [0 ..< n])"

definition
  freeze :: "'a\<Colon>heap array \<Rightarrow> 'a list Heap"
where
  "freeze a = (do
     n \<leftarrow> length a;
     mapM (nth a) [0..<n]
   done)"

definition
   map :: "('a\<Colon>heap \<Rightarrow> 'a) \<Rightarrow> 'a array \<Rightarrow> 'a array Heap"
where
  "map f a = (do
     n \<leftarrow> length a;
     mapM (\<lambda>n. map_entry n f a) [0..<n];
     return a
   done)"

hide_const (open) new map -- {* avoid clashed with some popular names *}


subsection {* Properties *}

lemma array_make [code]:
  "Array.new n x = make n (\<lambda>_. x)"
  by (rule Heap_eqI) (simp add: make_def new_def array_of_list_replicate map_replicate_trivial of_list_def)

lemma array_of_list_make [code]:
  "of_list xs = make (List.length xs) (\<lambda>n. xs ! n)"
  by (rule Heap_eqI) (simp add: make_def map_nth)


subsection {* Code generator setup *}

subsubsection {* Logical intermediate layer *}

definition new' where
  [code del]: "new' = Array.new o Code_Numeral.nat_of"
hide_const (open) new'
lemma [code]:
  "Array.new = Array.new' o Code_Numeral.of_nat"
  by (simp add: new'_def o_def)

definition of_list' where
  [code del]: "of_list' i xs = Array.of_list (take (Code_Numeral.nat_of i) xs)"
hide_const (open) of_list'
lemma [code]:
  "Array.of_list xs = Array.of_list' (Code_Numeral.of_nat (List.length xs)) xs"
  by (simp add: of_list'_def)

definition make' where
  [code del]: "make' i f = Array.make (Code_Numeral.nat_of i) (f o Code_Numeral.of_nat)"
hide_const (open) make'
lemma [code]:
  "Array.make n f = Array.make' (Code_Numeral.of_nat n) (f o Code_Numeral.nat_of)"
  by (simp add: make'_def o_def)

definition length' where
  [code del]: "length' a = Array.length a \<guillemotright>= (\<lambda>n. return (Code_Numeral.of_nat n))"
hide_const (open) length'
lemma [code]:
  "Array.length a = Array.length' a \<guillemotright>= (\<lambda>i. return (Code_Numeral.nat_of i))"
  by (simp add: length'_def)

definition nth' where
  [code del]: "nth' a = Array.nth a o Code_Numeral.nat_of"
hide_const (open) nth'
lemma [code]:
  "Array.nth a n = Array.nth' a (Code_Numeral.of_nat n)"
  by (simp add: nth'_def)

definition upd' where
  [code del]: "upd' a i x = Array.upd (Code_Numeral.nat_of i) x a \<guillemotright> return ()"
hide_const (open) upd'
lemma [code]:
  "Array.upd i x a = Array.upd' a (Code_Numeral.of_nat i) x \<guillemotright> return a"
  by (simp add: upd'_def upd_return)


subsubsection {* SML *}

code_type array (SML "_/ array")
code_const Array (SML "raise/ (Fail/ \"bare Array\")")
code_const Array.new' (SML "(fn/ ()/ =>/ Array.array/ ((_),/ (_)))")
code_const Array.of_list' (SML "(fn/ ()/ =>/ Array.fromList/ _)")
code_const Array.make' (SML "(fn/ ()/ =>/ Array.tabulate/ ((_),/ (_)))")
code_const Array.length' (SML "(fn/ ()/ =>/ Array.length/ _)")
code_const Array.nth' (SML "(fn/ ()/ =>/ Array.sub/ ((_),/ (_)))")
code_const Array.upd' (SML "(fn/ ()/ =>/ Array.update/ ((_),/ (_),/ (_)))")

code_reserved SML Array


subsubsection {* OCaml *}

code_type array (OCaml "_/ array")
code_const Array (OCaml "failwith/ \"bare Array\"")
code_const Array.new' (OCaml "(fun/ ()/ ->/ Array.make/ (Big'_int.int'_of'_big'_int/ _)/ _)")
code_const Array.of_list' (OCaml "(fun/ ()/ ->/ Array.of'_list/ _)")
code_const Array.length' (OCaml "(fun/ ()/ ->/ Big'_int.big'_int'_of'_int/ (Array.length/ _))")
code_const Array.nth' (OCaml "(fun/ ()/ ->/ Array.get/ _/ (Big'_int.int'_of'_big'_int/ _))")
code_const Array.upd' (OCaml "(fun/ ()/ ->/ Array.set/ _/ (Big'_int.int'_of'_big'_int/ _)/ _)")

code_reserved OCaml Array


subsubsection {* Haskell *}

code_type array (Haskell "Heap.STArray/ Heap.RealWorld/ _")
code_const Array (Haskell "error/ \"bare Array\"")
code_const Array.new' (Haskell "Heap.newArray/ (0,/ _)")
code_const Array.of_list' (Haskell "Heap.newListArray/ (0,/ _)")
code_const Array.length' (Haskell "Heap.lengthArray")
code_const Array.nth' (Haskell "Heap.readArray")
code_const Array.upd' (Haskell "Heap.writeArray")

end
