(*  Title:      HOL/Library/Array.thy
    ID:         $Id$
    Author:     John Matthews, Galois Connections; Alexander Krauss, Lukas Bulwahn & Florian Haftmann, TU Muenchen
*)

header {* Monadic arrays *}

theory Array
imports Heap_Monad Code_Index
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
                     else raise (''array lookup: index out of range''))
              done)"

-- {* FIXME adjustion for List theory *}
no_syntax
  nth  :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" (infixl "!" 100)

abbreviation
  nth_list :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" (infixl "!" 100)
where
  "nth_list \<equiv> List.nth"

definition
  upd :: "nat \<Rightarrow> 'a \<Rightarrow> 'a\<Colon>heap array \<Rightarrow> 'a\<Colon>heap array Heap"
where
  [code del]: "upd i x a = (do len \<leftarrow> length a;
                      (if i < len
                           then Heap_Monad.heap (\<lambda>h. (a, Heap.upd a i x h))
                           else raise (''array update: index out of range''))
                   done)" 

lemma upd_return:
  "upd i x a \<guillemotright> return a = upd i x a"
proof (rule Heap_eqI)
  fix h
  obtain len h' where "Heap_Monad.execute (Array.length a) h = (len, h')"
    by (cases "Heap_Monad.execute (Array.length a) h")
  then show "Heap_Monad.execute (upd i x a \<guillemotright> return a) h = Heap_Monad.execute (upd i x a) h"
    by (auto simp add: upd_def bindM_def run_drop split: sum.split)
qed


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
     return x
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
     foldM (\<lambda>n. map_entry n f) [0..<n] a
   done)"

hide (open) const new map -- {* avoid clashed with some popular names *}


subsection {* Properties *}

lemma array_make [code func]:
  "Array.new n x = make n (\<lambda>_. x)"
  by (induct n) (simp_all add: make_def new_def Heap_Monad.heap_def
    monad_simp array_of_list_replicate [symmetric]
    map_replicate_trivial replicate_append_same
    of_list_def)

lemma array_of_list_make [code func]:
  "of_list xs = make (List.length xs) (\<lambda>n. xs ! n)"
  unfolding make_def map_nth ..


subsection {* Code generator setup *}

subsubsection {* Logical intermediate layer *}

definition new' where
  [code del]: "new' = Array.new o nat_of_index"
hide (open) const new'
lemma [code func]:
  "Array.new = Array.new' o index_of_nat"
  by (simp add: new'_def o_def)

definition of_list' where
  [code del]: "of_list' i xs = Array.of_list (take (nat_of_index i) xs)"
hide (open) const of_list'
lemma [code func]:
  "Array.of_list xs = Array.of_list' (index_of_nat (List.length xs)) xs"
  by (simp add: of_list'_def)

definition make' where
  [code del]: "make' i f = Array.make (nat_of_index i) (f o index_of_nat)"
hide (open) const make'
lemma [code func]:
  "Array.make n f = Array.make' (index_of_nat n) (f o nat_of_index)"
  by (simp add: make'_def o_def)

definition length' where
  [code del]: "length' = Array.length \<guillemotright>== liftM index_of_nat"
hide (open) const length'
lemma [code func]:
  "Array.length = Array.length' \<guillemotright>== liftM nat_of_index"
  by (simp add: length'_def monad_simp',
    simp add: liftM_def comp_def monad_simp,
    simp add: monad_simp')

definition nth' where
  [code del]: "nth' a = Array.nth a o nat_of_index"
hide (open) const nth'
lemma [code func]:
  "Array.nth a n = Array.nth' a (index_of_nat n)"
  by (simp add: nth'_def)

definition upd' where
  [code del]: "upd' a i x = Array.upd (nat_of_index i) x a \<guillemotright> return ()"
hide (open) const upd'
lemma [code func]:
  "Array.upd i x a = Array.upd' a (index_of_nat i) x \<guillemotright> return a"
  by (simp add: upd'_def monad_simp upd_return)


subsubsection {* SML *}

code_type array (SML "_/ array")
code_const Array (SML "raise/ (Fail/ \"bare Array\")")
code_const Array.new' (SML "(fn/ ()/ =>/ Array.array/ ((_),/ (_)))")
code_const Array.of_list (SML "(fn/ ()/ =>/ Array.fromList/ _)")
code_const Array.make' (SML "(fn/ ()/ =>/ Array.tabulate/ ((_),/ (_)))")
code_const Array.length' (SML "(fn/ ()/ =>/ Array.length/ _)")
code_const Array.nth' (SML "(fn/ ()/ =>/ Array.sub/ ((_),/ (_)))")
code_const Array.upd' (SML "(fn/ ()/ =>/ Array.update/ ((_),/ (_),/ (_)))")

code_reserved SML Array


subsubsection {* OCaml *}

code_type array (OCaml "_/ array")
code_const Array (OCaml "failwith/ \"bare Array\"")
code_const Array.new' (OCaml "(fn/ ()/ =>/ Array.make/ _/ _)")
code_const Array.of_list (OCaml "(fn/ ()/ =>/ Array.of'_list/ _)")
code_const Array.make' (OCaml "(fn/ ()/ =>/ Array.init/ _/ _)")
code_const Array.length' (OCaml "(fn/ ()/ =>/ Array.length/ _)")
code_const Array.nth' (OCaml "(fn/ ()/ =>/ Array.get/ _/ _)")
code_const Array.upd' (OCaml "(fn/ ()/ =>/ Array.set/ _/ _/ _)")

code_reserved OCaml Array


subsubsection {* Haskell *}

code_type array (Haskell "STArray '_s _")
code_const Array (Haskell "error/ \"bare Array\"")
code_const Array.new' (Haskell "newArray/ (0,/ _)")
code_const Array.of_list' (Haskell "newListArray/ (0,/ _)")
code_const Array.length' (Haskell "length")
code_const Array.nth' (Haskell "readArray")
code_const Array.upd' (Haskell "writeArray")

end
