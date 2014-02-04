(*  Title:      HOL/SMT_Examples/Boogie.thy
    Author:     Sascha Boehme, TU Muenchen
*)

header {* Proving Boogie-generated verification conditions *}

theory Boogie
imports Main
begin

text {*
HOL-Boogie and its applications are described in:
\begin{itemize}

\item Sascha B"ohme, K. Rustan M. Leino, and Burkhart Wolff.
HOL-Boogie --- An Interactive Prover for the Boogie Program-Verifier.
Theorem Proving in Higher Order Logics, 2008.

\item Sascha B"ohme, Micha{\l} Moskal, Wolfram Schulte, and Burkhart Wolff.
HOL-Boogie --- An Interactive Prover-Backend for the Verifying C Compiler.
Journal of Automated Reasoning, 2009.

\end{itemize}
*}



section {* Built-in types and functions of Boogie *}

subsection {* Integer arithmetics *}

text {*
The operations @{text div} and @{text mod} are built-in in Boogie, but
without a particular semantics due to different interpretations in
programming languages. We assume that each application comes with a
proper axiomatization.
*}

axiomatization
  boogie_div :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "div'_b" 70) and
  boogie_mod :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "mod'_b" 70)



section {* Setup *}

ML_file "boogie.ML"



section {* Verification condition proofs *}

declare [[smt_oracle = false]]
declare [[smt_read_only_certificates = true]]


declare [[smt_certificates = "Boogie_Max.certs"]]

setup {* Boogie.boogie_prove "Boogie_Max.b2i" *}


declare [[smt_certificates = "Boogie_Dijkstra.certs"]]

setup {* Boogie.boogie_prove "Boogie_Dijkstra.b2i" *}


declare [[z3_with_extensions = true]]
declare [[smt_certificates = "VCC_Max.certs"]]

setup {* Boogie.boogie_prove "VCC_Max.b2i" *}

end
