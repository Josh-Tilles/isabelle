(*<*)
theory pairs = Main:;
(*>*)
text{*\label{sec:pairs}\indexbold{product type}
\index{pair|see{product type}}\index{tuple|see{product type}}
HOL also has pairs: \isa{($a@1$,$a@2$)} is of type $\tau@1$
\indexboldpos{\isasymtimes}{$Isatype} $\tau@2$ provided each $a@i$ is of type
$\tau@i$. The components of a pair are extracted by \isaindexbold{fst} and
\isaindexbold{snd}:
 \isa{fst($x$,$y$) = $x$} and \isa{snd($x$,$y$) = $y$}. Tuples
are simulated by pairs nested to the right: \isa{($a@1$,$a@2$,$a@3$)} stands
for \isa{($a@1$,($a@2$,$a@3$))} and $\tau@1 \times \tau@2 \times \tau@3$ for
$\tau@1 \times (\tau@2 \times \tau@3)$. Therefore we have
\isa{fst(snd($a@1$,$a@2$,$a@3$)) = $a@2$}.

Remarks:
\begin{itemize}
\item
There is also the type \isaindexbold{unit}, which contains exactly one
element denoted by \ttindexboldpos{()}{$Isatype}. This type can be viewed
as a degenerate product with 0 components.
\item
Products, like type @{typ nat}, are datatypes, which means
in particular that @{text induct_tac} and @{text case_tac} are applicable to
terms of product type.
\item
Instead of tuples with many components (where ``many'' is not much above 2),
it is preferable to use records.
\end{itemize}
For more information on pairs and records see Chapter~\ref{ch:more-types}.
*}
(*<*)
end
(*>*)
