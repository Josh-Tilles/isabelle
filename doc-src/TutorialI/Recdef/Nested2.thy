(*<*)
theory Nested2 = Nested0:;
consts trev  :: "('a,'b)term => ('a,'b)term";
(*>*)

text{*\noindent
The termintion condition is easily proved by induction:
*};

lemma [simp]: "t \\<in> set ts \\<longrightarrow> size t < Suc(term_size ts)";
by(induct_tac ts, auto);
(*<*)
recdef trev "measure size"
 "trev (Var x) = Var x"
 "trev (App f ts) = App f (rev(map trev ts))";
(*>*)
text{*\noindent
By making this theorem a simplification rule, \isacommand{recdef}
applies it automatically and the above definition of @{term"trev"}
succeeds now. As a reward for our effort, we can now prove the desired
lemma directly. The key is the fact that we no longer need the verbose
induction schema for type \isa{term} but the simpler one arising from
@{term"trev"}:
*};

lemmas [cong] = map_cong;
lemma "trev(trev t) = t";
apply(induct_tac t rule:trev.induct);
txt{*\noindent
This leaves us with a trivial base case @{term"trev (trev (Var x)) = Var x"} and the step case
\begin{quote}
@{term[display,margin=60]"ALL t. t : set ts --> trev (trev t) = t ==> trev (trev (App f ts)) = App f ts"}
\end{quote}
both of which are solved by simplification:
*};

by(simp_all add:rev_map sym[OF map_compose]);

text{*\noindent
If the proof of the induction step mystifies you, we recommend to go through
the chain of simplification steps in detail, probably with the help of
\isa{trace\_simp}.
%\begin{quote}
%{term[display]"trev(trev(App f ts))"}\\
%{term[display]"App f (rev(map trev (rev(map trev ts))))"}\\
%{term[display]"App f (map trev (rev(rev(map trev ts))))"}\\
%{term[display]"App f (map trev (map trev ts))"}\\
%{term[display]"App f (map (trev o trev) ts)"}\\
%{term[display]"App f (map (%x. x) ts)"}\\
%{term[display]"App f ts"}
%\end{quote}

The above definition of @{term"trev"} is superior to the one in \S\ref{sec:nested-datatype}
because it brings @{term"rev"} into play, about which already know a lot, in particular
@{prop"rev(rev xs) = xs"}.
Thus this proof is a good example of an important principle:
\begin{quote}
\emph{Chose your definitions carefully\\
because they determine the complexity of your proofs.}
\end{quote}

Let us now return to the question of how \isacommand{recdef} can come up with
sensible termination conditions in the presence of higher-order functions
like @{term"map"}. For a start, if nothing were known about @{term"map"},
@{term"map trev ts"} might apply @{term"trev"} to arbitrary terms, and thus
\isacommand{recdef} would try to prove the unprovable @{term"size t < Suc
(term_size ts)"}, without any assumption about \isa{t}.  Therefore
\isacommand{recdef} has been supplied with the congruence theorem
\isa{map\_cong}:
\begin{quote}
@{thm[display,margin=50]"map_cong"[no_vars]}
\end{quote}
Its second premise expresses (indirectly) that the second argument of
@{term"map"} is only applied to elements of its third argument. Congruence
rules for other higher-order functions on lists would look very similar but
have not been proved yet because they were never needed. If you get into a
situation where you need to supply \isacommand{recdef} with new congruence
rules, you can either append the line
\begin{ttbox}
congs <congruence rules>
\end{ttbox}
to the specific occurrence of \isacommand{recdef} or declare them globally:
\begin{ttbox}
lemmas [????????] = <congruence rules>
\end{ttbox}

Note that \isacommand{recdef} feeds on exactly the same \emph{kind} of
congruence rules as the simplifier (\S\ref{sec:simp-cong}) but that
declaring a congruence rule for the simplifier does not make it
available to \isacommand{recdef}, and vice versa. This is intentional.
*};
(*<*)end;(*>*)
