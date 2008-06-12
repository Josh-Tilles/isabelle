(*<*)theory Overloading imports Overloading1 begin(*>*)
instance list :: (type)ordrel
by intro_classes

text{*\noindent
This \isacommand{instance} declaration can be read like the declaration of
a function on types.  The constructor @{text list} maps types of class @{text
type} (all HOL types), to types of class @{text ordrel};
in other words,
if @{text"ty :: type"} then @{text"ty list :: ordrel"}.
Of course we should also define the meaning of @{text <<=} and
@{text <<} on lists:
*}

defs (overloaded)
prefix_def:
  "xs <<= (ys::'a list)  \<equiv>  \<exists>zs. ys = xs@zs"
strict_prefix_def:
  "xs << (ys::'a list)   \<equiv>  xs <<= ys \<and> xs \<noteq> ys"

(*<*)end(*>*)
