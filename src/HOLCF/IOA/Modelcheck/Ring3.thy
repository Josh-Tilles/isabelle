
(* $Id$ *)

theory Ring3
imports MuIOAOracle
begin

datatype token = Leader | id0 | id1 | id2 | id3 | id4

datatype Comm =
  Zero_One token | One_Two token | Two_Zero token |
  Leader_Zero | Leader_One | Leader_Two

constdefs
  Greater :: "[token, token] => bool"
  "Greater x y ==
    (x~=Leader & x~=id0 & y=id0) | (x=id4 & y~=id4 & y~=Leader) |
    (x=id2 & y=id1) | (x=id3 & y=id1) | (x=id3 & y=id2)"


(*the ring is the composition of aut0, aut1 and aut2*)

automaton aut0 =
  signature
    actions Comm
    inputs "Two_Zero t"
    outputs "Zero_One t","Leader_Zero"
  states
    idf :: token
  initially "idf=id0 | idf = id3"
  transitions
    "Two_Zero t"
      transrel
        "if (t=id0 | t=id3) then (idf'=Leader) else
        (if (Greater t idf) then (idf'=t) else (idf'=idf))"
    "Zero_One t"
      pre "t=idf"
    "Leader_Zero"
      pre "idf=Leader"

automaton aut1 =
  signature
    actions Comm
    inputs "Zero_One t"
    outputs "One_Two t","Leader_One"
  states
    idf :: token
  initially "idf=id1 | idf=id4"
  transitions
    "Zero_One t"
      transrel
        "if (t=id1 | t=id4) then (idf'=Leader) else
        (if (Greater t idf) then (idf'=t) else (idf'=idf))"
    "One_Two t"
      pre "t=idf"
    "Leader_One"
      pre "idf=Leader"

automaton aut2 =
  signature
    actions Comm
    inputs "One_Two t"
    outputs "Two_Zero t","Leader_Two"
  states
    idf :: token
  initially "idf=id2"
  transitions
    "One_Two t"
      transrel
        "if (t=id2) then (idf'=Leader) else
        (if (Greater t idf) then (idf'=t) else (idf'=idf))"
    "Two_Zero t"
      pre "t=idf"
    "Leader_Two"
      pre "idf=Leader"

automaton ring = compose aut0, aut1, aut2


(*one_leader expresses property that at most one component declares
  itself to leader*)

automaton one_leader =
  signature
    actions Comm
    outputs "Zero_One t","One_Two t","Two_Zero t","Leader_Zero","Leader_One","Leader_Two"
  states
    leader :: token
  initially "leader=Leader"
  transitions
    "Zero_One t"
      pre "True"
    "One_Two t"
      pre "True"
    "Two_Zero t"
      pre "True"
    "Leader_Zero"
      pre "leader=id0 | leader=Leader"
      post leader:="id0"
    "Leader_One"
      pre "leader=id1 | leader=Leader"
      post leader:="id1"
    "Leader_Two"
      pre "leader=id2 | leader=Leader"
      post leader:="id2"

lemmas aut_simps =
  Greater_def one_leader_def
  one_leader_asig_def one_leader_trans_def one_leader_initial_def
  ring_def aut0_asig_def aut0_trans_def aut0_initial_def aut0_def
  aut1_asig_def aut1_trans_def aut1_initial_def aut1_def
  aut2_asig_def aut2_trans_def aut2_initial_def aut2_def

(* property to prove: at most one (of 3) members of the ring will
	declare itself to leader *)
lemma at_most_one_leader: "ring =<| one_leader"
apply (tactic {* is_sim_tac (thms "aut_simps") 1 *})
apply auto
done

end
