
(* $Id$ *)

theory MuIOAOracle
imports MuIOA
begin

oracle sim_oracle ("term * thm list") =
  mk_sim_oracle

ML {*
(* call_sim_tac invokes oracle "Sim" *)
fun call_sim_tac thm_list i state = 
let val thy = Thm.theory_of_thm state;
        val (subgoal::_) = Library.drop(i-1,prems_of state);
        val OraAss = sim_oracle thy (subgoal,thm_list);
in cut_facts_tac [OraAss] i state end;


val ioa_implements_def = thm "ioa_implements_def";

(* is_sim_tac makes additionally to call_sim_tac some simplifications,
	which are suitable for implementation realtion formulas *)
fun is_sim_tac thm_list = SUBGOAL (fn (goal, i) =>
  EVERY [REPEAT (etac thin_rl i),
	 simp_tac (simpset() addsimps [ioa_implements_def]) i,
         rtac conjI i,
         rtac conjI (i+1),
	 TRY(call_sim_tac thm_list (i+2)),
	 TRY(atac (i+2)), 
         REPEAT(rtac refl (i+2)),
	 simp_tac (simpset() addsimps (thm_list @
				       comp_simps @ restrict_simps @ hide_simps @
				       rename_simps @  ioa_simps @ asig_simps)) (i+1),
	 simp_tac (simpset() addsimps (thm_list @
				       comp_simps @ restrict_simps @ hide_simps @
				       rename_simps @ ioa_simps @ asig_simps)) (i)]);

*}

end
