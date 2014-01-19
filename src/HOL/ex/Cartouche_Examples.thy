header {* Some examples with text cartouches *}

theory Cartouche_Examples
imports Main
keywords "cartouche" :: diag
begin

subsection {* Outer syntax *}

ML {*
  Outer_Syntax.improper_command @{command_spec "cartouche"} ""
    (Parse.cartouche >> (fn s =>
      Toplevel.imperative (fn () => writeln s)))
*}

cartouche \<open>abc\<close>
cartouche \<open>abc \<open>\<alpha>\<beta>\<gamma>\<close> xzy\<close>


subsection {* Inner syntax *}

syntax "_string_cartouche" :: "cartouche_position \<Rightarrow> string"  ("STR _")

parse_translation {*
  let
    val mk_nib =
      Syntax.const o Lexicon.mark_const o
        fst o Term.dest_Const o HOLogic.mk_nibble;

    fun mk_char (s, pos) =
      let
        val c =
          if Symbol.is_ascii s then ord s
          else if s = "\<newline>" then 10
          else error ("String literal contains illegal symbol: " ^ quote s ^ Position.here pos);
      in Syntax.const @{const_syntax Char} $ mk_nib (c div 16) $ mk_nib (c mod 16) end;

    fun mk_string [] = Const (@{const_syntax Nil}, @{typ string})
      | mk_string (s :: ss) =
          Syntax.const @{const_syntax Cons} $ mk_char s $ mk_string ss;

    fun string_tr ctxt args =
      let fun err () = raise TERM ("string_tr", []) in
        (case args of
          [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
            (case Term_Position.decode_position p of
              SOME (pos, _) =>
                c $ mk_string (Symbol_Pos.cartouche_content (Symbol_Pos.explode (s, pos))) $ p
            | NONE => err ())
        | _ => err ())
      end;
  in
    [(@{syntax_const "_string_cartouche"}, string_tr)]
  end
*}

term "STR \<open>\<close>"
term "STR \<open>abc\<close>"
lemma "STR \<open>abc\<close> @ STR \<open>xyz\<close> = STR \<open>abcxyz\<close>" by simp


subsection {* Proof method syntax *}

ML {*
structure ML_Tactic:
sig
  val set: (Proof.context -> tactic) -> Proof.context -> Proof.context
  val ml_tactic: string * Position.T -> Proof.context -> tactic
end =
struct
  structure Data = Proof_Data(type T = Proof.context -> tactic fun init _ = K no_tac);

  val set = Data.put;

  fun ml_tactic (txt, pos) ctxt =
    let
      val ctxt' = ctxt |> Context.proof_map
        (ML_Context.expression pos
          "fun tactic (ctxt : Proof.context) : tactic"
          "Context.map_proof (ML_Tactic.set tactic)" (ML_Lex.read pos txt));
    in Data.get ctxt' ctxt end;
end;
*}


subsection {* Explicit version: method with cartouche argument *}

method_setup ml_tactic = {*
  Scan.lift Args.cartouche_source_position
    >> (fn arg => fn ctxt => SIMPLE_METHOD (ML_Tactic.ml_tactic arg ctxt))
*}

lemma "A \<and> B \<longrightarrow> B \<and> A"
  apply (ml_tactic \<open>rtac @{thm impI} 1\<close>)
  apply (ml_tactic \<open>etac @{thm conjE} 1\<close>)
  apply (ml_tactic \<open>rtac @{thm conjI} 1\<close>)
  apply (ml_tactic \<open>ALLGOALS atac\<close>)
  done

lemma "A \<and> B \<longrightarrow> B \<and> A" by (ml_tactic \<open>blast_tac ctxt 1\<close>)

ML {* @{lemma "A \<and> B \<longrightarrow> B \<and> A" by (ml_tactic \<open>blast_tac ctxt 1\<close>)} *}

text {* @{ML "@{lemma \"A \<and> B \<longrightarrow> B \<and> A\" by (ml_tactic \<open>blast_tac ctxt 1\<close>)}"} *}


subsection {* Implicit version: method with special name "cartouche" (dynamic!) *}

method_setup "cartouche" = {*
  Scan.lift Args.cartouche_source_position
    >> (fn arg => fn ctxt => SIMPLE_METHOD (ML_Tactic.ml_tactic arg ctxt))
*}

lemma "A \<and> B \<longrightarrow> B \<and> A"
  apply \<open>rtac @{thm impI} 1\<close>
  apply \<open>etac @{thm conjE} 1\<close>
  apply \<open>rtac @{thm conjI} 1\<close>
  apply \<open>ALLGOALS atac\<close>
  done

lemma "A \<and> B \<longrightarrow> B \<and> A"
  by (\<open>rtac @{thm impI} 1\<close>, \<open>etac @{thm conjE} 1\<close>, \<open>rtac @{thm conjI} 1\<close>, \<open>atac 1\<close>+)

end
