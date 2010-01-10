/*
 * Document as list of commands, consisting of lists of tokens
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.proofdocument


import scala.actors.Actor._
import scala.collection.mutable

import java.util.regex.Pattern


object Document
{
  // Be careful when changing this regex. Not only must it handle the
  // spurious end of a token but also:
  // Bug ID: 5050507 Pattern.matches throws StackOverflow Error
  // http://bugs.sun.com/bugdatabase/view_bug.do?bug_id=5050507

  val token_pattern =
    Pattern.compile(
      "\\{\\*([^*]|\\*[^}]|\\*\\z)*(\\z|\\*\\})|" +
      "\\(\\*([^*]|\\*[^)]|\\*\\z)*(\\z|\\*\\))|" +
      "(\\?'?|')[A-Za-z_0-9.]*|" +
      "[A-Za-z_0-9.]+|" +
      "[!#$%&*+-/<=>?@^_|~]+|" +
      "\"([^\\\\\"]?(\\\\(.|\\z))?)*+(\"|\\z)|" +
      "`([^\\\\`]?(\\\\(.|\\z))?)*+(`|\\z)|" +
      "[()\\[\\]{}:;]", Pattern.MULTILINE)

  def empty(id: Isar_Document.Document_ID): Document =
  {
    val doc = new Document(id, Linear_Set(), Map(), Linear_Set(), Map())
    doc.assign_states(Nil)
    doc
  }

  type Edit = (Option[Command], Option[Command])

  def text_edits(session: Session, old_doc: Document, new_id: Isar_Document.Document_ID,
    edits: List[Text_Edit]): (List[Edit], Document) =
  {
    require(old_doc.assignment.is_finished)
    val doc0 =
      Document_Body(old_doc.tokens, old_doc.token_start, old_doc.commands, old_doc.assignment.join)

    val changes = new mutable.ListBuffer[Edit]
    val doc = (doc0 /: edits)((doc1: Document_Body, edit: Text_Edit) =>
      {
        val (doc2, chgs) = doc1.text_edit(session, edit)
        changes ++ chgs
        doc2
      })
    val new_doc = new Document(new_id, doc.tokens, doc.token_start, doc.commands, doc.states)
    (changes.toList, new_doc)
  }
}

private case class Document_Body(
  val tokens: Linear_Set[Token],   // FIXME plain List, inside Command
  val token_start: Map[Token, Int],  // FIXME eliminate
  val commands: Linear_Set[Command],
  val states: Map[Command, Command])
{
  /* token view */

  def text_edit(session: Session, e: Text_Edit): (Document_Body, List[Document.Edit]) =
  {
    case class TextChange(start: Int, added: String, removed: String)
    val change = e match {
      case Text_Edit.Insert(s, a) => TextChange(s, a, "")
      case Text_Edit.Remove(s, r) => TextChange(s, "", r)
    }
    //indices of tokens
    var start: Map[Token, Int] = token_start
    def stop(t: Token) = start(t) + t.length
    // split old token lists
    val tokens = Nil ++ this.tokens
    val (begin, remaining) = tokens.span(stop(_) < change.start)
    val (removed, end) = remaining.span(token_start(_) <= change.start + change.removed.length)
    // update indices
    start = end.foldLeft(start)((s, t) =>
      s + (t -> (s(t) + change.added.length - change.removed.length)))

    val split_begin = removed.takeWhile(start(_) < change.start).
      map (t => {
          val split_tok = new Token(t.content.substring(0, change.start - start(t)), t.kind)
          start += (split_tok -> start(t))
          split_tok
        })

    val split_end = removed.dropWhile(stop(_) < change.start + change.removed.length).
      map (t => {
          val split_tok =
            new Token(t.content.substring(change.start + change.removed.length - start(t)), t.kind)
          start += (split_tok -> start(t))
          split_tok
        })
    // update indices
    start = removed.foldLeft (start) ((s, t) => s - t)
    start = split_end.foldLeft (start) ((s, t) =>
    s + (t -> (change.start + change.added.length)))

    val ins = new Token(change.added, Token.Kind.OTHER)
    start += (ins -> change.start)

    var invalid_tokens = split_begin ::: ins :: split_end ::: end
    var new_tokens: List[Token] = Nil
    var old_suffix: List[Token] = Nil

    val match_start = invalid_tokens.firstOption.map(start(_)).getOrElse(0)
    val matcher =
      Document.token_pattern.matcher(Token.string_from_tokens(invalid_tokens, start))

    while (matcher.find() && invalid_tokens != Nil) {
			val kind =
        if (session.current_syntax.is_command(matcher.group))
          Token.Kind.COMMAND_START
        else if (matcher.end - matcher.start > 2 && matcher.group.substring(0, 2) == "(*")
          Token.Kind.COMMENT
        else
          Token.Kind.OTHER
      val new_token = new Token(matcher.group, kind)
      start += (new_token -> (match_start + matcher.start))
      new_tokens ::= new_token

      invalid_tokens = invalid_tokens dropWhile (stop(_) < stop(new_token))
      invalid_tokens match {
        case t :: ts =>
          if (start(t) == start(new_token) &&
              start(t) > change.start + change.added.length) {
          old_suffix = t :: ts
          new_tokens = new_tokens.tail
          invalid_tokens = Nil
        }
        case _ =>
      }
    }
    val insert = new_tokens.reverse
    val new_token_list = begin ::: insert ::: old_suffix
    token_changed(session, begin.lastOption, insert,
      old_suffix.firstOption, new_token_list, start)
  }


  /* command view */

  private def token_changed(
      session: Session,
      before_change: Option[Token],
      inserted_tokens: List[Token],
      after_change: Option[Token],
      new_tokens: List[Token],
      new_token_start: Map[Token, Int]): (Document_Body, List[Document.Edit]) =
  {
    val new_tokenset = Linear_Set[Token]() ++ new_tokens
    val cmd_before_change = before_change match {
      case None => None
      case Some(bc) =>
        val cmd_with_bc = commands.find(_.contains(bc)).get
        if (cmd_with_bc.tokens.last == bc) {
          if (new_tokenset.next(bc).map(_.is_start).getOrElse(true))
            Some(cmd_with_bc)
          else commands.prev(cmd_with_bc)
        }
        else commands.prev(cmd_with_bc)
    }

    val cmd_after_change = after_change match {
      case None => None
      case Some(ac) =>
        val cmd_with_ac = commands.find(_.contains(ac)).get
        if (ac.is_start)
          Some(cmd_with_ac)
        else
          commands.next(cmd_with_ac)
    }

    val removed_commands = commands.dropWhile(Some(_) != cmd_before_change).drop(1).
      takeWhile(Some(_) != cmd_after_change)

    // calculate inserted commands
    def tokens_to_commands(tokens: List[Token]): List[Command]= {
      tokens match {
        case Nil => Nil
        case t :: ts =>
          val (cmd, rest) =
            ts.span(t => t.kind != Token.Kind.COMMAND_START && t.kind != Token.Kind.COMMENT)
          new Command(session.create_id(), t :: cmd, new_token_start) :: tokens_to_commands(rest)
      }
    }

    val split_begin =
      if (before_change.isDefined) {
        val changed =
          if (cmd_before_change.isDefined)
            new_tokens.dropWhile(_ != cmd_before_change.get.tokens.last).drop(1)
          else new_tokenset
        if (changed.exists(_ == before_change.get))
          changed.takeWhile(_ != before_change.get).toList :::
            List(before_change.get)
        else Nil
      } else Nil

    val split_end =
      if (after_change.isDefined) {
        val unchanged = new_tokens.dropWhile(_ != after_change.get)
        if(cmd_after_change.isDefined) {
          if (unchanged.exists(_ == cmd_after_change.get.tokens.first))
            unchanged.takeWhile(_ != cmd_after_change.get.tokens.first).toList
          else Nil
        } else {
          unchanged
        }
      } else Nil

    val rescan_begin =
      split_begin :::
        before_change.map(bc => new_tokens.dropWhile(_ != bc).drop(1)).getOrElse(new_tokens)
    val rescanning_tokens =
      after_change.map(ac => rescan_begin.takeWhile(_ != ac)).getOrElse(rescan_begin) :::
        split_end
    val inserted_commands = tokens_to_commands(rescanning_tokens.toList)

    // build new document
    val new_commandset = commands.
      delete_between(cmd_before_change, cmd_after_change).
      append_after(cmd_before_change, inserted_commands)


    val doc =
      new Document_Body(new_tokenset, new_token_start, new_commandset, states -- removed_commands)

    val removes =
      for (cmd <- removed_commands) yield (cmd_before_change -> None)
    val inserts =
      for (cmd <- inserted_commands) yield (doc.commands.prev(cmd) -> Some(cmd))

    (doc, removes.toList ++ inserts)
  }
}


class Document(
    val id: Isar_Document.Document_ID,
    val tokens: Linear_Set[Token],   // FIXME plain List, inside Command
    val token_start: Map[Token, Int],  // FIXME eliminate
    val commands: Linear_Set[Command],
    old_states: Map[Command, Command])
{
  // FIXME eliminate
  def content = Token.string_from_tokens(Nil ++ tokens, token_start)


  /* command source positions */

  def command_starts: Iterator[(Command, Int)] =
  {
    var offset = 0
    for (cmd <- commands.elements) yield {
      // val start = offset  FIXME new
      val start = token_start(cmd.tokens.first)   // FIXME old
      offset += cmd.length
      (cmd, start)
    }
  }

  def command_start(cmd: Command): Option[Int] =
    command_starts.find(_._1 == cmd).map(_._2)

  def command_range(i: Int): Iterator[(Command, Int)] =
    command_starts dropWhile { case (cmd, start) => start + cmd.length <= i }

  def command_range(i: Int, j: Int): Iterator[(Command, Int)] =
    command_range(i) takeWhile { case (_, start) => start < j }

  def command_at(i: Int): Option[(Command, Int)] =
  {
    val range = command_range(i)
    if (range.hasNext) Some(range.next) else None
  }



  /* command state assignment */

  val assignment = Future.promise[Map[Command, Command]]
  def await_assignment { assignment.join }

  @volatile private var tmp_states = old_states

  def assign_states(new_states: List[(Command, Command)])
  {
    assignment.fulfill(tmp_states ++ new_states)
    tmp_states = Map()
  }

  def current_state(cmd: Command): State =
  {
    require(assignment.is_finished)
    (assignment.join)(cmd).current_state
  }
}
