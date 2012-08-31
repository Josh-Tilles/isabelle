/*  Title:      Pure/PIDE/protocol.scala
    Author:     Makarius

Protocol message formats for interactive proof documents.
*/

package isabelle


object Protocol
{
  /* document editing */

  object Assign
  {
    def unapply(text: String): Option[(Document.Version_ID, Document.Assign)] =
      try {
        import XML.Decode._
        val body = YXML.parse_body(text)
        Some(pair(long, list(pair(long, option(long))))(body))
      }
      catch {
        case ERROR(_) => None
        case _: XML.XML_Atom => None
        case _: XML.XML_Body => None
      }
  }

  object Removed
  {
    def unapply(text: String): Option[List[Document.Version_ID]] =
      try {
        import XML.Decode._
        Some(list(long)(YXML.parse_body(text)))
      }
      catch {
        case ERROR(_) => None
        case _: XML.XML_Atom => None
        case _: XML.XML_Body => None
      }
  }


  /* command status */

  object Status
  {
    val init = Status()
  }

  sealed case class Status(
    private val touched: Boolean = false,
    private val accepted: Boolean = false,
    private val failed: Boolean = false,
    forks: Int = 0,
    runs: Int = 0)
  {
    def + (that: Status): Status =
      Status(touched || that.touched, accepted || that.accepted, failed || that.failed,
        forks + that.forks, runs + that.runs)

    def is_unprocessed: Boolean = accepted && !failed && (!touched || (forks != 0 && runs == 0))
    def is_running: Boolean = runs != 0
    def is_finished: Boolean = !failed && forks == 0 && runs == 0
    def is_failed: Boolean = failed
  }

  val command_status_markup: Set[String] =
    Set(Isabelle_Markup.ACCEPTED, Isabelle_Markup.FORKED, Isabelle_Markup.JOINED,
      Isabelle_Markup.RUNNING, Isabelle_Markup.FINISHED, Isabelle_Markup.FAILED)

  def command_status(status: Status, markup: Markup): Status =
    markup match {
      case Markup(Isabelle_Markup.ACCEPTED, _) => status.copy(accepted = true)
      case Markup(Isabelle_Markup.FORKED, _) => status.copy(touched = true, forks = status.forks + 1)
      case Markup(Isabelle_Markup.JOINED, _) => status.copy(forks = status.forks - 1)
      case Markup(Isabelle_Markup.RUNNING, _) => status.copy(touched = true, runs = status.runs + 1)
      case Markup(Isabelle_Markup.FINISHED, _) => status.copy(runs = status.runs - 1)
      case Markup(Isabelle_Markup.FAILED, _) => status.copy(failed = true)
      case _ => status
    }

  def command_status(markups: List[Markup]): Status =
    (Status.init /: markups)(command_status(_, _))


  /* node status */

  sealed case class Node_Status(
    unprocessed: Int, running: Int, finished: Int, warned: Int, failed: Int)
  {
    def total: Int = unprocessed + running + finished + warned + failed
  }

  def node_status(
    state: Document.State, version: Document.Version, node: Document.Node): Node_Status =
  {
    var unprocessed = 0
    var running = 0
    var finished = 0
    var warned = 0
    var failed = 0
    node.commands.foreach(command =>
      {
        val st = state.command_state(version, command)
        val status = command_status(st.status)
        if (status.is_running) running += 1
        else if (status.is_finished) {
          if (st.results.exists(p => is_warning(p._2))) warned += 1
          else finished += 1
        }
        else if (status.is_failed) failed += 1
        else unprocessed += 1
      })
    Node_Status(unprocessed, running, finished, warned, failed)
  }


  /* result messages */

  def clean_message(body: XML.Body): XML.Body =
    body filter { case XML.Elem(Markup(Isabelle_Markup.NO_REPORT, _), _) => false case _ => true } map
      { case XML.Elem(markup, ts) => XML.Elem(markup, clean_message(ts)) case t => t }

  def message_reports(msg: XML.Tree): List[XML.Elem] =
    msg match {
      case elem @ XML.Elem(Markup(Isabelle_Markup.REPORT, _), _) => List(elem)
      case XML.Elem(_, body) => body.flatMap(message_reports)
      case XML.Text(_) => Nil
    }


  /* specific messages */

 def is_tracing(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Isabelle_Markup.TRACING, _), _) => true
      case _ => false
    }

  def is_warning(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Isabelle_Markup.WARNING, _), _) => true
      case _ => false
    }

  def is_error(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Isabelle_Markup.ERROR, _), _) => true
      case _ => false
    }

  def is_state(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Isabelle_Markup.WRITELN, _),
        List(XML.Elem(Markup(Isabelle_Markup.STATE, _), _))) => true
      case _ => false
    }

  object Sendback
  {
    def unapply(msg: Any): Option[XML.Body] =
      msg match {
        case XML.Elem(Markup(Isabelle_Markup.SENDBACK, _), body) => Some(body)
        case _ => None
      }
  }


  /* reported positions */

  private val include_pos =
    Set(Isabelle_Markup.BINDING, Isabelle_Markup.ENTITY, Isabelle_Markup.REPORT,
      Isabelle_Markup.POSITION)

  def message_positions(command: Command, message: XML.Elem): Set[Text.Range] =
  {
    def positions(set: Set[Text.Range], tree: XML.Tree): Set[Text.Range] =
      tree match {
        case XML.Elem(Markup(name, Position.Id_Range(id, raw_range)), body)
        if include_pos(name) && id == command.id =>
          val range = command.decode(raw_range).restrict(command.range)
          body.foldLeft(if (range.is_singularity) set else set + range)(positions)
        case XML.Elem(Markup(name, _), body) => body.foldLeft(set)(positions)
        case _ => set
      }
    val set = positions(Set.empty, message)
    if (set.isEmpty && !is_state(message))
      set ++ Position.Range.unapply(message.markup.properties).map(command.decode(_))
    else set
  }
}


trait Protocol extends Isabelle_Process
{
  /* commands */

  def define_command(command: Command): Unit =
    input("Document.define_command",
      Document.ID(command.id), encode(command.name), encode(command.source))


  /* document versions */

  def discontinue_execution() { input("Document.discontinue_execution") }

  def cancel_execution() { input("Document.cancel_execution") }

  def update(old_id: Document.Version_ID, new_id: Document.Version_ID,
    edits: List[Document.Edit_Command])
  {
    val edits_yxml =
    { import XML.Encode._
      def id: T[Command] = (cmd => long(cmd.id))
      def encode_edit(name: Document.Node.Name)
          : T[Document.Node.Edit[(Option[Command], Option[Command]), Command.Perspective]] =
        variant(List(
          { case Document.Node.Clear() => (Nil, Nil) },  // FIXME unused !?
          { case Document.Node.Edits(a) => (Nil, list(pair(option(id), option(id)))(a)) },
          { case Document.Node.Deps(header) =>
              val dir = Isabelle_System.posix_path(name.dir)
              val imports = header.imports.map(_.node)
              // FIXME val uses = deps.uses.map(p => (Isabelle_System.posix_path(p._1), p._2))
              val uses = header.uses
              (Nil,
                pair(Encode.string, pair(Encode.string, pair(list(Encode.string),
                  pair(list(pair(Encode.string,
                    option(pair(pair(Encode.string, list(Encode.string)), list(Encode.string))))),
                  pair(list(pair(Encode.string, bool)), list(Encode.string))))))(
                (dir, (name.theory, (imports, (header.keywords, (uses, header.errors))))))) },
          { case Document.Node.Perspective(a) => (a.commands.map(c => long_atom(c.id)), Nil) }))
      def encode_edits: T[List[Document.Edit_Command]] = list((node_edit: Document.Edit_Command) =>
      {
        val (name, edit) = node_edit
        pair(string, encode_edit(name))(name.node, edit)
      })
      YXML.string_of_body(encode_edits(edits)) }
    input("Document.update", Document.ID(old_id), Document.ID(new_id), edits_yxml)
  }

  def remove_versions(versions: List[Document.Version])
  {
    val versions_yxml =
      { import XML.Encode._
        YXML.string_of_body(list(long)(versions.map(_.id))) }
    input("Document.remove_versions", versions_yxml)
  }


  /* method invocation service */

  def invoke_scala(id: String, tag: Invoke_Scala.Tag.Value, res: String)
  {
    input("Document.invoke_scala", id, tag.toString, res)
  }
}
