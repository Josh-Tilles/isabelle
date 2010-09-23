/*  Title:      Tools/jEdit/src/jedit/session_dockable.scala
    Author:     Makarius

Dockable window for prover session management.
*/

package isabelle.jedit


import isabelle._

import scala.actors.Actor._
import scala.swing.{FlowPanel, Button, TextArea, ScrollPane, TabbedPane, Component}
import scala.swing.event.ButtonClicked

import java.awt.BorderLayout

import org.gjt.sp.jedit.View


class Session_Dockable(view: View, position: String) extends Dockable(view: View, position: String)
{
  /* main tabs */

  private val readme = new HTML_Panel(Isabelle.system, "SansSerif", 12)
  readme.render_document(Isabelle.system.try_read(List("$JEDIT_HOME/README.html")))

  private def session_syslog(): String =
    Isabelle.session.syslog.map(msg => XML.content(msg).mkString).mkString("\n")

  private val syslog = new TextArea(session_syslog())
  syslog.editable = false

  private val tabs = new TabbedPane {
    pages += new TabbedPane.Page("README", Component.wrap(readme))
    pages += new TabbedPane.Page("System log", new ScrollPane(syslog))
  }

  set_content(tabs)


  /* controls */

  private val interrupt = new Button("Interrupt") {
    reactions += { case ButtonClicked(_) => Isabelle.session.interrupt }
  }
  interrupt.tooltip = "Broadcast interrupt to all prover tasks"

  private val controls = new FlowPanel(FlowPanel.Alignment.Right)(interrupt)
  add(controls.peer, BorderLayout.NORTH)


  /* main actor */

  private val main_actor = actor {
    loop {
      react {
        case result: Isabelle_Process.Result =>
          if (result.is_syslog)
            Swing_Thread.now {
              val text = session_syslog()
              if (text != syslog.text) {
                syslog.text = text
              }
            }

        case bad => System.err.println("Session_Dockable: ignoring bad message " + bad)
      }
    }
  }

  override def init() { Isabelle.session.raw_messages += main_actor }
  override def exit() { Isabelle.session.raw_messages -= main_actor }
}
