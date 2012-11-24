/*  Title:      Tools/jEdit/src/plugin.scala
    Author:     Makarius

Convenience actions for Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.Buffer
import org.gjt.sp.jedit.textarea.JEditTextArea


object Isabelle_Actions
{
  /* full checking */

  def check_buffer(buffer: Buffer)
  {
    Isabelle.document_model(buffer) match {
      case None =>
      case Some(model) => model.full_perspective()
    }
  }


  def cancel_execution() { Isabelle.session.cancel_execution() }

  /* control styles */

  def control_sub(text_area: JEditTextArea)
  { Token_Markup.edit_ctrl_style(text_area, Symbol.sub_decoded) }

  def control_sup(text_area: JEditTextArea)
  { Token_Markup.edit_ctrl_style(text_area, Symbol.sup_decoded) }

  def control_isub(text_area: JEditTextArea)
  { Token_Markup.edit_ctrl_style(text_area, Symbol.isub_decoded) }

  def control_isup(text_area: JEditTextArea)
  { Token_Markup.edit_ctrl_style(text_area, Symbol.isup_decoded) }

  def control_bold(text_area: JEditTextArea)
  { Token_Markup.edit_ctrl_style(text_area, Symbol.bold_decoded) }

  def control_reset(text_area: JEditTextArea)
  { Token_Markup.edit_ctrl_style(text_area, "") }


  /* block styles */

  private def enclose_input(text_area: JEditTextArea, s1: String, s2: String)
  {
    s1.foreach(text_area.userInput(_))
    s2.foreach(text_area.userInput(_))
    s2.foreach(_ => text_area.goToPrevCharacter(false))
  }

  def input_bsub(text_area: JEditTextArea)
  { enclose_input(text_area, Symbol.bsub_decoded, Symbol.esub_decoded) }

  def input_bsup(text_area: JEditTextArea)
  { enclose_input(text_area, Symbol.bsup_decoded, Symbol.esup_decoded) }
}

