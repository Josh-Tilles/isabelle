/*  Title:      Tools/jEdit/src/completion_popup.scala
    Author:     Makarius

Completion popup.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Color, Font, Point, BorderLayout, Dimension}
import java.awt.event.{KeyEvent, MouseEvent, MouseAdapter, FocusAdapter, FocusEvent}
import javax.swing.{JPanel, JComponent, JLayeredPane, SwingUtilities}
import javax.swing.border.LineBorder
import javax.swing.text.DefaultCaret

import scala.swing.{ListView, ScrollPane}
import scala.swing.event.MouseClicked

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea, Selection}
import org.gjt.sp.jedit.gui.{HistoryTextField, KeyEventWorkaround}


object Completion_Popup
{
  /** items with HTML rendering **/

  private class Item(val item: Completion.Item)
  {
    private val html =
      item.description match {
        case a :: bs =>
          "<html><b>" + HTML.encode(a) + "</b>" +
            HTML.encode(bs.map(" " + _).mkString) + "</html>"
        case Nil => ""
      }
    override def toString: String = html
  }



  /** jEdit text area **/

  object Text_Area
  {
    private val key = new Object

    def apply(text_area: TextArea): Option[Completion_Popup.Text_Area] =
    {
      Swing_Thread.require()
      text_area.getClientProperty(key) match {
        case text_area_completion: Completion_Popup.Text_Area => Some(text_area_completion)
        case _ => None
      }
    }

    def active_range(text_area: TextArea): Option[Text.Range] =
      apply(text_area) match {
        case Some(text_area_completion) => text_area_completion.active_range
        case None => None
      }

    def action(text_area: TextArea): Boolean =
      apply(text_area) match {
        case Some(text_area_completion) =>
          if (text_area_completion.active_range.isDefined)
            text_area_completion.action()
          else
            text_area_completion.action(immediate = true, explicit = true)
          true
        case None => false
      }

    def exit(text_area: JEditTextArea)
    {
      Swing_Thread.require()
      apply(text_area) match {
        case None =>
        case Some(text_area_completion) =>
          text_area_completion.deactivate()
          text_area.putClientProperty(key, null)
      }
    }

    def init(text_area: JEditTextArea): Completion_Popup.Text_Area =
    {
      exit(text_area)
      val text_area_completion = new Text_Area(text_area)
      text_area.putClientProperty(key, text_area_completion)
      text_area_completion.activate()
      text_area_completion
    }

    def dismissed(text_area: TextArea): Boolean =
    {
      Swing_Thread.require()
      apply(text_area) match {
        case Some(text_area_completion) => text_area_completion.dismissed()
        case None => false
      }
    }
  }

  class Text_Area private(text_area: JEditTextArea)
  {
    // owned by Swing thread
    private var completion_popup: Option[Completion_Popup] = None

    def active_range: Option[Text.Range] =
      completion_popup match {
        case Some(completion) =>
          completion.active_range match {
            case Some(range) if completion.isDisplayable => Some(range)
            case _ => None
          }
        case None => None
      }


    /* caret */

    def before_caret_range(rendering: Rendering): Text.Range =
    {
      val snapshot = rendering.snapshot
      val former_caret = snapshot.revert(text_area.getCaretPosition)
      snapshot.convert(Text.Range(former_caret - 1, former_caret))
    }


    /* rendering */

    def rendering(rendering: Rendering, line_range: Text.Range): Option[Text.Info[Color]] =
    {
      active_range match {
        case Some(range) => range.try_restrict(line_range)
        case None =>
          val buffer = text_area.getBuffer
          if (line_range.contains(text_area.getCaretPosition)) {
            before_caret_range(rendering).try_restrict(line_range) match {
              case Some(range) if !range.is_singularity =>
                rendering.semantic_completion(range) match {
                  case Some(Text.Info(_, Completion.No_Completion)) => None
                  case Some(Text.Info(range1, _: Completion.Names)) => Some(range1)
                  case None =>
                    syntax_completion(Completion.History.empty, false, Some(rendering)).map(_.range)
                }
              case _ => None
            }
          }
          else None
      }
    }.map(range => Text.Info(range, rendering.completion_color))


    /* syntax completion */

    def syntax_completion(
      history: Completion.History,
      explicit: Boolean,
      opt_rendering: Option[Rendering]): Option[Completion.Result] =
    {
      val buffer = text_area.getBuffer
      val decode = Isabelle_Encoding.is_active(buffer)

      Isabelle.mode_syntax(JEdit_Lib.buffer_mode(buffer)) match {
        case Some(syntax) =>
          val caret = text_area.getCaretPosition

          val line = buffer.getLineOfOffset(caret)
          val line_start = buffer.getLineStartOffset(line)
          val line_length = (buffer.getLineEndOffset(line) min buffer.getLength) - line_start
          val line_text = buffer.getSegment(line_start, line_length)

          val context =
            (opt_rendering match {
              case Some(rendering) =>
                rendering.language_context(before_caret_range(rendering))
              case None => None
            }) getOrElse syntax.language_context

          syntax.completion.complete(
            history, decode, explicit, line_start, line_text, caret - line_start, false, context)

        case None => None
      }
    }


    /* spell-checker completion */

    def spell_checker_completion(rendering: Rendering): Option[Completion.Result] =
    {
      PIDE.spell_checker.get match {
        case Some(spell_checker) =>
          val caret_range = before_caret_range(rendering)

          val result =
            for {
              spell_range <- rendering.spell_checker_point(caret_range)
              text <- JEdit_Lib.try_get_text(text_area.getBuffer, spell_range)
              info <-
                Spell_Checker.marked_words(spell_range.start, text,
                  info => info.range.overlaps(caret_range)).headOption
            } yield info

          result match {
            case Some(Text.Info(range, original)) =>
              val words = spell_checker.complete(original)
              if (words.isEmpty) None
              else {
                val descr = "(from dictionary " + quote(spell_checker.toString) + ")"
                val items = words.map(word =>
                  Completion.Item(range, original, "", List(word, descr), word, 0, false))
                Some(Completion.Result(range, original, false, items))
              }
            case None => None
          }
        case None => None
      }
    }


    /* completion action: text area */

    private def insert(item: Completion.Item)
    {
      Swing_Thread.require()

      val buffer = text_area.getBuffer
      val range = item.range
      if (buffer.isEditable && range.length > 0) {
        JEdit_Lib.buffer_edit(buffer) {
          JEdit_Lib.try_get_text(buffer, range) match {
            case Some(text) if text == item.original =>
              text_area.getSelectionAtOffset(text_area.getCaretPosition) match {

                /*rectangular selection as "tall caret"*/
                case selection : Selection.Rect
                if selection.getStart(buffer, text_area.getCaretLine) == range.stop =>
                  text_area.moveCaretPosition(range.stop)
                  (0 until Character.codePointCount(item.original, 0, item.original.length))
                    .foreach(_ => text_area.backspace())
                  text_area.setSelectedText(selection, item.replacement)
                  text_area.moveCaretPosition(text_area.getCaretPosition + item.move)

                /*other selections: rectangular, multiple range, ...*/
                case selection
                if selection != null &&
                    selection.getStart(buffer, text_area.getCaretLine) == range.start &&
                    selection.getEnd(buffer, text_area.getCaretLine) == range.stop =>
                  text_area.moveCaretPosition(range.stop + item.move)
                  text_area.getSelection.foreach(text_area.setSelectedText(_, item.replacement))

                /*no selection*/
                case _ =>
                  buffer.remove(range.start, range.length)
                  buffer.insert(range.start, item.replacement)
                  text_area.moveCaretPosition(range.start + item.replacement.length + item.move)
              }
            case _ =>
          }
        }
      }
    }

    def action(immediate: Boolean = false, explicit: Boolean = false, delayed: Boolean = false)
      : Boolean =
    {
      val view = text_area.getView
      val layered = view.getLayeredPane
      val buffer = text_area.getBuffer
      val painter = text_area.getPainter

      val history = PIDE.completion_history.value
      val decode = Isabelle_Encoding.is_active(buffer)

      def open_popup(result: Completion.Result)
      {
        val font =
          painter.getFont.deriveFont(
            Font_Info.main_size(PIDE.options.real("jedit_popup_font_scale")))

        val range = result.range
        def invalidate(): Unit = JEdit_Lib.invalidate_range(text_area, range)

        val loc1 = text_area.offsetToXY(range.start)
        if (loc1 != null) {
          val loc2 =
            SwingUtilities.convertPoint(painter,
              loc1.x, loc1.y + painter.getFontMetrics.getHeight, layered)

          val items = result.items.map(new Item(_))
          val completion =
            new Completion_Popup(Some(range), layered, loc2, font, items)
            {
              override def complete(item: Completion.Item) {
                PIDE.completion_history.update(item)
                insert(item)
              }
              override def propagate(evt: KeyEvent) {
                if (view.getKeyEventInterceptor == inner_key_listener) {
                  try {
                    view.setKeyEventInterceptor(null)
                    JEdit_Lib.propagate_key(view, evt)
                  }
                  finally {
                    if (isDisplayable) view.setKeyEventInterceptor(inner_key_listener)
                  }
                }
                if (evt.getID == KeyEvent.KEY_TYPED) input(evt)
              }
              override def shutdown(focus: Boolean) {
                if (view.getKeyEventInterceptor == inner_key_listener)
                  view.setKeyEventInterceptor(null)
                if (focus) text_area.requestFocus
                invalidate()
              }
            }
          completion_popup = Some(completion)
          view.setKeyEventInterceptor(completion.inner_key_listener)
          invalidate()
          completion.show_popup(false)
        }
      }

      if (buffer.isEditable) {
        val (no_completion, semantic_completion, opt_rendering) =
        {
          PIDE.document_view(text_area) match {
            case Some(doc_view) =>
              val rendering = doc_view.get_rendering()
              val (no_completion, result) =
                rendering.semantic_completion(before_caret_range(rendering)) match {
                  case Some(Text.Info(_, Completion.No_Completion)) =>
                    (true, None)
                  case Some(Text.Info(range, names: Completion.Names)) =>
                    val result =
                      JEdit_Lib.try_get_text(buffer, range) match {
                        case Some(original) => names.complete(range, history, decode, original)
                        case None => None
                      }
                    (false, result)
                  case None =>
                    (false, None)
                }
              (no_completion, result, Some(rendering))
            case None =>
              (false, None, None)
          }
        }
        if (no_completion) false
        else {
          val result0 =
            Completion.Result.merge(history,
              semantic_completion, syntax_completion(history, explicit, opt_rendering))
          val result =
            opt_rendering match {
              case None => result0
              case Some(rendering) =>
                Completion.Result.merge(history, result0, spell_checker_completion(rendering))
            }

          result match {
            case Some(result) =>
              result.items match {
                case List(item) if result.unique && item.immediate && immediate =>
                  insert(item)
                  true
                case _ :: _ if !delayed =>
                  open_popup(result)
                  false
                case _ => false
              }
            case None => false
          }
        }
      }
      else false
    }


    /* input key events */

    def input(evt: KeyEvent)
    {
      Swing_Thread.require()

      if (PIDE.options.bool("jedit_completion")) {
        if (!evt.isConsumed) {
          dismissed()
          if (evt.getKeyChar != '\b') {
            val special = JEdit_Lib.special_key(evt)
            val immediate = PIDE.options.bool("jedit_completion_immediate")
            if (PIDE.options.seconds("jedit_completion_delay").is_zero && !special) {
              input_delay.revoke()
              action(immediate = immediate)
            }
            else {
              if (!special && action(immediate = immediate, delayed = true))
                input_delay.revoke()
              else
                input_delay.invoke()
            }
          }
        }
      }
    }

    private val input_delay =
      Swing_Thread.delay_last(PIDE.options.seconds("jedit_completion_delay")) {
        action()
      }


    /* dismiss popup */

    def dismissed(): Boolean =
    {
      Swing_Thread.require()

      completion_popup match {
        case Some(completion) =>
          completion.hide_popup()
          completion_popup = None
          true
        case None =>
          false
      }
    }


    /* activation */

    private val outer_key_listener =
      JEdit_Lib.key_listener(key_typed = input _)

    private def activate()
    {
      text_area.addKeyListener(outer_key_listener)
    }

    private def deactivate()
    {
      dismissed()
      text_area.removeKeyListener(outer_key_listener)
    }
  }



  /** history text field **/

  class History_Text_Field(
    name: String = null,
    instant_popups: Boolean = false,
    enter_adds_to_history: Boolean = true,
    syntax: Outer_Syntax = Outer_Syntax.init) extends
    HistoryTextField(name, instant_popups, enter_adds_to_history)
  {
    text_field =>

    // see https://forums.oracle.com/thread/1361677
    if (GUI.is_macos_laf) text_field.setCaret(new DefaultCaret)

    // owned by Swing thread
    private var completion_popup: Option[Completion_Popup] = None


    /* dismiss */

    private def dismissed(): Boolean =
    {
      completion_popup match {
        case Some(completion) =>
          completion.hide_popup()
          completion_popup = None
          true
        case None =>
          false
      }
    }


    /* insert */

    private def insert(item: Completion.Item)
    {
      Swing_Thread.require()

      val range = item.range
      if (text_field.isEditable && range.length > 0) {
        val content = text_field.getText
        JEdit_Lib.try_get_text(content, range) match {
          case Some(text) if text == item.original =>
            text_field.setText(
              content.substring(0, range.start) +
              item.replacement +
              content.substring(range.stop))
            text_field.getCaret.setDot(range.start + item.replacement.length + item.move)
          case _ =>
        }
      }
    }


    /* completion action: text field */

    def action()
    {
      GUI.layered_pane(text_field) match {
        case Some(layered) if text_field.isEditable =>
          val history = PIDE.completion_history.value

          val caret = text_field.getCaret.getDot
          val text = text_field.getText

          val context = syntax.language_context

          syntax.completion.complete(history, true, false, 0, text, caret, false, context) match {
            case Some(result) =>
              val fm = text_field.getFontMetrics(text_field.getFont)
              val loc =
                SwingUtilities.convertPoint(text_field, fm.stringWidth(text), fm.getHeight, layered)

              val items = result.items.map(new Item(_))
              val completion =
                new Completion_Popup(None, layered, loc, text_field.getFont, items)
                {
                  override def complete(item: Completion.Item) {
                    PIDE.completion_history.update(item)
                    insert(item)
                  }
                  override def propagate(evt: KeyEvent) {
                    if (!evt.isConsumed) text_field.processKeyEvent(evt)
                  }
                  override def shutdown(focus: Boolean) { if (focus) text_field.requestFocus }
                }
              completion_popup = Some(completion)
              completion.show_popup(true)

            case None =>
          }
        case _ =>
      }
    }


    /* process key event */

    private def process(evt: KeyEvent)
    {
      if (PIDE.options.bool("jedit_completion")) {
        dismissed()
        if (evt.getKeyChar != '\b') {
          val special = JEdit_Lib.special_key(evt)
          if (PIDE.options.seconds("jedit_completion_delay").is_zero && !special) {
            process_delay.revoke()
            action()
          }
          else process_delay.invoke()
        }
      }
    }

    private val process_delay =
      Swing_Thread.delay_last(PIDE.options.seconds("jedit_completion_delay")) {
        action()
      }

    override def processKeyEvent(evt0: KeyEvent)
    {
      val evt = KeyEventWorkaround.processKeyEvent(evt0)
      if (evt != null) {
        evt.getID match {
          case KeyEvent.KEY_PRESSED =>
            val key_code = evt.getKeyCode
            if (key_code == KeyEvent.VK_ESCAPE) {
              if (dismissed()) evt.consume
            }
          case KeyEvent.KEY_TYPED =>
            super.processKeyEvent(evt)
            process(evt)
            evt.consume
          case _ =>
        }
        if (!evt.isConsumed) super.processKeyEvent(evt)
      }
    }
  }
}


class Completion_Popup private(
  val active_range: Option[Text.Range],
  layered: JLayeredPane,
  location: Point,
  font: Font,
  items: List[Completion_Popup.Item]) extends JPanel(new BorderLayout)
{
  completion =>

  Swing_Thread.require()

  require(!items.isEmpty)
  val multi = items.length > 1


  /* actions */

  def complete(item: Completion.Item) { }
  def propagate(evt: KeyEvent) { }
  def shutdown(focus: Boolean) { }


  /* list view */

  private val list_view = new ListView(items)
  list_view.font = font
  list_view.selection.intervalMode = ListView.IntervalMode.Single
  list_view.peer.setFocusTraversalKeysEnabled(false)
  list_view.peer.setVisibleRowCount(items.length min 8)
  list_view.peer.setSelectedIndex(0)

  for (cond <-
    List(JComponent.WHEN_FOCUSED,
      JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT,
      JComponent.WHEN_IN_FOCUSED_WINDOW)) list_view.peer.setInputMap(cond, null)

  private def complete_selected(): Boolean =
  {
    list_view.selection.items.toList match {
      case item :: _ => complete(item.item); true
      case _ => false
    }
  }

  private def move_items(n: Int)
  {
    val i = list_view.peer.getSelectedIndex
    val j = ((i + n) min (items.length - 1)) max 0
    if (i != j) {
      list_view.peer.setSelectedIndex(j)
      list_view.peer.ensureIndexIsVisible(j)
    }
  }

  private def move_pages(n: Int)
  {
    val page_size = list_view.peer.getVisibleRowCount - 1
    move_items(page_size * n)
  }


  /* event handling */

  val inner_key_listener =
    JEdit_Lib.key_listener(
      key_pressed = (e: KeyEvent) =>
        {
          if (!e.isConsumed) {
            e.getKeyCode match {
              case KeyEvent.VK_TAB =>
                if (complete_selected()) e.consume
                hide_popup()
              case KeyEvent.VK_ESCAPE =>
                hide_popup()
                e.consume
              case KeyEvent.VK_UP | KeyEvent.VK_KP_UP if multi =>
                move_items(-1)
                e.consume
              case KeyEvent.VK_DOWN | KeyEvent.VK_KP_DOWN if multi =>
                move_items(1)
                e.consume
              case KeyEvent.VK_PAGE_UP if multi =>
                move_pages(-1)
                e.consume
              case KeyEvent.VK_PAGE_DOWN if multi =>
                move_pages(1)
                e.consume
              case _ =>
                if (e.isActionKey || e.isAltDown || e.isMetaDown || e.isControlDown)
                  hide_popup()
            }
          }
          propagate(e)
        },
      key_typed = propagate _
    )

  list_view.peer.addKeyListener(inner_key_listener)

  list_view.peer.addMouseListener(new MouseAdapter {
    override def mouseClicked(e: MouseEvent) {
      if (complete_selected()) e.consume
      hide_popup()
    }
  })

  list_view.peer.addFocusListener(new FocusAdapter {
    override def focusLost(e: FocusEvent) { hide_popup() }
  })


  /* main content */

  override def getFocusTraversalKeysEnabled = false
  completion.setBorder(new LineBorder(Color.BLACK))
  completion.add((new ScrollPane(list_view)).peer.asInstanceOf[JComponent])


  /* popup */

  private val popup =
  {
    val screen = JEdit_Lib.screen_location(layered, location)
    val size =
    {
      val geometry = JEdit_Lib.window_geometry(completion, completion)
      val bounds = Rendering.popup_bounds
      val w = geometry.width min (screen.bounds.width * bounds).toInt min layered.getWidth
      val h = geometry.height min (screen.bounds.height * bounds).toInt min layered.getHeight
      new Dimension(w, h)
    }
    new Popup(layered, completion, screen.relative(layered, size), size)
  }

  private def show_popup(focus: Boolean)
  {
    popup.show
    if (focus) list_view.requestFocus
  }

  private def hide_popup()
  {
    shutdown(list_view.peer.isFocusOwner)
    popup.hide
  }
}

