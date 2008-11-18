/*
 * ScrollerDockable.scala
 *
 * TODO: 
 * + scrolling *one* panel 
 */

package isabelle.jedit

import scala.collection.mutable.{ArrayBuffer, HashMap}

import java.awt.{ BorderLayout, Adjustable }
import java.awt.event.{ ActionListener, ActionEvent, AdjustmentListener, AdjustmentEvent, ComponentListener, ComponentEvent }
import javax.swing.{ JFrame, JPanel, JRadioButton, JScrollBar, JTextArea, Timer }

import org.w3c.dom.Document

import org.xhtmlrenderer.simple.XHTMLPanel
import org.xhtmlrenderer.context.AWTFontResolver

import org.gjt.sp.jedit.View

trait Unrendered[T] {
  def addUnrendered (id: Int, u: T) : Unit
  def getUnrendered (id: Int) : Option[T]
  def size : Int
}

trait Rendered[T] {
  def getRendered (id: Int) : Option[T]
}

object Renderer {
  def render (message: Document): XHTMLPanel = {
    val panel = new XHTMLPanel(new UserAgent())
    val fontResolver =
      panel.getSharedContext.getFontResolver.asInstanceOf[AWTFontResolver]
    if (Plugin.plugin.viewFont != null)
      fontResolver.setFontMapping("Isabelle", Plugin.plugin.viewFont)

    Plugin.plugin.viewFontChanged.add(font => {
      if (Plugin.plugin.viewFont != null)
        fontResolver.setFontMapping("Isabelle", Plugin.plugin.viewFont)
      panel.relayout()
    })
    panel.setDocument(message, UserAgent.baseURL)
    panel
  }
  
  def relayout_panel (panel: XHTMLPanel, width : Int) {
    // ATTENTION:
    // panel has to be displayable in a frame/container message_view for doDocumentLayout to have
    // an effect, especially returning correct preferredSize
    panel.setBounds (0, 0, width, 1) // document has to fit into width
    panel.doDocumentLayout (panel.getGraphics) //lay out, preferred size is set then
    // if there are thousands of empty panels, all have to be rendered -
    // but this takes time (even for empty panels); therefore minimum size
    panel.setPreferredSize(new java.awt.Dimension(width,Math.max(25, panel.getPreferredSize.getHeight.toInt)))
  }

}

class MessagePanel(cache: Rendered[XHTMLPanel]) extends JPanel {
  // defining the current view
  var offset = 0 //how many pixels of the lowest message are hidden
  var no = -1  //index of the lowest message

  // preferences
  val scrollunit = 5
  setLayout(null)
  
  // place the bottom of the message at y-coordinate and return the rendered panel
  def place_message (message_no: Int, y: Int) = {
    //add panel to cache if necessary and possible
    cache.getRendered(message_no) match {
      case Some(panel) => {
        //panel has to be displayable before calculating preferred size!
        add(panel)
        // recalculate preferred size after resizing the message_view
        if(panel.getPreferredSize.getWidth.toInt != getWidth){
          Renderer.relayout_panel (panel, getWidth)
        }
        val width = panel.getPreferredSize.getWidth.toInt
        val height = panel.getPreferredSize.getHeight.toInt
        panel.setBounds(0, y - height, width, height)
        panel
      }
      case None => null
    }
  }

  //move view a given amount of pixels
  // attention: y should be small, because messages are rendered incremental
  // (no knowledge on height of messages)
  def move_view (y : Int) = {
    var update = false
    if(getComponentCount >= 1){
      offset += y
      //remove bottommost panels
      while (offset >= getComponent(0).getHeight)
      {
        offset -= getComponent(0).getHeight
        no -= 1
        invalidate
        update = true
      }
      //insert panels at the bottom
      while (offset < 0) {
        no += 1
        val panel = place_message (no, 0)
        offset += panel.getHeight
        invalidate
        update = true
     }
      //insert panel at the top
      if (getComponent(getComponentCount - 1).getY + y > 0){
        invalidate
        update = true
      }
      //simply move panels
      if(!update){
        getComponents map (c => {
            val newrect = c.getBounds
            newrect.y = newrect.y + y
            c.setBounds(newrect)
          })
        repaint()
      } else {
        //vscroll.setValue(no)
        //TODO: create method to update vscroll
        System.err.println("lookatme2")
      }
    }
  }
  
  override def doLayout = {
    removeAll()
    var n = no
    var y:Int = getHeight + offset
    while (y >= 0 && n >= 0){
      val panel = place_message (n, y)
      panel.setBorder(javax.swing.border.LineBorder.createBlackLineBorder)
      y = y - panel.getHeight
      n = n - 1
    }
  }  
}

class InfoPanel extends JPanel {
  val auto_scroll = new JRadioButton("Auto Scroll", false)
  val message_ind = new JTextArea("0")
  add(message_ind)
  add(auto_scroll)
  
  def isAutoScroll = auto_scroll.isSelected
  def setIndicator(b: Boolean) = {
    message_ind.setBackground(if (b) java.awt.Color.red else java.awt.Color.white)
  }
  def setText(s: String) {
    message_ind.setText(s)
  }
  
}

class ScrollerDockable(view : View, position : String) extends JPanel with AdjustmentListener {

  val buffer:Unrendered[Document] = new MessageBuffer()
  val cache:Rendered[XHTMLPanel] = new PanelCache(buffer)
  
  // set up view
  val message_panel = new MessagePanel(cache)
  val infopanel = new InfoPanel
  val vscroll = new JScrollBar(Adjustable.VERTICAL, 0, 1, 0, 1)
  vscroll.addAdjustmentListener(this)
  
  setLayout(new BorderLayout())
  add (vscroll, BorderLayout.EAST)
  add (message_panel, BorderLayout.CENTER)
  add (infopanel, BorderLayout.SOUTH)
  
  // do not show every new message, wait a certain amount of time
  val message_ind_timer : Timer = new Timer(250, new ActionListener {
      // this method is called to indicate a new message
      override def actionPerformed(e:ActionEvent){
        //fire scroll-event if necessary and wanted
        if(message_panel.no != buffer.size && infopanel.isAutoScroll) {
          vscroll.setValue(buffer.size - 1)
        }
        infopanel.setIndicator(false)
      }
    })

  def add_message (message: Document) = {
    buffer.addUnrendered(buffer.size, message)
    vscroll.setMaximum (Math.max(1, buffer.size))
    infopanel.setIndicator(true)
    infopanel.setText(buffer.size.toString)

    if (! message_ind_timer.isRunning()){
      if(infopanel.isAutoScroll){
        vscroll.setValue(buffer.size - 1)
      }
      message_ind_timer.setRepeats(false)
      message_ind_timer.start()
    }

    if(message_panel.no == -1) {
      message_panel.no = 0
      message_panel.invalidate
    }
  }

  override def adjustmentValueChanged (e : AdjustmentEvent) = {
    //event-handling has to be so general (without UNIT_INCR,...)
    // because all events could be sent as TRACK e.g. on my mac
    if (e.getSource == vscroll){
        message_panel.no = e.getValue
        message_panel.offset = 0
        message_panel.invalidate
        System.err.println("event: "+message_panel.no)
        vscroll.setModel(new javax.swing.DefaultBoundedRangeModel(99,1,0,1000))
        System.err.println("hello"+e.getValue)
    }
  }

  
  // TODO: register somewhere
  // here only 'emulation of message stream'
  Plugin.plugin.stateUpdate.add(state => {
    var i = 0
    if(state != null) new Thread{
      override def run() {
        while (i < 1) {
          add_message(state.document)
          i += 1
          try {Thread.sleep(3)}
          catch{case _ =>}
        }
      }
    }.start
  })
}



//containing the unrendered messages
class MessageBuffer extends HashMap[Int,Document] with Unrendered[Document]{
  override def addUnrendered (id: Int, m: Document) {
    update(id, m)
  }
  override def getUnrendered (id: Int): Option[Document] = {
    if(id < size && id >= 0 && apply(id) != null) Some (apply(id))
    else None
  }
  override def size = super.size
}

//containing the rendered messages
class PanelCache (buffer: Unrendered[Document]) extends HashMap[Int, XHTMLPanel] with Rendered[XHTMLPanel]{
  override def getRendered (id: Int): Option[XHTMLPanel] = {
    //get message from buffer and render it if necessary
    if(!isDefinedAt(id)){
      buffer.getUnrendered(id) match {
        case Some (message) =>
          update (id, Renderer.render (message))
        case None =>
      }
    }
    val result = try {
      Some (apply(id))
    } catch {
      case _ => {
          None
      }
    }
    return result
  }
}