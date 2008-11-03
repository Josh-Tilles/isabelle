package isabelle.jedit


import java.awt.GridLayout
import javax.swing.{ JPanel, JScrollPane }

import isabelle.IsabelleSystem.getenv

import org.w3c.dom.Document

import org.xhtmlrenderer.simple.XHTMLPanel
import org.xhtmlrenderer.context.AWTFontResolver

import org.gjt.sp.jedit.View

class StateViewDockable(view : View, position : String) extends JPanel {
  {
    val panel = new XHTMLPanel(new UserAgent())
    setLayout(new GridLayout(1, 1))
    add(new JScrollPane(panel))
    
    val fontResolver =
      panel.getSharedContext.getFontResolver.asInstanceOf[AWTFontResolver]
    if (Plugin.plugin.viewFont != null)
      fontResolver.setFontMapping("Isabelle", Plugin.plugin.viewFont)

    Plugin.plugin.viewFontChanged.add(font => {
      if (Plugin.plugin.viewFont != null)
        fontResolver.setFontMapping("Isabelle", Plugin.plugin.viewFont)
      
      panel.relayout()
    })
    
    Plugin.plugin.stateUpdate.add(state => {
      if (state == null)
        panel.setDocument(null : Document)
      else
        panel.setDocument(state.document, UserAgent.baseURL)
    })
  }
}
