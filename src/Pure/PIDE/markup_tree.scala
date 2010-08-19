/*  Title:      Pure/PIDE/markup_tree.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Markup trees over nested / non-overlapping text ranges.
*/

package isabelle


import javax.swing.tree.DefaultMutableTreeNode

import scala.collection.immutable.SortedMap
import scala.collection.mutable
import scala.annotation.tailrec


object Markup_Tree
{
  case class Node(val range: Text.Range, val info: Any)
  {
    def contains(that: Node): Boolean = this.range contains that.range
  }


  /* branches sorted by quasi-order -- overlapping intervals appear as equivalent */

  object Branches
  {
    type Entry = (Node, Markup_Tree)
    type T = SortedMap[Node, Entry]

    val empty = SortedMap.empty[Node, Entry](new scala.math.Ordering[Node]
      {
        def compare(x: Node, y: Node): Int = x.range compare y.range
      })
    def update(branches: T, entries: Entry*): T =
      branches ++ entries.map(e => (e._1 -> e))
  }

  val empty = new Markup_Tree(Branches.empty)
}


case class Markup_Tree(val branches: Markup_Tree.Branches.T)
{
  import Markup_Tree._

  def + (new_node: Node): Markup_Tree =
  {
    branches.get(new_node) match {
      case None =>
        new Markup_Tree(Branches.update(branches, new_node -> empty))
      case Some((node, subtree)) =>
        if (node.range != new_node.range && node.contains(new_node))
          new Markup_Tree(Branches.update(branches, node -> (subtree + new_node)))
        else if (new_node.contains(branches.head._1) && new_node.contains(branches.last._1))
          new Markup_Tree(Branches.update(Branches.empty, (new_node -> this)))
        else {
          var overlapping = Branches.empty
          var rest = branches
          while (rest.isDefinedAt(new_node)) {
            overlapping = Branches.update(overlapping, rest(new_node))
            rest -= new_node
          }
          if (overlapping.forall(e => new_node.contains(e._1)))
            new Markup_Tree(Branches.update(rest, new_node -> new Markup_Tree(overlapping)))
          else { // FIXME split markup!?
            System.err.println("Ignored overlapping markup: " + new_node)
            this
          }
        }
    }
  }

  // FIXME depth-first with result markup stack
  // FIXME projection to given range
  def flatten(parent: Node): List[Node] =
  {
    val result = new mutable.ListBuffer[Node]
    var offset = parent.range.start
    for ((_, (node, subtree)) <- branches.iterator) {
      if (offset < node.range.start)
        result += new Node(Text.Range(offset, node.range.start), parent.info)
      result ++= subtree.flatten(node)
      offset = node.range.stop
    }
    if (offset < parent.range.stop)
      result += new Node(Text.Range(offset, parent.range.stop), parent.info)
    result.toList
  }

  def filter(pred: Node => Boolean): Markup_Tree =
  {
    val bs = branches.toList.flatMap(entry => {
      val (_, (node, subtree)) = entry
      if (pred(node)) List((node, (node, subtree.filter(pred))))
      else subtree.filter(pred).branches.toList
    })
    new Markup_Tree(Branches.empty ++ bs)
  }

  def swing_tree(parent: DefaultMutableTreeNode)(swing_node: Node => DefaultMutableTreeNode)
  {
    for ((_, (node, subtree)) <- branches) {
      val current = swing_node(node)
      subtree.swing_tree(current)(swing_node)
      parent.add(current)
    }
  }
}

