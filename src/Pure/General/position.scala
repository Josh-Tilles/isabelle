/*  Title:      Pure/General/position.scala
    Author:     Makarius

Position properties.
*/

package isabelle


object Position
{
  type T = List[(String, String)]

  def get_line(pos: T): Option[Int] = Markup.get_int(Markup.LINE, pos)
  def get_column(pos: T): Option[Int] = Markup.get_int(Markup.COLUMN, pos)
  def get_offset(pos: T): Option[Int] = Markup.get_int(Markup.OFFSET, pos)
  def get_end_line(pos: T): Option[Int] = Markup.get_int(Markup.END_LINE, pos)
  def get_end_column(pos: T): Option[Int] = Markup.get_int(Markup.END_COLUMN, pos)
  def get_end_offset(pos: T): Option[Int] = Markup.get_int(Markup.END_OFFSET, pos)
  def get_file(pos: T): Option[String] = Markup.get_string(Markup.FILE, pos)
  def get_id(pos: T): Option[Long] = Markup.get_long(Markup.ID, pos)

  def get_range(pos: T): Option[Text.Range] =
    (get_offset(pos), get_end_offset(pos)) match {
      case (Some(start), Some(stop)) if start <= stop => Some(Text.Range(start, stop))
      case (Some(start), None) => Some(Text.Range(start))
      case (_, _) => None
    }

  object Id { def unapply(pos: T): Option[Long] = get_id(pos) }
  object Range { def unapply(pos: T): Option[Text.Range] = get_range(pos) }
}
