/*  Title:      Pure/Concurrent/counter.scala
    Author:     Makarius

Synchronized counter for unique identifiers < 0.

NB: ML ticks forwards, JVM ticks backwards.
*/

package isabelle


object Counter
{
  type ID = Long
}

class Counter
{
  private var count: Counter.ID = 0

  def apply(): Counter.ID = synchronized {
    require(count > java.lang.Long.MIN_VALUE)
    count -= 1
    count
  }
}

