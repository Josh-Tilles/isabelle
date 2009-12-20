/*  Title:      Pure/General/scan.scala
    Author:     Makarius

Efficient scanning of keywords.
*/

package isabelle

import scala.util.parsing.combinator.RegexParsers


object Scan
{
  /** Lexicon -- position tree **/

  object Lexicon
  {
    private case class Tree(val branches: Map[Char, (String, Tree)])
    private val empty_tree = Tree(Map())

    val empty: Lexicon = new Lexicon
    def apply(elems: String*): Lexicon = empty ++ elems
  }

  class Lexicon extends scala.collection.Set[String] with RegexParsers
  {
    /* representation */

    import Lexicon.Tree
    protected val main_tree: Tree = Lexicon.empty_tree


    /* auxiliary operations */

    private def content(tree: Tree, result: List[String]): List[String] =
      (result /: tree.branches.toList) ((res, entry) =>
        entry match { case (_, (s, tr)) =>
          if (s.isEmpty) content(tr, res) else content(tr, s :: res) })

    private def lookup(str: CharSequence): Option[(Boolean, Tree)] =
    {
      val len = str.length
      def look(tree: Tree, tip: Boolean, i: Int): Option[(Boolean, Tree)] =
      {
        if (i < len) {
          tree.branches.get(str.charAt(i)) match {
            case Some((s, tr)) => look(tr, !s.isEmpty, i + 1)
            case None => None
          }
        } else Some(tip, tree)
      }
      look(main_tree, false, 0)
    }

    def completions(str: CharSequence): List[String] =
      lookup(str) match {
        case Some((true, tree)) => content(tree, List(str.toString))
        case Some((false, tree)) => content(tree, Nil)
        case None => Nil
      }


    /* Set methods */

    override def stringPrefix = "Lexicon"

    override def isEmpty: Boolean = { main_tree.branches.isEmpty }

    def size: Int = content(main_tree, Nil).length
    def elements: Iterator[String] = content(main_tree, Nil).sort(_ <= _).elements

    def contains(elem: String): Boolean =
      lookup(elem) match {
        case Some((tip, _)) => tip
        case _ => false
      }

    def + (elem: String): Lexicon =
      if (contains(elem)) this
      else {
        val len = elem.length
        def extend(tree: Tree, i: Int): Tree =
          if (i < len) {
            val c = elem.charAt(i)
            val end = (i + 1 == len)
            tree.branches.get(c) match {
              case Some((s, tr)) =>
                Tree(tree.branches +
                  (c -> (if (end) elem else s, extend(tr, i + 1))))
              case None =>
                Tree(tree.branches +
                  (c -> (if (end) elem else "", extend(Lexicon.empty_tree, i + 1))))
            }
          }
          else tree
        val old = this
        new Lexicon { override val main_tree = extend(old.main_tree, 0) }
      }

    def + (elem1: String, elem2: String, elems: String*): Lexicon =
      this + elem1 + elem2 ++ elems
    def ++ (elems: Iterable[String]): Lexicon = (this /: elems) ((s, elem) => s + elem)
    def ++ (elems: Iterator[String]): Lexicon = (this /: elems) ((s, elem) => s + elem)


    /** RegexParsers methods **/

    override val whiteSpace = "".r


    /* keywords from lexicon */

    def keyword: Parser[String] = new Parser[String]
    {
      def apply(in: Input) =
      {
        val source = in.source
        val offset = in.offset
        val len = source.length - offset

        def scan(tree: Tree, result: String, i: Int): String =
        {
          if (i < len) {
            tree.branches.get(source.charAt(offset + i)) match {
              case Some((s, tr)) => scan(tr, if (s.isEmpty) result else s, i + 1)
              case None => result
            }
          }
          else result
        }
        val result = scan(main_tree, "", 0)
        if (result.isEmpty) Failure("keyword expected", in)
        else Success(result, in.drop(result.length))
      }
    }.named("keyword")


    /* symbols */

    def symbols(pred: String => Boolean, min_count: Int, max_count: Int): Parser[String] =
      new Parser[String]
      {
        def apply(in: Input) =
        {
          val start = in.offset
          val end = in.source.length
          val matcher = new Symbol.Matcher(in.source)

          var i = start
          var count = 0
          var finished = false
          while (!finished) {
            if (i < end && count < max_count) {
              val n = matcher(i, end)
              val sym = in.source.subSequence(i, i + n).toString
              if (pred(sym)) { i += n; count += 1 }
              else finished = true
            }
            else finished = true
          }
          if (count < min_count) Failure("bad input", in)
          else Success(in.source.subSequence(start, i).toString, in.drop(i - start))
        }
      }.named("symbols")

    def one(pred: String => Boolean): Parser[String] = symbols(pred, 1, 1)
    def many(pred: String => Boolean): Parser[String] = symbols(pred, 0, Integer.MAX_VALUE)
    def many1(pred: String => Boolean): Parser[String] = symbols(pred, 1, Integer.MAX_VALUE)


    /* quoted strings */

    private def quoted(quote: String): Parser[String] =
    {
      quote ~
        rep(many1(sym => sym != quote && sym != "\\" && Symbol.is_closed(sym)) |
          "\\" + quote | "\\\\" |
          (("""\\\d\d\d""".r) ^? { case x if x.substring(1, 4).toInt <= 255 => x })) ~
      quote ^^ { case x ~ ys ~ z => x + ys.mkString + z }
    }.named("quoted")

    def quoted_content(quote: String, source: String): String =
    {
      require(parseAll(quoted(quote), source).successful)
      source.substring(1, source.length - 1)  // FIXME proper escapes, recode utf8 (!?)
    }


    /* verbatim text */

    private def verbatim: Parser[String] =
    {
      "{*" ~ rep(many1(sym => sym != "*" && Symbol.is_closed(sym)) | """\*(?!\})""".r) ~ "*}" ^^
        { case x ~ ys ~ z => x + ys.mkString + z }
    }.named("verbatim")

    def verbatim_content(source: String): String =
    {
      require(parseAll(verbatim, source).successful)
      source.substring(2, source.length - 2)
    }


    /* nested comments */

    def comment: Parser[String] = new Parser[String]
    {
      val comment_text =
        rep(many1(sym => sym != "*" && sym != "(" && Symbol.is_closed(sym)) |
          """\*(?!\))|\((?!\*)""".r)
      val comment_open = "(*" ~ comment_text ^^ (_ => ())
      val comment_close = comment_text ~ "*)" ^^ (_ => ())

      def apply(in: Input) =
      {
        var rest = in
        def try_parse(p: Parser[Unit]): Boolean =
        {
          parse(p, rest) match {
            case Success(_, next) => { rest = next; true }
            case _ => false
          }
        }
        var depth = 0
        var finished = false
        while (!finished) {
          if (try_parse(comment_open)) depth += 1
          else if (depth > 0 && try_parse(comment_close)) depth -= 1
          else finished = true
        }
        if (in.offset < rest.offset && depth == 0)
          Success(in.source.subSequence(in.offset, rest.offset).toString, rest)
        else Failure("comment expected", in)
      }
    }.named("comment")

    def comment_content(source: String): String =
    {
      require(parseAll(comment, source).successful)
      source.substring(2, source.length - 2)
    }


    /* outer syntax tokens */

    def token(symbols: Symbol.Interpretation, is_command: String => Boolean):
      Parser[Outer_Lex.Token] =
    {
      import Outer_Lex._

      val id = one(symbols.is_letter) ~ many(symbols.is_letdig) ^^ { case x ~ y => x + y }
      val nat = many1(symbols.is_digit)
      val id_nat = id ~ opt("." ~ nat) ^^ { case x ~ Some(y ~ z) => x + y + z case x ~ None => x }

      val ident = id ~ rep("." ~> id) ^^
        { case x ~ Nil => Ident(x)
          case x ~ ys => Long_Ident((x :: ys).mkString(".")) }

      val var_ = "?" ~ id_nat ^^ { case x ~ y => Var(x + y) }
      val type_ident = "'" ~ id ^^ { case x ~ y => Type_Ident(x + y) }
      val type_var = "?'" ~ id_nat ^^ { case x ~ y => Type_Var(x + y) }
      val nat_ = nat ^^ Nat

      val sym_ident =
        (many1(symbols.is_symbolic_char) |
          one(sym => symbols.is_symbolic(sym) & Symbol.is_closed(sym))) ^^ Sym_Ident

      val space = many1(symbols.is_blank) ^^ Space

      val string = quoted("\"") ^^ String_Token
      val alt_string = quoted("`") ^^ Alt_String_Token

      val bad_input = many1(sym => !(symbols.is_blank(sym))) ^^ Bad_Input


      /* tokens */

      // FIXME right-assoc !?

      (string | alt_string | verbatim ^^ Verbatim | comment ^^ Comment | space) |
      ((ident | var_ | type_ident | type_var | nat_ | sym_ident) |||
        keyword ^^ (x => if (is_command(x)) Command(x) else Keyword(x))) |
      bad_input
    }
  }
}
