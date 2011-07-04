/*  Title:      Pure/System/isabelle_system.scala
    Author:     Makarius

Fundamental Isabelle system environment: settings, symbols etc.
Quasi-static module with optional init operation.
*/

package isabelle

import java.lang.System
import java.util.regex.Pattern
import java.util.Locale
import java.io.{InputStream, FileInputStream, OutputStream, FileOutputStream, File,
  BufferedReader, InputStreamReader, BufferedWriter, OutputStreamWriter, IOException}
import java.awt.{GraphicsEnvironment, Font}
import java.awt.font.TextAttribute

import scala.io.Source
import scala.util.matching.Regex
import scala.collection.mutable


object Isabelle_System
{
  /** implicit state **/

  private case class State(
    standard_system: Standard_System,
    settings: Map[String, String],
    symbols: Symbol.Interpretation)

  @volatile private var _state: Option[State] = None

  private def check_state(): State =
  {
    if (_state.isEmpty) init()  // unsynchronized check
    _state.get
  }

  def standard_system: Standard_System = check_state().standard_system
  def settings: Map[String, String] = check_state().settings
  def symbols: Symbol.Interpretation = check_state().symbols

  /*
    isabelle_home precedence:
      (1) this_isabelle_home as explicit argument
      (2) ISABELLE_HOME process environment variable (e.g. inherited from running isabelle tool)
      (3) isabelle.home system property (e.g. via JVM application boot process)
  */
  def init(this_isabelle_home: String = null) = synchronized {
    if (_state.isEmpty) {
      import scala.collection.JavaConversions._

      val standard_system = new Standard_System

      val settings =
      {
        val env = Map(System.getenv.toList: _*) +
          ("THIS_JAVA" -> standard_system.this_java())

        val isabelle_home =
          if (this_isabelle_home != null) this_isabelle_home
          else
            env.get("ISABELLE_HOME") match {
              case None | Some("") =>
                val path = System.getProperty("isabelle.home")
                if (path == null || path == "") error("Unknown Isabelle home directory")
                else path
              case Some(path) => path
            }

          Standard_System.with_tmp_file("settings") { dump =>
              val shell_prefix =
                if (Platform.is_windows) List(standard_system.platform_root + "\\bin\\bash", "-l")
                else Nil
              val cmdline =
                shell_prefix ::: List(isabelle_home + "/bin/isabelle", "getenv", "-d", dump.toString)
              val (output, rc) = Standard_System.raw_exec(null, env, true, cmdline: _*)
              if (rc != 0) error(output)

              val entries =
                for (entry <- Source.fromFile(dump).mkString split "\0" if entry != "") yield {
                  val i = entry.indexOf('=')
                  if (i <= 0) (entry -> "")
                  else (entry.substring(0, i) -> entry.substring(i + 1))
                }
              Map(entries: _*) +
                ("HOME" -> System.getenv("HOME")) +
                ("PATH" -> System.getenv("PATH"))
            }
          }

      val symbols =
      {
        val isabelle_symbols = settings.getOrElse("ISABELLE_SYMBOLS", "")
        if (isabelle_symbols == "") error("Undefined environment variable: ISABELLE_SYMBOLS")
        val files =
          isabelle_symbols.split(":").toList.map(s => new File(standard_system.jvm_path(s)))
        new Symbol.Interpretation(Standard_System.try_read(files).split("\n").toList)
      }

      _state = Some(State(standard_system, settings, symbols))
    }
  }


  /* getenv */

  def getenv(name: String): String =
    settings.getOrElse(if (name == "HOME") "HOME_JVM" else name, "")

  def getenv_strict(name: String): String =
  {
    val value = getenv(name)
    if (value != "") value else error("Undefined environment variable: " + name)
  }


  /** file-system operations **/

  /* path specifications */

  def standard_path(path: Path): String = path.expand(getenv_strict).implode

  def platform_path(path: Path): String = standard_system.jvm_path(standard_path(path))
  def platform_file(path: Path) = new File(platform_path(path))

  def posix_path(jvm_path: String): String = standard_system.posix_path(jvm_path)


  /* try_read */

  def try_read(paths: Seq[Path]): String =
  {
    val buf = new StringBuilder
    for {
      path <- paths
      file = platform_file(path) if file.isFile
      c <- (Source.fromFile(file) ++ Iterator.single('\n'))
    } buf.append(c)
    buf.toString
  }


  /* source files */

  private def try_file(file: File) = if (file.isFile) Some(file) else None

  def source_file(path: Path): Option[File] =
  {
    if (path.is_absolute || path.is_current)
      try_file(platform_file(path))
    else {
      val pure_file = platform_file(Path.explode("~~/src/Pure") + path)
      if (pure_file.isFile) Some(pure_file)
      else if (getenv("ML_SOURCES") != "")
        try_file(platform_file(Path.explode("$ML_SOURCES") + path))
      else None
    }
  }



  /** external processes **/

  /* plain execute */

  def execute(redirect: Boolean, args: String*): Process =
  {
    val cmdline =
      if (Platform.is_windows) List(standard_system.platform_root + "\\bin\\env.exe") ++ args
      else args
    Standard_System.raw_execute(null, settings, redirect, cmdline: _*)
  }


  /* managed process */

  class Managed_Process(redirect: Boolean, args: String*)
  {
    private val params =
      List(standard_path(Path.explode("~~/lib/scripts/process")), "group", "-", "no_script")
    private val proc = execute(redirect, (params ++ args):_*)


    // channels

    val stdin: BufferedWriter =
      new BufferedWriter(new OutputStreamWriter(proc.getOutputStream, Standard_System.charset))

    val stdout: BufferedReader =
      new BufferedReader(new InputStreamReader(proc.getInputStream, Standard_System.charset))

    val stderr: BufferedReader =
      new BufferedReader(new InputStreamReader(proc.getErrorStream, Standard_System.charset))


    // signals

    private val pid = stdout.readLine

    private def kill(signal: String): Boolean =
    {
      execute(true, "kill", "-" + signal, "-" + pid).waitFor
      execute(true, "kill", "-0", "-" + pid).waitFor == 0
    }

    private def multi_kill(signal: String): Boolean =
    {
      var running = true
      var count = 10
      while (running && count > 0) {
        if (kill(signal)) {
          Thread.sleep(100)
          count -= 1
        }
        else running = false
      }
      running
    }

    def interrupt() { multi_kill("INT") }
    def terminate() { multi_kill("INT") && multi_kill("TERM") && kill("KILL"); proc.destroy }


    // JVM shutdown hook

    private val shutdown_hook = new Thread { override def run = terminate() }

    try { Runtime.getRuntime.addShutdownHook(shutdown_hook) }
    catch { case _: IllegalStateException => }

    private def cleanup() =
      try { Runtime.getRuntime.removeShutdownHook(shutdown_hook) }
      catch { case _: IllegalStateException => }


    /* result */

    def join: Int = { val rc = proc.waitFor; cleanup(); rc }
  }


  /* bash */

  def bash(script: String): (String, String, Int) =
  {
    Standard_System.with_tmp_file("isabelle_script") { script_file =>
      Standard_System.write_file(script_file, script)
      val proc = new Managed_Process(false, "bash", posix_path(script_file.getPath))

      proc.stdin.close
      val stdout = Simple_Thread.future("bash_stdout") { Standard_System.slurp(proc.stdout) }
      val stderr = Simple_Thread.future("bash_stderr") { Standard_System.slurp(proc.stderr) }

      val rc =
        try { proc.join }
        catch { case e: InterruptedException => Thread.interrupted; proc.terminate; 130 }
      (stdout.join, stderr.join, rc)
    }
  }


  /* system tools */

  def isabelle_tool(name: String, args: String*): (String, Int) =
  {
    getenv_strict("ISABELLE_TOOLS").split(":").find { dir =>
      val file = platform_file(Path.explode(dir) + Path.basic(name))
      try {
        file.isFile && file.canRead && file.canExecute &&
          !name.endsWith("~") && !name.endsWith(".orig")
      }
      catch { case _: SecurityException => false }
    } match {
      case Some(dir) =>
        val file = standard_path(Path.explode(dir) + Path.basic(name))
        Standard_System.process_output(execute(true, (List(file) ++ args): _*))
      case None => ("Unknown Isabelle tool: " + name, 2)
    }
  }


  /* named pipes */

  private val next_fifo = new Counter

  def mk_fifo(): String =
  {
    val i = next_fifo()
    val script =
      "FIFO=\"/tmp/isabelle-fifo-${PPID}-$$" + i + "\"\n" +
      "echo -n \"$FIFO\"\n" +
      "mkfifo -m 600 \"$FIFO\"\n"
    val (out, err, rc) = bash(script)
    if (rc == 0) out else error(err.trim)
  }

  def rm_fifo(fifo: String): Boolean =
    (new File(standard_system.jvm_path(if (Platform.is_windows) fifo + ".lnk" else fifo))).delete

  def fifo_input_stream(fifo: String): InputStream =
  {
    if (Platform.is_windows) { // Cygwin fifo as Windows/Java input stream
      val proc = execute(false, standard_path(Path.explode("~~/lib/scripts/raw_dump")), fifo, "-")
      proc.getOutputStream.close
      proc.getErrorStream.close
      proc.getInputStream
    }
    else new FileInputStream(fifo)
  }

  def fifo_output_stream(fifo: String): OutputStream =
  {
    if (Platform.is_windows) { // Cygwin fifo as Windows/Java output stream
      val proc = execute(false, standard_path(Path.explode("~~/lib/scripts/raw_dump")), "-", fifo)
      proc.getInputStream.close
      proc.getErrorStream.close
      val out = proc.getOutputStream
      new OutputStream {
        override def close() { out.close(); proc.waitFor() }
        override def flush() { out.flush() }
        override def write(b: Array[Byte]) { out.write(b) }
        override def write(b: Array[Byte], off: Int, len: Int) { out.write(b, off, len) }
        override def write(b: Int) { out.write(b) }
      }
    }
    else new FileOutputStream(fifo)
  }



  /** Isabelle resources **/

  /* components */

  def components(): List[String] =
    getenv_strict("ISABELLE_COMPONENTS").split(":").toList


  /* find logics */

  def find_logics(): List[String] =
  {
    val ml_ident = getenv_strict("ML_IDENTIFIER")
    val logics = new mutable.ListBuffer[String]
    for (dir <- getenv_strict("ISABELLE_PATH").split(":")) {
      val files = platform_file(Path.explode(dir) + Path.explode(ml_ident)).listFiles()
      if (files != null) {
        for (file <- files if file.isFile) logics += file.getName
      }
    }
    logics.toList.sortWith(_ < _)
  }


  /* fonts */

  def get_font(family: String = "IsabelleText", size: Int = 1, bold: Boolean = false): Font =
    new Font(family, if (bold) Font.BOLD else Font.PLAIN, size)

  def install_fonts()
  {
    val ge = GraphicsEnvironment.getLocalGraphicsEnvironment()
    for (font <- getenv_strict("ISABELLE_FONTS").split(":"))
      ge.registerFont(Font.createFont(Font.TRUETYPE_FONT, platform_file(Path.explode(font))))
  }
}
