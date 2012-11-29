/*  Author:     Makarius

Bash process group invocation.
*/

#include <stdlib.h>
#include <stdio.h>
#include <sys/types.h>
#include <unistd.h>


static void fail(const char *msg)
{
  fprintf(stderr, "%s\n", msg);
  exit(2);
}


int main(int argc, char *argv[])
{
  /* args */

  if (argc != 3) {
    fprintf(stderr, "Bad arguments\n");
    exit(1);
  }
  char *pid_name = argv[1];
  char *script = argv[2];


  /* report pid */

  FILE *pid_file;
  pid_file = fopen(pid_name, "w");
  if (pid_file == NULL) fail("Cannot open pid file");
  fprintf(pid_file, "%d", getpid());
  fclose(pid_file);


  /* setsid */

  if (setsid() == -1) {
    pid_t pid = fork();
    if (pid == -1) fail("Cannot set session id (failed to fork)");
    else if (pid != 0) exit(0);
    else if (setsid() == -1) fail("Cannot set session id (after fork)");
  }


  /* exec */

  char *cmd_line[4];
  cmd_line[0] = "bash";
  cmd_line[1] = "-c";
  cmd_line[2] = script;
  cmd_line[3] = NULL;

  execvp(cmd_line[0], cmd_line);
  fail("Cannot exec process");
}

