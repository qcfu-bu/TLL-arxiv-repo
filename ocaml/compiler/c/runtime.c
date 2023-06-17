#include "chan.h"
#include <pthread.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>
#include <unistd.h>

#include "prelude.h"
#include "runtime.h"

#define MALLOC malloc
#define FREE free

/*-------------------------------------------------------*/

pthread_attr_t attr;

void instr_init(void) {
  const rlim_t stacksize = 0xf000000;
  struct rlimit rl;
  getrlimit(RLIMIT_STACK, &rl);
  if (rl.rlim_cur < stacksize) {
    rl.rlim_cur = stacksize;
    setrlimit(RLIMIT_STACK, &rl);
  }
  srand(time(0));
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, stacksize);
  return;
}

/*-------------------------------------------------------*/

void instr_exit(void) {
  pthread_exit(NULL);
  return;
}

/*-------------------------------------------------------*/

tll_ptr to_char(unsigned long c) {
  tll_node x = (tll_node)MALLOC(tll_node_size);
  x->tag = Char_c;
  x->data = (tll_ptr *)MALLOC(tll_ptr_size);
  x->data[0] = (tll_ptr)c;
  return (tll_ptr)x;
}

tll_ptr to_string(char *s) {
  tll_node tmp;
  tll_node x = (tll_node)MALLOC(tll_node_size);
  x->tag = EmptyString_c;
  int len = strlen(s);
  for (int i = 2; i <= len; i++) {
    tmp = (tll_node)MALLOC(tll_node_size);
    tmp->tag = String_c;
    tmp->data = (tll_ptr *)MALLOC(tll_ptr_size * 2);
    tmp->data[0] = to_char(s[len - i]);
    tmp->data[1] = x;
    x = tmp;
  }
  return (tll_ptr)x;
}

unsigned long from_char(tll_ptr x) {
  unsigned long c = (unsigned long)((tll_node)x)->data[0];
  return (c % 256);
}

char *from_string(tll_ptr x) {
  char *str;
  int len = 0;
  tll_node tmp = (tll_node)x;
  while (tmp->tag != EmptyString_c) {
    tmp = (tll_node)(tmp->data[1]);
    len++;
  }
  str = (char *)MALLOC(sizeof(char) * (len + 1));
  str[len] = 0;
  tmp = (tll_node)x;
  for (int i = 0; i < len; i++) {
    str[i] = from_char(tmp->data[0]);
    tmp = (tll_node)(tmp->data[1]);
  }
  return str;
}

/*-------------------------------------------------------*/

tll_ptr proc_stdout(tll_ptr ch) {
  int b = 0, rep = 1;
  char *str;
  tll_ptr msg;
  while (rep) {
    chan_recv((chan_t *)ch, &msg);
    if (b) {
      str = from_string(msg);
      fputs(str, stdout);
      FREE(str);
      b = !b;
    } else {
      if (msg) {
        b = !b;
      } else {
        rep = !rep;
      }
    }
  }
  return NULL;
}

tll_ptr proc_stdin(tll_ptr ch) {
  int b = 0, rep = 1, tmp = 0;
  char *buffer;
  size_t len;
  tll_ptr msg;
  while (rep) {
    if (b) {
      tmp = getline(&buffer, &len, stdin);
      msg = to_string(buffer);
      free(buffer);
      chan_send((chan_t *)ch, msg);
      b = !b;
    } else {
      chan_recv((chan_t *)ch, &msg);
      if (msg) {
        b = !b;
      } else {
        rep = !rep;
      }
    }
  }
  return NULL;
}

tll_ptr proc_stderr(tll_ptr ch) {
  int b = 0, rep = 1;
  char *str;
  tll_ptr msg;
  while (rep) {
    chan_recv((chan_t *)ch, &msg);
    if (b) {
      str = from_string(msg);
      fputs(str, stderr);
      FREE(str);
      b = !b;
    } else {
      if (msg) {
        b = !b;
      } else {
        rep = !rep;
      }
    }
  }
  return NULL;
}

/*-------------------------------------------------------*/

void instr_lten(tll_ptr *x, tll_ptr v1, tll_ptr v2) {
  unsigned long res = (unsigned long)(v1 <= v2);
  *x = (tll_ptr)res;
  return;
}

/*-------------------------------------------------------*/

void instr_gten(tll_ptr *x, tll_ptr v1, tll_ptr v2) {
  unsigned long res = (unsigned long)(v1 >= v2);
  *x = (tll_ptr)res;
  return;
}

/*-------------------------------------------------------*/

void instr_ltn(tll_ptr *x, tll_ptr v1, tll_ptr v2) {
  unsigned long res = (unsigned long)(v1 < v2);
  *x = (tll_ptr)res;
  return;
}

/*-------------------------------------------------------*/

void instr_gtn(tll_ptr *x, tll_ptr v1, tll_ptr v2) {
  unsigned long res = (unsigned long)(v1 > v2);
  *x = (tll_ptr)res;
  return;
}

/*-------------------------------------------------------*/

void instr_eqn(tll_ptr *x, tll_ptr v1, tll_ptr v2) {
  unsigned long res = (unsigned long)(v1 == v2);
  *x = (tll_ptr)res;
  return;
}

/*-------------------------------------------------------*/

void instr_addn(tll_ptr *x, tll_ptr v1, tll_ptr v2) {
  unsigned long res = (unsigned long)v1 + (unsigned long)v2;
  *x = (tll_ptr)res;
  return;
}

/*-------------------------------------------------------*/

void instr_subn(tll_ptr *x, tll_ptr v1, tll_ptr v2) {
  long res = (long)v1 - (long)v2;
  if (0 <= res) {
    *x = (tll_ptr)res;
  } else {
    *x = 0;
  }
  return;
}

/*-------------------------------------------------------*/

void instr_muln(tll_ptr *x, tll_ptr v1, tll_ptr v2) {
  unsigned long res = ((unsigned long)v1 * (unsigned long)v2);
  *x = (tll_ptr)res;
  return;
}

/*-------------------------------------------------------*/

void instr_divn(tll_ptr *x, tll_ptr v1, tll_ptr v2) {
  unsigned long res = ((unsigned long)v1 / (unsigned long)v2);
  *x = (tll_ptr)res;
  return;
}

/*-------------------------------------------------------*/

void instr_modn(tll_ptr *x, tll_ptr v1, tll_ptr v2) {
  unsigned long res = ((unsigned long)v1 % (unsigned long)v2);
  *x = (tll_ptr)res;
  return;
}

/*-------------------------------------------------------*/

void instr_clo(tll_ptr *x, tll_ptr (*f)(tll_ptr, tll_env), int size, ...) {
  va_list ap;
  tll_clo tmp = (tll_clo)MALLOC(tll_clo_size);
  tmp->f = f;
  tmp->env = (tll_env)MALLOC(tll_ptr_size * size);

  va_start(ap, size);
  for (int i = 0; i < size; i++) {
    tmp->env[i] = va_arg(ap, tll_ptr);
  }
  va_end(ap);

  *x = (tll_ptr)tmp;
  return;
}

/*-------------------------------------------------------*/

void instr_app(tll_ptr *x, tll_ptr clo, tll_ptr v) {
  tll_ptr (*f)(tll_ptr, tll_env) = ((tll_clo)clo)->f;
  tll_env env = ((tll_clo)clo)->env;
  *x = (*f)(v, env);
  return;
}

/*-------------------------------------------------------*/

void instr_struct(tll_ptr *x, int tag, int size, ...) {
  va_list ap;
  tll_node tmp = (tll_node)MALLOC(tll_node_size);
  tmp->tag = tag;
  tmp->data = (tll_ptr *)MALLOC(tll_ptr_size * size);

  va_start(ap, size);
  for (int i = 0; i < size; i++) {
    tmp->data[i] = va_arg(ap, tll_ptr);
  }
  va_end(ap);

  *x = (tll_ptr)tmp;
  return;
}

/*-------------------------------------------------------*/

void instr_open(tll_ptr *x, tll_ptr (*f)(tll_ptr)) {
  pthread_t th;
  tll_ptr ch = (tll_ptr)chan_init(0);
  pthread_create(&th, 0, (void *(*)(void *))f, ch);
  *x = ch;
  return;
}

/*-------------------------------------------------------*/

void instr_fork(tll_ptr *x, tll_ptr (*f)(tll_env), int size, ...) {
  va_list ap;
  pthread_t th;
  tll_ptr ch = (tll_ptr)chan_init(0);
  tll_env local = (tll_env)MALLOC(tll_ptr_size * (size + 1));

  local[0] = ch;
  va_start(ap, size);
  for (int i = 0; i < size; i++) {
    local[i + 1] = va_arg(ap, tll_ptr);
  }
  va_end(ap);

  pthread_create(&th, &attr, (void *(*)(void *))f, local);
  *x = ch;
  return;
}

/*-------------------------------------------------------*/

void instr_send(tll_ptr *x, tll_ptr ch, tll_ptr msg) {
  chan_send((chan_t *)ch, msg);
  *x = ch;
  return;
}

/*-------------------------------------------------------*/

void instr_recv(tll_ptr *x, tll_ptr ch) {
  tll_ptr msg;
  chan_recv((chan_t *)ch, &msg);
  instr_struct(x, 0, 2, msg, ch);
  return;
}

/*-------------------------------------------------------*/

void instr_close(tll_ptr *x, tll_ptr ch) {
  chan_dispose((chan_t *)ch);
  *x = 0;
  return;
}

/*-------------------------------------------------------*/

void instr_sleep(tll_ptr *x, tll_ptr v) {
  sleep((unsigned long)v);
  *x = 0;
  return;
}

/*-------------------------------------------------------*/

void instr_rand(tll_ptr *x, tll_ptr v1, tll_ptr v2) {
  unsigned long lower = (unsigned long)v1;
  unsigned long offset = (unsigned long)v2;
  unsigned long num = (rand() % (offset + 1)) + lower;
  instr_struct(x, Between_c, 3, num, 0, 0);
  return;
}

/*-------------------------------------------------------*/

void instr_free_clo(tll_ptr *x) {
  FREE(((tll_clo)x)->env);
  FREE(x);
  return;
}

/*-------------------------------------------------------*/

void instr_free_struct(tll_ptr *x) {
  FREE(((tll_node)x)->data);
  FREE(x);
  return;
}

/*-------------------------------------------------------*/

void instr_free_thread(tll_env env) {
  FREE(env);
  return;
}
