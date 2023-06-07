CC=clang
RMF=rm -rf
# CFLAGS=-g -lpthread
CFLAGS=-g -O2 -lpthread -Wl,-stack_size -Wl,0xf000000
SRC = main.c runtime.c chan.c queue.c

all: main.out

main.out: $(SRC) 
	$(CC) $(CFLAGS) $^ -o $@

clean:: ; $(RMF) *.dSYM
clean:: ; $(RMF) *.gch
clean:: ; $(RMF) *.out
