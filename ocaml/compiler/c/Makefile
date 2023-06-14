CC=clang
RMF=rm -rf
CFLAGS=-g -O2
SRC=main.c runtime.c chan.c queue.c

UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S), Darwin)
    CFLAGS += -lpthread -Wl,-stack_size -Wl,0xf000000
endif
ifeq ($(UNAME_S), Linux)
    CFLAGS += -pthread
endif


all: main.out

main.out: $(SRC) 
	$(CC) $(CFLAGS) $^ -o $@

clean:: ; $(RMF) *.dSYM
clean:: ; $(RMF) *.gch
clean:: ; $(RMF) *.out

cleanall: clean
	$(RMF) main.c
