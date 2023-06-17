# TLL Compiler

## OCaml Dependencies
Tested with ocaml 4.14.0.
- `dune`
- `ppxlib`
- `ppx_deriving`
- `fmt`
- `sedlex`
- `menhirLib`
- `bindlib`
Dependencies can be installed by running `opam install . --deps-only` in the project root.

## C Dependencies 
Tested with clang 14.0.3 and gcc 13.1.0.
- `pthreads`
Unix-like operating systems (Linux, MacOS, WSL, etc.) should come with `pthreads`.

## Usage
Example source files of varying complexity are given in the [`tests`](./compiler/tests) directory. 

To compile a TLL program such as `test19.tll`, execute the command 
`dune exec --profile release bin/main.exe tests/test19.tll` from the [project root](./compiler).

A `log.tll` file will be generated at the project root logging the intermediate representation 
at each phase of compilation. Another `main.c` file will be generated in the [`c`](./compiler/c) 
directory containing the emitted C code. 

The emitted C code can be further compiled to a `main.out` executable by running `make -C ./c` 
from the project root.

The included [`tll-mode.el`](./tll-mode.el) provides optional syntax highlighting for Emacs users. 
Place `tll-mode.el` in your Emacs load path and add `(require 'tll-mode)` to your init file.

## Notable Examples
- [test01.tll](./compiler/tests/test01.tll): Proof of identity for sort-polymorphic length function.
- [test02.tll](./compiler/tests/test02.tll): Verification of sort-polymorphic append function.
- [test04.tll](./compiler/tests/test04.tll): Sort polymorphic tuples and dependent pairs.
- [test05.tll](./compiler/tests/test05.tll): Readline/printline from spawned thread.
- [test07.tll](./compiler/tests/test07.tll): McCarthy 91 function.
- [test08.tll](./compiler/tests/test08.tll): Encoding mutable references using dependent session types.
- [test09.tll](./compiler/tests/test09.tll): Verified concurrent mergesort (unbounded thread spawning).
- [test11.tll](./compiler/tests/test11.tll): Unverified concurrent mergesort (bounded thread spawning).
- [test12.tll](./compiler/tests/test12.tll): Verified concurrent mergesort (bounded thread spawning).
- [test13.tll](./compiler/tests/test13.tll): Logical inductive types and irrelevant match expressions.
- [test14.tll](./compiler/tests/test14.tll): Append function for length indexed linear vectors.
- [test15.tll](./compiler/tests/test15.tll): Append function for length indexed sort-polymorphic vectors.
- [test16.tll](./compiler/tests/test16.tll): Diffie-Hellman key exchange protocol.
- [test17.tll](./compiler/tests/test17.tll): RSA public-key encryption.
- [test18.tll](./compiler/tests/test18.tll): *Guess the Secret Number* game implementation using dependent session types.
- [test19.tll](./compiler/tests/test19.tll): Certified *Wordle* game implementation using dependent session types.
