# TLL Compiler

## OCaml Dependencies
- `dune`
- `ppxlib`
- `ppx_deriving`
- `fmt`
- `sedlex`
- `menhirLib`
- `bindlib`

## Usage
Example source files of varying complexity are given in the `tests` directory. 

To compile a TLL program such as `test12.tll`, execute the command `dune exec --profile release bin/main.exe tests/test12.tll` from the project root.

A `log.tll` file will be generated at the project root logging the intermediate representation at each phase of compilation. Another `main.c` file will be generated in the `c` directory containing the emitted C code. 

The emitted C code can be further compiled to a `main.out` executable by running `make -C ./c` from the project root.

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
