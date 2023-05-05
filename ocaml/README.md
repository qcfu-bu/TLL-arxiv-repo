# OCaml implementation of TLL

## Dependencies
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
