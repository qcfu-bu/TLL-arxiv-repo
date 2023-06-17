# Coq formalization of TLL

## Dependencies
- `coq-mathcomp-ssreflect`
- `coq-autosubst`

Tested on Coq 8.17.0

## Usage

Once dependencies have been met, run `make` in the `theories` directory.

## Organization

Generally, the prefix of each file describes what kind of theorems are contained inside.

- `tll_`      : General definitions concerning TLL.
- `mltt_`     : Definitions and theorems concerning Martin-Lof type theory.
- `logical_`  : Logical level definitions and theorems.
- `program_`  : Program level definitions and theorems.
- `erasure_`  : Definitions and theorems concerning erasure.
- `heap_`     : Definitions and theorems concerning heap semantics.

### Definitions

The following table shows the file containing the encodings of various judgments.

| name in paper              | file                                        |
| -------------------------- | ------------------------------------------- |
| Syntax of TLL              | [tll_ast.v](./theories/tll_ast.v)           |
| Logical Context            | [logical_ctx.v](./theories/logical_ctx.v)   |
| Type Formation             | [logical_type.v](./theories/logical_type.v) |
| Logical Terms              | [logical_type.v](./theories/logical_type.v) |
| Program Context            | [program_ctx.v](./theories/program_ctx.v)   |
| Context Merge              | [program_ctx.v](./theories/program_ctx.v)   |
| Context Constraint         | [program_ctx.v](./theories/program_ctx.v)   |
| General Program Typing     | [program_type.v](./theories/program_type.v) |
| Irrelevance Quantification | [program_type.v](./theories/program_type.v) |
| Relevance Quantification   | [program_type.v](./theories/program_type.v) |
| General Erasure            | [erasure_type.v](./theories/erasure_type.v) |
| Irrelevance Erasure        | [erasure_type.v](./theories/erasure_type.v) |
| Relevance Erasure          | [erasure_type.v](./theories/erasure_type.v) |
| Logical Reductions         | [logical_step.v](./theories/logical_step.v) |
| Program Values             | [program_step.v](./theories/program_step.v) |
| Program Reductions         | [program_step.v](./theories/program_step.v) |
| Logical TLL in MLTT        | [logical_sn.v](./theories/logical_sn.v)     |
| Heap Lookup                | [heap_res.v](./theories/heap_res.v)         |
| Heap Reductions            | [heap_step.v](./theories/heap_step.v)       |
| Pointer Resolution         | [heap_res.v](./theories/heap_res.v)         |
| Well-Resolved              | [heap_res.v](./theories/heap_res.v)         |
| WR-Heaps                   | [heap_res.v](./theories/heap_res.v)         |
| Propositional Equality     | [logical_type.v](./theories/logical_type.v) |
| Subset Pairs (Logical)     | [logical_type.v](./theories/logical_type.v) |
| Subset Pairs (Program)     | [program_type.v](./theories/program_type.v) |
| Standard Pairs (Logical)   | [logical_type.v](./theories/logical_type.v) |
| Standard Pairs (Program)   | [program_type.v](./theories/program_type.v) |
| Additive Pairs (Logical)   | [logical_type.v](./theories/logical_type.v) |
| Additive Pairs (Program)   | [program_type.v](./theories/program_type.v) |

### Meta Theory

Meta theorems presented in the paper can be found in the following files. 
All theorems have already taken the extensions described in Section 9 into account.

| name in paper                                | file                                          |
| -------------------------------------------- | --------------------------------------------- |
| Theorem 1 (Confluence of Logical Reductions) | [logical_conf.v](./theories/logical_conf.v)   |
| Theorem 2 (Type Validity)                    | [logical_valid.v](./theories/logical_valid.v) |
| Theorem 3 (Sort Uniqueness)                  | [logical_uniq.v](./theories/logical_uniq.v)   |
| Theorem 4 (Logical Subject Reduction)        | [logical_sr.v](./theories/logical_sr.v)       |
| Lemma 1 (Logical Type Model)                 | [logical_sn.v](./theories/logical_sn.v)       |
| Lemma 2 (Logical Reduction Model)            | [logical_sn.v](./theories/logical_sn.v)       |
| Theorem 5 (Logical Strong Normalization)     | [logical_sn.v](./theories/logical_sn.v)       |
| Lemma 3 (Program 0-Weakening)                | [program_weak.v](./theories/program_weak.v)   |
| Lemma 4 (Program 1-Weakening)                | [program_weak.v](./theories/program_weak.v)   |
| Theorem 6 (Program Reflection)               | [program_valid.v](./theories/program_valid.v) |
| Theorem 7 (Value Stability)                  | [program_sr.v](./theories/program_sr.v)       |
| Lemma 5 (Program 0-Substitution)             | [program_subst.v](./theories/program_subst.v) |
| Lemma 6 (Program 1-Substitution)             | [program_subst.v](./theories/program_subst.v) |
| Theorem 8 (Program Subject Reduction)        | [program_sr.v](./theories/program_sr.v)       |
| Theorem 9 (Program Progress)                 | [program_prog.v](./theories/program_prog.v)   |
| Theorem 10 (Erasure Existence)               | [erasure_type.v](./theories/erasure_type.v)   |
| Theorem 11 (Erasure Subject Reduction)       | [erasure_sr.v](./theories/erasure_sr.v)       |
| Theorem 12 (Erasure Progress)                | [erasure_prog.v](./theories/erasure_prog.v)   |
| Theorem 13 (Resolution Stability)            | [heap_res.v](./theories/heap_res.v)           |
| Theorem 14 (Heap Subject Reduction)          | [heap_sr.v](./theories/heap_sr.v)             |
| Theorem 15 (Heap Progress)                   | [heap_prog.v](./theories/heap_prog.v)         |
