# chick

`chick` is a small programming language with built-in support for lists.
It is dependently-typed; the list type includes a length and the length can be an expression (e.g., a variable, a sum), not necessarily a constant.
In this respect, `chick` is similar to (though *much* less feature-rich than) languages like [Coq](https://en.wikipedia.org/wiki/Rocq) and [Agda](https://agda.readthedocs.io/en/latest/getting-started/a-taste-of-agda.html).

This repository contains a type checker which can statically detect many bugs that are usually only caught at runtime: trying to access an element in an empty list, zipping two lists of different length, etc.
For more details, see the [presentation slides](./report/presentation.pdf) or the [report](report/report.pdf).

This project was done as part of COMP 523: Language-Based Security at McGill University.

## Running the Project

- Create an opam switch: `opam switch create . 5.1.1`
- Install dependencies: `opam install . --deps-only --with-test --with-doc`
	- Note that it will probably take a while to install z3 (20 minutes or so on my laptop)
- Run all tests: `dune test`
	- Run only the inline tests in the `lib` directory: `dune runtest lib`
