# comp523-proj

Project for COMP523: Language-Based Security.

## Running the Project

- Create an opam switch: `opam switch create .`
- Install dependencies: `opam install . --deps-only --with-test --with-doc`
- Run all tests: `dune test`
	- Run only the inline tests in the `lib` directory: `dune runtest lib`
