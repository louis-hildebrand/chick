# comp523-proj

Project for COMP523: Language-Based Security.

## Running the Project

- Create an opam switch: `opam switch create . 5.1.1`
- Install dependencies: `opam install . --deps-only --with-test --with-doc`
	- Note that it will probably take a while to install z3 (20 minutes or so on my laptop)
- Run all tests: `dune test`
	- Run only the inline tests in the `lib` directory: `dune runtest lib`
