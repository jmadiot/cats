all:
	dune build

install:
	dune build @install
	dune install
