all:
	dune build

lib:
	dune build lib

install-lib: lib
	dune build lib
	dune install Catincoq

install: all
	dune build
	dune build @install
	dune install

PHONY: all lib install-lib install
