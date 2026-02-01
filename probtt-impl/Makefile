.PHONY: all build clean test

all: build

build:
	dune build

clean:
	dune clean

test:
	dune runtest

check: build
	dune exec probtt -- check $(FILE)

infer: build
	dune exec probtt -- infer $(FILE)
