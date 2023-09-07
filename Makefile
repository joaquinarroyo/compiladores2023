.PHONY: run test
.DELETE_ON_ERROR:

TGT=app/Main

GHCOPTS=-prof
RTSOPTS=+RTS -xc

$(TGT): build

build:
	cabal build

interp:
	cabal repl

run: build
	 cabal run

include testing.mk
test: build vm
	$(MAKE) test_all

vm:
	$(MAKE) -C vm

.PHONY: vm
