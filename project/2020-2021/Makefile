SHELL := bash

DUNE  := dune build --display short

# [make all] compiles your project.

.PHONY: all
all:
	@ $(DUNE) src/Main.exe

# [make execute src=test/inputs/foo.th] interprets the file [foo.th].

.PHONY: execute
execute:
	@ dune exec src/Main.exe -- --execute ${src}

# [make typecheck src=test/inputs/foo.th] typechecks the file [foo.th].

.PHONY: typecheck
typecheck:
	@ dune exec src/Main.exe -- --typecheck ${src}

# [make clean] cleans up.

.PHONY: clean
clean:
	@ find . -name "*~" -exec rm '{}' \;
	@ dune clean

# [make test] runs all tests.

# If an expected-output file is missing, then an empty file is created.

.PHONY: test
test:
	@ for f in test/inputs/*.th ; do \
	    for mode in execute typecheck ; do \
	      touch "$${f%.th}.$${mode}.exp" ; \
	    done \
	  done
	@ $(DUNE) @runtest

# [make promote] updates the expected-output files used by [make test].

.PHONY: promote
promote:
	@ dune promote

# [make depend] regenerates the files dune.auto. This command should
# be run every time some test files are added or removed or renamed.

.PHONY: depend
depend:
	@ $(DUNE) @depend --auto-promote || true
