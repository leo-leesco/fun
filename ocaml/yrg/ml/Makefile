.PHONY: all clean doc check debug

ifeq ($(DEBUGPARSING), yes)
  MENHIROPT=-yaccflag --explain -yaccflag --trace
else
  MENHIROPT=-yaccflag --explain
endif

OCAMLBUILDFLAGS_COMMON = -cflag "-annot" -cflag "-bin-annot" $(MENHIROPT)

# In Emacs, use classic display to enable error jumping.
TERM = $(shell echo $$TERM)
ifeq ($(TERM), dumb)
 OCAMLBUILDFLAGS = $(OCAMLBUILDFLAGS_COMMON) -tag debug -classic-display
else
 OCAMLBUILDFLAGS = $(OCAMLBUILDFLAGS_COMMON)
endif

OCAMLBUILD = ocamlbuild -use-ocamlfind -use-menhir $(OCAMLBUILDFLAGS)
OCAMLDOC = ocamldoc

all:
	$(OCAMLBUILD) miniml.byte

debug:
	$(OCAMLBUILD) -tag debug miniml.byte

check: all
	$(MAKE) -C tests check

clean:
	$(OCAMLBUILD) -clean
	rm -f *~
