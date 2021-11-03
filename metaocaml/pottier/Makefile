.PHONY: all test clean

SWITCH   := 4.11.1+BER
OCAMLC   := opam exec --switch $(SWITCH) metaocamlc --
OCAMLOPT := opam exec --switch $(SWITCH) metaocamlopt --

# The executables that we wish to build.

TARGETS  := Power.exe StreamFusion.exe

all:: $(TARGETS)

test: all
	./Power.exe
	./StreamFusion.exe

clean:
	rm -f *~ *.cmi *.cmo *.cmx *.o *.exe

# Generic rules.

%.cmi %.cmx %.o: %.ml
	$(OCAMLOPT) -c $<

%.cmi %.cmo: %.ml
	$(OCAMLC) -c $<

# We must list the modules that make up each executable (yech).

Power.exe: Square.cmx Power.cmx
	$(OCAMLOPT) -o $@ Square.cmx Power.cmx

StreamFusion.exe: Shape.cmx StreamFusion.cmx
	$(OCAMLOPT) -o $@ Shape.cmx StreamFusion.cmx

# Apparently there is no ocamldep for metaocaml!?
# We write down our dependencies by hand.

Power.cmx: Square.cmx
StreamFusion.cmx: Shape.cmx

# Build also the .cmo files, so that we can load them in the REPL.

all:: Square.cmo Shape.cmo
