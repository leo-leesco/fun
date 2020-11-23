COQINCLUDE := -R $(shell pwd) MPRI
# The following flag avoids warnings about the use of Restart.
COQFLAGS   := -async-proofs-cache force
include Makefile.coq

clean::
	rm -rf `cat .gitignore | grep -v _CoqProject`
