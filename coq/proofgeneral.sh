#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

# Clone the ProofGeneral repository.
rm -rf /tmp/PG
cd /tmp
git clone git@github.com:ProofGeneral/PG.git
cd PG
# Determine how emacs is named.
EMACS=/Applications/Aquamacs.app/Contents/MacOS/Aquamacs
if [ ! -x $EMACS ]; then
  EMACS=emacs
fi
# Compile.
make EMACS=$EMACS compile
# Install.
TARGET=/usr/local/share/emacs/site-lisp/ProofGeneral
sudo rm -rf $TARGET
sudo mv /tmp/PG $TARGET
# Add a line to the user's .emacs file.
echo '(load-file "/usr/local/share/emacs/site-lisp/ProofGeneral/generic/proof-site.el")' > $HOME/.emacs
