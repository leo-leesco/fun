#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

# Automatically answer "yes" to the questions asked by opam.

export OPAMYES=true

# Create a new opam switch. (We assume opam 2 is installed.)

echo "Creating a new opam switch..."
opam switch create mpri24 4.05.0
eval "$(opam config env)"

# Declare the Coq repository (not a switch-local command, unfortunately).

echo "Declaring the Coq repository..."
opam repo add coq-released https://coq.inria.fr/opam/released 2>/dev/null || true

# Update the package list (not a switch-local command, unfortunately).

echo "Updating the list of available packages..."
opam update

# Configure EMACS (used during Tuareg's installation).

case $OSTYPE in
darwin*)
  EMACS="$(ls /Applications/Aquamacs*.app/Contents/MacOS/Aquamacs)"
  export EMACS
  ;;
esac

# Install Tuareg, Merlin, Coq.

echo "Installing Tuareg, Merlin, Coq 8.5.3..."
opam install -j4 \
  tuareg \
  merlin \
  coq.8.5.3 \

# Install AutoSubst.

echo "Installing AutoSubst..."
cd /tmp && \
  rm -rf autosubst && \
  git clone git@github.com:fpottier/autosubst.git && \
  make -C autosubst lib install && \
  rm -rf autosubst
