#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

# Automatically answer "yes" to the questions asked by opam.

export OPAMYES=true

# Create a new opam switch. (We assume opam 2 is installed.)

echo "Creating a new opam switch..."
opam switch create mpri24 4.11.1
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

echo "Installing Tuareg, Merlin, Coq 8.12.0..."
opam install -j4 \
  tuareg \
  merlin \
  coq.8.12.0 \

# Install AutoSubst.
# The exact commit I have used is e5bf249d7912a185c7f9f69af1a065daa4284f34.

echo "Installing AutoSubst..."
cd /tmp && \
  rm -rf autosubst && \
  git clone https://github.com/RalfJung/autosubst.git && \
  make -C autosubst lib install && \
  rm -rf autosubst
