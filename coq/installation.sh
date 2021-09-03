#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

# Automatically answer "yes" to the questions asked by opam.

export OPAMYES=true

# Create a new opam switch. (We assume opam 2 is installed.)

echo "Creating a new opam switch..."
if opam switch create mpri24 ocaml-base-compiler.4.12.0
then :
else
echo "Checking if the switch mpri24 already exists..."
if [ "$(opam exec --switch=mpri24 ocamlc -- --version)" = 4.12.0 ]
then echo "Fine!"
else
    echo "The switch mpri24 is not version 4.12.0 of the ocaml compiler; "
    echo "you probably wish to remove it (check first):"
    echo; echo "    opam switch remove mpri24"; echo
    echo "and restart the script."
fi
fi

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
        DARWINEMACS=/Applications/Aquamacs*.app/Contents/MacOS/Aquamacs
        if [ -x ${DARWINEMACS} ]
        then
            EMACS="$(ls ${DARWINEMACS})"
            export EMACS
        fi
  ;;
esac

# Install Tuareg, Merlin, Coq, AutoSubst.

echo "Installing Tuareg, Merlin, Coq 8.13.2, AutoSubst..."
opam install \
  tuareg \
  merlin \
  coq.8.13.2 \
  coq-autosubst.1.7 \
