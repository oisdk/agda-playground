#!/usr/bin/env bash

# Agda needs to be run in the source directory of the project to work
# correctly.
# Run this script with a path (like agda/Example.lagda) from the
# directory *above* agda/

cd agda || exit
agda --latex --latex-dir=. "${1#agda/}"
