#!/usr/bin/env bash

sh scripts/generate-everything.sh Everything
trap "rm -f Everything.agda" 0 2 3 15
agda Everything.agda
