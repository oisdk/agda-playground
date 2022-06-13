#!/usr/bin/env bash

sh scripts/generate-everything.sh Everything
trap "rm -f Everything.agda" 0 2 3 15
agda --version
agda --html --html-dir=docs Everything.agda
cp style.css docs/Agda.css
