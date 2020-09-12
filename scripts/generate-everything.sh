#!/usr/bin/env bash

# This script creates an Everything.agda file and generates html from
# it for all agda and literate agda files in the current directory.

agda_dir=$(pwd)
# echo "{-# OPTIONS --cubical #-}" > Everything
echo "module Everything where" > Everything
find . -type f \( -name "*.agda" -o -name "*.lagda" \) | cut -c 3- | cut -f1 -d'.' | sed 's/\//\./g' | sed 's/^/open import /' >> Everything
temp_dir=$(mktemp -d)
mv Everything $temp_dir/Everything.agda
cd $temp_dir
agda -i $agda_dir --html --html-dir=$agda_dir/../docs $temp_dir/Everything.agda
