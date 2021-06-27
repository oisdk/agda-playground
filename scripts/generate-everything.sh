#!/usr/bin/env bash

# This script creates an Everything.agda file in the agda directory.
# It contains an import statement for every module in the agda/
# directory. This means if you typecheck it it will typecheck every
# agda file.
#
# Run it from *above* the agda/ directory.
#
# It takes one argument, which is the module and file name

if [ -f "$1.agda" ]; then
    echo "file agda/$1.agda already exists: you must supply a module name which does not already exist"
    exit 17
fi
everything_file=$(mktemp)
trap "rm -f $everything_file" 0 2 3 15
echo "{-# OPTIONS --cubical --guardedness --prop --allow-unsolved-metas #-}" > "$everything_file"
echo "module $1 where" >> "$everything_file"
find . -type f \( -name "*.agda" -o -name "*.lagda" \) \
        | cut -c 3- \
        | cut -f1 -d'.' \
        | sed 's/\//\./g' \
        | sed 's/^/open import /' \
              >> $everything_file
mv $everything_file $1.agda
