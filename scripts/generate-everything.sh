#!/usr/bin/env bash

# This script creates an Everything.agda file in the agda directory.
# It contains an import statement for every module in this directory.
# This means if you typecheck it it will typecheck every agda file.
#
# It takes one argument, which is the desired module name for the module which
# contains every module in the project.

if [ -f "$1.agda" ]; then
    echo "file agda/$1.agda already exists: you must supply a module name which does not already exist"
    exit 17
fi
everything_file=$(mktemp)
trap "rm -f $everything_file" 0 2 3 15
cat > "$everything_file" <<-EOF
{-# OPTIONS --cubical --guardedness --prop --allow-unsolved-metas #-}

module $1 where

-- This file imports every module in the project. Click on
-- a module name to go to its source.

EOF
find . -type f \( -name "*.agda" -o -name "*.lagda" \) \
        | cut -c 3- \
        | cut -f1 -d'.' \
        | sed 's/\//\./g' \
        | sort \
        | sed 's/^/open import /' \
              >> "$everything_file"
mv "$everything_file" "$1.agda"
