#!/bin/bash

if [ ! -f "locallhs2TeX.lhs" ]; then
    echo "%include polycode.fmt" > "locallhs2TeX.lhs"
fi

if [ ! -f "locallhs2TeX.sty" ]; then
    lhs2TeX -o "locallhs2TeX.sty" "locallhs2TeX.lhs"
fi

find haskell -type f -name '*.lhs' | while read -r code ; do
    dir=$(dirname "$code")
    file="$dir"/$(basename "$code" .lhs).tex
    if [ ! -e "$file" ]
    then
        ./scripts/haskell-from-toplevel.sh "$code"
    fi
done
