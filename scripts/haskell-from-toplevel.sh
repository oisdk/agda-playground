#!/usr/bin/env bash

withcode=$1
nocode=${withcode#"haskell/"}
cd haskell || exit
dir=$(dirname "$nocode")
file=$(basename "$nocode" .lhs).tex
lhs2TeX -o "$dir/$file" "$nocode"
