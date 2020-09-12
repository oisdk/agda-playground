#!/usr/bin/env bash

sh scripts/generate-everything-agda.sh EveryModule
trap "rm -f agda/EveryModule.agda" 0 2 3 15
( cd agda ; agda EveryModule.agda )
