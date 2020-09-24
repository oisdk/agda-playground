#!/usr/bin/env bash

artefact="_build/2.6.1/agda/${1}i"
[ -f "$artefact" ] && rm "$artefact"
time agda "${1}"
