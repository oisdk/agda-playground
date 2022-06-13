#!/usr/bin/env bash

version_string="$(agda --version)"
version=${version_string#"Agda version "}
artefact="_build/$version/agda/${1}i"
[ -f "$artefact" ] && rm "$artefact"
time agda "${1}"
