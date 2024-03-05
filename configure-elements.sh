#!/usr/bin/env sh
cp -f _CoqProject-Elements.in _CoqProject
find . -name "*.v" | grep OriginalProofs   >> _CoqProject
find . -name "*.v" | grep euclid_to_tarski >> _CoqProject
coq_makefile -f _CoqProject -o Makefile
rm -f .coqdeps.d
