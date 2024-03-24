#!/usr/bin/env sh
cp -f _CoqProject-Elements.in _CoqProject
find theories/Elements -name "*.v" >> _CoqProject
coq_makefile -f _CoqProject -o Makefile
rm -f .coqdeps.d
