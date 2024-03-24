#!/usr/bin/env sh
cp -f _CoqProject-Axioms.in _CoqProject
find theories/Axioms -name "*.v" >> _CoqProject
coq_makefile -f _CoqProject -o Makefile
rm -f .coqdeps.d
