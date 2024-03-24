#!/usr/bin/env sh
cp -f _CoqProject-Algebraic.in _CoqProject
find theories/Algebraic -name "*.v" >> _CoqProject
coq_makefile -f _CoqProject -o Makefile
rm -f .coqdeps.d
