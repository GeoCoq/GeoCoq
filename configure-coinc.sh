#!/usr/bin/env sh
cp -f _CoqProject-Coinc.in _CoqProject
find theories/Coinc -name "*.v" >> _CoqProject
coq_makefile -f _CoqProject -o Makefile
rm -f .coqdeps.d
