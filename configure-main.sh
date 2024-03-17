#!/usr/bin/env sh
cp -f _CoqProject-Main.in _CoqProject
find theories/Main -name "*.v" >> _CoqProject
coq_makefile -f _CoqProject -o Makefile
rm -f .coqdeps.d
