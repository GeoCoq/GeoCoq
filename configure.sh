#!/usr/bin/env sh
cp -f _CoqProject.in _CoqProject
find theories -name "*.v" >> _CoqProject
coq_makefile -f _CoqProject -o Makefile
rm -f .coqdeps.d
