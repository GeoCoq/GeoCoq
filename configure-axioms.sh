#!/usr/bin/env sh
cp -f _CoqProject.in _CoqProject
find . -name "*.v" | grep Axioms >> _CoqProject
find . -name "*.v" | grep Definitions >> _CoqProject
find . -name "*.v" | grep finish >> _CoqProject
coq_makefile -f _CoqProject -o Makefile
