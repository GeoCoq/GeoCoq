#!/usr/bin/env sh
cp -f _CoqProject-Coinc.in _CoqProject
find . -name "*.v" | grep "Tactics/Coinc/" >> _CoqProject
find . -name "*.v" | grep Utils            >> _CoqProject
coq_makefile -f _CoqProject -o Makefile
rm -f .coqdeps.d
