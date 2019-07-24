#!/usr/bin/env sh
cp -f _CoqProject.in _CoqProject
find . -name "*.v" | grep -v Sandbox >> _CoqProject
coq_makefile -f _CoqProject -o Makefile
