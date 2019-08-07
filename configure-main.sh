#!/usr/bin/env sh
cp -f _CoqProject.in _CoqProject
find . -name "*.v" | grep -v "Tactics/Coinc/" | grep -v Axioms | grep -v OriginalProofs | grep -v Utils | grep -v Sandbox | grep -v finish | grep -v euclid_to_tarski | grep -v POF >> _CoqProject
coq_makefile -f _CoqProject -o Makefile
rm -f .coqdeps.d
