#!/usr/bin/env sh
cp -f _CoqProject.in _CoqProject
find . -name "*.v" | grep -v Sandbox | grep -v POF >> _CoqProject

# We lack a few minutes to be able to build the whole library.
#sed -i.bak '/Ch16_coordinates_with_functions\.v/d'             _CoqProject
#sed -i.bak '/Elements\/OriginalProofs\/proposition_30\.v/d'    _CoqProject
#sed -i.bak '/Elements\/OriginalProofs\/proposition_44A\.v/d'   _CoqProject
#sed -i.bak '/Elements\/OriginalProofs\/proposition_44\.v/d'    _CoqProject
#sed -i.bak '/Elements\/OriginalProofs\/proposition_45\.v/d'    _CoqProject
#sed -i.bak '/Elements\/OriginalProofs\/book1\.v/d'             _CoqProject
#sed -i.bak '/Elements\/Statements\/Book_1\.v/d'                _CoqProject
#sed -i.bak '/Elements\/Statements\/Book_3\.v/d'                _CoqProject
sed -i.bak '/main.v/d'                                         _CoqProject

coq_makefile -f _CoqProject -o Makefile
rm -f .coqdeps.d
