#!/usr/bin/env sh
cp -f Make.in Make
find . -name "*.v" | grep -v Sandbox >> Make

# We lack a few minutes to be able to build the whole library.
sed -i.bak '/Ch16_coordinates_with_functions\.v/d'             Make
sed -i.bak '/Elements\/Statements\/Book_1\.v/d'                Make
sed -i.bak '/Elements\/Statements\/Book_3\.v/d'                Make
sed -i.bak '/main.v/d'                                         Make

coq_makefile -f Make -o Makefile
