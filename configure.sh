#!/bin/bash

set -euxo pipefail
IFS=$'\n\t'

echo "-Q . Catincoq" > _CoqProject
echo >> _CoqProject

cd models && ./gen.sh ; cd ..
make -C zoo clean
make -C zoo sc_nosm.v tso_nosm.v lamport.v x86tso.v

ls */*.v \
   | grep -v 'DecidablePropKat' \
   | grep -v 'poubelle/' \
   | grep -v '^easy_tso_sc' \
   | grep -v '^testing/' \
   | grep -v '^lib/dprop_rel.v' \
   | grep -v '^lib/dprop.v' \
   >> _CoqProject

rm -f */*.vo */*.vok */*.vos */*.glob */.*.aux

coq_makefile -f _CoqProject -o Makefile
