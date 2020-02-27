#!/bin/bash

set -euf -o pipefail
set +f

options=(
	"-overwrite -defs ra"
	"-overwrite -defs ra -nonotations"
	"-overwrite -defs stdlib"
	"-overwrite -defs stdlib -nonotations"
	"-overwrite -keep_unused -defs ra"
	"-overwrite -defined A,B,C,D,E,F,G,H,I,X"
)

for cats in "sc.cat tso.cat c11_orig.cat rc11.cat" "-allcats"
do
	for i in ${!options[@]}
	do
		echo "OPTIONS: '${options[i]}'"
		cat2coq7 ${options[i]} -makefile ${cats}
		make -kj6
	done
done
