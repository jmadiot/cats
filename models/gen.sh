#!/bin/bash

cat2coq7 -nocat -allcats -overwrite -defs ra -keep_unused
rm -f importeverything.v
