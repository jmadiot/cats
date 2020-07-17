#!/bin/bash

set -euo pipefail
IFS=$'\n\t'

echo "This will git clone the current repository to a temp dir in /tmp and launch a build there."
echo "Press [enter] to continue, [ctrl-C] to abort."
read

TMP=$(mktemp -t -d cats-XXXX)
git clone . $TMP
cd $TMP
./configure.sh
make -j7
echo "Build should have been successful."

echo "I will now delete all created files in:"
echo $TMP
echo "Press [enter] to continue, [ctrl-C] to abort."
read

cd -
rm -rf $TMP
