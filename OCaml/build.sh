#!/bin/sh

echo "Writing OCaml program size to programsize.txt ..."
wc -l Examples.ml Grammar.ml Groof.ml Main.ml | tail -n 1 | cut -d " " -f 3 > programsize.txt
echo Cumulative program size: `cat programsize.txt`

echo "Building OCaml files ..."
ocamlbuild -libs nums Main.d.byte

echo "Generating statistics from OCaml program ..."
./Main.d.byte > /dev/null

echo "Creating plots ..."
gnuplot batch.plt 2> /dev/null