#!/bin/sh

echo "Writing OCaml program size ..."
mkdir -p sizes
wc -l Examples.ml Grammar.ml Groof.ml Main.ml | tail -n 1 | cut -d " " -f 3 > sizes/programsize.txt
echo Cumulative program size: `cat sizes/programsize.txt`

echo "Building OCaml files ..."
ocamlbuild -libs nums Main.d.byte

echo "Generating statistics from OCaml program ..."
./Main.d.byte > /dev/null

echo "Creating plots ..."
gnuplot batch.plt 2> /dev/null
rm fit.log
