#!/bin/sh

echo Building OCaml files ...
ocamlbuild Main.d.byte

echo Generating statistics from OCaml program ...
./Main.d.byte > /dev/null

echo Creating plots ...
gnuplot batch.plt

echo Converting SVG to PDF/LaTeX ...
for i in *.svg
do inkscape -z -D --file=$i --export-pdf=`basename $i .svg`.pdf --export-latex
done

echo Exporting from LyX to PDF \(via pdflatex driver\) ...
lyx Thesis.lyx -e pdf2 > /dev/null

echo Done.
