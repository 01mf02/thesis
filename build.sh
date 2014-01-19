#!/bin/sh

cd Isabelle
./build.sh
cd ..

cd OCaml
#./build.sh
cd ..


cd Graphics

echo "Converting SVG to PDF/LaTeX ..."
for i in *.svg
do inkscape -z -D --file=$i --export-pdf=`basename $i .svg`.pdf --export-latex
done

cd ..

echo "Exporting from LyX to PDF \(via pdflatex driver\) ..."
# lyx Thesis.lyx -e pdf2 > /dev/null

echo "Done."
