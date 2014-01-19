#!/bin/sh

cd Isabelle
./cleanup.sh
cd ..

cd OCaml
./cleanup.sh
cd ..

cd Graphics
rm *.pdf_tex *.pdf
cd ..
