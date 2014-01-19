#!/bin/sh

echo "Building Isabelle files ..."
isabelle build -D .

echo "Generating Isabelle statistics ..."
./statistics.sh > statistics.tex
