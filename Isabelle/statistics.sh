#!/bin/sh
echo "\\\\begin{itemize}"

USAGE=`du -hc *.thy | grep total | cut -f1`
LINES=`cat *.thy | wc -l`
echo "\\item Size of Isabelle theory: $USAGE, $LINES lines"

DEFS=`grep '^definition' *.thy | wc -l`
FUNS=`grep '^fun' *.thy | wc -l`
LEMS=`grep '^lemma' *.thy | wc -l`
echo "\\item Number of definitions/functions: $DEFS/$FUNS"
echo "\\item Number of lemmata: $LEMS"

echo "\\end{itemize}"
