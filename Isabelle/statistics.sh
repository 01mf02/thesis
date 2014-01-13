#!/bin/sh
printf '\\begin{itemize}\n'

USAGE=$(($(cat *.thy | wc -c) / 1024))
LINES=`cat *.thy | grep -c "[^ ]"`
printf '\\item Size of Isabelle theory: %s KB, %s lines\n' "$USAGE" "$LINES"

DEFS=`grep '^definition' *.thy | wc -l`
FUNS=`grep '^fun' *.thy | wc -l`
LEMS=`grep -e '^lemma' -e '^theorem' *.thy | wc -l`
printf '\\item Number of definitions: %s\n' "$DEFS"
printf '\\item Number of functions: %s\n' "$FUNS"
printf '\\item Number of lemmata: %s\n' "$LEMS"

printf '\\onslide<2->\\item Amount of hair lost fighting with Isabelle: ...\n'

printf '\\end{itemize}\n'
