#!/bin/sh
isabelle build -D .
./statistics.sh > statistics.tex
