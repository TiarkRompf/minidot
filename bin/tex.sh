#!/bin/bash

### script to generate tex for dot.elf
### must be ran from ../tex directory!

if [[ -z $TWELF_SERVER ]]; then
    bin=twelf-server
else
    bin=$TWELF_SERVER
fi
command -v $bin >/dev/null 2>&1 || { echo >&2 "twelf-server not found. aborting..."; exit 1; }

echo -e "set chatter 0\nloadFile ../src/main/elf/dot.elf\nPrint.sgn" | $bin | awk '!/^%%/' | tail -n +2 >dot.txt
../bin/twelf2tex.py dot.txt >dot_auto.tex
pdflatex dot_auto.tex


