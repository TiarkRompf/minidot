#!/bin/bash

if [[ -z $TWELF_SERVER ]]; then
    bin=twelf-server
else
    bin=$TWELF_SERVER
fi
command -v $bin >/dev/null 2>&1 || { echo >&2 "twelf-server not found. aborting..."; exit 1; }

echo -e "set chatter 1\nConfig.read src/main/elf/sources.cfg\nConfig.load" | $bin
echo

for f in "$@"; do
    echo -e "set chatter 1\nloadFile $f" | $bin
done


