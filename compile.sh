#!/bin/bash

rm -rf build

# FILES=$(find -name "*.agda" -type f)
# for f in $FILES; do agda2hs $f -o build; done

agda2hs agda/TypeChecker.agda -o build
