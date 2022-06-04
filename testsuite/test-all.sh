#!/bin/sh

echo 'Calocom Compiler Test Suite'
calocom-compiler -l O3 -t bin -o matrix-mul ./matrix-mul.mag
./matrix-mul-tester ./matrix-mul

calocom-compiler -l O3 -t bin -o quicksort ./quicksort.mag
./quicksort-tester ./quicksort