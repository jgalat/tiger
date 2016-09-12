#!/bin/bash

for i in tests/good/*.tig; do
    echo "$i"
    ./entrega1/tiger "$i"
    read
    echo "==========================================="
done
