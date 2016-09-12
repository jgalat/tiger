#!/bin/bash

for i in tests/syntax/*.tig; do
    echo "$i"
    ./entrega1/tiger "$i"
    read
    echo "==========================================="
done
