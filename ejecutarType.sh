#!/bin/bash

for i in tests/type/*.tig; do
    echo "$i"
    ./entrega1/tiger "$i"
    read
    echo "==========================================="
done
