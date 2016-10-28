#!/bin/bash

for i in tests/good/*.tig; do
    echo "$i"
    ./entrega3/tiger "$i" -code
    read
    echo "==========================================="
done
