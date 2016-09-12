#!/bin/bash

for i in tests/good/*.tig; do
    if [ "$i" != "tests/good/test06.tig" ] && [ "$i" != "tests/good/test07.tig" ]; then
        echo "$i"
        ./entrega1/tiger "$i" -inter
        read
        echo "==========================================="
    fi

done
