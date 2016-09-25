#!/usr/bin/env bash

function check_keyword() {
    echo "$1:"
    grep $1 P??.v
    echo ''
}

check_keyword 'FILL_IN_HERE'
for keyword in `cat forbidden.txt`; do
    check_keyword ${keyword}
done
