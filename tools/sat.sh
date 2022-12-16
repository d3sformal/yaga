#!/bin/sh

script_path=$(realpath "$0")
script_dir=$(dirname "$script_path")
bin=$(realpath "$script_dir/../build-release/sat")

echo "path,result"
for path in $@
do
    out=$("$bin" "$path")
    res=$(echo "$out" | grep 'SAT')
    echo "$path,$res"
done
