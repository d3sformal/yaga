#!/bin/sh

script_path=$(realpath "$0")
script_dir=$(dirname "$script_path")
bin=$(realpath "$script_dir/../build-release/sat")

echo "path,result,time,conflicts,decisions,restarts"
for path in $@
do
    out=$("$bin" "$path")
    res=$(echo "$out" | grep 'SAT')
    stats=$(echo "$out" | grep = | cut -d'=' -f2 | sed 's/ //g' | paste -sd',') 
    echo "$path,$res,$stats"
done
