#!/usr/bin/env bash

dir='submit'

if [[ -d "$dir" ]]; then
	rm -r "$dir"
fi

mkdir "$dir"

files=()

basenames=('DeadCodeDetection.java')

for name in "${basenames[@]}"; do
	files+=($(find . -name "$name"))
done

# echo "${files[@]}"

# copy files
for i in "${!files[@]}"; do
	cp "${files[$i]}" "$dir"
done

parent_dir=$(dirname "$(pwd)")
parent_base=$(basename "$parent_dir")
cd "$dir" || exit
zip "${parent_base}.zip" *

PA_DIR="${HOME}/Documents/pa/"
mkdir -p "$PA_DIR"
cp -f "${parent_base}.zip" "$PA_DIR"
