#!/usr/bin/env bash

dir='submit'

if ! [[ -d "$dir" ]]; then
	mkdir "$dir"
fi

files=()

basenames=('ConstantPropagation.java' 'Solver.java' 'WorkListSolver.java')

for name in "${basenames[@]}"; do
	files+=($(find . -name "$name"))
done

# echo "${files[@]}"

# copy files
for i in "${!files[@]}"; do
	if ! [[ -e "${dir}/${basenames[$i]}" ]]; then
		cp "${files[$i]}" "$dir"
	fi
done

parent_dir=$(dirname "$(pwd)")
parent_base=$(basename "$parent_dir")
cd "$dir" || exit
zip "${parent_base}.zip" *
