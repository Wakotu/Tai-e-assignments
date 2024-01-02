#!/usr/bin/env bash

# WARNING: should be invoked only once with caution
PA="$1"

git checkout -b "$PA"

find . -maxdepth 1 -type f -name "*.sh" ! -name "setup.sh" -exec cp {} "${PA}/tai-e/" \;
cd "${PA}/tai-e" || exit
