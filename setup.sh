#!/usr/bin/env bash

PA="$(git rev-parse --abbrev-ref HEAD)"

find . -maxdepth 1 -type f -name "*.sh" ! -name "setup.sh" -exec cp {} "${PA}/tai-e/" \;

sudo chmod 755 "${PA}/tai-e/gradlew"
