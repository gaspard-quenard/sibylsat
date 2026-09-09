#!/bin/bash

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SOURCE_DIR="$SCRIPT_DIR/pandaPIgrounder-src"
EXECUTABLE="$SCRIPT_DIR/pandaPIgrounder"
COMMIT="4ff15b2828d893a7976a92cd60cc63a61f1baffc"

if [ -x "$EXECUTABLE" ]; then
    echo "$EXECUTABLE already exists - skipping build"
    exit 0
fi

if [ ! -d "$SOURCE_DIR/.git" ]; then
    git clone https://github.com/panda-planner-dev/pandaPIgrounder.git "$SOURCE_DIR"
fi

git -C "$SOURCE_DIR" config advice.detachedHead false
git -C "$SOURCE_DIR" checkout --force "$COMMIT"
git -C "$SOURCE_DIR" apply "$SCRIPT_DIR/pandaPiGrounding_modifications.patch"
git -C "$SOURCE_DIR" submodule update --init
git -C "$SOURCE_DIR/cpddl" apply "$SOURCE_DIR/0002-makefile.patch"
make -C "$SOURCE_DIR/cpddl" boruvka opts bliss lpsolve
make -C "$SOURCE_DIR/cpddl" -j
make -C "$SOURCE_DIR/src" -j
cp "$SOURCE_DIR/pandaPIgrounder" "$EXECUTABLE"
