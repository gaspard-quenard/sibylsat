#!/bin/bash

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SOURCE_DIR="$SCRIPT_DIR/pandaPIparser-src"
EXECUTABLE="$SCRIPT_DIR/pandaPIparser"
# Keep the parameter-splitting representation used by SibylSat. Later PandaPIparser
# versions split artificial method-precondition tasks into additional methods that
# SibylSat does not currently reconstruct.
COMMIT="387d2743562e8669dd134f4184ef28d13aa9059e"

if [ -x "$EXECUTABLE" ]; then
    echo "$EXECUTABLE already exists - skipping build"
    exit 0
fi

if [ ! -d "$SOURCE_DIR/.git" ]; then
    git clone https://github.com/panda-planner-dev/pandaPIparser.git "$SOURCE_DIR"
fi

git -C "$SOURCE_DIR" config advice.detachedHead false
git -C "$SOURCE_DIR" checkout --force "$COMMIT"
git -C "$SOURCE_DIR" apply "$SCRIPT_DIR/preserve_method_preconditions.patch"
make -C "$SOURCE_DIR" -j
cp "$SOURCE_DIR/pandaPIparser" "$EXECUTABLE"
