#!/bin/bash

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SOURCE_DIR="$SCRIPT_DIR/aiplan4rust-src"
EXECUTABLE="$SCRIPT_DIR/aiplan"
COMMIT="7704d0dc9dbb9cbf1950524059f6f66a67b360d7"

if [ -x "$EXECUTABLE" ]; then
    echo "$EXECUTABLE already exists - skipping build"
    exit 0
fi

if [ ! -d "$SOURCE_DIR/.git" ]; then
    git clone --filter=blob:none --no-checkout https://github.com/pellierd/aiplan4rust.git "$SOURCE_DIR"
    git -C "$SOURCE_DIR" sparse-checkout set --no-cone /Cargo.toml /Cargo.lock /build.rs /src/
fi

git -C "$SOURCE_DIR" fetch --depth 1 origin "$COMMIT"
git -C "$SOURCE_DIR" checkout --detach "$COMMIT"
cargo build --release --manifest-path "$SOURCE_DIR/Cargo.toml"
cp "$SOURCE_DIR/target/release/aiplan" "$EXECUTABLE"
