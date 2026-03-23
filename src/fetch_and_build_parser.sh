#!/bin/bash

set -e

if [ -f ../lib/libpandaPIparser.a ]; then
    echo "../lib/libpandaPIparser.a already exists - skipping build"
    exit
fi

# Fetch repository if needed
if [ ! -d pandaPIparser ]; then
    echo "Fetching pandaPIparser ..."
    git clone https://github.com/panda-planner-dev/pandaPIparser.git
fi

cd pandaPIparser

# Force exact clean state
git config advice.detachedHead false
git checkout 334393290c13089a1a7e0ced070cc272f76fedf2
git reset --hard 334393290c13089a1a7e0ced070cc272f76fedf2
git clean -fdx

# Build original standalone executable for debugging purposes
make -j
cp pandaPIparser ../../lib/pandaPIparserOriginal
echo "Copied original pandaPIparser executable into lilotane root directory."
make clean

# Patch pandaPIparser with adapted makefile and "library" header
cp ../panda_makefile makefile
cp ../libpanda.hpp src/

# Replace the literal used for compiling out method preconditions
sed -i 's/__method_precondition_/<method_prec>/g' src/domain.hpp
sed -i 's/__immediate_method_precondition_/<method_prec>/g' src/domain.hpp

# Apply modifications to pandaPIparser for deordering
echo "Applying modifications to pandaPIparser for deordering ..."
git apply ../pandaPIparser_deordering.patch


# Build library (internally does a patch of pandaPIparser's main.cpp)
make -j library
cp build/libpandaPIparser.a ../../lib/
echo "Copied libpandaPIparser.a into lib/ directory."

# Build modified standalone executable for debugging purposes
make executable
cp pandaPIparser ../../lib/
echo "Copied pandaPIparser executable into lilotane root directory."
