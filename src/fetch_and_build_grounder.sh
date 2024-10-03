#!/bin/bash

set -e

if [ -f ../lib/pandaPiGrounder ]; then
    echo "pandaPIgrounder already compiled - skipping build"
    exit
fi

# Fetch a clean state of pandaPIparser
if [ ! -d pandaPiGrounder ]; then
    echo "Fetching pandaPIgrounder ..."
    git clone https://github.com/panda-planner-dev/pandaPIgrounder.git
    cd pandaPIgrounder
else
    cd pandaPIgrounder
    git clean -f
fi

# Checkout correct commit (can be updated but must be manually checked to build cleanly)
git config advice.detachedHead false
git checkout a1a937e766c47169f8f1ee8036405607182afdd5


# Patch pandaPiGrounder to add 4 options:
# 1. only-write-state-features -> write only state features in the ground files so skip methods and operators
# 2. quick-compute-state-features -> if the problem is slow to compute, compute an overestimation of the state features more quickly but lose in optimality. Need flag only-write-state-features to be set.
# 3. exit-after-invariants -> exit after having computed lifted FAM groups. Needs option invariants
# 4. out-invariants -> write the lifted FAM groups to the file specified. Needs option invariants string default=""
echo "Applying modifications..."
git apply ../pandaPiGrounding_modifications.patch


# Build modified standalone executable for debugging purposes
git submodule init
git submodule update
cd cpddl
git apply ../0002-makefile.patch
make boruvka opts bliss lpsolve
make -j
cd ../src
make -j
cd ../
cp pandaPIgrounder ../../lib/
echo "Copied pandaPIgrounder executable into lib directory."
