#!/bin/bash

set -e

if [ -f ../lib/pandaPIgrounder ]; then
    echo "pandaPIgrounder already compiled - skipping build"
    exit
fi

# Fetch a clean state of pandaPIparser
if [ ! -d pandaPIgrounder ]; then
    echo "Fetching pandaPIgrounder ..."
    git clone https://github.com/panda-planner-dev/pandaPIgrounder.git
fi

cd pandaPIgrounder

# Take the submodule in a clean state
git submodule update --init --recursive

# Force exact clean state
git config advice.detachedHead false
git checkout 4ff15b2828d893a7976a92cd60cc63a61f1baffc
git reset --hard --recurse-submodules 4ff15b2828d893a7976a92cd60cc63a61f1baffc
git clean -ffdx


# Patch pandaPiGrounder to add 4 options:
# 1. only-write-state-features -> write only state features in the ground files so skip methods and operators
# 2. quick-compute-state-features -> if the problem is slow to compute, compute an overestimation of the state features more quickly but lose in optimality. Need flag only-write-state-features to be set.
# 3. exit-after-invariants -> exit after having computed lifted FAM groups. Needs option invariants
# 4. out-invariants -> write the lifted FAM groups to the file specified. Needs option invariants string default=""
echo "Applying modifications..."
git apply ../pandaPiGrounding_modifications.patch


cd cpddl
git apply ../0002-makefile.patch
make boruvka opts bliss lpsolve
make -j
cd ../src
make -j
cd ../
cp pandaPIgrounder ../../lib/
echo "Copied pandaPIgrounder executable into lib directory."
