#!/bin/bash

if [ -f libuwrmaxsat.so ]; then
    echo "uwrmaxsat already compiled - skipping build"
    exit
fi


# To compile the UWrMaxSat solver, we need to have both a SAT solver and the maxpre preprocessor.

# First, we get and compile the maxpre preprocessor 
if [ ! -d maxpre ]; then
    git clone https://github.com/Laakeri/maxpre
fi

# Build the dynamic library of the maxpre preprocessor
cd maxpre
sed -i 's/-g/-fPIC -D NDEBUG/' src/Makefile
make lib
cd ..



# Then, we get and copile the SAT solver used by UWrMaxSat which is COMiniSatPS (other can be used as well)
if [ ! -d cominisatps ]; then
    git clone https://github.com/marekpiotrow/cominisatps
fi

cd cominisatps
rm core simp mtl utils && ln -s minisat/core minisat/simp minisat/mtl minisat/utils .
CXXFLAGS=-fPIC make lr
cd ..



# Finally, we get and compile the UWrMaxSat solver
if [ ! -d uwrmaxsat ]; then
    git clone https://github.com/marekpiotrow/UWrMaxSat uwrmaxsat
    cd uwrmaxsat
else
    cd uwrmaxsat
    git clean -f
fi

# Checkout correct commit (can be updated but must be manually checked to build cleanly)
git config advice.detachedHead false
git checkout a8a97d4d10657d64f498f53eac6403c2b3e5df90

# Apply the patch uwrmaxsat_modifications.patch which is situated in the parent directory
# And is use to improve the capacity of the incremental MaxSat solver (can reuse cores in subsequent calls)
git apply ../uwrmaxsat_modifications.patch
rm -f config.mk
make config
USESCIP= make lsh
cp build/dynamic/lib/libuwrmaxsat.so* ../
