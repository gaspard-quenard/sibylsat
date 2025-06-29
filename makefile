# Makefile for building SibylSat as an IPASIR application
# (see github.com/biotomas/ipasir )

TARGET=$(shell basename "`pwd`")
IPASIRSOLVER ?= glucose4

all: # clean
	mkdir -p build
	cd build && cmake .. -DCMAKE_BUILD_TYPE=RELEASE -DIPASIRSOLVER=$(IPASIRSOLVER) && make -j && cp sibylsat .. && cd ..

clean:
	rm -rf $(TARGET) build/
