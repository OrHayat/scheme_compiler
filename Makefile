MKDIR := $(dir $(realpath $(firstword $(MAKEFILE_LIST))))
BASEDIR := $(PWD)

.DEFAULT:
	cd $(MKDIR) && ocaml compiler.ml $@ > $@.s && nasm -f elf64 -o $@.o $@.s && gcc -m64 -o $@ $@.o && mv $@ $(BASEDIR)
