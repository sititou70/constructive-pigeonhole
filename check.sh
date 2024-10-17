#!/bin/sh
set -eu
cd $(dirname $0)

echo "-R src PHR" >_CoqProject
find src | grep ".v$" >>_CoqProject
coq_makefile -f _CoqProject -o Makefile
make
