#!/bin/sh
export MROOT=$PWD
echo $MROOT
cd simp
make clean
make rs
cp minisat_static ../hhlmuc
