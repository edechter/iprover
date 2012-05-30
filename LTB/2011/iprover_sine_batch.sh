#!/bin/bash

#Copyright (C) The University of Manchester. 



PROVER=$1
CLAUSIFIER=$2
BFILE=$3

BATCHLIST=

OPTS=`awk -F ' ' ' 
	/^division.category/ {cat=$2} 
	/^limit.time.problem.wc/ {ptl=$2}  
	/^limit.time.overall.wc/ {otl=$2} 
	END{print cat,ptl,otl}' $BFILE`
CAT=`echo $OPTS|cut -d' ' -f1`
PTL=`echo $OPTS|cut -d' ' -f2`
OTL=`echo $OPTS|cut -d' ' -f3`


if grep -q '/' "$0"; then
	PREFIX=`echo "$0"|sed 's|\(.*/\).*|\1|'`
else
	PREFIX=""
fi

CPU_CORES=`grep processor /proc/cpuinfo | wc -l`

PROB_CNT=0
PROB_SOLVED=0

for PROB in `awk -F ' ' ' 
	/^% SZS start BatchProblems/ {probLines=1} 
	/^division.category/ {'CAR'=$2} 
	/^limit.time.problem.wc/ {'PTL'=$2}  
	/^% SZS end BatchProblems/ {probLines=0}  
	/^[^%]/ {if(probLines) {print $1 ":" $2} }' $BFILE`; do
	
       
	PROB_CNT=$(($PROB_CNT+1))

	INP=`echo $PROB|cut -d':' -f1`
	OUTP=`echo $PROB|cut -d':' -f2`
	echo " "
	echo "% SZS status Started for $INP"
#	"$PREFIX"TreeLimitedRun -q1 0 $PTL "$PREFIX"iprover_sine_single.sh $CAT $PTL $CPU_CORES "$PROVER" "$CLAUSIFIER" $INP $OUTP 
	echo "% SZS status Ended for $INP"

	if grep -q "% SZS status Theorem" $OUTP; then
		PROB_SOLVED=$(($PROB_SOLVED+1))
	fi	
done

echo "% Solved $PROB_SOLVED out of $PROB_CNT"

