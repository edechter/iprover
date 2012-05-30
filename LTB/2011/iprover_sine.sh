#!/bin/bash

#Copyright (C) The University of Manchester. 


PROVER=$1
CLAUSIFIER=$2
BFILE=$3

PROB_CNT=0
PROB_SOLVED=0

STRATPROBS=0

if grep -q '/' "$0"; then
	PREFIX=`echo "$0"|sed 's|\(.*/\).*|\1|'`
else
	PREFIX=""
fi

CPU_CORES=`grep processor /proc/cpuinfo | wc -l`


while read LINE
do
    case $LINE in 
	"% SZS start BatchConfiguration"*)
	    ;;
	"division.category"*) 	    
	    CAT=`echo $LINE | awk '{print $2}'`
	  #  echo "$CAT"
	    ;;
	"output.required"*) 
	    OUTREQ=`echo $LINE | awk '{print $2}'`
	  #  echo $OUTREQ
	    ;;
	"output.desired"*) 
	    OUTDES1=`echo $LINE | awk '{print $2}'`
	    # can be more desirable outputs
	  #  echo $OUTDES1
	    ;;
	"limit.time.problem.wc"*)
	    PTL=`echo $LINE | awk '{print $2}'`
	 #   echo $PTL
	    ;;
	"% SZS start BatchProblems"*)
	    STRATPROBS=1
	    ;;
	"% SZS end BatchProblems"*)
	    STRATPROBS=0
	    ;;  

	*)
	    if [ $STRATPROBS -eq 1 ]; then
		INP=`echo $LINE | awk '{print $1}'`
		OUTP=`echo $LINE | awk '{print $2}'`
	#	echo "INP=$INP"
	#	echo "OUTP=$OUTP"
		echo " "
		echo "% SZS status Started for $INP"
		echo " "
		"$PREFIX"TreeLimitedRun -q1 0 $PTL "$PREFIX"iprover_sine_single.sh $CAT $PTL $CPU_CORES "$PROVER" "$CLAUSIFIER" $INP $OUTP 
		echo " "
		echo "% SZS status Ended for $INP"
		echo " "

		if grep -q "% SZS status Theorem" $OUTP; then
		    PROB_SOLVED=$(($PROB_SOLVED+1))
		fi
	    fi
	    ;;

    esac
done < $BFILE
