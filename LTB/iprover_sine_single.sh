#!/bin/bash

#Copyright (C) The University of Manchester. 
#For CASC-J5 use only


#category: LTB.SMO, LTB.MZR or LTB.CYC
CAT=$1
#time limit
TLIMIT=$2
#number of cpu cores
CPU_CORES=$3

PROVER=$4
CLAUSIFIER=$5
#problem file
INP=$6
#output file
OUTP=$7

#!!!!
#the following two functions need to be adapted for a prover, the rest should be prover-independent
#(as long as the prover passes the slice strings as options to the Vampire clausifier:)
#!!!!
MEMLIM=$((($(free|awk '/^Mem:/{print $2}')*2)/$CPU_CORES))

#echo "Memory Limit $MEMLIM"

function runProver {
# <sine strategy> <time> <out file> <background run (1 means true, other false)>
# if the process is run on background, its PID must be assigned to the global 
# variable PROVER_PID
        echo ""
	echo "Slice \"$1\" for $2 seconds"
	echo " "> $3
	echo "Slice \"$1\" for $2 seconds" >> $3
	if [ "$4" == "1" ]; then
	#    echo  \(ulimit -v $MEMLIM;"$PROVER" --clausifier "$CLAUSIFIER" --clausifier_options "--mode clausify -t $2 $1" --time_out_real $2 $INP\)
 #       	 iProver_sine/TreeLimitedRun 10000 10000 $MEMLIM "$PROVER" --clausifier "$CLAUSIFIER" --clausifier_options "--mode clausify -t $2 $1" --time_out_real $2 $INP > $3 &
	    (ulimit -v $MEMLIM -s 300000; "$PROVER" --clausifier "$CLAUSIFIER" --clausifier_options "--mode clausify -t $2 $1" --sat_out_model none  --time_out_real $2 $INP >> $3)&  
      		PROVER_PID=$!
	else	 
	    (ulimit -v $MEMLIM -s 300000;"$PROVER" --clausifier "$CLAUSIFIER" --clausifier_options "--mode clausify -t $2 $1" --sat_out_model none --time_out_real $2 $INP >> $3)
	fi
}

function wasSuccess {
# <out file>
#return 0 status if proof was found

	grep -q '% SZS status \(Theorem\|Unsatisfiable\)' $1
	return
}

#slices to be attempted
#Slice string must not be equal to "" -- slice with no arguments 
#should be denoted as " ".

if [ "$CAT" == "LTB.SMO" ]; then
    echo "$CAT Slices"
    SLICE[0]="-ss included -sd 0 -st 1.5"
    SLICE[1]="-ss included -sd 0 -st 3"
    SLICE[2]="-ss included -sd 2 -st 5 "
    SLICE[3]="-ss included -sd 6 -st 1.5"
    SLICE[4]="-ss included -sd 8 -st 2"
    SLICE[5]="-ss included -sd 10 -st 5"
    SLICE[6]="-ss included -sd 0 -st 2"
    SLICE[7]="-ss included -sd 0 -st 1.3"   
    SLICE[8]=" "
    
    SLICE[9]="-ss -sd 3 -st 3"
    SLICE[10]="-ss included -sd 4  -st 10"
    SLICE[11]="-ss included -sd 0 -st 20"

else
    if [ "$CAT" == "LTB.MZR" ]; then
	echo "$CAT Slices"
	SLICE[0]="-ss included"
	SLICE[1]="-ss included -sd 1"
	SLICE[2]="-ss included -sd 2"
	SLICE[3]=" "
	SLICE[4]="-ss included -st 2 -sd 1"
	SLICE[5]="-ss axioms"
	SLICE[6]="-ss included -st 1.2"	
	SLICE[7]="-ss included -st 1.5"
	SLICE[8]="-ss included -st 2"
	SLICE[9]="-ss included -st 5 -sd 2"
	SLICE[10]="-ss included -st 5"
	SLICE[11]="-ss included -st 5 -sd 1" 
    else
	if [ "$CAT" == "LTB.CYC" ]; then
	    echo "$CAT Slices"
	    SLICE[0]="-ss included"
            SLICE[1]="-ss included -st 5 -sd 2"
	    SLICE[2]=" "
	    SLICE[3]="-ss included -st 1.2"


	    SLICE[4]="-ss included -st 2 -sd 1"
	    SLICE[5]="-ss included -st 1.5"
	    SLICE[6]="-ss included -st 2"
	    SLICE[7]="-ss included -st 5"

	   SLICE[8]="-ss included -st 5 -sd 1" 
	   SLICE[9]="-ss axioms"
	   SLICE[10]="-ss included -sd 1"
	   SLICE[11]="-ss included -sd 2"
       else
	if [ "$CAT" == "LTB.ISA" ]; then
            SLICE[0]="-ss included -st 5 -sd 2"
            SLICE[1]="-ss included"
            SLICE[2]=" "
            SLICE[3]="-ss included -sd 2 -st 1.2"
           SLICE[4]="-ss included -sd 0 -st 1.5"
           SLICE[5]="-ss included -sd 0 -st 3"
           SLICE[6]="-ss included -sd 3 -st 3 "
           SLICE[7]="-ss included -sd 6 -st 1.5"
           SLICE[8]="-ss included -sd 8 -st 2"   
	   SLICE[9]="-ss included -st 3 -sd 4"
           SLICE[10]="-ss included -st 5 -sd 1"
           SLICE[11]="-ss included -st 5 -sd 0"
          else	
	    echo "Category $CAT"
	    echo "Default: All Slices"
	    SLICE[0]="-ss included"
	    SLICE[1]="-ss included -sd 1"
	    SLICE[2]=" "
	    SLICE[3]="-ss included -sd 2"
	    SLICE[4]="-ss included -st 1.2"
	    SLICE[5]="-ss axioms"
	    SLICE[6]="-ss included -st 2 -sd 3"
	    SLICE[7]="-ss included -st 1.5"
	    SLICE[8]="-ss included -st 2"
	    SLICE[9]="-ss included -st 5 -sd 5"
	    SLICE[10]="-ss included -st 5"
	    SLICE[11]="-ss included -st 5 -sd 1" 
 	   
          fi
       fi
   fi
fi

function killChildProcesses {
	#first store child list and only then start killing them (as 'ps' is a child as well)
	local CHILDREN=`ps -o pid --no-heading --ppid $$`
	local CHILD
	
	for CHILD in $CHILDREN; do 
		kill -9 $CHILD 2>/dev/null
	done
}

function terminate {
# <SZS status> <process result>
	echo "% SZS status $1 for $INP" >> $OUTP
	echo "% SZS status $1 for $INP"

        grep "% SZS answers Tuple" $OUTP
        echo ""
	killChildProcesses

	rm -rf $TMP
	wait
	exit $2
}

function timeOut {
	terminate GaveUp 1
}

function interrupted {
	terminate User 1
}

function success {
	terminate Theorem 0
}

function postprocessRun {
# <prover output>
# should be called on output of each run of a prover

	#we want to keep the record of the run of the prover, but we 
	#don't want to report failure while we're still trying
	grep -v "% SZS status" $1 >> $OUTP
	if wasSuccess $1; then
		success
	fi
}

function addChild {
# <pid> <output file> <slice time>

	CHILDREN[$CHILD_CNT]=$1
	PROCESS_OUTPUTS[$1]=$2
	PROCESS_STARTS[$1]=$SECONDS
	PROCESS_TIMES[$1]=$3
	CHILD_CNT=$(($CHILD_CNT+1))
	TAVAIL=$(($TAVAIL-$3))
}

function handleDeadChildProcess {
#if there is a newly terminated child process, run the postprocessRun function for it
#and return 0; otherwise return 1. (we return 0 only if the run was unsuccessful;
#if proof was found, we terminate)
        local I=0
        while [ "$I" -lt "$CHILD_CNT" ]; do
        	local CHILD_PID=${CHILDREN[$I]}
		if [ '!' -e /proc/$CHILD_PID ]; then
			local CHILD_OUT=${PROCESS_OUTPUTS[$CHILD_PID]}
			postprocessRun $CHILD_OUT
			#we get here only if the prover run was unsuccessful
			
			local SAVED_TIME=$((${PROCESS_STARTS[$CHILD_PID]}+${PROCESS_TIMES[$CHILD_PID]}-$SECONDS))
			TAVAIL=$(($TAVAIL+$SAVED_TIME))
			
			CHILD_CNT=$(($CHILD_CNT-1))
			CHILDREN[$I]=${CHILDREN[$CHILD_CNT]}
			return 0
		fi
		I=$(($I+1))
        done
        return 1
}


trap timeOut SIGALRM
trap timeOut SIGXCPU
trap interrupted SIGINT

#this variable is every second increased by shell
SECONDS=0

TMP=`mktemp -d`
rm -f $OUTP

SLICE_CNT=0
while [ "${SLICE[$SLICE_CNT]}" != "" ]; do
	SLICE_CNT=$(($SLICE_CNT+1))
done

if [ "$CPU_CORES" == 1 ]; then

#single core implementation
SLICE_INDEX=0
while [ "${SLICE[$SLICE_INDEX]}" != "" ]; do
	SLC="${SLICE[$SLICE_INDEX]}"
	
	TIME_REMAINS=$(( $TLIMIT-$SECONDS ))

	if [ $TIME_REMAINS -le 0 ]; then
		timeOut
	fi
	
	SLICES_REMAIN=$(($SLICE_CNT-$SLICE_INDEX))
	SLICE_TIME=$(( ($TIME_REMAINS+$SLICES_REMAIN-1)/$SLICES_REMAIN ))
	
	
	SLICE_OUT=$TMP"/1.tmp"
	runProver "$SLC" $SLICE_TIME $SLICE_OUT
	postprocessRun $SLICE_OUT
	
	SLICE_INDEX=$(($SLICE_INDEX+1))
done

else

#parallel implementation

CORES_LEFT=$CPU_CORES

#number of child processes
CHILD_CNT=0

#array of child processes
#on indexes from 0 to $CHILD_CNT-1 it contains children's PIDs
CHILDREN[0]=0

#array of children's output files
#indexed by children's PIDs, it contains their output filenames
PROCESS_OUTPUTS[0]=0

#array of children's start times
#indexed by children's PIDs, it contains content of the $SECONDS 
#variable at the time of their start
PROCESS_STARTS[0]=0

#array of children's time limits
#indexed by children's PIDs
PROCESS_TIMES[0]=0


#amount of available CPU time
TAVAIL=$(($TLIMIT*$CPU_CORES))

SLICE_INDEX=0
while [ $SLICE_INDEX -lt $SLICE_CNT ]; do
	SLC="${SLICE[$SLICE_INDEX]}"
	
	SLICES_REMAIN=$(($SLICE_CNT-$SLICE_INDEX))

#	SLICE_TIME=$(($TAVAIL/$SLICES_REMAIN))

#KK hack we run 0 slice until for the whole time	
	
#	if [ "$SLICE_INDEX" == 0 ]; then
#	    SLICE_TIME=$(($TLIMIT))
#	fi

#KK Slice time is always TILIMIT but if a core is freed then it is occupied by the next slice
	SLICE_TIME=$(($TLIMIT))
	SLICE_OUT=$TMP"/"$SLICE_INDEX".tmp"
	runProver "$SLC" $SLICE_TIME $SLICE_OUT 1
	
	addChild $PROVER_PID $SLICE_OUT $SLICE_TIME

	CORES_LEFT=$(($CORES_LEFT-1))
	
	while [ $CORES_LEFT -le 0 ]; do
		while ! handleDeadChildProcess; do
			sleep 0.5
		done
		CORES_LEFT=$(($CORES_LEFT+1))
	done
	
	SLICE_INDEX=$(($SLICE_INDEX+1))
done

while [ $CHILD_CNT -gt 0 ]; do
	while ! handleDeadChildProcess; do
		sleep 0.5
	done
done


fi

timeOut
