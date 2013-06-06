#!/bin/bash

#Copyright (C) The University of Manchester. 


PROVER=$1
CLAUSIFIER=$2
#overall time limit 0 is unlimited
#for simplicity unlimited it is replaced by MAXTIME
MAXTIME=10000000
OTLIMIT=$3
#batch file
BFILE=$4


#test $OTLIMIT is an integer

test $OTLIMIT -ge 0 2>/dev/null

if [[ $? -ne 0 || $# -ne 4 || $1 = "-h" || $1 = "--help" || ! -e $PROVER || ! -e $CLAUSIFIER || ! -e $BFILE ]]
then
    echo ""
    echo "Usage: LTB/`basename $0` iproveropt VClausifier/vclausify_rel timelimit LTB.batch"
    echo "where timelimit is overall time limit; 0 stands for MAXTIME=$MAXTIME"
    echo "      LTB.batch is a batch specification file see CASC-J6 description."
    echo ""
    exit 1
fi

if [ $OTLIMIT -eq 0 ]; then
    OTLIMIT=$MAXTIME
fi

echo ""
echo "Overall Time Limit $OTLIMIT"


PROB_CNT=0
PROB_SOLVED=0

STRATPROBS=0

if grep -q '/' "$0"; then
	PREFIX=`echo "$0"|sed 's|\(.*/\).*|\1|'`
else
	PREFIX=""
fi

CPU_CORES=`grep processor /proc/cpuinfo | wc -l`
#count the total  number of problems 

#BATCHPROBNUM is an array of batch_num -> number of problems in this batch
declare -a BATCHPROBNUM

PROBNUM=0

BATCHCOUNT=0

while read LINE
do
    case $LINE in 
	"% SZS start BatchProblems"*)
	    STRATPROBS=1
	    ;;
	"% SZS end BatchProblems"*)
	    STRATPROBS=0
	    BATCHPROBNUM[$BATCHCOUNT]=$PROBNUM
	    PROBNUM=0
	    BATCHCOUNT=$(($BATCHCOUNT+1))	    
	    ;;  
	*)
	    if [ $STRATPROBS -eq 1 ]; then
		PROBNUM=$(($PROBNUM+1))
	    fi
	    ;;
    esac
done < $BFILE

#number of problems in batches are in from  BATCHPROBNUM which is indexed 
#from 0 to TOTALNUMBATCHES-1

TOTALNUMBATCHES=$BATCHCOUNT

echo ""
echo "Number of Batches: $TOTALNUMBATCHES"
echo ""

PROBTRIED=0
PROBREMAINS=$PROBNUM

#$SECONDS -- bash var number of seconds the script run
# space in "division.category " is important, since Geoff also has division.category.

BATCHCOUNT=0

while read LINE
do
    case $LINE in 
	"% SZS start BatchConfiguration"*)
	    PROBNUM=${BATCHPROBNUM[$BATCHCOUNT]}
	    PROBREMAINS=$PROBNUM
	    echo "Batch: $BATCHCOUNT Problem num: $PROBNUM"
	    ;;
	"division.category "*) 	    
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
	    PTLI=`echo $LINE | awk '{print $2}'`
	 #   echo $PTL
	    if [ $PTLI -eq 0 ]; then
		PTLI=$MAXTIME
	    fi
	    ;;
	"limit.time.overall.wc"*)
	    OTLIMIT=`echo $LINE | awk '{print $2}'`
	    echo "batch limit = $OTLIMIT"
	    ;;
	"% SZS start BatchProblems"*)
	    STRATPROBS=1
	    ;;
	"% SZS end BatchProblems"*)
	    STRATPROBS=0
	    BATCHCOUNT=$(($BATCHCOUNT+1))
	    ;;  

	*)


	    if [ $STRATPROBS -eq 1 ]; then
#get problem time limit 
#it is minumum of time limits based on verall time limit 
#and PTLI, (0 is unlimited in both cases)

#PTLO: first get timelimit based on overall timelimit and the number of problems 
#then get minimum between PTLO and PTLI  		
		PTL=$MAXTIME
		TAVAIL=$(($OTLIMIT-$SECONDS))
		PTLO=$(($TAVAIL/$PROBREMAINS))
		if [ $PTLI -gt $PTLO ]; then
		    PTL=$PTLO
		else
		    PTL=$PTLI
		fi
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
		PROBREMAINS=$(($PROBREMAINS-1))
	    fi
	    ;;

    esac
done < $BFILE
