#!/bin/bash
## script fot timeouted+ulimited running of biabductor

F=$1
if [ -b $2 ]; then
	TIMEOUT=300	## default
else
	TIMEOUT=$2
fi
TOOLDIR=~/bi-work/scripts
OPT="-m32 -DTEST -DDBLFREE"

##################################################################

if [ ! -f "$F" ]; then
	echo "Usage: $0 file.c [timeout,default=300]"
	exit 1
fi
FB=${F%%.c}

##################################################################
echo "=================================================================="
echo $F
echo "=================================================================="
echo

ulimit -v 10000000		## avoid thrashing

##################################################################
#$TOOLDIR/call_graph $F            # create DOTs (call graph, CFGs) from C
#echo "------------------------------------------------------------------"
#$TOOLDIR/json_dumper $OPT $F > $FB.json           # create JSON from C
#$TOOLDIR/generator < $FB.json | tee $FB.contracts # print contracts
#echo "------------------------------------------------------------------"
##################################################################

echo "### biabductor $OPT $F"  	>$FB.result
date				>>$FB.result
date
timeout $TIMEOUT $TOOLDIR/biabductor $OPT $F  2>&1 >>$FB.result    # main binary
if [ $? -eq 124 ]; then
	echo "=====TIMEOUT:$TIMEOUT====="	>>$FB.result
	date				>>$FB.result
	mv $FB.result $FB.result-timeout-$TIMEOUT
	echo
	echo "=====TIMEOUT:$TIMEOUT====="
else
	echo "=====OK:$?====="			>>$FB.result
	date				>>$FB.result
	echo "=====OK:$?====="
fi
echo
date
echo

##################################################################
