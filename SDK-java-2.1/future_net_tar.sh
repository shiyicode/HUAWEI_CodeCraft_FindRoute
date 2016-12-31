#!/bin/bash

SCRIPT=$(readlink -f "$0")
BASEDIR=$(dirname "$SCRIPT")
cd $BASEDIR

if [ ! -d code ] || [ ! -f makelist.txt ]
then
    echo "ERROR: $BASEDIR is not a valid directory of SDK-gcc for future_net."
    echo "  Please run this script in a regular directory of SDK-gcc."
    exit -1
fi

rm -f future_net.tar.gz
tar -zcPf future_net.tar.gz code makelist.txt