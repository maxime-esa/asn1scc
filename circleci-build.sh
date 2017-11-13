#!/bin/bash
xbuild /p:TargetFrameworkVersion="v4.5" || exit 1
cd v4Tests || exit 1
chmod +xscripts/runTests.py 
scripts/runTests.py -l c
