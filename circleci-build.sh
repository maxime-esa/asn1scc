#!/bin/bash
nuget restore
xbuild /p:TargetFrameworkVersion="v4.5" || exit 1
cd Tests || exit 1
make || exit 1
