#!/bin/bash
xbuild || exit 1
cd Tests || exit 1
make || exit 1
