#!/bin/bash
xbuild || exit 1
cd Tests || exit 1
pyenv global 3.4.4 || exit 1
make || {
    cp tmp/covlog.txt $CIRCLE_ARTIFACTS
    exit 1
}
