#!/bin/bash
docker run --rm -v $PWD:/tmp/mounted -w /tmp/mounted -u $(id -u):$(id -g) -e PATH="/opt/asn1scc:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin" asn1scc-runtime mono /opt/asn1scc/asn1.exe "$@"