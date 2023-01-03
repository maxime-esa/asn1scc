#!/bin/bash
#docker build -t asn1scc .
docker run -ti --rm -v $(pwd):/app -v asn1scc_workdir:/workdir asn1scc bash -c "./local-build.sh $(git rev-parse --abbrev-ref HEAD)"
