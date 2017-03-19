FROM debian:stretch

RUN apt-get install mono-devel mono-complete fsharp mono-xbuild python3 \
    gnat-6 gcc g++ make
