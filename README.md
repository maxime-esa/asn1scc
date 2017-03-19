[![Build and Test Status of ASN1SCC on Circle CI](https://circleci.com/gh/ttsiodras/asn1scc.svg?&style=shield&circle-token=fcc32f415742887faa6ad69826b1cf25426df086)](https://circleci.com/gh/ttsiodras/asn1scc/tree/master)

Executive summary
=================

This is the source code of the ASN1SCC compiler - an ASN.1 compiler that
targets C and Ada, while placing specific emphasis on embedded systems.
You can read a comprehensive paper about it
[here (PDF)](http://web1.see.asso.fr/erts2012/Site/0P2RUC89/7C-4.pdf),
or a blog post with hands-on examples
[here](https://www.thanassis.space/asn1.html).
Suffice to say, if you are developing for embedded systems, it will probably
interest you.

Compilation
===========

## Common for all OSes

First, install the Java JRE. This is a compile-time only dependency,
required to execute ANTLR.

Then depending on your OS:

### Under Windows

Install:

1. A version of Visual Studio with support for F# .

2. Open `Asn1.sln` and build the `Asn1f2` project (right-click/build)

## Under OSX

1. Install the [Mono MDK](http://www.mono-project.com).

2. Execute ASN1SCC's `./build.sh` - and the compiler will be built.

## Under Linux

1. Install the [mono](http://www.mono-project.com) development tools. Under
   Debian Jessie for example (as of Sep/2014):

    ```
    $ mono -V
    Mono JIT compiler version 3.2.8 (Debian 3.2.8+dfsg-7)
    Copyright (C) 2002-2014 Novell, Inc, Xamarin Inc and Contributors.
            TLS:           __thread
            SIGSEGV:       altstack
            Notifications: epoll
            Architecture:  x86
            Disabled:      none
            Misc:          softdebug 
            LLVM:          supported, not enabled.
            GC:            sgen
    ```

2. Use the `fsharpc` compiler inside your distro, or just checkout and compile
   the Open Source F# compiler...

    ```
    git clone https://github.com/fsharp/fsharp && \
        cd fsharp && \
        ./configure && \
        make && sudo make install 
    ```

3. Execute

    xbuild

Depending on the version of Mono that you are using, you may need to specify
a specific target .NET framework version:

    xbuild /p:TargetFrameworkVersion="v4.5"

4. Run tests (if you want to):

    ```
    cd Tests
    make
    ```

Note that in order to run the tests you need both GCC and GNAT.
The tests will process hundreds of ASN.1 grammars, generate C and
Ada source code, compile it, run it, and check the coverage results.

Continuous integration
======================

Every time CircleCI detected a commit in ASN1SCC (any branch), it
checks the code, and tries to...

    (a) build it 
    (b) then run the tests.

But build it where? Inside what environment?

CircleCI offers only 3 build environments: OSX, Ubuntu 12 and Ubuntu 14.

Till recently (Mar/2017) Ubuntu 14 met all the dependencies we needed to build
and run the tests. But the work being done to enhance the Ada backend with the
new SPARK annotations needs the latest GNAT; which is simply not installeable
in Ubuntu 14 (even after adding the latest Ubuntu's source in the available
package sources).

But thankfully, CircleCI supports Docker images.

We have therefore setup the build, so that it creates (on the fly) a Debian
image using the latest version of Debian stable (the soon to be announced
Debian Stretch). Both the ASN1SCC build and the tests are then executed inside
the Docker image.

The amazing thing is, that after building the image for the first time, we can
cache it (see circle.yml for details) - which means that commits in ASN1SCC
re-use the pre-made Docker image - they don't re-install the build environment
every time.

In plain terms, we not only support the latest package versions that we need,
but also, the CircleCI checks of commits on ASN1SCC are very fast.

Usage
=====

The compiler has many features - it is documented in
[Chapter 10 of the TASTE manual](http://download.tuxfamily.org/taste/snapshots/doc/taste-documentation-current.pdf),
and you can see some simple usage examples in a related
[blog post](https://www.thanassis.space/asn1.html).

You can also read about
[how the compiler has been used in the TASTE project](http://www.semantix.gr/assert/)
to target safety-critical systems - and maybe also check out the
official [TASTE project site](http://taste.tuxfamily.org).

Credits
=======
George Mamais (gmamais@gmail.com), Thanassis Tsiodras (ttsiodras@gmail.com)
