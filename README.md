Executive summary
=================

This is the source code of the ASN1SCC compiler - an ASN.1 compiler that
targets C and Ada, while placing specific emphasis on embedded systems.
You can read a comprehensive paper about it
[here (PDF)](http://web1.see.asso.fr/erts2012/Site/0P2RUC89/7C-4.pdf),
or a blog post with hands-on examples
[here](http://users.softlab.ece.ntua.gr/~ttsiod/asn1.html).
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

3. Execute 'xbuild' in ASN1SCC directory

Usage
=====

The compiler has many features - it is documented in
[Chapter 10 of the TASTE manual](http://download.tuxfamily.org/taste/snapshots/doc/taste-documentation-current.pdf),
and you can see some simple usage examples in a related
[blog post](http://users.softlab.ece.ntua.gr/~ttsiod/asn1.html).

You can also read about
[how the compiler has been used in the TASTE project](http://www.semantix.gr/assert/)
to target safety-critical systems - and maybe also check out the
official [TASTE project site](http://taste.tuxfamily.org).

Credits
=======
George Mamais (gmamais@gmail.com), Thanassis Tsiodras (ttsiodras@gmail.com)


Changelog
=========

3.2.62
------
Minor bugfixes and improvements of the custom Stg backends
New rename policy option
New VDM backend

3.2.3
-----
Added error message for unsupported string and UTCTime types

3.2.2
-----
Various minor bugfixes
Improvements of ICD backend for ACN

3.2.0
-----
Minor API change in ICD backends - templates now contain code to customize the formatted output of the grammar.

3.1.4
-----
When adding fields to a SEQUENCE in an ACN model, the comments are now propagated to the ICD backends.

3.1.1/2/3
---------
Various minor bugfixes, in particular related to the handling of cyclic dependencies

3.1.0
-----
* Change in the API of the ICD backends: the comments are not only sent as a string but also as a list, allowing to extract the first line
* Added a Latex template for ICDs (in contrib) / Experimental

