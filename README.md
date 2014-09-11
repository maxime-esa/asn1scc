Executive summary
=================

This is the source code of the ASN1SCC compiler - an ASN.1 compiler that targets C and Ada, while placing specific emphasis on embedded systems. You can read a comprehensive paper about it [here (PDF)](http://www.erts2012.org/site/0p2ruc89/7c-4.pdf), or a blog post with hands-on examples [here](http://users.softlab.ece.ntua.gr/~ttsiod/asn1.html). Suffice to say, if you are developing for embedded systems, it will probably interest you.

Compilation
===========

## Under Windows

If you are working under Windows, you need a version of Visual Studio with support for F# .
Just open Asn1.sln and build the 'Asn1f2' project.

## Under Linux / OSX

1. Make sure you have installed the mono development tools. We have successfully built the compiler with versions of the tools from Debian Jessie (as of 2014/09):

    ```
    $ mono -V
    Mono JIT compiler version 3.2.8 (Debian 3.2.8+dfsg-7)
    Copyright (C) 2002-2014 Novell, Inc, Xamarin Inc and Contributors. www.mono-project.com
            TLS:           __thread
            SIGSEGV:       altstack
            Notifications: epoll
            Architecture:  x86
            Disabled:      none
            Misc:          softdebug 
            LLVM:          supported, not enabled.
            GC:            sgen
    ```

3. Use the `fsharpc` compiler inside your distro, or just checkout and compile the Open Source F# compiler...

    git clone https://github.com/fsharp/fsharp && cd fsharp && ./configure && make && sudo make install 

4. Execute ASN1SCC's ./build.sh - it will tell you what to do next.

Usage
=====

The compiler has many features - it is documented in [Chapter 11 of the TASTE manual](http://download.tuxfamily.org/taste/snapshots/doc/taste-documentation-20130619.pdf), and you can see some simple usage examples in a related [blog post](http://users.softlab.ece.ntua.gr/~ttsiod/asn1.html).

You can also read about [how the compiler has been used in the TASTE project](http://www.semantix.gr/assert/) to target safety-critical systems - and maybe also check out the official [TASTE project site](http://taste.tuxfamily.org).

Credits
=======
George Mamais (gmamais@gmail.com), Thanassis Tsiodras (ttsiodras@gmail.com)
