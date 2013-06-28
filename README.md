Executive summary
=================

This is the source code of the ASN1SCC compiler - an ASN.1 compiler that targets C and Ada, while placing specific emphasis on embedded systems. You can read a comprehensive paper about it [here (PDF)](http://www.erts2012.org/site/0p2ruc89/7c-4.pdf), or a blog post with hands-on examples [here](http://users.softlab.ece.ntua.gr/~ttsiod/asn1.html). Suffice to say, if you are developing for embedded systems, it will probably interest you.

Compilation
===========

## Under Windows

If you are working under Windows, you need a version of Visual Studio with support for F# . Main development is done with Visual Studio 2012, but you can probably also use the older versions of the IDEs with the appropriate F# plugins (published by Microsoft).

Just open Asn1.sln and build the 'Asn1f2' project.

## Under Linux / OSX

1. Make sure you have installed MonoDevelop and xbuild. We have successfully built the compiler with versions of the tools from Debian Stable (as of 2013/06) - i.e. MonoDevelop 3.0.3.2 and xbuild 2.10.8.1.

2. Your MonoDevelop must learn about F# - so go to...

    Tools / Add-in Manager / Gallery / Language Bindinds / F# Language Binding 

...and click on 'Install'. This step will probably become unnecessary in later versions of MonoDevelop.

3. Checkout and compile the Open Source F# compiler...

    git clone https://github.com/fsharp/fsharp && cd fsharp && ./configure && make && sudo make install 

...or just use your distro's package manager to install it. Make sure you are installing F# 3.0 or later.

4. Execute ASN1SCC's ./build.sh - it will tell you what to do next.

This last step can be streamlined more - ideally, just requiring an invocation of xbuild. When we find time, we will replace the Windows-specific build rules with portable workarounds (in the various .vcproj/.fsproj files). For now, bear with us :-)

Usage
=====

The compiler has many features - it is documented in [Chapter 11 of the TASTE manual](http://download.tuxfamily.org/taste/snapshots/doc/taste-documentation-current.pdf), and you can see some simple usage examples in a related [blog post](http://users.softlab.ece.ntua.gr/~ttsiod/asn1.html).

You can also read about [how the compiler has been used in the TASTE project](http://www.semantix.gr/assert/) to target safety-critical systems - and maybe also check out the official [TASTE project site](http://taste.tuxfamily.org).

Credits
=======
George Mamais (gmamais@gmail.com), Thanassis Tsiodras (ttsiodras@gmail.com)
