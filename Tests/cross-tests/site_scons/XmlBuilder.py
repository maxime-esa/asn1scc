from SCons.Script import *

import commons

def _xml_generator(target, source, env, for_signature):
    return ["mono '{}' -ast '{}' '{}'".format(
                env['ASN_BIN'],
                target[0].path,
                commons.get_files_with_suffix(source, '.asn1')[0])]

def builder():
    return Builder(generator=_xml_generator)
