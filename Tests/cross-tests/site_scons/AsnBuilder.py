from SCons.Script import *

import commons

def _asn_generator(target, source, env, for_signature):
    return ["mono '{}' -{} -ACN '{}' '{}' -o '{}'".format(
                env['ASN_BIN'],
                language,
                commons.get_files_with_suffix(source, '.acn')[0],
                commons.get_files_with_suffix(source, '.asn1')[0],
                os.path.dirname(str(target[0])))
            for language in env['LANGUAGES']]

def _append_output(target, source, env):
    c_basename, ada_basename = env['BASENAMES']
    dirname = env['DIRNAME']
    OUTPUT = ['real.c',
              'asn1crt.h',
              'acn.c',
              '{}.h'.format(c_basename),
              '{}.c'.format(c_basename),
              'asn1crt.c',
              'adaasn1rtl.ads',
              'adaasn1rtl.adb',
              '{}.adb'.format(ada_basename),
              '{}.ads'.format(ada_basename),
              'gnat.cfg',
              'IgnoredExaminerWarnings.wrn',
              'GPS_project.gpr',
              'runSpark.sh',
              'spark.idx']
    for file_ in OUTPUT:
        target.append(os.path.join(dirname, file_))
    return target, source

def builder():
    return Builder(generator=_asn_generator, emitter=_append_output)
