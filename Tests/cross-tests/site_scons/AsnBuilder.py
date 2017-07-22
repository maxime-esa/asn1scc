from SCons.Script import *

import commons

def _asn_generator(target, source, env, for_signature):
    return ["mono '{}' -{} -ACN '{}' '{}' -o '{}'".format(
                env['ASN_BIN'],
                language,
                commons.get_files_with_suffix(source, '.acn')[0],
                commons.get_files_with_suffix(source, '.asn1')[0],
                os.path.join(os.path.dirname(os.path.dirname(str(target[0]))), language + '_out'))
            for language in env['LANGUAGES']]

def builder():
    return Builder(generator=_asn_generator)

def get_c_basename(test_files):
    return os.path.splitext(os.path.basename(test_files[0].path))[0]

def get_output(build_dir, test_files):
    c_basename = get_c_basename(test_files)
    OUTPUT = ['c_out/real.c',
              'c_out/asn1crt.h',
              'c_out/acn.c',
              'c_out/{}.h'.format(c_basename),
              'c_out/{}.c'.format(c_basename),
              'c_out/asn1crt.c',
              'Ada_out/adaasn1rtl.ads',
              'Ada_out/adaasn1rtl.adb',
              'Ada_out/kappa.adb',
              'Ada_out/kappa.ads']

    return [os.path.join(build_dir, out_file) for out_file in OUTPUT]
