from SCons.Script import *

import os
import commons

def _ada_commands_generator(source, target, env, for_signature):
    main_source = os.path.splitext(source[0].path)[0]
    out_dir = os.path.dirname(os.path.dirname(main_source))
    ada_flags = ' '.join(['-I"' + os.path.join(out_dir, dir_) + '"' for dir_ in env['CPPPATH']])
    compile_cmd = (["gnatmake -c '{}' {} -i".format(
                      main_source,
                      ada_flags)]
                  + ["gnatbind '{}' {}".format(
                        main_source,
                        ada_flags)])

    link_cmd = "gnatlink '{}' '{}' -o '{}'".format(
        "' '".join([main_source + '.ali'] + commons.get_files_with_suffix(source, '.o')),
        os.path.join(out_dir, 'file_utility.o'),
        target[0].path)
    return compile_cmd + [link_cmd]

def builder():
    return Builder(generator = _ada_commands_generator, src_suffix = ['.adb', '.o'])
