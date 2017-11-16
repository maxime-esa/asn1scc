from SCons.Script import *

import glob
import itertools
import os
import json

from commons import *

def do_pair_test(decoder, encoder, test_case, report_file):
    encoded = int(call_bin([encoder, 'encode']))
    decoded = int(call_bin([decoder, 'decode']))
    result = Result(test_case,
                    os.path.basename(decoder),
                    os.path.basename(encoder),
                    decoded,
                    encoded)
    report_file.write(json.dumps(result._asdict()) + '\n')

def do_test_case(target, source, env):
    output = str(target[0])
    c_bin = str(source[0])
    ada_bin = str(source[1])
    test_case = os.path.basename(os.path.dirname(output))
    print("Running case {} ...".format(test_case))
    with open(output, 'w') as report:
        for pair in itertools.permutations([c_bin, ada_bin]):
            do_pair_test(*pair, test_case=test_case, report_file=report)

def builder():
    return Builder(action=do_test_case)
