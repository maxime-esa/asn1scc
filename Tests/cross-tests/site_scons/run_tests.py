#!/bin/python3

import glob
import itertools
import os

from commons import find_files_recursive, call_bin
from Tee import Tee

class TestRunner:
    def __init__(self, env, c_bin, ada_bin, output):
        self.env = env
        self.c_bin = c_bin
        self.ada_bin = ada_bin
        self.output = output

    def do_pair_test(self, decoder, encoder, test_case):
        encoded = int(call_bin([encoder, 'encode']))
        decoded = int(call_bin([decoder, 'decode']))
        with open(self.output, 'w') as report:
            tee = Tee(report)
            if encoded != decoded:
               tee.write("Failure in {} (with decoder={}, encoder={}), decoded: {}, encoded: {}"
                        .format(test_case,
                            os.path.basename(decoder),
                            os.path.basename(encoder),
                            decoded,
                            encoded
                        ))
            else:
                tee.write("Test case {} (with decoder={}, encoder={}) passed"
                        .format(test_case,
                            os.path.basename(decoder),
                            os.path.basename(encoder)
                        ))

    def do_test_case(self, test_case):
        print("Running case {} ...".format(test_case))
        for pair in itertools.permutations([self.c_bin, self.ada_bin]):
            self.do_pair_test(*pair, test_case=test_case)

def test_main(target, source, env):
    runner = TestRunner(
        output=target[0].path,
        c_bin=source[0].path,
        ada_bin=source[1].path,
        env=env)
    test_case = os.path.basename(os.path.dirname(runner.output))
    runner.do_test_case(test_case)

if __name__ == '__main__':
    test_main()
