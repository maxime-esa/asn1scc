from SCons.Script import *

from run_tests import test_main

def builder():
    return Builder(action=test_main)
