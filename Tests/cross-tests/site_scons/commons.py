import os
import re
import subprocess
import itertools

from SCons.Script import Glob
from SCons.Node.FS import Dir

def find_files_recursive(search_path, file_regex):
    regex = re.compile(file_regex)
    return [os.path.join(root, filename)
            for root, dirnames, filenames in os.walk(search_path)
            for filename in filenames
            if regex.match(filename)]

def glob_files_recursive(search_path, file_regex):
    out = []
    regex = re.compile(file_regex)
    for node in Glob(os.path.join(search_path, "*")):
        _handle_node(node, regex, out)
    return out

def _handle_node(node, regex, out):
    if type(node) is Dir:
        out += glob_files_recursive(str(node), regex)
    elif regex.match(str(node)):
        out.append(str(node))

def list_files(directory):
    return [os.path.join(directory, file_) for file_ in os.listdir(directory)]

def get_files_with_suffix(sources, suffix):
    return [str(source) for source in sources if os.path.splitext(str(source))[1] == suffix]

def call_bin(command):
    process = subprocess.Popen(command, 
        stdout=subprocess.PIPE, 
        stderr=subprocess.PIPE)
    stdout, stderr = process.communicate()
    if stderr or process.returncode != 0:
        class ChildProcessError(BaseException):
            pass
        raise ChildProcessError("Command failed: '" + stderr.strip() + "'")
    return stdout

def grouper(n, iterable, fillvalue=None):
  "grouper(3, 'ABCDEFG', 'x') --> ABC DEF Gxx"
  args = [iter(iterable)] * n
  return itertools.izip_longest(fillvalue=fillvalue, *args)
