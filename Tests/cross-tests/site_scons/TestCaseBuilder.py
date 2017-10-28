from SCons.Script import *

from xml.etree import ElementTree
from itertools import izip
from commons import glob_files_recursive, call_bin, get_files_with_suffix
from templates import templates
import AsnBuilder

def _prepare_test_case(target, source, env):
    test_case = _get_test_case_name(source)
    for targets in izip(*[iter(target)] * len(templates)):
        asn_header = os.path.splitext(os.path.basename(source[1].path))[0] + '.h'
        dir_name = os.path.dirname(targets[0].path)
        for target_file, template in izip(targets, templates):
            file_content = template.format(
                test_case=os.path.basename(dir_name),
                type_=env['VARIABLES'][dir_name],
                module=env['VARIABLES'][test_case]['MODULES'][0],
                buffer_=os.path.join(dir_name, "buffer_" + test_case),
                asn_header=asn_header)
            with open(target_file.path, 'w') as output:
                output.write(file_content)

def _get_test_case_name(source):
    return os.path.basename(os.path.dirname(source[0].path))

def _ignore_first_target(target):
    iterator = iter(target)
    next(iterator)
    return iterator

def _parse_xml(target, source, env):
    try:
        _make_xml(target[0].path, get_files_with_suffix(source, '.asn1')[0], env['ASN_BIN'])
        root = ElementTree.parse(target[0].path).getroot()
        _parse_metadata(root, target, env)
        _parse_assignments(root, target, env)
        return target, source
    except:
        raise
    finally:
        _cleanup(target)

def _make_xml(xml_name, asn_file, asn_bin):
    cmd = ["mono", asn_bin, '-ast', xml_name, asn_file]
    call_bin(cmd)

def _parse_metadata(root, target, env):
    test_case = _get_test_case_name(target)

    if test_case not in env['VARIABLES']:
        env['VARIABLES'][test_case] = {}

    env['VARIABLES'][test_case]['MODULES'] = [module.get('ID') for module in root[0].findall('Asn1Module')]

def _parse_assignments(root, target, env):
    for assignment in root.iter('VariableAssignment'):
        if _has_exactly_one_reference(assignment):
            _append_targets(assignment, target, env)
        else:
            class MultipleReferenceTypeError(Exception):
                pass
            raise MultipleReferenceTypeError("{} has multiple references".format(assignment.attrib['Name']))

def _has_exactly_one_reference(assignment):
    return len([assignment.iter('ReferenceType')]) == 1

def _append_targets(assignment, target, env):
    target_directory = os.path.join(env['BUILD_DIR'], assignment.attrib['Name'])
    Mkdir(target_directory)
    name = assignment.attrib['Name']
    target.append(File(os.path.join(target_directory, 'c_proxy.h')))
    target.append(File(os.path.join(target_directory, name + '_c_proxy.c')))
    target.append(File(os.path.join(target_directory, ada_main_filename(name))))
    target.append(File(os.path.join(target_directory, name + '_ada_accessors.ads')))
    target.append(File(os.path.join(target_directory, name + '_ada_accessors.adb')))
    target.append(File(os.path.join(target_directory, name + '_ada_proxy.ads')))
    target.append(File(os.path.join(target_directory, name + '_ada_proxy.adb')))
    target.append(File(os.path.join(target_directory, name + '_ada_helpers.c')))
    env['VARIABLES'][target_directory] = _get_type_name(assignment)

def ada_main_filename(name):
    return 'ada_main_{}.adb'.format(name)

def _get_type_name(assignment):
    return assignment.iter('ReferenceType').next().attrib['ReferencedTypeName']

def _cleanup(target):
    xml = target.pop(0)
    cmd = ['rm', xml.path]
    call_bin(cmd)

def builder():
    return Builder(action=_prepare_test_case, emitter=_parse_xml)


