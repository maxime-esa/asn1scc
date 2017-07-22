from SCons.Script import *

from xml.etree import ElementTree
from itertools import izip
from commons import glob_files_recursive, call_bin, get_files_with_suffix
from templates import *
import AsnBuilder

def _prepare_test_case(target, source, env, for_signature):
    iterator = iter(target)
    next(iterator)

    commands = []
    test_case = _get_test_case_name(target)
    for targets in izip(*[iterator] * 5):
        dir_name = os.path.dirname(targets[0].path)
        variable_name = targets[1].name[:-10]
        asn_header = AsnBuilder.get_c_basename(source[1:2]) + '.h'
        for target_file, template in izip(targets, templates):
            file_content = template.format(
                test_case=os.path.basename(dir_name),
                type_=env['VARIABLES'][dir_name],
                module=env['VARIABLES'][test_case]['MODULES'][0],
                variable=variable_name,
                buffer_=os.path.join(dir_name, "buffer_" + variable_name),
                asn_header=asn_header)
            commands.append('''@printf >'{}' $'{}' '''.format(target_file.path, file_content))
    return commands

def _parse_xml(target, source, env):
    _make_xml(target[0].path, get_files_with_suffix(source, '.asn1')[0], env['ASN_BIN'])
    root = ElementTree.parse(target[0].path).getroot()
    _parse_metadata(root, target, env)
    _parse_assignments(root, target, env)
    return target, source

def _make_xml(xml_name, asn_file, asn_bin):
    cmd = ["mono", asn_bin, '-ast', xml_name, asn_file]
    call_bin(cmd)

def _parse_metadata(root, target, env):
    test_case = _get_test_case_name(target)
    if test_case not in env['VARIABLES']:
        env['VARIABLES'][test_case] = {}

    test_case = _get_test_case_name(target)
    env['VARIABLES'][test_case]['TEST_FILE'] = root[0].get('FileName')
    env['VARIABLES'][test_case]['MODULES'] = [module.get('ID') for module in root[0].findall('Asn1Module')]

def _get_test_case_name(target):
    return os.path.basename(os.path.dirname(target[0].path))

def _parse_assignments(root, target, env):
    for assignment in root.iter('VariableAssignment'):
        if _validate_variable(assignment):
            _append_targets(assignment, target, env)

def _validate_variable(assignment):
    #TODO: we want only those assignments that have ONE reference type as Type in them
    return True

def _append_targets(assignment, target, env):
    target_directory = os.path.join(env['BUILD_DIR'], assignment.attrib['Name'])
    Mkdir(target_directory)
    target.append(File(os.path.join(target_directory, 'c_proxy.h')))
    target.append(File(os.path.join(target_directory, assignment.attrib['Name'] + '_c_proxy.c')))
    target.append(File(os.path.join(target_directory, 'ada_main_{}.adb'.format(assignment.attrib['Name']))))
    target.append(File(os.path.join(target_directory, assignment.attrib['Name'] + '_ada_proxy.ads')))
    target.append(File(os.path.join(target_directory, assignment.attrib['Name'] + '_ada_proxy.adb')))
    env['VARIABLES'][target_directory] = _get_type_name(assignment)

def _get_type_name(assignment):
    return assignment.iter('ReferenceType').next().attrib['ReferencedTypeName']

def builder():
    return Builder(generator=_prepare_test_case, emitter=_parse_xml)
