#!/usr/bin/env python
# NFV packaging tool
# Authors: Madhavi Cherukuri 2017
#          Sanjay Sreenath  2018

# DEV WARNING: This file may be invoked by the end user from and external
# environment. Therefore, make sure not to put anything dependent on NFVIS
# environment in this file.

import os
import sys
import argparse
import re
import hashlib
import string

import logging
from pprint import pprint
try:
    import xmltodict
except ImportError:
    print('run pip install xmltodict')
import json
from itertools import islice
from collections import OrderedDict
import tempfile
import inspect
import subprocess
import collections
BLOCKSIZE = 65536
VERSION = '3.9.1'
FIRST_DISK_IMAGE = True
bootstrap_file_num = 1
disk_file_num = 0
ACCEPTED_IMG_EXTS = [".iso",".img",".qcow2",".vmdk"]
INTERNAL_ERROR = "InternalServerError"
VALIDATION_ERROR = "ValidationError"
PACKAGE_CONTENTS_TAG = "PackageContents"
FILE_INFO_TAG = "File_Info"
FILE_INFO_TYPE_TAG = "type"
BOOTSTRAP_FILE_TYPE_PREFIX = "bootstrap_file"
FILE_INFO_NAME_TAG = "name"
ASCII_CHARSET = "ascii"

logger = logging.getLogger(__name__)
image_prop_file = "image_properties.xml"
sys_gen_prop = "system_generated_properties.xml"
pkgmf_file = "package.mf"
bsfile_list=[]
bootstrap_sources = []
image_properties_template_contents = """<?xml version="1.0" encoding="UTF-8"?>
<image_properties>
    <vnf_type></vnf_type>
    <name></name>
    <version></version>
    <applicationVendor></applicationVendor>
    <imageType>virtualmachine</imageType>
    <bootup_time>600</bootup_time>
    <root_file_disk_bus>virtio</root_file_disk_bus>
    <root_image_disk_format>qcow2</root_image_disk_format>
    <vcpu_min>1</vcpu_min>
    <vcpu_max>8</vcpu_max>
    <memory_mb_min>256</memory_mb_min>
    <memory_mb_max>32768</memory_mb_max>
    <root_disk_gb_min>1</root_disk_gb_min>
    <root_disk_gb_max>256</root_disk_gb_max>
    <vnic_max>8</vnic_max>
    <monitoring_supported>true</monitoring_supported>
    <monitoring_methods>ICMPPing</monitoring_methods>
    <low_latency>true</low_latency>
    <sysinfo_support>false</sysinfo_support>
    <privileged_vm>false</privileged_vm>
    <console_type_serial>false</console_type_serial>
</image_properties>"""

error_messages = {
    "mnt_point":"Mount point is missing for ",
    "name":"Bootstrap file name(s) is missing",
    "ha_mode":"HA mode is missing for ",
    "package_filename":"Invalid package name",
    "vnf_version":"Invalid VNF version",
    "vnf_name":"Invalid VNF name",
    "vnf_type":"Invalid VNF type",
    "monitored":"Monitored property for VNF is missing",
    "app_vendor":"Invalid Application vendor",
    "bootstrap_cloud_init_drive_type":"Cloud init drive type can only be cdrom or disk",
    "bootstrap_cloud_init_bus_type":"Cloud init BUS type can only be ide or scsi or virtio",
    "size":"Max allowed volume size is 250 GiB",
    "deviceType":"Volume device type has to be disk or cdrom",
    "format":"Volume device format has to be raw or qcow2 or vmdk",
    "package_output_dir":"Package output directory doesn't exist",
    "image_list":"Invalid image path ",
    "ephemeral":"Invalid number of root/ephemeral disks. ",
    "more_root":"Too many root disks. ",
    "image_name":"Invalid image name extension",
    "parse":"Invalid parse type for ",
    "vnic_max":"Invalid vnic_max. Allowed range is 8-256",
    "mgmt_vnic":"Invalid vnic_max. Allowed range is 0-vnic_max",
    "mgmt_vnic_count":"Invalid mgmt_vnic_count. Allowed range is 0-2",
    "ha_vnic":"Invalid ha_vnic. Allowed range is 0-vnic_max",
    "ha_vnic_count":"Invalid ha_vnic_count. Allowed range is 0 to vnic_max-mgmt_vnic_count-2",
    "file_list":"Invalid number of bootstrap files for the chosen ha_enable value",
    "console_type_serial":"Invalid console_type_serial. Can only be true or false",
    "sriov":"Invalid sriov. Can only be true or false",
    "privilege":"Invalid privilege. Can only be true or false",
    "bootup_time":"Invalid bootup_time. Can only be between 600 and 3000"
}

def createPackageMF(outdir,version):
    global pkgmf_file
    pkgmf_file = os.path.join(outdir, pkgmf_file)
    pkg_mf_file  = open(pkgmf_file, "w")

    pkg_mf_file.write("<!-- sha256sum - for calculating checksum -->\n")

    pkg_mf_file.write("<PackageContents>\n")
    if version:
        pkg_mf_file.write('  <Packaging_Version>1.0</Packaging_Version>\n')

    return pkg_mf_file

def closePackageMF(pkg_mf_file):
    pkg_mf_file.write("</PackageContents> \n")
    pkg_mf_file.close()

def updatePackageMF(filename, file, opt, chksum,ha_package):
    global disk_file_num, bootstrap_file_num
    str1 = "  <File_Info> \n"
    filename.write(str1)
    str1 = "    <name>" + file + "</name>" + "\n"
    filename.write(str1)
    if opt == "disk_img_names":
      if disk_file_num == 0:
        str1 = "    <type>root_image</type>\n"
        disk_file_num = disk_file_num+1
      else:
        str1 = "    <type>ephemeral_disk%s_image</type>\n"%disk_file_num
        disk_file_num = disk_file_num+1
    elif opt == "image_properties":
        str1 = "    <type>image_properties</type>\n"
    elif opt == "system_generated_properties":
        str1 = "    <type>system_generated_properties</type>\n"
    elif opt == "bootstrap_file":
        if (ha_package):
            str1 = "    <type>bootstrap_file</type>\n"
        else:
            str1 = "    <type>bootstrap_file_%s</type>\n"%bootstrap_file_num
            bootstrap_file_num = bootstrap_file_num+1
    else:
       str1 = "    <type>unknown</type>\n"

    filename.write(str1)

    str1 = "    <sha256_checksum>" + chksum + "</sha256_checksum>\n"
    filename.write(str1)

    str1 = "  </File_Info>\n"
    filename.write(str1)

def sha1sum(filename):
    hasher = hashlib.sha1()
    with open(filename, 'rb') as afile:
        buf = afile.read(BLOCKSIZE)
        while len(buf) > 0:
            hasher.update(buf)
            buf = afile.read(BLOCKSIZE)
    return hasher.hexdigest()

def sha256sum(filename):
    hasher = hashlib.sha256()
    ascii_filename = filename.encode('ascii', 'ignore')
    with open(ascii_filename, 'rb') as afile:
        buf = afile.read(BLOCKSIZE)
        while len(buf) > 0:
            hasher.update(buf)
            buf = afile.read(BLOCKSIZE)
    return hasher.hexdigest()


def cleanup(opts):
    logger.info("Cleaning up the directory")
    if 'verbose' in opts and opts['verbose']:
        print("\ndeleting template and manifest files")
    if os.path.isfile(image_prop_file):
        os.remove(image_prop_file)
    if os.path.isfile(pkgmf_file):
        os.remove(pkgmf_file)
    if os.path.isfile(sys_gen_prop):
        os.remove(sys_gen_prop)
    #if 'newjson' not in opts:
    if opts['cleanup']:
        if 'verbose' in opts and opts['verbose']:
            print("deleting qcow2 and config files")
      #delete qcow2 and bstrap files
        '''
        for file in opts['root_disk_image']:
            if os.path.isfile(file):
                os.remove(file)
        '''
        for item in bsfile_list:
          file=item['src']
          if os.path.isfile(file):
            os.remove(file)
    if 'newjson' in opts:
        os.removedirs(opts['scratch_dir'])

def buildTargetFile(opts):
    extension = ".tar.gz"
    cur_dir = opts['scratch_dir']
    outname = opts['package_filename']
    opts['package_filename'] = os.path.join(opts['package_output_dir'],outname)
    pkg_mf_file = createPackageMF(opts['scratch_dir'],opts['ha_package'])
    file_dict = {'disk_img_names':opts['root_disk_image'], \
                'bootstrap_file':bootstrap_sources, \
                'image_properties':image_prop_file}
    ha_package = opts['ha_package']
    if ha_package:
        file_dict['system_generated_properties'] = sys_gen_prop
    tar_cmd = ["tar", "-czf"]

    if opts['package_filename'].endswith(".tar.gz"):
        tar_cmd.append(opts['package_filename'])
    else:
        tar_cmd.append(opts['package_filename'] + extension)
    for opt in file_dict.keys(): # loop through the keys in file_dict
        file = file_dict[opt]
        if type(file) == type([]):
            for item in file:
                chksum = sha256sum(item)
                if "/" in item: # checks if the item is a pathname (directory/filename)
                    (path, file) = item.rsplit("/",1)
                    path = "/" if path == "" else path
                    tar_cmd.extend(["-C", path, file])
                else:
                    tar_cmd.extend(["-C", cur_dir, item])
                    file = item
                updatePackageMF(pkg_mf_file, file, opt, chksum,opts['ha_package'])
        elif file != None:
            if os.path.isfile(file) == False:
                print("File %s doesn't exist, Please make sure file exists and rerun the tool."%file)
                cleanup(opts)
                sys.exit()
            else:
                chksum = sha256sum(file)
                if "/" in file: #checks if the file is a pathname (directory/filename)
                    (path, file) = file.rsplit("/",1)
                    path = "/" if path == "" else path
                    tar_cmd.extend(["-C", path, file])
                else:
                    tar_cmd.extend(["-C", cur_dir, file])
                updatePackageMF(pkg_mf_file, file, opt, chksum,opts['ha_package'])

    closePackageMF(pkg_mf_file)
    if "/" in pkgmf_file:
        (path, file) = pkgmf_file.rsplit("/",1)
        path = "/" if path == "" else path
        tar_cmd.extend(["-C", path, file])
    else:
        tar_cmd.extend(["-C", cur_dir, pkgmf_file])

    print(tar_cmd)
    try:
        subprocess.call(tar_cmd) # run the command
    except OSError:
        pass
    cleanup(opts)

def extract_path(pkg_name=''):
    '''
        extract_path : if the full path not specified it will take the current directory
                       as both the src directory.
                       logic here is if no '/' present means the current directory.
                       else extract the directory and filename.
    '''
    path=pkg_name
    if '/' not in pkg_name:
        curr_dir = os.getcwd()
        if os.path.isfile(curr_dir+'/'+pkg_name):
            path = curr_dir
        else:
            print('File %s not present, enter the correct path'%pkg_name)
            sys.exit()
    else:
        if os.path.isfile(pkg_name):
            path = os.path.dirname(pkg_name)
            pkg_name = os.path.basename(pkg_name)
        else:
            print('Path %s specified is not correct or file doesn''t exist'%pkg_name)
            sys.exit()
    return path, pkg_name

def convertTargetFile(opts,pkg_name=''):
    """
        convertTargetFile: Take the options provided by the users
                        package name , src path, destination path.
        Output: convert the package in to the vmanage supported package
                at the destination path.
                - This function call the 
                'convert_image_properties' to change the image_propeties
                which are supported by vmanage.
                - Change the package.mf file as well re-calculate the 
                 sha256 checksum for each of the files present in the 
                 current package and update the package.mf file.
    """
    
    opts['src_dir'], pkg_name = extract_path(pkg_name)
    # if destination dir is not given generate the package at src directory.
    if 'dest_dir' not in opts:
        opts['dest_dir'] = opts['src_dir']

    dest_path = opts['dest_dir']
    if not os.path.isdir(dest_path):
        print('The destination path defined does not exist, please enter the correct path')
        return
    print('Conversion started ##############')
    try:
        #Call the function to change the image properties 
        # after untar of the package.

        # check if the /tmp exist on the system or not
        if os.path.isdir("/tmp"):
            temp_dir = tempfile.mkdtemp(dir="/tmp/")
        else:
            temp_dir = tempfile.mkdtemp(dir=os.getcwd())
        print(temp_dir)
        # use temp_dir, and when done:
        src_path = temp_dir
        convert_image_properties(opts['src_dir'], pkg_name, src_path)

        #Calculate the new sha256 cheksum of the change files and 
        #update the package.mf file.
        pkg_dict={}

        with open(os.path.join(src_path,'package.mf'),"r") as fd:
            pkg_dict = xmltodict.parse(fd.read())
        tar_cmd = ["tar", "-czf", dest_path+'/'+'vmanage_'+pkg_name]
        for pkg in pkg_dict['PackageContents']['File_Info']:
            if 'sha1_checksum' in pkg:
                del pkg['sha1_checksum']
            filename = pkg['name']
            full_path = os.path.join(src_path, filename)
            if os.path.isfile(full_path) == False:
                print("File %s doesn't exist, Please make sure file in tar.gz and package.mf have same name."%full_path)
                subprocess.call(["rm", "-rf", str(temp_dir)])
                cleanup(opts)
                sys.exit()
            else:
                chksum = sha256sum(full_path)
                pkg['sha256_checksum'] = chksum
                tar_cmd.extend(["-C", src_path, filename])

        #Addition of the keys in the package.mf file
        pkg_dict['PackageContents']['Packaging_Version'] = 1.0
        pkg_dict['PackageContents'] = collections.OrderedDict(reversed(list(pkg_dict['PackageContents'].items()))) 
        pkg_val=(xmltodict.unparse(pkg_dict, pretty=True, full_document=False))

        with open(os.path.join(src_path, pkgmf_file), "w+") as f:
            f.write("<!-- sha256sum - for calculating checksum -->\n")
        with open(os.path.join(src_path, pkgmf_file), "a") as f:
            f.write(pkg_val)
        tar_cmd.extend(["-C", src_path, pkgmf_file])
        print(tar_cmd)
        subprocess.call(tar_cmd) # run the command
        subprocess.call(["rm", "-rf", str(temp_dir)])
    except OSError:
        logger.info('OSError occured while converting the package.')
        subprocess.call(["rm", "-rf", str(temp_dir)])
        pass
    except Exception as e:
        print 'Exception occured %s'%e
        logger.info('Exception occured while converting the package.')
        subprocess.call(["rm", "-rf", str(temp_dir)])
        pass
    cleanup(opts)

def convert_image_properties(pkg_dir , filename, src):
    '''
    This function performs the following conversion or addition:

    - Untar the old package and parse the custom variable from the old format
    <custom_property>
        <UUID></UUID>
    </custom_property>

    to the vmanage supported format

    <custom_property>
        <type>string</type>
        <name display='UUID'>UUID</name>
        <val></val>
    </custom_property>

    - Altering the version in the package to repalce '_' with '-'
    - Removing the profile section from the package.
    - Adding 'imageType' as 'virtualMachine'.
    '''
    try:
        tar_cmd = ['tar', '-xzf', pkg_dir+ '/' + filename, '-C', src]
        subprocess.call(tar_cmd) # run the command
        # Untar the file given
        with open(os.path.join(src,'image_properties.xml'),"r") as fd:
            template_dict = xmltodict.parse(fd.read())

        IMAGE_TYPE='imageType'
        #PACKAGE_NAME='package_filename'
        template_dict['image_properties'][IMAGE_TYPE] = 'virtualmachine'
        custom_list = []
        if 'custom_property' in template_dict['image_properties'].keys():
            custom_list = (template_dict['image_properties']['custom_property'])

        # change the version tag in image propeties '_' to '-'
        # need to add more cases if vmanage doesn't support other format.
        if 'version' in template_dict['image_properties'].keys():
            template_dict['image_properties']['version'] = template_dict['image_properties']['version'].replace('_', '-')    
    
        # removing the profile section for now, remove this code when the esc-lite
        # changes comes in for the profile.
        if 'profiles' in template_dict['image_properties'].keys():
            del template_dict['image_properties']['profiles']
        
        if 'default_profile' in template_dict['image_properties'].keys():
            del template_dict['image_properties']['default_profile']

        # this is the list of attributes that are needed to be added to a property element.
        # we can always add more values in the future.

        attr_list = ['display']
        DISPLAY=0
        for custom in custom_list:
            key_list = custom.keys()
            value_list = custom.values()
            custom.popitem()
            custom['name'] = {}
            custom['name']['@'+attr_list[DISPLAY]] = key_list[0]
            custom['name']['#text'] = key_list[0]

            # If the type of the values list is a list
            # then the type of the property is 'selection'
            # and the format for val is slightly different.
            # else the type is 'string' for all properties

            if type(value_list[0]) == list:
                custom['type'] = 'selection'
                val_list=[]
                for v in value_list[0]:
                    val={}
                    val['@'+attr_list[DISPLAY]]= v
                    val['#text'] = v
                    val_list.append(val)
                custom['val'] = val_list
            else:
                custom['type'] = 'string'
                custom['val'] = value_list[0]
        val=(xmltodict.unparse(template_dict, pretty=True))
        with open(os.path.join(src,'image_properties.xml'), "w") as f:
            f.write(val)
    except OSError:
        logger.info("Error in creating/accessing the tmp directory")
        subprocess.call(["rm", "-rf", str(src)])
        sys.exit()

def get_image_extension(image_name):
    for ext in ACCEPTED_IMG_EXTS:
        if image_name.endswith(ext):
            if ext != ".qcow2":
                print("\nCurrently NFVIS does not support registration"
                      " of packaged images that are not in .qcow2 format\n")
            return ext[1:]
    print("\nUnsupported image format '." + str(image_name.rsplit(".")[1]) +"'")
    print("Supported image format - " + str(ACCEPTED_IMG_EXTS) + "\n")
    sys.exit()

def handle_root_disk_images(opts,t_dict):
    for (pos,image) in list(islice(enumerate(opts['root_disk_image']),1,None)):
        elem = "disk_%s_file_disk_bus"%pos
        t_dict[elem]= "virtio"
        elem = "disk_%s_image_format"%pos
        t_dict[elem]=get_image_extension(image)

def add_custom_legacy(opts,t_dict):
    c_opts = []
    for opt in opts['custom']:
        val_list=[]
        for key_val in opt:
            key,val=key_val.split(':')
            if key.startswith('val'):
                val_list.append(val)
            else:
                xmlkey = val
        c_opts.append({xmlkey:val_list})
    t_dict['image_properties']['custom_property'] = c_opts

def add_custom(opts,t_dict):
    custom_property = []
    for opt in opts['custom']:
        option_dict = {}
        vals=[]
        key_dict={}
        valattr_list=[]
        values={}
        for key_val in opt:
            splits = key_val.split(':',1)
            val1,val2 = splits[0],splits[1]
            if val1.startswith('propattr_'):
                val1 = '@'+val1[len('propattr_'):]
                option_dict[val1]=val2
            elif val1.startswith('keyattr_'):
                val1 = '@'+val1[len('keyattr_'):]
                key_dict[val1] = val2
            elif val1 == 'key':
                key_dict['#text']=val2
            elif val1 == 'type':
                option_dict[val1]=val2
            elif val1.startswith('val'):
                if 'attr' in val1:
                    valattr_list.append({val1:val2})
                else:
                    values[val1]=val2
        if len(valattr_list) > 0:
            for valattr_dict in valattr_list:
                val_dict={}
                for attrname,val in valattr_dict.items():
                    attrkey=attrname[0:attrname.find('attr')]
                    attrname = attrname[attrname.find('attr_')+5:]
                    val_dict['@'+attrname]=val
                    val_dict['#text'] = values.pop(attrkey,'-')
                    vals.append(val_dict)
        for key in values:
            val_dict={}
            val_dict['#text'] = values[key]
            vals.append(val_dict)
        option_dict['val'] = vals
        option_dict['name'] = key_dict
        custom_property.append(option_dict)
    t_dict['image_properties']['custom_property']=custom_property


def add_custom_special(opts,t_dict):
    enable_ha = {
        '@special':'true',
        'name':{'#text':'ha','@display':'Enable HA'},
        'type':'selection','default':'true',
        'val': [
            {'#text':'true','@display':'true'},
            {'#text':'false','@display':'false'}
        ],
    }
    termination = {
        '@special':'true',
        'name':{'#text':'terminationMode','@display':'Termination'},
        'type':'selection','default':'routed',
        'val': [
            {'#text': 'vlan', '@display': 'VNF-Tagged',
                '@help': 'L3 Mode With Sub-interfaces(Trunked)'},
            {'#text': 'vpn', '@display': 'Tunneled',
                '@help': 'L3 Mode With IPSEC Termination From Consumer and Routed to Provider GW'},
            {'#text': 'routed', '@display': 'Hypervisor-Tagged',
                '@help': 'L3 Mode In Access Mode (Non-Trunked)'}
        ]
    }
    firewall_mode = {
        '@special':'true',
        'name':{'#text':'firewallMode','@display':'Firewall Mode'},
        'type':'selection','default':'transparent',
        'val': [
            {'#text':'transparent','@display':'Transparent'},
            {'#text':'routed','@display':'Routed'}
        ]
    }
    if 'ha_capable' in opts and opts['ha_capable']:
        if 'custom_property' in t_dict['image_properties']:
            t_dict['image_properties']['custom_property'].append(enable_ha)
    if 'multi_use' in opts and opts['multi_use']:
        t_dict['image_properties']['custom_property'].append(termination)
    if 'vnf_type' in opts and opts['vnf_type'] == 'FIREWALL':
        if 'custom_property' in t_dict['image_properties']:
            t_dict['image_properties']['custom_property'].append(firewall_mode)


def initialize_logger(opts):
    logger.setLevel(logging.DEBUG)
    log_dir = opts['log_dir']
    logger_handler = logging.FileHandler(log_dir)
    logger_handler.setLevel(logging.DEBUG)
    logger_formatter = logging.Formatter('%(asctime)s %(levelname)s - %(message)s',datefmt='%Y-%m-%d %H:%M:%S')
    logger_handler.setFormatter(logger_formatter)
    logger.addHandler(logger_handler)

def error_handler(message,opts,code,etype,vname):
    error = '{"errorCode":"'+ str(code) + '", "errorType":"' +  etype + '", "errorMessage":"'+message+'", "key":"'+vname +'"}'
    if len(opts) > 0:
        cleanup(opts)
    sys.exit(error)

def unparse_resource_properties(opts, resource_properties):
    for rp in resource_properties:
        if rp == 'min_mem':
            opts['memory_mb_min'] = resource_properties[rp]
        elif rp == 'max_mem':
            opts['memory_mb_max'] = resource_properties[rp]
        elif rp == 'min_vcpu':
            opts['vcpu_min'] = resource_properties[rp]
        elif rp == 'max_vcpu':
            opts['vcpu_max'] = resource_properties[rp]
        elif rp == 'min_disk':
            opts['root_disk_gb_min']  = resource_properties[rp]
        elif rp == 'max_disk':
            opts['root_disk_gb_max'] = resource_properties[rp]
        else:
            opts[rp] = resource_properties[rp]

def handle_mounts_and_custom_vars(opts, t_dict, bs_file_list):
    sysgen_list = []
    ui_list = []
    bs_list = []
    inside = re.compile("INSIDE_VLAN")
    outside = re.compile("OUTSIDE_VLAN")
    for bsfile in bs_file_list:
        bs_dict = {}
        if not 'name' in bsfile:
            logger.error(error_messages['name'])
            error_handler(error_messages['name'],opts,lineno(),VALIDATION_ERROR,'name')
        if not 'mnt_point' in bsfile:
            logger.error(error_messages['mnt_point'])   #mnt point specific to a file
            error_handler(error_messages['mnt_point']+bsfile['name'],opts,lineno(),VALIDATION_ERROR,'mnt_point')
        if not 'parse' in bsfile:
            logger.error(error_messages['parse'])
            error_handler(error_messages['parse']+bsfile['name'],opts,lineno(),VALIDATION_ERROR,'parse')
        if not 'ha_mode' in bsfile:
            logger.error(error_messages['ha_mode'])
            error_handler(error_messages['ha_mode']+bsfile['name'],opts,lineno(),VALIDATION_ERROR,'ha_mode')
        bs_dict['@mnt_pnt'] = bsfile['mnt_point'] + bsfile['name'] if bsfile['mnt_point'] == '/' else bsfile['mnt_point']
        bs_dict['@parse'] = str(bsfile['parse']).lower()
        bs_dict['#text'] = bsfile['name']
        fullfilename = os.path.join(bsfile['path'], bsfile['name'])
        if not os.path.exists(fullfilename):
            logger.error("Bootstrap file %s doesn't exit"%(fullfilename))
            error_handler("Bootstrap file not found",opts,lineno(),INTERNAL_ERROR,bsfile['name'])
        bootstrap_sources.append(fullfilename)
        if bsfile['ha_mode'] == 'primary':
            bs_dict['@vm'] = '1'
        elif bsfile['ha_mode'] == 'secondary':
            bs_dict['@vm'] = '2'
        elif bsfile['ha_mode'] == 'standalone':
            bs_dict['@vm'] = '0'
        bs_list.append(bs_dict)

        if 'userInput' in bsfile:
            for each_var in bsfile['userInput']:
                custom_var_dict = OrderedDict()
                '''
                    Again no need to iterate
                '''

                if 'display_str' in each_var:
                    custom_var_dict['name'] = {
                        '@display':each_var['display_str'], '#text':each_var['name']
                    }
                else:
                    custom_var_dict['name'] = each_var['name']
                if 'type' in each_var:
                    custom_var_dict['type'] = each_var['type']
                if 'mandatory' in each_var:
                    custom_var_dict['@mandatory'] = each_var['mandatory']
                if 'value' in each_var:
                    custom_var_dict['val'] = each_var['value']
                else:
                    custom_var_dict['val'] = ''

                '''
                key of 'attributes' could have pointed to a dictionary simply
                instead it points to an array of dicts of type and vals
                '''
                if 'attributes' in each_var:
                    for attrib_dict in each_var['attributes']:
                        custom_var_dict['@'+attrib_dict['type']] = attrib_dict['value']
                ui_list.append(custom_var_dict)

        if 'sysGen' in bsfile:
            inside_count = 0
            outside_count = 0
            for each_var in bsfile['sysGen']:
                sysgen_var_dict = {}
                '''
                    Skip iteration
                '''
                sysgen_var_dict['name'] = each_var['name']
                if not inside.search(each_var['name']) is None:
                    inside_count += 1
                if not outside.search(each_var['name']) is None:
                    outside_count += 1
                if type in each_var:
                    sysgen_var_dict['type'] = each_var['type']
                sysgen_var_dict['val'] = ''
                '''
                for attrib_dict in each_var['attributes']:
                    sysgen_var_dict['@'+attrib_dict['type']] = attrib_dict['value']
                '''
                sysgen_list.append(sysgen_var_dict)
            if inside_count:
                t_dict['image_properties']['number_input_vlans'] = inside_count
            if outside_count:
                t_dict['image_properties']['number_output_vlans'] = outside_count

    t_dict['image_properties']['bootstrap_file'] = bs_list
    custom_set = set([json.dumps(c) for c in ui_list])
    custom_list = [json.loads(cs) for cs in custom_set]
    t_dict['image_properties']['custom_property'] = custom_list
    sysgen_set = set([json.dumps(c) for c in sysgen_list])
    sysgen_list = [json.loads(ss,object_pairs_hook=OrderedDict) for ss in sysgen_set]
    return sysgen_list

def validate_packagename(json_fields,opts):
    version = json_fields['vnf_version']
    valid_version = (version[0] != '.' and version[len(version)-1] != '.' and bool(re.match('^[0-9.]+$',version)))
    if not valid_version:
        logger.info(error_messages['vnf_version'])
        error_handler(error_messages['vnf_version'],opts,lineno(),VALIDATION_ERROR,'vnf_version')
    final_package_name_entities = {'package_filename','vnf_name','vnf_type','vnf_version'}
    for fpne in final_package_name_entities:
        if not bool(re.match('^[a-zA-Z0-9.-]+$',json_fields[fpne])):
            logger.error(error_messages[fpne])
            error_handler(error_messages[fpne],opts,lineno(),VALIDATION_ERROR,fpne)

def validate_resourceproperties(json_fields,opts):
    if 'resource_properties' in json_fields:
        if 'vnic_max' in json_fields['resource_properties'] and not(8<=json_fields['resource_properties']['vnic_max']<=256):
            logger.error("Max number of VNICs can only be between 8-256")
            error_handler(error_messages['vnic_max'],opts,lineno(),VALIDATION_ERROR,'vnic_max')
        if 'mgmt_vnic' in json_fields['resource_properties'] or 'ha_vnic' in json_fields['resource_properties']:
            if not(0<=json_fields['resource_properties']['mgmt_vnic']<=json_fields['resource_properties']['vnic_max']):
                logger.error("Range of Management vnic id is 0 to max number of VNICs")
                error_handler(error_messages['mgmt_vnic'],opts,lineno(),VALIDATION_ERROR,'mgmt_vnic')
        if 'mgmt_vnic_count' in json_fields['resource_properties'] and not(0<=json_fields['resource_properties']['mgmt_vnic_count']<=2):
            logger.error("Management vnic id count can only be between 0 and 2")
            error_handler(error_messages['mgmt_vnic_count'],opts,lineno(),VALIDATION_ERROR,'mgmt_vnic_count')
        if 'ha_vnic_count' in json_fields['resource_properties'] and 'mgmt_vnic_count' in json_fields['resource_properties'] and \
            'vnic_max' in json_fields['resource_properties']:
            max_ha_vnic_count  = json_fields['resource_properties']['vnic_max']-json_fields['resource_properties']['mgmt_vnic_count']-2
            if not(0<=json_fields['resource_properties']['ha_vnic_count']<=max_ha_vnic_count):
                logger.error("Invalid ha_vnic_count")
                error_handler(error_messages['ha_vnic_count'],opts,lineno(),VALIDATION_ERROR,'ha_vnic_count')




def validate_imageproperties(json_fields,opts):
    if 'image_properties' in json_fields:
        img_properties = {'sriov','monitored','console_type_serial','privilege'}
        for img_prop in img_properties:
            if img_prop in json_fields['image_properties'] and json_fields['image_properties'][img_prop] != True \
                and json_fields['image_properties'][img_prop] != False:
                logger.error("Invalid " +img_prop+" type. Can only be true or false")
                error_handler(error_messages[img_prop],opts,lineno(),VALIDATION_ERROR,img_prop)
        if 'bootup_time' in json_fields['image_properties'] and not (600 <= json_fields['image_properties']['bootup_time'] <= 3000):
            logger.error("Boot up time has to be between 600 and 3000")
            error_handler(error_messages['bootup_time'],opts,lineno(),VALIDATION_ERROR,'bootup_time')

def lineno():
    return inspect.currentframe().f_back.f_lineno

def validate_json(json_fields,opts):
    if not 'vnf_type' in json_fields:
        logger.error(error_messages['vnf_type'])
        error_handler(error_messages['vnf_type'],opts,lineno(),VALIDATION_ERROR,'vnf_type')
    if not 'package_filename' in json_fields:
        logger.error(error_messages['vnf_version'])
        error_handler("Package_filename is missing",opts,lineno(),VALIDATION_ERROR,'package_filename')
    if not 'vnf_version' in json_fields:
        logger.error("Vnf_version is missing in the json file")
        error_handler(error_messages['vnf_version'],opts,lineno(),VALIDATION_ERROR,'vnf_version')
    if not 'monitored' in json_fields['image_properties']:
        logger.error(error_messages['monitored'])
        error_handler(error_messages['monitored'],opts,lineno(),VALIDATION_ERROR,'monitored')
    if not 'vnf_name' in json_fields:
        logger.error(error_messages['vnf_name'])
        error_handler(error_messages['vnf_name'],opts,lineno(),VALIDATION_ERROR,'vnf_name')
    if not 'app_vendor' in json_fields:
        logger.error(error_messages['app_vendor'])
        error_handler(error_messages['app_vendor'],opts,lineno(),VALIDATION_ERROR,'app_vendor')
    for image in json_fields['image_list']:
        if len(image['image_name']) > 5 and image['image_name'][len(image['image_name'])-6:] != '.qcow2':
            logger.error("Invalid image extension")
            error_handler(error_messages['image_name'],opts,lineno(),VALIDATION_ERROR,'image_name')
    if 'bootstrap' in json_fields and 'file_list' in json_fields['bootstrap']:
        if 'ha_capable' in json_fields['resource_properties']:
            if json_fields['resource_properties']['ha_capable'] and len(json_fields['bootstrap']['file_list']) < 2:
                logger.error("At least two bootstrap files needed for HA packaging")
                error_handler(error_messages['file_list'],opts,lineno(),VALIDATION_ERROR,'file_list')
            if not json_fields['resource_properties']['ha_capable'] and len(json_fields['bootstrap']['file_list']) < 1:
                logger.error("At least one bootstrap file is needed for standalone packaging")
                error_handler(error_messages['file_list'],opts,lineno(),VALIDATION_ERROR,'file_list')
        for bfile in json_fields['bootstrap']['file_list']:
            if 'parse' in bfile and bfile['parse'] != True and bfile['parse'] != False:
                logger.error("Invalid parse type.Can only be true or false")
                error_handler(error_messages['parse']+bfile['name'],opts,lineno(),VALIDATION_ERROR,'parse')
    allowed_vnf_types = set(['FIREWALL','ROUTER','LOADBALANCER','OTHER', 'vWAAS', 'vWLC', 'WLC'])
    if json_fields['vnf_type'] not in allowed_vnf_types:
        logger.error(error_messages['vnf_type'])
        error_handler(error_messages['vnf_type'],opts,lineno(),VALIDATION_ERROR,'vnf_type')
    #validate package name
    validate_packagename(json_fields,opts)
    validate_imageproperties(json_fields,opts)
    validate_resourceproperties(json_fields,opts)
    if 'bootstrap' in json_fields:
        if 'bootstrap_cloud_init_drive_type' in json_fields['bootstrap']:
            bootstrap = json_fields['bootstrap']
            if bootstrap['bootstrap_cloud_init_drive_type'] != 'cdrom' and bootstrap['bootstrap_cloud_init_drive_type'] != 'disk':
               logger.error(error_messages['bootstrap_cloud_init_drive_type'])
               error_handler(error_messages['bootstrap_cloud_init_drive_type'],\
                   opts,lineno(),VALIDATION_ERROR,'bootstrap_cloud_init_drive_type')
        if 'bootstrap_cloud_init_bus_type' in json_fields['bootstrap']:
            bootstrap = json_fields['bootstrap']
            bus_types = set(['virtio','scsi','ide'])
            if bootstrap['bootstrap_cloud_init_bus_type'] not in bus_types:
                logger.error(error_messages['bootstrap_cloud_init_bus_type'])
                error_handler(error_messages['bootstrap_cloud_init_bus_type'], \
                    opts,lineno(),VALIDATION_ERROR,'bootstrap_cloud_init_bus_type')
    if 'volumes' in json_fields:
        for volume in json_fields['volumes']:
            if 'size' in volume and 'sizeunit' in volume:
                size = int(volume['size'])
                unit = volume['sizeunit']
                limit = 256
                if unit == 'MiB':
                    if size/1000 > limit:
                        logger.error(error_messages['size'])
                        error_handler(error_messages['size'],opts,lineno(),VALIDATION_ERROR,'size')
                elif unit == 'GiB':
                    if size > limit:
                        logger.error(error_messages['size'])
                        error_handler(error_messages['size'],opts,lineno(),VALIDATION_ERROR,'size')
                elif unit == 'TiB':
                    if size*1000 > limit:
                       logger.error(error_messages['size'])
                       error_handler(error_messages['size'],opts,lineno(),VALIDATION_ERROR,'size')
            if 'deviceType' in volume:
                if volume['deviceType'] != 'disk' and volume['deviceType'] != 'cdrom':
                    logger.error(error_messages['deviceType'])
                    error_handler(error_messages['deviceType'],opts,lineno(),VALIDATION_ERROR,'deviceType')
            if 'format' in volume:
                if volume['format'] != 'qcow2' and volume['format'] != 'raw' and volume['format'] != 'vmdk':
                    logger.error(error_messages['format'])
                    error_handler(error_messages['format'],opts,lineno(),VALIDATION_ERROR,'format')

def build_from_json(t_dict, jsonfile):
    logger.info('Checking if Json file %s exists or not...'%(jsonfile))
    if os.path.exists(jsonfile):
        logger.info("Reading the json file")
        with open(jsonfile,'r') as f:
            obj = json.load(f)
        opts = {}
        # validate the json file
        logger.info(obj)
        logger.info("->>>>>>>>>>>>>>>>>>>=====<<<<<<<<<<<<<<<<-")
        logger.info(opts)
        validate_json(obj,opts)
        sysgen_list = []
        opts['ha_package'] = True
        opts['no_compress'] = False
        opts['verbose'] = False
        opts['cleanup'] = True
        opts['newjson'] = jsonfile
        for json_element in obj:
            if json_element == 'vnf_name':
                opts['name'] = obj[json_element]
            elif json_element == 'image_list':
                opts['root_disk_image'] = []
                one_root = False
                for images in obj[json_element]:
                    image_path = os.path.join(images['path'],images['image_name'])
                    if not os.path.exists(image_path):
                        logger.error(error_messages['image_list'])
                        error_handler(error_messages['image_list']+image_path,opts,lineno(),INTERNAL_ERROR,'image_list')
                    normalize = images['disk'].lower()
                    if "root" in normalize:
                        if one_root:
                            logger.error(error_messages['more_root'])
                            error_handler(error_messages['more_root']+image_path, opts,lineno(),VALIDATION_ERROR,'image_list')
                        opts['root_disk_image'].insert(0,image_path)
                        one_root=True
                    else:
                        n = normalize[-1]
                        if n.isdigit():
                            ix = int(n)
                        else:
                            logger.error(error_messages['ephemeral'])
                            error_handler(error_messages['ephemeral']+image_path, opts,lineno(),VALIDATION_ERROR,'image_list')
                        opts['root_disk_image'].insert(ix, image_path)
            elif json_element == 'image_properties':
                for im_prop in obj[json_element]:
                    if im_prop == 'privilege':
                        opts['privileged_vm'] = str(obj[json_element][im_prop]).lower()
                    elif im_prop == 'sriov':
                        opts['sriov_supported'] = str(obj[json_element][im_prop]).lower()
                    elif im_prop == 'console_type_serial':
                        opts['console_type_serial'] = str(obj[json_element][im_prop]).lower()
                    elif im_prop == 'monitored':
                        opts['monitored'] = str(obj[json_element][im_prop]).lower()
                    elif im_prop == 'dedicate_cores':
                        opts['dedicate_cores'] = str(obj[json_element][im_prop]).lower()
                    elif im_prop == 'boot_time':
                        opts['bootup_time'] = obj[json_element][im_prop]
                    else:
                        opts[im_prop] = obj[json_element][im_prop]
            elif json_element == 'resource_properties':
                unparse_resource_properties(opts,obj['resource_properties'])
            elif json_element == 'package_output_dir':
                if not os.path.exists(obj[json_element]) :
                    logger.error(error_messages['package_output_dir'])
                    error_handler(error_messages['package_output_dir'],opts,lineno(),INTERNAL_ERROR,'package_output_dir')
                scratch_dir = tempfile.mkdtemp(dir=obj['package_output_dir'])
                opts['scratch_dir'] = scratch_dir
                opts[json_element] = obj[json_element]
                logger.info("Creating a temp workspace at %s"%(opts['scratch_dir']))
            elif json_element == 'bootstrap':
                for bs_element in obj[json_element]:
                    if bs_element == 'nocloud':
                        opts['nocloud'] = obj[json_element][bs_element]
                    elif bs_element == 'bootstrap_cloud_init_drive_type':
                        opts['bootstrap_cloud_init_drive_type'] = obj[json_element][bs_element]
                    elif bs_element == 'bootstrap_cloud_init_bus_type':
                        opts['bootstrap_cloud_init_bus_type'] = obj[json_element][bs_element]
                    elif bs_element == 'file_list':
                        sysgen_list = handle_mounts_and_custom_vars(opts, t_dict, obj[json_element][bs_element])
            else:
                opts[json_element] = obj[json_element]
        if 'package_output_dir' in opts:
            s_dict = {'system_generated_properties': {'system_property': sysgen_list}}
            sys_gen_xml = xmltodict.unparse(s_dict, pretty=True)
            global sys_gen_prop
            logger.info("creating system_generated_properties.xml file")
            sys_gen_prop = os.path.join(opts['scratch_dir'], sys_gen_prop)
            with open(os.path.join(opts['scratch_dir'], sys_gen_prop), "w") as fd:
                logger.info("writing system properties to system_generated_properties.xml file")
                fd.write(sys_gen_xml)
        else:
            logger.error(error_messages['package_output_dir'])
            error_handler(error_messages['package_output_dir'],opts,536,INTERNAL_ERROR,'package_output_dir')
    else:
        logger.error("The file %s doesn't exist. Make sure it exists and run the tool again"%(jsonfile))
        error_handler("Invalid Json file path specified",opts,539,INTERNAL_ERROR,jsonfile)
    return(opts)

def db_build_from_json(opts, t_dict):
    s_dict = {}
    json_file = opts['json']
    custom_list = []
    sysgen_list = []
    if os.path.exists(json_file):
        with open(json_file, 'r') as f:
            obj = json.load(f)
    else:
        print('No JSON input file found')
        sys.exit()
    for file in obj['file']:
        bootstrap_sources.append(file['@name'])
        for pos in file['position']:
            bs_dict = {}
            if opts['multi_use'] and 'terminationMode' in pos:
                termMode = pos['terminationMode']
            if 'terminationMode' in pos:
                bs_dict['@terminationMode'] = termMode
            bs_dict['@mnt_pnt'] = file['mnt_point']
            bs_dict['@parse'] = file['parse']
            ha_mode_spec = True if 'ha_mode' in file else False
            if ha_mode_spec:
                if file['ha_mode'] == 'standalone':
                    bs_dict['@vm'] = '0'
                elif file['ha_mode'] == 'primary':
                    bs_dict['@vm'] = '1'
                else:
                    bs_dict['@vm'] = '2'
            if 'vmMode' in file:
                bs_dict['@firewallMode'] = file['vmMode']
            bs_dict['#text'] = file['@name']
            bsfile_list.append(bs_dict)
            if 'UserInput' in pos:
                for opt in pos['UserInput']:
                    each_custom = {}
                    if 'common' in pos:
                        each_custom['@common'] = opt['@common']
                    if '@mandatory' in opt and opt['@mandatory'] == 'true':
                        each_custom['@mandatory'] = opt['@mandatory']
                    if '@terminationMode' in pos:
                        each_custom['@terminationMode'] = termMode
                    if opts['multi_use']:
                        each_custom['@position'] = pos['@at']
                    if 'vmMode' in file:
                        each_custom['@firewallMode'] = file['vmMode']
                    if ha_mode_spec:
                        each_custom['@ha'] = 'false' if bs_dict['@vm'] == '0' else 'true'
                    each_custom['name'] = {
                        '@display': opt['display_str'], '#text': opt['name']}
                    each_custom['type'] = opt['type']
                    each_custom['val'] = ""
                    custom_list.append(each_custom)
            if 'SysGen' in pos:
                for opt in pos['SysGen']:
                    each_sys = OrderedDict()
                    if 'common' in pos:
                        each_sys['@common'] = opt['@common']
                    if '@terminationMode' in pos:
                        each_sys['@terminationMode'] = termMode
                    if '@at' in pos and pos['@at'] != 'None':
                        each_sys['@position'] = pos['@at']
                    if 'vmMode' in file:
                        each_sys['@firewallMode'] = file['vmMode']
                    each_sys['name'] = opt['name']
                    each_sys['type'] = opt['type']
                    each_sys['val'] = ""

                    sysgen_list.append(each_sys)


    t_dict['image_properties']['bootstrap_file'] = bsfile_list
    '''
        eleminate dups
    '''
    custom_set = set([json.dumps(c) for c in custom_list])
    custom_list = [json.loads(cs) for cs in custom_set]
    t_dict['image_properties']['custom_property'] = custom_list
    sysgen_set = set([json.dumps(c) for c in sysgen_list])
    sysgen_list = [json.loads(ss,object_pairs_hook=OrderedDict) for ss in sysgen_set]
    s_dict = {'system_generated_properties': {'system_property': sysgen_list}}
    sys_gen_xml = xmltodict.unparse(s_dict, pretty=True)
    global sys_gen_prop
    sys_gen_prop = os.path.join(opts['scratch_dir'], sys_gen_prop)
    with open(sys_gen_prop, "w") as fd:
        fd.write(sys_gen_xml)



def add_profiles(opts,t_dict):
    profiles = opts['profile']
    if profiles != None:
        l = []
        for item in profiles:
            if not "," in item or len(item.split(",")) <4:
                print("profile should be in the format name,desc,vcpu,mem,disk \
                \n example:--profile profile1,\"This is profile 1\",2,2048,4096.")
                sys.exit()
            #if decsription is not provided
            if len(item.split(",")) <= 4:
                (name,vcpus,memory_mb,root_disk_mb) = item.split(",")
                description = name
            else:
                (name,description,vcpus,memory_mb,root_disk_mb) = item.split(",")

            l.append({"name":name,"description":description,'vcpus':vcpus,"memory_mb":memory_mb,"root_disk_mb":root_disk_mb})
        t_dict['image_properties']['profiles']={'profile':l}

def add_default_options(opts,t_dict):
    f_mode = {'name':'firewallMode','type':'string','val':'routed'}
    t_mode = {'name':'terminationMode','type':'string','val':'routed'}
    if 'multi_use' in opts and opts['multi_use']:
        t_dict['image_properties']['default_property'] = [f_mode,t_mode]


def make_image_prop_xml(template_dict,opts):
    for arg in opts:
        if arg == "root_disk_image":
            template_dict['image_properties']['root_image_disk_format']=get_image_extension(opts[arg][0])
            handle_root_disk_images(opts,template_dict['image_properties'])
            template_dict['image_properties']['imageType'] = "virtualmachine"
        elif arg == "monitored":
            template_dict['image_properties']['monitoring_supported'] = opts[arg]
            if opts['monitored'] == 'false':
                template_dict['image_properties']['bootup_time'] = "-1"
        elif arg == "bootup_time" and opts['monitored'] == 'false':
            template_dict['image_properties']['bootup_time'] = "-1"
        elif arg == "default_profile" and (not opts['ha_package']):
            template_dict['image_properties']['default_profile'] = opts[arg]
        elif arg == "virtual_interface_model":
            if opts[arg]!= None:
                template_dict['image_properties'][arg] = opts[arg]
        elif arg == "thick_disk_provisioning":
            if opts[arg]=="true":
                template_dict['image_properties'][arg] = opts[arg]
        elif arg == "eager_zero":
            if opts[arg]=="true":
                template_dict['image_properties'][arg] = opts[arg]
        elif arg == "bootstrap_cloud_init_bus_type":
            if opts[arg] == "virtio":
                template_dict['image_properties'][arg] = opts[arg]
        elif arg == "bootstrap_cloud_init_drive_type":
            if opts[arg] == "disk":
                template_dict['image_properties'][arg] = opts[arg]
        elif arg == "nocloud":
            if opts[arg] == 'true':
                template_dict['image_properties'][arg] = opts[arg]
        elif arg == "vnf_version":
            template_dict['image_properties']['version'] = opts[arg]
        elif arg == "app_vendor":
            template_dict['image_properties']['applicationVendor'] = opts[arg]
        elif arg == "profile" and (not opts['ha_package']):
            add_profiles(opts,template_dict)
        elif arg == "sriov_supported":
            template_dict['image_properties']['sriov_supported']=opts['sriov_supported']
        elif arg == 'sriov_driver_list':
            template_dict['image_properties'][arg]=opts[arg]
        elif arg == "pcie_supported":
            template_dict['image_properties']['pcie_supported']=opts['pcie_supported']
        elif arg == 'pcie_driver_list':
            template_dict['image_properties'][arg]=opts[arg]
        elif arg == 'vnic_names':
            l = []
            for vn in opts[arg]:
                l.append("vnics:"+vn)
            template_dict['image_properties'][arg]=l
        elif arg == 'ha_capable':
            if (opts[arg]):
                template_dict['image_properties'][arg] = 'true'
                if 'ha_vnic' in opts:
                    template_dict['image_properties']['ha_vnic']=opts['ha_vnic']
                    template_dict['image_properties']['num_ha_vnics']=opts['ha_vnic_count']
        elif arg == 'mgmt_vnic':
            if opts[arg] != None:
                template_dict['image_properties'][arg] = opts[arg]
        elif arg == 'bootstrap':
            if opts['ha_package']:
                template_dict['image_properties']['bootstrap_file']=bsfile_list
            else:
                for i,src_dest in enumerate(bsfile_list,1):
                    val = src_dest['dst']
                    template_dict['image_properties']['bootstrap_file_'+str(i)] = val
        elif arg == 'custom':
            if opts['ha_package']:
                add_custom(opts,template_dict)
            else:
                add_custom_legacy(opts,template_dict)
        elif arg == 'json':
            db_build_from_json(opts,template_dict)
        elif arg == 'volumes':
            vol_dict = {'volume':opts[arg]}
            #remove if UI takes care of it
            for volume in vol_dict['volume']:
                if 'deviceType' in volume:
                    volume['device_type'] = volume.pop('deviceType')
                if 'storageLocation' in volume:
                    volume['storage_location'] = volume.pop('storageLocation')
            template_dict['image_properties']['storage'] = {'volumes': vol_dict}
        elif arg == 'interface_hot_add':
            template_dict['image_properties'][arg]=str(opts[arg]).lower()
        elif arg == 'interface_hot_delete':
            template_dict['image_properties'][arg]=str(opts[arg]).lower()
        else:
            if arg in template_dict['image_properties']:
                template_dict['image_properties'][arg] = opts[arg]
    if 'privileged_vm' in template_dict['image_properties']:
        template_dict['image_properties']['disable_spoof_check'] = template_dict['image_properties'].pop('privileged_vm')

    if opts['ha_package']:
        add_default_options(opts,template_dict)
        add_custom_special(opts,template_dict)
    l = xmltodict.unparse(template_dict, pretty=True)

    global image_prop_file
    if 'newjson' in opts:
        logger.info("creating image_properties.xml")
        image_prop_file = os.path.join(opts['scratch_dir'], image_prop_file)
    if 'newjson' in opts:
        logger.info("writing to image_properties.xml")
    with open(image_prop_file,"w") as fd:
        fd.write(l)

def validateArguments(opts):
    if  opts['ha_package'] and ('_' in opts['name'] or '_' in opts['vnf_version'] or '_' in opts['vnf_type']):
        print("'_' character not allowed in -n(--vnf_name)/-t(--vnf_type) and -r/(--vnf_version) options")
        sys.exit()
    bootstrap_len = len(opts['bootstrap']) if 'bootstrap' in opts else 0
    if bootstrap_len != 0:
        bs_files = opts['bootstrap']
        if (bootstrap_len > 20):
            print("No of bootstraps given %s, max allowd is 20."%len(bs_files))
            sys.exit()
        for key_vals in bs_files:
            if len(key_vals)<2 and opts['ha_package']:
                print("--bootstrap options must be in format of comma separated key:value pairs; see Usage string")
                sys.exit()
            elif opts['ha_package']:
                key_val_dict = {}
                for key_val in key_vals:
                    if ':' not in key_val or len(key_val.split(':')) > 2:
                        print("--bootstrap options must be in format of comma separated key:value pairs; see Usage string")
                        sys.exit()
                    key,val = key_val.split(':')
                    if key != 'file':
                        if key == "mount_point":
                            key = 'mnt_pnt'
                        key = '@'+key
                    else:
                        key = '#text'
                    key_val_dict[key] = val
                if '@mnt_pnt' not in key_val_dict or '#text' not in key_val_dict:
                    print("--bootstrap must at minimum contain 'mount_point:value' and 'file:value' key:value pair")
                    sys.exit()
                file = key_val_dict['#text']
                if not os.path.isfile(file):
                    print("--bootstrap option - %s not found"%file)
                    sys.exit()
                mnt_pnt = key_val_dict['@mnt_pnt']
                file = key_val_dict['#text']
                if mnt_pnt == '/':
                    key_val_dict['@mnt_pnt'] = '/'+file
                bootstrap_sources.append(file)
                bsfile_list.append(key_val_dict)
            elif not opts['ha_package']:
                for item in key_vals:
                    bsfile={}
                    if ":" in item:
                        (key,val)=item.split(":")
                        if os.path.isfile(val) == False:
                            print("File %s doesn't exist, Please make sure file exists and rerun the tool."%(val))
                            sys.exit()
                        else:
                            if key == '/':
                                bsfile["dst"]=key+val
                            elif key == '':
                                bsfile["dst"]= '/'+val
                            else:
                                bsfile["dst"]=key
                            bsfile["src"]=val
                            bootstrap_sources.append(val)
                            bsfile_list.append(bsfile)
                    else:
                        print("wrong format of bootstrap options")

    if 'sriov_driver_list' in opts and opts['sriov_supported'] != 'true':
        print("sriov_list is provided, setting sriov flag to true. --sriov true")
        opts['sriov_supported'] = "true"
    if 'pcie_driver_list' in opts and opts['pcie_supported'] != 'true':
        print("pcie_list is provided, setting pcie flag to true. --pcie true")
        opts['pcie'] = "true"

    if opts['profile'] != None:
      if (opts['default_profile'] == None):
        input = raw_input('default_profile  should be provided... Please enter input:' )
        opts['default_profile'] = input

      items = [item.split(",")[0] for item in opts['profile']]
      while opts['default_profile'] not in items:
        input = raw_input('default_profile provided is not the profile list provided... Please enter input:' )
        opts['default_profile'] = input

      modProf = []
      for prof in opts['profile']:
        if len(prof.split(",")) == 5:
          prof = prof.split(",")[2:]
          modProf.append(prof)
        else:
          modProf.append(prof.split(",")[1:])

      items = [item[0] for item in modProf]
      for item in items:
          if not (opts['vcpu_min'] is None and opts['vcpu_max'] is None) :
            if (int(item) < int(opts['vcpu_min'])) or (int(item) > int(opts['vcpu_max'])):
              print("vcpu=%s given in the profile should be in the range of min_vcpu=%s to max_vcpu=%s, exiting...retry again" % (item, opts['min_vcpu'], opts['max_vcpu']))
              sys.exit()

      items = [item[1] for item in modProf]
      for item in items:
          if not (opts['memory_mb_min'] is None and opts['memory_mb_max'] is None) :
            if (int(item) < int(opts['memory_mb_min'])) or (int(item) > int(opts['memory_mb_max'])):
              print("mem=%s MB given in the profile should be in the range of min_mem=%s MB to max_mem=%s MB, exiting...retry again" % (item, opts['min_mem'], opts['max_mem']))
              sys.exit()

      items = [item[2] for item in modProf]
      for item in items:
          if not (opts['root_disk_gb_min'] is None and opts['root_disk_gb_max'] is None) :
            if (int(item) < int(opts['root_disk_gb_min'])*1024) or (int(item) > int(opts['root_disk_gb_max'])*1024):
              print("disk=%s MB given in the profile should be in the range of min_disk=%s GBto max_disk=%s GB, exiting...retry again" % (item, opts['min_disk'], opts['max_disk']))
              sys.exit()


def get_mandatory_args(opts):
   mandatoryArgs = ["package_filename","root_disk_image","name","vnf_type","vnf_version","monitored","optimize", "sysinfo_support"]
   for mandatoryArg in mandatoryArgs:
       if not mandatoryArg in opts:
            input = raw_input(re.sub('[^a-zA-Z0-9 \n.]', ' ', str(mandatoryArg))+ ': ' )
            while not (re.match('^[a-zA-Z0-9-.-_,]*$',input)) or input == '':
                print("invalid input...\n")
                input = raw_input('Following Mandatory parameters are needed: \n' + re.sub('[^a-zA-Z0-9 \n.]', ' ', str(mandatoryArg))+ ': ' )
                if mandatoryArg == "root_disk_image":
                    opts[mandatoryArg] = input.split(",")
                elif mandatoryArg == "monitored":
                    if (input.lower() == "true") or (input.lower() == "false"):
                        opts[mandatoryArg] = input.lower()
                    else:
                        print("Error: options for monitored are true/false \n")
                        input=''
                elif mandatoryArg == "optimize":
                    if (input.lower() == "true") or (input.lower() == "false"):
                        opts['low_latency'] = input.lower()
                    else:
                        print("Error: options for optimize are true/false \n")
                        input=''
                elif mandatoryArg == "sysinfo_support":
                    if (input.lower() == "true") or (input.lower() == "false"):
                        opts['sysinfo_support'] = input.lower()
                    else:
                        print("Error: options for sysinfo_support are true/false \n")
                        input=''

                else:
                   opts[mandatoryArg]=input

def csv_arg_parse(string):
    return string.lower().split(',')

def csv_arg_parse_case(string):
    return string.split(',')

def pack_files(opts):
    directory = opts['pack']
    files = os.listdir(directory)
    if not 'image_properties.xml' in files:
        print('image_properties file not found')
        sys.exit()
    #pprint(files)
    if 'system_generated_properties.xml' in files:
        opts['ha_package'] = True
    if opts['ha_package']:
        find_ha_bootstrap_sources(opts)
    else:
        find_non_ha_bootstrap_sources(opts)

def find_non_ha_bootstrap_sources(opts):
    """
        Populate the list of bootstrap configuration files to package. For branch
        flavored VMs, we read the bootstrap files from package manifest

        Args:
            opts (dict) : Python dict object with options passed by the user, or
                inferred by the script
    """
    directory = opts['pack']
    def _handle_file_info(item_path, item_value):
        """
            Handle each File_Info element to extract list of bootstrap files

            Args:
                item_path (list): List of tuples of ancestral tag names
                    and dictionary of their attribute names and values
                item_value (OrderedDict) : Dictionary of tags, attributes, and values
                    inside the element at given depth

            Returns:
                bool : always returns True to continue parsing
        """
        if item_path[0][0] != PACKAGE_CONTENTS_TAG:
            print("Invalid package manifest file format. Expecting tag {}".format(PACKAGE_CONTENTS_TAG))
            sys.exit(1)
        if item_path[1][0] != FILE_INFO_TAG:
            return True
        file_type = item_value.get(FILE_INFO_TYPE_TAG)
        if file_type and file_type.startswith(BOOTSTRAP_FILE_TYPE_PREFIX):
            file_name = item_value.get(FILE_INFO_NAME_TAG)
            if file_name:
                bootstrap_sources.append(file_name.encode(ASCII_CHARSET))
        return True
    package_manifest_abs_path = os.path.join(directory, pkgmf_file)
    if os.path.isfile(package_manifest_abs_path) and not os.path.islink(package_manifest_abs_path):
        with open(package_manifest_abs_path, "rt") as mf:
            xmltodict.parse(mf, item_depth=2, item_callback=_handle_file_info)


def find_ha_bootstrap_sources(opts):
    directory = opts['pack']
    #suck the image properties file and ensure all the bootstraps are available
    with open(os.path.join(directory,'image_properties.xml'),"r") as fd:
        template_dict = xmltodict.parse(fd.read())
        if 'bootstrap_file' in template_dict['image_properties']:
            bsfiles = template_dict['image_properties']['bootstrap_file']
            if (type(bsfiles) == list):
                for bsfile in bsfiles:
                    file_name = bsfile['#text']
                    if file_name not in  bootstrap_sources:
                        bootstrap_sources.append(file_name)
            else:
                file_name = bsfiles['#text']
                if file_name not in  bootstrap_sources:
                    bootstrap_sources.append(file_name)

def check_pythonversion():
    # Python version 2.7.5 in hex is 0x20705f0
    if sys.hexversion < 0x20705f0:
        print("Python version 2.7.5 or higher is needed to run the packaging tool. Exiting")
        sys.exit()

def validate_repackage(options, pkg_name=''):
    '''
        Function to check the validity of the options provided.
    '''
    # check for the disk option is provided or not
    if options['root_disk_image'] is None:
        return 'VM images is not provied, please provide the root_disk_image.', options, pkg_name

    options['src_dir'], pkg_name = extract_path(pkg_name)
    # if destination dir is not given generate the package at src directory.
    if 'dest_dir' not in options:
        options['dest_dir'] = options['src_dir']
    return '', options,  pkg_name

#Adding a switch case option for the tool functioning
#based on the option given specific part will be called

def convert(options, file_path):
    '''
        convert : function to conver the non-vmanaged packages 
                  to vmanaged version.
    '''
    print ('Conversion Started  ##########')
    convertTargetFile(options, file_path)
    print ('Conversion Finished ##########')


def recal_checksum(path, filename, tar_cmd, cksum):
    '''
        recal_checksum: function to check if the file is present or not 
                        and recalculate the sha1 or sha256 cheksum and also add the
                        file name in the tar command.
        Input: directory path, filename, tar command
        return: extended tar command and the checksum of the file.
    '''
    file_path = os.path.join(path, filename)
    # calucalte the checksum for the files
    if not os.path.isfile(file_path):
        print("File %s doesn't exist, Please make sure the path entered for the root disk image is correct."%file_path)
        subprocess.call(["rm", "-rf", str(temp_dir)])
        cleanup(options)
        sys.exit()
    else:
        if cksum == 'sha1_checksum':
            chksum = sha1sum(file_path)
        else:
            chksum = sha256sum(file_path)
        tar_cmd.extend(["-C", path, filename])
    return tar_cmd, chksum

def repackage(options, file_path, convert=False):
    '''
        repackage : function to re-package the metadata file with the vm images.
    '''
    # Running some validations and extraction the soruce and the destination directory.
    ret_str, options, pkg_name = validate_repackage(options, file_path)
    if ret_str is not '':
        print ('%s' %ret_str)
        return
    print ('Re-package Started  ##########')
    dest_path = options['dest_dir']
    if not os.path.isdir(dest_path):
        print ('The destination path defined does not exist, please enter the correct path')
        return
    # Here metadata.tar.gz will be untared and after that repackaging with the root_disk_images 
    # will be done.
    '''
        1. Untar the metadata file to a temp directory.
        2. generate the new package.mf based on the previous version or the option provided.
        3. tar all the file back along with root_disk_images, to a file with prefix 'repackaged'.
    '''
    try:
        # check if the /tmp exist on the system or not
        if os.path.isdir("/tmp"):
            temp_dir = tempfile.mkdtemp(dir="/tmp/")
        else:
            temp_dir = tempfile.mkdtemp(dir=os.getcwd())
        print(temp_dir)

        # use temp_dir to untar and delete when done:
        src_path = temp_dir
        tar_cmd = ['tar', '-xzf', os.path.join(options['src_dir'], pkg_name), '-C', src_path]
        subprocess.call(tar_cmd) # run the command

        #Calculate the new sha256/sha1 cheksum of the change files and
        #update the package.mf file.
        pkg_dict={}
        with open(os.path.join(src_path,'package.mf'),"r") as fd:
            pkg_dict = xmltodict.parse(fd.read())
        tar_cmd = ["tar", "-czf", os.path.join(dest_path,'repackaged_'+pkg_name)]

        #delete the disk image info as we need to update the image name
        image_list = [file_entry for file_entry in pkg_dict['PackageContents']['File_Info']
                    if ((file_entry['type'] == 'root_image') or re.match('^ephemeral_disk[0-9]+_image$',file_entry['type']))]
        print image_list
        for img in image_list:
            full_path = os.path.join(src_path,img['name'])
            if os.path.exists(full_path):
                os.remove(full_path)
        pkg_dict['PackageContents']['File_Info']=[file_entry for file_entry in pkg_dict['PackageContents']['File_Info']
                 if not ((file_entry['type'] == 'root_image') or re.match('^ephemeral_disk[0-9]+_image$',file_entry['type']))]

        sha_type = 'sha256_checksum'
        for pkg in pkg_dict['PackageContents']['File_Info']:
            if 'sha1_checksum' in pkg:
                sha_type = 'sha1_checksum'
            filename = pkg['name']
            tar_cmd, chksum = recal_checksum(src_path, filename, tar_cmd, sha_type)
            pkg[sha_type] = chksum

        #Add the root disk file to the metdata as well and update the checksum
        for disk_count,disk in enumerate(options['root_disk_image']):
            path, filename = extract_path(disk)
            root_dict={}
            root_dict['name'] = filename
            if (disk_count == 0):
                root_dict['type'] = 'root_image'
            else:
                root_dict['type'] = 'ephemeral_disk{disk_count}_image'.format(disk_count=disk_count)

            path = os.path.abspath(path)
            tar_cmd, chksum = recal_checksum(path, filename, tar_cmd, sha_type)
            root_dict[sha_type] = chksum
            pkg_dict['PackageContents']['File_Info'].append(root_dict)

        pkg_val=(xmltodict.unparse(pkg_dict, pretty=True, full_document=False))
        with open(os.path.join(src_path, pkgmf_file), "w+") as f:
            if sha_type == 'sha256_checksum':
                f.write("<!-- sha256sum - for calculating checksum -->\n")
            else:
                f.write("<!-- sha1sum - for calculating checksum -->\n")
        with open(os.path.join(src_path, pkgmf_file), "a") as f:
            f.write(pkg_val)
        tar_cmd.extend(["-C", src_path, pkgmf_file])
        print(tar_cmd)
        subprocess.call(tar_cmd) # run the command
        subprocess.call(["rm", "-rf", str(temp_dir)])
    except OSError:
        logger.info('OSError occured while converting the package.')
        subprocess.call(["rm", "-rf", str(temp_dir)])
        pass
    except Exception as e:
        print 'Exception occured %s'%e
        logger.info('Exception occured while converting the package.')
        subprocess.call(["rm", "-rf", str(temp_dir)])
        pass
    cleanup(options)
    print ('Re-package Finished ##########')

def string_to_option(val, options, file_path):
    switcher = {
        'convert': convert,
        'repackage': repackage,
    }
    func=switcher.get(val,lambda :'Invalid option')
    return func(options, file_path)


def main():
    print("\nCisco NFV-IS Packaging Tool \n")
    check_pythonversion()
    desc = 'Version: '+ VERSION + ' Cisco NFVIS: VNF image packaging utility'
    parser = argparse.ArgumentParser(description=desc)
    required = parser.add_argument_group('Required')
    required.add_argument("-o", "--package_filename",
                        help="[REQUIRED] file name for the target VNF package name- \
                        default is root disk image name with extension .tar.gz ")
    required.add_argument("-i", "--root_disk_image",
                        type=csv_arg_parse_case,
                        help="[REQUIRED] List of root disk images to be bundled \
                        example: --root_disk_image isrv.qcow2; --root_disk_image isrv1.qcow2,isrv2.qcow2")
    required.add_argument("--prop_template",
                        dest="prop_template",
                        default="image_properties_template.xml",
                        help="image properties template file name including path \
                              default path is the current dir of the tool \
                              and name is image_properties_template.xml if the user doesn't input this option \
                              example: --prop_template /usr/bin/image_properties_template.xml ")
    required.add_argument("-t", "--vnf_type",
                        dest="vnf_type",
                        default=argparse.SUPPRESS,
                        help="[REQUIRED] VNF type, e.g. ROUTER, FIREWALL, vWAAS, vWLC, WLC, and OTHER ")
    required.add_argument("-n", "--vnf_name",
                        dest="name",
                        default=argparse.SUPPRESS,
                        help="[REQUIRED] Name of the VNF image ")
    required.add_argument("-r", "--vnf_version",
                        dest="vnf_version",
                        default=argparse.SUPPRESS,
                        help="[REQUIRED] VNF version, e.g. --vnf_version 1.0 or  --vnf_version 0.9 ")
    required.add_argument("--app_vendor",
                        dest="app_vendor",
                        default=argparse.SUPPRESS,
                        help="Application Vendor e.g. Cisco, Juniper etc")
    required.add_argument("--monitored",
                        type=str.lower,
                        default=argparse.SUPPRESS,
                        choices=['true','false'],
                        dest="monitored",
                        help="[REQUIRED] Monitored VNF: --monitored=true/false; ")
    required.add_argument('--optimize',
                        type=str.lower,
                        choices=['true','false'],
                        default='true',
                        dest="low_latency",
                        help="[REQUIRED] optimized VM: --optimize=true/false;")
    required.add_argument('--sysinfo_support',
                          type=str.lower,
                          choices=['true', 'false'],
                          default='false',
                          dest="sysinfo_support",
                          help="Add system information in the domain XML while "
                               "deploying the VM")

    parser.add_argument('--json',
                        help="Provide JSON input for bootstrap variables; mutually exclusive with custom and bootstrap configs",
                        default=argparse.SUPPRESS,
                        dest="json")
    parser.add_argument('--newjson',
                        help="Provide JSON input for bootstrap variables; mutually exclusive with custom and bootstrap configs",
                        default=argparse.SUPPRESS,
                        dest="newjson")
    parser.add_argument('--log_dir',
                        help='Log Directory to for logfiles',
                        default=argparse.SUPPRESS)
    parser.add_argument('--multi_use',
                        help='Add options for use in multiple use-cases',
                        action='store_true')
    parser.add_argument('--console_type_serial',
                      type=str.lower,
                      choices=['true','false'],
                      default="false",
                      dest="console_type_serial",
                      help="Attach the console serial to the VM; default is false;\
                            --console_type_serial=true/false;")
    parser.add_argument('--root_file_disk_bus',
                      type=str.lower,
                      choices=["virtio","ide"],
                      default = "virtio",
                      help="root disk file type: --root_file_disk_bus=virtio/ide; default is virtio")
    parser.add_argument('--virtual_interface_model',
                      choices=["rtl8139"],
                      type=str.lower,
                      help="--virtual_interface_model=rtl8139; default is none")
    parser.add_argument('--thick_disk_provisioning',
                      choices=['true','false'],
                      type=str.lower,
                      dest="thick_disk_provisioning",
                      help="--thick_disk_provisioning=true; default is false",
                      default=argparse.SUPPRESS)
    parser.add_argument('--eager_zero',
                      choices=['true','false'],
                      type=str.lower,
                      dest="eager_zero",
                      help="--eager_zero=true; default is false",
                      default=argparse.SUPPRESS)
    parser.add_argument('--nocloud',
                      choices=['true','false'],
                      type=str.lower,
                      dest="nocloud",
                      help="--nocloud=true/false; default is false",
                      default=argparse.SUPPRESS)
    parser.add_argument('--bootstrap_cloud_init_bus_type',
                      choices=["ide","virtio"],
                      type=str.lower,
                      default=argparse.SUPPRESS,
                      help="--bootstrap_cloud_init_bus_type=virtio; default is ide")
    parser.add_argument('--bootstrap_cloud_init_drive_type',
                      choices=["cdrom","disk"],
                      type=str.lower,
                      default=argparse.SUPPRESS,
                      help="--bootstrap_cloud_init_drive_type=disk; default is cdrom")
    parser.add_argument("--bootstrap",
                       action='append', type=csv_arg_parse_case,default=argparse.SUPPRESS,
                       help=""" Every bootstrap file should be a different option
                            Non HA format: --bootstrap <mountpoint>:<file1>,<mountpoint>:<file2>...
                                See usage.txt for more details
                            HA format for Cisco Cloud OnRamp for Colocation: --bootstrap mount_point:<value>,file:<file2mount>[,<attrib>:<value>]
                                mount_point:<value> and file:<file2mount> are mandatory
                                followed by one or more attributes in the format <attrib>:<value>""")
    parser.add_argument("--interface_hot_add",
                       choices=['true','false'],
                       type=str.lower,
                       dest="interface_hot_add",
                       default=argparse.SUPPRESS,
                       help="VM supports interface add without power off.\
                             Default is set to true;\
                             --interface_hot_add=true/false")
    parser.add_argument("--interface_hot_delete",
                      choices=['true','false'],
                      type=str.lower,
                      dest="interface_hot_delete",default=argparse.SUPPRESS,
                      help="VM supports interface delete without power off.\
                            Default is set to false;\
                            --interface_hot_delete=true/false")
    parser.add_argument("-v", "--verbose",
                      action="store_true", dest="verbose",
                      help="verbose")
    parser.add_argument("-q", "--quiet",
                      action="store_false", dest="verbose",
                      help="quiet")

    parser.add_argument("--no_compress",
                       dest="no_compress",
                       action="store_true",
                       help="creates tar file without compressing the input files")
    parser.add_argument("--cleanup",
                       dest="cleanup",
                       action="store_true",
                       help="deletes all the input and configuration files upon tar file created ")

    parser.add_argument("--tablet",
                      choices=['true','false'],
                      type=str.lower,
                      dest="tablet",
                      help=": Add input device of type tablet --tablet=true/false; ")

    parser.add_argument("--ha_package",action="store_true",
                        help="enable HA packaging" )
    parser.add_argument("--mgmt_vnic",
                        help="VM management interface identifier",default=argparse.SUPPRESS)

    parser.add_argument('--pack_dir <DIR>',dest='pack',help='package all files in directory',default=argparse.SUPPRESS)

    ha_opts = parser.add_argument_group('HA options')
    ha_opts.add_argument('--ha_capable',action='store_true',default=argparse.SUPPRESS)
    ha_opts.add_argument('--ha_vnic',help="VM HA vnic",default=argparse.SUPPRESS)
    ha_opts.add_argument('--ha_vnic_count',help="Number of ha_vnics",default=argparse.SUPPRESS)

    resources = parser.add_argument_group('Resources','Resources: min and max - vCPU, memory and disk ')
    resources.add_argument('--min_vcpu', help='min #vCPU : min number of vCPU supported by VM \
                                example:--min_vcpu 2 ',dest='vcpu_min',default=str(1))
    resources.add_argument('--max_vcpu', help='max #vCPU : max number if vCPU required for VM \
                                example:--max_vcpu 4 ',dest='vcpu_max',default=str(8))
    resources.add_argument('--min_mem', help='min mem : min mem in MB required for VM \
                                example:--min_mem 1024',dest='memory_mb_min',default=str(4096))
    resources.add_argument('--max_mem', help='max mem : max mem in MB required for VM \
                                example:--max_mem 4196',dest='memory_mb_max',default=str(8192))
    resources.add_argument('--min_disk', help='min disk : min disk in GB required for VM \
                                example:--min_disk 8 ',dest='root_disk_gb_min',default=str(8))
    resources.add_argument('--max_disk', help='max disk : max disk in GB required for VM \
                                example:--max_disk 8 ',dest='root_disk_gb_max',default=str(8))
    resources.add_argument('--vnic_max', default=str(8),help='max number of Vnics allowed for VM \
                                example:--vnic_max 8 ')
    resources.add_argument('--vnic_names', type=csv_arg_parse,
                            help='list of vnic number to name mapping in format number:name\
                                example --vnic_names 1:GigabitEthernet2,2:GigabitEthernet4',default=argparse.SUPPRESS)

    profile = parser.add_argument_group('Profile Options')
    profile.add_argument('--profile', help='enter the profile name, \
                                \n profile description, \
                                \n  no of vCPU required, \
                                min memory required in MB, \
                                min disk space required in MB, \
                                example: \
                                        --profile profile1,"This is profile 1",2,2048,4096 \
                                        --profile profile2,"This is profile 2",4,4096,4096',\
                       action='append')
    profile.add_argument('--default_profile', help='default profile',default=argparse.SUPPRESS)

    drivers = parser.add_argument_group('Driver Support Options')
    drivers.add_argument('--sriov',
                       choices=['true','false'],
                       type=str.lower,
                       dest="sriov_supported",
                       help='Enable/Disable SRIOV support: --sriov=true/false; default is false', default='false')
    drivers.add_argument('--sriov_list', help='list of  SRIOV drivers \
                         example: --sriov_list igb,igbvf,i40evf',
                         type=csv_arg_parse,dest='sriov_driver_list',default=argparse.SUPPRESS)
    drivers.add_argument('--pcie',
                       choices=['true','false'],
                       type=str.lower,
                       dest="pcie_supported",
                       help='Not supported', default=argparse.SUPPRESS)
    drivers.add_argument('--pcie_list', dest='pcie_driver_list', type=csv_arg_parse,
                            help='Not supported',default=argparse.SUPPRESS)

    privileges = parser.add_argument_group('Privilege/Priority Options')
    privileges.add_argument('--privileged',
                            choices=['true','false'],
                            type=str.lower,
                            dest="privileged_vm",
                            help='Not supported ', default='false')

    custom_prop = parser.add_argument_group('Custom Properties')
    custom_prop.add_argument('--custom', action='append',type=csv_arg_parse_case,default=argparse.SUPPRESS,
                            help="""custom properties
                            format: --custom ["propattr_"<attr>:<value>],key:<value>,[keyattr_<attr>:<value>],type:<value>,val<N>:<value>,[val<N>attr_<attr>:<value>]
                            Allows specification of custom properties:
                                0 or more propattr_<attr>:<value> pairs - 'propattr' is a keyword and used to specify property attributes
                                key:<value> pairs
                                0 or more keyattr_<attr>:value pairs - 'keyattr' is a keyword and is used to specify key attributes
                                type:<value> pair - type of value
                                valN:<value> pair - val1:value,val2:value etc
                                0 or more valNattr_<attr>:<value> pairs - 'val<N>attr' is an attribute for val<N>
                                See usage_examples.txt
                            """)
    modify_prop = parser.add_argument_group('Modify Package')
    modify_prop.add_argument('--modify_package', choices=['convert', 'repackage'],
                            type=str.lower, dest='modify_package', default=argparse.SUPPRESS,
                                help='convert option is to change non-vmanaged to vmanaged package.\
                                      repackage is to modify the vm_package using a predefined metadata fiel package.\
                                      (for option repackage please provide the root file as well.) \
                            ')
    modify_prop.add_argument('--file_path', default=argparse.SUPPRESS,
                            help='provide the path to the tar file to \
                                  convert/repackage and generate a new package.')
    modify_prop.add_argument('--dest_dir', default=argparse.SUPPRESS,
                            help="""specify the destination directory:\
                                    --dest_dir /usr/share/ """)

    # if this tag is present conversion function get invokes 
    if '--modify_package' in sys.argv:
        options = vars(parser.parse_args())
        if 'file_path' in options:
            string_to_option(options['modify_package'], options, options['file_path'])
        else:
            print ('--file_path option is mandatory for modifying the package')
        sys.exit()

    if (len(sys.argv) == 0):
        options = {}
        get_mandatory_args(options)
    else:
        options = vars(parser.parse_args())

    if 'pack' not in options:
        mandateappvendor = 'app_vendor' in options if options['ha_package'] else True
        mandatory_opts_present = ('vnf_type' in options and 'name' in options and
                                  'vnf_version' in options and 'monitored' in options and
                                  'low_latency' in options and 'sysinfo_support' in options
                                  and mandateappvendor)
        opts_in_json = ('json' in options or 'newjson' in options)
        if not mandatory_opts_present and not opts_in_json:
            print ("""Neither JSON file nor Mandatory Options are not present:
                 -t/--vnf_type,-n/--vnf_name,-r/--vnf_version,--app_vendor,--monitored,--optimize""")
            sys.exit()
    else:
        if not os.path.exists(options['pack']):
            print ("Pack directory does not exist")

    if 'pack' in options:
        options['scratch_dir'] = options['pack']
        options['package_output_dir'] = options['pack']
        pack_files(options)
    elif 'newjson' in options:
        template_dict = xmltodict.parse(image_properties_template_contents)
        initialize_logger(options)
        logger.info("************Cisco Cloud OnRamp for Colocation - VNF packaging************")
        options = build_from_json(template_dict, options['newjson'])
        make_image_prop_xml(template_dict,options)
        if options['verbose']:
            print("Creating the target file %s " % options['package_filename'])
    else:
        if options['verbose']:
            print("validating the input arguments")
        validateArguments(options)
        cur_dir = os.getcwd()
        options['scratch_dir'] = cur_dir
        options['package_output_dir'] = cur_dir
        if options['verbose']:
            print("compiling image properties in mode ")
        if options['prop_template'] == None:
            options['prop_template'] = "image_properties_template.xml"
        with open(options['prop_template'],"r") as fd:
            template_dict = xmltodict.parse(fd.read())
        make_image_prop_xml(template_dict,options)
        if options['verbose']:
            print("Creating the target file %s " % options['package_filename'])

    buildTargetFile(options)

if __name__ == "__main__":
    main()
