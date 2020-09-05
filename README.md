# cisco_sdbranch
metadata for cisco and thirdparty VNF images

Use the nfvpt.py tool with the Modify option
nfvpt.py --modify_package REPACKAGE --file_path vedge_vmanage_scaf.tar.gz -i vedge.qcow2

Modify Package:
  --modify_package {convert,repackage}
                        convert option is to change non-vmanaged to vmanaged
                        package. repackage is to modify the vm_package using a
                        predefined metadata file package. (for option
                        repackage please provide the root file as well.)
  --file_path FILE_PATH
                        provide the path to the tar file to convert/repackage
                        and generate a new package.
  --dest_dir DEST_DIR   specify the destination directory: --dest_dir
                        /usr/share/
