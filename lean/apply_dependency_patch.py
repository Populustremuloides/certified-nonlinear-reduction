#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
root=Path(__file__).resolve().parent
spec=json.loads((root/'package_manifest.json').read_text())
directory=root/'.lake/packages/proofwidgets'
patch=root/'proofwidgets-local-build.patch'
current=subprocess.check_output(['git','-C',str(directory),'diff','HEAD','--no-ext-diff','--binary'])
if current:
    expected=spec['dependencies']['proofwidgets']['allowed_patch_sha256']
    if hashlib.sha256(current).hexdigest()!=expected:
        raise SystemExit('Unexpected existing ProofWidgets changes; preserved without modification.')
    print('Recorded build-target patch is already applied.')
else:
    subprocess.run(['git','-C',str(directory),'apply','--check',str(patch)],check=True)
    subprocess.run(['git','-C',str(directory),'apply',str(patch)],check=True)
    print('Applied the recorded build-target patch.')
