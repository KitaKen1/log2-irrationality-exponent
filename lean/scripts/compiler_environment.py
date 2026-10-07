"""Read Lake's compiler paths once, then run Lean without a resident Lake parent.
Only compiler/toolchain path variables are retained; no credentials are logged.
The same Lean binary, imported artifacts, and kernel checking are used.
"""
import os
from pathlib import Path
import subprocess

COMPILER_VARIABLES = {
    'LEAN', 'LEAN_SYSROOT', 'LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_GITHASH',
    'LEAN_AR', 'LEAN_CC', 'LAKE', 'LAKE_HOME', 'PATH',
    'DYLD_LIBRARY_PATH', 'LD_LIBRARY_PATH', 'ELAN_TOOLCHAIN',
}

def compiler_environment(root):
    # Bare `lake env` prints the variables set by Lake, not the entire process env.
    output = subprocess.check_output(['lake', 'env'], cwd=root, text=True)
    env = os.environ.copy()
    found = set()
    for line in output.splitlines():
        key, sep, value = line.partition('=')
        if sep and key in COMPILER_VARIABLES:
            env[key] = value
            found.add(key)
    if not {'LEAN', 'LEAN_PATH', 'LEAN_SYSROOT'} <= found:
        raise RuntimeError('Lake did not provide the required compiler paths')
    compiler = Path(env['LEAN'])
    if not compiler.is_absolute() or not compiler.is_file():
        raise RuntimeError('Lake returned an unavailable Lean executable')
    return str(compiler), env
