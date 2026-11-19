"""Rebuild the entire import closure in dependency order, ignoring external oleans."""
import os
import re
import subprocess
from pathlib import Path
root = Path(__file__).resolve().parents[1]
src = root / 'lean'
out = root / 'build'
out.mkdir(exist_ok=True)
env = dict(os.environ, LEAN_PATH=str(out))
subprocess.run(['lean','--version'],check=True)
seen = set()
def build(name):
    if name in seen:
        return
    source = src / (name+'.lean')
    for dep in re.findall(r'^import (\w+)',source.read_text(),re.M):
        build(dep)
    print('Checking',name,flush=True)
    subprocess.run(['lean','-j1','-o',str(out / (name+'.olean')),str(source)],cwd=root,env=env,check=True)
    seen.add(name)
if __name__=='__main__':
    subprocess.run(['python3',str(root/'scripts/generate.py')],cwd=src,check=True)
    build('Rule110Exact')
