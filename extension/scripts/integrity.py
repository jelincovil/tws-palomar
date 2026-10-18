#!/usr/bin/env python3
"""Read-only checks; snapshots write only the requested JSON output."""
import argparse,hashlib,json,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('mode',choices=['snapshot','check','baseline']);p.add_argument('repo',type=Path);p.add_argument('manifest',type=Path);p.add_argument('--exclude-extension',action='store_true');a=p.parse_args()
def digest(f): return hashlib.sha256(f.read_bytes()).hexdigest()
if a.mode=='snapshot':
 names=subprocess.check_output(['git','-C',str(a.repo),'ls-files','-z']).decode().split('\0')
 data={n:digest(a.repo/n) for n in names if n and (a.repo/n).is_file() and not(a.exclude_extension and n.startswith('extension/'))}
 a.manifest.write_text(json.dumps(data,indent=2)+'\n');print('Snapshot:',len(data));raise SystemExit(0)
data=json.loads(a.manifest.read_text());bad=[]
for n,h in data.items():
 f=a.repo/n
 if not f.is_file() or digest(f)!=h: bad.append(n)
for n in bad: print('DIFF/MISSING',n)
print('PASS' if not bad else 'FAIL',len(data),'files');raise SystemExit(bool(bad))
