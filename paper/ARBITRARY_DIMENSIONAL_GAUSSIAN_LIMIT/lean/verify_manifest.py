from pathlib import Path
import hashlib
root=Path(__file__).resolve().parent
bad=[]
for line in (root/'SHA256SUMS').read_text(encoding='utf-8').splitlines():
    expected,name=line.split('  ',1)
    path=root/name
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=expected:
        bad.append(name)
if bad:
    raise SystemExit('HASH MISMATCH: '+repr(bad))
print('All packaged file hashes verified.')
