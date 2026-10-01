"""Verify a sealed audit ZIP independently of its producer (stdlib only)."""
import hashlib,json,sys,zipfile
from pathlib import PurePosixPath
def verify(path):
    with zipfile.ZipFile(path) as z:
        names=z.namelist()
        assert len(names)==len(set(names)), 'duplicate ZIP members'
        assert all(not PurePosixPath(n).is_absolute() and '..' not in PurePosixPath(n).parts for n in names)
        assert all(not any(p in ('.git','.lake','__pycache__') or p.startswith('.env') for p in PurePosixPath(n).parts) for n in names)
        rows=json.loads(z.read('MANIFEST.json'))
        assert set(names)=={'MANIFEST.json'}|{r['path'] for r in rows}, 'manifest membership'
        for r in rows:
            assert z.getinfo(r['path']).file_size==r['bytes']
            with z.open(r['path']) as f:got=hashlib.file_digest(f,'sha256').hexdigest()
            assert got==r['sha256'], r['path']
        assert z.testzip() is None
    return dict(status='PASS',members=len(names),manifest_entries=len(rows))
if __name__=='__main__':print(json.dumps(verify(sys.argv[1]),indent=2))
