"""Serial bounded regressions. Each child has a 2 GiB Windows job limit."""
import ctypes as C
from ctypes import wintypes as W
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

RUN = Path(__file__).resolve().parents[1]
ROOT = RUN / '20_EVIDENCE/G2_MATHEMATICS'

class Memory(C.Structure):
    _fields_ = [('length', W.DWORD), ('load', W.DWORD)] + [(n, C.c_ulonglong) for n in ('physical', 'available', 'pagefile', 'free_pagefile', 'virtual', 'free_virtual', 'extended')]

class Basic(C.Structure):
    _fields_ = [('process_time', C.c_longlong), ('job_time', C.c_longlong), ('flags', W.DWORD), ('min_ws', C.c_size_t), ('max_ws', C.c_size_t), ('active', W.DWORD), ('affinity', C.c_size_t), ('priority', W.DWORD), ('scheduling', W.DWORD)]

class Extended(C.Structure):
    _fields_ = [('basic', Basic), ('io', C.c_ulonglong * 6), ('process_limit', C.c_size_t), ('job_limit', C.c_size_t), ('peak_process', C.c_size_t), ('peak_job', C.c_size_t)]

K = C.WinDLL('kernel32', use_last_error=True)
K.CreateJobObjectW.restype = W.HANDLE
K.AssignProcessToJobObject.argtypes = [W.HANDLE, W.HANDLE]
K.SetInformationJobObject.argtypes = [W.HANDLE, C.c_int, C.c_void_p, W.DWORD]
K.CloseHandle.argtypes = [W.HANDLE]
K.TerminateJobObject.argtypes = [W.HANDLE, W.UINT]
K.QueryInformationJobObject.argtypes = [W.HANDLE, C.c_int, C.c_void_p, W.DWORD, C.c_void_p]

def free_memory():
    m = Memory()
    m.length = C.sizeof(m)
    if not K.GlobalMemoryStatusEx(C.byref(m)):
        raise C.WinError(C.get_last_error())
    return m.available

def run(script):
    if free_memory() < 6 * 1024**3:
        raise RuntimeError('Less than 6 GiB free RAM; no child launched.')
    result_dir = script.parents[1] / 'results'
    result_dir.mkdir(exist_ok=True)
    record = result_dir / 'runner.json'
    if record.exists():
        old = json.loads(record.read_text())
        if old['script_sha256'] == hashlib.sha256(script.read_bytes()).hexdigest() and old['exit_code'] == 0:
            print('ALREADY_EXECUTED ' + str(script), flush=True)
            return old
        raise RuntimeError('Preserve prior attempt before retry: ' + str(record))
    job = K.CreateJobObjectW(None, None)
    limits = Extended()
    limits.basic.flags = 0x100 | 0x2000  # process memory limit; kill on close
    limits.process_limit = 2 * 1024**3
    if not K.SetInformationJobObject(job, 9, C.byref(limits), C.sizeof(limits)):
        raise C.WinError(C.get_last_error())
    started = time.time()
    argv = [sys.executable, str(script)]
    reason = None
    with (result_dir / 'stdout.txt').open('w', encoding='utf-8') as out, (result_dir / 'stderr.txt').open('w', encoding='utf-8') as err:
        env = dict(os.environ, OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1', MKL_NUM_THREADS='1', PYTHONIOENCODING='utf-8')
        p = subprocess.Popen(argv, stdout=out, stderr=err, env=env)
        if not K.AssignProcessToJobObject(job, W.HANDLE(int(p._handle))):
            p.kill()
            raise C.WinError(C.get_last_error())
        while p.poll() is None:
            if time.time() - started > 120 or free_memory() < 4 * 1024**3:
                reason = 'TIME_OR_MEMORY_GUARD'
                K.TerminateJobObject(job, 124)
                break
            time.sleep(0.5)
        code = p.wait()
    usage = Extended()
    K.QueryInformationJobObject(job, 9, C.byref(usage), C.sizeof(usage), None)
    K.CloseHandle(job)
    data = {'script': script.relative_to(RUN).as_posix(), 'script_sha256': hashlib.sha256(script.read_bytes()).hexdigest(), 'command': argv, 'exit_code': code, 'duration_seconds': time.time()-started, 'peak_memory_bytes': usage.peak_process, 'memory_limit_bytes': 2*1024**3, 'time_limit_seconds': 120, 'stop_reason': reason, 'scope': 'finite regression, not a universal proof'}
    record.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(data), flush=True)
    if code:
        raise RuntimeError('Regression failed; remaining jobs not launched.')
    return data

if __name__ == '__main__':
    for script in sorted(ROOT.glob('*/scripts/*.py')):
        run(script)
