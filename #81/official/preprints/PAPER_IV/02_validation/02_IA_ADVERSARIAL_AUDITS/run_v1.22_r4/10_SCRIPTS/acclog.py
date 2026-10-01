"""Append rows to 00_CONTROL/INPUT_ACCESS_LOG.csv.
usage: python acclog.py PATH HASH PURPOSE PHASE BASIS"""
import csv, sys, datetime, os
R = os.path.join(os.path.dirname(__file__), '..')
LOG = os.path.normpath(os.path.join(R, '00_CONTROL', 'INPUT_ACCESS_LOG.csv'))
def log(path, h, purpose, phase, basis):
    t = datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
    with open(LOG, 'a', newline='', encoding='utf-8') as f:
        csv.writer(f).writerow([path, h, purpose, phase, t, basis])
if __name__ == '__main__':
    log(*sys.argv[1:6])
