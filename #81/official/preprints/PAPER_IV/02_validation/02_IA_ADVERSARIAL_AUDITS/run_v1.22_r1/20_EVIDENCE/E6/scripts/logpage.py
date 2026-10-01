"""Append page-inspection rows: python logpage.py lang page status note [page status note ...] (only for sheets actually displayed)."""
import csv, sys, pathlib
P = pathlib.Path(__file__).resolve().parents[1] / 'PAGE_INSPECTION_LOG.csv'
a = sys.argv[1:]; lang = a[0]; rows = [[lang, a[i], a[i+1], a[i+2]] for i in range(1, len(a), 3)]
with open(P, 'a', newline='', encoding='utf-8') as f: csv.writer(f).writerows(rows)
