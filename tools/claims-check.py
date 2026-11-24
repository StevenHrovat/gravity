#!/usr/bin/env python3
"""Ledger check for the paper (docs/paper): stage 1 of docs/paper/REVIEW.md.

  python tools/claims-check.py

Fails (exit 1) on a duplicate claim ID, on a label in the paper that resolves to no row, folded label or section heading, or on a
count that differs from the first column of the counts table in CLAIMS.md. Prints the counts by primary status.
"""
import collections, glob, io, os, re, sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'docs', 'paper')
claims = io.open(os.path.join(ROOT, 'CLAIMS.md'), encoding='utf-8').read()
SCOPE = {'0.1', 'IV.0', 'VII.0e', 'VIII.0e', 'IX.0d', 'X.0a', 'X.0d', 'X.7d'}   # scope rows, not counted
R = r'(?:XI|IX|X|VIII|VII|VI|IV|V|III|II|I|A)'

rows_part = claims[:claims.index('## Draft 3 labels')]
ids, counts = collections.Counter(), collections.Counter()
malformed = []
for line in rows_part.splitlines():
    m = re.match(r'\| ([0-9IVXA]+\.[^ |]*) \| ', line)
    if not m:
        continue
    cells = [x.strip() for x in line.strip().strip('|').split('|')]
    if len(cells) < 5:
        continue
    ids[cells[0]] += 1
    if cells[0] in SCOPE:
        continue
    st = cells[2]
    if not st.split():
        malformed.append(cells[0])
        continue
    counts['paper' if st.lower().startswith('project rule') else st.split()[0].lower()] += 1

bad = []
if malformed:
    bad.append('malformed rows (empty status; a | inside a cell?): ' + ', '.join(malformed))
dups = [k for k, v in ids.items() if v > 1]
if dups:
    bad.append('duplicate IDs: ' + ', '.join(dups))

fi, ci = claims.index('## Folded labels'), claims.index('## Counts by')
folded = set(re.findall(r'(?m)^\| ([0-9IVXA]+\.[^ |]+) \| ', claims[fi:ci]))
heads = set()
for f in glob.glob(os.path.join(ROOT, 'draft', '*.md')):
    heads |= set(re.findall(r'(?m)^#{2,3} (' + R + r'\.\d+(?:\.\d+)*)', io.open(f, encoding='utf-8').read()))
known = set(ids) | folded | heads
def resolves(lab):
    return lab in known or any(k.startswith(lab + '.') or re.match(re.escape(lab) + r'[a-z]$', k) for k in known)
for f in glob.glob(os.path.join(ROOT, 'draft', '*.md')) + [os.path.join(ROOT, 'CLAIMS.md')]:
    t = io.open(f, encoding='utf-8').read()
    if f.endswith('CLAIMS.md'):
        t = t[:t.index('## Draft 3 labels')] + t[fi:]
    for m in re.finditer(r'(?<![A-Za-z0-9_/])(' + R + r'\.\d+[A-Za-z0-9.]*)', t):
        lab = m.group(1).rstrip('.')
        if not resolves(lab):
            bad.append('%s: unresolved label %s' % (os.path.basename(f), lab))

tbl = claims[ci:]
for st in ['Lean', 'classical', 'external', 'conditional', 'paper', 'numerical', 'certified', 'reading', 'open']:
    m = re.search(r'(?m)^\| ' + st + r' \| (\d+) \|', tbl)
    if not m or int(m.group(1)) != counts[st.lower()]:
        bad.append('count %s: table %s, rows %d' % (st, m.group(1) if m else '?', counts[st.lower()]))
m = re.search(r'(?m)^\| \*\*Total\*\* \| \*\*(\d+)\*\* \|', tbl)
if not m or int(m.group(1)) != sum(counts.values()):
    bad.append('total: table %s, rows %d' % (m.group(1) if m else '?', sum(counts.values())))

print('counts:', dict(sorted(counts.items())), 'total', sum(counts.values()))
if bad:
    print('\n'.join('FAIL ' + b for b in bad))
    sys.exit(1)
print('claims-check: OK')
