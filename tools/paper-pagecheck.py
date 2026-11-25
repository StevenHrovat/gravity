#!/usr/bin/env python3
"""Page check for a built paper: the table of contents must point to the page where each heading prints.

  python tools/paper-pagecheck.py <file.pdf> <file.toc>

Takes the part-level entries of the table of contents (\\contentsline {section}), picks the one in the middle, and checks with
pdftotext that its heading prints on the page the contents gives. A LaTeX build whose last pass read a stale table of contents
fails here. Exit 0 when the page matches, 1 when it does not, 2 when pdftotext is missing or the files cannot be read.
"""
import io, re, shutil, subprocess, sys

def norm(t):
    return re.sub(r'\s+', ' ', t).strip()

def main():
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    pdf, toc = sys.argv[1], sys.argv[2]
    if not shutil.which('pdftotext'):
        print('paper-pagecheck: pdftotext not installed, page check skipped')
        return 2
    entries = []
    for m in re.finditer(r'\\contentsline \{section\}\{(.*)\}\{(\d+)\}\{', io.open(toc, encoding='latin-1').read()):
        title = re.sub(r'\\[a-zA-Z]+\s*|[{}$\\`\'"]', '', m.group(1))
        entries.append((norm(title)[:24], int(m.group(2))))
    entries = [e for e in entries if len(e[0]) >= 8]
    if not entries:
        print('paper-pagecheck: no part-level entries in', toc)
        return 2
    title, page = entries[len(entries) // 2]
    text = subprocess.run(['pdftotext', '-f', str(page), '-l', str(page), pdf, '-'], capture_output=True, text=True,
                          encoding='utf-8', errors='ignore').stdout
    if title in norm(re.sub(r'[`\'"]', '', text)):
        print('paper-pagecheck: OK, "%s" prints on page %d, as the contents says' % (title, page))
        return 0
    print('paper-pagecheck: FAILED, the contents puts "%s" on page %d, but it does not print there (rebuild with one more pass)'
          % (title, page))
    return 1

if __name__ == '__main__':
    sys.exit(main())
