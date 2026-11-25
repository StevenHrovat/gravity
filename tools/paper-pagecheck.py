#!/usr/bin/env python3
"""Page check for a built paper: the table of contents printed in the PDF must point to the page where each heading prints.

  python tools/paper-pagecheck.py <file.pdf>

Reads the contents as printed in the PDF (lines ending in a page number, before the first page of the text), takes the part-level
entries ("Part ...", "Appendix ...", "Outlook ..."), picks the one in the middle, and checks with pdftotext that its heading prints
on the page the printed contents gives. It checks the PDF itself, not the .toc file: LaTeX prints the contents of the previous pass,
so a build with too few passes prints page numbers that are off by the length of the contents. Exit 0 when the page matches, 1 when
it does not, 2 when pdftotext is missing or no contents can be read.
"""
import re, shutil, subprocess, sys

def page_text(pdf, q, layout=False):
    args = ['pdftotext', '-f', str(q), '-l', str(q)] + (['-layout'] if layout else []) + [pdf, '-']
    return subprocess.run(args, capture_output=True, text=True, encoding='utf-8', errors='ignore').stdout

def norm(t):
    return re.sub(r'\s+', ' ', re.sub(r'[`\'"]', '', t)).strip()

def main():
    if len(sys.argv) not in (2, 3):   # a second argument (an old .toc path) is accepted and ignored
        raise SystemExit(__doc__)
    pdf = sys.argv[1]
    if not shutil.which('pdftotext'):
        print('paper-pagecheck: pdftotext not installed, page check skipped')
        return 2
    entries = []
    for q in range(1, 13):
        for line in page_text(pdf, q, layout=True).splitlines():
            m = re.match(r'\s*((?:Part [IVX]+\.|Appendix [A-Z]\.|Outlook\.).*?)\s*(?:\.\s*)*\s(\d+)\s*$', line)
            if m:
                entries.append((norm(m.group(1))[:24], int(m.group(2)), q))
    if not entries:
        print('paper-pagecheck: no printed contents found in', pdf)
        return 2
    title, page, _ = entries[len(entries) // 2]
    if title in norm(page_text(pdf, page)):
        print('paper-pagecheck: OK, "%s" prints on page %d, as the printed contents says' % (title, page))
        return 0
    where = [q for q in range(max(1, page - 8), page + 9) if title in norm(page_text(pdf, q))]
    print('paper-pagecheck: FAILED, the printed contents puts "%s" on page %d, but it prints on page(s) %s (build with one more pass)'
          % (title, page, where))
    return 1

if __name__ == '__main__':
    sys.exit(main())
