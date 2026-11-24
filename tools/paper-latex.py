#!/usr/bin/env python3
"""Build the paper as one LaTeX document from docs/paper/draft/*.md, with one bibliography.

  python tools/paper-latex.py            writes docs/paper/latex/guid-v8.tex and docs/paper/latex/references.tex
  (then, in docs/paper/latex:  pdflatex guid-v8.tex  twice)

The Markdown of the drafts is a small subset (headings, paragraphs, lists, pipe tables, block quotes, bold, italic, code spans,
links); this converts exactly that subset. The bibliography is collected from the Source column of every classical and external
row of CLAIMS.md (entries that name a year or an arXiv number), de-duplicated, as cited in the project notes; checking each entry
against its publisher is task R of the final verification (docs/paper/REVIEW.md).
"""
import glob, io, os, re

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'docs', 'paper')
OUT = os.path.join(ROOT, 'latex')

SPECIAL = {'\\': r'\textbackslash{}', '&': r'\&', '%': r'\%', '$': r'\$', '#': r'\#', '_': r'\_', '{': r'\{', '}': r'\}',
           '~': r'\textasciitilde{}', '^': r'\textasciicircum{}', '<': r'\textless{}', '>': r'\textgreater{}', '|': r'\textbar{}'}

def esc(t):
    return ''.join(SPECIAL.get(ch, ch) for ch in t)

def inline(t):
    """Escape and convert inline Markdown: code spans and links become placeholders first, so that bold and italic can span
    them; straight double quotes become TeX quotes."""
    held = []
    def hold(s):
        held.append(s)
        return '\x00%d\x00' % (len(held) - 1)
    t = re.sub(r'`([^`]*)`', lambda m: hold(r'\texttt{' + esc(m.group(1)) + '}'), t)
    t = re.sub(r'\[([^\]]*)\]\(([^)]*)\)',
               lambda m: hold(r'\href{' + m.group(2).replace('%', r'\%').replace('#', r'\#') + '}{' + emph(esc(m.group(1))) + '}'), t)
    t = emph(esc(t))
    t = re.sub(r'"([^"\x00]*)"', r"``\1''", t)
    return re.sub('\x00(\\d+)\x00', lambda m: held[int(m.group(1))], t)

def emph(t):
    t = re.sub(r'\*\*(.+?)\*\*', r'\\textbf{\1}', t)
    t = re.sub(r'(?<![\w*])\*(?!\s)(.+?)(?<!\s)\*(?![\w*])', r'\\emph{\1}', t)
    return t

def table(rows):
    cells = [[c.strip() for c in r.strip().strip('|').split('|')] for r in rows]
    cells = [c for c in cells if not all(re.fullmatch(r':?-{3,}:?', x) for x in c)]
    n = max(len(c) for c in cells)
    # column widths by content: the mean length of each column, square-rooted so long columns do not take everything
    lens = [sum(len(c[j]) if j < len(c) else 0 for c in cells) / len(cells) for j in range(n)]
    wts = [max(l, 4) ** 0.5 for l in lens]
    ws = [0.98 * x / sum(wts) for x in wts]
    spec = ''.join(r'>{\raggedright\arraybackslash}p{\dimexpr %.4f\linewidth-2\tabcolsep\relax}' % w for w in ws)
    out = [r'{\footnotesize', r'\begin{longtable}{' + spec + '}', r'\toprule']
    for k, c in enumerate(cells):
        c = c + [''] * (n - len(c))
        row = ' & '.join((r'\textbf{' + inline(x) + '}') if k == 0 else inline(x) for x in c) + r' \\'
        out.append(row)
        if k == 0:
            out += [r'\midrule', r'\endhead']
    out += [r'\bottomrule', r'\end{longtable}}']
    return '\n'.join(out)

def heading(level, text):
    cmd = {1: 'section', 2: 'subsection', 3: 'subsubsection'}.get(level, 'paragraph')
    t = inline(text)
    toc = {1: 'section', 2: 'subsection', 3: 'subsubsection'}.get(level)
    s = '\\%s*{%s}' % (cmd, t)
    if toc:
        s += '\n\\addcontentsline{toc}{%s}{%s}' % (toc, t)
    return s

def convert(md):
    lines = md.split('\n')
    out, i, para = [], 0, []
    stack = []  # list environments: (kind, indent)
    def flush_para():
        if para:
            out.append(inline(' '.join(x.strip() for x in para)))
            out.append('')
            para.clear()
    def close_lists(to_indent=-1):
        while stack and stack[-1][1] > to_indent:
            out.append('\\end{%s}' % stack.pop()[0])
    while i < len(lines):
        ln = lines[i]
        if not ln.strip():
            flush_para(); i += 1
            # a blank line ends lists unless the next line continues them
            nxt = lines[i] if i < len(lines) else ''
            if stack and not re.match(r'\s*([*-]|\d+\.)\s', nxt) and not (nxt.startswith('  ') and nxt.strip()):
                close_lists()
            continue
        m = re.match(r'(#{1,4}) (.*)', ln)
        if m:
            flush_para(); close_lists()
            out.append(heading(len(m.group(1)), m.group(2).strip()))
            out.append(''); i += 1; continue
        if ln.startswith('|'):
            flush_para(); close_lists()
            rows = []
            while i < len(lines) and lines[i].startswith('|'):
                rows.append(lines[i]); i += 1
            out.append(table(rows)); out.append(''); continue
        if ln.startswith('>'):
            flush_para(); close_lists()
            q = []
            while i < len(lines) and lines[i].startswith('>'):
                q.append(lines[i][1:].strip()); i += 1
            out.append('\\begin{quote}\n' + inline(' '.join(q)) + '\n\\end{quote}'); out.append(''); continue
        if ln.strip() == '---':
            flush_para(); close_lists()
            out.append('\\medskip\\noindent\\rule{\\linewidth}{0.4pt}\\medskip'); out.append(''); i += 1; continue
        m = re.match(r'(\s*)([*-]|\d+\.)\s+(.*)', ln)
        if m:
            flush_para()
            ind = len(m.group(1)); kind = 'enumerate' if m.group(2)[0].isdigit() else 'itemize'
            close_lists(ind)
            if not stack or stack[-1][1] < ind:
                out.append('\\begin{%s}' % kind); stack.append((kind, ind))
            item = [m.group(3)]; i += 1
            while i < len(lines) and lines[i].strip() and not re.match(r'\s*([*-]|\d+\.)\s', lines[i]) \
                    and lines[i].startswith(' ' * (ind + 2)):
                item.append(lines[i].strip()); i += 1
            out.append('\\item ' + inline(' '.join(item)))
            continue
        if stack and ln.startswith('  '):
            out[-1] += ' ' + inline(ln.strip()); i += 1; continue
        close_lists()
        para.append(ln); i += 1
    flush_para(); close_lists()
    return '\n'.join(out)

def bibliography():
    s = io.open(os.path.join(ROOT, 'CLAIMS.md'), encoding='utf-8').read()
    s = s[:s.index('## Draft 3 labels')]
    seen, items = set(), []
    for line in s.splitlines():
        if not re.match(r'\| [0-9IVXA]+\.\S* \| ', line):
            continue
        cells = [c.strip() for c in line.strip().strip('|').split('|')]
        if len(cells) < 5 or not re.match(r'(classical|external)', cells[2]):
            continue
        for src in re.split(r';', cells[3]):
            src = src.strip().rstrip('.')
            if src.count(')') > src.count('('):
                src = src.rstrip(')')
            if '`' in src or not src:
                continue
            if not (re.search(r'\b(1[89]\d\d|20\d\d)\b', src) or 'arXiv' in src):
                continue
            key = re.sub(r'\W+', '', re.sub(r'\((recalled|read)[^)]*\)', '', src.lower()))
            if key in seen:
                continue
            seen.add(key); items.append(src)
    items.sort(key=lambda x: x.lower())
    body = ['\\section*{Citation index}', '\\addcontentsline{toc}{section}{Citation index}', '',
            '\\noindent{\\small Every literature source the claims ledger cites for a classical or external row, as the project notes '
            'cite it (author and year, or an arXiv number), collected by script. This is the index the bibliography is built from: '
            'full entries (authors, title, venue, year, checked against the publisher or arXiv page) replace it before the final '
            'verification (review process, stage 3).}', '', '\\begin{enumerate}[label={[\\arabic*]},leftmargin=2.5em,itemsep=1pt]']
    body += ['\\item ' + inline(x) for x in items]
    body.append('\\end{enumerate}')
    return '\n'.join(body), len(items)

PREAMBLE = r"""%% GUID v8, generated by tools/paper-latex.py from docs/paper/draft/*.md. Do not edit by hand: edit the drafts and rebuild.
%% Build: pdflatex guid-v8.tex (twice). Licence: Apache License 2.0.
\documentclass[10pt,a4paper]{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{lmodern}
\usepackage[margin=2.2cm]{geometry}
\usepackage{amsmath,amssymb}
\usepackage{booktabs,longtable,array}
\usepackage{enumitem}
\usepackage{newunicodechar}
\usepackage[hidelinks]{hyperref}
\usepackage{url}
\newunicodechar{Δ}{\ensuremath{\Delta}}
\newunicodechar{Φ}{\ensuremath{\Phi}}
\newunicodechar{ℓ}{\ensuremath{\ell}}
\setlength{\emergencystretch}{3em}
\setlength{\parindent}{0pt}
\setlength{\parskip}{0.5ex}
\setcounter{tocdepth}{2}
\title{Grand Unified Information Duality v8\\[0.6ex]
\large The Millennium Prize Problem type as seen through DMP, with certified settling}
\author{Steven Hrovat \and Sirius (Claude Opus 5.5)}
\date{Draft 4, %s}
\begin{document}
\maketitle
\begin{center}\small\emph{Draft. No Millennium Prize problem is solved here; results that use the one assumption are marked
conditional on it.}\end{center}
\tableofcontents
\clearpage
"""

def main():
    os.makedirs(OUT, exist_ok=True)
    files = sorted(glob.glob(os.path.join(ROOT, 'draft', '[0-9][0-9]-*.md')))
    parts = []
    for f in files:
        md = io.open(f, encoding='utf-8').read()
        if os.path.basename(f).startswith('00-'):
            md = re.sub(r'\A# [^\n]*\n', '', md)  # the title line becomes \title
        # the italic editors' note right under a chapter's first heading is for the repository, not the typeset paper
        md = re.sub(r'\A((?:# [^\n]*\n)?\s*)\*[^\n][\s\S]*?\*\n(?=\n)', r'\1', md, count=1)
        parts.append('%% ---- ' + os.path.basename(f) + '\n' + convert(md))
    bib, n = bibliography()
    import datetime
    tex = PREAMBLE % datetime.date.today().isoformat() + '\n\n'.join(parts) + '\n\n\\clearpage\n' + bib + '\n\\end{document}\n'
    io.open(os.path.join(OUT, 'guid-v8.tex'), 'w', encoding='utf-8', newline='\n').write(tex)
    print('wrote guid-v8.tex: %d chapters, %d references' % (len(files), n))

if __name__ == '__main__':
    main()
