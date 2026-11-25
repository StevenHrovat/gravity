#!/usr/bin/env python3
"""Build the paper as one LaTeX document from docs/paper/draft/*.md, with one bibliography.

  python tools/paper-latex.py            Draft 4 (docs/paper, the merged state): writes docs/paper/latex/guid-v8.tex
  python tools/paper-latex.py D5         a later draft DN (docs/paper/DN, from the draft before it): writes
                                         docs/paper/DN/latex/guid-v8-DN.tex
  (then, in that latex folder:  pdflatex <name>.tex  twice)

Drafts are additive: Draft 4 stays as merged in docs/paper, and every later draft N lives whole in docs/paper/DN.

The Markdown of the drafts is a small subset (headings, paragraphs, lists, pipe tables, block quotes, bold, italic, code spans,
links); this converts exactly that subset. The bibliography is collected from the Source column of every classical and external
row of CLAIMS.md (entries that name a year or an arXiv number), de-duplicated, as cited in the project notes; checking each entry
against its publisher is task R of the final verification (docs/paper/REVIEW.md).
"""
import glob, io, os, re, sys

DRAFT = sys.argv[1] if len(sys.argv) > 1 else ''   # '' = Draft 4 in docs/paper; 'D5' = docs/paper/D5, and so on
if DRAFT and not re.fullmatch(r'D[5-9]|D[1-9][0-9]+', DRAFT):
    raise SystemExit('usage: tools/paper-latex.py [DN]   (N >= 5; no argument builds Draft 4 in docs/paper)')
PAPER = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'docs', 'paper')
ROOT = os.path.join(PAPER, DRAFT) if DRAFT else PAPER
OUT = os.path.join(ROOT, 'latex')
NAME = 'guid-v8-' + DRAFT if DRAFT else 'guid-v8'
STATUS = 'Draft ' + DRAFT[1:] if DRAFT else 'Merged at Draft 4'
REL = 'docs/paper/' + DRAFT + '/' if DRAFT else 'docs/paper/'

SPECIAL = {'\\': r'\textbackslash{}', '&': r'\&', '%': r'\%', '$': r'\$', '#': r'\#', '_': r'\_', '{': r'\{', '}': r'\}',
           '~': r'\textasciitilde{}', '^': r'\textasciicircum{}', '<': r'\textless{}', '>': r'\textgreater{}', '|': r'\textbar{}'}

GREEK = dict(zip('αβγδεζηθικλμνξπρστφχψωΓΔΘΛΞΠΣΦΨΩ',
                 ['alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta', 'eta', 'theta', 'iota', 'kappa', 'lambda', 'mu', 'nu', 'xi',
                  'pi', 'rho', 'sigma', 'tau', 'phi', 'chi', 'psi', 'omega', 'Gamma', 'Delta', 'Theta', 'Lambda', 'Xi', 'Pi',
                  'Sigma', 'Phi', 'Psi', 'Omega']))

def esc(t):
    return ''.join(SPECIAL.get(ch, ch) for ch in t)

# The sources transliterate umlauts and drop accents (repository rule); the typeset text restores them. Whole words only, and never
# inside code spans or URLs (those are held as placeholders while this runs).
TYPESET = [('Goettingen', 'G\\"ottingen'), ('Lueck', 'L\\"uck'), ('Mueller', 'M\\"uller'), ('Goedel', 'G\\"odel'),
           ('Godel', 'G\\"odel'), ('Luescher', 'L\\"uscher'), ('Fuerstenau', 'F\\"urstenau'), ('Juergen', 'J\\"urgen'),
           ('Kaehler', 'K\\"ahler'), ('Hyperkaehler', 'Hyperk\\"ahler'), ('Kroencke', 'Kr\\"oncke'), ('Ueber', '\\"Uber'),
           ('Saetze', 'S\\"atze'), ('fuer', 'f\\"ur'), ('Vollstaendigkeit', 'Vollst\\"andigkeit'), ('ueber', '\\"uber'),
           ('Bemerkung', 'Bemerkung'), ('Szego', 'Szeg\\H{o}'), ('Erdos', 'Erd\\H{o}s'), ('Lovasz', 'Lov\\\'asz'),
           ('Poincare', 'Poincar\\\'e'), ('Caratheodory', 'Carath\\\'eodory'), ('Fejer', 'Fej\\\'er'),
           ('Necas', 'Ne\\v{c}as'), ('Ruzicka', 'R\\r{u}\\v{z}i\\v{c}ka'), ('Sverak', '\\v{S}ver\\\'ak'),
           ('Kollar', 'Koll\\\'ar'), ('Andre', 'Andr\\\'e'), ('Asterisque', 'Ast\\\'erisque'), ('Alpoge', 'Alp\\"oge')]
TYPESET_RE = [(re.compile(r'\b%s\b' % a), b) for a, b in TYPESET if a != b]

def breakable(t):
    """Allow line breaks in long code spans (file paths, Lean names) after a slash, a dot or an underscore."""
    if len(t) < 12:
        return t
    return re.sub(r'(/|\.|\\_)', lambda m: m.group(1) + r'\allowbreak{}', t)

# Mathematics: the sources write formulas in plain ASCII (x^y, F_e, mu_4, <=, sqrt 2); the typeset text sets them in math mode.
# Conservative patterns only; code spans and links are held as placeholders while this runs, so they are never touched.
GREEK_WORDS = ['alpha', 'beta', 'gamma', 'delta', 'epsilon', 'eps', 'theta', 'kappa', 'lambda', 'mu', 'nu', 'xi', 'pi', 'rho',
               'sigma', 'tau', 'phi', 'chi', 'psi', 'omega', 'eta', 'Gamma', 'Delta', 'Theta', 'Lambda', 'Sigma', 'Phi', 'Psi',
               'Omega']
BS = chr(92)  # a backslash, kept out of string literals so that no escaping layer can eat it
GREEK_TEX = {w: (BS + 'varepsilon' if w in ('eps', 'epsilon') else BS + w) for w in GREEK_WORDS}
GW = '|'.join(sorted(GREEK_WORDS + ['zeta'], key=len, reverse=True))
ATT = r'(?:\{[^{}\s]{1,24}\}|\([^()]{1,16}\)|-?[A-Za-z0-9.*]{1,8})'
BASE = r'(?:' + GW + r'|[A-Za-z]{1,2}|\d+(?:\.\d+)?)'
TOKEN = re.compile(r'(?<![\w' + BS + BS + r'])(' + BASE + r')((?:[_^]' + ATT + r')+)(?![\w])')

def mathify_inner(x):
    x = re.sub(r'\b(' + GW + r')\b', lambda m: BS + 'zeta ' if m.group(1) == 'zeta' else GREEK_TEX[m.group(1)] + ' ', x)
    x = x.replace('sqrt', BS + 'sqrt ').replace('*', BS + 'ast ')
    return x.strip()

def math_token(m):
    base, rest = m.group(1), m.group(2)
    out = mathify_inner(base)
    for op, arg in re.findall(r'([_^])(' + ATT + r')', rest):
        if arg.startswith('(') or arg.startswith('{'):
            arg = arg[1:-1]
        out += op + '{' + mathify_inner(arg) + '}'
    return '$' + out + '$'

def inner_math(x):
    """A short formula inside abs(...) or sqrt(...), as math without dollars."""
    x = TOKEN.sub(lambda m: math_token(m)[1:-1], x)
    return re.sub(r'(?<!' + BS + BS + r')\b(' + GW + r')\b',
                  lambda m: (BS + 'zeta ' if m.group(1) == 'zeta' else GREEK_TEX[m.group(1)] + ' '), x).strip()

def mathify(t, hold):
    """Turn the formula tokens of a line into held TeX math (returns the line with placeholders)."""
    t = re.sub(r'\babs\(([^()]{1,12})\)', lambda m: hold('$|' + inner_math(m.group(1)) + '|$'), t)
    t = re.sub(r'\bsqrt ?(\d+|\(([^()]{1,20})\))', lambda m: hold('$' + BS + 'sqrt{' + inner_math(m.group(2) or m.group(1)) + '}$'), t)
    t = TOKEN.sub(lambda m: hold(math_token(m)), t)
    t = re.sub(r'(?<=[\w)]) <-> (?=\w)', lambda m: ' ' + hold('$' + BS + 'leftrightarrow$') + ' ', t)
    t = re.sub(r'(?<=[\w)\]]) -> (?=[\w(])', lambda m: ' ' + hold('$' + BS + 'to$') + ' ', t)
    for a, b in (('<=', BS + 'le'), ('>=', BS + 'ge'), ('!=', BS + 'ne'), ('<', '<'), ('>', '>')):
        t = re.sub(r'(?<=[\w)\]}\x00]) ' + re.escape(a) + r' (?=[-\w(\x00])', lambda m, b=b: ' ' + hold('$' + b + '$') + ' ', t)
    t = re.sub(r'(?<=\)) x (?=(?:SU|U|SO|Sp|GL|Z)\b)', lambda m: ' ' + hold('$' + BS + 'times$') + ' ', t)
    t = re.sub(r'(?<=[\d)]) \? (?=\d|SU\()', lambda m: ' ' + hold('$' + BS + 'stackrel{?}{=}$') + ' ', t)
    t = re.sub(r'(?<![\w' + BS + BS + r'])(' + '|'.join(sorted(GREEK_WORDS, key=len, reverse=True)) + r')(?![\w])',
               lambda m: hold('$' + GREEK_TEX[m.group(1)] + '$'), t)
    return t

def typeset_names(t):
    for r, b in TYPESET_RE:
        t = r.sub(lambda m, b=b: b, t)
    return t

def inline(t):
    """Escape and convert inline Markdown: code spans and links become placeholders first, so that bold and italic can span
    them; straight double quotes become TeX quotes."""
    held = []
    def hold(s):
        held.append(s)
        return '\x00%d\x00' % (len(held) - 1)
    t = re.sub(r'`([^`]*)`', lambda m: hold(r'\texttt{' + breakable(esc(m.group(1))) + '}'), t)
    # TeX mathematics written in the source: $$...$$ is a displayed formula, $...$ an inline one; both are passed through
    t = re.sub(r'\$\$(.+?)\$\$', lambda m: hold(r'\[' + m.group(1) + r'\]'), t)
    t = re.sub(r'\$([^$]+)\$', lambda m: hold('$' + m.group(1) + '$'), t)
    t = re.sub(r'\[([^\]]*)\]\(([^)]*)\)',
               lambda m: hold(r'\href{' + m.group(2).replace('%', r'\%').replace('#', r'\#') + '}{' + emph(esc(m.group(1))) + '}'), t)
    t = mathify(t, hold)
    t = cite_links(t, hold)
    t = label_links(t, hold)
    t = emph(esc(t))
    t = typeset_names(re.sub(r'"([^"\x00]*)"', r"``\1''", t))
    t = ''.join(('\\ensuremath{\\%s}' % GREEK[ch]) if ch in GREEK else ch for ch in t)
    for _ in range(4):  # held pieces may hold others (a formula inside abs(...)); restore until none is left
        t = re.sub('\x00(\\d+)\x00', lambda m: held[int(m.group(1))], t)
    return t

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

REPO_URL = 'https://github.com/StevenHrovat/gravity'
COMMIT = ['unknown']
LEDGER = ['']
LEDGER_IDS, HEADING_IDS = set(), set()
LABEL_RE = re.compile(r'(?<![\w./-])((?:XI|IX|X|VIII|VII|VI|IV|V|III|II|I|A|R|T)\.\d+(?:\.\d+)*[a-z]?)(?![\w])')

def source_commit():
    """The commit the sources are built from (the PDF itself is committed after it)."""
    import subprocess
    try:
        return subprocess.run(['git', '-C', ROOT, 'rev-parse', '--short', 'HEAD'], capture_output=True, text=True,
                              check=True).stdout.strip()
    except Exception:
        return 'unknown'

def build_label_sets(files):
    """Section numbers (headings of the drafts) and claim labels (rows of the ledger)."""
    for f in files:
        HEADING_IDS.update(re.findall(r'(?m)^#{2,3} ([IVXART]+\.\d+(?:\.\d+)*)', io.open(f, encoding='utf-8').read()))
    c = io.open(os.path.join(ROOT, 'CLAIMS.md'), encoding='utf-8').read()
    c = c[:c.index('## Draft 3 labels')]
    LEDGER_IDS.update(re.findall(r'(?m)^\| ([IVXART]+\.[^ |]+) \| ', c))

def label_links(t, hold):
    """A claim label that is not also a section number links to the ledger, where its row says what checks it."""
    if not CITING[0] or not LEDGER[0]:
        return t
    def f(m):
        lab = m.group(1)
        if lab in LEDGER_IDS and lab not in HEADING_IDS:
            return hold(r'\href{' + LEDGER[0] + '}{' + lab + '}')
        return lab
    return LABEL_RE.sub(f, t)

CITES = []  # (regex, number): author-year citations in the text, linked to their bibliography entry
CITING = [True]

KEY_RE = re.compile(r"^[A-Z][A-Za-z'\-]+(?:[- ](?:and )?[A-Z][A-Za-z'\-]+)*(?: et al\.)? \d{4}[a-z]?$")

def build_cites(rows):
    """From the 'cited as' column: every key of the form 'Name 1997' or 'Name-Other 1997' becomes a link to its entry number;
    the text may write it 'Name 1997' or 'Name (1997)'. A key that names two entries links to neither."""
    seen = {}
    for num, cite in rows:
        for piece in cite.split(';'):
            key = re.sub(r'\(.*?\)', '', piece).strip().rstrip(',.')
            if KEY_RE.match(key):
                seen.setdefault(key, set()).add(num)
    CITES.clear()
    for key in sorted(seen, key=len, reverse=True):
        if len(seen[key]) != 1:
            continue
        name, year = key.rsplit(' ', 1)
        pat = re.compile(r'(?<![\w-])(' + re.escape(name) + r'(?: \(' + re.escape(year) + r'\)| ' + re.escape(year) + r'))(?![\w-])')
        CITES.append((pat, next(iter(seen[key]))))

def cite_links(t, hold):
    if not CITING[0]:
        return t
    for pat, n in CITES:
        t = pat.sub(lambda m, n=n: m.group(1) + hold(r'\,\hyperlink{bib%d}{[%d]}' % (n, n)), t)
    return t

def bib_rows():
    p = os.path.join(ROOT, 'references.md')
    if not os.path.exists(p):
        return None
    rows = []
    for line in io.open(p, encoding='utf-8').read().splitlines():
        if not line.startswith('| ') or line.startswith('| #') or line.startswith('|---'):
            continue
        c = [x.strip() for x in line.strip().strip('|').split('|')]
        if len(c) < 7 or c[5] == 'not identified':
            continue
        rows.append((clean_bib(c[1]), clean_bib(c[2]), clean_bib(c[3]), bib_link(c[4]), c[5], c[6]))
    def surname(a):
        first = re.split(r'[;,]| and ', a)[0].strip()
        first = re.sub(r'\(.*?\)', '', first).strip()
        toks = [x for x in first.split() if not x.isdigit()]
        return (toks[-1] if toks else a).lower()
    rows.sort(key=lambda r: (surname(r[0]), r[2]))
    return rows

def bibliography_checked():
    """The bibliography from docs/paper/references.md (one table row per work, each checked against the page named), if it exists."""
    rows = bib_rows()
    if rows is None:
        return None
    CITING[0] = False
    body = ['\\section*{References}', '\\addcontentsline{toc}{section}{References}', '',
            '{\\sloppy', '\\begin{enumerate}[label={[\\arabic*]},leftmargin=2.5em,itemsep=1pt]']
    for k, (authors, title, venue, url, status, cite) in enumerate(rows, 1):
        t = inline(authors) + (', \\emph{' + inline(title) + '}' if title else '') + ', ' + inline(venue).rstrip('.') + '.'
        if url.startswith('doi:'):
            t += ' \\doi{' + url[4:].replace('%', '\\%').replace('#', '\\#') + '}'
        elif url:
            t += ' \\url{' + url.replace('%', '\\%').replace('#', '\\#') + '}'
        body.append('\\item\\hypertarget{bib%d}{}' % k + t)
    body.append('\\end{enumerate}}')
    CITING[0] = True
    return '\n'.join(body), len(rows)

def bibliography_checked_old():
    p = os.path.join(ROOT, 'references.md')
    if not os.path.exists(p):
        return None
    rows = []
    for line in io.open(p, encoding='utf-8').read().splitlines():
        if not line.startswith('| ') or line.startswith('| #') or line.startswith('|---'):
            continue
        c = [x.strip() for x in line.strip().strip('|').split('|')]
        if len(c) < 7:
            continue
        n, authors, title, venue, url, status = c[0], c[1], c[2], c[3], c[4], c[5]
        if status == 'not identified':
            continue
        rows.append((clean_bib(authors), clean_bib(title), clean_bib(venue), bib_link(url), status))
    def surname(a):
        first = re.split(r'[;,]| and ', a)[0].strip()
        first = re.sub(r'\(.*?\)', '', first).strip()
        toks = [x for x in first.split() if not x.isdigit()]
        return (toks[-1] if toks else a).lower()
    rows.sort(key=lambda r: (surname(r[0]), r[2]))
    body = ['\\section*{References}', '\\addcontentsline{toc}{section}{References}', '',
            '{\\sloppy', '\\begin{enumerate}[label={[\\arabic*]},leftmargin=2.5em,itemsep=1pt]']
    for authors, title, venue, url, status in rows:
        t = inline(authors) + ', \\emph{' + inline(title) + '}, ' + inline(venue).rstrip('.') + '.'
        if url.startswith('doi:'):
            t += ' \\doi{' + url[4:].replace('%', '\\%').replace('#', '\\#') + '}'
        elif url:
            t += ' \\url{' + url.replace('%', '\\%').replace('#', '\\#') + '}'
        body.append('\\item ' + t)
    body.append('\\end{enumerate}}')
    return '\n'.join(body), len(rows)

# Working remarks in references.md (what page was read, what could not be confirmed) stay there; the typeset entry drops them.
REMARK = re.compile(r'\s*\((?=[^()]*\b(page|read|record|snippet|search|listed|given|confirmed|settled|submitter|request|Crossref|'
                    r'fetched|shown|displays|as printed|not in|from a|one source|the PDF|abstract|full text|seen|initials|pinned|'
                    r'catalogue|as cited|index(?:ed)?|unconfirmed|not identified|reference list|credited)\b)[^()]*\)', re.I)
REMARK_CLAUSE = re.compile(r'[;.]\s*[^;.|]*\b(read|not seen|search|snippet|record|pinned|initials|catalogue|not confirmed|no year|'
                           r'as cited|is printed|was not identified|not the \d{4})\b[^;|]*(?=;|$)', re.I)

def clean_bib(t):
    t = REMARK.sub('', t)
    t = REMARK_CLAUSE.sub('', t)
    t = re.sub(r';\s*(the page|as read|DOI) [^;]*$', '', t)
    return re.sub(r'\s{2,}', ' ', t).strip().rstrip(';,. ')

def bib_link(url):
    """A stable link for the typeset entry: a Crossref record becomes its DOI, typeset by the `doi` package ('doi:' prefix);
    arXiv and record pages are kept; search queries, API answers and encyclopaedia pages are dropped. The converter reaches no
    host itself; it only writes links."""
    url = (url.split() or [''])[0].strip()
    m = re.match(r'https?://api\.crossref\.org/works/(10\.[^?\s]+)$', url)
    if m:
        return 'doi:' + m.group(1)
    if not url.startswith('http') or 'wikipedia.org' in url or '/api/' in url or 'api.crossref.org' in url or 'rechercher.do' in url:
        return ''
    return url

def bibliography():
    checked = bibliography_checked()
    if checked:
        return checked
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
%% Build: pdflatex BUILDNAME.tex (twice). Licence: Apache License 2.0.
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
\usepackage{xurl}
\usepackage{doi}
\newunicodechar{Δ}{\ensuremath{\Delta}}
\newunicodechar{Φ}{\ensuremath{\Phi}}
\newunicodechar{ℓ}{\ensuremath{\ell}}
\setlength{\emergencystretch}{6em}
\setlength{\parindent}{0pt}
\setlength{\parskip}{0.5ex}
\setcounter{tocdepth}{2}
\title{Grand Unified Information Duality v8\\[0.6ex]
\large The Millennium Prize Problem type as seen through DMP, with certified settling}
\author{Steven Hrovat\\[0.3ex] {\normalsize with Claude (Anthropic) during pressing}}
\hypersetup{pdftitle={Grand Unified Information Duality v8: The Millennium Prize Problem type as seen through DMP, with certified settling},
  pdfauthor={Steven Hrovat}}
\date{%s, %s\\[0.6ex]\small Source, ledger and reproduction: \url{%s}, built from commit \texttt{%s}}
\begin{document}
\maketitle
\begin{center}\small\emph{Draft. No Millennium Prize problem is solved here; results that use the one assumption are marked
conditional on it.}\end{center}
\tableofcontents
\clearpage
"""

ANY_RAW = False

def main():
    os.makedirs(OUT, exist_ok=True)
    files = sorted(glob.glob(os.path.join(ROOT, 'draft', '[0-9][0-9]-*.md')))
    COMMIT[0] = source_commit()
    LEDGER[0] = REPO_URL + '/blob/' + COMMIT[0] + '/' + REL + 'CLAIMS.md'
    build_label_sets(files)
    rows = bib_rows()
    if rows:
        build_cites([(k, r[5]) for k, r in enumerate(rows, 1)])
    parts = []
    for f in files:
        md = io.open(f, encoding='utf-8').read()
        if os.path.basename(f).startswith('00-'):
            md = re.sub(r'\A# [^\n]*\n', '', md)  # the title line becomes \title
        # the italic editors' note right under a chapter's first heading is for the repository, not the typeset paper
        md = re.sub(r'\A((?:# [^\n]*\n)?\s*)\*[^\n][\s\S]*?\*\n(?=\n)', r'\1', md, count=1)
        # A LaTeX block kept in an HTML comment (invisible in the Markdown view) passes into the typeset paper verbatim:
        # <!-- latex ... --> on lines of its own.
        raw = []
        global ANY_RAW
        def keep(m):
            raw.append(m.group(1))
            return '\n\nRAWLATEXBLOCK%d\n\n' % (len(raw) - 1)
        md = re.sub(r'<!-- latex\n(.*?)\n-->', keep, md, flags=re.S)
        ANY_RAW = ANY_RAW or bool(raw)
        body = convert(md)
        for n, block in enumerate(raw):
            body = body.replace('RAWLATEXBLOCK%d' % n, block)
        parts.append('%% ---- ' + os.path.basename(f) + '\n' + body)
    bib, n = bibliography()
    import datetime
    tex = PREAMBLE % (STATUS, datetime.date.today().isoformat(), REPO_URL, COMMIT[0]) + '\n\n'.join(parts) + '\n\n\\clearpage\n' + bib + '\n\\end{document}\n'
    tex = tex.replace('BUILDNAME', NAME, 1)
    if ANY_RAW:  # TikZ only when a raw LaTeX block is present, so a draft without one builds as before
        tex = tex.replace('\\usepackage{doi}', '\\usepackage{doi}\n\\usepackage{tikz}\n\\usetikzlibrary{decorations.pathreplacing}', 1)
    io.open(os.path.join(OUT, NAME + '.tex'), 'w', encoding='utf-8', newline='\n').write(tex)
    print('wrote %s.tex: %d chapters, %d references' % (NAME, len(files), n))

if __name__ == '__main__':
    main()
