#!/usr/bin/env python3
"""skeleton.py CHAPTER.tex [GIT_REF]  (default GIT_REF: blueprint)

Compare the graph skeleton of a chapter's working file with a committed version. A readability edit
must leave the skeleton IDENTICAL: same nodes in the same order, same environment, \\label, \\lean list,
\\leanok flags, \\uses lists (statement and proof), and the same node furniture -- \\contrib value,
\\srcloc pointers, \\axfoot text, and a \\thesisref wherever there was one. No \\label may be lost.
Also reports house-style violations: \\reviewnote (review material lives in review-data/), mentions of
client projects, non-ASCII characters, unescaped underscores, nested proofs, \\multirow.
Run from anywhere inside the repository."""
import os, re, subprocess, sys
KINDS = 'definition|lemma|proposition|theorem|corollary|example'
node_re = re.compile(r'\\begin\{(%s)\}(.*?)\\end\{\1\}' % KINDS, re.S)
proof_re = re.compile(r'\\begin\{proof\}(.*?)\\end\{proof\}', re.S)
import codecs
# Names of client projects are kept out of clear text on purpose (rot13): the blueprint never names them.
BANNED = re.compile(codecs.decode(r'ynzoqn-?obk|crertevar', 'rot13') + r'|\berasure\b|\beraser\b|downstream', re.I)
def items(mac, t):
    out = []
    for m in re.finditer(r'\\%s\{([^}]*)\}' % mac, t, re.S):
        out += [x.strip() for x in m.group(1).replace('\n', ' ').split(',') if x.strip()]
    return out
def skel(txt):
    txt = re.sub(r'(?<!\\)%.*', '', txt)
    ev = [(m.start(), 'n', m) for m in node_re.finditer(txt)] + [(m.start(), 'p', m) for m in proof_re.finditer(txt)]
    nodes, last = [], None
    for pos, k, m in sorted(ev, key=lambda e: e[0]):
        if k == 'n':
            b = m.group(2); lab = re.findall(r'\\label\{([^}]*)\}', b)
            last = dict(kind=m.group(1), label=lab[0] if lab else None, lean=items('lean', b),
                        leanok=bool(re.search(r'\\leanok\b', b)), uses=sorted(items('uses', b)), proof=None,
                        contrib=re.findall(r'\\contrib\{([^}]*)\}', b),
                        srcloc=sorted(re.findall(r'\\srcloc\{([^}]*)\}\{([^}]*)\}', b)),
                        axfoot=[' '.join(x.split()) for x in re.findall(r'\\axfoot\{([^}]*)\}', b)],
                        thesisref=bool(re.search(r'\\thesisref\{', b)), nested='\\begin{proof}' in b)
            nodes.append(last)
        elif last is not None:
            b = m.group(1)
            last['proof'] = dict(leanok=bool(re.search(r'\\leanok\b', b)), uses=sorted(items('uses', b)),
                                 axfoot=[' '.join(x.split()) for x in re.findall(r'\\axfoot\{([^}]*)\}', b)])
    return nodes, sorted(set(re.findall(r'\\label\{([^}]*)\}', txt)))
path = os.path.abspath(sys.argv[1]); ref = sys.argv[2] if len(sys.argv) > 2 else 'blueprint'
top = subprocess.run(['git', 'rev-parse', '--show-toplevel'], capture_output=True, text=True, cwd=os.path.dirname(path)).stdout.strip()
old = subprocess.run(['git', 'show', f'{ref}:{os.path.relpath(path, top)}'], capture_output=True, text=True, cwd=top).stdout
new = open(path, encoding='utf-8').read()
on, ol = skel(old); nn, nl = skel(new); bad = 0
if [n['label'] for n in on] != [n['label'] for n in nn]:
    print('NODE SEQUENCE DIFFERS'); bad += 1
    print('  missing:', [n['label'] for n in on if n['label'] not in [x['label'] for x in nn]])
    print('  added  :', [n['label'] for n in nn if n['label'] not in [x['label'] for x in on]])
om = {n['label']: n for n in on}
for n in nn:
    o = om.get(n['label'])
    if not o: continue
    for k in ('kind', 'lean', 'leanok', 'uses', 'proof', 'contrib', 'srcloc', 'axfoot'):
        if o[k] != n[k]: print(f"{n['label']}: {k} changed\n   old={o[k]}\n   new={n[k]}"); bad += 1
    if o['thesisref'] and not n['thesisref']: print(f"{n['label']}: \\thesisref lost"); bad += 1
    if n['nested']: print(f"{n['label']}: proof nested inside the statement environment"); bad += 1
lost = [l for l in ol if l not in nl]
if lost: print('LABELS LOST:', lost); bad += 1
for i, l in enumerate(new.split('\n'), 1):
    if any(ord(c) > 127 for c in re.sub(r'\\(lean|axfoot)\{[^}]*\}', '', l)): print(f'L{i}: non-ASCII character'); bad += 1
    for m in re.finditer(r'\\texttt\{([^{}]*)\}', l):
        if re.search(r'(?<!\\)_', m.group(1)): print(f'L{i}: unescaped underscore in {m.group(0)[:50]}'); bad += 1
    if '\\reviewnote' in l: print(f'L{i}: \\reviewnote (move review material out of the chapter)'); bad += 1
    if '\\multirow' in l: print(f'L{i}: \\multirow has no plasTeX shim'); bad += 1
    m = BANNED.search(re.sub(r'\\(lean|label|uses|ref|srcloc)\{[^}]*\}(\{[^}]*\})?', '', l))
    if m: print(f'L{i}: mentions a client project or review framing: "{m.group(0)}"'); bad += 1
if new.count('\\begin{') != new.count('\\end{'): print('UNBALANCED begin/end'); bad += 1
ow, nw = len(old.split()), len(new.split())
print(f'words: {ow} -> {nw} ({100 * nw // max(ow, 1)}%)   nodes: {len(on)} -> {len(nn)}   '
      f'lists: {len(re.findall(r"begin.(itemize|enumerate|description)", new))}   tables: {new.count("begin{tabular}")}')
print('SKELETON OK' if not bad else f'SKELETON BROKEN: {bad} problem(s)')
sys.exit(1 if bad else 0)
