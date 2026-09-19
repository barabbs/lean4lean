#!/usr/bin/env python3
"""Usage: check_chapter.py <chapter.tex> [...]   — validates blueprint chapter files against the registry/census.
Exit 1 if any ERROR. Prints ERROR/WARN lines with file:line."""
import re,sys,os,json,glob,collections
ROOT=os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..'))
WORK=os.environ.get('BLUEPRINT_WORK') or os.path.join(ROOT,'.blueprint-work')
U=os.path.join(WORK,'understand')
BP=os.path.join(ROOT,'blueprint','src','chapters')
names=set(l.split('\t')[0] for l in open(U+'/all-constants.tsv') if l.strip())|set(l.split('\t')[0] for l in open(U+'/decls.tsv') if l.strip())
reg={}
for l in list(open(U+'/registry.tsv'))[1:]:
    p=l.rstrip('\n').split('\t'); reg[p[0]]=dict(chapter=p[1],kind=p[2],attr=p[3],lean=p[4].split(',') if p[4] else [],title=p[5])
enr={}
for f in glob.glob(U+'/enriched/*.json'):
    for n in json.load(open(f))['nodes']: enr[n['id']]=n
alllabels=set(reg)
for f in glob.glob(BP+'/*.tex'):
    alllabels|=set(re.findall(r'\\label\{([^}]*)\}',open(f).read()))
NODE_ENVS={'definition','theorem','lemma','example','proposition','corollary'}
SAFE=r'\\(?:lean|srcloc|label|uses|ref|href|url|input|axfoot|leanurl|cite)\{[^}]*\}(?:\{[^}]*\})?'
def check(path):
    txt=open(path).read(); lines=txt.split('\n'); errs=0; warns=0
    def E(ln,m): nonlocal errs; errs+=1; print(f'ERROR {os.path.basename(path)}:{ln}: {m}')
    def W(ln,m): nonlocal warns; warns+=1; print(f'WARN  {os.path.basename(path)}:{ln}: {m}')
    # labels unique in file
    seen=collections.Counter(re.findall(r'\\label\{([^}]*)\}',txt))
    for k,v in seen.items():
        if v>1: E(0,f'duplicate label {k}')
    # walk environments
    stack=[]; nodes=[]; cur=None; lastnode=None; i=0
    for ln,line in enumerate(lines,1):
        for m in re.finditer(r'\\begin\{(\w+)\}(?:\[([^\]]*)\])?',line):
            env=m.group(1)
            if env in NODE_ENVS:
                cur=dict(env=env,title=m.group(2),start=ln,label=None,lean=[],leanok=False,uses=[],contrib=None,proof=None); nodes.append(cur)
            elif env=='proof':
                if lastnode is None or lastnode.get('proof') is not None: W(ln,'proof without preceding theorem/lemma (or duplicate proof)')
                else: lastnode['proof']=dict(start=ln,leanok=False,uses=[],notproved=False)
        for m in re.finditer(r'\\end\{(\w+)\}',line):
            if m.group(1) in NODE_ENVS and cur: lastnode=cur; cur=None
        tgt=None
        if cur: tgt=cur
        elif lastnode and lastnode.get('proof') and 'end' not in lastnode['proof']: tgt=lastnode['proof']
        if tgt is not None:
            for m in re.finditer(r'\\label\{([^}]*)\}',line): tgt['label']=m.group(1)
            for m in re.finditer(r'\\lean\{([^}]*)\}',line): tgt.setdefault('lean',[]).extend(x.strip() for x in m.group(1).split(',') if x.strip())
            if re.search(r'\\leanok\b',line): tgt['leanok']=True
            for m in re.finditer(r'\\uses\{([^}]*)\}',line): tgt['uses'].extend(x.strip() for x in m.group(1).split(',') if x.strip())
            for m in re.finditer(r'\\contrib\{([^}]*)\}',line): tgt['contrib']=m.group(1)
            if 'Not proved in Lean' in line: tgt['notproved']=True
            if re.search(r'\\end\{proof\}',line) and lastnode and lastnode.get('proof') is tgt: tgt['end']=ln
        # underscore heuristic
        s=re.sub(SAFE,'',line); s=re.sub(r'\$[^$]*\$','',s); s=re.sub(r'\\verb(.).*?\1','',s); s=s.replace('\\_','')
        if re.search(r'(?<!\\)_',s) and not line.strip().startswith('%'): W(ln,'possible unescaped underscore: '+line.strip()[:90])
        if re.search(r'\\(sub)?section\{[^}]*\$',line) or re.search(r'\\chapter\{[^}]*\$',line): W(ln,'math in heading without texorpdfstring')
    for n in nodes:
        ln=n['start']
        if not n['label']: E(ln,f'{n["env"]} without \\label'); continue
        lab=n['label']
        if lab not in reg: W(ln,f'label {lab} not in registry (new node?)')
        if not n['lean']: W(ln,f'{lab}: no \\lean{{}}')
        for x in n['lean']:
            if x not in names: E(ln,f'{lab}: \\lean name not found in compiled environment: {x}')
        if not n['leanok']: W(ln,f'{lab}: statement without \\leanok')
        for u in n['uses']:
            if u not in alllabels: E(ln,f'{lab}: \\uses unknown label {u}')
            if u==lab: E(ln,f'{lab}: uses itself')
        attr=reg.get(lab,{}).get('attr')
        if attr and attr!='master' and not n['contrib']: E(ln,f'{lab}: attribution {attr} but no \\contrib{{}} badge')
        if n['contrib'] and n['contrib'] not in ('iota','trproj','mixed'): E(ln,f'{lab}: bad \\contrib value {n["contrib"]}')
        if n['env'] in ('theorem','lemma','proposition','corollary'):
            p=n.get('proof')
            if not p: E(ln,f'{lab}: {n["env"]} without sibling proof environment')
            else:
                for u in p['uses']:
                    if u not in alllabels: E(p['start'],f'{lab}: proof \\uses unknown label {u}')
                    if u==lab: E(p['start'],f'{lab}: proof uses itself')
                e=enr.get(lab)
                if e is not None:
                    if e.get('direct_sorry') and p['leanok']: E(p['start'],f'{lab}: proof has \\leanok but declaration contains a literal sorry (direct_sorry=true)')
                    if not e.get('direct_sorry') and not p['leanok'] and not p.get('notproved'): W(p['start'],f'{lab}: proof lacks \\leanok though no direct sorry recorded')
                    if e.get('usesSorry') and attr!='master' and '\\axfoot' not in txt[txt.find('\\label{'+lab+'}'):txt.find('\\label{'+lab+'}')+6000]: W(ln,f'{lab}: sorry-tainted contributed node without \\axfoot')
    print(f'{os.path.basename(path)}: {len(nodes)} nodes, {errs} errors, {warns} warnings')
    return errs
tot=0
for p in sys.argv[1:]: tot+=check(p)
sys.exit(1 if tot else 0)
