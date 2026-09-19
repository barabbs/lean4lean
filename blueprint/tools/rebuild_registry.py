#!/usr/bin/env python3
"""Rebuild understand/registry.tsv, lean2label.tsv and enriched/all.json from the chapter .tex files + decls.tsv. Run after editing chapters."""
import re,sys,os,glob,json,collections
R=os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..'))
S=os.environ.get('BLUEPRINT_WORK') or os.path.join(R,'.blueprint-work')
U=os.path.join(S,'understand'); CH=os.path.join(R,'blueprint','src','chapters')
decl={}
for l in open(U+'/decls.tsv'):
    p=l.rstrip('\n').split('\t'); decl.setdefault(p[0],p)
bymod=collections.defaultdict(list)
for n,p in decl.items():
    try: bymod[p[1]].append((int(p[3]),n))
    except: pass
src_sorry={}
for mod,lst in bymod.items():
    f=R+'/'+mod.replace('.','/')+'.lean'
    if not os.path.exists(f): continue
    lines=open(f).read().split('\n'); lst.sort(); starts=sorted(set(s for s,_ in lst))+[len(lines)+1]
    for s,n in lst:
        if s<1: continue
        nxt=min(x for x in starts if x>s)
        seg=lines[s-1:nxt-1]
        src_sorry[n]=any(re.search(r'\bsorry\b',re.sub(r'--.*','',x)) for x in seg)
NODE={'definition','theorem','lemma','example','proposition','corollary'}
os.makedirs(U+'/enriched',exist_ok=True)
for old in glob.glob(U+'/enriched/*.json'): os.remove(old)
reg=open(U+'/registry.tsv','w'); reg.write('label\tchapter\tkind\tattribution\tlean\ttitle\n'); l2l=open(U+'/lean2label.tsv','w')
nodes=[]
for f in sorted(glob.glob(CH+'/*.tex')):
    c=os.path.basename(f)[:-4]; txt=open(f).read()
    for m in re.finditer(r'\\begin\{(\w+)\}(?:\[((?:[^\]\\]|\\.)*)\])?(.*?)\\end\{\1\}',txt,re.S):
        env,title,body=m.group(1),m.group(2) or '',m.group(3)
        if env not in NODE: continue
        lab=re.search(r'\\label\{([^}]*)\}',body)
        if not lab: continue
        lean=[x.strip() for mm in re.finditer(r'\\lean\{([^}]*)\}',body) for x in mm.group(1).split(',') if x.strip()]
        cb=re.search(r'\\contrib\{([^}]*)\}',body); attr=cb.group(1) if cb else 'master'
        us=any(decl.get(x,[0]*7)[5]=='true' for x in lean); ds=any(src_sorry.get(x,False) for x in lean)
        ax=sorted(set(a for x in lean if x in decl for a in decl[x][4].split(',') if a and a!='-'))
        nodes.append(dict(id=lab.group(1),lean=lean,attribution=attr,usesSorry=us,direct_sorry=ds,axioms=ax,chapter=c,kind=env))
        reg.write(f"{lab.group(1)}\t{c}\t{env}\t{attr}\t{','.join(lean)}\t{title.strip()}\n")
        for x in lean: l2l.write(f"{x}\t{lab.group(1)}\n")
json.dump(dict(nodes=nodes),open(U+'/enriched/all.json','w'),indent=1)
print(len(nodes),'nodes;',dict(collections.Counter(n['attribution'] for n in nodes)))
