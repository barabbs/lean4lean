#!/usr/bin/env python3
"""Global blueprint checks across all chapters: duplicate labels, unresolved \\uses, and \\uses cycles (which crash plasTeX depgraph)."""
import re,glob,sys,os,collections
ROOT=os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..'))
CH=os.path.join(ROOT,'blueprint','src','chapters')
NODE_ENVS={'definition','theorem','lemma','example','proposition','corollary'}
defined={}; uses=collections.defaultdict(set); where={}
for f in sorted(glob.glob(CH+'/*.tex')):
    lines=open(f).read().split('\n'); cur=None; last=None; inproof=False
    for ln,line in enumerate(lines,1):
        for m in re.finditer(r'\\begin\{(\w+)\}',line):
            if m.group(1) in NODE_ENVS: cur='?'; inproof=False
            elif m.group(1)=='proof': inproof=True
        for m in re.finditer(r'\\label\{([^}]*)\}',line):
            lab=m.group(1)
            if cur=='?': cur=lab; last=lab
            if lab in defined and not lab.startswith('chap:'): print(f'ERROR duplicate label {lab}: {defined[lab]} and {f.split("/")[-1]}:{ln}')
            defined[lab]=f'{f.split("/")[-1]}:{ln}'
        tgt=cur if cur and cur!='?' else (last if inproof else None)
        if tgt:
            for m in re.finditer(r'\\uses\{([^}]*)\}',line):
                for u in m.group(1).split(','):
                    u=u.strip()
                    if u: uses[tgt].add(u); where[(tgt,u)]=f'{f.split("/")[-1]}:{ln}'
        for m in re.finditer(r'\\end\{(\w+)\}',line):
            if m.group(1) in NODE_ENVS: cur=None
            elif m.group(1)=='proof': inproof=False
errs=0
for a,us in uses.items():
    for u in us:
        if u not in defined: print(f'ERROR unresolved \\uses{{{u}}} in {a} at {where[(a,u)]}'); errs+=1
        if u==a: print(f'ERROR self-use {a} at {where[(a,u)]}'); errs+=1
# Tarjan SCC
sys.setrecursionlimit(10000)
index={}; low={}; st=[]; on=set(); sccs=[]; idx=[0]
def sc(v):
    index[v]=low[v]=idx[0]; idx[0]+=1; st.append(v); on.add(v)
    for w in uses.get(v,()):
        if w not in index: sc(w); low[v]=min(low[v],low[w])
        elif w in on: low[v]=min(low[v],index[w])
    if low[v]==index[v]:
        comp=[]
        while True:
            w=st.pop(); on.discard(w); comp.append(w)
            if w==v: break
        if len(comp)>1: sccs.append(comp)
for v in list(uses):
    if v not in index: sc(v)
for comp in sccs:
    errs+=1; print(f'ERROR \\uses cycle among {len(comp)} nodes: '+', '.join(sorted(comp)))
    # show the edges inside the cycle
    cs=set(comp)
    for a in sorted(comp):
        for u in sorted(uses[a]&cs): print(f'    {a} -> {u}   ({where[(a,u)]})')
print(f'{len(defined)} labels, {sum(len(v) for v in uses.values())} uses edges, {len(sccs)} cycles, {errs} errors')
sys.exit(1 if errs else 0)
