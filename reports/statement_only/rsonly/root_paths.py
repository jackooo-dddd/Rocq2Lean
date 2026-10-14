import json,collections,sys,re
RUN='/home/shunqwang4/research/r2l-run-SPLIT2/runs/st-corpus-SPLIT2'
deps={}
for line in open(RUN+'/source.ndjson'):
    d=json.loads(line)
    if d.get('kind') in ('constant','inductive'):
        dd=d.get('deps') or {}; deps[d['name']]=set((dd.get('type') or [])+(dd.get('body') or []))-{d['name']}
rep={x['source']:x for x in json.load(open(RUN+'/translation_report.json'))['results']}
# generated rows (obligations) are separate decls in the source already
CL={'TRANSLATED_AND_CHECKED','STATEMENT_KERNEL_CHECKED','BOOTSTRAP_RESOLVED','PENDING_KERNEL_CHECKED','STATEMENT_PENDING_KERNEL_CHECKED'}
pins=json.load(open(sys.argv[1]))
def cls(n):
    x=rep[n]; m=x.get('message') or ''
    if n in pins: return {'result-sort-only':'A','field/param':'B','implicit':'B','constant':'B'}.get(pins[n][2],'?')
    if 'native fact' in m and 'solved as' in m: return 'SOL'
    if 'coherence' in m: return 'COH'
    return x['status'][:12]
memo={}
def frontier(n):
    if n in memo: return memo[n]
    memo[n]=set()
    st=rep[n]['status']
    if st in CL: return set()
    if st!='BLOCKED_DEPENDENCY': memo[n]={n}; return memo[n]
    out=set()
    for d in deps.get(n,()):
        if d in rep: out|=frontier(d)
    memo[n]=out; return out
sys.setrecursionlimit(100000)
prot=[n for n,x in rep.items() if x.get('protected') and x['status'] not in CL]
combo=collections.Counter(); ex={}
for r in prot:
    f=frontier(r); k=tuple(sorted({cls(x) for x in f}))
    combo[k]+=1; ex.setdefault(k,(r,sorted(f)[:6]))
for k,v in combo.most_common(): print(v,k,'|',ex[k][0].split('.')[-1][:60],'|',[e.split('.')[-1][:45] for e in ex[k][1]])
A_roots=[r for r in prot if any(cls(x)=='A' for x in frontier(r))]
print('roots with case A in frontier:',len(A_roots))
