import json,re,collections,sys
sys.path.insert(0,'/home/shunqwang4/research/r2l-B/tools'); import audit
RUN='/home/shunqwang4/research/r2l-run-SPLIT2/runs/st-corpus-SPLIT2'
decls={}; deps={}
for line in open(RUN+'/source.ndjson'):
    d=json.loads(line)
    if d.get('kind') in ('constant','inductive'):
        decls[d['name']]=d
        dd=d.get('deps') or {}
        deps[d['name']]=set((dd.get('type') or [])+(dd.get('body') or []))
rep={x['source']:x for x in json.load(open(RUN+'/translation_report.json'))['results']}
pat=re.compile(r"refused: Rocq\.(\S+?): the level of u_(\S+) is free")
def lvname(p,cands):
    for l in cands:
        if 'u_'+l.replace('.','_')==p: return l
def where(h,l):
    """occurrence class of level l in the source of referenced declaration h"""
    d=decls.get(h)
    if d is None: return 'unknown-head'
    occ=audit._occ_paths(d,l)
    if not occ: return 'implicit'
    if d['kind']=='inductive':
        b=d['bodies'][0]
        res=set(audit._final_sort_paths(b['type'],('bodies',0,'type'),l))|{q for q in occ if q[:3]==('bodies',0,'sort')}
        if occ<=res: return 'result-sort-only'
        # carrier: a field sort of a record (ctor arg whose type is Sort l)
        return 'field/param'
    return 'constant'
cls={}
for n,x in rep.items():
    m=pat.search(x.get('message') or '')
    if x['status']=='UNIVERSE_REJECTED' and m:
        tgt=m.group(1); # Rocq name -> source name: resolve by target map
        cls[n]=(tgt,m.group(2))
# map target names to source decls
t2s={}
for n,x in rep.items():
    if x.get('target'): t2s[x['target'].removeprefix('Rocq.')]=n
    for c in x.get('target_ctors') or []: t2s[c['name'].removeprefix('Rocq.')]=n
lvls=json.loads(open(RUN+'/source.ndjson').readlines()[4])['levels']
pmap={'u_'+l.replace('.','_'):l for l in lvls}
out={}
for n,(tgt,p) in cls.items():
    h=t2s.get(tgt); l=pmap.get('u_'+p)
    out[n]=(h,l,where(h,l) if h and l else 'unresolved')
c=collections.Counter((v[0],v[1],v[2]) for v in out.values())
for k,v in c.most_common(15): print(v,k)
json.dump(out,open('/tmp/claude-1001/-home-shunqwang4-research/8ab6b15e-27d1-40c0-80cb-9145426e41b9/scratchpad/pin_classes.json','w'))
