import json,sys
SRC='/home/shunqwang4/research/r2l-run-SPLIT2/runs/st-corpus-SPLIT2/source.ndjson'
def lv(u): return 'max('+','.join((e['l'].get('n','Set') if e['l']['k']!='set' else 'Set')+('+%d'%e['n'] if e['n'] else '') for e in u)+')' if len(u)>1 else ((u[0]['l'].get('n','Set') if u[0]['l']['k']!='set' else 'Set')+('+%d'%u[0]['n'] if u[0]['n'] else ''))
def short(n): return n.split('.')[-1] if len(n)>40 else n
def pp(t,ctx,d=0):
    k=t['k']
    if k=='rel': i=t['i']; return ctx[-1-i] if i<len(ctx) else f'#{i}'
    if k=='sort':
        s=t['s']; return 'Prop' if s['k']=='prop' else 'SProp' if s['k']=='sprop' else f"Type@{{{lv(s['u'])}}}"
    if k=='prod':
        n=t['n']['n'] or '_'; return f"(∀ {n} : {pp(t['ty'],ctx)}, {pp(t['b'],ctx+[n])})"
    if k=='lam':
        n=t['n']['n'] or '_'; return f"(fun {n} : {pp(t['ty'],ctx)} => {pp(t['b'],ctx+[n])})"
    if k=='let':
        n=t['n']['n']; return f"(let {n} := {pp(t['v'],ctx)} in {pp(t['b'],ctx+[n])})"
    if k=='app': return '('+' '.join([pp(t['f'],ctx)]+[pp(a,ctx) for a in t['args']])+')'
    if k=='const': return t['c']+(('@'+str([l.get('n') for l in t['u']])) if t['u'] else '')
    if k=='ind': return t['ind']['mind']+(('@'+str([l.get('n') for l in t['u']])) if t['u'] else '')
    if k=='construct': return f"{t['ind']['mind']}#c{t['c']}"
    if k=='case': return f"(match {pp(t['c'],ctx)} ...)" if 'c' in t else '(match ...)'
    if k=='proj': return f"{pp(t['t'],ctx)}.π{t['p']['arg']}"
    if k=='cast': return pp(t['t'],ctx)
    return f'<{k}>'
def get(name):
    for line in open(SRC):
        if f'"name":"{name}"' in line[:300]:
            return json.loads(line)
def show(name):
    d=get(name)
    if d is None: print('NOT FOUND',name); return
    print('###',name,d['kind'],d.get('universes',{}).get('k'), d.get('body_state',''))
    if d['kind']=='constant':
        print('TYPE:',pp(d['type'],[]))
        if d.get('body'): print('BODY:',pp(d['body'],[])[:3000])
    else:
        print('npars',d['npars'],'params(outer→inner):',[ (p['n']['n'],pp(p['ty'],[])) for p in reversed(d['params'])][:6])
        for b in d['bodies']:
            print(' body',b['name'],'sort',b['sort'],'\n  arity',pp(b['type'],[]))
            for c in b['ctors']: print('  ctor',c['name'],':',pp(c['type'],[b['name']])[:1500])
            for pj in b['projs']: print('  proj',pj[0] if isinstance(pj,list) else pj)
if __name__=='__main__':
    for n in sys.argv[1:]: show(n)
