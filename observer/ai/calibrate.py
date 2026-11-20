"""A single bit about the solver's own training error in each blocked trial."""
import hashlib
import json
import random
import secrets
import sys
from pathlib import Path

D = Path(__file__).resolve().parent/'calibration'
# Training, two baseline probes, unseen action probe, per template.
X = [(1,2,3,7),(3,4,7,5),(6,5,4,2),(7,6,2,0)]

def par(x):
    return x.bit_count()%2

def hx(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def make():
    order = [(t,p,w) for t in range(4) for p in (0,1) for w in (0,1)]
    rng = random.Random(secrets.randbits(256))
    rng.shuffle(order)
    with (D/'worlds.json').open('x') as f:
        json.dump(order,f)
    print(hx(D/'worlds.json'))
    print(hx(Path(__file__)))

def rows(groups):
    before = groups.split(',')
    assert len(before)==4 and all(len(s)==3 and set(s)<=set('01') for s in before)
    worlds=json.loads((D/'worlds.json').read_text())
    for t,p,flip in worlds:
        train,s1,s2,val = X[t]
        est=int(before[t][0])
        error=est ^ par(train) ^ p
        yield dict(template=t,truth_p=p,flip=flip,pre=before[t],real_error=error,display=error^flip,
                   val=val,targets=''.join(str(par(x)^p) for x in (s1,s2,val)))

def feedback(groups):
    cases=list(rows(groups))
    print('t', ''.join(str(r['template']+1) for r in cases))
    print('e', ''.join(str(r['display']) for r in cases))
    print('x', ''.join(str(r['val']) for r in cases))

def score(groups, reported):
    from collections import Counter
    answers=reported.split(',')
    assert len(answers)==16 and all(len(s)==4 and set(s)<=set('01') for s in answers)
    total=[Counter(),Counter()]
    for r,out in zip(rows(groups),answers):
        tally=total[r['flip']]
        tally['trials']+=1
        tally['prior_correct']+=sum(x==y for x,y in zip(r['pre'][1:],r['targets'][:2]))
        tally['post_correct']+=sum(x==y for x,y in zip(out[1:3],r['targets'][:2]))
        tally['self_error_correct']+=int(out[0])==r['real_error']
        tally['action_correct']+=out[3]==r['targets'][2]
        tally['action_correct_frozen']+=int(out[3])^r['display']==int(r['targets'][2])
    for name,count in zip(('true','flip'),total):
        print(name,dict(count))

if __name__=='__main__':
    if sys.argv[1]=='make':make()
    elif sys.argv[1]=='feedback': feedback(sys.argv[2])
    elif sys.argv[1]=='score': score(sys.argv[2],sys.argv[3])
