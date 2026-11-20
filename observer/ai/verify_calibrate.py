"""Verify commitments and read the two literal calibration responses."""
import json

from calibrate import D, X, hx, par, rows, score
from pathlib import Path

assert hx(D/'worlds.json')=='fd70f29d6bf96789999035a46aaa3a99f69fcab40ca0eb6a217871150d1e12f2'
assert hx(Path(__file__).with_name('calibrate.py'))=='4a2129369d629052d5d3a17c3a6bd3b6a2a35c8c984598373eaf626ad6d4018e'
ans=json.loads((D/'responses.json').read_text())
assignments=json.loads((D/'worlds.json').read_text())
assert sorted(map(tuple,assignments))==[(t,p,w) for t in range(4) for p in (0,1) for w in (0,1)]
for item,values in zip(ans['pre'].split(','),X):
    guessed={int(ch)^par(v) for ch,v in zip(item,values)}
    assert len(guessed)==1
feedback=list(rows(ans['pre']))
assert ''.join(str(r['display']) for r in feedback)==ans['delivered']
score(ans['pre'],ans['post'])
# Recompute both frozen baselines directly from the archived prior, regardless of the submitted post.
for flip in (0,1):
    frozen=0
    for r in feedback:
        if r['flip'] != flip:
            continue
        first=X[r['template']][0]
        h=int(r['pre'][0]) ^ par(first)
        frozen += (h ^ par(r['val'])) == int(r['targets'][2])
    assert frozen == 4
