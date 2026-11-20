#!/usr/bin/env python3
"""Run with Python 3, without -O. Prints the full JSON certificate to stdout."""
import itertools
import json
from collections import Counter, defaultdict

assert __debug__, "This audit requires assertions. Run without -O."
TABLE = {(a,b,c): (110 >> (4*a+2*b+c)) & 1 for a,b,c in itertools.product((0,1),repeat=3)}


def bits(word):
    return tuple(map(int,word))


def word(row):
    return ''.join(map(str,row))


def step(row):
    return tuple(TABLE[row[i-1], value, row[(i+1)%len(row)]] for i,value in enumerate(row))


def trace(row, horizon):
    states = [row]
    for _ in range(horizon):
        states.append(step(states[-1]))
    return states


def write(row, index, bit):
    result = list(row)
    result[index % len(row)] = bit
    return tuple(result)


def best_score(examples):
    by_input = defaultdict(Counter)
    for observed, label in examples:
        by_input[observed][label] += 1
    return sum(max(counts.values()) for counts in by_input.values())


def audit_clean():
    initial = ('011000010000000','011001010000000','110100010000101','110101010000101')
    traces = [trace(bits(s),4) for s in initial]
    rows = []
    for k, y in itertools.product((0,1),repeat=2):
        xs = traces[2*k+y]
        assert xs[0][0] == xs[4][0] == k and xs[0][5] == y
        z = xs[2][3]
        assert z == (k ^ y)
        own_trace = [word((x[13],x[14],x[0])) for x in xs]
        decoded = step(write(xs[4],14,z))[14]
        flipped = step(write(xs[4],14,1-z))[14]
        assert xs[4][13] == 1 and decoded == y and flipped == 1-y
        rows.append(dict(k=k,y=y,z=z,states=list(map(word,xs)),own_trace=own_trace,
                         decoded=decoded,flipped=flipped,without_pulse=step(xs[4])[14]))
    for k in (0,1):
        a,b = traces[2*k:2*k+2]
        assert write(a[0],5,1) == b[0]
        assert all(x!=y for x,y in zip(a[:4],b[:4])) and a[4] == b[4]
        assert rows[2*k]['own_trace'] == rows[2*k+1]['own_trace']
    assert best_score((tuple(r['own_trace']), r['y']) for r in rows) == 2
    assert best_score((r['z'], r['y']) for r in rows) == 2
    assert sum(r['without_pulse']==r['y'] for r in rows) == 2
    # Full held-out intervention check: perturb one other initial cell consistently
    # in all four worlds, keep the apparatus and the original (K,Y) labels fixed.
    heldout = {}
    for j in range(15):
        if j in (0,5):
            continue
        score = 0
        for xs in traces:
            varied = trace(write(xs[0],j,1-xs[0][j]),4)
            z = varied[2][3]
            score += step(write(varied[4],14,z))[14] == varied[0][5]
        heldout[j] = score
    return dict(rows=rows,held_out_single_background_flip_scores_out_of_four=heldout)


def delta(a,b,t,center_index,offset=0,ring=False):
    result = []
    for i,(v,w) in enumerate(zip(a,b)):
        if v==w:
            continue
        j = i+offset-center_index
        if ring:
            n=len(a)
            j=(j+n//2)%n-n//2
        result.append((t,j,v,w))
    return tuple(sorted(result))


def audit_impossibility():
    # Target flip at index 6. At t=3 no cell outside [-3,3] can differ.
    # Computing that entire interval requires only [-6,6] at t=0.
    expected = ((1,-1,1,0),(1,0,1,0),(2,-2,1,0),(2,-1,1,0),(2,0,0,1))
    extinct=[]
    for other in itertools.product((0,1),repeat=12):
        a = other[:6]+(0,)+other[6:]
        b = write(a,6,1)
        initial = a
        signature = ()
        for t in range(1,4):
            a = tuple(TABLE[nb] for nb in zip(a,a[1:],a[2:]))
            b = tuple(TABLE[nb] for nb in zip(b,b[1:],b[2:]))
            if t < 3:
                signature += delta(a,b,t,center_index=6,offset=t)
        if a == b:
            assert signature == expected
            extinct.append(word(initial))
    assert len(extinct) == 8
    small_rings = {}
    for size in range(1,13):
        center = 0
        count=0
        for other in itertools.product((0,1),repeat=size-1):
            a = (0,)+other
            b = write(a,center,1)
            aa,bb = trace(a,3),trace(b,3)
            if aa[3] == bb[3]:
                count += 1
                signature = delta(aa[1],bb[1],1,center,ring=True) + delta(aa[2],bb[2],2,center,ring=True)
                # Rings of size 2 or 3 may wrap a perturbation onto itself.
                if size>=4:
                    assert signature == expected
        small_rings[size] = count
    return dict(contexts_checked=4096, extinct_contexts_with_Y_zero=extinct,
                common_signature=expected, small_ring_extinct_counts=small_rings)


def audit_adaptive():
    initial=('01011001100','01101111100','10000011110','10101110111')
    rows=[]
    for k,y in itertools.product((0,1),repeat=2):
        xs=trace(bits(initial[2*k+y]),3)
        z=xs[0][6+k]
        assert xs[0][0]==k and xs[0][5]==y and z==(k^y)
        assert xs[-1]==bits('10011011111')
        assert step(write(xs[3],4+k,z))[4] == y
        rows.append(dict(k=k,y=y,z=z,raw=[xs[0][6],xs[0][7]],
                         states=list(map(word,xs)), own_trace=word(x[0] for x in xs)))
    for k in (0,1):
        a,b=rows[2*k:2*k+2]
        assert a['own_trace']==b['own_trace']
        assert a['states'][2]!=b['states'][2]
    passive_scores=[best_score(((r['own_trace'],r['raw'][j]),r['y']) for r in rows) for j in range(2)]
    assert passive_scores == [3,3]
    seen = {}
    state=bits('10011011111')
    while state not in seen:
        # Public address schedule depending only on phase. At t=3 choose cell 4.
        order=[(4+j)%11 for j in range(11)]
        i=next(i for i in order if (state[i-1],state[i],state[(i+1)%11]) == (1,1,0))
        seen[state]=i
        for r in rows:
            assert step(write(state,i+r['k'],r['z']))[i]==r['y']
        state=step(state)
    assert len(seen)==110 and state==bits('10011011111')
    common=state
    basin=[]
    for s in itertools.product((0,1),repeat=11):
        if trace(s,3)[-1]==common:
            k=s[0]
            basin.append(dict(initial=word(s),correct=(k^s[6+k])==s[5]))
    outside_fail=[r['initial'] for r in basin if not r['correct']]
    assert len(basin)==7 and outside_fail==['10000010001']
    return dict(rows=rows,best_fixed_port_correct_out_of_four=passive_scores,
                free_orbit_period=len(seen),all_seven_preimages=basin)


if __name__=='__main__':
    print(json.dumps(dict(clean_four_step=audit_clean(), three_step_obstruction=audit_impossibility(),
                          adaptive_three_step=audit_adaptive()),indent=2))
