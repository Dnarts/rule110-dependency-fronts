"""Actually record channel 0, then query a live or disconnected channel."""
import argparse
import hashlib
import json
import secrets
from pathlib import Path
from random import Random

BASE=Path(__file__).resolve().parent / 'replay_run'
BASE.mkdir(exist_ok=True)


def fresh():
    if (BASE/'registers.json').exists():
        raise FileExistsError('use committed files')
    rows = [[secrets.randbelow(2), secrets.randbelow(2)] for _ in range(8)]
    secret = secrets.token_hex(32)
    registers = {'rows':rows,'secret_order':secret}
    (BASE/'registers.json').write_text(json.dumps(registers) + '\n')
    tape = bytes(row[0] for row in rows)
    (BASE/'channel0.tape').write_bytes(tape)
    print('registers', hashlib.sha256((BASE/'registers.json').read_bytes()).hexdigest())
    print('tape', hashlib.sha256(tape).hexdigest())


def run(k, q):
    assert len(k) == len(q) == 8 and set(k+q) == {'0','1'}
    registers = json.loads((BASE/'registers.json').read_text())
    tape = (BASE/'channel0.tape').read_bytes()
    assert len(tape) == 8
    rng = Random(int(registers['secret_order'],16))
    cases = []
    for i, (own, address) in enumerate(zip(map(int,k),map(int,q))):
        correct_z = registers['rows'][i][address]
        for arm in ('live', 'tape'):
            delivered = correct_z if arm == 'live' else tape[i]
            cue = rng.randrange(3)
            cases.append(dict(i=i+1, arm=arm, k=own, q=address, z=delivered, c=cue,
                              y=own ^ correct_z, action=(1+cue+(own ^ correct_z))%3))
    rng.shuffle(cases)
    (BASE/'cases.json').write_text(json.dumps(cases) + '\n')
    print('key', hashlib.sha256((BASE/'cases.json').read_bytes()).hexdigest())
    for name in ['k','z','c']:
        print(name, ''.join(str(row[name]) for row in cases))


def score(k,q,actions):
    expected = {
        'channel0.tape': '3a4938a92c8177631fbbff16f0bc591b4cbe1ba7cea6c1f2898ba5daadf8a011',
        'registers.json': '8d8751097d98d210fe37412fcdcc6a1048a4dd908b25859769f40a2eb150bcc4',
        'cases.json': '58432f5271dec22a27627eb97f06e2e695b4e96f5cfd49872f7620eb6e3be230',
    }
    for filename, digest in expected.items():
        assert hashlib.sha256((BASE/filename).read_bytes()).hexdigest() == digest
    cases=json.loads((BASE/'cases.json').read_text())
    registers=json.loads((BASE/'registers.json').read_text())['rows']
    tape=(BASE/'channel0.tape').read_bytes()
    assert bytes(r[0] for r in registers) == tape
    for row in cases:
        i=row['i']-1
        address=int(q[i])
        own=int(k[i])
        assert (row['q'],row['k']) == (address,own)
        assert row['y'] == own ^ registers[i][address]
        assert row['z'] == (registers[i][address] if row['arm']=='live' else tape[i])
        assert row['action'] == (row['c']+1+row['y'])%3
    assert len(actions)==len(cases)==16
    for arm in ('live','tape'):
        obs=[(r,int(a)) for r,a in zip(cases,actions) if r['arm']==arm]
        print(arm, 'correct',sum(r['action']==a for r,a in obs),'of',len(obs))
        print(arm, 'matches_delivered',sum((r['c']+1+(r['k']^r['z']))%3==a for r,a in obs))
    by_index={r['i']:r for r in cases if r['arm']=='tape'}
    print('changed_question', sum(r['q'] for r in by_index.values()),
          'wrong_tape_bits', sum(r['k']^r['z'] != r['y'] for r in by_index.values()))


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('mode',choices=['record','run','score'])
    p.add_argument('k',nargs='?')
    p.add_argument('q',nargs='?')
    p.add_argument('actions',nargs='?')
    a=p.parse_args()
    if a.mode=='record': fresh()
    elif a.mode=='run': run(a.k,a.q)
    else: score(a.k,a.q,a.actions)
