"""Finite-speed delivery in an isolated one-bit side channel, then native Rule 110 readout."""
from causal_line import run
from domain import step
import json


def check():
    records = []
    for case in run():
        k,y,z = case['k'],case['y'],case['z']
        states = [frozenset(s) for s in case['trace']]
        for _ in range(3):
            states.append(step(states[-1]))
        assert (3 in states[2]) == bool(z)
        route = (3,3,3,2,1,0)  # positions at times 2,3,4,5,6,7
        assert all(abs(b-a)<=1 for a,b in zip(route,route[1:]))
        assert (-1 in states[7]) and (1 in states[7]) == bool(k)
        results = []
        for signal in (z, 1-z):
            bus = (route[0], signal)
            for i in route[1:]:
                bus = (i,bus[1])
            target, value = bus
            after = (states[7] - {target}) | ({target} if value else set())
            results.append(int(target in step(after)))
        assert results == [y,1-y]
        h = [''.join(str(int(i in s)) for i in (-1,0,1)) for s in states]
        records.append(dict(k=k,y=y,z=z,h=h,valid_and_flip=results))
    assert records[0]['h'] == records[1]['h'] and records[2]['h'] == records[3]['h']
    return records

if __name__ == '__main__':
    print(json.dumps(check(),indent=2))
