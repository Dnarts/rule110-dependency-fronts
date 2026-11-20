"""Single-cell interventions on the infinite line, zero outside [-6,13]."""
import json
from domain import step
from causal_crosscheck import verify_late_gate

def run():
    rows = []
    for n, seed in enumerate(verify_late_gate()):
        k,y = divmod(n,2)
        state = frozenset(i for i in range(-6,14) if seed[i % 15] == '1')
        states = [state]
        for _ in range(4):
            states.append(step(states[-1]))
        z = int(3 in states[2])
        assert int(5 in state) == y and z == k ^ y
        assert -2 in states[4] and (0 in states[4]) == bool(k)
        outputs = []
        for incoming in (0,1):
            after = (states[4] - {-1}) | ({-1} if incoming else set())
            t5 = step(after)
            t6 = step(t5)
            outputs.append({'decoded':int(-1 in t5),
                            'next':{str(i):int(i in t6) for i in (-2,-1,0)}})
        assert outputs[z]['decoded'] == y and outputs[1-z]['decoded'] != y
        rows.append(dict(k=k,y=y,z=z,initial=''.join(str(int(i in state)) for i in range(-6,14)),
                         trace=[sorted(s) for s in states],
                         port_history=[''.join(str(int(i in s)) for i in (-2,-1,0)) for s in states],
                         received=outputs))
    for a,b in [(0,1),(2,3)]:
        assert set(rows[a]['trace'][0]) ^ set(rows[b]['trace'][0]) == {5}
        assert all(x!=y for x,y in zip(rows[a]['trace'][:4],rows[b]['trace'][:4]))
        assert rows[a]['trace'][4] == rows[b]['trace'][4]
        assert rows[a]['port_history'] == rows[b]['port_history']
    return rows

if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
