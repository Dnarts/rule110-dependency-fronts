"""Homogeneous radius-one multi-track automaton: isolated transport plus native Rule 110."""
from typing import NamedTuple
import json
from causal_line import run


class Cell(NamedTuple):
    data: int
    clock: int
    role: str
    message: int


def visible(cell):
    return cell.message if cell.clock == 7 and cell.role == 'receiver' else cell.data


def update(left, center, right):
    triple = 4*visible(left) + 2*visible(center) + visible(right)
    data = (110 >> triple) & 1
    received = center.message
    if center.clock == 2 and center.role == 'observer':
        received = center.data
    if 4 <= center.clock <= 6:
        received = right.message
    return Cell(data, min(8, center.clock+1), center.role, received)


def run_check():
    size = 61
    public = []
    for case in run():
        initial = set(case['trace'][0])
        roles = {0:'receiver',3:'observer'}
        cells = [Cell(int(j in initial),0,roles.get(j,'plain'),0) for j in range(-30,31)]
        snapshots = [cells]
        for _ in range(8):
            cells = [update(cells[(j-1)%size],cells[j],cells[(j+1)%size]) for j in range(size)]
            snapshots.append(cells)
        assert snapshots[3][33].message == case['z']
        assert snapshots[7][30].message == case['z']
        assert snapshots[8][30].data == case['y']
        public.append(snapshots)
    for a,b in ((0,1),(2,3)):
        for t in range(4,8):
            assert [c.data for c in public[a][t]] == [c.data for c in public[b][t]]
            assert public[a][t] != public[b][t]
    return {'worlds':4, 'correct_outputs_at_tick_8':4, 'ring_size':size,
            'radius':1, 'single_time_invariant_local_transition':True}

if __name__ == '__main__':
    print(json.dumps(run_check(),indent=2))
