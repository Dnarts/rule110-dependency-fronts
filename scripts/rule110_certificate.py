#!/usr/bin/env python3
"""Rule 110: auditable finite certificate + explicitly stated induction lemmas.

Uses Python 3 standard library only. It does NOT claim proof-assistant/kernel
verification of general quantified statements. The 128-pattern check, periodic
background and moving-defect base cases are exhaustive finite certificates;
mathematical induction lemmas are given in rule110_certificate_proof_ru.md.

Run: python3 rule110_certificate.py --output rule110_certificate.json
"""
from __future__ import annotations

import argparse
import json
from itertools import product
from pathlib import Path
from typing import NamedTuple

RULE = 110
BACKGROUND = (1, 0, 1, 1)


def f(l: int, c: int, r: int, rule: int = RULE) -> int:
    """Truth table, with neighborhood 111..000 mapped to rule bits 7..0."""
    return (rule >> (4 * l + 2 * c + r)) & 1


def anf(l: int, c: int, r: int) -> int:
    return c ^ r ^ (c & r) ^ (l & c & r)


def step_window(xs: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(f(xs[i], xs[i + 1], xs[i + 2]) for i in range(len(xs) - 2))


def step3_window(xs: tuple[int, ...]) -> int:
    if len(xs) != 7:
        raise ValueError('requires exactly 7 cells')
    for _ in range(3):
        xs = step_window(xs)
    assert len(xs) == 1
    return xs[0]


def check_local_truth_tables() -> dict:
    for l, c, r in product((0, 1), repeat=3):
        assert f(l, c, r) == anf(l, c, r), (l, c, r)
    for c, r in product((0, 1), repeat=2):
        assert f(1, c, r) ^ f(0, c, r) == c & r
    for mask in range(128):
        xs = tuple((mask >> i) & 1 for i in range(7))
        flipped = (1 - xs[0],) + xs[1:]
        assert step3_window(xs) == step3_window(flipped), mask
    # Strengthened form: output at time 3 depends only on the rightmost 6
    # coordinates, regardless of the leftmost 7-window bit.
    return {'anf_cases': 8, 'left_derivative_cases': 4,
            'three_step_neighborhoods': 128, 'status': 'PASS'}


class DefectState(NamedTuple):
    bg: tuple[int, ...]       # period-p background
    support: frozenset[int]  # finite coordinates where perturbed state differs


def periodic_at(bg: tuple[int, ...], i: int) -> int:
    return bg[i % len(bg)]


def step_defect(st: DefectState) -> DefectState:
    """Exact update of a finite defect on an infinite periodic background.

    If background and perturbed configuration agree outside finite S, then
    after one step they agree outside S+[-1,1]. We evaluate *every* position
    inside that finite candidate range. This is exact on Z, not a truncation.
    """
    bg, S = st
    p = len(bg)
    next_bg = tuple(f(bg[(i - 1) % p], bg[i], bg[(i + 1) % p])
                    for i in range(p))
    if not S:
        return DefectState(next_bg, frozenset())

    def val(i: int) -> int:
        return bg[i % p] ^ int(i in S)

    lo, hi = min(S) - 1, max(S) + 1
    next_support = frozenset(
        i for i in range(lo, hi + 1)
        if f(val(i - 1), val(i), val(i + 1)) != next_bg[i % p]
    )
    return DefectState(next_bg, next_support)


def evolve_defect(st: DefectState, t: int) -> DefectState:
    for _ in range(t):
        st = step_defect(st)
    return st


def shift_defect(st: DefectState, d: int) -> DefectState:
    bg, S = st
    return DefectState(tuple(bg[(i - d) % len(bg)] for i in range(len(bg))),
                       frozenset(i + d for i in S))


def L(t: int) -> int:
    return t - t // 3


def check_periodic_certificate() -> dict:
    states = [DefectState(BACKGROUND, frozenset({2}))]
    for _ in range(6):
        states.append(step_defect(states[-1]))
    assert states[6] == shift_defect(states[3], 2), 'Y6≠shift2(Y3)'
    assert all(max(st.support) == 2 + L(t) for t, st in enumerate(states)), (
        'sharp right-front base cases failed'
    )

    # Check component-wise equality of the two *full* configurations at
    # t=6 and shift by 2 of t=3, using exact infinite representations.
    assert states[6].bg == shift_defect(states[3], 2).bg
    assert states[6].support == shift_defect(states[3], 2).support

    # Independent direct code path: two integer-encoded 32-site cyclic worlds.
    # In t<=6 the defect cone has not wrapped onto itself, N divisible by 4.
    N = 32
    bg = sum(BACKGROUND[i % 4] << i for i in range(N))
    pert = bg ^ (1 << 2)
    ring_states = []
    for _ in range(7):
        ring_states.append((bg, pert))
        bg, pert = step_ring(bg, N), step_ring(pert, N)
    for t, st in enumerate(states):
        b, y = ring_states[t]
        ring_diff = {i if i < 16 else i - N
                     for i in range(N) if ((b ^ y) >> i) & 1}
        assert ring_diff == set(st.support), (t, ring_diff, st.support)
    assert ring_states[6][0] == shift_ring(ring_states[3][0], 2, N)
    assert ring_states[6][1] == shift_ring(ring_states[3][1], 2, N)

    # Finite recurrence base phases t=3,4,5, plus t=0,1,2 checked above.
    return {
        'period4_defect': 'PASS', 'Y6_equals_shift2_Y3': 'PASS',
        'background_B6_equals_shift2_B3': 'PASS',
        'independent_ring32_crosscheck': 'PASS',
        'front_base_0_to_6': 'PASS',
        'frames': [{'t': t, 'background': ''.join(map(str, st.bg)),
                    'differences': sorted(st.support), 'rightmost': max(st.support)}
                   for t, st in enumerate(states)]
    }


def step_ring(state: int, n: int, rule: int = RULE) -> int:
    """Independent bit-vector update (no finite-support-defect logic)."""
    out = 0
    for i in range(n):
        l = (state >> ((i - 1) % n)) & 1
        c = (state >> i) & 1
        r = (state >> ((i + 1) % n)) & 1
        out |= f(l, c, r, rule) << i
    return out


def shift_ring(state: int, d: int, n: int) -> int:
    d %= n
    mask = (1 << n) - 1
    return ((state << d) | (state >> (n - d))) & mask if d else state


def single_one_step(active: frozenset[int]) -> frozenset[int]:
    """Direct evolution on zero background; independent of defect update."""
    if not active:
        return frozenset()
    return frozenset(i for i in range(min(active) - 1, max(active) + 2)
                     if f(int(i - 1 in active), int(i in active),
                          int(i + 1 in active)))


def check_right_endpoint_cases(horizon: int = 300) -> dict:
    active = frozenset({0})
    for t in range(horizon + 1):
        assert active and min(active) == -t and -t in active, t
        assert all(i >= -t for i in active)
        active = single_one_step(active)
    # General t proof in Markdown: background 0 fixed; when the leftmost
    # live site is a-t, previous 2 sites are 0, so f(0,0,1)=1.
    return {'single_seed_left_front_tested_t': horizon, 'status': 'PASS'}


def ring_audit(rule: int, n: int, times: tuple[int, ...]) -> dict:
    limit = 1 << n
    transition = [step_ring(s, n, rule) for s in range(limit)]
    states = list(range(limit))
    out = {}
    for t in range(max(times) + 1):
        if t in times:
            output = [(s & 1) for s in states]
            d = [j for j in range(n)
                 if any(output[s] != output[s ^ (1 << j)]
                        for s in range(limit))]
            image_size = len(set(states))
            out[t] = {'image_states': image_size,
                      'capacity_bits': (image_size - 1).bit_length(),
                      'essential_sites': d}
        states = [transition[s] for s in states]
    return out


def check_finite_ring_examples() -> dict:
    a = ring_audit(110, 5, (4, 5, 6))
    b = ring_audit(90, 4, (1, 2, 3))
    assert a[4]['image_states'] == 2 and len(a[4]['essential_sites']) == 5
    assert a[5] == {'image_states': 1, 'capacity_bits': 0, 'essential_sites': []}
    assert b[2] == {'image_states': 1, 'capacity_bits': 0, 'essential_sites': []}
    return {'Rule110_N5': a, 'Rule90_N4': b, 'status': 'PASS'}


def check_periodic_cover(max_t: int, max_period: int) -> dict:
    """Construct finite witnesses for *all* sites of I_t up to a chosen T.

    The test is finite but not bounded by a preselected observation interval:
    discrepancy supports are computed exactly on Z for each period background.
    """
    target = [set(range(-L(t), t + 1)) for t in range(max_t + 1)]
    found = [set() for _ in range(max_t + 1)]
    used_patterns: set[tuple[int, ...]] = set()
    for p in range(1, max_period + 1):
        for mask in range(1 << p):
            bg = tuple((mask >> i) & 1 for i in range(p))
            st = DefectState(bg, frozenset({0}))
            used = False
            for t in range(max_t + 1):
                matches = {-site for site in st.support} & (target[t] - found[t])
                if matches:
                    found[t].update(matches)
                    used = True
                if t < max_t:
                    st = step_defect(st)
            if used:
                used_patterns.add(bg)
    gaps = [(t, sorted(target[t] - found[t])) for t in range(max_t + 1)
            if found[t] != target[t]]
    return {'time_range': [0, max_t], 'max_background_period': max_period,
            'positions_requested': sum(map(len, target)),
            'positions_witnessed': sum(map(len, found)),
            'candidate_patterns_used': len(used_patterns),
            'first_uncovered': gaps[:8], 'full_coverage': not gaps}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', type=Path, default=Path('rule110_certificate.json'))
    ap.add_argument('--coverage-time', type=int, default=100)
    ap.add_argument('--coverage-period', type=int, default=6)
    args = ap.parse_args()
    assert args.coverage_time >= 0 and args.coverage_period >= 1
    certificate = {
        'kind': 'finite computation plus explicit general mathematical induction',
        'formal_kernel_checked': False,
        'local': check_local_truth_tables(),
        'periodic_defect': check_periodic_certificate(),
        'right_endpoint': check_right_endpoint_cases(),
        'finite_ring': check_finite_ring_examples(),
        'gapless_finite_horizon': check_periodic_cover(args.coverage_time,
                                                        args.coverage_period),
        'induction_obligations': [
            '3-step local independence => global upper bound by 3q+r decomposition',
            'F commutes with shifts and F^(t+s)=F^t ∘ F^s',
            'Y6=shift2(Y3) and B6=shift2(B3) => Y_(3+3k+r)=shift(2k)(Y_(3+r))',
            'singleton leftmost 1 advances one site left per step',
        ]
    }
    args.output.write_text(json.dumps(certificate, ensure_ascii=False, indent=2),
                           encoding='utf-8')
    print('PASS: ANF=8, derivative=4, local 3-step=128')
    print('PASS: 4-periodic defect, global shift recurrence finite base (t=3,6)')
    print('PASS: independent ring32 double-check, both endpoint constructions')
    print('PASS: ring counterexamples Rule110(N5) and Rule90(N4)')
    c = certificate['gapless_finite_horizon']
    print('COVERAGE:', c['positions_witnessed'], '/', c['positions_requested'],
          'period <=', args.coverage_period, 'max t=', args.coverage_time,
          'FULL' if c['full_coverage'] else f'GAPS={c["first_uncovered"]}')
    print('Certificate saved:', args.output)
    print('NOTE: general induction is a human-readable proof, not a Python runtime theorem.')


if __name__ == '__main__':
    main()
