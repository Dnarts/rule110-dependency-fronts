#!/usr/bin/env python3
"""Fast finite-range coverage audit using exact bit-parallel periodic rings.

No third-party dependencies. For each spatial period <= P and each word of
that period, run a full periodic ring containing a single toggled bit at 0.
The ring length N is a multiple of 1..P and N > 2*T+1, so its radius-T
light cone around a single defect does not interact with copies created
by the periodic boundary. The image of a defect on Z is therefore exact
up to time T. A target initial coordinate j corresponds to a defect at
output coordinate s=-j by translation-equivariance.

Finite computation only; not an all-time theorem.
"""
from __future__ import annotations
import argparse
import json
import math
from pathlib import Path


def step(state: int, n: int, mask: int) -> int:
    left = ((state << 1) | (state >> (n - 1))) & mask
    right = (state >> 1) | ((state & 1) << (n - 1))
    # f(0,c,r)=c OR r; f(1,c,r)=c XOR r.
    return ((~left & (state | right)) | (left & (state ^ right))) & mask


def audit(max_t: int, max_period: int) -> dict:
    if max_t < 0 or max_period <= 0:
        raise ValueError('T >= 0 and max-period >= 1 required')
    unit = math.lcm(*range(1, max_period + 1))
    n = unit * ((2 * max_t + 2) // unit + 1)
    assert n > 2 * max_t + 1
    mask = (1 << n) - 1
    covered = [0] * (max_t + 1)

    for p in range(1, max_period + 1):
        stride = mask // ((1 << p) - 1)  # repeat a length-p seed N/p times
        for seed in range(1 << p):
            bg = seed * stride
            u, v = bg, bg ^ 1
            for t in range(max_t + 1):
                covered[t] |= u ^ v
                if t < max_t:
                    u, v = step(u, n, mask), step(v, n, mask)

    gaps: list[dict] = []
    found = 0
    expected = 0
    for t, actual in enumerate(covered):
        L = t - t // 3
        right = (1 << (L + 1)) - 1
        left = ((1 << t) - 1) << (n - t) if t else 0
        needed = right | left  # spatial sites s ∈ [-t, L(t)]
        hit = needed & actual
        expected += needed.bit_count()
        found += hit.bit_count()
        miss = needed & ~actual
        if miss:
            missing = [s for s in range(-t, L + 1) if (miss >> (s % n)) & 1]
            gaps.append({'t': t, 'uncovered_output_sites': missing[:20],
                         'total_uncovered': len(missing)})
    return {'max_t': max_t, 'max_period': max_period,
            'ring_length': n, 'backgrounds_tested': sum(1 << p for p in range(1, max_period + 1)),
            'expected_pairs': expected, 'witnessed_pairs': found,
            'complete_finite_coverage': not gaps,
            'first_gaps': gaps[:8], 'times_with_gaps': len(gaps)}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--max-time', type=int, default=100)
    ap.add_argument('--max-period', type=int, default=6)
    ap.add_argument('--output', type=Path, default=Path('rule110_large_coverage.json'))
    args = ap.parse_args()
    result = audit(args.max_time, args.max_period)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps(result, ensure_ascii=False, indent=2))
    if not result['complete_finite_coverage']:
        print('NOTE: missing periodic witnesses is NOT a counterexample to essentiality.')

if __name__ == '__main__':
    main()
