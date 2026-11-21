#!/usr/bin/env python3
"""Independent finite checks, using only the numbered elementary-rule table.

These computations complement the Lean induction proofs. They do not replace
the proofs for unbounded time, arbitrary infinite tails, or infinite streams.
Run from any directory; Python 3.10+ and the standard library are sufficient.
"""

from __future__ import annotations

import argparse
from collections import deque
from fractions import Fraction
from itertools import product
import json
import math
from pathlib import Path


def local(rule: int, left: int, center: int, right: int) -> int:
    return (rule >> (4 * left + 2 * center + right)) & 1


def strip_step(bits: tuple[int, ...], rule: int = 110) -> tuple[int, ...]:
    return tuple(local(rule, *bits[i : i + 3]) for i in range(len(bits) - 2))


def ring_step(state: int, size: int, rule: int = 110) -> int:
    return sum(
        local(rule, (state >> ((i - 1) % size)) & 1,
              (state >> i) & 1, (state >> ((i + 1) % size)) & 1) << i
        for i in range(size)
    )


def line_step(ones: frozenset[int], rule: int = 110) -> frozenset[int]:
    assert local(rule, 0, 0, 0) == 0
    if not ones:
        return frozenset()
    return frozenset(i for i in range(min(ones) - 1, max(ones) + 2)
                     if local(rule, int(i - 1 in ones), int(i in ones),
                              int(i + 1 in ones)))


def check_ring() -> dict:
    maps = [list(range(128))]
    for _ in range(21):
        maps.append([ring_step(u, 7) for u in maps[-1]])
    counts = [len(set(m)) for m in maps[:8]]
    supports = [[j for j in range(7)
                 if any((m[u] & 1) != (m[u ^ (1 << j)] & 1)
                        for u in range(128))] for m in maps]
    assert counts == [128, 79, 50, 43, 36, 29, 22, 15]
    assert list(map(len, supports[:8])) == [1, 3, 5, 6, 7, 7, 7, 7]
    assert maps[21] == maps[7]
    cycle = [13, 79, 104, 124, 70, 103, 52, 62, 35, 115, 26, 31, 81, 121]
    assert len(set(cycle)) == 14
    assert [ring_step(u, 7) for u in cycle] == cycle[1:] + cycle[:1]
    assert set(maps[7]) == {0, *cycle}
    assert maps[6][5] == 88 and 88 not in set(maps[7])
    witnesses = []
    for t in range(7, 21):
        assert supports[t] == list(range(7))
        for j in range(7):
            u = next(u for u in range(128)
                     if (maps[t][u] & 1) != (maps[t][u ^ (1 << j)] & 1))
            witnesses.append({"time": t, "coordinate": j, "input": u})
    r90 = list(range(256))
    for _ in range(4):
        r90 = [ring_step(u, 8, 90) for u in r90]
    assert set(r90) == {0}
    return {"image_sizes_t0_to_7": counts,
            "essential_counts_t0_to_7": list(map(len, supports[:8])),
            "eventual_image": sorted(set(maps[7])), "cycle": cycle,
            "complete_map_identity": "F^21 = F^7 on all 128 inputs",
            "transient_witness": {"input": 5, "time": 6, "output": 88},
            "essential_witnesses": witnesses,
            "rule90_ring8_image_after_4": [0]}


def check_merge3() -> dict:
    environments = []
    orientations: dict[tuple[int, int], set[tuple[int, int]]] = {}
    positions = list(range(-6, 0)) + list(range(1, 7))
    for env in product((0, 1), repeat=12):
        arrays = []
        histories = []
        for y in (0, 1):
            bits = env[:6] + (y,) + env[6:]
            history = [bits]
            for _ in range(3):
                history.append(strip_step(history[-1]))
            histories.append(history)
            arrays.append(history[3])
        merged = arrays[0] == arrays[1]
        fixed = {p: b for p, b in zip(positions, env)}
        pattern = all(fixed[p] == b for p, b in
                      {-5: 1, -4: 0, -3: 1, -2: 1, -1: 1,
                       1: 1, 2: 0, 3: 0, 4: 0}.items())
        assert merged == pattern
        if merged:
            environments.append(''.join(map(str, env[:6])) + '[Y]' +
                                ''.join(map(str, env[6:])))
            for t in range(3):
                for s in range(-t, t + 1):
                    pair = tuple(histories[y][t][s + 6 - t] for y in (0, 1))
                    if pair[0] != pair[1]:
                        orientations.setdefault((t, s), set()).add(pair)
    assert len(environments) == 8
    assert all(len(values) == 1 for values in orientations.values())
    return {"environments_checked": 4096,
            "merging_environments": environments,
            "pattern": "*10111[Y]1000**",
            "sensitive_sensor_orientations":
                [{"time": t, "site": s, "outputs_at_y0_y1": list(next(iter(v)))}
                 for (t, s), v in sorted(orientations.items())]}


WORDS = {
    (0, 0): '00000001100001000000',
    (0, 1): '00000001100101000000',
    (1, 0): '00010111010001000010',
    (1, 1): '00010111010101000010',
}


def check_witnesses() -> dict:
    trajectories = {}
    for ky, word in WORDS.items():
        rows = [frozenset(i - 6 for i, b in enumerate(word) if b == '1')]
        for _ in range(4):
            rows.append(line_step(rows[-1]))
        trajectories[ky] = rows
    table = []
    for (k, y), rows in trajectories.items():
        z = int(3 in rows[2])
        assert int(5 in rows[0]) == y
        assert z == k ^ y
        assert int(0 in rows[4]) == k and -2 in rows[4]
        assert -4 not in rows[0]
        for q in (0, 1):
            written = q ^ z
            patched = (rows[4] - {-1}) | ({-1} if written else set())
            after = line_step(frozenset(patched))
            assert int(-1 in after) == q ^ y
            assert -4 in after
        table.append({"context": k, "target": y, "sensor": z,
                      "return_with_q0": int(-1 in line_step(frozenset(
                          (rows[4] - {-1}) | ({-1} if z else set()))))})
    for k in (0, 1):
        a, b = trajectories[(k, 0)], trajectories[(k, 1)]
        assert a[0] ^ b[0] == {5}
        assert a[3] != b[3] and a[4] == b[4]
    schedules = 0
    for n in range(5):
        for eps in product(WORDS, repeat=n):
            for q0 in (0, 1):
                q, qinv, parity = q0, 1 ^ q0, q0
                for k, y in eps:
                    z = k ^ y
                    old = q
                    q ^= z
                    qinv ^= z
                    parity ^= z
                    out, outinv = q ^ k, qinv ^ k
                    assert q == parity and out == old ^ y and outinv == 1 ^ out
                schedules += 1
    return {"table": table, "merge_time": 4, "return_time": 5,
            "initial_pair_difference": [5],
            "finite_stream_checks_including_two_initial_bits": schedules,
            "stream_output_identity": "O_n = q_n XOR Y_n",
            "reset_witness": {"coordinate": -4, "after_return": 1,
                              "next_initial_word": 0}}


def check_seam() -> dict:
    ether = [16072]
    for _ in range(7):
        ether.append(ring_step(ether[-1], 14))
    assert ether[-1] == ether[0]
    assert ether[:7] == [16072, 9196, 12862, 15139, 4018, 2299, 11407]

    def bit(t: int, x: int) -> int:
        return (ether[t % 7] >> (x % 14)) & 1

    initials = [(0, p, tuple(bit(0, p + i) for i in range(4))) for p in (0, 7)]
    seen = set(initials)
    todo = deque(initials)
    transitions = []
    while todo:
        t, r, window = node = todo.popleft()
        for tail in (0, 1):
            nine = tuple(bit(t, r + i) for i in range(-4, 0)) + window + (tail,)
            five = strip_step(strip_step(nine))
            assert five[0] == bit(t + 2, r - 2)
            successor = ((t + 2) % 7, (r - 1) % 14, five[1:])
            transitions.append({"state": node, "new_bit": tail,
                                "seam": five[0], "successor": successor})
            if successor not in seen:
                seen.add(successor)
                todo.append(successor)
    assert len(seen) == 63 and len(transitions) == 126
    for t in range(7):
        assert any(bit(t, x) != bit(t, x + 7) for x in range(14))
    t, r, window = initials[0]
    nine = tuple(bit(t, r + i) for i in range(-4, 0)) + window + (0,)
    mirror = strip_step(strip_step(nine, 124), 124)[0]
    assert mirror == 0 and bit(2, -2) == 1
    return {"ether_rows": ether[:7], "reachable_nodes": len(seen),
            "checked_transitions": len(transitions),
            "states": sorted(seen), "transitions": transitions,
            "rule124_negative_control": {"actual": mirror, "required": 1}}


def mutual_information(joint: dict) -> float:
    pa, pb = {}, {}
    for (a, b), p in joint.items():
        pa[a] = pa.get(a, 0) + p
        pb[b] = pb.get(b, 0) + p
    return sum(float(p) * math.log2(float(p / (pa[a] * pb[b])))
               for (a, b), p in joint.items() if p)


def check_channel_bridge() -> dict:
    """Separate derived examples; these are not claimed as Lean theorems."""
    yz, yk, ykz, actual, reference = {}, {}, {}, {}, {}
    for k, y in product((0, 1), repeat=2):
        z, h, p = k ^ y, (k, y), Fraction(1, 4)
        for target, key in [(yz, (y, z)), (yk, (y, k)), (ykz, (y, (k, z))),
                            (actual, (h, (k, k ^ z)))]:
            target[key] = target.get(key, 0) + p
        for a in (0, 1):
            key = (h, (k, k ^ a))
            reference[key] = reference.get(key, 0) + Fraction(1, 8)
    values = {"I_Y_Z": mutual_information(yz), "I_Y_K": mutual_information(yk),
              "I_Y_KZ": mutual_information(ykz),
              "I_H_Hprime_actual": mutual_information(actual),
              "I_H_Hprime_reference": mutual_information(reference)}
    assert values == {"I_Y_Z": 0.0, "I_Y_K": 0.0, "I_Y_KZ": 1.0,
                      "I_H_Hprime_actual": 2.0, "I_H_Hprime_reference": 1.0}
    values["Lambda_strict"] = 1.0
    return {"assumption": "four histories equiprobable; fair independent K,Y",
            "values_bits": values,
            "scope": "derived finite illustration, not an application of B/B-prime"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'build/finite-checks.json')
    args = parser.parse_args()
    report = {"rule_definition": "(rule >> (4*l+2*c+r)) & 1",
              "ring": check_ring(), "merge3": check_merge3(),
              "four_histories": check_witnesses(), "seam": check_seam(),
              "derived_channel_bridge": check_channel_bridge(), "status": "PASS"}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print('PASS: ring7 image/period/98 witnesses; 4096 merge environments;')
    print('four histories and streams; 63 seam states/126 transitions; channel bridge.')
    print(f'Report: {args.output}')


if __name__ == '__main__':
    main()
