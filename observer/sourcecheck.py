#!/usr/bin/env python3
"""Independent Rule 110 witness check, using exact finite supports on Z.

Indices increase from left to right. JSON output is deterministic. No packages.
The periodic-tail identities are checked over all residues, separately from
the finite-support model. Extension to all return times uses finite speed.
"""
import json
from itertools import product

SEEDS = ("10111010001", "10111110111", "11000010111", "11001100001")
TAILS = ("1011", "1101")


def rule(left, center, right):
    if not center:
        return int(right)
    if not right:
        return 1
    return int(not left)


def evolve(support):
    """Outside the radius-one neighborhood of the support, all cells stay 0."""
    candidates = {i + offset for i in support for offset in (-1, 0, 1)}
    return {i for i in candidates if rule(i - 1 in support, i in support, i + 1 in support)}


def check(condition, message):
    if not condition:
        raise ValueError(message)


def row(seed, active):
    current = {i for i, bit in enumerate(seed) if bit == '1'}
    if active:
        current.add(11)
    history = [current]
    for _ in range(3):
        history.append(evolve(history[-1]))
    return history


def write_bit(support, i, value):
    return (support - {i}) | ({i} if value else set())


def grid(history, lo=-3, hi=11):
    return "".join(str(int(i in history)) for i in range(lo, hi + 1))


def check_witness():
    check([rule(*bits) for bits in product((0, 1), repeat=3)]
          == [(110 >> i) & 1 for i in range(8)], "incorrect local rule")
    y = [int(seed[5]) for seed in SEEDS]
    result = {}
    for active in (False, True):
        histories = [row(seed, active) for seed in SEEDS]
        k = [int(0 in history[3]) for history in histories]
        z = [int(10 in history[2]) for history in histories]
        h = ["".join(str(int(0 in state)) for state in history)
             for history in histories]
        output = [int(-1 in evolve(write_bit(history[3], -1, bit)))
                  for history, bit in zip(histories, z)]
        name = 'active' if active else 'passive'
        for a, b in ((0, 1), (2, 3)):
            check(histories[a][3] == histories[b][3], f'{name}: merge failed')
            check(all(histories[a][t] != histories[b][t] for t in range(3)),
                  f'{name}: early merge')
            check(h[a] == h[b] and y[a] != y[b], f'{name}: H alone suffices')
        check(histories[0][3] != histories[2][3], 'contexts should be distinct')
        check(k == [0, 0, 1, 1] and h == ['1100', '1100', '1101', '1101'],
              'wrong decoder context')
        check(all(-2 in history[3] for history in histories), 'gate left input')
        check(z == ([0, 1, 1, 0] if active else [1] * 4), 'unexpected probe')
        check(output == [key ^ bit for key, bit in zip(k, z)], 'gate incorrect')
        if active:
            check(output == y, 'readback failed')
            downstream = []
            for history, bit, fact in zip(histories, z, y):
                state4 = evolve(write_bit(history[3], -1, bit))
                flipped_return4 = evolve(write_bit(history[3], -1, 1 - bit))
                flipped_decoder4 = write_bit(state4, -1, 1 - int(-1 in state4))
                normal5 = evolve(state4)
                flipped_return5 = evolve(flipped_return4)
                flipped_decoder5 = evolve(flipped_decoder4)
                check(int(0 in normal5) == 1-fact and int(0 in flipped_return5) == fact,
                      'the next cell should depend on the returned bit')
                check((-2 in normal5) != (-2 in flipped_decoder5),
                      'a selective decoder flip should propagate to cell -2')
                downstream.append({'normal_cell0_t5': int(0 in normal5),
                                   'flipped_return_cell0_t5': int(0 in flipped_return5),
                                   'flipped_decoder_cell0_t5': int(0 in flipped_decoder5),
                                   'normal_cell_minus2_t5': int(-2 in normal5),
                                   'flipped_decoder_cell_minus2_t5': int(-2 in flipped_decoder5)})
            check([item['flipped_decoder_cell0_t5'] for item in downstream] == [0, 1, 1, 1],
                  'unexpected single-cell mediation')
            result['downstream'] = downstream
        if not active:
            sites = {}
            for time in range(3):
                # The union contains every site with bit 1 in some history.
                # Outside the union the observed bit is uniformly zero.
                locations = set.union(*(history[time] for history in histories))
                sites[time] = []
                for i in sorted(locations):
                    answers = [int(i in history[time]) for history in histories]
                    if answers[0] != answers[1] and answers[2] != answers[3]:
                        sites[time].append(i)
            check(sites == {0: [5, 8, 9], 1: [4, 7, 8, 9], 2: [3, 4]},
                  'unexpected passive ports')
            result['passive_ports_with_context_before_merger'] = sites
        result[name] = [
            dict(seed=seed, t0_to_t3_in_cells_minus3_to_11=[grid(s) for s in history],
                 H=h[j], K=k[j], Z=z[j], Y=y[j], returned_output=output[j])
            for j, (seed, history) in enumerate(zip(SEEDS, histories))]
    # Pair every eleven-bit seed with the seed differing only at initial cell 5.
    # At t<=3 cell 0 depends on [-3,3]; the t=2 probe depends on [8,12].
    # Hence these features carry zero information about an independent cell 5.
    history_counts = {}
    correct = 0
    for prefix in product('01', repeat=11):
        seed = ''.join(prefix)
        trajectory = row(seed, True)
        h = tuple(int(0 in state) for state in trajectory)
        bit = int(10 in trajectory[2])
        observed = h, bit
        fact = int(seed[5])
        counts = history_counts.setdefault(observed, [0, 0])
        counts[fact] += 1
        returned = write_bit(trajectory[3], -1, bit)
        correct += (int(-1 in evolve(returned)) == fact)
    check(all(zero == one for zero, one in history_counts.values()),
          'the joint observations must be balanced on the full seed class')
    check(correct == 1024, 'unexpected uniform accuracy')
    result['all_eleven_bit_seeds'] = {
        'total': 2048, 'distinct_observations': len(history_counts),
        'native_correct': correct, 'native_correct_excluding_original_four': correct - 4,
        'best_any_decoder_correct': sum(max(counts) for counts in history_counts.values())
    }
    # New counterfactually paired witness. Within each pair only bit 5 differs.
    # The passive first probe is inside the one-step cone of cell 5.
    early_pairs = []
    for bits in product('01', repeat=11):
        seed = ''.join(bits)
        if seed[5] == '1':
            continue
        alternate = seed[:5] + '1' + seed[6:]
        if row(seed, False)[3] == row(alternate, False)[3]:
            early_pairs.append([seed, alternate])
    check(early_pairs == [['10111010000', '10111110000'],
                          ['10111010001', '10111110001']],
          'unexpected early counterfactually paired mergers')
    result['all_pure_x5_pairs_merged_by_t3'] = early_pairs
    causal_seeds = ('01100001000', '01100101000', '10111010000', '10111110000')
    causal_histories = []
    causal_rows = []
    for idx, seed in enumerate(causal_seeds):
        history = row(seed, False)
        history.append(evolve(history[-1]))
        causal_histories.append(history)
        fact = int(seed[5])
        context = int(-1 in history[4])
        bit = int(4 in history[1])
        local_trace = ''.join(str(int(-1 in state)) for state in history)
        check(context == idx // 2 and fact == idx % 2, 'missing K/Y combination')
        check(bit == fact ^ context and -3 in history[4], 'new encoding failed')
        decoded = evolve(write_bit(history[4], -2, bit))
        inverted = evolve(write_bit(history[4], -2, 1-bit))
        check(int(-2 in decoded) == fact and int(-2 in inverted) == 1-fact,
              'new native decoder failed')
        causal_rows.append(dict(seed=seed, K=context, Y=fact, Z=bit, H=local_trace,
                                returned_output=int(-2 in decoded),
                                t0_to_t4_in_cells_minus4_to_10=[grid(s,-4,10) for s in history]))
    for a, b, first_merge in ((0, 1, 4), (2, 3, 3)):
        ha, hb = causal_histories[a], causal_histories[b]
        check(ha[0] ^ hb[0] == {5}, 'the manipulation must change only Y')
        check(causal_rows[a]['H'] == causal_rows[b]['H'], 'local trace leaked Y')
        check(next(t for t in range(5) if ha[t] == hb[t]) == first_merge,
              'incorrect merger chronology')
    result['new_causally_paired_witness'] = causal_rows
    for k, tail in enumerate(TAILS):
        a = tuple(map(int, tail))
        b = tuple(rule(a[j-1], a[j], a[(j+1) % 4]) for j in range(4))
        check(b == a[2:] + a[:2], 'the periodic carrier must shift by two')
        # With tail beginning at i=20, r=20+2T and all T>=3,
        # r±1 at time T depend entirely on tail cells (r-1-T>=20).
        # State there equals a[(r±1-20+2T) % 4], i.e. a[3] and a[1].
        check(a[3] == 1 and a[1] == k, 'incorrect asymptotic gate')
        for bit in (0, 1):
            check(rule(a[3], bit, a[1]) == bit ^ k, 'asymptotic gate failure')
    result['tail'] = {'phase_at_20': list(TAILS), 'periodic_step_phase_offset': 2,
                      'write_cell_at_T': '20+2*T', 'return_time': 'T+1'}
    return result


if __name__ == '__main__':
    print(json.dumps(check_witness(), indent=2, ensure_ascii=False))
