"""Exhaust all 11-bit words of the zero-background experiment."""
from collections import defaultdict
from itertools import product
import json


def step(row):
    if not row:
        return frozenset()
    return frozenset(i for i in range(min(row) - 1, max(row) + 2)
                     if (4 * ((i - 1) in row) + 2 * (i in row) + ((i + 1) in row))
                     in {1, 2, 3, 5, 6})


def measure(word):
    first = frozenset(i for i, bit in enumerate(word) if bit == '1') | {11}
    states = [first]
    for _ in range(3):
        states.append(step(states[-1]))
    y = int(word[5])
    z = int(10 in states[2])
    local = tuple(int(0 in x) for x in states)
    after = (states[3] - {-1}) | ({-1} if z else set())
    return y, z, local, states[3], int(-1 in step(after))


def ambiguity(cells):
    for words_by_y in cells.values():
        if all(words_by_y.values()):
            return [words_by_y[y][0] for y in (0, 1)]
    return None


def run():
    original = ['10111010001', '10111110111', '11000010111', '11001100001']
    full = defaultdict(lambda: {0: [], 1: []})
    seen = defaultdict(lambda: {0: [], 1: []})
    local_xor = physical = causal_flips = 0
    for symbols in product('01', repeat=11):
        word = ''.join(symbols)
        y, z, local, final, readout = measure(word)
        full[final, z][y].append(word)
        seen[local, z][y].append(word)
        local_xor += (local[-1] ^ z) == y
        physical += readout == y
        if y == 0:
            causal_flips += z != measure(word[:5] + '1' + word[6:])[1]
    output = {
        'original': {word: measure(word)[:3] for word in original},
        'total_words': 2048,
        'xor_correct': local_xor,
        'local_cell_rule_correct': physical,
        'one_cell_interventions_on_x5': 1024,
        'interventions_that_changed_original_sensor': causal_flips,
        'counterexample_even_given_full_state_and_z': ambiguity(full),
        'counterexample_given_local_history_and_z': ambiguity(seen),
        'maximum_correct_any_decoder_full_final_and_z':
            sum(max(len(w) for w in cell.values()) for cell in full.values()),
        'maximum_correct_any_decoder_local_and_z':
            sum(max(len(w) for w in cell.values()) for cell in seen.values())
    }
    assert all(measure(w)[0] == measure(w)[4] for w in original)
    assert local_xor == 1024 and causal_flips == 0 and ambiguity(full)
    return output


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
