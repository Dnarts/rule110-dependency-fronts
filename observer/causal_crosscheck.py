"""Independent bit-parallel certificate for one-bit perturbations and raw sensors."""
from collections import defaultdict
from itertools import product
import json


def step(word, n):
    mask = (1 << n) - 1
    left = ((word << 1) & mask) | (word >> (n - 1))
    right = (word >> 1) | ((word & 1) << (n - 1))
    return (word | right) ^ (left & word & right)


def trace(word, n, steps):
    result = [word]
    for _ in range(steps):
        result.append(step(result[-1], n))
    return result


def verify_no_early_gate():
    # Radius three gives a [-6,6] initial dependency interval for the
    # entire difference cone at time three. Padding by 3 on both sides
    # prevents wraparound into that cone for any of the inspected times.
    sensor = defaultdict(set)
    erased = 0
    for surround in range(1 << 12):
        baseline = ((surround & 63) | ((surround >> 6) << 7)) << 3
        u = trace(baseline, 19, 3)
        v = trace(baseline | (1 << 9), 19, 3)
        if u[-1] != v[-1]:
            continue
        erased += 1
        for t in range(3):
            for offset in range(-t,t+1):
                j = 9 + offset
                if ((u[t] ^ v[t]) >> j) & 1:
                    sensor[t,offset].add((u[t] >> j) & 1)
    assert all(len(signs) == 1 for signs in sensor.values())
    return erased, {str(key): next(iter(values)) for key,values in sensor.items()}


def verify_late_gate():
    words = ('011000010000000','011001010000000','110100010000101','110101010000101')
    streams = []
    for index, word in enumerate(words):
        n = len(word)
        history = trace(int(word[::-1], 2), n, 4)
        k,y = divmod(index,2)
        z = (history[2] >> 3) & 1
        assert (history[0] >> 5) & 1 == y
        assert (history[4] >> 13) & 1 == 1 and history[4] & 1 == k
        assert z == (k ^ y)
        observed = []
        for inject in (0,1):
            received = (history[4] & ~(1 << 14)) | (inject << 14)
            observed.append((step(received,n) >> 14) & 1)
        assert observed[z] == y and observed[1-z] == 1-y
        streams.append(history)
    for a,b in [(0,1),(2,3)]:
        u,v = streams[a],streams[b]
        assert u[0] ^ v[0] == 1 << 5 and u[4] == v[4]
        assert all(x!=w for x,w in zip(u[:4],v[:4]))
        assert all(((x^w) & ((1<<13)|(1<<14)|1)) == 0 for x,w in zip(u,v))
    return words


if __name__ == '__main__':
    n,s=verify_no_early_gate()
    print(json.dumps({'erased_environments_of_4096':n,'sensor_baseline_if_sensitive':s,
                      'horizon_4_witness':verify_late_gate()}, indent=2))
