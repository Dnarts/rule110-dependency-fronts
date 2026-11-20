"""Rebuild the observer’s committed bits, blinded stimuli, and their scores."""
import hashlib
import hmac
import json
import random
from pathlib import Path

ROOT = Path(__file__).resolve().parent
K = '10100110'
ARMS = ('live', 'flip', 'drop', 'shuffle', 'foreign', 'replay', 'fixed_query')
SEED = bytes.fromhex((ROOT / 'seed.txt').read_text().strip())


def generator(domain):
    stream = hmac.new(SEED, domain.encode(), 'sha256').digest()
    return random.Random(int.from_bytes(stream, 'big'))


def balanced(domain):
    values = [0, 0, 0, 0, 1, 1, 1, 1]
    generator(domain).shuffle(values)
    return values


def make_cases():
    mark = balanced('marked position')
    alternate = balanced('distractor at opposite address')
    foreign = balanced('marked positions of an independent run')
    shift = generator('nonidentity circular permutation').randint(1, 7)
    rows = []
    for arm in ARMS:
        for i, own in enumerate(map(int, K)):
            z = mark[i]
            if arm == 'flip':
                z = 1 - z
            elif arm == 'drop':
                z = None
            elif arm == 'shuffle':
                z = mark[(i + shift) % 8]
            elif arm == 'foreign':
                z = foreign[i]
            elif arm == 'fixed_query':
                z = alternate[i] if own else mark[i]
            rows.append(dict(arm=arm, source_index=i + 1, k=own, z=z, y=own ^ mark[i]))
    generator('blind row order').shuffle(rows)
    return rows


def transfer_challenges(rows):
    subset = []
    for arm in ARMS:
        indices = [i for i, row in enumerate(rows) if row['arm'] == arm]
        subset.extend(generator('subsample/' + arm).sample(indices, 2))
    generator('transfer order').shuffle(subset)
    cue = generator('transfer cues')
    return [(i + 1, cue.randrange(3)) for i in subset]


if __name__ == '__main__':
    rows = make_cases()
    public = [{'k':r['k'], 'z':r['z']} for r in rows]
    public_bytes = (json.dumps(public,separators=(',', ':')) + '\n').encode()
    (ROOT / 'stimuli.json').write_bytes(public_bytes)
    hidden_bytes = (json.dumps(rows,separators=(',', ':')) + '\n').encode()
    (ROOT / 'truth.json').write_bytes(hidden_bytes)
    print('CODE', hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('DATA', hashlib.sha256(hidden_bytes).hexdigest())
    for start in range(0,len(rows),8):
        chunk=rows[start:start+8]
        print(f"{start+1}-{start+8}", ''.join(str(r['k']) for r in chunk), ''.join('-' if r['z'] is None else str(r['z']) for r in chunk))
