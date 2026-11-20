"""Check frozen trial materials and score the two actual solver outputs."""
import collections
import hashlib
import json

from trial import ARMS, K, ROOT, SEED, make_cases, transfer_challenges

SEED_SHA = 'b6e41b57b4000728c5da5d9011c5302de9a553082942822134447ecdc7409396'
CODE_SHA = '05545d5e655572a91642ccef52f2e875398a5d8fbe4af35d6c5a20531531d078'
KEY_SHA = '43ed3e654a2366165c92e983810dfa7f0cbeb8d82bef640d56b0ca67a64d7546'


def summarize():
    rows = make_cases()
    truth = (json.dumps(rows, separators=(',', ':')) + '\n').encode()
    assert hashlib.sha256(SEED).hexdigest() == SEED_SHA
    assert hashlib.sha256((ROOT / 'trial.py').read_bytes()).hexdigest() == CODE_SHA
    assert hashlib.sha256(truth).hexdigest() == KEY_SHA
    assert (ROOT / 'truth.json').read_bytes() == truth
    public = [{'k':case['k'], 'z':case['z']} for case in rows]
    assert public == json.loads((ROOT / 'stimuli.json').read_text())
    report = json.loads((ROOT / 'answers.json').read_text())
    assert K == report['k']
    ys = ''.join(report['reports'].split())
    actions = ''.join(report['actions'].split())
    assert len(ys) == len(rows) and set(ys) <= set('01?')
    transfer = transfer_challenges(rows)
    assert len(actions) == len(transfer) and set(actions) <= set('012?')
    counts = {arm:collections.Counter() for arm in ARMS}
    for char, row in zip(ys, rows):
        cnt = counts[row['arm']]
        cnt['n'] += 1
        cnt['correct'] += char == str(row['y'])
        cnt['abstain'] += char == '?'
        received = '?' if row['z'] is None else str(row['k'] ^ row['z'])
        cnt['decoded_as_instructed'] += char == received
    for action, (caseid, cue) in zip(actions, transfer):
        row=rows[caseid-1]
        cnt=counts[row['arm']]
        cnt['transfer_n'] += 1
        cnt['transfer_correct'] += action == str((cue+1+row['y'])%3)
        cnt['transfer_abstain'] += action == '?'
        report_y = ys[caseid-1]
        report_action = '?' if report_y == '?' else str((cue+1+int(report_y))%3)
        cnt['transfer_matches_own_estimate'] += action == report_action
    return {arm:dict(vals) for arm,vals in counts.items()}


if __name__ == '__main__':
    print(json.dumps(summarize(), indent=2))
