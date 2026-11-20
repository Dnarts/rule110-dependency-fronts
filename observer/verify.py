"""Verify the archive and recalculate every computational certificate."""
import csv
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def execute(script, *args):
    result = subprocess.run([sys.executable, '-E', '-B', str(ROOT / script), *args],
                            cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f"{script} failed\n{result.stdout}\n{result.stderr}")
    print(f"OK  {script}")
    return result.stdout


def main():
    if not __debug__:
        raise RuntimeError('Run Python without -O')
    for row in (ROOT / 'sha256.txt').read_text().splitlines():
        digest, relative = row.split('  ', 1)
        actual = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
        if actual != digest:
            raise RuntimeError(f'Changed file: {relative}')
    seen = set()
    with (ROOT / 'hypotheses.tsv').open(encoding='utf-8') as f:
        for row in csv.DictReader(f,delimiter='\t'):
            if row['id'] in seen:
                raise ValueError(row['id'])
            if row['depends_on'] != '-' and not set(row['depends_on'].split(';')) <= seen:
                raise ValueError(row['depends_on'])
            if not (ROOT / row['evidence'].split('#')[0]).is_file():
                raise FileNotFoundError(row['evidence'])
            seen.add(row['id'])
    print(f'OK  hashes and {len(seen)} claims')
    for script in ('sourcecheck.py','domain.py','causal_crosscheck.py','causal_line.py',
                   'local_return.py','autonomous.py'):
        record=json.loads(execute(script))
        if not record:
            raise ValueError(script)
    cert=json.loads(execute('new/verify_witnesses.py'))
    if cert != json.loads((ROOT/'new/witnesses_certificate.json').read_text()):
        raise ValueError('Ring certificate does not reproduce')
    scores=json.loads(execute('ai/score.py'))
    if scores != json.loads((ROOT/'ai/result.json').read_text()):
        raise ValueError('Recorded scores do not reproduce')
    answer=json.loads((ROOT/'ai/replay_run/answers.json').read_text())
    replay=execute('ai/replay.py','score',answer['k'],answer['q'],answer['actions'])
    if replay.strip() != (ROOT/'ai/replay_run/result.txt').read_text().strip():
        raise ValueError('Tape scoring mismatch')
    cal=execute('ai/verify_calibrate.py')
    if cal.strip() != (ROOT/'ai/calibration/result.txt').read_text().strip():
        raise ValueError('Calibration scoring mismatch')
    print(execute('leaf/render_leaf.py').strip())
    print('All computational checks passed.')

if __name__ == '__main__':
    main()
