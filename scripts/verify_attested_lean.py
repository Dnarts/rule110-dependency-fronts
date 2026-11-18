#!/usr/bin/env python3
"""Check user-provided Lean verification attestation without claiming a new Lean run."""
from pathlib import Path
import hashlib, re
ROOT=Path(__file__).resolve().parents[1]
attested=(ROOT/'verification/attested_source/rule110_complete.lean').read_bytes()
current=(ROOT/'formal/rule110_complete.lean').read_bytes()
report=(ROOT/'verification/reports/lean_check_status_supplied.txt').read_text()
digest=hashlib.sha256(attested).hexdigest()
assert digest in report, 'Input Lean source does not match reported SHA-256'
assert attested.split(b'-/',1)[1]==current.split(b'-/',1)[1], 'Proof source differs beyond introductory comment'
assert 'Exit code: 0' in report and 'Errors: 0' in report and 'Warnings: 0' in report
assert 'no sorryAx' in report
for thm in ('left_dependency_bound','right_dependency_bound','left_endpoint_essential','right_endpoint_essential'):
    assert 'Rule110Complete.'+thm in report, f'Missing reported axiom check: {thm}'
print('PASS: supplied Lean status source digest matches; current Lean code is comment-only update')
print('This is an attestation integrity check, NOT a local Lean compiler run.')
