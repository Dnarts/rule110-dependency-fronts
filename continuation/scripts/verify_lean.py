#!/usr/bin/env python3
"""Build every continuation module from source and audit its actual dependencies.

No Mathlib, network access, supplied .olean files, or historical logs are used.
The four mathematical modules are compiled before their audit/threshold imports.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    ('Rule110ChiralSeam', 0),
    ('Rule110RingDecoupling', 0),
    ('MergeMinimality4', 11),
    ('ContinuousSubject110', 24),
    ('AxiomAudit', 22),
    ('RingAxiomAudit', 19),
    ('MergeThreshold', 3),
]
ALLOWED_AXIOMS = {'propext', 'Quot.sound'}
CRITICAL = {
    'Rule110ChiralSeam.counterfactual_donor_swap_G5_1',
    'Rule110RingDecoupling.ring7_exact_image_size',
    'Rule110RingDecoupling.ring7_minimal_preperiod',
    'Rule110RingDecoupling.ring7_minimal_common_period',
    'Rule110RingDecoupling.ring7_all_bits_essential_all_time',
    'MergeMinimality4.global_merge3_iff_pattern',
    'ContinuousSubject110.infinite_witness_stream',
    'ContinuousSubject110.witness_restart_coordinate',
    'MergeThreshold.four_is_least',
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def expected_names(source: str) -> set[str]:
    namespace = re.search(r'^namespace\s+(\S+)', source, re.M)
    prefix = namespace.group(1) + '.' if namespace else ''
    names = re.findall(r'^#print axioms\s+(\S+)\s*$', source, re.M)
    return {name if '.' in name else prefix + name for name in names}


def parse_axioms(output: str) -> dict[str, list[str]]:
    reports = {}
    pattern = r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, output):
        name = match.group(1)
        if name in reports:
            raise RuntimeError(f'Duplicate axiom report: {name}')
        axioms = [] if match.group(2) is None else [
            x.strip() for x in match.group(2).split(',') if x.strip()]
        if not set(axioms) <= ALLOWED_AXIOMS:
            raise RuntimeError(f'Unapproved proof dependency for {name}: {axioms}')
        reports[name] = axioms
    return reports


def requested_name(printed_name: str) -> str:
    # Lean reports private helpers by their generated internal name. Preserve
    # that name in the record, but compare the source-visible qualified name.
    return re.sub(r'^_private\.[^.]+\.\d+\.', '', printed_name)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default=os.environ.get('LEAN', 'lean'),
                        help='Lean 4.35.0 executable (or set LEAN)')
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'build/verification')
    parser.add_argument('--timeout', type=int, default=1200,
                        help='maximum seconds per module')
    args = parser.parse_args()
    launcher = shutil.which(args.lean)
    if launcher is None:
        raise SystemExit('Lean not found. Install the version in lean-toolchain or pass --lean.')
    # Resolve an elan proxy while the package's lean-toolchain is in scope.
    # Keep the launcher's name intact: resolving a proxy symlink first could
    # change elan's dispatch. Use the actual compiler after changing cwd.
    launcher = str(Path(launcher).absolute())
    prefix = subprocess.check_output([launcher, '--print-prefix'], cwd=ROOT,
                                     text=True, timeout=60).strip()
    executable = 'lean.exe' if os.name == 'nt' else 'lean'
    compiler = Path(prefix) / 'bin' / executable
    if not compiler.is_absolute() or not compiler.is_file():
        raise SystemExit(f'Lean returned an invalid installation prefix: {prefix!r}')
    lean = str(compiler.resolve())
    version = subprocess.check_output([lean, '--version'], cwd=ROOT,
                                      text=True, timeout=60).strip()
    if not re.search(r'\bversion 4\.35\.0\b', version):
        raise SystemExit(f'Expected Lean 4.35.0; observed: {version}')
    outdir = args.output_dir.resolve()
    outdir.mkdir(parents=True, exist_ok=True)
    report = {
        'status': 'RUNNING', 'started_utc': datetime.now(timezone.utc).isoformat(),
        'toolchain': version, 'dependencies': 'Lean core only; no Mathlib',
        'runner_sha256': sha256(Path(__file__)),
        'allowed_axioms': sorted(ALLOWED_AXIOMS),
        'fresh_build': True, 'modules': [],
    }
    all_axioms = {}
    report_path = outdir / 'lean-check.json'
    try:
        with tempfile.TemporaryDirectory(prefix='rule110-continuation-') as temp:
            build = Path(temp)
            env = os.environ.copy()
            env['LEAN_PATH'] = str(build)
            for module, count in MODULES:
                source_path = ROOT / 'lean' / f'{module}.lean'
                source = source_path.read_text()
                expected = expected_names(source)
                if len(expected) != count:
                    raise RuntimeError(f'{module}: expected {count} audit commands, found {len(expected)}')
                start = time.monotonic()
                command = [lean, '-j', '1', f'--root={ROOT / "lean"}',
                           '-o', str(build / f'{module}.olean'), str(source_path)]
                result = subprocess.run(command, cwd=build, env=env, text=True,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                        timeout=args.timeout)
                output = result.stdout
                log_path = outdir / f'{module}.log'
                log_path.write_text(output)
                record = {
                    'module': module, 'source': f'lean/{module}.lean',
                    'source_sha256': sha256(source_path),
                    'exit_code': result.returncode,
                    'duration_seconds': round(time.monotonic() - start, 3),
                    'log': log_path.name, 'log_sha256': sha256(log_path),
                    'warnings': len(re.findall(r'\bwarning:', output)),
                }
                report['modules'].append(record)
                if result.returncode != 0 or re.search(r'\berror:', output):
                    raise RuntimeError(f'{module}: compiler failure; see {log_path}')
                if 'sorryAx' in output or 'declaration uses \'sorry\'' in output:
                    raise RuntimeError(f'{module}: unproved declaration in compiler output')
                audited = parse_axioms(output)
                if {requested_name(name) for name in audited} != expected:
                    raise RuntimeError(f'{module}: printed declarations do not match requested audit')
                if set(audited) & set(all_axioms):
                    raise RuntimeError(f'{module}: duplicate declarations across audits')
                record['audit_count'] = len(audited)
                record['axioms'] = audited
                all_axioms.update(audited)
                print(f'PASS {module}: {len(audited)} audit reports, {record["warnings"]} warnings', flush=True)
        if len(all_axioms) != 79 or not CRITICAL <= set(all_axioms):
            raise RuntimeError('The final audit does not cover all 79 declarations and all critical results')
        report['status'] = 'PASS'
        report['total_distinct_audit_reports'] = len(all_axioms)
        report['observed_axioms'] = sorted({a for aa in all_axioms.values() for a in aa})
        print('PASS: all seven modules rebuilt; 79 distinct reports; only propext and Quot.sound.')
    except Exception as error:
        report['status'] = 'FAIL'
        report['failure'] = str(error)
        raise
    finally:
        report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')


if __name__ == '__main__':
    main()
