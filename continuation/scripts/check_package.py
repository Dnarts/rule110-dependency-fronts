#!/usr/bin/env python3
"""Check publication identities, source/log binding, and local Markdown links."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def anchors(path: Path) -> set[str]:
    text = path.read_text()
    found = set(re.findall(r'<a\b[^>]*\b(?:id|name)=["\']([^"\']+)', text))
    used = {}
    for title in re.findall(r'^#{1,6}\s+(.+?)\s*#*$', text, flags=re.M):
        title = re.sub(r'<[^>]+>', '', title).strip().lower()
        title = re.sub(r'[^\w\s-]', '', title)
        base = re.sub(r'\s', '-', title)
        n = used.get(base, 0)
        used[base] = n + 1
        found.add(base if n == 0 else f'{base}-{n}')
    return found


def main() -> None:
    checked = 0
    manifest = json.loads((ROOT / 'archive/supplied/manifest.json').read_text())
    for entry in manifest:
        path = ROOT / entry['archived_path']
        assert path.stat().st_size == entry['bytes'], path
        assert digest(path) == entry['sha256'], path
    for name in ('Rule110ChiralSeam', 'Rule110RingDecoupling',
                 'MergeMinimality4', 'ContinuousSubject110'):
        assert (ROOT / f'lean/{name}.lean').read_bytes() == (
            ROOT / f'archive/supplied/{name}.lean').read_bytes(), name
    assert (ROOT / 'paper/rule110-continuation-ru.pdf').read_bytes() == (
        ROOT / 'archive/supplied/rule110-continuation-ru.pdf').read_bytes()

    audit = json.loads((ROOT / 'verification/current/lean-check.json').read_text())
    assert audit['status'] == 'PASS'
    assert audit['runner_sha256'] == digest(ROOT / 'scripts/verify_lean.py')
    assert audit['total_distinct_audit_reports'] == 79
    assert audit['observed_axioms'] == ['Quot.sound', 'propext']
    assert len(audit['modules']) == 7
    for item in audit['modules']:
        assert digest(ROOT / item['source']) == item['source_sha256'], item['source']
        assert digest(ROOT / 'verification/current' / item['log']) == item['log_sha256']
        assert item['exit_code'] == 0

    finite = json.loads((ROOT / 'verification/finite-checks.json').read_text())
    assert finite['status'] == 'PASS'
    assert finite['seam']['reachable_nodes'] == 63
    assert finite['seam']['checked_transitions'] == 126

    documents = [p for p in ROOT.rglob('*.md') if 'build' not in p.relative_to(ROOT).parts]
    documents.append(REPO / 'README.md')
    for source in documents:
        text = source.read_text()
        assert '<!-- ROOT:' not in text, source
        for raw in re.findall(r'\[[^\]]+\]\(([^)]+)\)', text):
            url = urlsplit(raw)
            if url.scheme in ('http', 'https', 'mailto'):
                continue
            assert not url.scheme, (source, raw)
            target = (source.parent / unquote(url.path)).resolve() if url.path else source
            assert target.exists(), f'{source.relative_to(REPO)}: missing {raw}'
            assert target == REPO or REPO in target.parents, (source, raw)
            if url.fragment:
                assert target.is_file() and target.suffix == '.md', (source, raw)
                assert unquote(url.fragment) in anchors(target), (
                    f'{source.relative_to(REPO)}: missing anchor {raw}')
            checked += 1

    checksum_path = ROOT / 'SHA256SUMS'
    assert checksum_path.exists(), 'Generate the publication SHA256SUMS before this check.'
    listed = set()
    for line in checksum_path.read_text().splitlines():
        expected, relative = line.split('  ', 1)
        assert relative not in listed
        listed.add(relative)
        assert digest(ROOT / relative) == expected, f'Checksum mismatch: {relative}'
    published = {str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file()
                 and p.name != 'SHA256SUMS'
                 and not any(x in ('build', '__pycache__') for x in p.relative_to(ROOT).parts)
                 and p.suffix not in ('.olean', '.ilean', '.pyc')}
    assert listed == published, 'Checksum inventory differs from publication files.'
    print(f'PASS: {len(manifest)} supplied identities, four unchanged proof sources,')
    print(f'79-report source/log binding, {checked} local Markdown links,')
    print(f'and {len(listed)} complete publication checksums.')


if __name__ == '__main__':
    main()
