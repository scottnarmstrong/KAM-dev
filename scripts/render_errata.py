#!/usr/bin/env python3
"""Render the working errata and deviations record docs/errata/working-record.md from docs/errata/ledger.json.

usage: scripts/render_errata.py [--check]

The rendered file is the campaign's working record. Before release it is rewritten in reader-facing language and
every erratum is verified against the pinned PDF by its writer and an independent verifier (see the
lean-orchestrator skill, references/errata-and-deviations.md).
"""
import argparse
import json
import sys
from pathlib import Path

root = Path(__file__).resolve().parent.parent
ledger = json.loads((root / 'docs/errata/ledger.json').read_text())
sources = {s['key']: s for s in json.loads((root / 'docs/sources.json').read_text())['sources']}
target = root / 'docs/errata/working-record.md'

INTRO = """# Errata and deviations

*Working record, generated from the findings ledger [`ledger.json`](ledger.json) by
`scripts/render_errata.py`; do not edit by hand. The reader-facing record is [`ERRATA-AND-DEVIATIONS.md`](../ERRATA-AND-DEVIATIONS.md); every
erratum is verified against the pinned PDF by its writer and then by an independent refute-first verifier. Until
then an erratum marked CANDIDATE is a report to check, not a claim.*

**Policy.** {policy}

Locations refer to the pinned versions in [`sources.json`](../sources.json); counts are of entries, not occurrences.
"""


def pinned(key):
    s = sources.get(key)
    if not s:
        return key
    v = f'arXiv:{s["arxiv"]}' if s.get('arxiv') else (f'doi:{s["doi"]}' if s.get('doi') else 'pinned PDF')
    return f'{key} ({v})'


def render():
    entries = ledger['entries']
    keys = []
    for e in entries:
        if e['source'] not in keys:
            keys.append(e['source'])
    out = [INTRO.format(policy=ledger['policy']), '## Count', '',
           '| Source | Errata | Deviations |', '|---|---|---|']
    for k in keys:
        er = [e for e in entries if e['source'] == k and e['type'] == 'erratum' and e['status'] != 'DROPPED']
        dv = [e for e in entries if e['source'] == k and e['type'] == 'deviation' and e['status'] != 'RETIRED']
        cand = sum(1 for e in er if e['status'] == 'CANDIDATE')
        out.append(f'| {pinned(k)} | {len(er)}' + (f' ({cand} candidate)' if cand else '') + f' | {len(dv)} |')
    for k in keys:
        out += ['', f'## {pinned(k)}', '']
        for kind, title in (('erratum', 'Errata'), ('deviation', 'Deviations')):
            out += [f'### {title}', '']
            sel = [e for e in entries if e['source'] == k and e['type'] == kind]
            if not sel:
                out += ['None.', '']
                continue
            for i, e in enumerate(sel, 1):
                printed = f' Printed: {e["printed"]}.' if e.get('printed') else ''
                ev = f' Evidence: {e["evidence"]}.' if e.get('evidence') else ''
                out.append(f'{i}. **{e["location"]}.** *{e["kind"]}; {e["status"]}* ({e["id"]}).{printed} '
                           f'{e["claim"].rstrip(".")}.{ev} Effect: {e.get("effect", "to be determined")}.')
            out.append('')
    return '\n'.join(out).rstrip() + '\n'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--check', action='store_true')
    a = ap.parse_args()
    text = render()
    if a.check:
        if not target.exists() or target.read_text() != text:
            print('docs/errata/working-record.md is out of date; run scripts/render_errata.py', file=sys.stderr)
            return 1
        return 0
    target.write_text(text)
    return 0


if __name__ == '__main__':
    sys.exit(main())
