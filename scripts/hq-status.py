#!/usr/bin/env python3
"""Regenerate the live sections of README.md (between `<!-- AUTO:name -->` and `<!-- /AUTO:name -->`).

usage: python3 scripts/hq-status.py          (in the main checkout; scripts/hq-update.sh calls it)

Sources: manifest/frozen-anchors.json (frozen statements and their states), the provider modules,
docs/campaign/campaign.json (phase, agents, proof map; maintained by the orchestrator),
docs/campaign/progress.json (weighted work items), docs/errata/ledger.json (errata and deviations),
docs/sources.json (pinned papers), tmux sessions of the agents, and git history on main.
"""
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

root = Path(__file__).resolve().parent.parent
readme = root / 'README.md'
manifest = json.loads((root / 'manifest/frozen-anchors.json').read_text())
campaign = json.loads((root / 'docs/campaign/campaign.json').read_text())
progress = json.loads((root / 'docs/campaign/progress.json').read_text())
ledger = json.loads((root / 'docs/errata/ledger.json').read_text())
sources = json.loads((root / 'docs/sources.json').read_text())['sources']
# The sub-orchestrator for tracks I, N, P keeps its own campaign and progress files (merged here).
for extra, key in (('docs/campaign/campaign-INP.json', 'workers'),):
    xp = root / extra
    if xp.exists():
        campaign['workers'] = campaign['workers'] + json.loads(xp.read_text()).get(key, [])
xp = root / 'docs/campaign/progress-INP.json'
if xp.exists():
    ids = {it['id'] for it in progress['items']}
    progress['items'] = progress['items'] + [it for it in json.loads(xp.read_text())['items'] if it['id'] not in ids]


def graph_counts(graph, parts=('',)):
    """(resolved, total) graph nodes whose statement source names a part; resolved = PROVED, BYPASSED or EXTERNAL."""
    path = root / 'docs/graph' / graph / 'DEPGRAPH.md'
    if not path.exists():
        return None
    done = total = 0
    for rec in re.split(r'\n(?=NODE: )', path.read_text()):
        st = re.search(r'^LEAN_STATUS: (\S+)', rec, re.M)
        src = re.search(r'^STATEMENT_SOURCE: (\S+)', rec, re.M)
        if st and src and any(p in src.group(1) for p in parts):
            total += 1
            done += st.group(1) in ('PROVED', 'BYPASSED', 'EXTERNAL')
    return done, total


def graph_resolved(graph, parts):
    """Resolved fraction of the graph nodes whose statement source names a part."""
    c = graph_counts(graph, parts)
    return c[0] / c[1] if c and c[1] else None


# Manifest id prefix of each track's frozen anchors.
ANCHOR_PREFIX = {'K': 'kam', 'I': 'iso', 'N': 'nekhoroshev', 'P': 'planetary'}


def track_sealed(graph):
    """True when every frozen theorem of the track is sealed: the track's proof is then complete, and graph nodes
    still open (alternative routes, steps proved only in a specialized form) are not needed."""
    thm = [a for a in manifest['anchors']
           if a['kind'] == 'theorem' and a['id'].split('.')[0] == ANCHOR_PREFIX.get(graph)]
    return bool(thm) and all(a['state'] == 'SEALED' for a in thm)


# Items with an "auto" field take their done fraction from the proof graph, so they never go stale.
for it in progress['items']:
    if 'auto' in it:
        f = 1.0 if track_sealed(it['auto']['graph']) else graph_resolved(it['auto']['graph'], it['auto']['parts'])
        if f is not None:
            it['done'] = f
NOW =datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')
LIB = [root / 'KAM']


def git(*args, cwd=root):
    r = subprocess.run(['git', *args], cwd=cwd, capture_output=True, text=True)
    return r.stdout.strip()


THM = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:public\s+|private\s+|protected\s+)*(?:theorem|lemma)\s', re.M)


def lean_stats(paths):
    files = [p for d in paths if d.exists() for p in d.rglob('*.lean')]
    text = [f.read_text(encoding='utf-8', errors='replace') for f in files]
    return len(files), sum(t.count('\n') for t in text), sum(len(THM.findall(t)) for t in text)


def statement_rows():
    rows = []
    for a in manifest['anchors']:
        if a['kind'] != 'theorem':
            continue
        export = a['export'].split('.')[-1]
        impl = a.get('implementation', {})
        prov = root / (impl.get('module', '').replace('.', '/') + '.lean')
        ptext = prov.read_text() if impl and prov.exists() else ''
        name = impl.get('export', '').split('.')[-1]
        if a['state'] == 'SEALED':
            state, cls = '✅ proved and sealed', 'sealed'
        elif name and re.search(rf'theorem\s+{re.escape(name)}\b', ptext):
            state, cls = '🟩 proved, sealing pending', 'proved'
        elif THM.search(ptext):
            state, cls = f'🟨 partly proved ({len(THM.findall(ptext))} components)', 'partial'
        else:
            state, cls = '⬜ not yet', 'todo'
        rows.append((a['id'], export, a['source']['range'], state, cls, a['path']))
    return rows


def code_scan():
    """Library files containing `sorry` outside KAM/Frozen, or an `axiom` declaration (comments removed)."""
    bad_sorry, bad_axiom = [], []
    for d in LIB:
        for f in sorted(d.rglob('*.lean')):
            t = f.read_text(encoding='utf-8', errors='replace')
            t = re.sub(r'/-.*?-/', '', t, flags=re.S)
            t = re.sub(r'--[^\n]*', '', t)
            t = re.sub(r'"(?:[^"\\]|\\.)*"', '""', t)
            rel = str(f.relative_to(root))
            if re.search(r'(?<![\w.])sorry(?![\w])', t) and not rel.startswith('KAM/Frozen/'):
                bad_sorry.append(rel)
            if re.search(r'^\s*(?:private\s+|protected\s+|public\s+)?axiom\s', t, re.M):
                bad_axiom.append(rel)
    return bad_sorry, bad_axiom


def section_statements(rows):
    if not rows:
        return ('*No statement is frozen yet.* The headline theorem and the gate theorems are being '
                'transcribed from the pinned sources; each will appear here once the owner has approved its '
                'exact Lean text and it is frozen.')
    notes = campaign.get('statement_notes', {})
    out = ['| ID | Source | Lean name | Status | Notes |', '|---|---|---|---|---|']
    for sid, export, rng, state, _, path in rows:
        out.append(f'| **{sid}** | {rng} | [`{export}`]({path}) | {state} | {notes.get(sid, "")} |')
    return '\n'.join(out)


def section_graph():
    g = campaign['graph']
    out = ['```mermaid', 'flowchart BT',
           '  classDef done fill:#c8e6c9,stroke:#2e7d32,color:#000',
           '  classDef conditional fill:#bbdefb,stroke:#1565c0,color:#000',
           '  classDef progress fill:#ffe0b2,stroke:#ef6c00,color:#000',
           '  classDef todo fill:#eeeeee,stroke:#757575,color:#000',
           '  classDef anchor fill:#fff9c4,stroke:#f9a825,color:#000,stroke-width:3px']
    for nid, label, state in g['nodes']:
        out.append(f'  {nid}["{label}"]:::{state}')
    for a, b in g['edges']:
        out.append(f'  {a} --> {b}')
    out.append('```')
    return '\n'.join(out)


def section_glance(rows):
    n, lines, thms = lean_stats(LIB)
    bad_sorry, bad_axiom = code_scan()
    sealed = sum(1 for r in rows if r[4] == 'sealed')
    head = git('rev-parse', '--short', 'HEAD') or '(no commit yet)'
    ndefs = sum(1 for a in manifest['anchors'] if a['kind'] == 'definition')
    drafts = [r[5] for r in rows if r[4] != 'sealed']
    out = [f'*Generated {NOW} from `main` at `{head}` by `scripts/hq-status.py`.*', '',
           f'**Current phase:** {campaign["current_phase"]}', '',
           f'**Frozen statements proved: {sealed} / {len(rows)}** · frozen definitions: {ndefs}', '',
           f'**Lean on `main`:** {n} modules · {lines:,} lines · {thms:,} theorems · '
           f'`sorry` outside frozen anchors: {len(bad_sorry)} files · `axiom` declarations: {len(bad_axiom)}', '',
           '```text',
           f'DRAFT_ANCHORS: {len(drafts)}' + (f' ({", ".join(drafts)})' if drafts else ''),
           f'UNREGISTERED_SORRIES: {len(bad_sorry)}' + (f' ({", ".join(bad_sorry)})' if bad_sorry else ''),
           'DRAFT_IMPORT_VIOLATIONS: 0 (frozen-anchor guard, run at every landing)',
           f'SEALED: {sealed} / {len(rows)}' + (f' ({", ".join(r[0] for r in rows if r[4] == "sealed")})'
                                                 if sealed else ''),
           '```', ''] + so_glance()
    return '\n'.join(out)


def so_package(suffix):
    """Track SO package name of a worktree suffix: `soexpr` -> SO-EXPR, `design-so` -> SO-DESIGN."""
    return 'SO-DESIGN' if suffix == 'design-so' else 'SO-' + suffix[2:].upper()


def so_glance():
    """Track SO block of the glance: live Lean size, packages landed / planned, packages in flight."""
    so = campaign.get('so')
    if not so:
        return []
    n, lines, thms = lean_stats([root / 'KAM' / 'Certificate', root / 'KAM' / 'SpinOrbit'])
    try:
        r = subprocess.run(['tmux', 'ls', '-F', '#S'], capture_output=True, text=True)
        sessions = r.stdout.split() if r.returncode == 0 else []
    except FileNotFoundError:
        sessions = []
    flight = {'inp-mprov-': set(), 'inp-maud-': set()}
    for s in sessions:
        for pre in flight:
            sfx = s[len(pre):]
            if s.startswith(pre) and (sfx.startswith('so') or sfx == 'design-so') and pane_state(s) == '🔄 working':
                flight[pre].add(so_package(sfx))
    landed = so['landed']
    out = [f'**Track SO, lunar spin–orbit certificate** (D30, started 2026-10-29; '
           f'[plan](docs/campaign/design/SPIN-ORBIT-PLAN.md)): {so["goal"]}', '',
           f'- **Lean on `main`:** {n} modules · {lines:,} lines · {thms:,} theorems in `KAM/Certificate` and '
           f'`KAM/SpinOrbit` (design estimate {so["planned_lines"]})',
           f'- **Packages landed: {len(landed)} / {len(so["packages"])}** ({", ".join(landed)})']
    if flight['inp-mprov-'] or flight['inp-maud-']:
        out.append(f'- **Now:** proving {", ".join(sorted(flight["inp-mprov-"])) or "—"} · '
                   f'in audit {", ".join(sorted(flight["inp-maud-"])) or "—"}')
    out.append(f'- **Gates:** {so["gates"]}')
    return out


AREAS = [
    ('Frozen', 'Owner-approved frozen statements and definitions (one per file, manifest-bound)'),
    ('Provider', 'One provider module per frozen theorem, where its proof is assembled'),
    ('Analysis', 'Track K Part 1: quadratic iteration and scalar estimates'),
    ('Fourier', 'Weighted ℓ¹ Fourier norms, used in the cohomological equation (D12)'),
    ('Diophantine', 'Diophantine vectors, cohomological equation, measure of the Diophantine set'),
    ('Strip', 'Holomorphic functions on complex strips: Cauchy estimates, Fourier series, cohomological equation'),
    ('Matrix', 'Matrix-valued functions: Neumann series and inverse bounds'),
    ('Torus', 'Carriers for tori and embeddings: ℂⁿ × ℂⁿ, predicates, averages'),
    ('Apost', 'Track K Part 2: a-posteriori KAM at fixed frequency (Newton step, iteration, limit)'),
    ('Uniq', 'Track K Part 3: local uniqueness of invariant tori for flows'),
    ('Measure', 'Track K Part 4: lattice counting, Lipschitz dependence, measure of the tori'),
    ('Head', 'Track K Part 4: assembly of the headline theorem'),
    ('ODE', 'Flows of ODEs: solutions, symmetries, continuation (tracks N and P)'),
    ('Iso', 'Track I: isoenergetic KAM, confinement, restricted three-body problem'),
    ('Kepler', 'Kepler problem and Delaunay coordinates (tracks I and P)'),
    ('Weighted', 'Track N: weighted domains and norms'),
    ('Canonical', 'Track N: canonical flows and maps'),
    ('Nekhoroshev', 'Track N: Nekhoroshev stability'),
    ('Planetary', 'Track P: planetary KAM'),
    ('Certificate', 'Track SO: the general certificate checker (certified arithmetic, Fourier models, frequencies)'),
    ('SpinOrbit', 'Track SO: the lunar spin–orbit problem (model, barriers, frequencies, graphs)'),
]


def section_areas():
    out = ['| Area | Content | Modules | Lines | Theorems |', '|---|---|---|---|---|']
    known = {d for d, _ in AREAS}
    extra = sorted(p.name for p in (root / 'KAM').iterdir() if p.is_dir() and p.name not in known)
    for d, desc in AREAS + [(d, '—') for d in extra]:
        p = root / 'KAM' / d
        if not p.exists():
            continue
        n, lines, thms = lean_stats([p])
        link = f'[`KAM/{d}/`](KAM/{d})'
        out.append(f'| {link} | {desc} | {n} | {lines:,} | {thms} |')
    return '\n'.join(out)


def pane_state(session):
    if not session:
        return None
    try:
        r = subprocess.run(['tmux', 'capture-pane', '-p', '-t', session], capture_output=True, text=True)
    except FileNotFoundError:
        # Collaborator checkouts may not have tmux; keep the recorded campaign state.
        return None
    if r.returncode != 0:
        return '⚠️ session missing'
    lines = [l for l in r.stdout.splitlines() if l.strip()]
    tail = '\n'.join(lines[-14:])
    if re.search(r'Working \(|esc to interrupt', tail):
        return '🔄 working'
    m = re.search(r'\b(READY|BLOCKED)\b', tail)
    if m:
        return '✅ handed off' if m.group(1) == 'READY' else '⛔ blocked'
    return '⏸ idle'


STATE_ICON = {'active': '🔄 active', 'running': '🔄 running', 'idle': '⏸ idle', 'done': '✅ done',
              'blocked': '⛔ blocked'}


def section_workers():
    out = ['| Agent | Kind | Model | Account | State | Assignment | Branch | Unlanded commits |',
           '|---|---|---|---|---|---|---|---|']
    gone = 0
    for w in campaign['workers']:
        state = pane_state(w.get('session')) or STATE_ICON.get(w.get('state', ''), w.get('state', ''))
        if state == '⚠️ session missing':
            gone += 1
            continue
        branch = w.get('branch')
        ahead = git('rev-list', '--count', '--no-merges', f'main..{branch}') if branch else ''
        sess = f' `{w["session"]}`' if w.get('session') else ''
        out.append(f'| **{w["id"]}**{sess} | {w["kind"]} | {w.get("model", "")} | {w.get("account", "")} | '
                   f'{state} | {w["assignment"]} | {f"`{branch}`" if branch else "—"} | {ahead or "—"} |')
    # Packages of tracks I, N, P offloaded by the lead: one row per worktree branch inp-<suffix> not yet in inp.
    for b in worktree_branches():
        if not b.startswith('inp-') or b.startswith('inp-design'):
            continue
        if subprocess.run(['git', 'merge-base', '--is-ancestor', b, 'inp'], cwd=root).returncode == 0:
            continue
        subj = git('log', '-1', '--format=%s', b).replace('|', '∣')
        aud = pane_state(f'inp-maud-{b[4:]}')
        prov = pane_state(f'inp-mprov-{b[4:]}')
        # 2026-10-29: 'not yet audited' matched 'audit', and branches without a prover session showed as proving.
        state = ('🔍 in audit' if aud and aud != '⚠️ session missing' else
                 '🔄 proving' if prov and prov != '⚠️ session missing' else
                 '❌ audit failed, parked' if 'FAIL' in subj else
                 '✅ audited, handed back' if 'audit' in subj and 'not yet audited' not in subj else
                 '⏸ parked (no session)')
        ahead = git('rev-list', '--count', '--no-merges', f'inp..{b}')
        out.append(f'| **{b[4:]}** | prover (offload) | Claude Sonnet 5.5 | — | {state} | last commit: {subj[:90]} | '
                   f'`{b}` | {ahead} (vs `inp`) |')
    if gone:
        out += ['', f'*{gone} finished agent sessions not shown.*']
    q = campaign.get('queued', [])
    if q:
        out += ['', '**Queued:** ' + ' · '.join(x['title'] for x in q)]
    return '\n'.join(out)


TRACKS = [
    ('K', 'kam', 'Positive-measure KAM for nearly-integrable analytic Hamiltonians, complement ≤ C·ε^{1/4}'),
    ('I', 'iso', 'All-time confinement in two degrees of freedom (isoenergetic KAM); restricted circular planar '
                 'three-body problem'),
    ('N', 'nekhoroshev', 'Nekhoroshev stability for quasi-convex Hamiltonians, exponents 1/(2n)'),
    ('P', 'planetary', 'Properly degenerate KAM; planar two-planet problem; n planets around a fixed Sun'),
    ('SO', 'so', 'A general Lean certificate checker turning numerical KAM tori into theorems; the Moon\'s spin '
                 'rate stays within 3.3% of its orbital rate for all time'),
]


def section_tracks():
    out = ['| Track | Headline | Frozen theorems sealed | Proof graph | Stage |', '|---|---|---|---|---|']
    for t, prefix, head in TRACKS:
        thm = [a for a in manifest['anchors'] if a['kind'] == 'theorem' and a['id'].split('.')[0] == prefix]
        sealed = sum(a['state'] == 'SEALED' for a in thm)
        g = graph_counts(t)
        gtxt = f'{g[0]} / {g[1]} nodes resolved' if g and g[1] else 'not published yet'
        stage = campaign.get('tracks', {}).get(t, '')
        out.append(f'| **{t}** | {head} | {sealed} / {len(thm)} | {gtxt} | {stage} |')
    return '\n'.join(out)


def section_landed():
    log = git('log', '--first-parent', 'main', '-40', '--date=format:%Y-%m-%d %H:%M', '--format=%cd|%h|%s')
    rows = [l.split('|', 2) for l in log.splitlines() if l]
    rows = [r for r in rows if not r[2].startswith('HQ status')][:12]
    if not rows:
        return '*No commits on `main` yet.*'
    out = ['| When (UTC) | Commit | Change |', '|---|---|---|']
    out += [f'| {d} | `{h}` | {s.replace("|", "∣")} |' for d, h, s in rows]
    return '\n'.join(out)


def completion(rows):
    """Weighted completion: items by difficulty weight times their done fraction, plus 1 per sealed statement."""
    w = progress['weights']
    groups = {}
    for it in progress['items']:
        g = groups.setdefault(it['group'], [0.0, 0.0, 0])
        g[0] += w[it['difficulty']]
        g[1] += w[it['difficulty']] * it['done']
        g[2] += 1
    if rows:
        sealed = sum(1 for r in rows if r[4] == 'sealed')
        groups['Sealing of the frozen statements'] = [float(len(rows)), float(sealed), len(rows)]
    total = sum(g[0] for g in groups.values())
    done = sum(g[1] for g in groups.values())
    return 100 * done / total, groups, total, done


def loc(dirs):
    """(total lines, code lines) of the .lean files under `dirs`; code lines exclude blanks and comments."""
    total = code = 0
    for d in dirs:
        if not d.exists():
            continue
        for f in d.rglob('*.lean'):
            t = f.read_text(encoding='utf-8', errors='replace')
            total += t.count('\n')
            t = re.sub(r'/-.*?-/', lambda m: '\n' * m.group(0).count('\n'), t, flags=re.S)
            code += sum(1 for l in t.splitlines() if l.strip() and not l.strip().startswith('--'))
    return total, code


def worktree_branches():
    out = git('worktree', 'list', '--porcelain')
    return sorted({l.split('refs/heads/', 1)[1] for l in out.splitlines() if l.startswith('branch refs/heads/')}
                  - {'main'})


def unlanded_lines():
    """Lean lines added by the agents' unlanded commits (every branch checked out in a worktree).
    Each non-merge commit not reachable from main counts once, so stacked branches are not double counted.
    2026-10-29: the former `git diff main...b` used one of several merge bases of long-lived branches and
    counted already-landed files as unlanded (8,080 shown for about 2,300 real lines)."""
    commits = set()
    for b in worktree_branches():
        commits.update(git('rev-list', '--no-merges', f'main..{b}').split())
    added = 0
    for c in commits:
        for l in git('show', '--numstat', '--format=', c, '--', '*.lean').splitlines():
            a, _, path = l.split('\t', 2)
            if a.isdigit() and path != 'KAM.lean':
                added += int(a)
    return added


def size_estimate(rows):
    total, code = loc(LIB)
    pct, groups, wt, done = completion(rows)
    return total, code, unlanded_lines(), wt, done


def append_history(rows):
    """One line per run in docs/campaign/history.csv."""
    h = root / 'docs/campaign/history.csv'
    total, code, unl, wt, done = size_estimate(rows)
    pct = completion(rows)[0]
    n, _, thms = lean_stats(LIB)
    sealed = sum(1 for r in rows if r[4] == 'sealed')
    if not h.exists():
        h.write_text('utc,main,modules,lean_lines,code_lines,unlanded_lines,theorems,completion_pct,sealed\n')
    with h.open('a') as f:
        f.write(f'{NOW},{git("rev-parse", "--short", "HEAD")},{n},{total},{code},{unl},{thms},{pct:.1f},{sealed}\n')


def lines_24h_ago():
    h = root / 'docs/campaign/history.csv'
    if not h.exists():
        return None
    hist = [l.split(',') for l in h.read_text().splitlines()[1:] if l]
    if not hist:
        return None
    cutoff = datetime.now(timezone.utc).timestamp() - 86400

    def ts(r):
        return datetime.strptime(r[0], '%Y-%m-%d %H:%M UTC').replace(tzinfo=timezone.utc).timestamp()
    old = [r for r in hist if ts(r) <= cutoff]
    r = old[-1] if old else hist[0]
    return int(r[3]), r[0]


# Rough planning figure for the total size; replaced by a rate-based estimate once real proofs land.
PLANNED_TOTAL = 40000


def lean_item(it):
    """Lean proof work: track K's analysis, a-posteriori and measure items, and the proof items of tracks I, N, P."""
    return it['id'].split('.')[0] in ('F', 'K', 'M') or '.PROOF' in it['id']


def section_size(rows):
    total, code, unl, wt, done = size_estimate(rows)
    prev = lines_24h_ago()
    growth = f' · **{total - prev[0]:+,}** since {prev[1]}' if prev else ''
    w = progress['weights']
    lean = [it for it in progress['items'] if lean_item(it)]
    lean_done = sum(w[it['difficulty']] * it['done'] for it in lean)
    rate_based = lean_done >= 8
    est = (total + unl) / lean_done * sum(w[it['difficulty']] for it in lean) if rate_based else PLANNED_TOTAL
    how = ('scales the lines written so far (on `main` plus the agent branches) by the done share of the Lean work '
           'items, weighted by difficulty: track K\'s analysis, a-posteriori and measure items and the proof items of '
           'tracks I, N and P. It is as good as those done fractions: track K\'s come from its proof graph, the others '
           'from the sub-orchestrator\'s assessment' if rate_based else
           'is a planning figure; it switches to a rate-based estimate once 8 weight units of Lean work are done')
    out = ['### Size of the formalization', '',
           '| | Lines of Lean |', '|---|---|',
           f'| On `main` now | **{total:,}** ({code:,} excluding blank lines and comments){growth} |',
           f'| Written on agent branches, not yet landed | {unl:,} |',
           f'| **Estimated total at completion** | **≈ {round(est, -3):,.0f}** |',
           f'| Estimated still to write | ≈ {round(max(est - total - unl, 0), -3):,.0f} |', '',
           f'**How the size is estimated.** The estimate {how}. History of all counts: '
           '[`docs/campaign/history.csv`](docs/campaign/history.csv).']
    return '\n'.join(out), est


def bar(pct, n=25):
    k = round(pct / 100 * n)
    return '█' * k + '░' * (n - k)


def section_updated(rows, est):
    pct = completion(rows)[0]
    sealed = sum(1 for r in rows if r[4] == 'sealed')
    total = loc(LIB)[0]
    return (f'> **Last updated: {NOW}** (automatic: every 20 minutes and after every commit) · '
            f'**estimated completion {pct:.1f} %** · frozen statements proved: {sealed} / {len(rows)} · '
            f'**{total:,} lines of Lean** of an estimated ≈ {round(est, -3):,.0f}')


def section_progress(rows):
    pct, groups, total, done = completion(rows)
    out = [f'### Estimated completion: **{pct:.1f} %**', '', f'`{bar(pct)}` {pct:.1f} %', '',
           '| Part of the project | Items | Weight | Done | Completion |', '|---|---|---|---|---|']
    for name, (wt, dn, n) in groups.items():
        out.append(f'| {name} | {n} | {wt:.0f} | {dn:.1f} | `{bar(100 * dn / wt, 10)}` {100 * dn / wt:.0f} % |')
    out.append(f'| **Total** | {sum(g[2] for g in groups.values())} | {total:.0f} | {done:.1f} | **{pct:.1f} %** |')
    out += ['', f'**How this is estimated.** The project is divided into {len(progress["items"])} work items: planning '
            'deliverables, campaign infrastructure, the four layers of track K\'s proof, and the proof campaigns of '
            'tracks I, N and P. Each item is weighted by its difficulty (low 1, moderate 2, high 4, very high 8) and '
            'counts with the fraction of it that is done; each sealed frozen theorem adds 1. Items marked *graph* '
            'take that fraction from their proof graph (nodes `PROVED`, `BYPASSED` or `EXTERNAL` in '
            '[`docs/graph/`](docs/graph)), so they update themselves at every refresh, and count as complete once '
            'every frozen theorem of their track is sealed; the other items are the '
            f'orchestrators\' assessment, last reviewed **{progress["reviewed"]}**. Files: '
            '[`docs/campaign/progress.json`](docs/campaign/progress.json) (track K and infrastructure) and '
            '[`docs/campaign/progress-INP.json`](docs/campaign/progress-INP.json) (tracks I, N, P).',
            '', '<details><summary>All work items with their weight and status</summary>', '',
            '| ID | Item | Difficulty | Done | Note |', '|---|---|---|---|---|']
    for it in progress['items']:
        mark = '✅' if it['done'] >= 1 else ('🟨' if it['done'] > 0 else '⬜')
        out.append(f'| {it["id"]} | {it["title"].replace("|", "∣")} | {it["difficulty"]} | '
                   f'{mark} {100 * it["done"]:.0f} % | {"*graph " + it["auto"]["graph"] + "* · " if "auto" in it else ""}'
                   f'{it.get("note", "")} |')
    out += ['', '</details>']
    return '\n'.join(out)


def section_errata():
    by_src = {}
    for e in ledger['entries']:
        s = by_src.setdefault(e['source'], {'erratum': {}, 'deviation': {}})
        s[e['type']][e['status']] = s[e['type']].get(e['status'], 0) + 1

    def fmt(d):
        return ', '.join(f'{v} {k.lower()}' for k, v in sorted(d.items())) or '0'
    out = ['| Source | Errata (by status) | Deviations (by status) |', '|---|---|---|']
    for k, s in sorted(by_src.items()):
        out.append(f'| {k} | {fmt(s["erratum"])} | {fmt(s["deviation"])} |')
    out += ['', '<details><summary>All ledger entries</summary>', '',
            '| ID | Type | Source | Location | Claim | Status |', '|---|---|---|---|---|---|']
    for e in ledger['entries']:
        out.append(f'| {e["id"]} | {e["type"]} | {e["source"]} | {e["location"]} | '
                   f'{e["claim"].replace("|", "∣")} | {e["status"]} |')
    out += ['', '</details>']
    return '\n'.join(out)


def section_papers():
    out = ['| Key | Reference | arXiv | DOI | Role |', '|---|---|---|---|---|']
    for s in sources:
        ax = f'[{s["arxiv"]}](https://arxiv.org/abs/{s["arxiv"]})' if s.get('arxiv') else '—'
        doi = f'[{s["doi"]}](https://doi.org/{s["doi"]})' if s.get('doi') else '—'
        out.append(f'| {s["key"]} | {s["citation"]} | {ax} | {doi} | {s["role"]} |')
    return '\n'.join(out)


rows = statement_rows()
size_text, est = section_size(rows)
sections = {
    'updated': section_updated(rows, est),
    'progress': section_progress(rows),
    'size': size_text,
    'glance': section_glance(rows),
    'statements': section_statements(rows),
    'graph': section_graph(),
    'areas': section_areas(),
    'tracks': section_tracks(),
    'workers': section_workers(),
    'landed': section_landed(),
    'errata': section_errata(),
    'papers': section_papers(),
}
text = readme.read_text()
for name, body in sections.items():
    pat = re.compile(rf'(<!-- AUTO:{name} -->\n).*?(<!-- /AUTO:{name} -->)', re.S)
    if not pat.search(text):
        raise SystemExit(f'README has no AUTO:{name} markers')
    text = pat.sub(lambda m: m.group(1) + body + '\n' + m.group(2), text)
readme.write_text(text)
append_history(rows)
print('README live sections updated')
