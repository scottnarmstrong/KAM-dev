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
# Track SO (D30): its items take their done fraction from the design's package line estimates and the landed list.
# 2026-10-29: in two parts (owner); a package counts as landed when all its files exist on main (no hand-kept list).
SO_GROUPS = ['Track SO, part 1: general Lean certificate checker',
             "Track SO, part 2: the Moon's spin rate (lunar spin–orbit)"]
SO_PARTS = {}
xp = root / 'docs/campaign/progress-SO.json'
if xp.exists():
    for it in json.loads(xp.read_text())['items']:
        if 'so_packages' in it:
            pk = it['so_packages']
            here = {k for k, (_, fs) in pk.items() if all((root / f).exists() for f in fs)}
            part = SO_PARTS.setdefault(it['group'], {'landed': [], 'packages': []})
            part['packages'] += list(pk)
            part['landed'] += [k for k in pk if k in here]
            it['done'] = sum(v[0] for k, v in pk.items() if k in here) / sum(v[0] for v in pk.values())
            it['note'] = 'landed: ' + (', '.join(k for k in pk if k in here) or 'none') + ' (of ' + ', '.join(pk) + ')'
        progress['items'].append(it)
    if 'so' in campaign:
        campaign['so']['landed'] = [k for p in SO_PARTS.values() for k in p['landed']]
        campaign['so']['packages'] = [k for p in SO_PARTS.values() for k in p['packages']]


def graph_counts(graph, parts=('',)):
    """(resolved, total) graph nodes whose statement source names a part; resolved = PROVED, BYPASSED, EXTERNAL or ASSUMED (an owner-accepted convention, D31)."""
    path = root / 'docs/graph' / graph / 'DEPGRAPH.md'
    if not path.exists():
        return None
    done = total = 0
    for rec in re.split(r'\n(?=NODE: )', path.read_text()):
        st = re.search(r'^LEAN_STATUS: (\S+)', rec, re.M)
        src = re.search(r'^STATEMENT_SOURCE: (\S+)', rec, re.M)
        if st and src and any(p in src.group(1) for p in parts):
            total += 1
            done += st.group(1) in ('PROVED', 'BYPASSED', 'EXTERNAL', 'ASSUMED')
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


def ledger_note():
    """Counts of the errata ledger by type and status (2026-10-31: the hand-kept note still read "8 candidate errata,
    6 planned deviations")."""
    out = []
    for typ, label in (('erratum', 'errata'), ('deviation', 'deviations')):
        es = [e for e in ledger['entries'] if e['type'] == typ]
        st = {}
        for e in es:
            st[e['status'].lower()] = st.get(e['status'].lower(), 0) + 1
        out.append(f'{len(es)} {label} (' + ', '.join(f'{v} {k}' for k, v in sorted(st.items())) + ')')
    return (f'ledger: {" and ".join(out)} over {len({e["source"] for e in ledger["entries"]})} sources; reader-facing '
            'record docs/ERRATA-AND-DEVIATIONS.md')


for it in progress['items']:
    if it['id'] == 'S.ERRATA':
        it['note'] = ledger_note()
NOW = datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')
LIB = [root / 'KAM']


def git(*args, cwd=root):
    r = subprocess.run(['git', *args], cwd=cwd, capture_output=True, text=True)
    return r.stdout.strip()


THM = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:public\s+|private\s+|protected\s+)*(?:theorem|lemma)\s', re.M)
# Machine-generated certificate literals (track SO: the Moon's barrier tori, later the lock's torus), emitted by
# scripts/spin_orbit/. 2026-10-31: counted apart everywhere; the hand-written size, the size estimate and the
# theorem count exclude them (they had made the headline read 1,000,870 lines and "≈ 0 still to write").
GENERATED_DATA = 'KAM/SpinOrbit/Data/'
_FILE_STATS = {}


def is_generated(f):
    return f.relative_to(root).as_posix().startswith(GENERATED_DATA)


def file_stats(f):
    """(lines, code lines, theorems) of one .lean file, cached; code lines exclude blank lines and comments."""
    s = _FILE_STATS.get(f)
    if s is None:
        t = f.read_text(encoding='utf-8', errors='replace')
        u = re.sub(r'/-.*?-/', lambda m: '\n' * m.group(0).count('\n'), t, flags=re.S)
        code = sum(1 for l in u.splitlines() if l.strip() and not l.strip().startswith('--'))
        s = _FILE_STATS[f] = (t.count('\n'), code, len(THM.findall(t)))
    return s


def lean_files(paths, generated=None):
    """The .lean files under `paths`; generated=False drops the generated certificate data, True keeps only it."""
    files = [p for d in paths if d.exists() for p in d.rglob('*.lean')]
    return files if generated is None else [f for f in files if is_generated(f) == generated]


def lean_stats(paths, generated=None):
    """(modules, lines, theorems) of the .lean files under `paths` (see lean_files for `generated`)."""
    st = [file_stats(f) for f in lean_files(paths, generated)]
    return len(st), sum(s[0] for s in st), sum(s[2] for s in st)


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


STATEMENT_TRACKS = [('kam', 'Track K: positive-measure KAM'),
                    ('iso', 'Track I: isoenergetic KAM, confinement, restricted three-body problem'),
                    ('nekhoroshev', 'Track N: Nekhoroshev stability'),
                    ('planetary', 'Track P: planetary systems'),
                    ('russmann', "Track R: Rüssmann's KAM theorem (weak non-degeneracy)"),
                    ('wave', 'Track W: PDE KAM (cubic wave equation)'),
                    ('spinorbit', "Track SO: the Moon's spin rate and synchronous lock (certified tori)")]


def frozen_doc(path, short):
    """(line of the declaration, its docstring flattened) in a frozen file."""
    try:
        lines = (root / path).read_text().split('\n')
    except OSError:
        return 1, ''
    n = next((i for i, l in enumerate(lines, 1)
              if re.match(rf'\s*(?:theorem|def|noncomputable def|abbrev|structure|inductive)\s+{re.escape(short)}\b', l)), 1)
    text = '\n'.join(lines[:n - 1])
    docs = re.findall(r'/--(.*?)-/', text, re.S)
    return n, ' '.join(docs[-1].split()) if docs else ''


def statements_page(rows):
    """docs/STATEMENTS.md: every frozen theorem and definition, per track, with source, docstring, link and status."""
    notes = campaign.get('statement_notes', {})
    defs = [a for a in manifest['anchors'] if a['kind'] == 'definition']
    by_id = {a['id']: a for a in manifest['anchors']}
    sealed = sum(1 for r in rows if r[4] == 'sealed')
    out = ['# Frozen statements', '',
           '*Generated by `scripts/hq-status.py` from [`manifest/frozen-anchors.json`](../manifest/frozen-anchors.json); '
           'back to the [README](../README.md).*', '',
           'Every statement below is an exact Lean declaration that the owner approved before its proof was written. Each '
           'lives alone in its own file under `KAM/Frozen/`, and the manifest pins its bytes. A sealed theorem has a '
           'complete proof, assembled in a separate provider module, replayed by the kernel, and using only the standard '
           'axioms (`propext`, `Classical.choice`, `Quot.sound`).', '',
           f'**{len(rows)} frozen theorems, {sealed} sealed; {len(defs)} frozen definitions.**', '', '## Index', '']
    for pre, title in STATEMENT_TRACKS:
        ts = [r for r in rows if r[0].split('.')[0] == pre]
        if ts:
            out.append(f'- **{title}:** ' + ' · '.join(f'[`{r[1]}`](#{r[1].lower()})' for r in ts))
    for pre, title in STATEMENT_TRACKS:
        ts = [r for r in rows if r[0].split('.')[0] == pre]
        if not ts:
            continue
        out += ['', f'## {title}']
        for sid, export, rng, state, _, path in ts:
            a = by_id[sid]
            n, doc = frozen_doc(path, export)
            impl = a.get('implementation', {})
            out += ['', f'### {export}', '',
                    f'[`{a["export"]}`](../{path}#L{n}) · {state}']
            if doc:
                out += ['', doc]
            key = str(a.get('source', {}).get('revision', '')).split(' ')[0]
            paper = f'[{key}](PAPERS.md#{key.lower()}), ' if key in {p['key'] for p in sources} else ''
            out += ['', f'- **Source:** {paper}{rng}']
            if notes.get(sid):
                out.append(f'- **Role:** {notes[sid]}')
            if impl.get('module'):
                out.append(f'- **Proof assembled in:** `{impl["module"]}`')
            out.append(f'- **Manifest ID:** `{sid}`')
        ds = [d for d in defs if d['id'].split('.')[0] == pre]
        if ds:
            out += ['', f'<details><summary>Frozen definitions of this track ({len(ds)})</summary>', '']
            for d in ds:
                short = d['export'].split('.')[-1]
                n, _ = frozen_doc(d['path'], short)
                out.append(f'- [`{d["export"]}`](../{d["path"]}#L{n})')
            out += ['', '</details>']
    other = [d for d in defs if d['id'].split('.')[0] not in {p for p, _ in STATEMENT_TRACKS}]
    if other:
        out += ['', '## Other frozen definitions', '']
        out += [f'- [`{d["export"]}`](../{d["path"]})' for d in other]
    return '\n'.join(out) + '\n'


def section_statements(rows):
    if not rows:
        return '*No statement is frozen yet.*'
    page = root / 'docs' / 'STATEMENTS.md'
    text = statements_page(rows)
    if not page.exists() or page.read_text() != text:
        page.write_text(text)
    sealed = sum(1 for r in rows if r[4] == 'sealed')
    ndefs = sum(1 for a in manifest['anchors'] if a['kind'] == 'definition')
    out = [f'**{len(rows)} frozen theorems ({sealed} sealed) and {ndefs} frozen definitions.** Each theorem, with its '
           'source, its docstring, a link to the exact Lean declaration and its status, is on its own page: '
           '**[docs/STATEMENTS.md](docs/STATEMENTS.md)**.', '']
    for pre, title in STATEMENT_TRACKS:
        ts = [r for r in rows if r[0].split('.')[0] == pre]
        if ts:
            out.append(f'- {title}: ' + ', '.join(f'[`{r[1]}`](docs/STATEMENTS.md#{r[1].lower()})' for r in ts))
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
    n, lines, thms = lean_stats(LIB, generated=False)
    gn, gl, gt = lean_stats(LIB, generated=True)
    bad_sorry, bad_axiom = code_scan()
    sealed = sum(1 for r in rows if r[4] == 'sealed')
    head = git('rev-parse', '--short', 'HEAD') or '(no commit yet)'
    ndefs = sum(1 for a in manifest['anchors'] if a['kind'] == 'definition')
    drafts = [r[5] for r in rows if r[4] != 'sealed']
    out = [f'*Generated {NOW} from `main` at `{head}` by `scripts/hq-status.py`.*', '',
           f'**Current phase:** {campaign["current_phase"]}', ''] + so_glance() + w_glance() + ['',
           f'**Frozen statements proved: {sealed} / {len(rows)}** · frozen definitions: {ndefs}', '',
           f'**Lean on `main` (hand-written):** {n:,} modules · {lines:,} lines · {thms:,} theorems · '
           f'`sorry` outside frozen anchors: {len(bad_sorry)} files · `axiom` declarations: {len(bad_axiom)} '
           '(both scans cover every module, generated data included)', '',
           *([f'**Generated certificate data on `main`:** {gl:,} lines in {gn:,} modules (numeric literals; not '
              f'counted above), with {gt:,} generated kernel-check theorems; under '
              f'[`{GENERATED_DATA}`]({GENERATED_DATA.rstrip("/")})', ''] if gn else []),
           '```text',
           f'DRAFT_ANCHORS: {len(drafts)}' + (f' ({", ".join(drafts)})' if drafts else ''),
           f'UNREGISTERED_SORRIES: {len(bad_sorry)}' + (f' ({", ".join(bad_sorry)})' if bad_sorry else ''),
           'DRAFT_IMPORT_VIOLATIONS: 0 (frozen-anchor guard, run at every landing)',
           f'SEALED: {sealed} / {len(rows)}' + (f' ({", ".join(r[0] for r in rows if r[4] == "sealed")})'
                                                 if sealed else ''),
           '```']
    return '\n'.join(out)


def so_package(suffix):
    """Track SO package name of a worktree suffix: `soexpr` -> SO-EXPR, `design-so` -> SO-DESIGN, `lockdata` ->
    LOCK-DATA."""
    special = {'design-so': 'SO-DESIGN', 'soadv': 'SO-ADVCOUNT', 'sopolya': 'SO-POLY-A', 'sopolyb': 'SO-POLY-B',
               'soexprc': 'SO-EXPR-B2', 'sosounda': 'SO-SOUND-A', 'sosoundb': 'SO-SOUND-B'}
    if suffix.startswith('lock'):
        return 'LOCK-' + suffix[4:].upper()
    return special.get(suffix, 'SO-' + suffix[2:].upper())


_SESSIONS = []


def tmux_sessions():
    """Names of the tmux sessions (none where tmux is missing); cached."""
    if not _SESSIONS:
        try:
            r = subprocess.run(['tmux', 'ls', '-F', '#S'], capture_output=True, text=True)
            _SESSIONS.append(r.stdout.split() if r.returncode == 0 else [])
        except FileNotFoundError:
            _SESSIONS.append([])
    return _SESSIONS[0]


def session_worktree(session, sfx):
    """Where an agent session works: the worktree KAM-inp-<sfx> beside the main checkout if it exists, else the
    pane's working directory (the LOCK-FREEZE worker runs in KAM-inp-lockdesign)."""
    wt = root.parent / f'KAM-inp-{sfx}'
    if wt.exists():
        return wt
    try:
        r = subprocess.run(['tmux', 'display', '-p', '-t', session, '#{pane_current_path}'], capture_output=True,
                           text=True)
    except FileNotFoundError:
        return None
    path = Path(r.stdout.strip()) if r.returncode == 0 and r.stdout.strip() else None
    return path if path and path.exists() else None


def session_package(session, sfx):
    """Package of an agent session, from the branch of its worktree (2026-10-31: session names outlive their
    package; inp-mprov-sodata3 runs SO-FREEZE3 on branch inp-sofreeze3)."""
    wt = session_worktree(session, sfx)
    b = git('-C', str(wt), 'rev-parse', '--abbrev-ref', 'HEAD') if wt else ''
    return so_package(b[4:] if b.startswith('inp-') else sfx)


MOON_FILE = 'KAM/SpinOrbit/LunarFinalR2V2.lean'
MOON_THEOREM = 'lunar_spin_confinement_65_v2'
MOON_FROZEN = 'KAM/Frozen/SpinOrbit/Theorems/LunarSpinConfinement.lean'


def so_anchors(lock):
    """Frozen theorems of track SO part 2 (lock=False) or part 3 (lock=True), by manifest id."""
    return [a for a in manifest['anchors'] if a['kind'] == 'theorem' and a['id'].startswith(('spinorbit.', 'so.'))
            and (re.search(r'sync|lock', a['id'], re.I) is not None) == lock]


def moon_state():
    """Track SO part 2 read from the repository: (proved, when it reached main, frozen, sealed)."""
    f = root / MOON_FILE
    proved = f.exists() and re.search(rf'^theorem\s+{MOON_THEOREM}\b', f.read_text(), re.M) is not None
    when = git('log', '--first-parent', 'main', '--diff-filter=A', '--date=format:%Y-%m-%d %H:%M',
               '--format=%cd UTC, `%h`', '--', MOON_FILE).splitlines()
    thm = so_anchors(False)
    return (proved, when[-1] if when else '', (root / MOON_FROZEN).exists(),
            bool(thm) and all(a['state'] == 'SEALED' for a in thm))


def so_glance():
    """Track SO block of the glance: live Lean size, packages landed / planned, packages in flight."""
    so = campaign.get('so')
    if not so:
        return []
    sessions = tmux_sessions()
    flight = {'inp-mprov-': set(), 'inp-maud-': set()}
    for s in sessions:
        for pre in flight:
            sfx = s[len(pre):]
            if s.startswith(pre) and (sfx.startswith('so') or sfx == 'design-so') and pane_state(s) == '🔄 working':
                flight[pre].add(session_package(s, sfx))
    nc, lc, tc = lean_stats([root / 'KAM' / 'Certificate'])
    ns, ls, ts = lean_stats([root / 'KAM' / 'SpinOrbit'], generated=False)
    gn, gl, gt = lean_stats([root / 'KAM' / 'SpinOrbit'], generated=True)
    p1, p2 = (SO_PARTS.get(g, {'landed': [], 'packages': []}) for g in SO_GROUPS)
    proved, when, frozen, sealed = moon_state()
    done1 = bool(p1['packages']) and len(p1['landed']) == len(p1['packages'])
    if not proved:
        moon = ("- **Part 2, the Moon's spin rate:** two certified barrier tori at N = 65 (D38) prove that the Moon's "
                'spin rate stays close to its orbital rate for all time; in progress.')
    else:
        seal = ('frozen (D49) and sealed (D50)' if sealed else
                'frozen (D49); the seal (D50) is in progress (SO-FREEZE3)' if frozen else
                'freeze (D49) and seal (D50) approved by the owner and in progress (SO-FREEZE3: Q11 data rebuild, '
                'freeze, seal, seal audit)')
        moon = (f"- **Part 2, the Moon's spin rate: PROVED** (on `main` since {when}): {so['moon_statement']} "
                f'[`{MOON_THEOREM}`]({MOON_FILE}). Status: ordinary theorem; {seal}.')
    out = [f'**Track SO** (D30, started 2026-10-29; [plan](docs/campaign/design/SPIN-ORBIT-PLAN.md)), in three parts:', '',
           f'- **Part 1, a general Lean certificate checker{" (complete)" if done1 else ""}:** a numerical KAM '
           'candidate (any dimension, Hamiltonians given as finite expressions) passes a kernel-evaluated checker, and '
           'one soundness theorem turns it into an exact invariant torus. ' + so.get('part1_note', '') +
           f' `KAM/Certificate`: {nc} modules · {lc:,} lines. '
           f'**Packages landed: {len(p1["landed"])} / {len(p1["packages"])}**.',
           f'{moon} `KAM/SpinOrbit`: {ns:,} modules · {ls:,} lines hand-written, plus {gl:,} lines of generated '
           f'certificate data in {gn:,} modules. **Packages landed: {len(p2["landed"])} / {len(p2["packages"])}**.',
           *lock_glance(sessions),
           f'- Design estimate for parts 1 and 2: {so["planned_lines"]}; landed: {", ".join(so["landed"])}.']
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
    ('Russmann', "Track R: Rüssmann's KAM theorem (finite-order non-degeneracy, Lipschitz extension, assembly)"),
    ('Sharp', 'Sharp explicit a-posteriori KAM: Newton engine, torsion route, step, g1_sharp, parameter boxes'),
    ('CertificateSharp', 'The sharp KAM certifier: engine-agnostic checker, rational constants, soundness'),
    ('Sharp2', 'v2 sharp a-posteriori KAM: route A, modified step (route B), l1 entry, small-divisor constants, PlasmaLean example'),
    ('Root', 'Generated parts of the root import file KAM.lean (scripts/gen_root_imports.py)'),
    ('Certificate', 'Track SO: the general certificate checker (certified arithmetic, Fourier models, frequencies)'),
    ('SpinOrbit', "Track SO: the lunar spin–orbit problem (model, barriers, frequencies, graphs, the Moon's band "
                  'theorems, the synchronous lock in `Lock/`); its generated certificate data are the next row'),
    ('SpinOrbit/Data', 'Track SO: generated certificate data of the barrier tori (numeric literals emitted by '
                       '`scripts/spin_orbit/`, checked by the kernel; with their literal format and support lemmas); '
                       'counted apart from the hand-written Lean'),
    ('Wave', 'Track W: PDE KAM for the cubic wave equation (Pöschel 1996): sequence calculus and the weighted '
             'convolution algebra, analytic maps on Banach domains, Banach-valued Fourier coefficients for the KAM '
             'step, Birkhoff normal form (averaged quartic part, nonresonance, nondegeneracy), analytic and classical '
             'reconstruction of the solutions'),
]


def section_areas():
    """One row per area; an area listed with a sub-path (SpinOrbit/Data) gets its own row and leaves its parent's."""
    out = ['| Area | Content | Modules | Lines | Theorems |', '|---|---|---|---|---|']
    known = {d for d, _ in AREAS}
    extra = sorted(p.name for p in (root / 'KAM').iterdir() if p.is_dir() and p.name not in known)
    for d, desc in AREAS + [(d, '—') for d in extra]:
        p = root / 'KAM' / d
        if not p.exists():
            continue
        subs = [root / 'KAM' / k for k in known if k.startswith(d + '/')]
        st = [file_stats(f) for f in lean_files([p]) if not any(s in f.parents for s in subs)]
        link = f'[`KAM/{d}/`](KAM/{d})'
        out.append(f'| {link} | {desc} | {len(st)} | {sum(x[0] for x in st):,} | {sum(x[2] for x in st)} |')
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
              'blocked': '⛔ blocked', 'paused': '⏸ paused'}
_PROCS = []


def process_table():
    """{pid: (parent pid, argv)} of the running processes, read from /proc (empty without it); cached."""
    if not _PROCS:
        procs = {}
        for d in (Path('/proc').iterdir() if Path('/proc').is_dir() else []):
            if not d.name.isdigit():
                continue
            try:
                argv = [x.decode(errors='replace') for x in (d / 'cmdline').read_bytes().split(b'\0') if x]
                ppid = int((d / 'stat').read_text().rsplit(')', 1)[1].split()[1])
            except (OSError, ValueError, IndexError):
                continue
            procs[int(d.name)] = (ppid, argv)
        _PROCS.append(procs)
    return _PROCS[0]


def model_name(argv):
    """Readable model of an agent's launch command: `--model claude-opus-5-5` -> Claude Opus 5.5; codex
    `-m gpt-6.1-sol -c model_reasoning_effort="medium"` -> GPT-6.1-Sol medium; None without a model flag."""
    m = next((argv[i + 1] for i in range(len(argv) - 1) if argv[i] in ('--model', '-m')), None)
    m = m or next((x.split('=', 1)[1] for x in argv if x.startswith('--model=')), None)
    if not m:
        return None
    c = re.fullmatch(r'claude-([a-z]+)-(\d+)-(\d+)(?:-\d+)?', m)
    if c:
        return f'Claude {c.group(1).title()} {c.group(2)}.{c.group(3)}'
    g = re.fullmatch(r'gpt-([\d.]+)-(\w+)', m)
    if g:
        eff = next((e.group(1) for x in argv for e in [re.search(r'model_reasoning_effort="?(\w+)', x)] if e), '')
        return f'GPT-{g.group(1)}-{g.group(2).title()}' + (f' {eff}' if eff else '')
    return m


def agent_process(session):
    """(model, account) of the agent in a tmux session, from its launch command (`--model`, codex `-m`) and its
    environment (CLAUDE_CONFIG_DIR=/root/.claude-accounts/N is account claude-N); None where unknown."""
    if not session or session not in tmux_sessions():
        return None, None
    try:
        r = subprocess.run(['tmux', 'list-panes', '-t', session, '-F', '#{pane_pid}'], capture_output=True, text=True)
    except FileNotFoundError:
        return None, None
    procs = process_table()
    kids = {}
    for pid, (ppid, _) in procs.items():
        kids.setdefault(ppid, []).append(pid)
    queue, seen = [int(x) for x in r.stdout.split() if x.isdigit()], set()
    while queue:
        pid = queue.pop(0)
        if pid in seen or pid not in procs:
            continue
        seen.add(pid)
        argv = procs[pid][1]
        exe = Path(argv[0]).name if argv else ''
        if exe in ('claude', 'codex') or (exe == 'node' and len(argv) > 1 and Path(argv[1]).name == 'codex.js'):
            acct = None
            try:
                for e in (Path('/proc') / str(pid) / 'environ').read_bytes().split(b'\0'):
                    m = re.match(rb'CLAUDE_CONFIG_DIR=.*claude-accounts/(\d+)/?$', e)
                    if m:
                        acct = f'claude-{m.group(1).decode()}'
            except OSError:
                pass
            return model_name(argv), acct
        queue.extend(kids.get(pid, []))
    return None, None


def trailer_model(rng):
    """The most frequent Claude co-author of the commits in a git range (`Co-Authored-By: Claude Opus 5.5 <…>`)."""
    out = git('log', '--format=%(trailers:key=Co-Authored-By,valueonly,separator=%x1f)', rng)
    names = [re.sub(r'\s*<[^>]*>', '', t).strip() for l in out.splitlines() for t in l.split('\x1f')]
    names = [n for n in names if n.startswith('Claude')]
    return max(sorted(set(names)), key=names.count) if names else None


def worktree_paths():
    """{branch: worktree path} of the worktrees."""
    out, path = {}, None
    for l in git('worktree', 'list', '--porcelain').splitlines():
        if l.startswith('worktree '):
            path = Path(l[len('worktree '):])
        elif l.startswith('branch refs/heads/') and path:
            out[l[len('branch refs/heads/'):]] = path
    return out


def section_workers():
    """Agents from campaign.json (and campaign-INP.json), then one row per offloaded package branch. Model and account
    come from the agent's running process where there is one (2026-10-31: the table showed stale accounts and Sonnet
    for Opus workers); otherwise from the JSON, or for a branch from its commits' co-author trailers."""
    out = ['| Agent | Kind | Model | Account | State | Assignment | Branch | Unlanded commits |',
           '|---|---|---|---|---|---|---|---|']
    gone = 0
    for w in campaign['workers']:
        live = pane_state(w.get('session'))
        state = live or STATE_ICON.get(w.get('state', ''), w.get('state', ''))
        if state in ('⚠️ session missing', '✅ done'):
            gone += 1
            continue
        if w.get('state') == 'paused' and live in ('⏸ idle', '✅ handed off'):
            state = STATE_ICON['paused']
        model, acct = agent_process(w.get('session'))
        branch = w.get('branch')
        ahead = git('rev-list', '--count', '--no-merges', f'main..{branch}') if branch else ''
        name = f'**{w["id"]}**' + (f' ({w["label"]})' if w.get('label') else '') + \
            (f' `{w["session"]}`' if w.get('session') else '')
        out.append(f'| {name} | {w["kind"]} | {model or w.get("model", "")} | {acct or w.get("account", "")} | '
                   f'{state} | {w["assignment"]} | {f"`{branch}`" if branch else "—"} | {ahead or "—"} |')
    # Offloaded packages: one row per worktree branch inp-<suffix> not yet in inp. Their sessions are named after the
    # branch suffix or after the worktree folder KAM-inp-<sfx> (2026-10-31: SO-FREEZE3 runs on branch inp-sofreeze3
    # in session inp-mprov-sodata3 and showed as "parked (no session)").
    paths = worktree_paths()
    for b in worktree_branches():
        if not b.startswith('inp-') or b.startswith('inp-design'):
            continue
        if subprocess.run(['git', 'merge-base', '--is-ancestor', b, 'inp'], cwd=root).returncode == 0:
            continue
        subj = git('log', '-1', '--format=%s', b).replace('|', '∣')
        sfxs = [b[4:]]
        if b in paths and paths[b].name.startswith('KAM-inp-') and paths[b].name[8:] != b[4:]:
            sfxs.append(paths[b].name[8:])

        def live(pre):
            for x in sfxs:
                st = pane_state(pre + x)
                if st and st != '⚠️ session missing':
                    return pre + x, st
            return None, None
        aud_s, aud = live('inp-maud-')
        prov_s, prov = live('inp-mprov-')
        # 2026-10-29: 'not yet audited' matched 'audit', and branches without a prover session showed as proving.
        # 2026-10-31: an auditor that has handed off (READY) no longer marks the branch as in audit.
        state = ('🔍 in audit' if aud == '🔄 working' else
                 '🔄 proving' if prov else
                 '🔍 in audit' if aud and aud != '✅ handed off' else
                 '❌ audit failed, parked' if 'FAIL' in subj else
                 '✅ audited, handed back' if 'audit' in subj and 'not yet audited' not in subj else
                 '⏸ parked (no session)')
        model, acct = agent_process(prov_s)
        model = model or trailer_model(f'inp..{b}') or '—'
        ahead = git('rev-list', '--count', '--no-merges', f'inp..{b}')
        pkg = so_package(b[4:]) if b[4:].startswith(('so', 'lock')) else b[4:]
        sess = ''.join(f' `{x}`' for x in (prov_s, aud_s) if x)
        out.append(f'| **{pkg}**{sess} | prover (offload) | {model} | {acct or "—"} | {state} | last commit: '
                   f'{subj[:90]} | `{b}` | {ahead} (vs `inp`) |')
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
    ('R', 'russmann', "Rüssmann's KAM theorem under weak non-degeneracy: invariant tori fill all but κ of phase space"),
    ('W', 'wave', 'PDE KAM: two-frequency quasi-periodic solutions of the cubic wave equation '
                  'u_tt = u_xx − m u − u³ on [0, π], every m > 0 (Pöschel 1996)'),
    ('SO-1', None, 'Track SO, part 1: a general Lean certificate checker turning numerical KAM tori into theorems'),
    ('SO-2', 'so-band', "Track SO, part 2: the Moon's spin rate stays within 2.755 % of its orbital rate for all time "
                        '(N = 65; proved 2026-10-31)'),
    ('SO-3', 'so-lock', 'Track SO, part 3: the Moon locked in synchronous rotation forever (one librational torus '
                        'around a certified synchronous orbit; D42, D45)'),
    ('LG00', 'lg00', 'Side project: a kernel-checked KAM torus of Locatelli–Giorgilli\'s secular Sun–Jupiter–Saturn '
                     'model (first formally verified torus of a planetary model; v2 certifier)'),
]
# Tracks without a source-level dependency graph: track R is proved through track P's quantitative theorem; track SO
# and LG00 are certificate campaigns.
NO_GRAPH = {'R', 'SO-1', 'SO-2', 'SO-3', 'LG00'}


def track_anchors(prefix):
    """Frozen theorems of a track: by manifest id prefix; track SO's parts 2 and 3 split its `spinorbit.*` ids."""
    if prefix in ('so-band', 'so-lock'):
        return so_anchors(prefix == 'so-lock')
    return [a for a in manifest['anchors'] if a['kind'] == 'theorem' and a['id'].split('.')[0] == prefix]


def section_tracks():
    out = ['| Track | Headline | Frozen theorems sealed | Proof graph | Stage |', '|---|---|---|---|---|']
    for t, prefix, head in TRACKS:
        thm = track_anchors(prefix) if prefix else []
        sealed = sum(a['state'] == 'SEALED' for a in thm)
        g = graph_counts(t)
        gtxt = (f'{g[0]} / {g[1]} nodes resolved' if g and g[1] else '—' if t in NO_GRAPH else 'not on `main` yet')
        ftxt = (f'{sealed} / {len(thm)}' if thm else '— (ordinary theorems)' if prefix is None else
                'none frozen yet (freeze approved, D49)' if prefix.startswith('so-') else '0 / 0')
        stage = campaign.get('tracks', {}).get(t, '') if t != 'LG00' else lg00_stage_text()
        out.append(f'| **{t}** | {head} | {ftxt} | {gtxt} | {stage} |')
    return '\n'.join(out)


def section_landed():
    log = git('log', '--first-parent', 'main', '-40', '--date=format:%Y-%m-%d %H:%M', '--format=%cd|%h|%s')
    rows = [l.split('|', 2) for l in log.splitlines() if l]
    rows = [r for r in rows if not r[2].startswith('HQ status')][:12]
    if not rows:
        return '*No commits on `main` yet.*'
    out = ['| When (UTC) | Commit | Change |', '|---|---|---|']
    out += [f'| {d} | `{h}` | {neutral_subject(s).replace("|", "∣")} |' for d, h, s in rows]
    return '\n'.join(out)


def neutral_subject(s):
    """Commit subject without credit to one author or one author's team (the project is joint; owner, 2026-10-29).
    Pushed history is not rewritten, so the README table filters what it shows."""
    names = r'(?:Zohar|Komargodski|zkomargo|Scott|Armstrong)'
    s = re.sub(rf'\s*\((?=[^()]*{names})[^()]*\)', '', s)
    s = re.sub(rf'\s*(?:sealed )?by {names}[^,;)]*?team', '', s)
    s = re.sub(rf'\b(from|into) {names}[^ ]*/\S+', r'\1 a contributor branch', s)
    s = re.sub(rf'\b{names}\'s ', '', s)
    return s


def completion(rows):
    """Weighted completion: items by difficulty weight times their done fraction, plus 1 per sealed statement."""
    w = progress['weights']
    groups = {}
    for it in progress['items']:
        g = groups.setdefault(it['group'], [0.0, 0.0, 0])
        g[0] += w[it['difficulty']]
        g[1] += w[it['difficulty']] * it['done']
        g[2] += 1
    # The original project's sealing row: tracks K, I, N, P and R. Track W's and track SO's own frozen theorems are
    # counted in their own rows below (2026-10-30: a frozen nlw2 must not lower the original project's figure).
    # Track SO's anchors are `spinorbit.*` (SO-FREEZE3, LOCK-FREEZE); `so.` kept for older drafts.
    orig_rows = [r for r in rows if not r[0].startswith(('wave.', 'so.', 'spinorbit.'))]
    if orig_rows:
        sealed = sum(1 for r in orig_rows if r[4] == 'sealed')
        groups['Sealing of the frozen statements'] = [float(len(orig_rows)), float(sealed), len(orig_rows)]
    for g in SO_GROUPS:  # list track SO's two parts after the sealing row, just before the total
        if g in groups:
            groups[g] = groups.pop(g)
    # Track SO part 3 and track W, derived from repository state (lock_progress, w_progress).
    # Weights reflect size against the other rows (track P weighs 30): track W is the largest campaign (34k-70k
    # Lean lines estimated, D30), the lock a new theory on top of track SO.
    lock_pct, lock_done = lock_progress()
    groups[LOCK_GROUP] = [16.0, 16.0 * lock_pct / 100, len(LOCK_STAGES)]
    lg_pct, lg_w = lg00_progress()
    if lg_w:
        groups[LG00_GROUP] = [float(lg_w), lg_w * lg_pct / 100, len(LG00['stages'])]
    w_pct, _ = w_progress()
    groups[W_GROUP] = [64.0, 64.0 * w_pct / 100, 5]
    total = sum(g[0] for g in groups.values())
    done = sum(g[1] for g in groups.values())
    return 100 * done / total, groups, total, done


LOCK_GROUP = 'Track SO, part 3: the Moon locked in synchronous rotation (D42)'
LG00_GROUP = 'Side project LG00: certified torus of the secular Sun–Jupiter–Saturn model'
_lg00_file = root / 'docs/campaign/side/lg00-status.json'
LG00 = json.loads(_lg00_file.read_text()) if _lg00_file.exists() else {'stages': []}


def lg00_progress():
    """Side project LG00 (docs/campaign/side/lg00-status.json): percent done, weighted by stage effort."""
    w = sum(s['weight'] for s in LG00['stages'])
    return (100 * sum(s['weight'] * s['done'] for s in LG00['stages']) / w if w else 0.0), w


def lg00_stage_text():
    st = LG00['stages']
    if not st:
        return ''
    done = [s['name'] for s in st if s['done'] >= 1]
    cur = next((s for s in st if s['done'] < 1), None)
    txt = f'{lg00_progress()[0]:.0f} %: done: ' + ('; '.join(done) or 'none')
    if cur:
        txt += f'; now: {cur["name"]} ({100 * cur["done"]:.0f} %)'
    return txt
W_GROUP = 'Track W: PDE KAM for the cubic wave equation (D30, D41)'
W_MILESTONES = ['W0', 'W1', 'W2', 'W3', 'W4', 'W5', 'W6', 'W7', 'W8']


def w_progress():
    """Track W, derived from repository state only: (percent, parts) with parts = (statements frozen, blueprint
    milestones written, graph published, (resolved, total) graph nodes, nlw2 sealed). Weights: statements 1,
    blueprint 3, graph 1, proofs 10, seal 0.5."""
    frozen = (root / 'KAM/Frozen/Wave/Theorems/Nlw2.lean').exists()
    parts = root / 'blueprint-W' / 'parts'
    written = [m for m in W_MILESTONES if parts.exists() and list(parts.glob(m.lower() + '-*.tex'))]
    g = graph_counts('W')
    nlw2 = next((a for a in manifest['anchors'] if a['id'] == 'wave.nlw2.v1'), None)
    sealed = bool(nlw2 and nlw2['state'] == 'SEALED')
    proof = g[0] / g[1] if g and g[1] else 0.0
    score = 1 * frozen + 3 * len(written) / len(W_MILESTONES) + 1 * bool(g) + 10 * proof + 0.5 * sealed
    return 100 * score / 15.5, (frozen, written, g, sealed)


def w_glance():
    pct, (frozen, written, g, sealed) = w_progress()
    n, lines, thms = lean_stats([root / 'KAM' / 'Wave'])
    stmt = ('frozen (12 anchors; `nlw2` sealed)' if sealed else 'frozen (12 anchors; `nlw2` draft until proved)'
            if frozen else 'approved (D41), freeze in progress')
    gtxt = f'{g[0]} / {g[1]} nodes resolved' if g and g[1] else 'not on `main` yet'
    return ['', f'**Track W** (D30, D41; [plan](blueprint-W/PLAN.md)): PDE KAM for the cubic wave equation '
            f'u_tt = u_xx − m u − u³ on [0, π] (Pöschel 1996) · **{pct:.0f} %**',
            f'- Statements: {stmt} · blueprint milestones written: {len(written)} / {len(W_MILESTONES)} '
            f'({", ".join(written) or "none"}) · proof graph: {gtxt} · `KAM/Wave`: {n} modules, {lines:,} lines',
            *([f'- **Now:** {campaign["w"]["now"]}'] if campaign.get('w', {}).get('now') else [])]


# Stages of track SO part 3, weighted by effort (owner/orchestrator, 2026-10-31; they had counted equally): each
# test reads the repository. The sealed test also accepts the planned anchor `lunar_sync_lock` (LOCK-FREEZE names its
# anchors spinorbit.*, which `so.lunar_lock` alone never matched).
LOCK_STAGES = [
    ('scoping study', 5, lambda: (root / 'docs/tracks/SO/studies/SO-LOCK-SCOPE.md').exists()),
    ('design', 10, lambda: (root / 'docs/tracks/SO/design/SO-LOCK-DESIGN.md').exists()),
    ('statements frozen', 5, lambda: any((root / 'KAM/Frozen/SpinOrbit/Theorems').glob('*Lock*.lean'))),
    ('Lean proof modules', 40, lambda: (root / 'KAM/SpinOrbit/Lock').exists()),
    ('certificate data', 35, lambda: any((root / 'KAM/SpinOrbit/Data').glob('Lock*'))
     if (root / 'KAM/SpinOrbit/Data').exists() else False),
    ('sealed', 5, lambda: any(re.match(r'(?:so\.lunar_lock|spinorbit\.(?:\w+\.)?lunar_sync_lock)', a['id'])
                              and a['state'] == 'SEALED' for a in manifest['anchors'])),
]


def lock_progress():
    """Track SO part 3 (the synchronous lock, D42), read from the repository: (percent by stage weight, stages
    reached)."""
    done = [(name, w) for name, w, test in LOCK_STAGES if test()]
    return 100 * sum(w for _, w in done) / sum(w for _, w, _ in LOCK_STAGES), [name for name, _ in done]


def lock_glance(sessions):
    pct, done = lock_progress()
    suborch = any(t.startswith('kam-suborch-lock') for t in sessions)
    pkgs = sorted(session_package(t, t[len('inp-mprov-'):]) for t in sessions if t.startswith('inp-mprov-lock'))
    now = (f' · the lock sub-orchestrator is running (package workers: {", ".join(pkgs) or "none"})'
           if suborch else '')
    note = campaign.get('so', {}).get('lock_note', '')
    return [f'- **Part 3, the Moon locked in synchronous rotation forever** (D42, D45): one librational invariant torus '
            f'around a certified synchronous periodic orbit confines the spin (a stronger result than the spin-rate '
            f'band; route: polar coordinates, the landed certifier, one new primitive `HamExpr.sqrt`; N = 65) · '
            f'**{pct:.0f} %** · stages reached: {", ".join(done) or "none yet"}' + now + (f'. {note}' if note else '')]


def completion_split(rows):
    """(original project %, SO checker %, SO Moon %, overall %): the original project is every group except track SO
    (its three parts), track W and the side project LG00 (2026-10-31: LG00 had been counted in the original project's
    figure, which read 96.0 % then)."""
    pct, groups, total, done = completion(rows)
    parts = [groups.get(g, [0.0, 0.0, 0]) for g in SO_GROUPS]
    extra = [groups.get(g, [0.0, 0.0, 0]) for g in (LOCK_GROUP, W_GROUP, LG00_GROUP)]
    orig = 100 * (done - sum(p[1] for p in parts + extra)) / (total - sum(p[0] for p in parts + extra))
    so1, so2 = (100 * p[1] / p[0] if p[0] else 0.0 for p in parts)
    return orig, so1, so2, pct


def loc(dirs, generated=False):
    """(total lines, code lines) of the .lean files under `dirs`; code lines exclude blanks and comments. By default
    hand-written only (generated certificate data excluded; generated=True: the data only, None: everything)."""
    st = [file_stats(f) for f in lean_files(dirs, generated)]
    return sum(s[0] for s in st), sum(s[1] for s in st)


def worktree_branches():
    out = git('worktree', 'list', '--porcelain')
    return sorted({l.split('refs/heads/', 1)[1] for l in out.splitlines() if l.startswith('branch refs/heads/')}
                  - {'main'})


def unlanded_split():
    """(hand-written, generated) Lean lines added by the agents' unlanded commits (every branch checked out in a
    worktree). Each non-merge commit not reachable from main counts once, so stacked branches are not double counted.
    2026-10-29: the former `git diff main...b` used one of several merge bases of long-lived branches and
    counted already-landed files as unlanded (8,080 shown for about 2,300 real lines).
    2026-10-30: generated certificate data (KAM/SpinOrbit/Data/) is counted apart; 59.5k lines of lunar literals had
    been shown as unlanded Lean work."""
    return _unlanded()[:2]


_UNLANDED = []


def _unlanded():
    """(hand-written, generated, hand-written by top-level area of KAM/) lines on unlanded agent commits; cached."""
    if _UNLANDED:
        return _UNLANDED[0]
    commits = set()
    for b in worktree_branches():
        commits.update(git('rev-list', '--no-merges', f'main..{b}').split())
    hand = gen = 0
    area = {}
    for c in commits:
        for l in git('show', '--numstat', '--format=', c, '--', '*.lean').splitlines():
            a, _, path = l.split('\t', 2)
            if a.isdigit() and path != 'KAM.lean' and not path.startswith('KAM/Root/'):
                if path.startswith(GENERATED_DATA):
                    gen += int(a)
                else:
                    hand += int(a)
                    key = path.split('/')[1] if path.startswith('KAM/') and path.count('/') > 1 else ''
                    area[key] = area.get(key, 0) + int(a)
    _UNLANDED.append((hand, gen, area))
    return _UNLANDED[0]


def unlanded_lines():
    """Hand-written Lean lines on agent branches, not yet landed (generated data excluded)."""
    return unlanded_split()[0]


def size_estimate(rows):
    """(hand-written lines on main, their code lines, hand-written unlanded lines, total weight, done weight)."""
    total, code = loc(LIB)
    pct, groups, wt, done = completion(rows)
    return total, code, unlanded_lines(), wt, done


HISTORY_HEADER = 'utc,main,modules,lean_lines,code_lines,unlanded_lines,theorems,completion_pct,sealed,generated_lines'


def append_history(rows):
    """One line per run in docs/campaign/history.csv. The columns before `generated_lines` keep their meaning (every
    .lean file under KAM/, generated certificate data included; unlanded_lines is hand-written only). The column
    `generated_lines` (added 2026-10-31) is the generated data's share of lean_lines: hand-written lines on main are
    lean_lines - generated_lines. Older rows have no value there (lines_24h_ago reads their commit instead)."""
    h = root / 'docs/campaign/history.csv'
    unl = unlanded_lines()
    total, code = loc(LIB, generated=None)
    pct = completion(rows)[0]
    n, _, thms = lean_stats(LIB)
    gen = lean_stats(LIB, generated=True)[1]
    sealed = sum(1 for r in rows if r[4] == 'sealed')
    if not h.exists():
        h.write_text(HISTORY_HEADER + '\n')
    else:
        head, _, body = h.read_text().partition('\n')
        if head.startswith('utc,') and 'generated_lines' not in head:
            h.write_text(head + ',generated_lines\n' + body)
    with h.open('a') as f:
        f.write(f'{NOW},{git("rev-parse", "--short", "HEAD")},{n},{total},{code},{unl},{thms},{pct:.1f},{sealed},'
                f'{gen}\n')


def generated_lines_at(commit):
    """Lines of generated certificate data in a commit (git grep counts every line); None for an unknown commit."""
    r = subprocess.run(['git', 'grep', '-c', '', commit, '--', GENERATED_DATA + '*.lean'], cwd=root,
                       capture_output=True, text=True)
    if r.returncode not in (0, 1):
        return None
    return sum(int(l.rsplit(':', 1)[1]) for l in r.stdout.splitlines() if l)


def lines_24h_ago():
    """(hand-written Lean lines, time) of the last history row at least 24 hours old (the first row otherwise)."""
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
    gen = int(r[9]) if len(r) > 9 and r[9].isdigit() else generated_lines_at(r[1])
    return (int(r[3]) - gen, r[0]) if gen is not None else None


# Rough planning figure for the total size; replaced by a rate-based estimate once real proofs land.
PLANNED_TOTAL = 40000


def lean_item(it):
    """Lean proof work: track K's analysis, a-posteriori and measure items, and the proof items of tracks I, N, P."""
    return it['id'].split('.')[0] in ('F', 'K', 'M') or '.PROOF' in it['id']


def size_parts(rows):
    """The size estimate in parts (hand-written lines only): the other tracks scaled by the done share of their Lean
    work items; track SO from its design; track W from its planning range (campaign.json size_plan.W)."""
    total, code, unl, _, _ = size_estimate(rows)
    w = progress['weights']
    lean = [it for it in progress['items'] if lean_item(it)]
    lean_all = sum(w[it['difficulty']] for it in lean)
    lean_done = sum(w[it['difficulty']] * it['done'] for it in lean)
    so_on_main = loc([root / 'KAM' / 'Certificate', root / 'KAM' / 'SpinOrbit'])[0]
    landed = set(campaign.get('so', {}).get('landed', []))
    so_left = sum(v[0] for it in progress['items'] for k, v in it.get('so_packages', {}).items()
                  if k not in landed and not v[1][0].startswith('scripts/'))
    wave = loc([root / 'KAM' / 'Wave'])[0] + _unlanded()[2].get('Wave', 0)
    plan = campaign.get('size_plan', {}).get('W', {})
    lo, hi = plan.get('low', 0), plan.get('high', 0)
    rest = total + unl - so_on_main - wave        # tracks K, I, N, P, R, the sharp a-posteriori work, the rest
    rest_est = rest / lean_done * lean_all if lean_done >= 8 else PLANNED_TOTAL
    fixed = rest_est + so_on_main + so_left
    est, est_lo, est_hi = (fixed + max(x, wave) for x in ((lo + hi) / 2, lo, hi))
    return dict(total=total, code=code, unl=unl, est=est, est_lo=est_lo, est_hi=est_hi, so_left=so_left, wave=wave,
                lo=lo, hi=hi, source=plan.get('source', ''), share=lean_done / lean_all if lean_all else 0.0,
                rate_based=lean_done >= 8)


def section_size(rows):
    z = size_parts(rows)
    total, unl, est = z['total'], z['unl'], z['est']
    gen_unl = unlanded_split()[1]
    gn, gl, gt = lean_stats(LIB, generated=True)
    prev = lines_24h_ago()
    growth = f' · **{total - prev[0]:+,}** since {prev[1]}' if prev else ''
    left, left_lo, left_hi = (max(x - total - unl, 0) for x in (est, z['est_lo'], z['est_hi']))
    rng = (f' ({round(left_lo, -3):,.0f}–{round(left_hi, -3):,.0f} over the range of track W\'s plan)'
           if z['hi'] > z['lo'] else '')
    how = (f'scales the lines written so far for the other tracks (on `main` plus the agent branches: tracks K, I, N, '
           f'P and R, the sharp a-posteriori theorems and certifiers, the shared infrastructure) by the done share of '
           f'the Lean work items, weighted by difficulty (track K\'s analysis, a-posteriori and measure items and the '
           f'proof items of tracks I, N and P: {100 * z["share"]:.0f} % done); adds track SO from its design (its '
           f'lines on `main` plus the line estimates of its packages not yet landed, {z["so_left"]:,} lines; the Lean '
           f'packages of part 3 are on `main`, and what it still needs is generated data); and adds track W from its '
           f'planning range of {z["lo"]:,}–{z["hi"]:,} lines ({z["source"]}; midpoint used), of which '
           f'{z["wave"]:,} are written. The side project LG00 is not counted: its certificate never enters this '
           f'library' if z['rate_based'] else
           'is a planning figure; it switches to a rate-based estimate once 8 weight units of Lean work are done')
    out = ['### Size of the formalization', '',
           '| | Lines of Lean |', '|---|---|',
           f'| On `main` now (hand-written) | **{total:,}** ({z["code"]:,} excluding blank lines and comments){growth} |',
           f'| Generated certificate data on `main` (numeric literals; not counted in the other rows) | {gl:,} lines '
           f'in {gn:,} modules |',
           f'| Written on agent branches, not yet landed (hand-written) | {unl:,} |',
           *([f'| Generated certificate data on agent branches (numeric literals; not counted in the other rows) | '
              f'{gen_unl:,} |'] if gen_unl else []),
           f'| **Estimated total at completion** (hand-written) | **≈ {round(est, -3):,.0f}** |',
           f'| Estimated still to write | ≈ {round(left, -3):,.0f}{rng} |', '',
           f'**How the size is estimated.** Every figure except the two rows of generated data counts hand-written Lean '
           f'only: the generated certificate data under `{GENERATED_DATA}` (the barrier tori of the Moon, emitted by '
           f'`scripts/spin_orbit/` and checked by the kernel) are counted apart. The estimate {how}. History of all '
           'counts: [`docs/campaign/history.csv`](docs/campaign/history.csv) (`lean_lines` counts every module, '
           '`generated_lines` the generated data among them).']
    return '\n'.join(out), est


def bar(pct, n=25):
    k = round(pct / 100 * n)
    return '█' * k + '░' * (n - k)


def section_updated(rows, est):
    orig, so1, so2, pct = completion_split(rows)
    sealed = sum(1 for r in rows if r[4] == 'sealed')
    total = loc(LIB)[0]
    gen = lean_stats(LIB, generated=True)[1]
    return (f'> **Last updated: {NOW}** (automatic: every 20 minutes and after every commit) · '
            f'**estimated completion: original project {orig:.1f} % · SO checker {so1:.0f} % · SO Moon {so2:.0f} % · '
            f'Moon locked {lock_progress()[0]:.0f} % · track W {w_progress()[0]:.0f} %** · '
            f'frozen statements proved: {sealed} / {len(rows)} · '
            f'**{total:,} lines of hand-written Lean** of an estimated ≈ {round(est, -3):,.0f}' +
            (f' (plus {gen:,} lines of generated certificate data, not counted)' if gen else ''))


def section_progress(rows):
    pct, groups, total, done = completion(rows)
    orig, so1, so2, _ = completion_split(rows)
    out = [f'### Estimated completion: original project **{orig:.1f} %** · SO checker **{so1:.0f} %** · '
           f'SO Moon **{so2:.0f} %** · Moon locked **{lock_progress()[0]:.0f} %** · track W **{w_progress()[0]:.0f} %** · '
           f'LG00 **{lg00_progress()[0]:.0f} %**', '',
           f'Original project (tracks K, I, N, P): `{bar(orig)}` {orig:.1f} %', '',
           f'Track SO, part 1, the general Lean certificate checker: `{bar(so1)}` {so1:.1f} %', '',
           f"Track SO, part 2, the Moon's spin rate (its first client): `{bar(so2)}` {so2:.1f} %", '',
           f'Track SO, part 3, the Moon locked in synchronous rotation forever (D42): `{bar(lock_progress()[0])}` '
           f'{lock_progress()[0]:.0f} % (stages, weighted by effort: ' +
           ', '.join(f'{n} {w}' for n, w, _ in LOCK_STAGES) + '; each read from the repository)', '',
           f'Track W, PDE KAM for the cubic wave equation: `{bar(w_progress()[0])}` {w_progress()[0]:.1f} % '
           '(statements frozen 1, blueprint milestones 3, graph published 1, graph nodes resolved 10, seal 0.5; '
           'all read from the repository)', '',
           f'Side project LG00, a certified torus of the secular Sun–Jupiter–Saturn model: `{bar(lg00_progress()[0])}` '
           f'{lg00_progress()[0]:.0f} % (stages, weighted by effort: ' + ', '.join(s['name'] for s in LG00['stages']) + '; '
           'from [`docs/campaign/side/lg00-status.json`](docs/campaign/side/lg00-status.json), the side orchestrator\'s '
           f'assessment, last reviewed {LG00.get("reviewed", "")})', '',
           f'Overall, everything together: {pct:.1f} %', '',
           '| Part of the project | Items | Weight | Done | Completion |', '|---|---|---|---|---|']
    for name, (wt, dn, n) in groups.items():
        out.append(f'| {name} | {n} | {wt:.0f} | {dn:.1f} | `{bar(100 * dn / wt, 10)}` {100 * dn / wt:.0f} % |')
    out.append(f'| **Total** | {sum(g[2] for g in groups.values())} | {total:.0f} | {done:.1f} | **{pct:.1f} %** |')
    out += ['', f'**How this is estimated.** The project is divided into {len(progress["items"])} work items: planning '
            'deliverables, campaign infrastructure, the four layers of track K\'s proof, the proof campaigns of '
            'tracks I, N and P, and parts 1 and 2 of track SO (their items count the design\'s line estimates of the '
            'packages landed so far; [`docs/campaign/progress-SO.json`](docs/campaign/progress-SO.json)). Each item is '
            'weighted by its difficulty (low 1, moderate 2, high 4, very high 8) and '
            'counts with the fraction of it that is done; each sealed frozen theorem adds 1. Items marked *graph* '
            'take that fraction from their proof graph (nodes `PROVED`, `BYPASSED`, `EXTERNAL` or owner-accepted `ASSUMED` in '
            '[`docs/graph/`](docs/graph)), so they update themselves at every refresh, and count as complete once '
            'every frozen theorem of their track is sealed; the other items are the '
            f'orchestrators\' assessment, last reviewed **{progress["reviewed"]}**. Files: '
            '[`docs/campaign/progress.json`](docs/campaign/progress.json) (track K and infrastructure) and '
            '[`docs/campaign/progress-INP.json`](docs/campaign/progress-INP.json) (tracks I, N, P). The rows of track '
            'SO part 3, track W and the side project LG00 are not work items: they take their fraction from the meters '
            'above, with weights 16, 64 and the LG00 stage weights.',
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


PAPER_GROUPS = [
    ('core', 'Core sources of the KAM proof (track K)'),
    ('original', 'Original papers'),
    ('statement', 'Statement sources'),
    ('track I/N/P', 'Sources shared by tracks I, N and P'),
    ('track N', 'Track N: Nekhoroshev stability'),
    ('track N/P', 'Tracks N and P'),
    ('track P', 'Track P: planetary systems'),
    ('reference', 'Reference works'),
    ('cross-check', 'Cross-checks'),
    ('errata', 'Errata sources'),
    ('context', 'Context and further reading'),
]


def paper_groups():
    known = {t for t, _ in PAPER_GROUPS}
    groups = [(title, [p for p in sources if p.get('tier') == t]) for t, title in PAPER_GROUPS]
    groups.append(('Other sources', [p for p in sources if p.get('tier') not in known]))
    return [(title, ps) for title, ps in groups if ps]


def papers_page():
    """docs/PAPERS.md: every pinned source, grouped, with links, its role, the frozen theorems citing it and its errata."""
    thms = [a for a in manifest['anchors'] if a['kind'] == 'theorem']
    errata = {}
    for e in ledger['entries']:
        errata[e.get('source')] = errata.get(e.get('source'), 0) + 1
    out = ['# Papers', '',
           f'*Generated by `scripts/hq-status.py` from [`docs/sources.json`](sources.json); back to the '
           f'[README](../README.md).*', '',
           f'The formalization pins {len(sources)} sources. The PDFs live in `sources/pdf/` (kept out of git) with '
           'their SHA-256 hashes in [`sources/SHA256SUMS`](../sources/SHA256SUMS); arXiv versions were read from the '
           'pinned PDFs, and DOIs come from the arXiv API or exact Crossref title matches. Each entry says what the '
           'project uses the source for, which frozen theorems cite it, and how many errata were recorded against it '
           '(see the README\'s errata section).', '', '## Index', '']
    for title, ps in paper_groups():
        out.append(f'- **{title}:** ' + ' · '.join(f'[{p["key"]}](#{p["key"].lower()})' for p in ps))
    for title, ps in paper_groups():
        out += ['', f'## {title}']
        for p in ps:
            links = []
            if p.get('arxiv'):
                links.append(f'[arXiv:{p["arxiv"]}](https://arxiv.org/abs/{p["arxiv"]})')
            if p.get('doi'):
                links.append(f'[doi:{p["doi"]}](https://doi.org/{p["doi"]})')
            if p.get('chapter_doi'):
                cd = p['chapter_doi'].split(' ', 1)
                links.append(f'[chapter doi:{cd[0]}](https://doi.org/{cd[0]})' + (f' {cd[1]}' if len(cd) > 1 else ''))
            if p.get('url'):
                links.append(f'[{p["url"].split("/")[2]}]({p["url"]})')
            pat = re.compile(rf'(?<![A-Za-z0-9]){re.escape(p["key"])}(?![A-Za-z0-9])')
            cited = [a['export'] for a in thms if pat.search(json.dumps(a.get('source', ''), ensure_ascii=False))]
            out += ['', f'### {p["key"]}', '', p['citation'], '',
                    ('Links: ' + ' · '.join(links)) if links else 'Links: none (print only).', '',
                    f'**Used for.** {p["role"]}']
            if cited:
                out += ['', '**Cited by the frozen theorems** ' + ', '.join(f'`{c}`' for c in cited) + '.']
            if errata.get(p['key']):
                n = errata[p['key']]
                out += ['', f'**Errata recorded:** {n} {"entry" if n == 1 else "entries"}.']
    return '\n'.join(out) + '\n'


def section_papers():
    page = root / 'docs' / 'PAPERS.md'
    text = papers_page()
    if not page.exists() or page.read_text() != text:
        page.write_text(text)
    groups = paper_groups()
    out = [f'**{len(sources)} pinned sources.** The annotated list, with links, what each source is used for, the frozen '
           'theorems citing it and its recorded errata, is on its own page: **[docs/PAPERS.md](docs/PAPERS.md)**.', '']
    out += [f'- {title}: ' + ', '.join(f'[{p["key"]}](docs/PAPERS.md#{p["key"].lower()})' for p in ps)
            for title, ps in groups]
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
