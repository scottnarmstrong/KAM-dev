# Independent audit S8-B, audit 1

Overall verdict: **PASS WITH NOTES** for the S8-B definition package. There is no frozen anchor, provider export, or new theorem in scope; seal-readiness is not applicable. No mathematical or implementation defect was found in the assigned module. The notes concern the permitted stale generated root and explicitly bounded downstream ownership.

Audited worktree: `/root/code/KAM-inp-s8b`. HEAD `6f2cb1ec6284a98aaffeed74340762f20f4afc04`; comparison ref `inp` was `408ea7a6f026a1ecf1d0cf0e988bdc54494497f9`. `git diff inp...HEAD` contains exactly one new file, `KAM/Planetary/SecularForm/Basic.lean` (82 lines). The handoff names `6aab906`; the later `6f2cb1e` commit rewraps its docstring only. The pre-existing untracked handoff was left untouched. This report is written in the package worktree as the user's explicit path instruction requires, overriding the generic brief's MAIN-worktree destination.

Read: AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, S8-B handoff/AUDIT FOCUS, P810 Revision 2 design and both design audits, Part 8 blueprint conventions/definitions and relevant pair-average passages, track-P statement, frozen SecularAverage/Assemble/PlaneLength definitions and delivered Poincare/Newtonian definitions. The original signatures live at `/root/code/KAM-inp/.drafts/design/P810Signatures.lean`, not in this worktree. SHA-256: `492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`. All 22 named declaration blocks match that file verbatim and the design appendix; comparison includes complete bodies and Data fields.

## Declaration-by-declaration assessment

Names are relative to `KAM.Planetary.SecularForm`; line numbers refer to Basic. Blueprint labels below have prefix `bpP:p8:` unless otherwise indicated. Infrastructure rows implement definitions only, not the entire associated theorem node.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| conv#data / carrier | `Vec` (32) | PASS | Real Pi carrier, no new norm instance. |
| conv#data / carrier | `CVec` (33) | PASS | Complex Pi carrier. |
| conv#data / carrier | `Mat` (34) | PASS | Real matrix carrier; no new instance. |
| conv#data / carrier | `Slow` (35) | PASS | Product in literal (xi,Lambda,eta) order. |
| conv#data / carrier | `CSlow` (36) | PASS | Same product over complex scalars. |
| conv#data | `Data` (38) | PASS | Only G,m0,m and their positivity, plus positive dimension. |
| conv#data / axes | `axes` (47) | PASS | Positive strictly increasing axes; no ordering of masses/actions imposed. |
| conv#data / actions | `action` (48) | PASS | Literal m_i sqrt(G m0 a_i). |
| conv#data / actions | `axis` (49) | PASS | Literal I_i^2/(m_i^2 G m0); inverse claims require action domain. |
| conv#data / actions | `actionDomain` (50) | PASS | Exact image of positive ordered axes under action. |
| p7:product-chart(b) / frequency | `nu` (51) | PASS | Literal Kepler frequency (G m0)^2 m_i^3/I_i^3. |
| conv#data / matched models | `perturbation` (52) | PASS | true selects delivered moving model, false fixed model; coupling independent. |
| conv#data / average | `secular` (56) | PASS | Literal frozen secularAverage, with (I,p,q)=(Lambda,eta,xi). |
| conv#data / slow restriction | `slowSecular` (58) | PASS | Fixes actions; slow variation order (xi,eta). |
| conv#data / domain | `slowDom` (60) | PASS | Exact zero-fast-angle section of poincareProdDom; independent of D as intended. |
| conv#data / angular cell | `cell` (62) | PASS | Closed radian cell [0,2*pi]^n. |
| conv#data / average | `avg` (63) | PASS | Normalized Bochner integral, scalar factor (2*pi)^(-n). |
| rho | `rho` (65) | PASS | Literal rho_0 finite infimum of min(Lambda_i/2,sqrt(Lambda_i)/16); not rho_*. |
| conv#data / polydisc | `polydisc` (67) | PASS | Coordinatewise strict complex radii centered at (0,action D a,0). |
| conv#data / inclusion | `inclusion` (69) | PASS | Componentwise real-to-complex embedding in unchanged tuple order. |
| conv#data / real polydisc | `realDisc` (71) | PASS | Exact preimage under inclusion; no substitute neighborhood. |
| quadratic-form / qf-pair; quartic | `pairSlowSecular` (74) | PASS | Literal double radian average of negative Newtonian pair potential; only I,J and two slow vectors. |

## Definition classification and whole-carrier behavior

Five abbreviations are transparent carrier notation; Data is standing physical/typing data only. The sixteen `def`s are literal scalar formulas, model compositions, integrals, sets, or embeddings. No definition bundles an analytic/spectral conclusion, adds an instance, chooses an unproved radius, or replaces the frozen average. `@[expose] public noncomputable section` exposes the intended bodies. No new theorem premises, weakened conclusions, constants with wider dependence, or proof steps assumed as hypotheses occur.

The whole-carrier assessment distinguishes total definitions from their later physical interpretations:

- `action` uses Lean's total real square root on all real vectors; `axis` and `nu` use total division, including at zero. They match the prescribed definitions everywhere. Inverse, positivity, and frequency interpretations require the intended positive axes/actions; S8-B asserts none of these results globally.
- `rho` matches the finite minimum when Data supplies `0<n`; there is no empty physical index set. Its positivity requires `a ∈ axes n`, and no positivity theorem is claimed here. `polydisc` and `realDisc` also accept arbitrary real radii, yielding the literal strict-inequality sets (empty for nonpositive radius with positive dimension).
- `perturbation` and `pairSlowSecular` reuse the delivered total Poincare chart. In particular the upstream `keplerLong` (KAM/Kepler/Equation.lean:117) returns zero outside `planeLength v < 1`; Newtonian reciprocal lengths use total division at collisions. These are unchanged upstream extensions, not newly selected physical values. No theorem in this package relies on those fallback values. Physical chart and collision guards must be paid by later analytic packages.
- `avg`, `secular`, and `pairSlowSecular` are the actual totalized integrals, with zero for nonintegrable Bochner integrands. The generic avg deliberately has the exact draft type without a CompleteSpace premise. Integrability/regularity is not inferred here. The Part 8 identification proof explicitly discusses the nonintegrable-zero convention; the package does not claim subtraction identities without integrability.
- `slowDom` guards individual chart validity only, not pairwise collision avoidance, action ordering, or analyticity. Evaluating fast angles at zero is the draft's exact section: the delivered chart-domain predicate depends only on actions and squared slow coordinates. `pairSlowSecular` is defined even for equal indices and unordered actions; physical pair results must add their intended guards.

The two normalization factors in the pair average are each `(2*pi)^(-1)`. Its denominator is the frozen Euclidean `planeLength`, not the ambient Pi max norm. The pair slow vectors contain `(xi_i,eta_i)` and `(xi_j,eta_j)`; the chart inputs are `((s,xi_i),(I,eta_i))` and `((t,xi_j),(J,eta_j))`. The general secular wrapper uses exactly the same coordinate dictionary.

## Independent checks

All auditor-controlled Lean/Lake invocations are sequential with `LEAN_NUM_THREADS=1` and `nice -n 5`; the targeted build uses the prescribed compile gate. No root regeneration, cache fetch, library clean, production edit, or state-changing git command was used.

### Targeted build: PASS, exit 0

```text
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s8b KAM.Planetary.SecularForm.Basic
[inp-gate] slot 1 acquired 09:12:42 for KAM.Planetary.SecularForm.Basic
✔ [9109/9109] Built KAM.Planetary.SecularForm.Basic (12s)
Build completed successfully (9109 jobs).
```

The gate runs `nice -n 5 lake build`. Replayed upstream unused-variable warnings occurred in Energy.lean (106), Chart.lean (212,247) and Mass.lean (147,157,500,524). No warning was emitted for Basic.lean. The job count includes replayed dependency jobs; this was the single targeted build, not a library rebuild from scratch.

### Axioms and literal-identity probes: PASS, exit 0

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S8BAudit.lean
'KAM.Planetary.SecularForm.Vec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.CVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Mat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Slow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.CSlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.Data' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.axes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.action' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.axis' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.actionDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.nu' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.secular' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.slowSecular' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.slowDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.cell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.polydisc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.inclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.realDisc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairSlowSecular' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The same probe elaborated three examples with `rfl`: secular equals its literal frozen wrapper; secular equals `avg` of perturbation on `assemble Lambda t eta xi`; slowSecular equals secular on `(u.1,I,u.2)`. All hold on the entire declared carrier, without integrability or physical-domain assumptions. Provider/frozen type-equality and seal-body probes are not applicable because the package contains neither a provider nor a theorem anchor. There are no new public theorems requiring separate axiom reports.

### Kernel replay: PASS, exit 0

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.Basic
replaying KAM.Planetary.SecularForm.Basic
```

One invocation covers the only package module. There are no separate provider/lemma modules.

### Repository lint: permitted exception only, exit 1

```text
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (508 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The sole complaint is exactly the generated-root exception allowed by the audit brief. No forbidden-token, line-length, file-length, module-format, errata-rendering or frozen/ABI failure was reported. The root was left unchanged.

### Static and protected-path checks: PASS

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no output)
git diff --check inp...HEAD
(no output; exit 0)
git diff --name-only inp...HEAD
KAM/Planetary/SecularForm/Basic.lean
```

Independent Python scans reported:

```text
SIGNATURE SOURCE MATCH: all 22 named declarations match verbatim
PROJECT IMPORT CLOSURE: 63 modules; 47 frozen definitions
PROVIDER/FROZEN THEOREM IMPORTS: []
LINES 82
OVER_100 []
FORBIDDEN []
```

The import scan recursively follows KAM imports (Mathlib is external). None is a provider or frozen theorem, so no imported theorem requires a SEALED-state exception. Basic has the copyright header, `module`, public imports, module docstring and public exposed section. There is no forbidden proof token or option override, and no line exceeds 100 Unicode characters.


## Scope notes, uncertainties, and suspected defects

1. The allowed generated-root lint exception does not authorize editing `KAM.lean`. No protected file changed.
2. The S8-B row (design line 420) assigns Data, domains, literal averages, rho, inclusion, actions, and pairSlowSecular. All are delivered. Complex continuations (`planetC`, `separationC`, `perturbationC`, `secularC`), rotations and position/momentum adapters remain outside this audit, as the handoff says. The package table does not explicitly enumerate ownership of all those definitions; later owners must supply/import them before their consumer statements can compile. This is an implementation-planning note, not a missing S8-B export under the assigned row.
3. `rho` is rho_0, not an existence proof for a common collision-free rho_*. No analyticity, averaged-model identification, coefficient expansion, spectral result, torsion, or frozen theorem is closed by S8-B. The earlier design audit PASS is contract evidence only; the present audit independently checked these definition bodies.
4. No new suspected pinned-source or blueprint defect, and no mathematical deviation introduced by this package, was found. Previously recorded Part 8 matrix-normalization errata are outside this definition-only scope and were not re-audited against pinned PDFs.

Only this report was added to repository content by the auditor; temporary Lean probes are removed after checking.
