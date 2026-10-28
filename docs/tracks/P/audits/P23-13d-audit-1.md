# P23-13d independent package audit 1

Overall verdict: **PASS WITH NOTES** for P23-13d. Both signed declarations pass statement and proof review; the targeted build, signature/axiom probe and kernel replay pass independently. Source lint has only the explicitly permitted stale generated-root failure. There is no frozen anchor in this package, so no per-anchor seal verdict applies.

## Scope and authority

Audited HEAD `febe6208ce10809020c4cd94ab2f27655d509e24` in `/root/code/KAM-inp-p2313d`. Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local P23-13d handoff, track P statements, design Revision 3 and Appendix A.3, the design audit, and `/root/code/KAM-inp/.drafts/design/P23Signatures.lean`. The user's exact worktree report destination overrides the generic brief's MAIN-worktree destination.

`git diff inp...HEAD` at `inp=05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2` adds three files: OscillatorSeriesAlgebra (335 lines), OscillatorAdjoint (312), and OscillatorCompositionSeries (101). The focus comparison `git diff inp-p2313c...HEAD`, with `inp-p2313c=fd01549d5738a7b6652cfd75c11bd98e86523e07`, adds **only** `KAM/Planetary/Averaging/OscillatorCompositionSeries.lean`. The inherited 13b/13c implementations are dependencies, not new audited declarations here. Their consumed interfaces and relevant limit argument were inspected.

This is a helper package with **no frozen theorem anchor or provider export**. Provider/frozen type-equality and seal-body probes are therefore inapplicable. This audit cannot seal a planetary anchor, close the full `osc_iter`, or release P23-15; R3.6 retains the later full-contract gate.

## Declaration fidelity

All Lean names below have prefix `KAM.Planetary`; implementation locators refer to `KAM/Planetary/Averaging/OscillatorCompositionSeries.lean`.

| Node / obligation | Declaration | Verdict | Reason |
|---|---|---|---|
| `bpP:p2:s-osc#data`; R3.5 P23-13d | `OscComposeData`, lines 34–43 | PASS | Structure and all seven fields match the shared signature and Appendix A.3 exactly, including binder order and numerical smallness. Fields are source inputs, with no flow, series identity, remainder or reality conclusion. |
| `stepP:p2:oi-ratio`; R3.5 P23-13d | `osc_lie_series`, lines 49–96 | PASS | Full signature matches both authorities exactly: one-loss assumptions, two-loss carrier, actual factorial adjoints, pointwise HasSum, holomorphic/periodic sum, exact q-bound, and uniform weighted tails. No additional premise or widened constant dependence. |

A Python extraction compared the structure command and the entire theorem statement before its proof against both authorities, reporting four `EXACT TEXT MATCH` results. Shared signature SHA256: `d067d47dbabfdf4913da3e2b76886eb29598f4502ad16318d328568d82380cd3`. Audited implementation SHA256: `e55bc9a3cd7dbfbc83cf142b9984e949e5ae37fe1a480c2bcbb487f1c9b69ad2`.

The precise new signature is a component of blueprint `blueprint-P/parts/p2-averaging.tex:192`, not the whole node: flow identification and integral composition belong to 13e/13f. The sharper q-bound is the intended R3 refinement; q ≤ theta gives compatibility with the blueprint's coarser ratio without changing its constants.

## Definitions and proof review

The sole new definitional object is the Prop structure `OscComposeData`. Its dimension assumptions, twice-loss widths, generator class/bound, nonnegative majorant and smallness describe the intended inputs on the entire carrier. There are no new defs, abbrevs, instances, alternate Hamiltonians, flows, coefficient norms or truncations. Constructor/projections are the generated API of this source-premise bundle. Empty D is allowed and entails the expected vacuous domain assertions; no nonemptiness premise is added.

The local lets V and L are the exact two-loss domain and literal pointwise total tsum of factorial-scaled `Canonical.adPow`, respectively. Total tsum outside the controlled domain is not used as a convergence assertion: HasSum is explicitly proved on V. Existing `oscDom`, `oscClass`, `oscBound`, flat packing and `adPow` were inspected. Only fast angles are Fourier-expanded; phase dimension is n+m, flat parameter dimension n+(m+m), and class includes holomorphy plus period-one fast-angle invariance. No EuclideanSpace or alternate ambient norm is introduced.

At lines 62–69, positive losses imply d=min(rho*sigma,rhop*rhoq)>0. `osc_ratio_range` supplies 0 ≤ q ≤ theta and (16/9)theta < 1, hence q < 1 and a positive denominator. At lines 79–85, `osc_adjoint_bound` is instantiated with u on the one-loss domain and the generator on its original domain. All outer-margin inequalities are equalities; twice-loss margins imply each remaining loss fits. Its raw adjoint class is closed under multiplication by the inverse complex factorial. The j=0 term is covered by the dependency's explicit zero-index branch.

At lines 86–94, the nonnegative summable majorant is q^j*A, and the second angle width is positive. `osc_bound_tsum` yields the sum's class, weighted bound and tails. Its implementation uses uniform convergence and `uniform_limit_holomorphic` for holomorphy, termwise periodicity, coefficient/series interchange at fixed flat parameters, and finite coefficient sums for the weighted bound. The tails use shifted summable series and preserve the same domain and quantified epsilon/N/N' contract. The geometric identity gives sum(q^j*A)=(1-q)^(-1)*A, including q=0 or A=0. Finally `oscBound.norm_le` and `Summable.of_norm_bounded` prove pointwise summability and HasSum on V. No flow equality or reality assertion is assumed or claimed here.

## Hygiene and independent checks

All final Lean/Lake checks are serialized with `LEAN_NUM_THREADS=1` and niceness 5. The lint script's internal ABI Lean process was also checked to have that environment and niceness. An initial lint attempt was stopped during its Python guard before any ABI Lean process started, and the gate-waiting build was stopped before acquiring a slot, so the full lint could run in isolation; these interrupted scheduling attempts supply no validation evidence.

Command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Output (exit **1**):

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (554 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The stale generated root is the sole reported failure and is expressly permitted by the audit brief. It was not regenerated.

Signature/axiom probe (temporary `.lake/abi-scratch/P2313dAudit.lean`, removed after use): imported the implementation and restated the complete exact signed theorem as an `example`, proved by `exact osc_lie_series H hu hb hA`; then printed its axioms.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2313dAudit.lean
```

Output (exit **0**, no warnings):

```text
'KAM.Planetary.osc_lie_series' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is every new explicitly declared public theorem in the package. No `sorryAx` or additional axiom occurs. The Prop structure's generated constructor/projections introduce no new assumed proposition.

The build waiter was paused before it acquired a slot while the probe and kernel replay ran serially. Kernel replay command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.OscillatorCompositionSeries KAM.Planetary.Averaging.OscillatorAdjoint KAM.Planetary.Averaging.OscillatorSeriesAlgebra
```

Output (exit **0**):

```text
replaying KAM.Planetary.Averaging.OscillatorSeriesAlgebra
replaying KAM.Planetary.Averaging.OscillatorAdjoint
replaying KAM.Planetary.Averaging.OscillatorCompositionSeries
```

Targeted build command (the gate runs `nice -n 5 lake build`):

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2313d KAM.Planetary.Averaging.OscillatorCompositionSeries
```

Output (exit **0**, no warning or sorry diagnostic):

```text
[inp-gate] slot 1 acquired 11:51:47 for KAM.Planetary.Averaging.OscillatorCompositionSeries
Build completed successfully (9121 jobs).
```

This was the prescribed single targeted module build against the existing worktree build overlay. No unqualified library build, cache fetch or clean was run.

Static checks:

- File length: **101 lines**. Copyright, `module`, public interface imports, module docstring, `@[expose] public noncomputable section` all present.
- Source scans: no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or `set_option` in the audited file; no resource overrides.
- Source import traversal: 75 KAM modules, **no provider modules and no frozen theorem anchors**. The 12 transitive frozen imports are all definition anchors with manifest state **SEALED**: ActionNbhd, ComplexStrip, OmegaZero, IsPrimaryOnStrip, IsRealOnReals, HamiltonianVectorFieldC, HamiltonianVectorField, Planetary/Phase, IsDiophantine, SymplecticForm, Planetary/Fast and Planetary/Slow. Relevant frozen bodies were read. No DRAFT_SORRY import is hidden in that source closure.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
- `git diff --check`: empty, exit 0.

## Suspected errata, deviations and limitations

No new suspected pinned-source defect, signature deviation or implementation defect found. No pinned PDF was freshly audited; the exact local design/signature and blueprint contracts control this helper audit.

The inherited blueprint issue remains at `blueprint-P/parts/p2-averaging.tex:177`: the derivative display uses `1/(e(S_0-S))` while the bracket hypotheses at line 173 require only `S-sigma<S_0`. The latter does not force S_0-S positive. R3.4 (design line 1335) already flags this and requires the landed target-width derivative estimates. This package uses those existing adjoint estimates with the original generator strictly outside the one-loss u domain, and never uses the potentially nonpositive displayed denominator. This is an inherited documented issue, not a new defect introduced by 13d.

Only this report is an intended repository edit. Temporary audit probes are confined to `.lake/abi-scratch/` and were removed. No state-changing git operation, frozen edit, generated-root regeneration or library rebuild was performed.
