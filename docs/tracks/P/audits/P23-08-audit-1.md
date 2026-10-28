# P23-08 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the assigned P23-08 infrastructure contract. No mathematical or signature defect found. No frozen theorem anchor or provider is assigned to this package; “seal-ready” is therefore not applicable, and this report does not certify P-G or the complete Part 3 torus dictionary.

Audited HEAD `ff12f667dfda932168bc7d1a9bc1f8083c1b89ce`, against `inp` at `42e1afbf28c6097caabe5a9b6d5d7a81463eeae7`, using `git diff inp...HEAD`. The entire production delta is the 287-line new file `KAM/Planetary/TwoScale/Period.lean`, SHA256 `b4484af65edf3099266b02a0694faea6a7db0c88dd2733efc13d63adc6c712bf`.

Read AGENTS.md, PLAN, DECISIONS, the package audit brief, P23-08 handoff/focus, P23 design revision 2 and both design audits, the relevant P statement conventions, P1 period conversion, P2 use5, P3 period dictionary and its proof steps, and the imported carrier/norm/constant/vector-field definitions. The shared signature file is outside this worktree at `/root/code/KAM-inp/.drafts/design/P23Signatures.lean`; SHA256 `7d7dae4308ea9ec0ca763a2a21ce4b83280bdbb4b91d2c4f5e7567b71085e834`, matching design audit 2. The user's explicit report destination overrides the generic brief's MAIN-worktree destination.

## Declaration review

All names below have prefix `KAM.Planetary`. Line numbers refer to Period.lean.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| `bpP:p3:period-dictionary`, `stepP:p3:pd-invar` | `period_dictionary` (37) | PASS | Exact signature; simultaneous transformations preserve x, K, radius and error. All scalar data allowed, including zero denominators under Lean's total division; stronger than the positive-data source use. |
| `bpP:p2:use5` scalar dictionary | `use5_constants` (76) | PASS | Exact signature; preserves radius-width product, cutoff ratio and the smallness equivalence. Division by positive 2π preserves the inequality; αcp=0 handled explicitly. |
| `stepP:p3:pd-subst` | `period_dictionary_coeff` (111) | PASS | Exact signature; integral linearity divides coefficients by 2π and propagates summability plus the fixed-action weighted bound. Same domain and geometric weight radius; no exchange of sum and supremum. |
| Auxiliary chart | `diagChart` (148) | PASS | Actual bounded complex-linear diagonal coordinate map on the whole carrier. |
| Auxiliary evaluation | `diagChart_apply` (154) | PASS | Definitional evaluation, no premise. |
| Auxiliary conformal field law / P1(b) | `diagChart_field` (159) | PASS | Chain rule at the stated differentiability point, then coordinate identities from aᵢbᵢ=κ≠0. These are chart premises, not an assumed field-conjugacy conclusion. General complex κ and arbitrary diagonal weights strengthen the required case. |
| `stepP:p3:pd-dyn`, P1(b) | `period_dictionary_field` (212) | PASS | Exact signature; Q=(2πθ,I), Hamiltonian divided by 2π, same-time vector-field transport. See integration note below. |
| `bpP:p2:use5` chart | `oscPeriodChart` (233) | PASS | Exact design body; fast angle/action scales reciprocal, oscillator position/momentum blocks unchanged. |
| Auxiliary weights | `oscWeight` (238) | PASS | Exact blockwise diagonal weights, 2π and 1. |
| Auxiliary nonvanishing | `oscWeight_ne_zero` (241) | PASS | Both block constants nonzero, including empty-block cases. |
| Auxiliary chart identification | `oscPeriodChart_eq_diag` (246) | PASS | Correct Fin.append/block coordinate equality, both position and momentum. |
| `bpP:p2:use5` | `use5` (253) | PASS | Exact signature; symplectic form preserved termwise and unnormalized H∘chart has the correct transported vector field. No spurious oscillator-speed division. |

The five theorem signatures match the shared signatures after whitespace normalization, including binder order, premises, constants and conclusions. A Lean probe copied each signature under a fresh name and closed it by the production theorem applied to exactly its explicit binders; reverse `type_of%` assignments also elaborated. A separate `rfl` probe checked the complete `oscPeriodChart` body.

## Definitions and proof refutation checks

The three new definitions are transparent, exposed, total formula objects: `diagChart` constructs its continuous linear map directly; `oscWeight` selects the two specified block constants; `oscPeriodChart` concatenates the correctly scaled blocks. None uses choice, a fallback branch or a junk value. They work for n=0 or m=0 as well.

`WBound` includes `WSummable` at every action point, so the proof never exploits the junk value of an unsummable `tsum`. The coefficient equality is valid as an integral scaling identity on its full stated carrier; the theorem does not pretend to infer analyticity or periodicity from `WBound`. Differentiability is expressly assumed for every field identity, avoiding the total `fderiv` fallback. `constants` is a pre-existing total formula; the invariant proof remains algebraically valid at degenerate scalar inputs and introduces no new interpretation of those inputs as physical scales.

The import closure contains 41 KAM modules and 12 frozen definition modules, no provider and no frozen theorem module. Thus there is no imported DRAFT_SORRY theorem and no SEALED-theorem state to check. Relevant frozen objects retain `Fin n → ℂ` phase coordinates, position/momentum order, and `X_H=(∂I H,-∂θ H)`. No conclusion-shaped hypothesis or bundled hard step is added.

## Notes, source fidelity and limits

1. **P1 consumption is mathematical, not a direct Lean dependency.** Period.lean imports Setting and Constants, and proves the complex diagonal version of P1's period-conversion field law directly. It does not import or apply the existing real `angleScale_hamiltonianVectorField` in `KAM/Planetary/Hamiltonian/Chart.lean:229`. The chart, Hamiltonian factor and time convention agree with `blueprint-P/parts/p1-hamiltonian-tools.tex:127–143`. Thus the requested P1 mathematics is implemented, but literal reuse of that existing Lean theorem is not demonstrated. This is an integration note, not a false proof or signature mismatch.
2. **Keep the assigned signature boundary explicit.** `blueprint-P/parts/p3a-two-scale-iteration.tex:99` also discusses transporting a whole torus, its output-angle displacement, and its frozen frequency. This package proves the design's numerical, coefficient-bound and local field interfaces; it does not export that complete torus transport statement. P1 transport / later assembly must supply it. Similarly P2 use5's full domain and displacement narrative is not all asserted by these scalar/chart signatures. These limits are already present in the independently audited revision-2 design, rather than omissions introduced by this implementation.
3. **Audit execution deviation.** An early lint invocation launched its internal `abi_hashes.py` Lean subprocess while a later audit probe was running; lint was initially invoked without the explicit thread/nice environment. I discovered this by inspecting the lint script and process list. This violated the requested audit serialization/resource procedure. The probe and lint succeeded, and the final lint was rerun serially with `LEAN_NUM_THREADS=1 nice -n 5`; subsequent kernel replay and lint were sequential. This is an auditor workflow deviation, not a defect in the submitted source. Do not treat this audit as having flawless process-serialization provenance.

No suspected new pinned-source or blueprint defect found in the scoped conversion formulas. No source PDF was independently re-audited, and this report does not revalidate inherited CP10 errata. No production deviation from the six assigned design declarations was found.

## Independent checks

Targeted compile gate:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2308 KAM.Planetary.TwoScale.Period
[inp-gate] slot 2 acquired 07:24:54 for KAM.Planetary.TwoScale.Period
Build completed successfully (9087 jobs).
exit 0
```

This is the prescribed targeted build, not a clean library rebuild. No warnings or heartbeat failures were emitted.

Probe command (scratch removed after audit):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2308Audit.lean
exit 0
```

Exact `#print axioms` output for every new public theorem:

```text
'KAM.Planetary.period_dictionary' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.use5_constants' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.period_dictionary_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.diagChart_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.diagChart_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.period_dictionary_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscWeight_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscPeriodChart_eq_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.use5' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay (one invocation, the only changed lemma module; no provider):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.TwoScale.Period
replaying KAM.Planetary.TwoScale.Period
exit 0
```

Final serialized lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (448 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The stale generated root is the brief's permitted exception; it was not regenerated. No other lint failure. Period.lean has the required copyright, module header, public imports, docstring and exposed public section, and 287 lines (<1500). Token/resource-override scan found no forbidden construct. `git diff --check inp...HEAD` exited 0 with no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. Frozen/provider type and literal seal-body probes are not applicable because this is a helper-only package; the design-signature probes above are their relevant replacement.

Only this report was added outside `.lake/abi-scratch/`; the pre-existing untracked P23-08 handoff was left unchanged. No production edits, generated-file changes, commits or other state-changing git operations were performed.
