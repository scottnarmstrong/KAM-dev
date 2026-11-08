# B4-TDOM independent audit 1

Verdict: **PASS WITH NOTES** for B4-TDOM infrastructure. All 23 public declarations satisfy the package brief. No proof or statement defect found. No frozen anchor is assigned or proved by this package, so provider/frozen type equality and a proposed seal-body probe are **not applicable**; this is not a seal authorization for B1-T or any I/N/P anchor.

## Audited snapshot and authority

- Worktree: `/root/code/KAM-inp-b4tdom`.
- HEAD: `1d03cd11a0362a051d330a7fa671b664966a42b6`.
- `inp`: `58e886b1ecac99539862e5aa3ab98b19184c985b`; merge base: `ad866be3d99dedc60770845c912878d17a4c0489`.
- Comparison: `git diff inp...HEAD`, not a working-tree-only comparison.
- Diff: `KAM/EffectiveStability/TorusDomain.lean` (295 new lines), `docs/tracks/B/audits/B4-TDOM-handoff.md` (58 new lines). The handoff's “Nothing else touched” describes the implementation; the actual branch also adds its handoff.
- Lean file SHA-256: `771587d987b97d4d3e28192b15ff2efebb88350bdc488a899b07f847c6ad264e`.
- Read: AGENTS, PLAN, DECISIONS, package-audit brief, B4-TDOM handoff/AUDIT FOCUS, B4-TDOM and B1-common briefs, B SPEC, FREEZE-PROPOSAL and OWNER-DECISIONS (OD-B11/B12), PolyDomain, relevant Canonical and RealFlow APIs and frozen definitions. The B brief/SPEC are the controlling package statements; `blueprint-N/parts/p5-canonical-maps.tex`, `bpN:p5:setting` and `bpN:p5:flow` supply the reused gauge/flow conventions. This is Track B geometry, not an implementation of an I/N/P headline anchor.
- Report destination follows the user's explicit worktree-path instruction, overriding the generic audit brief's MAIN-worktree destination.

## Declaration review

All names below are in `KAM.EffectiveStability`; line numbers refer to `KAM/EffectiveStability/TorusDomain.lean`. PASS means the stated local contract passes, subject to the scope notes below.

| Brief item / node | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| 1 / strip | `cstripOpen` (29) | PASS | Exact strip × polydisc set, angles first, no real-angle restriction. |
| 1 / openness | `isOpen_cstripOpen` (32) | PASS | Finite intersection of strict continuous inequalities. |
| 1 / shift | `cshiftVec` (43) | PASS | Complex inclusion of real angle shift, action component zero. |
| 1 / lattice | `cshiftVec_integer` (45) | PASS | Integer-to-real-to-complex casts match direct complex casts. |
| 1 / preservation | `add_cshiftVec_mem_cstripOpen` (49) | PASS | Real angle shift changes neither imaginary part nor actions. |
| 1 / image | `image_add_cshiftVec_cstripOpen` (57) | PASS | Equality, not merely forward inclusion; inverse translation supplied. Real-shift version generalizes requested integer case. |
| 2 / gauge | `mem_gaugeInterior_cstripOpen` (77) | PASS | Closed gauge ball has coordinate increments ≤ `c*σ'`, `c*ρ'`; triangle inequalities preserve strict margins. |
| 3 / holomorphy | `differentiableOn_hamVFℂ_strip` (95) | PASS | Holomorphic derivative field on open strip, using existing general-open-domain helper. |
| 3 / field | `smallField_of_strip_bounds` (102) | PASS | Correct crossed derivative weights; proves all SmallField fields from source bounds. |
| 4 / field shift | `hamVFℂ_shift` (124) | PASS | Local eventual equality on open strip transfers fderiv; translation chain rule is valid for total fderiv. No differentiability premise is necessary here. |
| 4 / complex flow | `flow_shift_equivariant` (137) | PASS | Exact application of `flow_d` with domain image equality and field invariance. |
| 4 / real shift | `rshiftVec` (149) | PASS | Exact `(s,0)`. |
| 4 / lattice | `rshiftVec_integer` (151) | PASS | Definitionally the repository's `KAM.ODE.angleShift`. |
| 4 / inclusion | `realInclusion₂_rshiftVec` (154) | PASS | Linear real inclusion intertwines the shift vectors. |
| 4 / real domain | `realInterior_add_rshiftVec` (158) | PASS | Translates the full complex gauge ball about a real point. |
| 4 / real flow | `realFlow_shift_equivariant` (172) | PASS | Complex equivariance transported through injective real inclusion; both initial points satisfy half-interior membership. |
| 4 / integer flow | `realFlow_angleShift_equivariant` (193) | PASS | Integer specialization; casts and shift normalization agree. |
| 4 / composition | `comp_realFlow_angleShift` (211) | PASS | Rewrites equivariance then applies `hH`; see N1. |
| 5 / cylinder | `cyl_subset_realInterior_cstrip` (232) | PASS | Open action bound plus `c i + ρ' ≤ ρ` yields strict action margin; `σ' < σ` handles angles. |
| 5 / closed cylinder | `cylClosed_subset_realInterior_cstrip` (244) | PASS | Closed action bound requires the stated strict outer action margin. |
| 6 / Cauchy | `cauchyDisc_subset_gaugeInterior_strip` (257) | PASS | Imaginary angle ≤ `δc`; action norm ≤ `r i + δc`; remaining half-gauge margins exactly as requested. |
| 7 / zero field | `smallField_strip_zero_smoke` (281) | PASS | Genuine constant-zero Hamiltonian, derivative bounds and ε zero. |
| 7 / zero point | `zero_mem_gaugeInterior_strip_smoke` (287) | PASS | Nontrivial gauge-membership witness under explicit strip/action margins. |

Private helper `coord_le_of_scale` (70) also passes: it divides by positive scale widths and uses the Pi sup norm. It is not a new public API or assumption.

## Definitions, premises and consumer scope

The only new definitions are `cstripOpen`, `cshiftVec`, `rshiftVec`. Each is an intended geometric object on its entire carrier, with no fallback, junk branch or hidden proof field. The empty-dimensional case uses ordinary vacuous finite-coordinate conditions; nonpositive strip/radius parameters are not silently repaired. No new abbrev, structure or instance is introduced.

`scaleCLE ρ' σ'` is the existing diagonal complex linear equivalence with norm `max(‖angle‖/σ', ‖action‖/ρ')`. The frozen field is `(∂_J φ, −∂_θ φ)`. Thus `hJ ≤ ε*σ'` bounds the first component after scaling, while `hθ ≤ ε*ρ'` bounds the second; its minus sign disappears only inside the norm. No component or width interchange occurs. These are geometric strip widths, with no Fourier coefficient-radius or `2π` conversion claimed here.

All hypothesis bundles were inspected: `SmallField` contains openness, field holomorphy, `0 ≤ ε ≤ 1/2`, and a field bound. It contains no solution, equivariance, confinement or downstream conclusion. Supplying SmallField to the equivariance lemmas is a standing source assumption; constructing it from derivative bounds is proved in this package. `hreal` is the source reality condition used by the real restriction theorem.

- **N1 (consumer scope/documentation).** `comp_realFlow_angleShift` (211–227) assumes `hH : ∀ y, H (y + angleShift m) = H y` globally. Its docstring says “If H is angle-periodic on the real interior”, which is looser than the actual assumption. The formal statement matches required item 4's angle-periodic H, and the handoff explicitly states “for all y”; it does not prove a version assuming periodicity only on the initial half interior. Flow endpoints need not stay in that same half interior. A future application with only local periodicity must discharge periodicity at those endpoints or prove a separately scoped helper. This is a documentation/consumer note, not a failure of the requested global version.
- **N2 (proved range).** Flow equivariance is for a fixed real shift (integer shift in the specialization), initial half interior and `t ∈ Icc (-1) 1`, endpoints included. Full lattice periodicity follows by discharging the premise for every integer vector. No assertion is made for arbitrary times or all initial points.
- **N3 (stronger/minimal forms).** The real-shift versions are legitimate generalizations, not assumptions of invariance under all real shifts: `hper` is only for the supplied `s`. The gauge criterion omits a nonnegativity premise on `c`; for negative `c` the closed gauge ball is empty and membership is vacuous by the existing definition. Similarly negative Cauchy radius gives an empty disc when `n > 0`. No downstream flow use relies on either vacuity: its radius is positive `1/2`. No extra positivity of `r` or `c` is necessary in the inclusion lemmas.

The transitive KAM source import closure has 38 modules, no provider and no frozen theorem anchor. Its nine frozen imports are ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, SymplecticForm, and Planetary/Defs/OscillatorAction; all are definitions in manifest state SEALED. Their meanings and the reused realFlow/realInterior and flow_d contracts were checked. The chosen-flow fallback outside its existence domain is not used: SmallField and half-interior hypotheses invoke the existing existence/uniqueness theorem.

## Independent checks

All commands below ran from `/root/code/KAM-inp-b4tdom`. Every Lean/Lake/checker invocation, including lint's internal ABI elaboration, was inside this exact prefix:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
```

Lean-consuming checks ran serially. The package-specific memory/nice policy is used; the compile-gate script additionally applies its own `nice -n 5` to the build. No heartbeat, recursion or synthesis override was introduced.

Targeted build (prefix above, followed by):

```sh
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b4tdom KAM.EffectiveStability.TorusDomain
```

Output, exit 0, no warnings:

```text
[inp-gate] slot 1 acquired 02:19:07 for KAM.EffectiveStability.TorusDomain
Build completed successfully (2941 jobs).
```

Kernel replay (prefix above, followed by):

```sh
lake env leanchecker --verbose KAM.EffectiveStability.TorusDomain
```

Output, exit 0:

```text
replaying KAM.EffectiveStability.TorusDomain
```

This is the sole changed lemma module; no provider module exists in this package. The replay command uses module names in one invocation as required.

Axiom probe (prefix above, followed by):

```sh
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/B4TDOMAudit.lean
```

The scratch file imported `KAM.EffectiveStability.TorusDomain` and issued `#print axioms KAM.EffectiveStability.<name>` for every one of the 20 public theorems in the declaration table. Exit 0. Each printed exactly `[propext, Classical.choice, Quot.sound]` (the Cauchy theorem's list wrapped across lines). No `sorryAx` or additional axiom. Scratch file removed after the checks.

Names:

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-b4tdom KAM.EffectiveStability.TorusDomain
```

Output, exit 0:

```text
short-name check OK (no reused public short name)
```

Static inspection: 295 lines; 23 public declarations (3 definitions, 20 theorems); over-100-character lines `[]`; forbidden-token/resource-override matches `[]`. Correct copyright, `module`, public interface import, module docstring and `@[expose] public noncomputable section`. Correct Fin-function carriers. `git diff --check inp...HEAD` exits 0, no output.

Protected paths:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Exit 0, empty output. Full diff confirms no generated root parts, application roots or lakefile edits either.

Lint (prefix above, followed by):

```sh
sh scripts/lint_sources.sh
```

LINT_RECEIPT_PENDING

## Source/blueprint defects, deviations and uncertainty

No suspected mathematical source or blueprint defect found in the audited package. N1 quotes the local docstring/formal-premise mismatch and its precise consumer limitation; it does not challenge the pinned source. No external PDF theorem is newly formalized by B4-TDOM: the elementary geometry is specified by the package brief and the general flow theorem is reused. This audit does not certify unrelated I/N/P source nodes or the future B4 checker/B1-T assembly.

No signature repair, source modification or proof change was made. The only repository edit is this report; scratch probes are removed. No state-changing git command, clean, cache fetch, package mutation, frozen edit or generated-root regeneration was performed.
