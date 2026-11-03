# B2-REALFLOW independent package audit 1

Date: 2026-11-03 (UTC). Worktree: `/root/code/KAM-inp-b2flow`.
Audited HEAD: `344c3acfe195e25545dc5c4be9b3c5e5bdfe4de0`.
Comparison ref `inp`: `33f7f52a5edf58c18691986ea716b571c1487f1e`.
Scope: `git diff inp...HEAD`, the four new RealFlow modules and three Track B documentation changes.
The explicit user destination overrides the generic audit brief's MAIN-worktree destination.

## Verdict

**FAIL (literal AGENTS rule 3 hygiene only, F1).** All 19 public theorems pass the mathematical,
axiom and kernel checks. No mathematical repair is requested. After F1, the scoped package merits
**PASS WITH NOTES**, with the smooth-versus-analytic signature difference retained as N1.

There is **no frozen anchor and no provider** in this package. Provider/frozen type-equality and
seal-body probes are therefore not applicable; this is not a seal authorization. The controlling
specification is the B2-REALFLOW brief, common B brief, handoff AUDIT FOCUS, program-b-plan §3.2,
Track B SPEC/FREEZE-PROPOSAL and OD-B7–B10. Existing blueprint-N Part 5 setting, flow, symplectic
and Taylor nodes supply the reused complex results; no Track I/N/P anchor is newly proved here.

## Findings and applicability

**F1 — Low severity, required hygiene correction.** `KAM/EffectiveStability/RealFlow.lean:6–18`
has `module`, public imports and its module docstring, but no `public section`. AGENTS rule 3
explicitly requires every `.lean` file to contain it. This import-only facade has no declarations,
so the omission has no mathematical or export effect, and the repository module checker does not
reject it. Nevertheless it is a literal hard-rule discrepancy: add `public section` after the
module docstring. Report-only scope prevents the auditor from applying that edit. The overall
FAIL is confined to this small compliance fix.

**N1 — Smoothness is not the brief's literal analytic signature.** B2 brief required items 2 and
6 say `ContDiffOn ℝ ⊤`, while Basic:148–152 and Lie:48–54 prove `ContDiffOn ℝ ∞`.
Pinned Mathlib `Analysis/Calculus/ContDiff/Defs.lean:90–91,118–123` identifies outer `⊤` as `ω`
(analytic), and the embedded infinity as smooth order. Thus this is a strictly weaker literal
regularity conclusion, not equality of notations. The handoff explicitly discloses it and the
AUDIT FOCUS specifically asks for `∞ ⇒ 2`, so it is accepted for this B1-facing audit only.
No analytic theorem is certified. Align the producer brief with this scope, or supply the
analytic strengthening if the original literal signature is retained. The original requested
analytic statement is not shown false or unusable by this package.

**N2 — Consumer domains remain application obligations.** With `Ψ = realFlow φ Ω 1` and
`Ψinv = realFlow φ Ω (-1)`, the probe below proves B1's C², exact `fderiv` symplectic form,
left-inverse and image requirements on any `D ⊆ realInterior W Ω 1`. Smoothness and symplecticity
already hold on the larger half-interior; `realInterior_mono` supplies that inclusion. For
Oscillator:41–48 and Torus:40–44, instantiate `D` with their actual chart domains and prove
this geometric inclusion. The image result supplies `hΨV` for `V = realInterior W Ω (1/2)`
(or a larger chosen physical domain). The package does not discharge B1's Hamiltonian,
normal-form identity, periodicity or drift bounds, and proves no concrete confinement instance.

**N3 — Harmless premise/documentation excess.** Explicit `hΩ` is redundant wherever
`h : SmallField ...` supplies `h.isOpen`. `realFlow_zero` also carries holomorphy/reality premises
unneeded for time zero. These are standing source premises, not assumed conclusions, and do not
strengthen the required assumptions beyond the brief. Basic:87–88 mentions reality in the
`contDiffOn_reMap` docstring although its stronger theorem does not require it.
Symplectic:71–72 describes inverse identities as well as membership, whereas the immediately
following theorem exports membership alone; the next two theorems export the inverse identities.
Handoff line counts (180/128) are stale: current Basic/Lie have 181/130 lines. These are notes,
not proof failures.

## Declaration-by-declaration review

Names below are in `KAM.EffectiveStability`. PASS rows concern the declared mathematical result;
F1 is the separate facade hygiene failure.

| Node / brief item | Lean declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| Real restriction definition | `reMap` (Basic:41) | PASS | Componentwise Re after real inclusion, on the whole carrier. |
| Conditional bridge | `realInclusion₂_reMap` (Basic:47) | PASS | Generic map-real premise; equality reversed from private `psi_real_eq`, faithfully generalized. |
| Conditional derivative bridge | `reMap_hasFDerivAt` (Basic:62) | PASS | Local complex differentiability and eventual reality suffice; derivative uniqueness proves inclusion identity for every vector. |
| Smooth restriction | `contDiffOn_reMap` (Basic:89) | PASS | Stronger than its docstring: no reality assumption needed. |
| Flow definition | `realFlow` (Basic:108) | PASS | Exactly Re ∘ complex Hamiltonian flow ∘ inclusion. |
| Domain definition | `realInterior` (Basic:113) | PASS | Exact preimage of closed-gauge-ball interior, no altered radius. |
| Domain openness | `isOpen_realInterior` (Basic:117) | PASS | Continuous preimage of open gauge interior, for every real c. |
| Domain nesting | `realInterior_mono` (Basic:120) | PASS | Correct reversed monotonicity in c. |
| 1 / field reality | `hamiltonianVectorFieldℂ_real` (Basic:125) | PASS | Derived from holomorphic generator reality through the existing real-Hamiltonian bridge. |
| 1 / flow reality | `realInclusion₂_realFlow` (Basic:134) | PASS | `flow_e` derives map reality; no assumption that flow is real. |
| 2 | `contDiffOn_realFlow` (Basic:148) | PASS WITH NOTES | Smoothness from `flow_b`; no generator reality needed; N1. |
| Time zero | `realFlow_zero` (Basic:155) | PASS WITH NOTES | Correct identity; unnecessary standing premises, N3. |
| 5 | `norm_realFlow_sub_le` (Basic:167) | PASS | Exactly `flow_a` displacement, same W, absolute time and ε. |
| 3 / derivative | `realFlow_hasFDerivAt` (Symplectic:36) | PASS | Eventual reality obtained from openness and item 1; no derivative conclusion assumed. |
| 3 / form preservation | `realFlow_symplectic` (Symplectic:52) | PASS | Derivative uniqueness identifies real fderiv; complex form equals cast of frozen real form, with correct sign. |
| 4 / images | `realFlow_mem_realInterior` (Symplectic:73) | PASS | Both ±1 images from radius 1 land at radius 1/2, exactly `flow_c`. |
| 4 / left inverse | `realFlow_neg_realFlow_one` (Symplectic:90) | PASS | Inner image membership licenses outer reality bridge; no domain mismatch. |
| 4 / right inverse | `realFlow_one_realFlow_neg` (Symplectic:104) | PASS | Symmetric use of `flow_c`, on radius 1. |
| 6 / observable | `realObs_realFlow` (Lie:36) | PASS | Stronger: arbitrary g, no regularity or reality premise on g. |
| 6 / regularity | `contDiffOn_realObs` (Lie:48) | PASS WITH NOTES | Smooth restriction via scalar restriction/Re; no reality of g needed; N1. |
| 7 | `real_taylor_lie_bound` (Lie:57) | PASS | Exactly original Taylor premises at ιx, plus source bracket bound; same N!, range N and sign. |
| 8 | `smoke_zero_generator` (Lie:91) | PASS | Constructs SmallField at ε=0, proves reality/holomorphy and identity, for every n including zero. |
| Facade | `RealFlow.lean` | FAIL (F1) | Missing literal `public section`; no declarations or mathematical defect. |

## Definitions, bridges and hypothesis audit

There are precisely three new definitions, and no new abbreviations or structures. `reMap` is a
faithful componentwise projection for all inputs, not an extension by a junk value. Its body is
identical to the earlier `KAM.Stability.reMap` in Stability/Setting:61–64; the handoff's claim
that the older definition is in the root namespace is imprecise (its namespace is
`KAM.Stability`). The new namespace prevents a declaration collision; qualified use resolves
any short-name ambiguity if both namespaces are opened. Avoiding that heavy import is reasonable.

`realFlow` is deliberately a total projection of the existing total `Canonical.flow`. Outside
its guaranteed time/domain it is not claimed to be a real solution or canonical. Within the
stated half-interior and |t|≤1, `flow_a` supplies existence, so no theorem exploits flow's
no-solution fallback. `realInterior` retains gaugeInterior's meaning for every c, including
negative c (vacuous ball condition), and the public monotonicity/openness results remain valid.

The adapted derivative helper follows Conjugation:56–87: restrict scalars, compose with inclusion
and Re, use eventual reality to identify two derivatives. Unlike the source-specific helper,
it assumes local differentiability/eventual reality directly; these are appropriate source
premises for the distinctly named generic helper. Actual flow reality is derived before use.
The inline form computation agrees with Planetary/TwoScale/ToriLagr:47–51 and the frozen
`Σ (v.2*w.1 - v.1*w.2)` convention. There is no norm or carrier substitution.

`real_taylor_lie_bound` reuses Canonical/Lie:177 onward at z=ιx: the full htraj on [-1,1]
is unchanged; hB is only on [0,1]. It takes real parts of the exact Taylor equality, casts the
real factorial inverses faithfully and applies |Re I|≤‖I‖. No extra factor, lost term, bracket
sign or factorial shift occurs. Reality of the generator/observable/iterates is unnecessary
for that inequality. htraj and hB are explicit original Taylor applicability/bound premises,
not an assumed Taylor remainder conclusion. No claim of a computed numerical bound B is made.

The 39-module transitive project import closure contains no provider, frozen theorem anchor,
or Nekhoroshev module. Its seven frozen definition modules (ComplexStrip, HamiltonianVectorField,
HamiltonianVectorFieldC, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, SymplecticForm) are all SEALED
in the current manifest. No DRAFT_SORRY dependency is present.

## Verification (serial; LEAN_NUM_THREADS=1)

All Lean/Lake invocations, including lint's ABI subprocess, inherited this wrapper:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

Each build separately invoked the prescribed gate (never two of this audit's Lean/Lake calls
at once):

```sh
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-b2flow KAM.EffectiveStability.RealFlow.Basic
# Build completed successfully (2935 jobs).                 exit 0
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-b2flow KAM.EffectiveStability.RealFlow.Symplectic
# Build completed successfully (2945 jobs).                 exit 0
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-b2flow KAM.EffectiveStability.RealFlow.Lie
# Build completed successfully (2947 jobs).                 exit 0
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-b2flow KAM.EffectiveStability.RealFlow
# Build completed successfully (2948 jobs).                 exit 0
```

These are Lake's dependency/job totals, not evidence of thousands of concurrent processes.
No package warning, OOM or heartbeat failure was emitted.

Axiom/consumer probe command (under the same wrapper):

```sh
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
  .lake/abi-scratch/B2RealFlowAudit.lean
```

Final exit 0, no warnings. All 19 new public theorems were checked, not just handoff main lemmas:

```text
'KAM.EffectiveStability.realInclusion₂_reMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.reMap_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.contDiffOn_reMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.isOpen_realInterior' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.realInterior_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.hamiltonianVectorFieldℂ_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.realInclusion₂_realFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.contDiffOn_realFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.realFlow_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_realFlow_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.realObs_realFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.contDiffOn_realObs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.real_taylor_lie_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.smoke_zero_generator' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.realFlow_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.realFlow_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.realFlow_mem_realInterior' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.realFlow_neg_realFlow_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.realFlow_one_realFlow_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The first auditor-written consumer probe had unbound local-notation dimension/time metavariables
and exited 1; this was a scratch-only probe defect. Replacing the notation by full carrier types
and specifying `(t := 1)` produced the clean final result above. No production source changed.
The successful consumer portion is preserved here for reproducibility:

```lean
section Consumer
variable {n : ℕ}
variable {W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))} {Ω : Set ((Fin n → ℂ) × (Fin n → ℂ))} {φ : ((Fin n → ℂ) × (Fin n → ℂ)) → ℂ} {ε : ℝ}
variable (hφ : DifferentiableOn ℂ φ Ω)
variable (h : KAM.Canonical.SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
variable (hr : ∀ x : ((Fin n → ℝ) × (Fin n → ℝ)), KAM.realInclusion₂ n x ∈ Ω → (φ (KAM.realInclusion₂ n x)).im = 0)
variable {D : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hD : D ⊆ realInterior W Ω 1)
example : ContDiffOn ℝ 2 (realFlow φ Ω 1) D := by
  exact ((contDiffOn_realFlow h (by norm_num : (1 : ℝ) ∈ Icc (-1) 1)).of_le
    (by simp)).mono (fun x hx => realInterior_mono (by norm_num) (hD hx))
example : ∀ w ∈ D, ∀ u v : ((Fin n → ℝ) × (Fin n → ℝ)),
    KAM.symplecticForm (fderiv ℝ (realFlow φ Ω 1) w u)
      (fderiv ℝ (realFlow φ Ω 1) w v) = KAM.symplecticForm u v := by
  intro w hw u v
  exact realFlow_symplectic hφ h hr (t := 1) (by norm_num)
    (realInterior_mono (by norm_num) (hD hw)) u v
example : ∀ w ∈ D, realFlow φ Ω (-1) (realFlow φ Ω 1 w) = w := by
  intro w hw
  exact realFlow_neg_realFlow_one h.isOpen hφ h hr (hD hw)
example : MapsTo (realFlow φ Ω 1) D (realInterior W Ω (1/2)) := by
  intro w hw
  exact realFlow_mem_realInterior h.isOpen hφ h hr (hD hw) (Or.inl rfl)
end Consumer
```

Kernel replay, one invocation under the same wrapper:

```sh
lake env leanchecker --verbose KAM.EffectiveStability.RealFlow \
  KAM.EffectiveStability.RealFlow.Basic \
  KAM.EffectiveStability.RealFlow.Symplectic \
  KAM.EffectiveStability.RealFlow.Lie
```

Exit **0**, output:

```text
replaying KAM.EffectiveStability.RealFlow
replaying KAM.EffectiveStability.RealFlow.Symplectic
replaying KAM.EffectiveStability.RealFlow.Lie
replaying KAM.EffectiveStability.RealFlow.Basic
```

## Lint and protected files

LINT_RESULT_PLACEHOLDER

Four package files have respectively 18, 181, 119 and 130 physical lines; all lines are ≤100
characters. The common-brief width check over all `KAM/EffectiveStability/**/*.lean` returned
`[]`, exit 0. All implementation modules contain copyright, `module`, public imports, module
docstrings, and exposed public noncomputable sections. Facade exception F1 is retained explicitly.
Source inspection and lint found no proof escape or resource override in the new files.

```sh
git diff --check inp...HEAD
# no output; exit 0
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
# no output; exit 0
```

No generated root, frozen file, manifest or production source was changed by this audit.
The only repository edit is this report. Audit probe files were removed after checks; no
state-changing git operation was run.

Audited Lean source SHA256 values:

```text
6085499894cb78932fef9191c9f40568db3960693f405d26014fa868a5f06042  KAM/EffectiveStability/RealFlow.lean
7059cf4a52aba036cb2c01a89737e16dda33b2846ea56f0a7f8863065d5c6875  KAM/EffectiveStability/RealFlow/Basic.lean
a5d8cf82a3e283910103c2c6679f637241cece78b05245b4863c48af1ea39f80  KAM/EffectiveStability/RealFlow/Symplectic.lean
eba867b7d70f5fb6c5b623501a533133a40161212155a7934c9efeab20168c76  KAM/EffectiveStability/RealFlow/Lie.lean
```

## Source defects, deviations and limits

No new suspected defect in a pinned mathematical source was found in this scoped audit. The
local blueprint-N flow/symplectic/Taylor formulations agree with the reused statements; no
external-source attribution is upgraded to a new source audit. The brief's `⊤`/smooth wording
mismatch is the precise specification discrepancy N1, and F1 is an implementation hygiene
omission. Short modules below the brief's 150–600 target are justified by direct reuse and stay
well below the hard 1500-line cap. No heartbeat/design signal occurred.

Nothing has been frozen, sealed, merged, or committed. Remaining actions: correct the facade's
literal rule-3 omission; reconcile the original analytic regularity wording with the accepted
B1 smooth scope; prove geometric inclusions and analytic bounds when building an actual B1
application. No extra mathematical premise or silent frozen-statement change is proposed.
