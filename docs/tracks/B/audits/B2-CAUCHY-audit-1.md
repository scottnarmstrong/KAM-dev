# Independent package audit: B2-CAUCHY, round 1

Verdict: **PASS WITH NOTES** for B2-CAUCHY as ordinary analytic infrastructure. No blocking mathematical or proof-hygiene defect found. No frozen anchor is proved or sealed by this package; per-anchor seal readiness and provider/frozen-type and seal-body probes are **not applicable**. All six required brief items are supplied.

Audited worktree: `/root/code/KAM-inp-b2cauchy`. HEAD: `ab602fd41a60bb50fe16a77c6e17900d7a978f3d`. Comparison `inp` and merge base: `33f7f52a5edf58c18691986ea716b571c1487f1e`. Review uses `git diff inp...HEAD`, including all five changed paths. The only changed Lean module is `KAM/EffectiveStability/Cauchy.lean`, 214 lines, SHA256 `853a193ed81de7215ff75a017a7d7766b3c1696d874c32490f315cb26b5cb917`.

Controlling texts read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package-audit brief, B2-CAUCHY handoff including AUDIT FOCUS, external brief-B1-common.md and brief-B2-CAUCHY.md, Track B SPEC.md and FREEZE-PROPOSAL.md, program-b-plan §3.2 (lines 341–420), and Oscillator.lean through its hRη consumer. Track B is unfrozen under OD-B7; the applicable statement contract is the six-item B2 brief and plan §3.2, rather than unrelated I/N/P frozen theorems or blueprint nodes. The user's exact worktree report destination overrides the generic brief's main-worktree destination.

## Declaration review

All names below have prefix `KAM.EffectiveStability.`. One row per new public declaration (14 theorems and one definition).

| Brief node | Declaration (Cauchy.lean line) | Verdict | Reason |
|---|---|---|---|
| 1 | `norm_fderiv_le_of_closedDisc` (34) | PASS | General normed complex domain; exactly the directional closed-disc estimate. No completeness or unit-direction premise. |
| 1 | `norm_fderiv_coord_le` (60) | PASS | Requested set-form disc; same bound and quantifiers; arbitrary directions are expressly allowed by the brief. |
| 2 | `cpolydisc` (75) | PASS | Exact coordinatewise closed Cartesian polydisc definition. |
| 2 helper | `fst_mem_cpolydisc` (78) | PASS | First-block coordinate disc inclusion, with nonnegative radius. |
| 2 helper | `snd_mem_cpolydisc` (86) | PASS | Second-block coordinate disc inclusion, with nonnegative radius. |
| 2 | `norm_fderiv_fst_le_of_cpolydisc` (95) | PASS | First-block derivative bounded by M/δ; no change of radius or norm. |
| 2 | `norm_fderiv_snd_le_of_cpolydisc` (104) | PASS | Second-block derivative bounded by M/δ; no change of radius or norm. |
| 3 | `fderiv_realPart_eq` (113) | PASS | Real derivative equals the real part of the complex derivative; no reality premise. |
| 3 | `abs_fderiv_realPart_fst_le` (129) | PASS WITH NOTES | Correct bound; hx is derivable from hsub and hδ (N1). |
| 3 | `abs_fderiv_realPart_snd_le` (141) | PASS WITH NOTES | Correct bound; same redundant hx (N1). |
| 4 | `abs_actionBracket_le_of_cauchy` (154) | PASS WITH NOTES | Exact B1-E bracket/sign/order and prefactor; same redundant hx (N1). |
| 6 | `smoke_coord` (172) | PASS | Requested coordinate-function inequality, M = ‖z.1 i‖ + δ. |
| 5 helper | `geometric_tail_identity` (186) | PASS | Stronger finite algebraic identity: only x < 1, without x ≥ 0. |
| 5 | `hasSum_nat_mul_geometric_tail` (199) | PASS | Exact shifted infinite tail and guards 0 ≤ x < 1; subtraction is in ℝ. |
| 5 | `sum_range_nat_mul_geometric_tail_le` (207) | PASS | Every finite partial sum, including m = 0; nonnegativity proved, not assumed as tail bound. |

## Mathematical and consumer checks

The directional proof restricts to `g ζ = f (z + ζ • e)`. Openness and differentiability on U provide differentiability at every point of the closed disc. The proof constructs continuity on the closed ball and differentiability on the open ball, uses `closure_ball` with δ > 0, and applies Mathlib's sphere estimate at radius δ. The chain rule identifies `deriv g 0` with `fderiv ℂ f z e`. There is no hidden unit-direction assumption, extra factor ‖e‖, radius shrinkage, or geometric/coefficient-width conversion. The bound includes ζ = 0, so M ≥ 0 follows from the hypotheses; a separate M ≥ 0 premise is unnecessary. Degenerate e = 0 is harmless.

The polydisc hypotheses imply both coordinate disc hypotheses at the same radius, using `Pi.single`. The carrier uses the usual Pi and product max norms throughout. The real-slice proof composes the real-linear inclusion with `restrictScalars ℝ` and `Complex.reCLM`; it proves an equality of real parts, so it correctly needs no assertion that f takes real values. It does not substitute the stronger complex equality from `hamiltonian_real_fderiv`, which would require reality.

The bracket is precisely `q_j ∂_{p_j}F - p_j ∂_{q_j}F` for `F = Re ∘ f ∘ realInclusion₂`, with bound `(|q_j| + |p_j|) * M/δ`. This matches Oscillator.lean:56–60 and SPEC's q-first, p-second convention. To instantiate hRη uniformly, the caller must supply the holomorphic remainder/domain/disc/bound data at every point of the stopped oscillator region, identify R with F (or identify their derivatives), and dominate this pointwise prefactor by η j. This package does not assert those future normalization inputs. For the plan's equal margins δq_j = δp_j = δ and |q_j|, |p_j| ≤ w_j, its bound gives 2 w_j M/δ, exactly the plan's Cartesian expression. Unequal coordinate margins remain outside this equal-radius package contract.

For the tail, all appearances of `d - 1` in the numerator are real subtraction, as required at d = 0. The finite identity starts with the full sum x/(1-x)^2 minus degrees below d; the shifted HasSum starts at k+d. The partial sum proof uses nonnegative summands under x ≥ 0. At d = 0 the formula is x/(1-x)^2; at x = 0 it is zero for every d, including d = 0 (0^0 = 1 multiplies a zero numerator). Both were checked by Lean probes; the x = 0 partial-sum bound was also checked. The general m = 0 case follows directly from the proved partial-sum theorem. No first-omitted-term approximation is substituted.

## Definition classification and hypotheses

`cpolydisc` is the only new definition; there are no new abbrevs, structures, instances, or chosen/default objects. Its body is exactly `{w | ∀ i, ‖w.1 i - z.1 i‖ ≤ δ ∧ ‖w.2 i - z.2 i‖ ≤ δ}` on its entire carrier. Negative radius gives the empty set when n > 0; at n = 0 the coordinate predicate is vacuous. These are the literal intended coordinatewise semantics, and all derivative estimates require δ > 0. The definition is exposed by `@[expose] public noncomputable section`.

No theorem assumes a derivative bound, HasSum conclusion, flow conclusion, or other hard step as a premise. hM is the stipulated source function bound. The arbitrary-E directional theorem and the finite-tail helper's allowance of negative x are valid generalizations. No signature weakening or wider constant dependence was found.

N1 (minor premise redundancy, not a source mismatch): in Cauchy.lean:129,141,154, `hx : realInclusion₂ n x ∈ U` follows from hsub because the center lies in the nonnegative-radius polydisc. It is explicitly present in the handoff and does not narrow the usable data class. The scratch probe established center membership from δ ≥ 0. It can be omitted in a later API cleanup, but is not a conclusion-shaped hypothesis or a blocker. The standalone real-slice identity still needs its own hx.

N2 (handoff accounting): handoff line 26 says “all 11 declarations”; the actual module has 14 public theorems plus one definition. This audit checks axioms of all 14 theorems, including both coordinate-disc inclusion helpers and the finite-tail helper.

## Imports and protected paths

Static recursive local-import review found 13 local modules, no provider import and no frozen THEOREM import (hence no imported DRAFT_SORRY theorem). The six frozen definition imports in the closure are all SEALED: ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC, IsPrimaryOnStrip, IsRealOnReals, OmegaZero. Their files and realInclusion₂'s body were inspected. No new result relies on a frozen theorem's unproved body.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no output, exit 0. The additional protected-path comparison for `KAM/Root lakefile.lean` was also empty. `git diff --check inp...HEAD` produced no output, exit 0. The other four changed paths contain Track B coordination/progress/package metadata and the handoff; they introduce no Lean premises or frozen changes. Their presence in the comparison is recorded rather than silently excluded.

## Validation receipts

All Lean/Lake invocations, including the ABI subprocess inside lint, ran sequentially in a 4 GiB no-swap systemd scope with LEAN_NUM_THREADS=1. No heartbeat, recursion, or synthesis-budget override was used. The gate supplies nice 5 inside the required nice 10 scope; explicit probes and replay also received nice 5 inside that scope.

Targeted build (exit 0):

```text
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b2cauchy KAM.EffectiveStability.Cauchy
[inp-gate] slot 1 acquired 00:46:08 for KAM.EffectiveStability.Cauchy
Build completed successfully (2853 jobs).
```

Kernel replay, one invocation for the sole new module (exit 0):

```text
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.EffectiveStability.Cauchy
replaying KAM.EffectiveStability.Cauchy
```

Scratch axiom/edge-case probe (exit 0):

```text
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B2CauchyAudit.lean
'KAM.EffectiveStability.norm_fderiv_le_of_closedDisc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_fderiv_coord_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.fst_mem_cpolydisc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.snd_mem_cpolydisc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_fderiv_fst_le_of_cpolydisc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_fderiv_snd_le_of_cpolydisc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.fderiv_realPart_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.abs_fderiv_realPart_fst_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.abs_fderiv_realPart_snd_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.abs_actionBracket_le_of_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.smoke_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.geometric_tail_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.hasSum_nat_mul_geometric_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.sum_range_nat_mul_geometric_tail_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The same probe instantiated HasSum at d = 0; HasSum and partial sums at x = 0 for arbitrary d; and center membership in cpolydisc for δ ≥ 0. It emitted only two `unnecessarySimpa` warnings at scratch lines 24 and 28 (“simp already closes the goal”); there were no package build warnings or probe errors. The probe is removed after audit.

Direct size/width/declaration scan output:

```text
lines: 214
over 100 characters: []
public theorem count: 14
```

The module has the copyright header, `module`, all three interface imports as `public import`, module docstring, and exposed public section. No forbidden proof escape, budget override, EuclideanSpace carrier, or global Phase abbreviation occurs in the new code. Names match the requested API and namespace.

LINT_RECEIPT_PENDING

## Source defects, deviations, and limits

No suspected mathematical defect in the applicable plan/brief or imported frozen definitions was found. N2 is an evidence-count discrepancy in the handoff, not a source erratum. No repository correction, freeze, seal, commit, numerical certificate, or normalization proof was performed. The only repository deliverable of this audit is this report; temporary probes are confined to `.lake/abi-scratch/` and deleted. The explicit source scope is plan §3.2 and the six-item brief, not an independent audit of the external CL20/GLS17 articles or unrelated I/N/P anchors.
