# P11A-P2c independent audit 1

Audit date: 2026-10-28. Worktree `/root/code/KAM-inp-p11ap2c`; HEAD
`02ca2bb08607c4667288cf065902823b66a620cd`; comparison ref `inp` at
`4a5b757e944936d0ae6e9269a1170dc7098e4240`; merge base
`02ee95b6d03dcaf74adaf6b29d46beab4b7cfffb`.

The user's exact report destination overrides the generic brief's main-worktree destination.
Only this report is a repository edit. Temporary probes are confined to `.lake/abi-scratch/`.
Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, handoff and AUDIT FOCUS,
P11A design and design audits 1–3, the signature's P11SecularSpec clauses, track P statement,
and blueprint Part 11 lines 63–84. Inspected the complete three-dot diff: seven new modules,
1,599 inserted lines; the four HoloStrip modules are the audit scope. The other three modules
(Holomorphic, HolomorphicRotation, Polar) were read as context and are not independently certified here.

## Scope and verdict

**Verdict: PASS WITH NOTES for the authorized parametric hc-strip / hc-F slice.**
No frozen anchor or provider export is supplied by this package; frozen-type/seal-body probes
are therefore inapplicable. This is not a seal-readiness claim for holo_chart or P-FIXED.
The overnight scope excludes hc-lift, hc-id/hc-lat, hc-mean and full holo_chart assembly.
The design node table assigns the original monolithic proof to Preparation/Holomorphic;
the handoff explicitly reallocates only hc-strip and the four F clauses to these modules.
No literal graph-node-named export or SIGNED declaration occurs in the four audited modules.
Their 43 public theorems and 12 definitions/structures are inventoried below.

The conditional F theorem proves the four requested clauses on precisely
`p11WorkingDom n J0 (2*σ) (2*rC) rz`. The pointwise bound is definitionally the
signature's `p11Bound` clause; no weighted Fourier summability is silently claimed.
`MF = max 1 (coth(π*σ)^n * p11hsMInf D a)` supplies its numerical premise.
The explicit MInf is an upper bound, not an assertion of attained supremum.

## Notes and consumer applicability

**N1 — The handoff's original-axis attachment is not established by shrinking rC.**
`HoloStripInput.lean:131–132` assumes `center`: every action in the rotation ball is
within r' of `action D a`. At the center of this nonempty ball it necessarily implies
`‖(J0/(2π))_i - action D a i‖ < r'`. This necessary implication is checked in the scratch
probe. `p11hs_strip_data` (HoloStrip.lean:36–42) chooses r' independently of the physical
forward-tube radius. With the advertised specialization `a := D.a`, neither
`p11_rotation_complex`, `p11_rotation_bounds`, nor the existing patch's delta/8 bound
implies this inequality. Making rC smaller leaves J0 unchanged. The handoff's statement
that P2f/P2b must shrink must not be read as a proof that shrinking only rC works.

This does **not** make the generic parametric interface unusable. The formula `p11hsF D ρ`
and separation `p11hsSep D` do not depend on a. From P2b's P11HoloData.R_frame at its center
one has `L0 := J0/(2π) ∈ SecularForm.actionDomain D`. Unfolding that image gives an ordered
positive axis vector a0 with `action D a0 = L0`. Apply `p11hs_strip_data D` at a0, then shrink
rC to at most `π*r'/2` and the old rotation radius. The center condition now follows from
ball membership and the Pi norm bound. A scratch existence proof checks this construction,
including the strip data and center condition together. This uses the same F and ρ and
preserves the selected J0; it does change the auxiliary axes, the gap bound and MInf.
P2f must explicitly reconcile that choice with its physical-domain/identity/mean obligations,
which are outside this audit. No attachment at the original axes is certified here.
The P2b interface was read at
`/root/code/KAM-inp-p11ap2b/KAM/Planetary/Preparation/HoloData.lean` as current neighboring
source evidence; it is not imported into this worktree or independently kernel-checked here.

All other P11HsHyp fields have source-input provenance: entrywise holomorphy and reality
come from p11_rotation_complex, row sums from p11_rotation_bounds, positive radii and
sigma ≤ sigma'/4 are shrink choices, B≥0 follows from B≥1, and the two rz inequalities
can be enforced by choosing rz small after the strip and B,B' are fixed. The separation
field is exactly supplied by p11hs_strip_data; it is not an unpaid assumption within
hc-strip. No target F conclusion is a bundled hypothesis. Orthogonality is unnecessary
for this analytic conditional result, making it stronger in that respect.

**N2 — Recorded radius/constant deviations.** The extra `2π*σ' ≤ 1/8` is obtained by shrinking
the strip and ensures strict membership in the original |Im λ|<1/4 Poincare neighborhood.
The real-angle separation radius r0 comes from SecularForm.exists_radius, and p11hs_strip_data
uses r0/2, retaining the intended compact-interior margin. This radius is not identified with
p11PhysicalDelta. The bound is the explicit `G Σ_{i<j} m_i m_j 2/(a_j-a_i)` rather than an
abstract sup; all dependences are in fixed data/axes, before rz and σ are chosen.

No new pinned-paper erratum or false frozen statement was found. N1 is an implementation
handoff/consumer reconciliation issue, not evidence that the source theorem is false.

## Proof review

The separation proof uses continuity on the original open complex Poincare domain;
`p11hs_eventually` applies compact uniformity on `[0,2π]^n × closedBall(center,r'')` with
r' < r'' < r0. The strict real-angle half-gap estimate leaves a quarter-gap margin.
Finite i,j quantification supplies a common imaginary neighborhood, then the proof picks
sigma' with `2π*sigma' < ε` and reduces arbitrary real angles by integer 2π shifts.
The nonpositive-r' branch is vacuous since Data has positive dimension. No boundary
continuity or compactness hypothesis is assumed without containment.

For each i<j the positive quarter-gap places separation in the complex slit plane.
The negative-half complex power is therefore holomorphic, its norm is bounded by
`2/(a_j-a_i)`, and it is real on real inputs. The input map has the literal transpose
rotation-derivative quadratic shift with positive sign, `(2π θ,J/(2π))`, and rotated x,y
in frozen position/momentum order. Its angular budget is at most
`4π*σ + π*σ'/2 ≤ 3π*σ'/2 < 2π*σ'`. Realness of the rotation derivative is proved by
restricting to real lines inside the open real ball, not assumed as extra data.
All four final clauses are obtained for the actual constructed F.

## Declaration ledger

Names below are in `KAM.Planetary`. PASS means the stated helper is sound and faithful
at its indicated responsibility; applicability is subject to N1 where P11HsHyp is used.

| Node / responsibility | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| hc-strip | `p11hs_strip_data` (HoloStrip.lean:36) | PASS | Chooses r0/2 and a positive uniform strip; N2. |
| hc-F / analytic helper | `p11hsF_differentiableOn` (HoloStrip.lean:44) | PASS | Holomorphic composition on exact working domain. |
| hc-F / analytic helper | `p11hsF_norm_le` (HoloStrip.lean:51) | PASS | Explicit fixed-data upper bound. |
| hc-F / analytic helper | `p11hsF_bound_weighted` (HoloStrip.lean:56) | PASS | Exact MF/coth(πσ)^n bound by positive division. |
| hc-F / analytic helper | `single_castAdd_natAdd` (HoloStrip.lean:72) | PASS | Disjoint fast and slow index blocks. |
| hc-F / analytic helper | `p11hsF_shift` (HoloStrip.lean:76) | PASS | Exact unit fast-angle periodicity clause. |
| hc-F / analytic helper | `p11hsF_real` (HoloStrip.lean:108) | PASS | Exact real-on-real-points clause. |
| hc-F / analytic helper | `p11hs_F` (HoloStrip.lean:175) | PASS | Exact four F clauses, definitionally including p11Bound; N1. |
| hc-F / analytic helper | `p11hsMInf_nonneg` (HoloStripBound.lean:52) | PASS | Positive masses, G and ordered gaps. |
| hc-F / analytic helper | `norm_cpow_neg_half_le` (HoloStripBound.lean:60) | PASS | Principal power norm bound from positive real part. |
| hc-F / analytic helper | `p11hsFHat_norm_le` (HoloStripBound.lean:76) | PASS | Finite Newtonian sum with explicit fixed-data bound. |
| hc-F / analytic helper | `differentiable_p11hsBlock` (HoloStripBound.lean:94) | PASS | Linear coordinate extraction. |
| hc-F / analytic helper | `differentiableOn_p11hsPlanet` (HoloStripBound.lean:100) | PASS | Original complex Poincare chart on its domain. |
| hc-F / analytic helper | `differentiableOn_p11hsSep` (HoloStripBound.lean:109) | PASS | Finite polynomial in the actual planet positions. |
| hc-F / analytic helper | `p11hsFHat_differentiableOn` (HoloStripBound.lean:122) | PASS | Positive real part avoids branch cut. |
| hc-F / analytic helper | `p11hsFHat_shift` (HoloStripBound.lean:137) | PASS | Literal fast-angle periodicity. |
| hc-F / analytic helper | `p11hsPlanet_im_zero` (HoloStripBound.lean:146) | PASS | Original chart reality at real inputs. |
| hc-F / analytic helper | `p11hsSep_im_zero` (HoloStripBound.lean:167) | PASS | Reality of squared separation. |
| hc-F / analytic helper | `p11hsFHat_real` (HoloStripBound.lean:180) | PASS | Positive real separation gives real principal power. |
| hc-strip | `p11hsSep_real` (HoloStripGeometry.lean:45) | PASS | Definitional agreement with existing real-angle separation. |
| hc-strip | `p11hsBlock_mem_nbhd` (HoloStripGeometry.lean:48) | PASS | Original open Poincare-domain containment. |
| hc-strip | `continuousOn_p11hsSep` (HoloStripGeometry.lean:56) | PASS | Continuity of actual squared separation. |
| hc-strip | `p11hs_poincareC_shift` (HoloStripGeometry.lean:80) | PASS | All integer 2π shifts from original chart periodicity. |
| hc-strip | `p11hsPlanet_shift` (HoloStripGeometry.lean:109) | PASS | Planet chart periodicity. |
| hc-strip | `p11hsSep_shift` (HoloStripGeometry.lean:121) | PASS | Separation periodicity. |
| hc-strip | `p11hs_continuousAt_re` (HoloStripGeometry.lean:129) | PASS | Continuous complex-angle perturbation of real-angle input. |
| hc-strip | `isOpen_p11hsU` (HoloStripGeometry.lean:150) | PASS | Open original analytic domain. |
| hc-strip | `isCompact_p11hsK` (HoloStripGeometry.lean:167) | PASS | Finite-dimensional compact cell times closed ball. |
| hc-strip | `p11hs_eventually` (HoloStripGeometry.lean:171) | PASS | Uniform quarter-gap margin on compact interior. |
| hc-strip | `p11hs_strip` (HoloStripGeometry.lean:203) | PASS | Positive uniform strip, all pairs and all real angles. |
| hc-F / analytic helper | `norm_mulVec_le` (HoloStripInput.lean:49) | PASS | Row sums and Pi norm; no isometry claim. |
| hc-F / analytic helper | `norm_hRho_le` (HoloStripInput.lean:59) | PASS | Explicit n factor in the quadratic shift. |
| hc-F / analytic helper | `p11hs_fderiv_entry` (HoloStripInput.lean:81) | PASS | Entrywise derivative of the same matrix map. |
| hc-F / analytic helper | `p11hs_differentiableOn_fderiv` (HoloStripInput.lean:100) | PASS | Holomorphic derivative on an open domain. |
| hc-F / analytic helper | `P11HsHyp.B'_nonneg` (HoloStripInput.lean:143) | PASS | Derived from a nonempty row at the ball center. |
| hc-F / analytic helper | `p11hs_L_mem` (HoloStripInput.lean:151) | PASS | Exact reciprocal 2π action scaling. |
| hc-F / analytic helper | `p11hsAngle_input` (HoloStripInput.lean:170) | PASS | Literal input angle formula. |
| hc-F / analytic helper | `p11hsSlow_input` (HoloStripInput.lean:178) | PASS | Literal slow coordinate formula. |
| hc-F / analytic helper | `norm_H_le` (HoloStripInput.lean:185) | PASS | n B' rz² and the source angle budget. |
| hc-F / analytic helper | `p11hsInput_mem_good` (HoloStripInput.lean:202) | PASS | Rotation, center and strip hypotheses give actual containment; N1. |
| hc-F / analytic helper | `p11hsInput_differentiableOn` (HoloStripInput.lean:239) | PASS | Holomorphic actual input including derivative terms. |
| hc-F / analytic helper | `p11hs_real_mem_ball` (HoloStripInput.lean:294) | PASS | Real inclusion preserves the Pi norm. |
| hc-F / analytic helper | `p11hs_fderiv_im` (HoloStripInput.lean:300) | PASS | Real-line differentiation establishes derivative reality. |

## Definition classification

All definitions are exposed in a public noncomputable section. No new global instance,
root declaration, choice/default selector, infimum or supremum is introduced.

| Declaration | Classification | Whole-carrier behavior / guard |
|---|---|---|
| p11hsBlock | Coordinate construction | Literal `(λ,ξ;Λ,η)` block, no branch. |
| p11hsPlanet | Actual imported chart application | poincareC at the block; original domain guards every analytic use. |
| p11hsSep | Actual complex squared separation | Sum of squares, intentionally without complex conjugation; equals separationC at real angles. |
| p11hsK | Auxiliary compact set | Real fundamental cell times a closed slow ball. |
| p11hsAngle | Projection | Fast position block. |
| p11hsSlow | Projection | Existing `(ξ,Λ,η)` order. |
| p11hsFHat | Literal complex Newtonian potential | Principal complex negative-half powers. Outside the good domain no analytic/physical claim is made and no fallback value is exploited. |
| p11hsGood | Analytic-domain predicate | Original angle neighborhood, actual polydisc and explicit positive separation. |
| p11hsMInf | Explicit finite bound | Defined for all axes; positivity/bound theorems require ordered positive axes, so denominators are nonzero. |
| p11hsInput | Actual complex lift formula | Uses actual fderiv; holomorphy and reality proofs establish the required derivatives on the open ball. No reliance on off-domain fderiv fallback. |
| p11hsF | Actual composition | Exactly p11hsFHat applied to p11hsInput. |
| P11HsHyp | Conditional source/domain inputs | No field assumes a property of F; separation has its own independent supplier. Original-axis applicability caveat N1. |

## Verification

Verification receipts follow below. All Lean/Lake commands are serialized with
`LEAN_NUM_THREADS=1` and `nice -n 5`; the targeted build uses the required compile gate.

### Targeted build — PASS

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap2c KAM.Planetary.Preparation.HoloStrip
```

Exit 0. Gate output: `[inp-gate] slot 3 acquired 21:39:33 for KAM.Planetary.Preparation.HoloStrip`.
Final output: `Build completed successfully (9248 jobs).` Replayed upstream modules emitted
unused-variable, deprecated-syntax/name and unused-simp/style warnings; no audited module
produced an error. No budget override was introduced.

### Axioms and exact-clause / domain probes — PASS

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/p11ap2c-audit-1.lean
```

Exit 0. The scratch file imported HoloStrip, issued `#print axioms` for every theorem
in the ledger, assigned `p11hs_F hn ha h hMF` directly to the literal four-clause type
using `p11Bound`, proved the necessary center-point condition by applying h.center at
the center of the ball, and proved the recentering existence statement below. No warning
or error was emitted. Complete axiom output:

```text
'KAM.Planetary.p11hs_strip_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsF_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsF_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsF_bound_weighted' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.single_castAdd_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsF_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsF_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hs_F' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsMInf_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_cpow_neg_half_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsFHat_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiable_p11hsBlock' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiableOn_p11hsPlanet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiableOn_p11hsSep' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsFHat_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsFHat_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsPlanet_im_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsSep_im_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsFHat_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsSep_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsBlock_mem_nbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuousOn_p11hsSep' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hs_poincareC_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsPlanet_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsSep_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hs_continuousAt_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_p11hsU' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isCompact_p11hsK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hs_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hs_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_hRho_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hs_fderiv_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hs_differentiableOn_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HsHyp.B'_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hs_L_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsAngle_input' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsSlow_input' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_H_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsInput_mem_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsInput_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hs_real_mem_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hs_fderiv_im' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The recentering probe used only existing API; its statement and proof were:

```lean
example {n : ℕ} (D : Data n) (L0 : Vec n) (hL0 : L0 ∈ actionDomain D)
    {old : ℝ} (hold : 0 < old) :
    ∃ a : Vec n, a ∈ axes n ∧ ∃ r' σ' rC : ℝ,
      0 < r' ∧ r' < rho D a ∧ 0 < σ' ∧ σ' ≤ 1/4 ∧ 2*π*σ' ≤ 1/8 ∧
      0 < rC ∧ rC ≤ old ∧
      (∀ L ∈ Metric.ball (KAM.realInclusion n L0) (rC/π), ∀ i,
        ‖L i - (action D a i : ℂ)‖ < r') ∧
      (∀ lam : CVec n, (∀ l, |(lam l).im| ≤ 2*π*σ') →
        ∀ x ∈ polydisc D a r', ∀ i j : Fin n, i < j →
          (a j-a i)^2/4 ≤ (p11hsSep D lam x i j).re) := by
  obtain ⟨a, ha, rfl⟩ := hL0
  obtain ⟨r', σ', hr', hrho, hs0, hs1, hs2, hstrip⟩ := p11hs_strip_data D ha
  let rC := min old (π*r'/2)
  have hrc : 0 < rC := lt_min hold (by positivity)
  have hrcr : rC/π < r' := by
    apply (div_lt_iff₀ Real.pi_pos).2
    have := min_le_right old (π*r'/2)
    dsimp [rC]
    nlinarith [Real.pi_pos]
  refine ⟨a, ha, r', σ', rC, hr', hrho, hs0, hs1, hs2, hrc,
    min_le_left _ _, ?_, hstrip⟩
  intro L hL i
  have hn : ‖L - KAM.realInclusion n (action D a)‖ < rC/π := by
    simpa [Metric.mem_ball, dist_eq_norm] using hL
  exact (norm_le_pi_norm (L - KAM.realInclusion n (action D a)) i).trans_lt (hn.trans hrcr)
```

P2b's R_frame at L0 gives the `actionDomain` premise; its positive t1 ensures that
L0 belongs to its own real frame ball. The existing rotation ball and its hypotheses
restrict to any smaller positive rC; rz and σ are selected afterwards. The audited API
therefore admits a source-data construction without assuming a property of the target F.
This scratch result does not claim hc-id or hc-mean at the recentered axes.

### Kernel replay — PASS

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.HoloStripGeometry KAM.Planetary.Preparation.HoloStripBound KAM.Planetary.Preparation.HoloStripInput KAM.Planetary.Preparation.HoloStrip
```

Exit 0. Complete output:

```text
replaying KAM.Planetary.Preparation.HoloStrip
replaying KAM.Planetary.Preparation.HoloStripInput
replaying KAM.Planetary.Preparation.HoloStripBound
replaying KAM.Planetary.Preparation.HoloStripGeometry
```

### Static integrity — PASS

```sh
git diff --stat inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
git diff --check
rg -n '\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace)\b|set_option' KAM/Planetary/Preparation/HoloStrip*.lean
```

The protected-path diff is empty; both whitespace checks exit 0 with no output.
The forbidden-token scan has no matches (rg exit 1). The three-dot diff contains the seven
new modules already identified above, including the three context modules; nothing under
Frozen or manifest and no generated file changed. No provider or DRAFT_SORRY theorem is
in the audited transitive KAM import closure (202 modules; 58 frozen definition modules,
all SEALED in the manifest). No new theorem anchor is imported.

A Python scan of all declarations in KAM found no reused public short name among the
new audited declarations. All are inside KAM.Planetary (the B'_nonneg extension is under
P11HsHyp); none shadows a root declaration. All four files have the copyright header,
module/import/docstring/public-section structure, and no resource override.

| File | Lines | Maximum line length |
|---|---:|---:|
| HoloStrip.lean | 193 | 100 |
| HoloStripBound.lean | 214 | 98 |
| HoloStripGeometry.lean | 288 | 97 |
| HoloStripInput.lean | 337 | 99 |

Total: 1,032 lines. The handoff's 1,030 count predates the Bound line wrapping;
this is only a bookkeeping correction. Every file is below 1,500 lines.

### Source lint, frozen guard and ABI — PASS with permitted generated-root exception

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely for the explicitly permitted generated-root staleness. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (947 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

All other source checks pass. The generated root was not regenerated; neither it nor
README, frozen sources or manifest was edited. The ABI comparison covers all 144 current
frozen declarations, beyond this package's import subset.

## Handoff disposition and remaining uncertainty

The authorized two-step parametric slice is proved and independently checked. The four
F clauses match the signed specification; the uniform strip and all supporting analytic
bounds are established. Numerical smallness choices are compatible and noncircular.
N1 records the exact original-axis gap and a checked alternative using source action-domain
data; downstream physical attachment remains a task for the owning packages. No provider,
frozen seal, actual holomorphic chart, weighted Fourier norm theorem, mean estimate or
physical identification is claimed by this report.

Temporary audit probe and receipt files under `.lake/abi-scratch/` were removed after their
contents were incorporated above. Final `git diff --check` passes. Final status has only
the new audit report and the pre-existing untracked P11A-P2c-handoff.md; no production
source or git state was changed by the auditor.
