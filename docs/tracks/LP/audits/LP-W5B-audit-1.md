# LP-W5B independent package audit 1

Audited revision: `90e33d02a956fd32d2afba3a49b3f9b87176c845`.
Comparison bases: `inp=d3a2c262b6b99851b768298de443febdd8630cb5`,
`inp-lp=7c08250f49670aa07ca7ec1b5f8361c5ff3c9ef5`.
Both requested three-dot comparisons identify the same five new implementation modules (894 lines),
five generated imports in `KAM/Root/Planetary.lean`, and the combined handoff.
Only this report is retained as an audit edit; temporary probes live under `.lake/abi-scratch/`.
Nothing in LP is frozen: this is a package acceptance audit, not a seal audit or headline closure.

Authority: the package audit brief, LP-W5B handoff AUDIT FOCUS, external LP-W5B and its two
component briefs in `/root/code/KAM-inp-lp/docs/tracks/LP/packages/`, SPEC, MAIN as amended,
and LP3-PLAN §§2.3–2.5. D58 was checked with `git show main:docs/DECISIONS.md`.
MAIN SHA-256: `68e9167f04e4a04689ea163c74e02ffcaea657b252726080abdbe37bdba48c1b`.
AMENDMENTS SHA-256: `c887d1e27354a3db7fb8a20d8bf3e33a9ef95ff3173f925ba5ebfab192651881`.

## LP3-SP-COVER — PASS WITH NOTES

The bounded target is met. All names below are in `KAM.Planetary.Spatial`.
References `C` and `P` mean `Spatial/Nek/Cover.lean` and `Spatial/Nek/Perturbation.lean`.

| Node | Lean declaration | Verdict | Reason |
|---|---|---|---|
| Slow cell | `spatialNekCellSlow` (C:46) | PASS | Literal `slowBall (n+n) (B(c)-5δ/16)`; all 2n slow pairs. |
| Openness | `isOpen_spatialNekCellSlow` (C:49) | PASS | Generic quadratic-ball openness. |
| Tube containment | `spatialNekCell_containment` (C:57) | PASS | Correct R/2 tube and all fast/slow coordinates; details below. |
| Gap positivity | `spatialNekCell_slowGap_pos` (C:116) | PASS | Positive numerator and denominator for n≥2, δ>0, B(c)≥δ. |
| Uniform gap | `exists_spatialNekSlowGap` (C:132) | PASS | Finite minimum; explicit empty-family case; √(2(n+n)). |
| Extension data | `IsSpatialStrongExtension` (P:47) | PASS | Exact four existing extension clauses, including bound only on R/2. |
| Extension existence | `exists_isSpatialStrongExtension` (P:61) | PASS | Constructed from `exists_spatialStrongTube`, no new analytic assumption. |
| Normalization | `spatialNekNormalizedPerturbation` (P:72) | PASS | Explicitly authorized tube cutoff; no consumer uses its exterior values. |
| Tube evaluation | `spatialNekNormalizedPerturbation_of_mem` (P:82) | PASS | Exact division formula on its carrier. |
| Nested tubes | `complexTubeNM_half_subset` (P:88) | PASS | Same core and witness, R/2<R. |
| Bound and membership | `spatialNekCell_mem_tube` (P:94) | PASS | Uses the R/2 containment for the bound before enlarging membership to R. |
| Positive perturbation | `isPartialPerturbation_spatialNekCell` (P:104) | PASS | Holomorphy, norm≤1, reality, and lattice periodicity all discharged. |
| Negative perturbation | `isPartialPerturbation_neg_spatialNekCell` (P:131) | PASS | Standard negation adapter. |
| Real region | `spatialNekCellRegion` (P:143) | PASS | Literal fast-outer-cell × slow-ball condition; fast angles unrestricted. |
| Region openness | `isOpen_spatialNekCellRegion` (P:147) | PASS | Continuous projections, intersection of preimages. |
| Complexification | `complexifyPhase_mem_spatialNekCell` (P:158) | PASS | Real points satisfy imaginary inequalities because ρ>0. |
| Trace | `spatialNekCell_region_trace` (P:170) | PASS | Chart safety and exact spatial physical perturbation trace. |
| Hamiltonian identity | `spatialNekCell_hamiltonian_eq` (P:185) | PASS | ε=B₀μ cancels normalization; exactly `spLiftChartHam ν μ`. |
| Field identity | `spatialNekCell_field_eq` (P:203) | PASS | Open-region equality gives equal derivatives/fields and differentiability. |
| Uniform bundle | `exists_spatialNekPerturbation` (P:236) | PASS | R, B₀, P chosen before c, μ, w; uniform over every level-set centre. |

Containment uses rs=min(4r_g,R/4), η=rs/4, ρ=rs/8. Fast real actions lie within 2η,
and their complex distance from c is <2η+ρ=5rs/8<rs. Fast-angle imaginary parts and
both slow-coordinate imaginary blocks are <ρ<4η=rs. Choosing the real slow witness
as the real parts gives exactly the sum split
`Σ(y₁²+y₂²)/2 = (Σy₁²+Σy₂²)/2`.
Since B(c)-5δ/16≤B(c)-δ/4, that witness belongs to `spatialSecularBall`.
The maximum width is rs≤R/4<R/2, so the extension's actual bounded tube is reached.
This is MAIN L8 (244–271), L18 (580–597) with N2/N3/N12, specialized to the package cells.
There is no alignment restriction on this domain.

The slow gap separates A=B(c)-5δ/16 from A′=B(c)-3δ/8, with A-A′=δ/16 and
A′≥5δ/8>0. Its denominator √(2(n+n)) is the correct sup-to-Euclidean factor for
4n real slow coordinates. The positive finite infimum is taken only for a nonempty family;
the empty family uses εD=1 with a vacuous conclusion.

For ±P, normalization uses B₀>0 and M≤B₀, and the bundle sets B₀=max(M,1).
Periodicity also proves the shifted point is inside the tube before evaluating the cutoff.
The Hamiltonian calculation is h+(B₀μ)(f/B₀)=h+μf, for every real μ. Its time is physical
time: no extra factor B₀, μ, 2π or time conversion is introduced. The bundle is stronger
than a finite-centres-only statement and keeps the planar quantifier order.

Definition classification (whole carriers): `spatialNekCellSlow` and `spatialNekCellRegion`
are literal polynomial sublevel/preimage sets for all real parameter values. A nonpositive
slow level yields the empty set; with n=0 the empty quadratic sum is zero, so the slow ball
is the singleton phase space precisely for a positive level. No positivity or openness theorem
silently assumes a nonempty ball. `IsSpatialStrongExtension` is a source-data predicate;
its fields are independently produced by the existing extension theorem. It does not bundle
perturbation admissibility or drift. `spatialNekNormalizedPerturbation` equals fc/B₀ on the
open R tube and zero everywhere else, including its boundary. At B₀=0 division gives zero;
normalization claims require B₀>0. The cutoff may fail to be continuous at the tube boundary,
but every analytic/field consumer is confined to the cell inside R/2. This fallback is explicitly
required by the component brief and is never used to discharge an analytic claim outside its carrier.
These are internal package definitions, not new physical frozen objects under D59.

## LP3-SP-DRIFT — PASS WITH NOTES

References `K`, `S`, `D` mean `Spatial/Nek/Drift/Kepler.lean`, `Drift/Slow.lean`, `Drift.lean`.

| Node | Lean declaration | Verdict | Reason |
|---|---|---|---|
| Kepler collar margin | `nekCell_nbhd_re_mem_ball` (K:47) | PASS | Real-part distance <2η+ρ=5rs/8<rs. |
| Kepler data | `spatialNek_kepler_premises` (K:81) | PASS | Uniform positive g,m,M for h and -h on the stated collars. |
| Uniform cell drift | `exists_spatialNek_cell_threshold` (K:124) | PASS | Correct 2n slow pairs, uniform in P, both time signs and exponent bridges. |
| Sharp slow bound | `spatialNek_sharp_slow_bound` (S:43) | PASS | Two δ/16 threshold changes improve stopped δ/2 margin to 3δ/8. |
| Aligned deficit | `spatialNek_chart_amd_lt` (S:65) | PASS | Explicit conditional chart identity; alignment supplied by the existing lift. |
| Slow erosion | `spatialNek_slow_mem_innerCore` (S:77) | PASS | Generic erosion at n+n, literal chart slow sum and correct √(2(n+n)). |
| Solution transfer | `spatialNek_isSolutionOn_of_region` (S:90) | PASS | Explicit conditional helper; its field premise is proved by COVER's bundle. |
| Radius | `spatialNekRadius` (D:45) | PASS | (B₀μ) raised to the planetary drift exponent. |
| Horizon | `spatialNekHorizon` (D:48) | PASS | exp((B₀μ)^(-a_n)); no hidden rescaling. |
| Small powers | `exists_spatialNek_rpow_lt` (D:51) | PASS | Positive κ,b; explicit threshold κ^(1/b). |
| Stopped supplier | `spatial_stopped_drift_nek` (D:67) | PASS | Constants precede μ and orbit; literal first-exit hstop conclusion. |

The deviation from the suggested `kepler_cell_drift` is justified: no extra assumption that
fixed cell collars fit Imin/4 is introduced. For c in the finite cover,
`closedBall c rs ⊆ cthickening (4r_g) 𝓛_δ = sharedTube` follows from rs≤4r_g.
The complex collar's real parts therefore belong to the compact chamber tube U.
Uniform bounds Imin≤Re z_i and I_i≤Imax on the relevant real points establish holomorphy,
C², reality and the complex Hessian bound. The constants actually chosen are
`g=νmin³/Imax³`, `m=3νmin³/Imax⁴`, `M=keplerHessConst ν Imin`.
These are legitimate (sharper real-point bounds than the plan's Imax+rs denominators):
definiteness is required at real points, while the complex Hessian uses Re z_i≥Imin.
The sign adapter for -h and CELL's backward-time argument preserve the same real cells.
The finite-family threshold is chosen before ε and P, including an empty family.

Sharp slow control uses only the stopped conditions and existing shared-tube modulus:
B(Λ(z u))≤B(I⁰)+δ/16≤B(c)+δ/8. Hence C(z u)<B(c)-3δ/8.
The aligned lift proves its chart deficit equals C; slow erosion is then derived,
not assumed at the main theorem boundary. Fast-cell membership and initial erosion follow
from the cover closeness η/2 and r≤η/4. COVER's open-region field equality supplies S:90's
premise; the main theorem supplies no arbitrary field-equality assumption.

`planetaryDriftExponent_eq_partial` and `planetaryTimeExponent_eq_partial` are rewritten
explicitly at K:162–163. Only the slow dimension changes; a_n=2/(6n²-3n+14),
b_n=3/(6n²-3n+14) still depend on the fast dimension n. This is LP3-PLAN's approved
nonarithmetic variant, not a claim to MAIN's Diophantine O(√μ) rate.
The smaller horizon exp(ε^(-a_n)) is bounded by CELL's ε⁻¹exp(ε^(-a_n)) since 0<ε<1.
With ε*=min(ε₀,ε₁,1) and μ₀=ε*/(2B₀), μ≤μ₀ yields ε≤ε*/2<ε*;
thus the closed upper μ endpoint is valid.

Hypothesis audit: `spatialActionVector ν z₀ ∈ L` is initial-set membership, used with the
nonnegative physical AMD and the initial sharp margin to put I⁰ in 𝓛_δ. It does not assume
a drift, alignment or AMD estimate. `SpatialLiftData` is unchanged: positive masses,
n≥2, compact chamber tube, positive δ,r, radius budget, initial negative energy,
action-ball containment, initial AMD margin and initial alignment. These are standing
source/typing data, and the theorem independently supplies its uniform radius and budget.
Alignment is permitted for this internal supplier by the spatial brief; the rotation
reduction for a public orientation-free headline is outside this package. The stopped
premise contains the weaker strict drift <r and AMD margin δ/2, exactly as first exit
requires; the proved ≤r/2 is never assumed. The low-level chart/field transfer lemmas
are distinctly named conditional helpers and their conditions are discharged in D:140–161.

Definition classification: the only new definitions in DRIFT are `spatialNekRadius` and
`spatialNekHorizon`. Both are literal formulas on their whole declared carriers. For any
natural n the exponent denominators are positive. At B₀μ=0, Mathlib real power gives
radius 0 and horizon 1 (the negative exponent is nonzero). At a negative base the real
power is the real part of complex power, not a positive physical scale; no theorem uses
that regime. Every physical-scale conclusion explicitly requires B₀≥1 and μ>0. There
is no auxiliary branch or convenient fallback used by the proof.

## Combined verdict and notes

**PASS WITH NOTES** for LP-W5B, scoped to its exact non-frozen package statements.
No blocking source-fidelity, carrier, quantifier-order or conclusion-shaped-hypothesis defect found.
This supplies stopped drift for the existing confinement consumer; it does not itself
assemble, freeze or prove the final spatial safety headline.

- N1: Generated-root exception: both comparison diffs contain five import additions in
  `KAM/Root/Planetary.lean`. This is expressly permitted by the component briefs/handoff.
  `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. No audit repair
  or regeneration of a protected/generated file was performed.
- N2: Direct use of `cell_drift_two_sided` replaces the suggested Kepler adapter, with the
  collar premises proved locally as described above. No hypothesis or intended conclusion changes.
- N3: The source-facing exponents are the LP3 variant's weaker rates; the supplied MAIN
  references describe domain/first-exit ingredients. They are not evidence that this variant
  has MAIN's nonresonant rates. Initial alignment remains internal to `SpatialLiftData`.

Suspected MAIN/AMENDMENTS errata: none newly found in this bounded review. No new source
repair is proposed. No proof heartbeat/design signal was encountered. Existing dependencies
were inspected at their consumed interfaces, not re-audited globally.

## Validation

All Lean/Lake invocations in this audit are serial and run under the exact D53 wrapper:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

Lint command (the sole lint entry point used):

```sh
/root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-w5b
```

Exit 0; complete substantive output:

```text
check_lean_modules: PASS (3788 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

No stale-root exemption was needed for lint. The opt-in lunar declarations were only
hash-checked by lint, as reported; they are outside this package.

Static checks:

```sh
git diff inp...HEAD --stat
git diff inp-lp...HEAD -- KAM
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
rg -n 'axiom|sorry|admit|unsafe|opaque|maxHeartbeats|maxRecDepth|maxSynthPendingDepth|synthInstance.max|EuclideanSpace|KAM.Provider' KAM/Planetary/Spatial/Nek
wc -l KAM/Planetary/Spatial/Nek/*.lean KAM/Planetary/Spatial/Nek/Drift/*.lean
```

Protected-path diff: empty. Forbidden-token scan: no matches (rg exit 1).
Sizes: Cover 163, Perturbation 271, Drift/Kepler 168, Drift/Slow 116, Drift 176.
All five files have copyright, `module`, public imports, module docstring and
`@[expose] public noncomputable section`. There are no new provider imports or
budget overrides. The consumed partial-convexity anchor is `SEALED` in the manifest;
D58 authorizes its use through the existing CELL/Exponential interfaces. The expected
transitive provider behind a sealed anchor is not a direct provider import by LP.

Kernel replay and short-name checks: the user states these were run by the launcher.
They were not rerun, and no fresh replay exit code or unseen launcher output is claimed.
The handoff reports standard axioms; this audit independently checks every new theorem below.


Targeted build command (driver invokes each target separately, serially, under the
D53 wrapper and compile gate):

```sh
/root/code/KAM-inp/.drafts/LP/lp_build.sh /root/code/KAM-inp-lp-w5b KAM.Planetary.Spatial.Nek.Cover KAM.Planetary.Spatial.Nek.Perturbation KAM.Planetary.Spatial.Nek.Drift.Kepler KAM.Planetary.Spatial.Nek.Drift.Slow KAM.Planetary.Spatial.Nek.Drift
```

Driver exit 0. In target order the terminal success lines were:

```text
Build completed successfully (9353 jobs).
Build completed successfully (9360 jobs).
Build completed successfully (9356 jobs).
Build completed successfully (9362 jobs).
Build completed successfully (9375 jobs).
```

Lake replayed existing dependency warnings (unused binders/tactics/simp arguments and
a deprecated `dif_pos`); no package build failure or resource-limit signal occurred.
These are targeted dependency-closure checks, not a clean/global build or kernel replay.

Axiom/consumer probe command:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean .lake/abi-scratch/LPW5BAudit.lean
```

Exit 0, no errors. The probe imports `Spatial.Nek.Drift` and `Spatial.Confinement`,
prints axioms for every new public theorem (25), and elaborates the following consumer
application after obtaining the constants from `spatial_stopped_drift_nek`:

```lean
  have consumer (μ : ℝ) (hμ : 0 < μ) (hle : μ ≤ μ₀)
      (z₀ : Phase (n * 3)) (hAz : spatialActionVector ν z₀ ∈ L)
      (hd : SpatialLiftData ν (sharedTube ν L δ rg) z₀ δ (spatialNekRadius n B0 μ)) := by
    obtain ⟨hr, hr4, hbudget, hstop⟩ := H μ hμ hle
    exact spatialStrongFirstExit_of_stopped_drift hν hn hg.compact hg.subset_chamber hδ hr
      (Real.exp_pos _) hbudget hd.physical hd.ball hd.amd (hstop z₀ hAz hd)
```

This checks literal compatibility, including the closed μ endpoint, physical time,
stop antecedent and drift conclusion. No conversion lemma, extra stopped estimate or
weakened consumer was supplied. Ball containment is the unchanged lift datum; for its
construction, the returned r≤4r_g and I⁰∈𝓛_δ put the closed action ball in the shared tube.

Axiom output below is verbatim except that multiline lists are joined onto one line:

```text
'KAM.Planetary.Spatial.exists_isSpatialStrongExtension' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialNekNormalizedPerturbation_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.complexTubeNM_half_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialNekCell_mem_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.isPartialPerturbation_spatialNekCell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.isPartialPerturbation_neg_spatialNekCell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.isOpen_spatialNekCellRegion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.complexifyPhase_mem_spatialNekCell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialNekCell_region_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialNekCell_hamiltonian_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialNekCell_field_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.exists_spatialNekPerturbation' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.isOpen_spatialNekCellSlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialNekCell_containment' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialNekCell_slowGap_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.exists_spatialNekSlowGap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.exists_spatialNek_rpow_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatial_stopped_drift_nek' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialNek_sharp_slow_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialNek_chart_amd_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialNek_slow_mem_innerCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialNek_isSolutionOn_of_region' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.nekCell_nbhd_re_mem_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialNek_kepler_premises' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.exists_spatialNek_cell_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The scratch probe was removed after its successful run. The final retained audit change
is only `docs/tracks/LP/audits/LP-W5B-audit-1.md`; no source, manifest, generated root,
package configuration or dependency was edited. No git state-changing command was run.
