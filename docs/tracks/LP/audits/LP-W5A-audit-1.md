# LP-W5A independent audit 1

Audited HEAD `d83718b51aceb600c5e13f3e68e404b6073e504e` in
`/root/code/KAM-inp-lp-w5a`, 2026-11-01. Refute-first statement, definition and proof review.
Nothing in LP is frozen. This is a bounded package audit, not a seal or headline safety audit.

Read AGENTS.md, PLAN, DECISIONS, the independent-package audit brief, LP-W5A brief and handoff,
the four component briefs and handoffs, SPEC, MAIN as amended by AMENDMENTS, and LP3-PLAN
(particularly §2.1–§2.4). The controlling import permission is the explicit D58 ruling reproduced
in the package briefs and audit focus; this checkout's DECISIONS file itself ends at D51.

Both `git diff inp...HEAD` and `git diff inp-lp...HEAD -- KAM` were inspected. The code scopes
coincide: six new modules (1,441 lines) and six generated imports in `KAM/Root/Planetary.lean`.
`inp = ba0ef7f41f06f24d16b542e3f9852c70ccb59696`;
`inp-lp = acf6083ce13f9469696f7ce3e25a1f984a2de911`.
No production file was edited by this audit. Only this report is retained; temporary probes are removed.

All declaration names below are in `KAM.Planetary.StrongAMD`.

## LP3-KEP — PASS WITH NOTES

The Kepler function is MAIN (4), with radian frequency `ν_i³/I_i³` and Hessian
`diag(-3ν_i³/I_i⁴)`. `keplerC_definite` supplies the sealed definition with sign `-1`;
`hasDefiniteFastPart_neg` supplies sign `+1` for the negated function. The frequency lower bound
uses one coordinate, justified by `1 ≤ n`. No normalization `max ν = 1` is needed: omitting it
strengthens this infrastructure result.

The two collars consume at most `Imin/2`: `ρ₀ = Imin/4`, `ρ ≤ ρ₀` gives
`Re z_i ≥ Imin/2` and real-coordinate upper bound `Ibar = Imax + Imin/2`.
Thus `g = νmin³/Ibar³`, `m = 3νmin³/Ibar⁴`, and
`Mcomplex = Σ_i 3ν_i³/(Imin/2)⁴` are positive and chosen before the fast set and width.
The brief's `Imin/2` collar is an example, not a required literal; the smaller implemented
collar pays both enlargements. This is a harmless recorded adjustment, with a stronger real-part margin.

| Declaration (node) | Verdict | Reason |
|---|---|---|
| `exists_pos_le_forall_fin` (Kepler.lean) | PASS | Positive lower bound; empty Fin handled explicitly. |
| `exists_chamber_bounds` (Kepler.lean) | PASS | Compact chamber bounds; empty U and n = 0 allowed. |
| `actionNbhd_re_near` (Kepler.lean) | PASS | Common real witness; both collar distances are paid. |
| `exists_keplerMargin` (Kepler.lean) | PASS | ρ₀ = Imin/4; real-part margin Imin/2; weaker assumptions on ρ are harmless. |
| `keplerHessConst` (Kepler.lean) | PASS | Literal finite Hessian bound sum, no choice or fallback. |
| `keplerHessConst_pos` (Kepler.lean) | PASS | Nonzero dimension and positive masses/denominator guard strict positivity. |
| `keplerC_clauses` (Kepler.lean) | PASS | Holomorphy, C², reality and operator Hessian bound on the guarded neighbourhood. |
| `keplerCNeg_clauses` (Kepler.lean) | PASS | Negation preserves all four clauses and the Hessian bound. |
| `keplerC_definite` (Kepler.lean) | PASS | Exact HasDefiniteFastPart; σ = -1, nonvanishing frequency and real C³. |
| `lp3_kepler_data` (Kepler.lean) | PASS | All fast premises for ±h; constants depend only on ν,U. |

## LP3-COVERPERT — PASS WITH NOTES

Widths, balls, collar and threshold budget are exactly plan (F3)–(F5). The finite cover uses
η/2 balls, leaving room for the full closed fast erosion when r ≤ η/4.
`partialComplexDomain G′ D ρ` is contained in the R/2 tube, not merely its real slice.
The slow witness is the real slow pair, so no circular-orbit exclusion or slow-periodicity
premise is introduced. At B(c) = δ the levels are still strictly positive:
A = 11δ/16 and A′ = 5δ/8, with A−A′ = δ/16. The slow erosion is in the ambient max norm;
the √(2n) conversion is supplied by the reused `stopped_slow_erosion`.

**N1 (brief inconsistency, nonblocking).** LP3-COVERPERT brief, LP3-PERT second bullet,
says “equals the chart Hamiltonian divided by B₀ in the time scale the plan specifies”.
LP3-PLAN §0.4 and §2.3 explicitly specify no time conversion. Since P = fc/B₀ and ε = B₀μ,
the exact physical Hamiltonian is h+εRe P = h+μf. Dividing the full Hamiltonian by B₀ would
also divide its Kepler term and change time. `nekCell_hamiltonian_eq` follows the plan and
MAIN L8's exact physical split. Accept the implementation; correct the component brief's wording.
The all-centres perturbation result is stronger than a cover-only result and is used correctly.

| Declaration (node) | Verdict | Reason |
|---|---|---|
| `nekWidth` (Cover.lean) | PASS | Literal min(4rg,R/4). |
| `nekEta` (Cover.lean) | PASS | Literal nekWidth/4. |
| `nekRho` (Cover.lean) | PASS | Literal nekWidth/8. |
| `nekWidth_pos` (Cover.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `nekWidth_le_four_mul` (Cover.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `nekWidth_lt_half` (Cover.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `nekEta_pos` (Cover.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `nekRho_pos` (Cover.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `nekRho_le_eta` (Cover.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `four_mul_nekEta` (Cover.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `nekEta_le` (Cover.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `nekCellInner` (Cover.lean) | PASS | Open max-norm ball of radius η. |
| `nekCellOuter` (Cover.lean) | PASS | Open max-norm ball of radius 2η. |
| `nekCellLevel` (Cover.lean) | PASS | Exact sharp local level B(c)-5δ/16. |
| `nekCellSlow` (Cover.lean) | PASS | Round slow AMD ball, not a coordinate box. |
| `isOpen_nekCellInner` (Cover.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `convex_nekCellInner` (Cover.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `isOpen_nekCellOuter` (Cover.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `convex_nekCellOuter` (Cover.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `isOpen_nekCellSlow` (Cover.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `nekCellInner_subset_outer` (Cover.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `nekCell_collar` (Cover.lean) | PASS | Closed ρ-ball about each point of G lies in G′; strict outer margin. |
| `nekCell_level_le` (Cover.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `IsNekCover` (Cover.lean) | PASS | Only finite-cover geometry is bundled, no drift field. |
| `exists_isNekCover` (Cover.lean) | PASS | Compactness gives centres in the sharp level set and η/2 cover. |
| `nekCell_mem_of_close` (Cover.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `nekCell_mem_innerCore` (Cover.lean) | PASS | Closed max-norm erosion, including r = 0. |
| `IsNekCover.mem_innerCore` (Cover.lean) | PASS | Each admissible initial point belongs to an eroded cell. |
| `nekCell_threshold_bound` (Cover.lean) | PASS | Shared compact modulus pays δ/16. |
| `nekCell_threshold_bound_of_close` (Cover.lean) | PASS | η/2 proximity implies the shared-tube distance bound. |
| `norm_sub_ofReal_re_eq` (Cover.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `nekCell_containment` (Cover.lean) | PASS | Whole partialComplexDomain lies in the R/2 tube; 2η+ρ < rs. |
| `nekCell_slowGap_pos` (Cover.lean) | PASS | B(c) ≥ δ keeps both radicands positive, including equality. |
| `exists_nekSlowGap` (Cover.lean) | PASS | Finite minimum of positive gaps; empty family gets positive bound 1. |
| `IsStrongExtension` (Perturbation.lean) | PASS | Exactly the four pre-existing extension clauses, not assumed drift. |
| `exists_isStrongExtension` (Perturbation.lean) | PASS | All extension fields obtained from exists_strongTube. |
| `nekNormalizedPerturbation` (Perturbation.lean) | PASS | Planned fc/B₀ on the tube, zero outside; see whole-carrier classification. |
| `nekNormalizedPerturbation_of_mem` (Perturbation.lean) | PASS | Exact trace on the tube; no positive-B₀ assumption needed for this identity. |
| `complexTube_half_subset` (Perturbation.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `nekCell_mem_tube` (Perturbation.lean) | PASS | Containment plus extension bound, valid at all cell centres in the level set. |
| `isPartialPerturbation_nekCell` (Perturbation.lean) | PASS | All four sealed clauses, including full integer fast-periodicity. |
| `isPartialPerturbation_neg_nekCell` (Perturbation.lean) | PASS | Negation preserves the sealed perturbation predicate. |
| `nekCellRegion` (Perturbation.lean) | PASS | Exact real V_j with outer fast cell and slow ball. |
| `isOpen_nekCellRegion` (Perturbation.lean) | PASS | Exact elementary width, ball, norm or openness consequence of the displayed definitions. |
| `complexifyPhase_mem_nekCell` (Perturbation.lean) | PASS | Zero imaginary coordinates satisfy positive strip widths. |
| `nekCell_region_trace` (Perturbation.lean) | PASS | Real trace and chartSafe follow from proved extension data. |
| `nekCell_hamiltonian_eq` (Perturbation.lean) | PASS WITH NOTES | PASS WITH NOTES: h+(B₀μ)Re P = liftChartHam, without division/time rescaling. |
| `nekCell_field_eq` (Perturbation.lean) | PASS | Equality on open V_j plus actual differentiability guards fderiv. |
| `exists_nekPerturbation` (Perturbation.lean) | PASS | One P and B₀ ≥ 1 for every level-set centre, stronger than only cover centres. |

## LP3-CELL — PASS

Read the frozen binder list and definitions directly. The anchor is `SEALED` in the manifest.
Both calls in `cell_threshold_uniform` pass domains, collar, h and fast data before extracting
μ₀; P and the orbit are quantified afterwards, with strict μ < μ₀. `PartialConvexConclusion`
retains C > 0, the exact solution domain, the initial closed erosion, the min(C,horizon),
the slow condition only through the query time, and drift ≤ μ^b/2. No conclusion is weakened.
Taking two finite lower bounds and their minimum is equivalent threshold bookkeeping to a
minimum over cells × signs; an empty cell family is handled without a fabricated centre.

Time reversal differentiates w(-s), negates both h and P and uses the negative Hamiltonian field.
The two-sided corollary needs the genuine frozen solution predicate only on uIcc, including its
two-sided derivatives at endpoints. This is stronger than requiring a solution on a larger
open interval. At t = 0 the drift is zero; no C = 0 call to the frozen theorem is made.
The Kepler adapter chooses its collar before all cell data. Its generic slow dimension k is
not replaced by a planetary dimension in the statement.

| Declaration (node) | Verdict | Reason |
|---|---|---|
| `PartialConvexConclusion` (Cells.lean) | PASS | Definitional transcription of the frozen conclusion; no μ threshold hidden. |
| `exists_pos_le_forall_fintype` (Cells.lean) | PASS | Positive common bound for any finite family, including the empty type. |
| `cell_threshold_uniform` (Cells.lean) | PASS | Threshold before P,C,orbit; strict μ < μ₀; common minimum over cells and signs. |
| `isSolutionOn_reverse_neg` (Cells.lean) | PASS | Both h and P negated; chain derivative and vector-field sign agree. |
| `cell_drift_two_sided` (Cells.lean) | PASS | Exact frozen orbit premises on uIcc; t<0,t=0,t>0 treated separately. |
| `kepler_cell_drift` (Cells.lean) | PASS | Fast assumptions discharged by KEP; ρ₀ precedes the finite cell family. |

## LP3-DRIFT — PASS WITH NOTES

The dependency order is acyclic: compact level set → Kepler collar ρ₀ → shrink
rg = min(rg₀,ρ₀/2) → analytic extension and B₀,P,R → finite cover → cell thresholds and slow
gap → scalar cutoff. Since η ≤ rg, the outer cells fit in cthickening ρ₀ of the level set and
ρ ≤ ρ₀. This is a valid refinement of the plan's shared-tube Kepler-data description.

With ε₀ = min(1,μ₁,y₁,y₂,y₃) and μ₀ = ε₀/(2B₀), the external non-strict μ ≤ μ₀ implies
0 < ε = B₀μ ≤ ε₀/2 < ε₀. Thus the frozen strict threshold and all three radius limits are
satisfied. ε < 1 pays exp(ε^(-a)) ≤ ε⁻¹exp(ε^(-a)). The exported shorter horizon is exactly
the plan's physical-time horizon. The exponent bridges are the existing literal planetary/partial
identities, with a = 2/(6n²−3n+14) and b = 3/(6n²−3n+14).

The stopped slow estimate spends δ/16 twice and obtains strict C < B(c)−3δ/8; the positive
gap to B(c)−5δ/16 pays the closed slow erosion. The lifted solution stays in G and V_j;
therefore field equality and differentiability give the exact frozen solution predicate.
At Drift.lean's final call, hfield comes from `hident` and hcell from the proved `hcell`
returned by `kepler_cell_drift`. Neither remains a premise of either final supplier.

**N2 (scope boundary, nonblocking).** `nek_stopped_drift_core` is public Lean infrastructure,
although described as internal in the audit focus. Its documentation explicitly labels hfield
and hcell as conditional cell data; it is not a source theorem. Those conclusion-like fields
are proved and discharged at its sole package call. The exported supplier assumes only standing
source data, initial LiftData, level-set typing and the precise stopped conditions. LiftData's
initial AMD margin and StoppedOn's temporary AMD bound are intended source premises, not a
pre-assumed global drift or confinement conclusion. Planar orientation is existing LiftData;
reflection and final first-exit assembly remain LP3-PS work.

After fixing the supplied μ,z₀,LiftData, `lp_stopped_drift_nek_hstop` quantifies exactly
J, OrdConnected, 0∈J, z, moving solution, z 0=z₀, t∈J, the time bound and the literal stopped
antecedent of Confinement.lean:177–182, with r=(B₀μ)^b. Its time conversion uses
(B₀μ)^(-a)=B₀^(-a)μ^(-a), B₀>0, μ>0; c>0 and T₀=1. No additional orbit premise occurs.
The initial action's membership in the sharp level set is necessary typing data, outside hstop.

| Declaration (node) | Verdict | Reason |
|---|---|---|
| `isSharedTube_of_le` (Drift/Stopped.lean) | PASS | Positive shrink preserves compactness, chamber and shared modulus. |
| `nek_sharp_slow_bound` (Drift/Stopped.lean) | PASS | Two δ/16 allowances yield strict C < B(c)-3δ/8 from StoppedOn. |
| `nekNHam` (Drift/Stopped.lean) | PASS | Exact frozen degenerate Hamiltonian at arbitrary ε; no hidden rescaling. |
| `nek_isSolutionOn_cell` (Drift/Stopped.lean) | PASS | Conditional field-transport helper, with genuine two-sided derivative. |
| `nek_stopped_drift_core` (Drift/Stopped.lean) | PASS | Conditional cell helper; hfield and hcell fully discharged by Drift.lean. |
| `exists_pos_rpow_lt` (Drift.lean) | PASS | Positive base and exponent; continuity threshold realized by x^(1/b). |
| `lp_stopped_drift_nek` (Drift.lean) | PASS | Non-arithmetic supplier, budget and r ≤ 4rg; constants precede μ and orbit. |
| `lp_stopped_drift_nek_hstop` (Drift.lean) | PASS | Literal confinement hstop type after fixing z₀ and LiftData; time cμ^(-a). |

## Combined verdict — PASS WITH NOTES

All four bounded targets are met. There is no blocking source-fidelity, carrier, quantifier,
normalizer, sign or circular-hypothesis finding. N1 is a brief defect; N2 records the explicitly
conditional helper boundary. The smaller KEP collar, all-centres perturbation strength,
shared-tube shrink and generated root imports are accounted for. Nothing here proves the LP3
headline, the future LP3-PS assembly, or MAIN's Diophantine theorem by itself.

### Definition classification (all 14 new definitions/structures)

| Definition | Whole-carrier classification and edge cases |
|---|---|
| `keplerHessConst` | Literal finite sum on every ν,c,n. For c=0 Lean division gives 0; no positivity or analytic estimate uses c=0. Strict positivity explicitly requires n≠0, positive masses and c>0. |
| `nekWidth`, `nekEta`, `nekRho` | Literal real arithmetic for arbitrary rg,R. Nonpositive widths are not clamped; every use as a width supplies positivity. |
| `nekCellInner`, `nekCellOuter` | Literal metric balls for every radius, including the usual empty balls at nonpositive radius. |
| `nekCellLevel` | Literal B(c)−5δ/16 for all c,ν,δ; no chamber substitution or minimizer choice. Physical uses have c in the sharp level set. |
| `nekCellSlow` | Literal quadratic slow ball for every level and dimension. A nonpositive level gives an empty set. Accepted centres and δ>0 give a positive level. |
| `IsNekCover` | Exactly centres-in-level-set plus η/2-cover. Empty s is legitimate only for an empty level set; existence does not invent a centre. |
| `IsStrongExtension` | Exactly the proved four extension clauses. M need not be positive here; normalization chooses max(M,1). No hard drift step is bundled. |
| `nekNormalizedPerturbation` | Explicit planned cut: fc/B₀ on the tube and 0 elsewhere. B₀=0 gives totalized zero division, but all perturbation/field uses require B₀>0. Boundary and off-tube values are never used as analytic or physical data. Cells and their integer translates are proved inside the open tube before unfolding this definition. This authorized cut from the specific LP3 plan does not replace any sharp threshold by a fallback. |
| `nekCellRegion` | Literal open product condition on real fast actions and slow phase; fast angles unrestricted. Empty factors give an empty region without fabricated chart points. |
| `PartialConvexConclusion` | Exact quantified frozen conclusion for arbitrary parameters. This predicate asserts a property, and is only obtained from the sealed theorem under its premises. |
| `nekNHam` | Exact degenerateHamiltonian(realPart Kepler)(Re P∘complexify) ε for every input; no choice, cut or implicit time change. Real differentiability is separately proved whenever a field is used. |

Empty U/level set and empty cell types are accepted. Equality B(c)=δ remains admissible.
The KEP result excludes n=0 exactly where nonzero frequency and positive Hessian constant require it;
CELL requires n≥2,k≥1, and planar DRIFT uses k=n. Ambient spaces are Pi types and Phase products;
no EuclideanSpace is introduced. All 59 new theorem statements and all 14 bodies were reviewed.

### Validation and provenance

Fresh checks, serialized; every Lean/Lake invocation ran inside the D53 4G/no-swap scope.
No resource override, library rebuild, application build, replay, name-check rerun or state-changing
git operation was performed.

1. **Prescribed lint only**:
   `/root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-w5a`, exit **0**.
   The wrapper executes:
   `systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh`.
   Exact stdout:

   ```text
   check_lean_modules: PASS (3775 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
   ```

   No stale-root exception was needed. The application qualification is retained literally;
   it does not affect this LP package or the sealed partial-convexity anchor.

2. **Independent axiom probe**, after lint completed:

   ```sh
   systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/LPW5AAudit1.lean
   ```

   Exit **0**. The temporary file imported `KAM.Planetary.StrongAMD.Nek.Drift` and
   `KAM.Planetary.StrongAMD.Confinement` and issued `#print axioms` for **every one of the 59
   new public theorems listed above** (theorem names extracted from the six new modules).
   There were exactly 59 output lines, no diagnostics; each was exactly the following form,
   replacing DECLARATION by the fully qualified name in the declaration table:

   ```text
   'DECLARATION' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   In particular, the exact main-result output was:

   ```text
   'KAM.Planetary.StrongAMD.lp3_kepler_data' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.StrongAMD.exists_nekPerturbation' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.StrongAMD.cell_threshold_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.StrongAMD.isSolutionOn_reverse_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.StrongAMD.cell_drift_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.StrongAMD.kepler_cell_drift' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.StrongAMD.lp_stopped_drift_nek' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.StrongAMD.lp_stopped_drift_nek_hstop' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   Thus there is no sorryAx through the sealed engine. This checks the available compiled
   exports; source statements and bodies were separately inspected. The scratch file was deleted.

3. **Replay, short names and builds**: the user explicitly supplies launcher replay/name checks
   as already run and requests economical reruns only when necessary. They were not rerun here;
   their exact stdout and exit codes were not visible in this auditor's context. The combined
   handoff reports a successful six-module build and short-name check. This report does not
   invent independent replay or build output, or extend its source review to the sealed engine's
   proof internals. Provider/frozen-type and seal-body probes are inapplicable: this package has
   no provider or new frozen anchor. The two frozen-theorem application bodies were checked
   directly against the actual frozen signature and are included in the axiom-checked exports.

4. **Static hygiene**:
   `git diff --check inp...HEAD` exited **0**, empty output.
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` exited **0**, empty output.
   `rg -n 'sorry|admit|axiom|unsafe|opaque|set_option|EuclideanSpace' KAM/Planetary/StrongAMD/Nek`
   returned no matches (exit **1**, expected for no matches).
   A source-import traversal of 249 KAM modules, stopping at frozen theorem boundaries, found
   exactly one frozen theorem boundary, `PartialConvexNekhoroshev.lean`, state **SEALED**;
   forbidden provider edges: **[]**. The sealed anchor's own authorized provider import is
   distinguished from a direct production-module provider import. No LP module imports a
   provider, DRAFT_SORRY anchor, root, or application.

All six modules have copyright, `module`, public imports, module docstrings, and exposed public
noncomputable sections. Sizes (total lines, stronger than code-line cap): Kepler 253, Cover 329,
Perturbation 261, Cells 225, Drift/Stopped 184, Drift 189. The only root delta is six generated
imports, reported by the handoff; the auditor did not regenerate it. No heartbeat, recursion,
synthesis override or default-heartbeat elaboration failure was observed in the fresh probe.

### Pins and remaining uncertainty

Reviewed source SHA-256:

| File | SHA-256 |
|---|---|
| `docs/tracks/LP/source/MAIN.md` | `68e9167f04e4a04689ea163c74e02ffcaea657b252726080abdbe37bdba48c1b` |
| `docs/tracks/LP/source/AMENDMENTS.md` | `c887d1e27354a3db7fb8a20d8bf3e33a9ef95ff3173f925ba5ebfab192651881` |
| `docs/tracks/LP/lp3/LP3-PLAN.md` | `1b58b7048fb3de47e1cadfee0e904085551227a28949a564ea2dc13085ab06ba` |
| `docs/tracks/LP/SPEC.md` | `ffd8a2793b9b37ca35e4a626d38d9af3c2f79d5cefa7c36e5e2aa844978dad22` |

Reviewed package SHA-256 (HEAD bytes):

| File under `KAM/Planetary/StrongAMD/Nek/` | SHA-256 |
|---|---|
| `Cells.lean` | `81a7e7583d1d2fc13e6f3f15d9af1923e0b0f761c417183fd174ca5804f6dcda` |
| `Cover.lean` | `38c2944677d735cacf11aa7bbfe5ba80e19ece0c4577fbcb32412d73e1db27b9` |
| `Drift/Stopped.lean` | `a48d428fbe53f1ed4056cfe3fd2603ec535338e6d5c2584f7b14a660ac301df6` |
| `Drift.lean` | `93c28814b32d1184ca2eed25076ed7101f376fe1f2f5dff8ca4e4dc87358bc1a` |
| `Kepler.lean` | `36aa12508203c5da24dec99666539ef20406d118e984eac6464e0cad57d467e4` |
| `Perturbation.lean` | `3385a9f14ed75d24231f84eadd23a132a09517d0cffe2c009209b4e1c4bc131d` |

No suspected defect in MAIN as amended was found. N1 is a package-brief defect, quoted and
explained above; N2 and the collar/quantifier/order adjustments are reported deviations or
scope notes, not new mathematical assumptions. No source text, ledger, statement, production
proof or generated root was repaired by this auditor. Remaining uncertainty is limited to the
launcher checks whose original logs were not available and the explicitly unaudited future
headline assembly. No unpaid package inequality was found.
