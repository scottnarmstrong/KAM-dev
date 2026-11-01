# Independent audit LP-W1B-1

Audit date: 2026-11-01. Auditor marker: `maud-lp-geomod-1`.

Scope: HEAD `d927990e734b4969abc7d41a4d0fcfa1328f9ff9`; `inp` =
`c2cd35af52220132dde03d7f60c450496d879439`; `inp-lp` =
`1600e127690e44f39373a8ea540aa1a2f85f6138`.
Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the independent package-audit brief,
SPEC.md, MAIN.md with AMENDMENTS.md, and all three W1B/prover handoffs.
Compared `git diff inp...HEAD` and audited the exact statements in
`git diff inp-lp...HEAD -- KAM`: six new modules (1,377 lines) and six generated root imports.
LP-THR/LP-MOM and the reused engine/chart implementations are dependencies, not freshly audited packages.
No LP statement is frozen; provider/frozen-type and seal-body probes are inapplicable.

The requested `/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-W1B.md` does not exist.
The combined handoff instead identifies LP-GEOMOD.md and LP-DICT.md; their complete briefs
are present under this checkout's `docs/tracks/LP/packages/` and define the bounded targets used below.
No source or statement was silently repaired.

## LP-GEOMOD — PASS WITH NOTES

G0–G3 and M1–M4 match the package brief and MAIN L5–L6 as amended by N2/N11.
The arbitrary compact U is shared data; no modulus over another set is substituted.
All barrier constants are existentially chosen before the quantified I, e and physical z.
They depend only on fixed dimension, masses, U and m, with no hidden orbit or action dependence.

The compactness helper explicitly uses 1 for an empty compact set, and its finite-index induction
also handles an empty index family. Thus an empty K_m or empty U does not force an illicit minimizer.
Strict eccentricity and gap positivity are proved from the star/pair thresholds and m>0.
Adjacent gaps extend to all pairs using ordered radial endpoints and the Euclidean reverse triangle
inequality. The projection statement is the planar invariable-frame condition: m ≤ |L_i| and
L_i times totalMomentum > 0.

M3 drops the unused physical-state-along-J and initial-L-membership assumptions. This is a valid
strengthening: conservation gives the exact strongAMD difference identity, and the two endpoint
action vectors explicitly belong to U. The continuation corollary still requires physical states
on the relevant tail; it drops only the redundant L label. `movingField` is exactly the Hamiltonian
field of `movingHamiltonian 1 1 nu mu`, and `moving_ode` supplies both C1 regularity and the equivalence
with the moving-solution predicate on `collisionFreeDomain n`. The proof uses this equivalence,
not a substitute ODE. Both forward and backward maximal endpoints are covered.

The modulus is literally sSup of the stated set. In the compact/chamber regime it is bounded.
Every le_csSup application has an actual pair witness, hence a nonempty set. The upper estimates
use Real.sSup_le with a nonnegative bound and work for the empty set. Negative r or empty U gives
an empty set and real sSup = 0; r=0 gives only zero differences (or the empty set). No invalid
conditional-completeness inference is used. Outside the compact/chamber regime no theorem claims
that an unbounded real sSup is a mathematical supremum. The one-sided limit is precisely r down to 0.

G1 note (nonblocking): G3's explicit compact container need only be collision-free; it may include
nonelliptic points. G2 separately proves a uniform negative energy bound for the actual barrier states.
This is exactly the brief's G3 conclusion and suffices for continuation. The N11 floor and its
momentum estimate are supplied separately; G2's momentum bound uses its own positive dS.

| Node | Declaration (namespace KAM.Planetary.StrongAMD) | Verdict | Reason |
|---|---|---|---|
| Geometry | `IsPhysicalState.orbital` | PASS | Unpacks source mass/physical premises. |
| Geometry | `actionAxis_actionVector` | PASS | G0: literal axis bridge on negative-energy, nonzero-position states. |
| Geometry | `exists_pos_forall_le_on_compact` | PASS | Finite family of positive continuous functions; empty compact or index set handled. |
| Geometry | `isCompact_deficitRegion` | PASS | Closed deficit sublevel of compact U × [0,1]^n. |
| Geometry | `eccDeficit_one` | PASS | Literal endpoint D(1)=1. |
| Geometry | `lt_one_of_mem_deficitRegion` | PASS | Star threshold and m>0 exclude radial degeneration. |
| Geometry | `gap_pos_of_mem_deficitRegion` | PASS | Nonpositive gap gives pair feasibility, contradicting the strict deficit margin. |
| Geometry | `exists_deficitBarrier` | PASS | G1: constants precede all I,e; empty K_m explicitly supported. |
| Geometry | `chain_gap` | PASS | Adjacent separation extends to every ordered pair using P_k ≤ A_k. |
| Geometry | `planeLength_le_add_sub` | PASS | Reverse triangle inequality for physical Euclidean length. |
| Geometry | `exists_axis_bound` | PASS | Uniform positive upper axis bound, including empty U. |
| Geometry | `strongBarrier_physical` | PASS | G2: all requested physical bounds and signed MOM projection; constants uniform. |
| Geometry | `continuous_planeLength'` | PASS | Continuity of Euclidean length, not the ambient Pi norm. |
| Geometry | `continuous_bodyVector'` | PASS | Continuous coordinate extraction. |
| Geometry | `barrierCompact_isCompact` | PASS | Closed bounded set in the finite-dimensional Pi carrier. |
| Geometry | `barrierCompact_subset` | PASS | Positive star/pair floors imply literal collision-free membership. |
| Geometry | `exists_barrierCompact` | PASS | G3: one compact collision-free container for all barrier states. |
| Geometry | `perihelionFloor_le` | PASS | N11: explicit floor first, then perihelion, position and momentum bounds. |
| Modulus | `bddAbove_strongThresholdModulus_set` | PASS | Continuity on compact U bounds the literal defining set. |
| Modulus | `strongThresholdModulus_nonneg` | PASS | Valid even for empty or unbounded defining sets under real sSup semantics. |
| Modulus | `abs_strongThreshold_sub_le_modulus` | PASS | Actual pair witnesses membership; boundedness supplies le_csSup. |
| Modulus | `strongThresholdModulus_mono` | PASS | Nested defining sets; Real.sSup_le handles the empty case. |
| Modulus | `bddAbove_strongThresholdModulus` | PASS | Uniform bound for all real radii, including negative radii. |
| Modulus | `tendsto_strongThresholdModulus` | PASS | M1: uniform continuity, epsilon/2 bound, right-hand limit at zero. |
| Modulus | `exists_cthickening_compact` | PASS | M2/N2: positive closed-thickening radius inside the open chamber. |
| Continuation | `strongAMD_le_of_tube` | PASS | M3: exact (17); dropping unused physical and L-membership premises strengthens it. |
| Continuation | `maximal_global_of_barrier` | PASS | M4: actual moving field/domain; both endpoint directions. |
| Continuation | `maximal_global_of_tube` | PASS | M3+M4 with margin delta/2; physical states required on the relevant tail. |

## LP-DICT — PASS WITH NOTES

Part A matches MAIN L7 and the brief: prograde elliptic image, per-planet dictionary,
absolute-momentum AMD, Hamiltonian identity, analyticity, symplecticity, periodicity, and
inverse uniqueness modulo 2pi Z^n. The local inverse statement supplies an analytic inverse on
an open target. The chart is reused, not reconstructed. On circular orbits Gamma=0 the scale is
1/sqrt(I), and the eccentricity vector is zero; no perihelion angle is introduced. Positive chart
actions exclude division by zero, and Gamma<I makes the square-root radicand positive.
The sign identity is literal: xi=x, eta=-y gives (k,l)=(b_e x,-b_e y).
The standard slow form d eta wedge d xi becomes dx wedge dy under this substitution.

For Part B, write G_lambda, G_Lambda, G_xi, G_eta for chart derivatives. The chart field's
four blocks are (G_Lambda,G_eta;-G_lambda,-G_xi). Applying lpRescale gives
(theta-dot,I-dot,q-dot,p-dot) =
(G_Lambda/(2pi),-G_lambda,G_eta/ell,-G_xi/ell).
For Ghat=G(2pi theta,I,ell q,ell p)/(2pi), the engine field with c=2pi/ell^2
has exactly those four blocks. These identities hold componentwise for every Fin n index. The proof splits every concatenated
slot and checks the four inverse basis formulas.
Both fastAction and slowPair agree literally with the engine's Setting.lean definitions.
Time remains physical time. ell!=0 is a harmless strengthening of the positive-scale route;
the actual block has positive ell by the engine's radius/width assumptions.

D1 (nonblocking scope/applicability note): `nonresonant_drift_of_chartData` is explicitly a
conditional helper, not MAIN L13 or L8 closure. ExtNFHyp contains holomorphy, reality,
nonresonance, frequency Lipschitz, scalar size, slow-width, cutoff and Fourier-bound inputs;
it contains no normal-form output or drift conclusion. The helper additionally assumes the chart
lift's domain, projection and chart ODE, a trace identity, and membership in b.realDom b.rB on J.
That membership is outer domain localization and entails an outer action tube; it does NOT assume
the improved rB/2 drift. The stopped slow-membership hypothesis is exactly the engine's allowed
stopped input. hinit is initial data. No AMD, improved drift, or confinement conclusion is assumed.
The chart ODE is supplied as a solution premise, not proved from a bare physical-solution predicate;
`liftPhysicalDeriv` identifies its physical projection. Supplying such a chart lift and the outer
domain locality remains future first-exit/chart-lifting work, expressly recorded in the handoff.
Thus the claimed adapter composition passes; an unconditional physical-orbit theorem is not supplied.

The exact engine field is `realWfield b.c (realHamiltonianExt b b.rB (liftFast h + f))`.
The open-domain germ argument removes the indicator only where the trace identity holds.
The initial slow condition is derived at time zero from hstop. No time, radius or exponential
constant is weakened: the conclusion is rB/2 up to s*rB/(5*epsilon)*exp(2pi*K*s/6).
N6's width selection, analytic-data construction and scalar scale specialization remain outside
this one-centre test, as specified in the brief.

| Node | Declaration (namespace KAM.Planetary.StrongAMD) | Verdict | Reason |
|---|---|---|---|
| PlanarDictionary | `lpChart_image` | PASS | A1: exact prograde elliptic image. |
| PlanarDictionary | `lpChart_action` | PASS | A2: I=Lambda, no rescaling of actions. |
| PlanarDictionary | `lpChart_energy` | PASS | A2: total canonical Kepler energy -nu^3/(2 I^2). |
| PlanarDictionary | `lpChart_momentum` | PASS | A2: individual scalar momentum I-Gamma. |
| PlanarDictionary | `lpChart_eccVector` | PASS | A2: actual eccentricity vector, not a surrogate scalar. |
| PlanarDictionary | `lpChart_eccSq` | PASS | A2: Euclidean squared length 1-(1-Gamma/I)^2. |
| PlanarDictionary | `lpChart_eccentricity_sq` | PASS | A2: same identity for actual eccentricity. |
| PlanarDictionary | `lpChart_eccVector_xy` | PASS | A2: xi=x, eta=-y gives (b_e x,-b_e y), as MAIN. |
| PlanarDictionary | `lpChart_physicalAMD` | PASS | A3: existing signed AMD chart identity. |
| PlanarDictionary | `lpChart_strongAMD` | PASS | A3: absolute-momentum AMD; prograde image discharges sign bridge. |
| PlanarDictionary | `chartAMD_eq_sum_lpGamma` | PASS | A3: literal sum of oscillator actions. |
| PlanarDictionary | `lpChart_hamiltonian` | PASS | A4: exact moving Hamiltonian pullback hProd + mu fMov. |
| PlanarDictionary | `lpChart_symplectic` | PASS | A4: symplectic constant 1; sign change gives MAIN dx wedge dy. |
| PlanarDictionary | `lpChart_analytic` | PASS | A4: real analytic on the entire chart domain, including circular points. |
| PlanarDictionary | `lpChart_isOpen_dom` | PASS | A4: open chart domain. |
| PlanarDictionary | `lpChart_periodic` | PASS | A4: period 2pi lattice; both domain invariance and image invariance. |
| PlanarDictionary | `lpChart_inverse` | PASS | A4: preimage exists and is unique modulo the angle lattice. |
| PlanarDictionary | `lpChart_localDiffeo` | PASS | A4: local analytic inverse on an open target. |
| NonresonantAdapterRescale | `lp_append_addNat` | PASS | B5: Fin slot normalization only. |
| NonresonantAdapterRescale | `lpRescale_apply` | PASS | B5: continuous linear map has the specified coordinate formula. |
| NonresonantAdapterRescale | `lpUnrescale_apply` | PASS | B5: inverse map has the specified coordinate formula. |
| NonresonantAdapterRescale | `lpUnrescale_lpRescale` | PASS | B5: left inverse, ell nonzero explicitly required. |
| NonresonantAdapterRescale | `lpRescale_lpUnrescale` | PASS | B5: right inverse, ell nonzero explicitly required. |
| NonresonantAdapterRescale | `fastAction_lpRescale` | PASS | B5: engine action slot is exactly Lambda for every ell. |
| NonresonantAdapterRescale | `slowPair_lpRescale` | PASS | B5: engine slow slots are (xi/ell,eta/ell). |
| NonresonantAdapterRescale | `smul_slowPair_lpRescale` | PASS | B5: physical slow pair recovered when ell is nonzero. |
| NonresonantAdapterRescale | `lpUnrescale_theta` | PASS | B6: theta basis maps to 2pi times lambda basis. |
| NonresonantAdapterRescale | `lpUnrescale_fast` | PASS | B6: fast action basis unchanged. |
| NonresonantAdapterRescale | `lpUnrescale_q` | PASS | B6: q basis maps to ell times xi basis. |
| NonresonantAdapterRescale | `lpUnrescale_p` | PASS | B6: p basis maps to ell times eta basis. |
| NonresonantAdapterRescale | `lpRescaleHam_hasFDerivAt` | PASS | B6: derivative chain rule with exactly the 1/(2pi) factor. |
| NonresonantAdapterRescale | `lpRescale_field` | PASS | B6: exact field equality; no time rescaling. |
| NonresonantAdapterRescale | `lpRescale_hasDerivAt` | PASS | B6: chart solution carried to weighted engine solution in physical time. |
| NonresonantAdapter | `lpContinuous_extCx` | PASS | B7: continuous real-to-complex inclusion. |
| NonresonantAdapter | `lpRealDom_isOpen` | PASS | B7: real domain open for every block and real R, even empty. |
| NonresonantAdapter | `lpRealWfield_congr_eventuallyEq` | PASS | B7: field depends only on Hamiltonian germ; no derivative hypothesis concealed. |
| NonresonantAdapter | `lpIndicator_field` | PASS | B7: trace equality on open domain removes indicator locally. |
| NonresonantAdapter | `lpBlock_c_eq` | PASS | B7: literal c=2pi/ell^2. |
| NonresonantAdapter | `lpBlock_lam_pos` | PASS | B7: positive block widths give nonzero scaling. |
| NonresonantAdapter | `lpOrbit_hasDerivAt` | PASS | B8: exact N6 field with supplied chart orbit, trace and domain locality. |
| NonresonantAdapter | `lpFastAction_rescale_eq_keplerAction` | PASS | B9: engine actions equal physical Kepler actions on the chart. |
| NonresonantAdapter | `nonresonant_drift_of_chartData` | PASS | B9: conditional engine composition; rB/2 and exponential horizon preserved; see note D1. |

## Definition classification (all 19 new definitions)

All definitions are exposed by the section attribute and use the intended Fin-function carriers.
No new structure or abbrev is introduced. The local tactic macro lp_basis constructs proofs only.

| Definition | Classification and edge cases | Verdict |
|---|---|---|
| IsPhysicalState | Exact nonzero-star-position and negative total Kepler energy predicate; equivalent to negative specific energy for positive masses. Empty planet family vacuous, never used to evade hn. | PASS |
| actionVector | Literal vector of repository Kepler actions. Total inherited arithmetic off the physical region is not used in physical bounds. | PASS |
| DeficitBarrier | Uniform conclusion predicate quantified over all I,e; proved by G1, never an incoming assumption of the exported source results. Empty U/empty feasible region is vacuous. | PASS |
| BarrierState | Source state assumptions: physical, actions in U, initial/current source deficit margin. These are L5/L6 inputs, not an encoded geometry/continuation conclusion. | PASS |
| deficitRegion | Literal K_m on U times [0,1]^n, closed deficit sublevel. May be empty. | PASS |
| barrierCompact | Closed position/momentum/separation box. Not the exact set of elliptic barrier states; intended compact container. Negative bounds can make it empty; compactness theorem uses nonnegative upper bounds. | PASS |
| perihelionFloor | Literal aMin*m^2/(2*Imax^2). Imax=0 totalizes to zero; its consuming theorem derives Imax>0 from its actual planet and positive physical action. | PASS |
| strongThresholdModulus | Literal sSup; empty/negative-radius case is zero. All mathematical-supremum uses have boundedness and a witness when needed. | PASS |
| movingField | Literal moving Hamiltonian vector field, same masses, G=1 and star mass=1. Smoothness used only on the collision-free domain. | PASS |
| lpEccScale | Literal sqrt((1-Gamma/(2I))/I); I=0 gives zero under total division; negative radicands give zero under real sqrt. Dictionary consumes it only at I>0, 0<=Gamma<I. | PASS |
| lpGamma | Literal (xi^2+eta^2)/2 for every real chart point; nonnegative, regular at zero. | PASS |
| lpRescaleFun | Coordinates lambda/(2pi), Lambda, xi/ell, eta/ell. At ell=0 slow information collapses to zero; no inverse/field theorem uses that case. n=0 gives the unique empty-coordinate map. | PASS |
| lpUnrescaleFun | Coordinates 2pi*theta, ell*q, I, ell*p. Inverse only for ell!=0; at zero it is the explicit degenerate linear map. | PASS |
| lpRescaleLin | Linear packaging of the same formula, including the degenerate zero-scale case. | PASS |
| lpUnrescaleLin | Linear packaging of the same inverse formula; no false global invertibility. | PASS |
| lpRescale | Continuous linear packaging in finite dimension; same pointwise function. | PASS |
| lpUnrescale | Continuous linear packaging; same pointwise function. | PASS |
| lpRescaleEquiv | Actual continuous linear equivalence with ell!=0 in its type. | PASS |
| lpRescaleHam | Literal G composed with inverse rescaling and divided by 2pi. Defined for arbitrary G and ell; differentiability and ell!=0 explicitly required in the field conversion. | PASS |

The table contains nine GEOMOD and ten DICT definitions, with no hidden structure fields.

## Validation and hygiene

All Lean/Lake invocations were serialized inside the D53 wrapper:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

1. Required lint, exact command:

```sh
/root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-geomod
```

Exit **0**. Output:

```text
check_lean_modules: PASS (3675 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

2. Targeted builds, exact command (the inspected driver acquires the compile gate and executes
each individual lake build with the exact D53 wrapper above):

```sh
/root/code/KAM-inp/.drafts/LP/lp_build.sh /root/code/KAM-inp-lp-geomod KAM.Planetary.StrongAMD.Continuation KAM.Planetary.StrongAMD.NonresonantAdapter
```

Exit **0**, sequential target completion output:

```text
Build completed successfully (9117 jobs).
Build completed successfully (9233 jobs).
```

These two leaf targets cover all six new modules. Cached dependencies emit existing warnings
(including Kepler.Energy and several Nekhoroshev.Partial/chart modules); no warning was reported
from a new LP module. No full-library build or certificate application was requested.

3. Axioms of **every one of the 70 new public theorems** listed in the tables, exact command:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean .lake/abi-scratch/LPW1BAudit.lean
```

The temporary probe imported Continuation and NonresonantAdapter and issued
`#print axioms KAM.Planetary.StrongAMD.<name>` for every public theorem in the six source files.
Exit **0**. For each of the 69 entries other than lp_append_addNat, the output was exactly
(up to line wrapping and the declaration name):

```text
'KAM.Planetary.StrongAMD.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The remaining output was:

```text
'KAM.Planetary.StrongAMD.lp_append_addNat' depends on axioms: [propext, Quot.sound]
```

This covers G0–G3, N11, every M1–M4 export, every dictionary theorem and the conditional drift
helper, rather than just the handoff's selected main results. The probe was deleted after use.

4. Kernel replay / short-name checks: the task explicitly states that the launcher already ran
these. I did not rerun them; their output and exit codes were not visible to this audit, and no
independently observed leanchecker exit code is asserted here. The combined handoff separately
records the six-module short-name check as OK. This report's independently observed checks are
lint, the targeted builds, the axiom probe and source/import inspection.

5. Static hygiene: all six files have the copyright header, module declaration, public imports,
module docstring, exposed public noncomputable section and intended Fin carriers. Lengths are
Geometry 498, Modulus 120, Continuation 130, PlanarDictionary 219, NonresonantAdapterRescale 246,
NonresonantAdapter 164; each is below 1500. Token inspection found no sorry, admit, axiom,
unsafe, opaque, EuclideanSpace or set_option in the six modules. A recursive KAM-import scan
visited 195 modules and found **no frozen theorem import and no provider import**; in particular
no DRAFT_SORRY theorem or Exponential.Stopped is imported.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Exit **0**, empty output. The only generated-root diff is the six expected imports in
KAM/Root/Planetary.lean; the auditor did not regenerate or edit it.

```sh
git diff --check inp-lp...HEAD -- KAM
```

Exit **2**, sole output:

```text
KAM/Planetary/StrongAMD/PlanarDictionary.lean:24: trailing whitespace.
+is the chart of MAIN Lemma 7 with `(I, λ) = (Λ, λ)` and the slow pair `(ξ, η) = (x, −y)`. 
```

This is a nonblocking formatting note; the required LP lint passed.


## Source defects, deviations and uncertainties

No suspected mathematical defect found in the reviewed portions of MAIN as amended.
MAIN's L5 energy bound -1/(2 a_max) concerns the specific E_i defined in section 1;
Lean's bound -nu_min/(2M) concerns nu_i E_i (`keplerEnergy`), so there is no mass-normalization mismatch.
The dropped M3 hypotheses and ell!=0 generalization are valid strengthenings, not source changes.
The analytic supplier, scale arithmetic, existence of a suitable lifted orbit and first-exit
application are not certified by this scoped audit.

Documentation-only notes: the combined package brief path is absent as recorded above;
LP-DICT-handoff.md lists PlanarDictionary.lean as 231 lines, but the reviewed file has 219.
`git diff --check inp-lp...HEAD -- KAM` reports a trailing space at PlanarDictionary.lean:24.
These do not change a declaration. No repository repair was made.

## Combined verdict — PASS WITH NOTES

LP-GEOMOD and LP-DICT pass their bounded statement/source/definition audits, with the explicit
conditional applicability boundary D1 and the documentation notes above. This is package-diff
acceptance, not a freeze/seal approval or a proof of the LP headline or unconditional MAIN L13.
Only this report was added; the axiom probe was temporary and removed. No state-changing git,
source edits, forbidden resource overrides, or uncapped Lean/Lake command was used.
