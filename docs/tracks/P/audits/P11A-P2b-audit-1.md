# P11A-P2b independent package audit 1

Verdict: **PASS WITH NOTES for the assigned P2b slice** (data selection, real frame/rotation interface, real inverse-lift identification and the two complex bounds). No frozen anchor is offered for sealing by this package. This is not a seal of `holo_chart` or P-FIXED, nor certification of the entire unsplit complex-domain `hc-lift` node.

## Scope and authority

Audited HEAD `20c39731675faff719689107c3592dca838fe322` against `inp` at `4a5b757e944936d0ae6e9269a1170dc7098e4240`, using `git diff inp...HEAD`; merge base `02ee95b6d03dcaf74adaf6b29d46beab4b7cfffb`. The full diff has seven new Lean files, 1450 insertions. The four assigned files have 883 lines:

| File under `KAM/Planetary/Preparation/` | Lines | Longest line |
|---|---:|---:|
| `HoloFrame.lean` | 222 | 100 |
| `HoloScalar.lean` | 189 | 97 |
| `HoloData.lean` | 279 | 99 |
| `HoloLift.lean` | 193 | 98 |

The inherited additions `Holomorphic`, `HolomorphicRotation`, `Polar` belong to the separate P2 audit, as explicitly directed by `P11A-P2b-handoff.md:72–74`. Their interface/import context was read; no independent package verdict on those files is implied. The handoff already existed untracked at audit start. The report is written at the user's exact path inside this worktree, overriding the generic brief's main-worktree destination.

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the supplied package brief, handoff, track P statement, relevant frozen definitions and P-FIXED anchor, P11A design and design audits 1–3, signed specification, and blueprint `p11-cp09-preparation.tex:63–84`. Current input hashes:

- Design `docs/tracks/P/design/P11A-LEAN-DESIGN.md`: `2a76150dbcbee3ca01974d01e2d0ec73a2a0dd1063301bb519b9136a54652d4a`.
- `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`: `627ab032a68be7aca3f547d898c1e82fe8146c18a363a5dd63163916b8d3beee`.

There are no signed declarations among the 25 new named declarations in the assigned files. The imported signed definitions `p11ChartInput`, `P11SecularSpec`, `P11SecularFullSpec` agree with the supplied signature after whitespace normalization. They have not been repaired or replaced. Frozen type-equality and seal-body probes are **not applicable**: no provider export or proposed frozen seal exists in this slice.

## Declaration and node ledger

Names below are in `KAM.Planetary`. Every new public theorem was axiom-checked, including the small generic helpers.

| Node / role | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| hc-rot / positive actions | `p11_pos_of_close` (`HoloFrame:36`) | PASS | Derives positivity from the literal physical delta tube; no extra physical premise. |
| hc-rot / ordered axes | `p11_axis_mem_axes` (`HoloFrame:48`) | PASS | Forward tube at zero phase gives coordinatewise axis distance below zeta; six-zeta gap margin yields strict order. |
| hc-rot / spectrum identification | `p11_sorted_eq_patch` (`HoloFrame:125`) | PASS | Same literal secular matrix via `action_axis`; monotone characteristic-polynomial roots identify the sorted spectrum. Local domain premises are discharged in its caller. |
| hc-rot / real frame | `p11_holo_frame` (`HoloFrame:144`) | PASS | Positive radius, entrywise analytic SO frame of actual coefficients, patch identification and conjugation of actual `p11SecularMatrix`. |
| scalar construction | `p11HoloH` (`HoloScalar:33`) | PASS | Explicit Keplerian energy with the correct period conversion. |
| scalar construction | `p11HoloFreq` (`HoloScalar:37`) | PASS | Explicit gradient in J coordinates; derivative theorem proves identification. |
| domain | `p11NonVanishing` (`HoloScalar:41`) | PASS | Literal complement of coordinate hyperplanes. |
| domain | `isOpen_p11NonVanishing` (`HoloScalar:43`) | PASS | Finite intersection of open coordinate conditions. |
| domain | `exists_ball_nonvanishing` (`HoloScalar:49`) | PASS | Positive coordinate center gives a positive max-norm ball; finite reciprocal sum handles all coordinates. |
| scalar holomorphy | `differentiableOn_p11HoloH` (`HoloScalar:66`) | PASS | Rational expression differentiated only off its poles. |
| scalar holomorphy | `differentiableOn_p11HoloFreq` (`HoloScalar:75`) | PASS | Same nonvanishing domain. |
| scalar gradient | `fderiv_p11HoloH` (`HoloScalar:85`) | PASS | Exact coordinate derivative, positive sign and factor 4 pi squared. |
| real energy | `p11HoloH_re` (`HoloScalar:114`) | PASS | Literal signed Keplerian real-part expression. |
| real frequency | `p11HoloFreq_re` (`HoloScalar:127`) | PASS | Literal fast patch frequency at J/(2 pi), with the extra 1/(2 pi). |
| finite jet and size bounds | `p11_jet_bound_complex` (`HoloScalar:141`) | PASS | Compact smaller closed ball inside a holomorphic open ball; one L >= 1 bounds all orders including zero and explicit Euclidean length. |
| data interface | `P11HoloData` (`HoloData:37`) | PASS | Output structure with exact retained specification clauses and proved construction facts; classified below. |
| holomorphic append helper | `differentiableOn_p11_append` (`HoloData:126`) | PASS | Coordinatewise differentiability, no additional source premise. |
| hc-rot / scalar-data selection | `p11_holo_data` (`HoloData:135`) | PASS | Takes only `P11Physical`; actually constructs all fields. No output certificate assumed. |
| derivative projection helper | `p11_mat_entry_hasFDerivAt` (`HoloLift:33`) | PASS | Two continuous coordinate projections; generic field/spaces do not alter physical carriers. |
| real/complex derivative bridge | `p11_fderiv_rho_real` (`HoloLift:47`) | PASS | Restriction of scalars and uniqueness of derivatives from local agreement; matrix norm scope is local. |
| hc-lift / real formula | `p11ChartInput_eq_liftInv` (`HoloLift:69`) | PASS | Correct T1 angle/action conversion and inverse-lift sign; hypotheses are differentiability and real-slice agreement, supplied by the constructed interface. |
| hc-lift / rotation bound | `p11_mulVec_bound` (`HoloLift:120`) | PASS | Row-sum operator bound for complex max norms, including zero dimension. |
| hc-lift / angle bound | `p11_angle_correction_bound` (`HoloLift:131`) | PASS | Exact factor n and product of max norms; no unjustified complex isometry. |
| hc-lift / interface bounds | `P11HoloData.lift_bounds` (`HoloLift:149`) | PASS | Both complex bounds on the exact rC/pi ball, for arbitrary x,y; applying the rotation bound twice handles x and y. |
| hc-lift / interface identity | `P11HoloData.chartInput_eq_liftInv` (`HoloLift:163`) | PASS | Any secular datum with the same rho; local real-action condition only, with all analytic premises derived from d. |

The interface bounds are stronger than their small-secular-variable specialization: x,y are arbitrary, giving the source bounds after `norm x,norm y < rz`. The constants are chosen from fixed physical data and the selected base point, before any perturbation epsilon. No claim of a complex orthogonal matrix being an isometry occurs.

## Exact specification-field audit

An independent scratch probe extracted the following targets directly from the supplied signed `P11SecularSpec` text, replaced only `C.x` by `d.x`, and elaborated `example (d : P11HoloData D) : <target> := d.<field>`. The paired differentiability conjunct uses `⟨d.omega_diff, d.Omega_diff⟩`. The extra full-spec target was extracted directly from `P11SecularFullSpec`. All examples elaborated without coercive rewriting or extra hypotheses.

| Field(s) | Signed clause | Verdict |
|---|---|---|
| `freq` | Real J in the complex 2rC ball: membership in V, fast and slow frequency real parts | PASS, exact |
| `h_re` | Real-point Kepler energy on norm(J-J0) < 2rC | PASS, exact |
| `omega_diff`, `Omega_diff` | Both complex differentiability clauses on the 2rC ball | PASS, exact components |
| `tau_eq` | max(n * mu, 2n) | PASS, exact |
| `h_diff` | Complex differentiability of h on the same ball | PASS, exact |
| `omega_eq` | Gradient via `fderiv` at `Pi.single i 1` | PASS, exact |
| `jets` | Full complex operator norms, every j <= mu+1, append(omega, (2pi)^-1 Omega) | PASS, exact |
| `J0_interior` | J0 in interior K | PASS, exact |
| `gamma_pos`, `gamma_le`, `dio` | Positive gamma <= 1 and full-vector frozen Diophantine predicate | PASS, exact |
| `rC_pos`, `rC_le_one`, `rC_le_delta` | Positive rC <= 1, rC <= pi * physicalDelta / 8 | PASS, exact |
| `one_le_L`, `one_le_Brho`, `one_le_Bdrho` | Same lower bounds, no larger normalizer substituted | PASS, exact |
| `rho_clause` | Same real action ball; imaginary entries zero, determinant 1, actual Hessian diagonalization | PASS, exact |
| `rho_bounds` | Same complex action ball; holomorphy, transpose orthogonality, row sums and derivative row sums | PASS, exact |
| `euclid_le` | Additional FullSpec Euclidean bound on the same appended vector | PASS, exact |

The handoff's word “every” is understood with its explicit list of additional construction facts: `t2_pos`, `t2_le`, `R_analytic`, `R_frame`, `rho_diff`, `rho_real`, `rho_orth_t2`, `rC_le_t2`, `nonvanishing`, `dio_fast`, `dio_slow` are supplementary output facts, not verbatim conjuncts of SecularSpec/FullSpec. This is a descriptive qualification, not a signature failure. They are all proved by `p11_holo_data`; the two extra Diophantine clauses come from `select`. No output field is silently an input assumption of the existence theorem.

The construction uses `select`, obtains the literal real eigenframe, complexifies it, chooses compactness bounds and shrinks rC simultaneously to fit V, the nonvanishing region and the analytic slow-frequency extension. In particular, `2*rC < r0`, `rC <= pi*t2/2` and `rC <= pi*physicalDelta/8` are proved, not assumed. The same L controls the required jets and Euclidean size.

## Definition classification and consumer checks

- `p11HoloH`: genuine rational Kepler energy on its intended domain; total Lean division assigns values at poles, but every analytic/gradient use is guarded by `p11NonVanishing`. No proof relies on the pole values.
- `p11HoloFreq`: genuine rational gradient, with the same guarded treatment of poles.
- `p11NonVanishing`: exact intended open set on the whole carrier, no fallback.
- `P11HoloData`: stage output certificate with 14 data fields and additional proof fields. It does not redefine frozen physical data, spectrum, Hessian, phase, Hamiltonian or Diophantine predicate. Its unconditional existence from D prevents circular use of its Prop fields as unproved source assumptions.

Downstream assembly can copy J0/gamma/tau/rC/L/Brho/Bdrho/h/omega/Omega/rho directly and use the exact fields above without weakening the signed specification. For the real chart, entrywise analyticity combines via `analyticAt_pi_iff` in the local elementwise matrix norm scope. The exported lift identity then applies on the real action region, with T1 preserving position/momentum order: positions (theta,x), momenta (J,y), converted fast angle 2pi*theta and action J/(2pi). The derivative bridge uses local real equality, not merely equality at one point.

Boundary of this verdict: the original design table maps all hc steps to `Preparation/Holomorphic` (`P11A-LEAN-DESIGN.md:145–152`); the later split ruling controls this audit. `hc-rot`'s real frame, complex orthogonality/reality and bounds are established through this interface, using the separately owned rotation construction. For `hc-lift`, this report certifies exactly the handoff focus at line 74: real inverse-lift identification and the two bounds. The unsplit registry at design line 328 and blueprint line 76 additionally say “holds on the complex domain with H_rho holomorphic”, and involve rz and the strip width. This package exports no named complex lift/holomorphy theorem and no rz choice. Those claims must be checked in the later complex composition/strip assembly before marking the entire original graph node complete. They are not inferred from the real identity or from this scoped PASS. The explicitly excluded F/strip, chart/lattice, mean and `holo_chart` assembly are not findings against P2b.

## Independent verification

All audit-owned Lean/Lake/checker invocations were sequential and used `LEAN_NUM_THREADS=1` and `nice -n 5`. No clean, update, cache fetch, root generation, git mutation or production-source edit was performed.

### Targeted build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap2b KAM.Planetary.Preparation.HoloFrame KAM.Planetary.Preparation.HoloScalar KAM.Planetary.Preparation.HoloData KAM.Planetary.Preparation.HoloLift
```

Exit **0**. Gate output: `[inp-gate] slot 2 acquired 21:43:22 ...`. Final output: `Build completed successfully (9269 jobs).` Replayed dependencies emit existing unused-variable/simp/deprecation warnings; no warning is from the four assigned files. Waiting for the gate was not treated as failure.

### Field probe and all public theorem axioms

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11P2bAudit.lean
```

Exit **0**. The 19 selected SecularSpec conjunct targets (including paired differentiability), one FullSpec target and direct application of `p11_holo_data` all elaborate. The 21 `#print axioms` outputs are reproduced below; no `sorryAx` or custom axiom appears.

```text
'KAM.Planetary.p11_pos_of_close' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_axis_mem_axes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_sorted_eq_patch' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_holo_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_p11NonVanishing' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exists_ball_nonvanishing' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiableOn_p11HoloH' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiableOn_p11HoloFreq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_p11HoloH' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11HoloH_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11HoloFreq_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_jet_bound_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiableOn_p11_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_holo_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_mat_entry_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_fderiv_rho_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11ChartInput_eq_liftInv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_mulVec_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_angle_correction_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.lift_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.chartInput_eq_liftInv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.HoloFrame KAM.Planetary.Preparation.HoloScalar KAM.Planetary.Preparation.HoloData KAM.Planetary.Preparation.HoloLift
```

Exit **0**. Exact output:

```text
replaying KAM.Planetary.Preparation.HoloLift
replaying KAM.Planetary.Preparation.HoloData
replaying KAM.Planetary.Preparation.HoloScalar
replaying KAM.Planetary.Preparation.HoloFrame
```

### Lint and source/import integrity

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, with exactly the permitted generated-root exception and no other failure:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (947 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This is a qualified lint pass under the supplied audit brief, not a claim that the raw lint command exited zero. `KAM.lean` was not regenerated.

Direct scans of the four source files find no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or `set_option`. Every file has copyright, `module`, public imports, module docstring and an exposed public noncomputable section. All are below 1500 lines and every line is at most 100 characters. All 25 declaration names were checked against KAM source declarations: no reused public helper short name and no root declaration/shadow introduced.

Recursive KAM import closure: **223 modules**, **59 frozen definition files**, **zero provider modules**, **zero frozen theorem modules**. Every exact-path matching frozen anchor is manifest `SEALED`; no DRAFT_SORRY anchor is imported. This check matched manifest `path` exactly, rather than searching mentions in dependency metadata.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check
```

Both exit **0**, with empty output. The protected paths are unchanged across the full three-dot diff.

## Errata, deviations and closeout

No new suspected defect in a pinned mathematical source or false blueprint assertion was found. The patch interface limitation is real but locally resolved: signed `P11PatchSpec` states the spectral and closeness properties without a general ordered-action-domain clause for V. `HoloFrame:48–122` proves the needed ordered axes on the physical close tube; `HoloFrame:164–203` then restricts to the open actual action domain. This does not strengthen the signed patch specification or assume a missing source theorem.

The sole scope qualification is the real-versus-full-complex hc-lift distinction documented above. There is no new frozen/signature deviation. Existing P11A design-audit source gaps outside this slice remain outside this verdict. The only permitted lint exception is the generated-root staleness explicitly allowed by the brief. An isolated generated-root exception does not excuse any other lint failure.

Final integrity: `git diff --check` passes; the report passes an explicit trailing-whitespace and balanced-fence check. The initial handoff remains unchanged, and the only new persistent repository artifact from this audit is this report. All audit-owned probe/source/log scratch files were removed after copying the verification output here. No tracked production file changed. No state-changing git command was used.
