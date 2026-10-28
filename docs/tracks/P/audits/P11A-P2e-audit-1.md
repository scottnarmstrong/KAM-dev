# P11A-P2e independent package audit 1

Overall verdict: **FAIL for complete delivery of `stepP:p11:hc-mean`**. The conditional Lean results are sound and the mean inequality has the correct shape, but the extra `hΩ` premise is not supplied by the exported P2b/P2c interface. This is an interface/consumption failure, not a refutation of the physical mean estimate.

No frozen anchor is offered for sealing in this slice. `bpP:p11:holo-chart` and its assembly belong to P2f under the explicit overnight ruling and are not findings here. No claim of P-FIXED closure is made.

## Authority, snapshot and scope

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package-audit brief at `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the P2e handoff and AUDIT FOCUS, track P statement, the P11A design/node table, design audits 1–3, the signature file, the hc-mean blueprint and graph record, and the definitions used by the slice. The user's explicit report destination overrides the generic brief's MAIN-worktree destination. Only this report is a persistent audit edit; transient probes/logs reside under this worktree's `.lake/abi-scratch/` and are removed at closeout.

Audited HEAD: `acf60b35713e3a27f676b1019935c27c0cc48fa6`.
Comparison `inp`: `980388b435b56c1a548f7c9771a8f4c62033aba7` at initial inspection.
`git diff inp...HEAD` reports multiple merge bases and selects `b8e023179635e643629844d102983e478c955c1e`; the other merge bases are `02ca2bb08607c4667288cf065902823b66a620cd` and `20c39731675faff719689107c3592dca838fe322`.
The full comparison lists 17 added Lean files, 3523 lines, including inherited P2b/P2c/P2 material. The scoped comparison is six added HoloMean modules, 1041 source lines (1077 diff lines). The handoff was already untracked before the audit. No inherited package is re-audited or repaired here.

Input SHA-256 pins:

| Input | SHA-256 |
|---|---|
| P11A design | `2a76150dbcbee3ca01974d01e2d0ec73a2a0dd1063301bb519b9136a54652d4a` |
| `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` | `627ab032a68be7aca3f547d898c1e82fe8146c18a363a5dd63163916b8d3beee` |
| `blueprint-P/parts/p11-cp09-preparation.tex` | `4c0e2dfefb50b1e06581e069a55846d25e0e4697a8826514ac699bbb83efb41f` |

The graph record at `docs/graph/P/packets/P-p11.nodes.md:450–476` has no FROZEN_FILE/DECL/ANCHOR for hc-mean. Its premises are “hc-F, hc-rot; Part 9 diagonalisation”; its conclusion includes holomorphy, identification, vanishing jets and the quartic bound. The design maps this single step to a local `hc_mean` in Holomorphic (design lines 152, 338); the authorized split moves its proof to these six modules.

## F1 — Extra Omega-realness premise prevents consumption from the supplied data

Locations: `KAM/Planetary/Preparation/HoloMean.lean:259` (`p11_hc_mean`), line 173 (`p11_mean_real_bound`), and line 143 (`p11_mean_Omega_real`).

The added premise is:

```lean
hΩ : ∀ J : P11Vec n, ‖J - d.J0‖ < 2 * d.rC →
  ∀ i, (d.Omega (KAM.realInclusion n J) i).im = 0
```

The source node and signed mean clause do not assume this separately. `P11HoloData.freq` (`HoloData.lean:80–85`) states only the `.re` values; `Omega_diff`, `jets` and `euclid_le` provide holomorphy and bounds, not imaginary-part identification. `P11HsHyp` mentions the rotation family and strip geometry, not Omega. The name `p11_mean_Omega_real` does not supply hΩ: its own type assumes realness and then identifies the full coefficient with `2*sigma`.

`p11_holo_data` (`HoloData.lean:135`) exports only `Nonempty (P11HoloData D)`. Its proof internally constructs `Omega := (2π) • G`, where the complexification has real values on the real slice (lines 168–169, 222). That construction makes a strengthened existence theorem plausible, but its equality/realness evidence does not escape the proposition `Nonempty`. Choosing a witness of that exported proposition does not give additional properties of the internal witness. There is no exported strengthened existence theorem or Omega-realness lemma in the supplied P2b/P2c modules. The handoff itself says P2b/P2f “should add Omega_real as a field/lemma”; that is outstanding proof/interface work, not a current producer-to-consumer composition.

Refutation: knowledge of the real part does not fix a complex value. The audit probe proves `(a + I).re = a` and `(a + I).im ≠ 0`. At the analytic level, adding a nonzero constant imaginary vector to Omega preserves holomorphy and all specified real-part values; finite size bounds can be enlarged by choosing a larger L, without changing the physical integrand. Along a real coordinate direction the resulting mean remainder acquires a nonzero imaginary quadratic term. No finite quartic bound can absorb that term as the coordinate tends to zero. This is a mathematical countermodel argument for the missing interface property; a full modified P11HoloData record was not kernel-constructed by this audit.

The handoff's phrase “typing datum” is inaccurate for this interface: imaginary-part vanishing is a mathematical property that excludes admissible complex-valued functions, rather than a carrier-formation condition. It is not conclusion-shaped, but it is EXCESS for the claimed source-node delivery unless supplied by an exported producer. The allowed parametric split permits P11HoloData/P11HsHyp; it does not expressly approve this additional unproduced assumption.

Required closeout: expose a proved producer of the SAME data together with hΩ (for example, a strengthened P2b existence result retaining the real-complexification equality), and compile its composition with `p11_hc_mean`, or otherwise prove the literal mean clause from the authorized exported data. Merely adding an assumed field, or passing hΩ onward to P2f, does not close F1. No source or signature repair was made during this audit.

## Statement, constants and proof review

Apart from F1 the final inequality is exactly the mean clause with `C J := p11FastMean F J 0`, `F := p11hsF (p11PhysicalData D) d.rho`, `MF := M`, the action ball of radius `2*d.rC`, all complex phase vectors of norm `< rz`, the quadratic coefficient `Omega/2`, and exponent four. The constant `p11MeanM0 = 2*MInf + n*(2π*L)*rz^2` depends on the selected physical/analytic data and rz, before the universally quantified J,z. It has no epsilon dependence. Choosing MF at least this constant, the previous weighted/sup constant, and 1 is a scalar enlargement, with no additional analytic argument.

The proof checks the period conversion J/(2π), angle conversion 2πθ, and normalized unit-cube versus 2π-cell average. Real identification uses the inverse canonical lift, including its angle shift. The real quartic estimate is obtained from `SecularSpectrum.diagonalize` (d), with `D.n_ge` supplying its dimension premise. Joint holomorphy is proved by compact parametric integration. Real line bounds force low scalar derivatives to vanish; identity on the real slice extends the diagonal jets first in phase directions and then in J. A general finite-dimensional radial Schwarz helper yields the complex quartic bound. No uniform real Taylor constant in J is assumed: the identity argument legitimately uses local constants separately for each real J.

The diagonal jet formulation is sufficient for every radial restriction and the final mean-clause consumer. It avoids an unnecessary full-tensor polarization bridge. `p11_radial_schwarz_diag` has its own distinct name; it does not replace or alter the signed `p11_radial_schwarz`. Its missing explicit `0 ≤ M` premise is a strengthening: the pointwise bound at 0 already forces nonnegativity. No Euclidean/Pi norm identification is used.

The files contain no declaration whose name is a signed declaration from P11ASignatures. The inherited signed radial helper was nevertheless checked at its exact signature in a transient Lean example. The main result was checked by a transient copy of its full statement applied to its export. This verifies the conditional type only; it is not a successful producer-to-consumer witness discharging hΩ.

## Declaration ledger

All names below are in `KAM.Planetary`; paths are under `KAM/Planetary/Preparation/`. PASS is scoped helper fidelity/soundness, not frozen-theorem sealing. CONDITIONAL entries fail complete source-node delivery through F1.

| Node/component | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| hc-mean | `p11_mean_L_norm` (HoloMean.lean:47) | PASS | Correct J/(2π) max-norm conversion. |
| hc-mean | `p11_mean_L_t2` (HoloMean.lean:56) | PASS | Derives required real frame radius from rC_le_t2. |
| hc-mean | `p11_mean_real_value` (HoloMean.lean:63) | PASS | Exact physical matched average and period conversion; also proves real-valuedness by equality to a real cast. |
| hc-mean | `p11_mean_Omega_real` (HoloMean.lean:141) | CONDITIONAL / F1 | Assumes hΩ; full Omega=2*sigma identification is conditional (F1). |
| hc-mean | `p11_mean_real_bound` (HoloMean.lean:170) | CONDITIONAL / F1 | Local quartic real remainder follows from diagonalize, conditional on hΩ (F1). |
| hc-mean | `p11_Omega_norm_le` (HoloMean.lean:239) | PASS | Zeroth jet gives 2πL bound on each Omega coordinate. |
| hc-mean | `p11_hc_mean` (HoloMean.lean:256) | CONDITIONAL / F1 | Exact mean-clause inequality, but unproduced extra hΩ prevents complete node delivery (F1). |
| hc-mean | `p11_torusAverage_eq_avg` (HoloMeanAvg.lean:29) | PASS | Exact normalized change of variables, including nonintegrable total-integral convention. |
| hc-mean | `isOpen_p11WorkingDom` (HoloMeanHolo.lean:31) | PASS | Continuous coordinate projections and strict inequalities. |
| hc-mean | `isOpen_p11MeanDom` (HoloMeanHolo.lean:48) | PASS | Open product of action and phase balls. |
| hc-mean | `p11MeanLin_apply` (HoloMeanHolo.lean:66) | PASS | Literal defining equation. |
| hc-mean | `p11MeanPt_eq` (HoloMeanHolo.lean:73) | PASS | Affine decomposition used for parameter holomorphy. |
| hc-mean | `p11MeanPt_mem` (HoloMeanHolo.lean:79) | PASS | Real angles in positive strip; all product-ball restrictions preserved. |
| hc-mean | `continuous_p11MeanPt` (HoloMeanHolo.lean:92) | PASS | Coordinatewise continuity. |
| hc-mean | `p11_fastMean_differentiableOn` (HoloMeanHolo.lean:98) | PASS | Joint holomorphy on the whole mean domain. |
| hc-mean | `p11Split_apply` (HoloMeanJets.lean:42) | PASS | Literal defining equation. |
| hc-mean | `p11_phase_real_slice` (HoloMeanJets.lean:46) | PASS | Identity from real slice with explicit positive radius. |
| hc-mean | `p11_jet_slice` (HoloMeanJets.lean:77) | PASS | Correct partial-jet identification on directions (0,v), including order zero. |
| hc-mean | `p11_jets_zero_real` (HoloMeanJets.lean:97) | PASS | Real line O(norm^k) estimate implies diagonal jets vanish. |
| hc-mean | `p11_jets_zero_gen` (HoloMeanJets.lean:157) | PASS | Identity in J extends diagonal jet vanishing to every complex J in ball. |
| hc-mean | `p11hsInput_real` (HoloMeanReal.lean:37) | PASS | Exact inverse-lift input equality; derivative/extension premises are appropriate generic bridge inputs. |
| hc-mean | `assemble_fast_slow` (HoloMeanReal.lean:105) | PASS | Literal append/projection reconstruction; no duplicated public declaration found. |
| hc-mean | `p11hsF_real_eq` (HoloMeanReal.lean:112) | PASS | Physical perturbation equality on real working domain. |
| hc-mean | `p11_iteratedDeriv_eq_factorial_dslope` (HoloMeanSchwarz.lean:31) | PASS | Correct factorial normalization of iterated dslope. |
| hc-mean | `p11_jets_zero_of_real_bound` (HoloMeanSchwarz.lean:44) | PASS | Real-axis order bound forces holomorphic jets below k to vanish. |
| hc-mean | `p11_radial_schwarz_diag` (HoloMeanSchwarz.lean:107) | PASS | Correct radial-line estimate, all k including zero and z=0. |

Aggregate graph row: `stepP:p11:hc-mean` — **FAIL**, solely for F1; holomorphy/real identification/radial estimate components pass. No other graph node is assigned to this authorized slice. Full multilinear-tensor vanishing is not exported; diagonal vanishing is proved and suffices for the literal mean bound requested by the signed consumer.

## Definition classification

All six definitions are exposed literal constructions. They introduce no instance, fallback, if/default branch, choice, or assumed result bundle. For each row: BODY_MATCH=OK; PUBLIC_CARRIER=OK; WELL_DEFINEDNESS=N/A_LITERAL; CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=PASS.

| Definition | Location | Classification / body |
|---|---|---|
| p11MeanRem | HoloMean.lean:43 | Literal mean minus central mean minus specified quadratic form, on the whole declared function carrier. |
| p11MeanM0 | HoloMean.lean:236 | Explicit real bound constant; positivity is used only under analytic data/positive rz. |
| p11MeanDom | HoloMeanHolo.lean:45 | Strict product-ball set; empty sets for nonpositive radii are the ordinary literal inequalities, never exploited to discharge the main result. |
| p11MeanLin | HoloMeanHolo.lean:56 | Actual continuous complex linear coordinate insertion map, not a norm-changing alias. |
| p11MeanPt | HoloMeanHolo.lean:70 | Literal insertion of real angles, complex actions and phase coordinates. |
| p11Split | HoloMeanJets.lean:36 | Literal complex linear split of Fin(n+n) into the two Fin n coordinate blocks. |

## Binder audit for the main source-facing export

Bins use SOURCE, STANDING, TYPING, RULED, EXCESS. The authorized parametric P2b/P2c split is taken literally; pre-existing physical/data bundles are expanded below, without reclassifying their already audited construction as a new physical assumption. Quantifiers inside fields describe that field's property and do not add independent assumptions. No hΩ property occurs in those expansions.

| Binder | Bin | Evidence |
|---|---|---|
| implicit n | TYPING | Fin n/Pi/phase carriers. |
| D | TYPING | Physical data object; property fields expanded below. |
| d | TYPING | Selected data object; property fields expanded below. |
| implicit a | TYPING | Reference ordered axes vector. |
| ha | SOURCE | axes n = positivity and StrictMono; hc-strip/physical domain. |
| implicit σ | TYPING | Working strip parameter. |
| implicit rz | TYPING | Phase radius. |
| implicit B | TYPING | Rotation bound parameter. |
| implicit B' | TYPING | Rotation derivative bound parameter. |
| implicit r' | TYPING | Input radius parameter. |
| implicit σ' | TYPING | Input strip parameter. |
| h | TYPING | Existing P2c property bundle; fields expanded below. |
| hΩ | EXCESS | HoloMean.lean:259; absent from P2b exported interface and source-node hypotheses (F1). |
| implicit M | TYPING | Freely enlarged mean-bound constant. |
| hM | SOURCE | Explicit enlargement allowed in blueprint L83 and signed mean clause. |

Outer binder counts: SOURCE 2; STANDING 0; TYPING 12; RULED 0; EXCESS 1. The following expansion table replaces the D/d/h object rows for inspection of every stored field. Source references for d are hc-rot/hc-F and signed P11SecularSpec/FullSpec, and the accepted P2b interface; for h they are hc-lift/hc-strip/hc-F and the accepted P2c interface. D's fields are the physical standing assumptions in track P statement.

| Expanded field | Bin | Evidence |
|---|---|---|
| `D.G` | TYPING | KAM/Planetary/Preparation/Working.lean; track P physical premises. |
| `D.m0` | TYPING | KAM/Planetary/Preparation/Working.lean; track P physical premises. |
| `D.m` | TYPING | KAM/Planetary/Preparation/Working.lean; track P physical premises. |
| `D.a` | TYPING | KAM/Planetary/Preparation/Working.lean; track P physical premises. |
| `D.eta` | TYPING | KAM/Planetary/Preparation/Working.lean; track P physical premises. |
| `D.n_ge` | STANDING | KAM/Planetary/Preparation/Working.lean; track P physical premises. |
| `D.G_pos` | STANDING | KAM/Planetary/Preparation/Working.lean; track P physical premises. |
| `D.m0_pos` | STANDING | KAM/Planetary/Preparation/Working.lean; track P physical premises. |
| `D.m_pos` | STANDING | KAM/Planetary/Preparation/Working.lean; track P physical premises. |
| `D.a_pos` | STANDING | KAM/Planetary/Preparation/Working.lean; track P physical premises. |
| `D.ordered` | STANDING | KAM/Planetary/Preparation/Working.lean; track P physical premises. |
| `D.eta_pos` | STANDING | KAM/Planetary/Preparation/Working.lean; track P physical premises. |
| `d.J0` | TYPING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.gamma` | TYPING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.tau` | TYPING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.rC` | TYPING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.L` | TYPING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.Brho` | TYPING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.Bdrho` | TYPING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.h` | TYPING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.omega` | TYPING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.Omega` | TYPING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.rho` | TYPING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.R` | TYPING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.t1` | TYPING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.t2` | TYPING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.t2_pos` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.t2_le` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.R_analytic` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.R_frame` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.rho_diff` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.rho_real` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.rho_orth_t2` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.rC_le_t2` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.nonvanishing` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.freq` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.h_re` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.omega_diff` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.Omega_diff` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.tau_eq` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.h_diff` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.omega_eq` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.jets` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.euclid_le` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.J0_interior` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.gamma_pos` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.gamma_le` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.dio` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.dio_fast` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.dio_slow` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.rC_pos` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.rC_le_one` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.rC_le_delta` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.one_le_L` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.one_le_Brho` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.one_le_Bdrho` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.rho_clause` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `d.rho_bounds` | STANDING | KAM/Planetary/Preparation/HoloData.lean; P2b hc-rot/hc-F interface. |
| `h.rot_diff` | STANDING | KAM/Planetary/Preparation/HoloStripInput.lean; P2c hc-lift/hc-strip/hc-F interface. |
| `h.rot_bound` | STANDING | KAM/Planetary/Preparation/HoloStripInput.lean; P2c hc-lift/hc-strip/hc-F interface. |
| `h.rot_real` | STANDING | KAM/Planetary/Preparation/HoloStripInput.lean; P2c hc-lift/hc-strip/hc-F interface. |
| `h.B_nonneg` | STANDING | KAM/Planetary/Preparation/HoloStripInput.lean; P2c hc-lift/hc-strip/hc-F interface. |
| `h.rC_pos` | STANDING | KAM/Planetary/Preparation/HoloStripInput.lean; P2c hc-lift/hc-strip/hc-F interface. |
| `h.sigma_pos` | STANDING | KAM/Planetary/Preparation/HoloStripInput.lean; P2c hc-lift/hc-strip/hc-F interface. |
| `h.rz_pos` | STANDING | KAM/Planetary/Preparation/HoloStripInput.lean; P2c hc-lift/hc-strip/hc-F interface. |
| `h.center` | STANDING | KAM/Planetary/Preparation/HoloStripInput.lean; P2c hc-lift/hc-strip/hc-F interface. |
| `h.hB_rz` | STANDING | KAM/Planetary/Preparation/HoloStripInput.lean; P2c hc-lift/hc-strip/hc-F interface. |
| `h.hB'_rz` | STANDING | KAM/Planetary/Preparation/HoloStripInput.lean; P2c hc-lift/hc-strip/hc-F interface. |
| `h.sigma_le` | STANDING | KAM/Planetary/Preparation/HoloStripInput.lean; P2c hc-lift/hc-strip/hc-F interface. |
| `h.r'_lt` | STANDING | KAM/Planetary/Preparation/HoloStripInput.lean; P2c hc-lift/hc-strip/hc-F interface. |
| `h.sigma'_pos` | STANDING | KAM/Planetary/Preparation/HoloStripInput.lean; P2c hc-lift/hc-strip/hc-F interface. |
| `h.sigma'_small` | STANDING | KAM/Planetary/Preparation/HoloStripInput.lean; P2c hc-lift/hc-strip/hc-F interface. |
| `h.strip` | STANDING | KAM/Planetary/Preparation/HoloStripInput.lean; P2c hc-lift/hc-strip/hc-F interface. |

Expanded stored-field counts: TYPING 19; STANDING 54; SOURCE 0; RULED 0; EXCESS 0. The separate outer hΩ remains the single EXCESS property. In particular d.freq expands to J in patch, fast real-part equality, and slow real-part equality; d.R_frame expands to patch membership, real action-domain membership, SO, real diagonalisation, sigma identification, and the rotated matrix identity. None identifies the imaginary part of Omega.

## Independent validation receipts

Every audit-owned Lean/Lake/checker command is serialized and uses `LEAN_NUM_THREADS=1` with `nice -n 5`. No clean, update, cache fetch, frozen edit, generated-root regeneration or git mutation was performed. Other sessions on this shared host are outside this audit's process ownership.

Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap2e KAM.Planetary.Preparation.HoloMean
```

Exit 0. Output begins `[inp-gate] slot 2 acquired 22:31:17 for KAM.Planetary.Preparation.HoloMean` and ends `Build completed successfully (9280 jobs).` Replayed dependency warnings concern unused variables, deprecated simp names and style; there was no error or scoped module failure.

Axiom and signature probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP2eAudit.lean
```

Final exit 0, exactly 26 axiom lines below, no errors. The probe imports HoloMean, opens KAM.Planetary/SecularForm/Real, prints axioms for every new public theorem, checks the signed radial Schwarz type by `example ... := p11_radial_schwarz hr hM hF hb hj`, checks a fresh copy of the full p11_hc_mean type with body `p11_hc_mean D d ha h hΩ hM`, and proves the elementary complex-number counterexample described in F1. The first probe attempt exited 1 because the audit scratch file omitted the SecularForm namespace for `axes`; this scratch-only mistake was corrected and the entire probe rerun successfully. No package source was changed.

```text
'KAM.Planetary.p11_mean_L_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_mean_L_t2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_mean_real_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_mean_Omega_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_mean_real_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_Omega_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_hc_mean' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_torusAverage_eq_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_p11WorkingDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_p11MeanDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11MeanLin_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11MeanPt_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11MeanPt_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuous_p11MeanPt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_fastMean_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Split_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_phase_real_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_jet_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_jets_zero_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_jets_zero_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsInput_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.assemble_fast_slow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11hsF_real_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_iteratedDeriv_eq_factorial_dslope' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_jets_zero_of_real_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_radial_schwarz_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Import closure: recursively followed project imports from HoloMean (234 KAM modules). Exactly 59 frozen anchors occur, all definitions with manifest state SEALED; no frozen theorem and no provider occurs. Thus there is no DRAFT_SORRY import or hidden provider consumption in this slice. Exact provider=frozen-type and fresh seal-body probes are **N/A**, because hc-mean has no frozen anchor/provider export. No auxiliary result is substituted for a frozen theorem.

All 26 theorem short names were searched against declarations throughout KAM: no duplicated theorem/def/abbrev/structure name found. All declarations are inside KAM.Planetary; no root declaration, global instance, or harmful shadow is introduced. Raw scoped scans find no sorry/admit/axiom/unsafe/opaque/EuclideanSpace/set_option. Module-system invariants are additionally checked by the lint receipt below.

| Scoped file | Lines | Maximum Unicode line width | SHA-256 |
|---|---:|---:|---|
| HoloMean.lean | 343 | 100 | `3cca11482c56f2cd68e175d8bf863d5182dc40387e8bf7dfd53b59bae62ea6ee` |
| HoloMeanAvg.lean | 66 | 91 | `d10d8889202fc1a04e173b56f3ad43426b56bf72554b6e259ba02afd6edc94eb` |
| HoloMeanHolo.lean | 147 | 100 | `8b6f598b1af44109bac98ebdc98c702c4c7ec72d4fa82edfea1f34b5b2d563e3` |
| HoloMeanJets.lean | 189 | 99 | `49dcee6d9e37895512a9152aa5836edde499d4a136dd62de9ce97d6ce9dd6812` |
| HoloMeanReal.lean | 149 | 96 | `066f892b800d1bfad50f38f12ffabe1bcacdb7a993f91bced8f1e8779d2d93b5` |
| HoloMeanSchwarz.lean | 147 | 96 | `10bd6c1667812d474b22bc6976b58c6f67ccf68910e4e2771261e6985f21809a` |

Kernel replay, one invocation:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.HoloMean KAM.Planetary.Preparation.HoloMeanAvg KAM.Planetary.Preparation.HoloMeanHolo KAM.Planetary.Preparation.HoloMeanJets KAM.Planetary.Preparation.HoloMeanReal KAM.Planetary.Preparation.HoloMeanSchwarz
```

Exit 0. Complete output:

```text
replaying KAM.Planetary.Preparation.HoloMeanSchwarz
replaying KAM.Planetary.Preparation.HoloMeanReal
replaying KAM.Planetary.Preparation.HoloMeanJets
replaying KAM.Planetary.Preparation.HoloMeanHolo
replaying KAM.Planetary.Preparation.HoloMeanAvg
replaying KAM.Planetary.Preparation.HoloMean
```

Source lint (including frozen-file guard and ABI elaboration):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, with complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (998 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The only failure is the explicitly permitted generated-root freshness exception. The module checker, frozen-anchor guard and all 144 ABI hashes pass. Generated KAM.lean was not edited. This hygiene note does not waive F1.

Protected-path comparison:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit 0 with no diff/whitespace output, apart from Git's multiple-merge-base warning. The `inp` ref advanced externally during the audit to `086928650ca9281e65a68123f75f45436881167a`; HEAD remained unchanged. Final comparison was repeated against live inp and retained the same 17-file/3523-line scope and selected merge base. No state-changing Git command was used. The untracked report was also checked with `git diff --no-index --check /dev/null <report>`: no whitespace diagnostics (exit 1 denotes the new-file difference).

## Errata, deviations and limits

No new suspected defect in the pinned mathematical source or frozen declaration was found. F1 is an implementation interface deviation from the source node: the handoff's proposed hΩ obligation remains unpaid. Source locator `blueprint-P/parts/p11-cp09-preparation.tex:83` says the remainder “has vanishing jet to order 3” and derives the quartic Schwarz bound after enlarging MF; it does not add an Omega-realness assumption to physical data. The implementation proves the needed diagonal jet evaluations and avoids full-tensor polarization; this is an acceptable proof route for the mean clause, not a weakened norm or carrier.

P2b/P2c are accepted as previously audited dependencies under the prompt. Their internal constructions were inspected only to evaluate the specific availability of hΩ; this report does not replace their audits. No full P11HoloData countermodel was elaborated. No P2f assembly, holo_chart seal, or physical KAM theorem closure was requested or certified. The remaining work is the concrete hΩ-producing interface and its composition, not further checking of the already validated conditional estimate.

All audit-created probes, diff scratch and output logs were removed after their results were incorporated here. The original untracked handoff remains untouched. The sole new persistent artifact is this report at the user's exact absolute worktree path.
