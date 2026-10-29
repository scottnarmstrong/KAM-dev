# GAP-I1b prover handoff (branch inp-gi1b, 3bbffc16; built on GAP-I1a (SettingSrc, landed); track I graph-gap programme package run by the main orchestrator)


## Files (new, append-only; no landed file edited; KAM.lean/README/Frozen/manifest untouched)
- `KAM/Iso/Linear/FullRangeStepsExt.lean` (267 lines): eb-*, lr-*
- `KAM/Iso/Linear/FullRangeStepsEnergy.lean` (194): ea-*, ec-*
- `KAM/Iso/Linear/FullRangeStepsFrame.lean` (186): rd-*, geo-*
- `KAM/Iso/Linear/FullRangeStepsPert.lean` (186): pt-*
- `KAM/Iso/Linear/FullRangeSteps.lean`: facade (imports the four)

All 29 nodes were NOT_STARTED in docs/graph/I/DEPGRAPH.md on this branch (none PROVED/BYPASSED), so none skipped.
Every export is stated under `SettingSrc` (tau >= 0), with the step's own hypotheses; none takes a proved
dependency's output as a premise (parents `*_src`, `extended_regular`, `energy_conservation_src`, ... are used
inside proofs). All namespace `KAM.Iso.Linear`.

## Node -> declaration
| node | declaration | note |
|---|---|---|
| eb-holo | step_eb_holo (Ext) | needs only hK, K(T_r)⊆D, det G unit (no primary/real) |
| eb-holo-inverse | step_eb_holo_inverse | B, N, P holomorphic; only hK, hG |
| eb-holo-field | step_eb_holo_field | A=DX_H∘K, DH∘K |
| eb-holo-torsion | step_eb_holo_torsion | X_N,T,E_sym,Q,eta,Y + T_H = bordMat T ω Y |
| eb-holo-conclude | step_eb_holo_conclude | same conclusion as eb-holo (as source) |
| eb-period | step_eb_period | needs hKp, hKr (periodicity/realness); DH periodic along K and real at real points |
| eb-average | step_eb_average | needs hKp, hKr (realness) |
| eb-bounds | step_eb_bounds | ∑|Y_b| ≤ (∑_s|DH e_s|)‖N‖ ≤ Mσ'σ'; ‖T_H‖ ≤ max(CT+‖ω‖, ∑|Y_b|) |
| lr-gradient | step_lr_gradient | DH row = Ω0 *ᵥ X_H = -(X_H ᵥ* Ω0), any z (no setting needed) |
| lr-average | step_lr_average | (b) Y=ω, T_H, avg when E=0; (c) avg T_H = T^inv - bordMat 0 0 ⟨ηL⟩ and 2n²σσe bound |
| ea-chain | step_ea_chain | plus integrability of H∘K on the cube |
| ea-gradient | step_ea_gradient | LᵀΩ0E = (D(H∘K))ᵀ - Ω_K ω; ηN = LᵀΩ0E |
| ea-avg | step_ea_avg | |
| ea-size | step_ea_size | |
| ea-defect | step_ea_defect | identities, avg split, ηω consequence, bound n(Aη+‖ω‖AΩ)X |
| ec-derivative | step_ec_derivative | |
| ec-unique | step_ec_unique | uses landed `energy_conservation_src` inside the proof (conclusion = its (a)) |
| ec-pointwise | step_ec_pointwise | incl. `sSup` over T_r equals ‖Ē-E0‖ |
| rd-expand | step_rd_expand | stated with Δω = -ξω•ω literally (Q(AΔK-∂ΔK-DKΔω)+QE = ...) |
| rd-consequence | step_rd_consequence | incl. NEW Neumann clause ‖E_sym‖<1 ⇒ IsUnit det P ∧ IsUnit det Q |
| geo-de | step_geo_de | + E holomorphic, ‖E‖≤ε |
| geo-red | step_geo_red | |
| geo-red-domega | step_geo_red_domega | both forms of the constant |
| geo-red-ered | step_geo_red_ered | C_red = 2n(n+1)m² |
| geo-sym | step_geo_sym | ‖E_sym‖ ≤ m²‖Ω_K‖ on T_r |
| pt-small | step_pt_small | C_DT ≥ max{n,C_G,C_DN} and the 4 smallness bounds |
| pt-domain | step_pt_domain | ball(K̃,β-d) ⊆ ball(K,β) ⊆ D; ‖Ã-A‖ ≤ Md ≤ md |
| pt-frame | step_pt_frame | L̃, L̃ᵀ, G̃, B̃ bounds |
| pt-torsion | step_pt_torsion | N, X_N, T differences |

## Approach
Projections/bundles of the landed `*_src` parents and track K helpers; new mathematics only in:
eb-bounds (row-sum chain, ~25 lines), rd-consequence (Neumann: det(PᵀΩ0P)=det Ω0·det(1-Ω0E_sym) unit ⇒ det P unit, uses
`isUnit_det_one_sub`; ~15 lines), pt-small/frame/torsion (sigma-free constants via `mSize_max_one`/`max σ 1`).
The pt-frame bound |L̃|≤2m and |L̃ᵀ|≤4nm are assembled from `frame_items`, `norm_transpose_tangentMat_le_four`.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-gi1b KAM.Iso.Linear.FullRangeSteps`: Build completed successfully (3210 jobs), no warnings in my files.
- `sh scripts/lint_sources.sh`: only message is `KAM.lean is out of date; run scripts/gen_root_imports.py`
  (expected: new modules not yet in root; I did not edit KAM.lean); module check PASS, frozen guard OK, ABI OK.
  No line >100, no set_option, all files <270 lines.
- `#print axioms` of all 29 `step_*`: only propext, Classical.choice, Quot.sound.
- No sorry/axiom/EuclideanSpace/maxHeartbeats.

## Deviations / uncertainties (for the orchestrator)
- Extra hypotheses vs. the DG "setting; det G": eb-period, eb-average, ea-*, ec-* take K primary / real on reals / K(T_r)⊆D —
  these are the standing hypotheses of the parent lemmas (extended-basic, energy-approx); eb-period/eb-average need them for
  periodicity/realness (false without). Steps eb-holo*, eb-bounds, lr-gradient need none.
- lr-average omits the lr-insert content (not in my node list); (a) of last-row is not restated.
- rd-consequence (d) keeps `det P` premise over all of T_{r'}, as the landed parent does (the source says "moreover det P ≠ 0 on T_{r'}").
- eb-bounds states |DH(K)| as the row-sum norm ∑_s|DH(K)e_s| of the 1×2n matrix (the max-norm operator norm of DH equals this).
- ec-unique is derived from `energy_conservation_src` (the parent it supports); DEPS direction is circular in the graph sense
  though not in Lean (parent does not depend on the step export).
- geo-*/pt-*: σ's free (see FullRange docstring), no positivity assumed; pt-small/frame/torsion also take hr : 0 < r (to get d ≥ 0), as the parent.
- No errata found in the pinned sources. No design signals (every file elaborates in ~2-3 s at default heartbeats).
- `KAM.lean` needs regeneration by the orchestrator (`scripts/gen_root_imports.py`).

ORCHESTRATOR RULING (OVERNIGHT 05:10): track I graph-gap programme (/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-I.md, section GAP-I1b): 29 Part-1 step exports stated under the literal SettingSrc (tau >= 0, ruling N1 option (i)). KAM.lean regeneration is the sub-orchestrator's job at merge.

AUDIT FOCUS: for EVERY node in the handoff's node table, read its NODE record in docs/graph/I/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint-I lines it cites; per-node verdict: does the named declaration state the literal conclusion under only the source's hypotheses, quantifiers in source order? Judge explicitly each disclosed deviation: (i) the extra hypotheses K primary / real on reals / K(T_r) subset D on eb-period, eb-average, ea-*, ec-*: are they part of the source's standing setting for these steps (then fine) or added premises? (ii) lr-average omitting lr-insert's content; (iii) rd-consequence (d) keeping det P on all of T_r'; (iv) eb-bounds' row-sum norm reading of |DH(K)|; (v) ec-unique derived from energy_conservation_src (is that a dependency-output premise or a legitimate derivation of a step's literal content?). An export taking a proved dependency's OUTPUT as a premise is a FAIL. List each failing node precisely. Audit KAM/Iso/Linear/FullRangeStepsExt.lean, FullRangeStepsEnergy.lean, FullRangeStepsFrame.lean, FullRangeStepsPert.lean and FullRangeSteps.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
