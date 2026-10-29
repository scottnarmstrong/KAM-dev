# GAP-P11a2-cut prover handoff (branch inp-g11cut, 885fd3c2; off inp; graph-gap programme package run by the main orchestrator)


**Files:** new `KAM/Planetary/MaximalStep/CutoffNodes.lean` (~330 lines). Nothing else touched (KAM.lean not regenerated; lint reports it out of date, as expected).

**Approach:** append-only unsigned exports built from landed declarations (`p11_isOpen_actionNbhd`, `p11_cutoff`, `p11_cutoff_coeff`, `cutoff_R0/R1`, `stepF0_diff/stepF1_diff`, `differentiableOn_coeff`, `loss_choice`, `p11_norm_fderiv_le_of_ball`, `p11_taylor_remainder`). `fc_tail` re-proves the private `cutoff_tail` of `FourierCutoff.lean` privately, stopping before `p11_tail_le` so the literal tail sum stays in the conclusion.

## Node -> declaration (all in namespace KAM.Planetary)
| node | declaration | note |
|---|---|---|
| bpP:p11a:c2-conv#data | `p11_c2_conv_data` | iff with the sup-norm thickening, openness, polydisc `ball (realInclusion b') t ⊆ actionNbhd E t`. The optional matrix-operator-norm (max row sum) clause is NOT exported. |
| stepP:p11a:fc-tail | `p11_fc_tail` | `‖F - cut_T F‖ ≤ M * ∑' k, if T < ‖k‖₁ then exp(-(2π d)‖k‖₁) else 0` for θ ∈ T_{r-d}, ‖η‖<s, b ∈ B. Needs only 0<r, 0<d, 0≤M, admissible, bound (no hn, hT, d<r). Scalar-valued. |
| stepP:p11a:tc-a | `p11_tc_a` | `‖p11Taylor F z‖ ≤ M + M‖η‖/s` on D(r,s;B); `‖∂_{η_j}F(θ,0,b)‖ ≤ M/s` for all j. |
| stepP:p11a:tc-b | `p11_tc_b` | inequality chain only (per ruling): `‖F-F^≤1‖ ≤ M(a/s)²/(1-a/s) ≤ M q²/(1-q)`, a=‖η‖<qs. The chain's first step is proved by a limit q'↓a/s of `p11_taylor_remainder` (it needs strict `‖η‖ < q' s`). |
| stepP:p11a:cu-coeff | `p11_cu_coeff` | holomorphy of both coefficient families on B for every k; `R_*0`, `R_*1,i` equal `∑_{k∈hmModes} (if ‖k‖₁≤T then coeff else 0)·χ_k` on B; holomorphic on `univ ×ˢ B` and 1-periodic. |
| stepP:p11a:cu-a | `p11_cu_a` | three bounds (R_*, R_*0, each R_*1,j). |
| bpP:p11a:cutoff | `p11_cutoff_node` (+ def `p11TrigPolyAdm`) | conjunction: identities (R_*0 = cut_T[R(·,0,·)], R_*1,j = cut_T[∂_{η_j}R(·,0,·)], R_* = R_*0+R_*1·η on B); trig polynomials of degree ≤ T admissible on ℂᴺ×B; (a); (b); (c); and for 0<α≤1, T≥1, d = p11Loss n T α, d ≤ 1: `E_T ≤ α` and `‖R-R_*‖ ≤ ε(q²/(1-q)+2α)`. |

**Already closed / not mine:** `stepP:p11a:cu-b` closes by LEAN_REF (clause 3 of `p11_cutoff`, MaximalStep/Cutoff.lean:87-88); DEPGRAPH still shows it NOT_STARTED. No listed node was PROVED/BYPASSED in DEPGRAPH or AMENDMENTS on this branch (none of my 7 nodes appears in AMENDMENTS.md).

**Checks:** `inp_lake_build.sh ... KAM.Planetary.MaximalStep.CutoffNodes`: Build completed successfully, no warnings in my file (no sorry). `scripts/lint_sources.sh`: only "KAM.lean is out of date" (generated; not edited), module check PASS, frozen guard OK, ABI OK; no line >100 cols. `#print axioms` of all seven declarations: `[propext, Classical.choice, Quot.sound]`.

**Candidate source erratum (ruling 02:30):** `p11a2-cutoff-step.tex:124` loss addendum "E_T ≤ α" omits the premises d ≤ 1 and T ≥ 1 (and 0<α≤1); added as premises of `p11_cutoff_node` (as `loss_choice` already requires). Also: `tc-b` source equality `= |Σ_{j≥2} g_j a^j|` is not exported (series coefficients exist only inside a proof).

**Deviations / flags:**
- Scalar vs vector: `fc-tail`, `tc-a`, `tc-b` (and the cutoff exports) are ℂ-valued, as in the landed Lean; the source's ℂ^q-valued form was not exported (componentwise lifting is not short: it needs the vector-valued admissibility framework). Flagged per ruling.
- `fc-tail` `M` plays the role of `‖F‖_r` (sup bound), as in `fourier_cutoff`.
- `cutoff` clause (b)/(a)/(c) are copies of landed `p11_cutoff`/`p11_cu_a` conjuncts; the loss clause adds `d = p11Loss n T α` as premise form.
- `p11_cutoff_node` keeps `0 ≤ eps`, `0 ≤ T` as typing data (source: eps a norm, T ≥ 0).

**Uncertainties:** whether the audit accepts `p11TrigPolyAdm` (a public def with `@[expose]`) bundling "trig polynomial of degree ≤ T admissible on ℂᴺ×B"; the `∃ c` form is satisfied by the Fourier coefficients (`cu_coeff` gives them explicitly). No heartbeat problems.

ORCHESTRATOR RULING (OVERNIGHT 02:30, 02:40): graph-gap programme, second plan (/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P2.md). This package appends UNSIGNED exports stating the LITERAL conclusion of each listed graph node. Package rulings (02:30): the cutoff loss addendum (p11a2-cutoff-step.tex:124) omits the premises d <= 1 and T >= 1 that the proof needs; the package adds exactly those (and 0<alpha<=1 if the source's standing data give it) and records a candidate source erratum (owner to review): check that ONLY those premises were added and that each is genuinely needed. tc-b exports the inequality chain only (its series coefficients exist only inside a proof). cu-b is closed by LEAN_REF elsewhere. KAM.lean regeneration is the sub-orchestrator's job at merge, not a finding.

AUDIT FOCUS: for EVERY node in the handoff's node table, read its NODE record in docs/graph/P/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint lines it cites, and give a per-node verdict: does the named declaration state that node's literal conclusion under only the source's hypotheses (plus any premise a ruling above explicitly allows), with quantifiers in the source's order? An export that takes a proved dependency's OUTPUT as a premise is a FAIL (export from the source hypotheses and build the dependency inside). A node whose export is weaker, conditional on an unsourced premise, or a different statement is a FAIL; list each such node precisely. Audit ONLY KAM/Planetary/MaximalStep/CutoffNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
