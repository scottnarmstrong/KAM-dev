# P11A-P8b prover handoff (branch inp-p11ap8b, 7023f944; contains P11A-P8 PreparedData and P7d; offloaded package run by the main orchestrator)


## Files (committed on inp-p11ap8b; both build; no sorry)
- NEW `KAM/Planetary/Preparation/PreparedCauchy.lean` (137 lines): `p11PolyStep_iterate_bound`,
  `p11PolyRuns_bound`, `p11PartialVec_norm_le_poly` — the polydisc Cauchy estimate of
  `SlowCauchy.p11PartialVec_norm_le` with one radius per coordinate (needed for radii s2/4 in J, eps/4 in rho).
- NEW `KAM/Planetary/Preparation/PreparedJets.lean` (605 lines), helpers parametric in
  `P11SlowSpecOf C Fast nu eps c A` / `P11FastSpec C eps Fast` (apply to `p11SlowData` via `P11SlowSpec`, `rfl`):
  - pr-in (iii): `p11_prin_g2_jet` (sharp), `p11_prin_g2_jet_log`
    (|d_J^a d_rho^g g2| <= c a! g! eps^(3-|g|) l^(5tau+2+(tau+1)|a|), constants explicit; radii s2/4, eps/4).
  - pr-in (ii): `p11_prin_Z_jet` (|d_J^a d_rho Z| <= k a! eps l^(2tau+1+(tau+1)|a|)); supporting
    `p11_prin_K1_le`, `p11_prin_s1_inv`, `p11_prin_alpha1_inv`, `p11_prin_d1_inv`, `p11_prin_eta1_le`
    (eta1 <= k eps l^(2tau+1)).
  - pr-in (i): `p11_prin_G0_jet`: |d_J^b G0hat| <= b! (M_F+eta1)(4/s1)^|b| for `G0hat = p11PolarAverage Fast.G`
    (the object with h0 = C.h + eps*G0hat on V); also the constant-term version `p11_prin_C_bound`,
    `p11_prin_C_diff` (holomorphy of C on D(J0,s2)), `p11_prin_C_jet`, `p11_prin_C_jet_log`; helpers
    `p11_prin_F_bound`, `p11_prin_fastMean_bound`.
- Nothing from KAM.lean/Frozen/manifest touched; no provider/DRAFT_SORRY import.

## Approach
Every bound is the copied-and-generalised polydisc Cauchy estimate applied to the holomorphic data of the
signed spec (conjuncts of `P11SlowSpecOf` / `P11FastSpec` / `P11SecularSpec` projected by `obtain`), with
`s1, s2 >= c l^-(tau+1)` from existing `p11s1_log_lower`/`p11s2_log_lower` (SlowSmall) and `slow_pos`.
Explicit hypotheses beyond the specs are only numeric smallness: `eps*MF <= exp(-1)` (for l >= 1, as in P7),
and where a point must lie in the Z-domain / polar-average disc: `2*pi*eps < pi*rz^2/16` (`p11_prin_C_diff`,
`p11_prin_C_jet*`) and `|rho| < pi (rz/2)^2` (`p11_prin_G0_jet`). These are the "eps <= eps_3" premises, not
conclusion-shaped.

## Not done (pr-b, pr-c, pr-d) and why
They need, beyond pr-in, the translation of the complex coordinate partials (`p11PartialVec`) into the real
operator/diagonal jet norms `p11op`/`p11dg` of `p11PreparedFreqR Q` (with the Euclidean unit-ball sup, the eps
rescaling of the chart `Q.N z.2 = (h0+g2)(p11Rescale ..)/eps`, and `checkW`), plus eventual-in-eps smallness (e4)
statements. Not started: (pr-b) |omega-hat| <= 2L+1, |D^2 N| <= 1; (pr-c) the p11JetBound closeness with
theta = c3 eps l^Q; (pr-d) 2^k M1^2 bound, M*, M0*. Suggested next brick: a lemma
`p11op f j y <= c(n,j) * max_alpha ||d^alpha f||` for holomorphic f restricted to the real slice, and
`p11PartialVec (single j) = fun x => fderiv _ x (single j 1)`; then pr-b is pr-in + the L-bound of
`C.omega, C.Omega` (conjunct 7 of `P11SecularSpec`) + `p11_prin_g2_jet` with `alpha = single`.
Note for the consumers: `P11SlowSpecOf` gives no bound for d_J Z (only d_rho Z); d_J of the eps-part must go
through `p11_prin_G0_jet` (h0 = C.h + eps*G0hat is conjunct 2).

## Checks
- `LEAN_NUM_THREADS=1` gate builds `KAM.Planetary.Preparation.PreparedCauchy` and `...PreparedJets`: success.
- `scripts/lint_sources.sh`: only "KAM.lean is out of date" (generated, not edited); module check PASS,
  frozen guard OK, ABI hashes OK. Lines <= 100 columns; no sorry/maxHeartbeats/EuclideanSpace.
- `#print axioms` of p11_prin_g2_jet_log, p11_prin_Z_jet, p11_prin_C_jet_log, p11_prin_G0_jet,
  p11_prin_eta1_le, p11_prin_C_diff, p11PartialVec_norm_le_poly: [propext, Classical.choice, Quot.sound].

## Uncertainties / errata / deviations
- No signature file entry exists for a PreparedJets module, so statements are mine (distinct `p11_prin_*` names).
- Z-jet statement keeps the spec's form (derivative in rho of `Z (append J rho)`); constant `k` is uniform in alpha
  except through `(4k)^|alpha|`.
- No source defect found. No design signal (all declarations elaborate at default heartbeats).

ORCHESTRATOR RULING (OVERNIGHT 01:25): P8b delivered step pr-in only. Steps pr-b, pr-c, pr-d continue in P11A-P8b2 (branch inp-p11ap8b2, built on this branch); their absence is NOT a finding here. PreparedData.lean is audited separately (P11A-P8 data audit).

AUDIT FOCUS: design docs/tracks/P/design/P11A-LEAN-DESIGN.md (prepared, step pr-in) and the graph record NODE: stepP:p11:pr-in in docs/graph/P/DEPGRAPH.md. Check that the exports together state pr-in's literal conclusion (the Cauchy estimates for G0-hat, Z and g2 with the source's radii, factorials and powers of l and eps), that the extra hypotheses are only numeric eps-smallness (eps*MF <= e^-1, 2 pi eps < pi rz^2/16, |rho| < pi (rz/2)^2) and not conclusion-shaped, and the polydisc Cauchy estimate is sound. Audit ONLY KAM/Planetary/Preparation/PreparedCauchy.lean and KAM/Planetary/Preparation/PreparedJets.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
