# P11A-P8b2 prover handoff (branch inp-p11ap8b2, 9d0f2815; built on inp-p11ap8b (P8b pr-in, landed); offloaded package run by the main orchestrator)


Branch inp-p11ap8b2 (all committed). Base for P8b3: commit 921970b0 (pr-b); later commits add pr-c and
pr-d prep lemmas.

## Files (all new, in KAM/Planetary/Preparation/, no sorry, lines <= 100)
- PreparedOps: partial calculus. `p11PartialVec_single` (via `p11_partial_...`), `p11_partial_eq_iteratedFDeriv`,
  `p11_norm_iteratedFDeriv_le`, `p11_norm_partial_le_iterated`, `p11_iteratedFDeriv_real_slice`,
  `p11_euclid_jet_re_le`, **`p11op_re_le`, `p11dg_re_le`** (the brief's brick: real jet norm of Re of the real slice
  <= sqrt m * n^j * B from complex coordinate partials), `p11_partial_step/congr/add/clm/slice/affine`.
  NB: `p11PartialVec_single` was stated as in the brief and is used in PreparedFreq/p11_pr_b.
- PreparedDev: identities + Cauchy bounds for partials of h = h0+g2 (formula 1 / formula 2 of the spec):
  `p11_dev_J(_bound)`, `p11_dev_rho(_bound)`, `p11_dev_Z_jet`, main-term bounds from conj. 7 (`p11_dev_main_h/omega/Omega`).
- PreparedNum: pure real inequalities. PreparedResc: `p11_dev_resc` (rescaled bound eps^j|d^beta h| <=
  (L if j=0 else eps L) + K(1+c) eps l^Q), plus dev-form lemmas `p11_resc_pure_dev`, `p11_resc_rho_dev`
  (difference from the main term; these are the pr-d j=0 Euclid inputs, committed as-is, pr-d NOT done).
- PreparedFreq: `p11_freq_partial_eq` (d^alpha omega-hat_c = eps^|alpha| d^{alpha+e_c}(h0+g2)), `p11_freq_partial`,
  **`p11_pr_b`** (pr-b).
- PreparedClose: **`p11_pr_c`** (pr-c), `p11CloseFun`, `p11_close_partial`, `p11_close_block1/2`.

## Step -> declaration
- stepP:p11:pr-in: (earlier, PreparedJets).
- stepP:p11:pr-b: `KAM.Planetary.p11_pr_b`: exists K>0, for eps with K(1+c) eps l^Q <= 1 (plus 0<eps, eps*MF<=exp(-1),
  3 pi eps <= pi rz^2/16, 5 eps <= s2, P11FastSpec, P11SlowSpecOf, and hN: Q.N I = (h0+g2)(rescale I)/eps on
  actionNbhd box 1): `p11Bound (actionNbhd box (3/4)) (p11PreparedFreq Q) (2L+1)` and
  `‖fderiv ℂ (p11PreparedFreq Q) I‖ <= 2L+1` there (conjuncts 9, 10 of P11PreparedSpec).
- stepP:p11:pr-c: `KAM.Planetary.p11_pr_c` (needs 1<=n): exists K>0, for cc with K(1+c)<=cc, with hypothesis
  hcheck (= FullSpec conjunct 2, A generic; `p11SlowNormalizedFreq D nu eps J rho` unfolds to the stated formula when
  A := p11SlowData D nu eps), conclusion is EXACTLY the p11JetBound true clause of P11PreparedFullSpec:
  `p11JetBound true mu {J | ‖J-J0‖<s2/4} ((fun J => Q.checkW (append (eps⁻¹•(J-J0)) rho)) - varpi) (cc*eps*l^Q)`.
  Numeric premises are only the eps<=eps3 inequalities above (no theta<=1 needed for pr-c).
- stepP:p11:pr-d: NOT done here (P11A-P8b3).

## Checks
Gate build of PreparedClose (imports all): success. `scripts/lint_sources.sh`: only "KAM.lean out of date"
(generated); module check PASS, frozen guard OK, ABI OK; no long lines.
`#print axioms` of p11_pr_b, p11_pr_c, p11op_re_le, p11dg_re_le: [propext, Classical.choice, Quot.sound].

## Notes / uncertainties
- Design signal (no override used): big single proofs timed out at default heartbeats when P11SlowSpecOf/P11FastSpec
  were in context for linarith/nlinarith/positivity (whnf unfolds the spec); fixed by splitting into small lemmas,
  introducing spec hypotheses after arithmetic, and `linarith only`. Quick-check tip: plain `lake env lean` misses
  autoImplicit errors; use `-DautoImplicit=false -DrelaxedAutoImplicit=false`.
- For pr-d: Euclid j=0 needs P11SecularFullSpec second conjunct plus the dev-form lemmas above; jets j>=1 follow from
  `p11_freq_partial` + `p11op_re_le`; scalar parts from `M_bound`.
- No source defect found. Constants K depend on data (mu, tau, MF, ...), not on eps, c.

ORCHESTRATOR RULINGS: (OVERNIGHT 01:25) P8b2 continues P11A-P8b with steps pr-b and pr-c; (02:35) step pr-d moved to the parallel package P11A-P8b3, so its absence here is NOT a finding. (01:45, recorded as AMEND P-A002 on pr-in) constants in the preparation estimates may depend on n, tau, the fixed data and the derivative orders, fixed before eps. The signed prepared/amount are assembled later by P8e: their absence is not a finding.

AUDIT FOCUS: design docs/tracks/P/design/P11A-LEAN-DESIGN.md (prepared, steps pr-b, pr-c) and the graph records NODE: stepP:p11:pr-b, stepP:p11:pr-c in docs/graph/P/DEPGRAPH.md. Check: (1) pr-b's export states |omega-hat| <= 2L+1 and |D^2 N| <= 1 literally; (2) pr-c's export states the p11JetBound closeness with theta = c3 eps l^Q in EXACTLY the shape of P11PreparedFullSpec's p11JetBound true clause (signatures /root/code/KAM-inp/.drafts/design/P11ASignatures.lean) AND of the premise he of amount_transfer in KAM/Planetary/Preparation/AmountCore.lean (landed), so P8e can feed one into the other without restating; (3) eps-smallness appears only as explicit numeric premises (the eps <= eps3 inequalities), never conclusion-shaped, and no proved dependency's output is taken as a premise; (4) the PreparedOps brick (p11op vs iterated jets, real-slice bounds) is sound. Audit KAM/Planetary/Preparation/PreparedOps.lean, PreparedDev.lean, PreparedNum.lean, PreparedResc.lean, PreparedFreq.lean and PreparedClose.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.

## Round 2 (fix of audit-1 F1)
- Changed only `KAM/Planetary/Preparation/PreparedFreq.lean`: `p11_pr_b` now has a third (last) conjunct
  `∀ I ∈ actionNbhd (p11PreparedBox n) (3/4), ‖fderiv ℂ (p11PreparedFreq Q) I‖ ≤ 1`; the first two conjuncts
  (`|ω̂| ≤ 2L+1`, `‖Dω̂‖ ≤ 2L+1`) are unchanged. The `≤ 1` estimate is proved once as local `hess`; the `2L+1`
  Hessian conjunct is derived from it via `1 ≤ L`. No other file uses `p11_pr_b` (grep of worktree).
- Checks: gate build of `KAM.Planetary.Preparation.PreparedFreq` and `...PreparedClose` (its only importer): success.
  `scripts/lint_sources.sh`: PASS apart from the known generated-root `KAM.lean is out of date` notice.
  `#print axioms KAM.Planetary.p11_pr_b`: [propext, Classical.choice, Quot.sound]. No lines > 100; file 362 lines.
