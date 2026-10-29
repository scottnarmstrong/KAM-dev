# P11A-P8c prover handoff (branch inp-p11ap8c, 41efd537; contains P11A-P8 PreparedData and P7d; offloaded package run by the main orchestrator)


## Files
- NEW `KAM/Planetary/Preparation/AmountCore.lean` (369 lines, module, no sorry, no heartbeat override).
  Imports only `KAM.Planetary.WeakMeasure.ChartScaling` (and through it Stability/Basic). No frozen
  theorem, no provider.

## Exported declarations (new names; short names grepped, no clashes)
- `amount_norm` (stepP:p11:am-norm): `eps^2 * index_def 2 mu w K ≤ index_def 2 mu (diag(1,eps) ∘ w) K`
  for `0<eps≤1`, `w` C^mu on open `V ⊇ K`, K nonempty. Helpers: `p11DiagVec`, `p11dot_diagVec`,
  `p11euclid_sq`, `p11euclid_diagVec_sq`, `p11euclid_diagVec_bounds`, `p11dot_smul_left`,
  `p11maxJet_smul_ge`.
- `amount_dir` (stepP:p11:am-dir): from `stability`; `betaJ ≤ index psi A`, jet bound `L1` of psi,
  closeness `theta` and `2^mu theta(2 L1+theta) ≤ betaJ/2` give `betaJ/2 ≤ index psiE A`.
- `amount_scale` (stepP:p11:am-scale): with `chart_scaling` and the slice lemmas
  (`p11Inl`, `p11_append_eq`, `p11_iteratedFDeriv_slice`, `p11dg_slice_le`, `p11_slice_chart`):
  a lower bound `b` for the n-dim amount of the frozen-rho slice over `J0 + eps R` gives
  `eps^mu * b ≤ p11maxJet mu (p11scalar 2 W c) (append r rho)` for all unit c, r in R.
- `amount_transfer`: combination. `(1/2) eps^(mu+2) betaJ ≤ index_def 2 mu (p11DiagVec eps ∘ W) K`.
  Premises: `W` (= `Q.checkW`) C^mu on an open `U` containing `append r rho` (r∈R, rho∈Rho); varpi C^mu
  on open `Vn ⊇ A := J0+eps•R`; `hb` (jet bound L1 of varpi on A), `he` (prepared (c) closeness theta
  for every frozen rho∈Rho, in the shape of `P11PreparedFullSpec`'s `p11JetBound true` clause),
  `hbeta` (norm-dict amount on A), smallness; `K` with head/tail in R/Rho.
- `index_def_anti` (monotone in the set; use `A ⊆ A.K` to get `beta ≤ index varpi A` from the patch's
  `beta ≤ index_def 2 mu varpi K`), `index_def_congr` (germ invariance; to replace `diag∘checkW` by
  `p11PreparedFreqR Q` on `‖y‖ ≤ 5/4`, take `U := ball 0 (5/4)` ⊇ the box).

## P8e assembly notes
`p11PreparedFreqR Q y = Fin.append (checkW head) (eps * checkW tail) = p11DiagVec eps (Q.checkW y)` for
`‖y‖ ≤ 5/4`; box = `p11PreparedBox n = pi univ (Icc (-1/2) (1/2))`, so `R := pi univ Icc`,
`Rho := R`, `A = J0 + eps R`. P8e must supply: smoothness of `checkW` on a ball (from the identification with
`p11SlowNormalizedFreq` = derivative of the analytic `h0+g2`), `A ⊆ A.K` and `A ⊆ Vn` for small eps
(J0 ∈ int K_J), `hb` (L1) and `hbeta` (norm-dict), `eps ≤ 1`, and the smallness of theta_eps.

## Checks
- Gate build `KAM.Planetary.Preparation.AmountCore`: success, no warnings in this file.
- `scripts/lint_sources.sh`: only "KAM.lean is out of date" (expected); module check, frozen guard, ABI PASS;
  no over-100-column lines remain in AmountCore.
- `#print axioms` of `amount_norm`, `amount_dir`, `amount_scale`, `amount_transfer`, `index_def_congr`,
  `index_def_anti`: `[propext, Classical.choice, Quot.sound]`.

## Uncertainties / errata / deviations
- No source defect found. Helpers carry the smoothness hypotheses (`ContDiffOn`) that the source leaves
  implicit (index_def uses `iteratedFDeriv`, junk off smooth points); the statement of `amount_transfer` is a
  distinct conditional helper, not the signed `amount`.
- `ρ'`-smoothness of `checkW` is only needed on the box neighbourhood; it is a premise, not proved here.

ORCHESTRATOR RULING (OVERNIGHT 01:05): P11A-P8 split into P8a (pr-basic, pr-a), P8b (pr-in, pr-b, pr-c, pr-d), P8c (amount: am-norm, am-dir, am-scale, PARAMETRIC in prepared's conclusions) and P8e (assembly of the signed prepared and amount). The signed amount itself is NOT a finding here; parametric hypotheses (e.g. rho'-smoothness of checkW, the prepared closeness clause) are legitimate if they have exactly the shapes P8e can discharge from P8a/P8b.

AUDIT FOCUS: design docs/tracks/P/design/P11A-LEAN-DESIGN.md (amount and steps am-norm, am-dir, am-scale) and the graph records NODE: stepP:p11:am-norm / am-dir / am-scale / bpP:p11:amount in docs/graph/P/DEPGRAPH.md; signatures /root/code/KAM-inp/.drafts/design/P11ASignatures.lean (amount, P11PreparedFullSpec, p11JetBound). Check amount_norm, amount_dir, amount_scale state the literal step conclusions (eps^2 factor; beta_J/2 via stability; eps^mu-bar scaling) and amount_transfer gives (1/2) eps^(mu-bar+2) beta_J; the hypotheses match P11PreparedFullSpec's clauses so P8e can instantiate them; no hidden premise. Audit ONLY KAM/Planetary/Preparation/AmountCore.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
Orchestrator note: helper p11euclid_sq renamed p11euclid_sq_sum (clash with a different p11euclid_sq in WeakMeasure/BallSublevel).
