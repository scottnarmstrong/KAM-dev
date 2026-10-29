# P11A-P8D prover handoff (branch inp-p11ap8d, dc185656; off inp; offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/Preparation/Datum.lean` (~150 lines). Not added to `KAM.lean`
(generated; lint reports it out of date: orchestrator must run `scripts/gen_root_imports.py`).

**Theorem:** `KAM.Planetary.data_star_of_amount (D : P11Physical n) (hamount : ∀ nu, 1 ≤ nu → ∃ epsA c3,
0 < epsA ∧ epsA < 1 ∧ 1 ≤ c3 ∧ ∀ eps, 0 < eps → eps ≤ epsA → let Q := p11PreparedData D nu eps c3;
P11PreparedFullSpec D nu eps c3 Q ∧ (1/2)*eps^(mu+2)*beta ≤ index_def 2 mu (p11PreparedFreqR Q)
(p11PreparedBox n))` concludes exactly the signed `data_star D` statement. `hamount` is verbatim the
conclusion of signed `amount D hnu` (quantified over nu ≥ 1). `data_star` itself is NOT written; when P8e
lands add `theorem data_star D := data_star_of_amount D (fun nu hnu => amount D hnu)`.

**Discharge:**
- IsCompact / volume = 1 / diam = 1 of the box: `p11PreparedBox_isCompact`, `_volume`, `_diam`
  (diam uses `n+n ≥ 1` from `D.n_ge`).
- max inequality: `p11_tau_max_gt` (pure arithmetic). 0<1/4, 0<1/2: norm_num.
- Per nu: take amount's `epsA, c3`; shrink epsA to `min epsA (1/(1+beta_J))`.
  `P11PreparedFullSpec` and `beta ≤ index_def` come directly from `hamount`.
  `0 < beta ≤ min 1 M`: `p11_beta_bounds` (uses `0 < beta_J` from `p11PatchData_spec`, `1 ≤ L` from
  `P11SecularSpec`, eps*beta_J ≤ 1 so beta_eps ≤ 1/2 and M ≥ 2). `1 ≤ p11M0`: `p11_one_le_M0` (from `1 ≤ L`).
- Every clause followed from amount + numerics; no gap. Only shrinking epsA (allowed by ∃ in the goal).

**Checks:** gate build `KAM.Planetary.Preparation.Datum` succeeds, no warnings in the file;
`scripts/lint_sources.sh`: only "KAM.lean is out of date" (generated, not edited); module/frozen/ABI checks PASS;
lines ≤ 100. `#print axioms KAM.Planetary.data_star_of_amount`: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations:** none. New public names (`p11PreparedBox_*`, `p11_tau_max_gt`,
`p11_one_le_L`, `p11_one_le_M0`, `p11_beta_bounds`, `data_star_of_amount`) grep-checked unused in KAM.

ORCHESTRATOR RULING (OVERNIGHT 03:25): parametric form. The signed amount is being proved concurrently by P11A-P8e. This package proves data_star_of_amount whose ONLY non-source hypothesis is exactly the conclusion of the signed amount (for every nu >= 1), and whose conclusion is exactly the signed data_star. The signed data_star itself is added as a one-line application when amount lands; its absence is NOT a finding.

AUDIT FOCUS: (1) the hypothesis hamount is VERBATIM the conclusion of the signed amount D hnu in /root/code/KAM-inp/.drafts/design/P11ASignatures.lean (~1135), quantified over nu >= 1, and nothing else is assumed beyond source data; (2) the conclusion is VERBATIM the signed data_star D (~1282); (3) the numeric/box helper lemmas are sound and the proof does not smuggle a clause through the hypothesis that amount does not give; (4) design row P11A-P8D and node bpP:p11:data-star (design ~412) are covered. Audit ONLY KAM/Planetary/Preparation/Datum.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
