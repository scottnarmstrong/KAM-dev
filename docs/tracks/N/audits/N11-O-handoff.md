# N11-O prover handoff (branch inp-n11o, 1366d5f3; offloaded package run by the main orchestrator)


**Files:** new `KAM/Nekhoroshev/Partial/Threshold.lean` (195 lines). No other file touched.

**Declarations:** `KAM.Nekhoroshev.threshold` (signature verbatim from N11Signatures.lean, incl. the
unused `hne`). Helpers (unique `nthr_` prefix, grep-checked): `PartialConstants.nthr_pos`,
`PartialConstants.nthr_K_eq`, `nthr_rpow_le_eventually`, `nthr_exp_eventually`, `nthr_key`
(the statement for an abstract `PartialConstants`, `(k:ℝ)` as parameter).

**Approach:** with `y = μ^(-1/(2n))`: `K μ = cK*y`, `kappa μ = c₁*y`, `d μ = y^(-D/E)`,
`μ^(-T) = y^(T/E)`, `blockTime μ = C0*exp(c₁y/6)/(y^n μ)`. Using `exponents` (T<D, 2D<E) the exponents
D/E<1/2, T/E<1. Each comparison becomes an eventually-in-`y` statement (root
`tendsto_exp_mul_div_rpow_atTop`, `tendsto_rpow_neg_atTop`), pulled back along
`tendsto_rpow_neg_nhdsGT_zero`; `μ0` extracted by `mem_nhdsGT_iff_exists_Ioo_subset`.
Positivity of g, m from `a.definite`; ρ, Mc, n≥2 from `PartialData`. All constants precede μ.
Imports: Constants, Pow.Asymptotics (root names, per audit F4), DerivHyp (for `Real.sinh_pos_iff`).
No `Real.` alias used for the asymptotics.

**Checks:** gate build `KAM.Nekhoroshev.Partial.Threshold`: success (only warning: unused `hne`,
verbatim signature). `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI OK;
the only remark is "KAM.lean is out of date" (generated; not edited, orchestrator regenerates).
Lines ≤100. `#print axioms KAM.Nekhoroshev.threshold`: propext, Classical.choice, Quot.sound.
No set_option, no sorry, no EuclideanSpace.

**Uncertainties / errata / deviations / design signals:** none. Heartbeats default; elaboration ~30–60 s.

AUDIT FOCUS: design docs/tracks/N/design/N11-LEAN-DESIGN.md row N11-O (threshold; all constants fixed before mu; rpow/exp asymptotics) and its node table; both N11 design audits; signatures /root/code/KAM-inp/.drafts/design/N11Signatures.lean. Audit ONLY KAM/Nekhoroshev/Partial/Threshold.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
