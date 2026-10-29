# B18 prover handoff (branch inp-p11b-b18, 1f061eb1; contains B17 (passed), B16; offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/WeakKAM/ParameterLipschitz.lean` (~265 lines). Nothing else changed.

**Declarations (signatures verbatim):** `collar_increment_lipschitz` (graph step lf-stage supplier),
`SelectionLipschitz`, `lipschitz_family` (graph nodes lf-split, lf-tel, lf-stage, lf-sum).
Helpers (unique names): `collar_real_sub`, `lipFam_t_succ_le`, `lipFam_stage`,
`lipFam_alpha_nonneg`, `lipFam_limit`.

**Approach:** collar lemma: long case (|b-b'| >= t/2) by the sup bound 2e; short case by
`KAM.norm_fderiv_le_of_closedBall` on the max-norm polydisc radius t/2 (op-norm <= 2e/t, no factor N)
along the real segment, then the real mean-value inequality (constant 2e/t <= 4e/t).
Family: for fixed real theta, stage increment g_j(beta)=C_{j+1}-C_j is holomorphic on the collar of
Kinf with bound (1+2^-11)max(A_j,alpha_j) (composition_holo/composition_increment, Kinf ⊆ K_j,
t_{j+1} <= t_j); stage lemma gives 4 B_j/t_{j+1}; partial sums are bounded via `param_lip_sum`
(<= 2^-10/16), pass to the limit with `limit_uniform` (pointwise at real theta), giving 2^-11|b-b'|;
add `angle_lipschitz` for the theta part; joint field from max-norm.

**Checks:** gate build `KAM.Planetary.WeakKAM.ParameterLipschitz` succeeds, no warnings in the file
(no sorry). `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI hashes OK, no
over-100-column lines; only message is "KAM.lean is out of date" (generated, not edited per rules).
`#print axioms` of `collar_increment_lipschitz` and `lipschitz_family`: propext, Classical.choice,
Quot.sound.

**Uncertainties / errata / deviations / design signals:** none. No heartbeat overrides.
Source remark: the source says Lipschitz sums to "2^-10" in the statement; the signed record has the
separate 2^-11 + 2^-11 and joint 2^-10, which is what is proved.

AUDIT FOCUS: design docs/tracks/P/design/P11B-LEAN-DESIGN.md row B18 (collar_increment_lipschitz, lipschitz-family; B13, B15, B17, directional one-variable Cauchy and short/long split) and its node table incl. lf-* steps; P11B design audits; signatures /root/code/KAM-inp/.drafts/design/P11BSignatures.lean. Audit ONLY KAM/Planetary/WeakKAM/ParameterLipschitz.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
