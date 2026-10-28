# S9 prover handoff (branch inp-p14-s9, 4597d414; contains S8 and S7 round 1 (both in audit); offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/SecularBox/GlobalFlow.lean` (171 lines, lines <= 100 cols). Nothing else touched.

**Declarations (signatures verbatim from P14Signatures.lean):** `angle_quadrature`, `sb_global`.
Private helpers: `sbGlobal_eta`, `sbGlobal_mem_congr`, `sbGlobal_amd_congr`, `sbGlobalShift`,
`sbGlobal_add_shift`, `sbGlobal_assemble_shift`, `sbGlobal_omega_lam`, `sbGlobal_omega_cont`.

**Approach:**
- `angle_quadrature`: `intervalIntegral.integral_hasDerivAt_right` with interval integrability,
  strong measurability at the filter and continuity from `Continuous omega`.
- `sb_global`: `sb_slow` gives y. Put g(t) = assemble I 0 (y t).2 (y t).1 and
  lam(t) = fast w0.1 + ∫_0^t sb_omega(g s) ds. Then w(t) = assemble I (lam t) (y t).2 (y t).1.
  - sb-gl-1: continuity of sb_omega on S from `sb_smooth_prop.1` via
    `ContDiffOn.continuousOn_fderiv_of_isOpen` (proved locally; did not need S7's continuity
    addition), and `angle_quadrature`.
  - sb-gl-2: w 0 = w0 (eta). Membership in S and the AMD transfer from g(t) by congruence
    lemmas (S and AMD depend only on fast actions and slow coordinates). The fast actions are I.
  - sb-gl-3: lambda-independence of omega, from lambda-invariance of H (`sb_smooth_prop.2.2`)
    plus `fderiv_comp_add_right`. The derivative of w at t is X_H(w t) componentwise, using
    `sb_field` (fast action component = 0) and `secular_field_components`. Differentiability
    of H at w t comes from `sb_smooth_prop` on the open S.

**Checks:** gate build `KAM.Planetary.SecularBox.GlobalFlow`: success, no warnings.
`#print axioms` for `sb_global` and `angle_quadrature`: `[propext, Classical.choice, Quot.sound]`.
`scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK. The only
message is "KAM.lean is out of date" (expected: generated file, not edited by me).

**Uncertainties / errata / deviations:** none. No signature changed; no hypotheses added. No
heartbeat issues. Inputs used: S8 (SlowFlow) and the existing S7 Field/Smooth/Region; no re-merge of S7 needed.

AUDIT FOCUS: design docs/tracks/P/design/P14-LEAN-DESIGN.md row S9 (angle_quadrature, sb_global; S8, S7, FTC) and its node table incl. stepP:p14:sb-gl-*; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean (~lines 98, 504). S9 derived omega continuity and lambda-independence privately; S7's fix round now exports sb_omega_continuousOn and sb_omega_fast_angle: duplication is not a finding. Audit ONLY KAM/Planetary/SecularBox/GlobalFlow.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
