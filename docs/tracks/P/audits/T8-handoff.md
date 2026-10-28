# T8 prover handoff (branch inp-p11c-t8, 488d5689; offloaded package run by the main orchestrator)


## Files (new, committed)
- KAM/Planetary/PlanarTorsion/Homological.lean (~210 lines): `p11c_chi`, `homological` (signature verbatim,
  incl. unused `hO`, a linter warning only), helpers `chiModes`, `mem_chiModes`, `chi_eq_sum`, `chi_div_ne`,
  `chiModes_sum`, `charprod_extract`, `chiCoeff`, `chiCoeff_analytic`, `chi_family`, `chi_bracket`.
- KAM/Planetary/PlanarTorsion/Homological/Extract.lean (~140 lines): `quarticVec`, `quarticVec_smul`,
  `quarticVec_prod`, `quartic_extract`, `quartic_of_coeffs`.
- No KAM.lean / Frozen / manifest edits (lint reports KAM.lean out of date: orchestrator regenerates).

## Nodes
- bpP:p11b:homological -> `KAM.Planetary.homological`, `KAM.Planetary.p11c_chi`.
- stepP:p11b:ho-def -> `chi_eq_sum` (finite-mode form), `chi_family` (chi is a QuarticFamily on O).
- stepP:p11b:ho-eq -> `chi_bracket` (bracket equation), `chiModes_sum` (reality/reconstruction of modes).

## Approach
`p11c_chi` tsum reduces to a finite sum over chiModes (k != 0, sum |k_i| <= 4) using `char` support.
NR4 makes each divisor nonzero on O. Existence of chi as QuarticFamily: each product of one-plane Fourier
coefficients is a degree-4 homogeneous polynomial (charFcPoly, charFc_smul), so `quartic_extract` gives
constant complex monomial coefficients; the chi coefficient of each monomial is Re of a finite sum with
analytic terms; `quartic_of_coeffs` packages a QuarticFamily.
Bracket: chi is Re of a finite sum of differentiable characters; `character_bracket` gives
fderiv char_k = i<k,w> char_k; cancel the divisor; `char` HasSum gives sum_{k!=0} char_k = F - average.

## Checks
- Gate build `KAM.Planetary.PlanarTorsion.Homological`: success (warnings: unused `hO`; deprecated names in T7).
- `scripts/lint_sources.sh` (run after final edit): check_lean_modules PASS, frozen-anchor guard OK, ABI hashes
  OK, no >100-column lines; only complaint "KAM.lean is out of date". (A later re-run timed out on a busy machine.)
- `#print axioms KAM.Planetary.homological` and `p11c_chi`: [propext, Classical.choice, Quot.sound].
- No set_option, sorry, axiom, EuclideanSpace; no provider/DRAFT_SORRY imports.

## Uncertainties / errata / deviations
- None. `hO : IsOpen O` is unused (analyticity on O suffices); kept for the verbatim signature.
- A fresh worktree lacked Characters oleans; first gate build took ~14 min.
- Design signals: none.

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row T8 (finite chi, reality, homological equation; NR4 source premises) and its node table; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean. Audit ONLY KAM/Planetary/PlanarTorsion/Homological.lean and Homological/Extract.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
