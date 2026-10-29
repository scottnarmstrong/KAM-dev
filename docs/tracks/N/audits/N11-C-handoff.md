# N11-C prover handoff (branch inp-n11c, 3fd1914d; offloaded package run by the main orchestrator)


## Files
- KAM/Nekhoroshev/Partial/Bracket.lean (~380 lines): `ext_part4`, `bracket`, `bracket_dominated`, `bracket_g`
  (+ private helpers: clm_eq_sum, extBracket_eq, inClass_anti, wsum_sum_le, prod_wsum, wbound_congr, wbound_sum, ...).
- KAM/Nekhoroshev/Partial/VectorField.lean (~100 lines): `scaled` (def), `vf`.
Statements copied verbatim from .drafts/design/N11Signatures.lean (checked textually up to `:=`).

## Nodes
bpN:p11:ext-part4 -> ext_part4 (sup_le_wbound); bpN:p11:bracket (+ br-fast/br-slow/br-dom) -> bracket, bracket_dominated;
bpN:p11:bracket-g -> bracket_g; bpN:p11:scaled -> scaled; bpN:p11:vf -> vf.

## Approach
Bracket: `extBracket` = signed sum over Fin n ⊕ Fin n ⊕ Fin k ⊕ Fin k of products (∂θu∂I v, -∂I u∂θ v, c∂q̃u∂p̃v,
-c∂p̃u∂q̃v) (`extBracket_eq`, unconditional, by linearity of fderiv). Then Part 4's wbound_bracket proof pattern:
wsum_sum_le + coeff_mul + cauchy_theta/cauchy_action; slow part gives 2kc/((R0-R+ρ)ρ).
bracket_dominated: exp 1 > 2.718 (Real.exp_one_gt_d9). bracket_g: per-j `bracket` + dominated, fderiv_fun_sum on the open
domain, coefficient congruence (wbound_congr), finite-sum wbound. vf: cauchy_loss + sup_le_wbound; needs 1 ≤ k only for cσ ≤ ρ.

## Checks
- Gate: `inp_lake_build.sh /root/code/KAM-inp-n11c KAM.Nekhoroshev.Partial.VectorField` -> "Build completed successfully (3227 jobs)"; Bracket 18s, VectorField 9.7s; no warnings in my files.
- `sh scripts/lint_sources.sh`: no violations in my files (over-100-col lines fixed); only note "KAM.lean is out of date" (generated; not edited, per rules); modules PASS, frozen guard OK, ABI OK.
- `#print axioms` of ext_part4, bracket, bracket_dominated, bracket_g, vf: [propext, Classical.choice, Quot.sound].

## Uncertainties / notes
- `ext_part4` and `bracket_dominated` are signed but not listed in the N11-C package row; I put them in Bracket.lean
  (design audit table maps them to the bracket/ext-part4 nodes). Orchestrator: confirm no other package defines them.
- Short-name overlap: `KAM.NormalForm.bracket_g` exists (NormalForm/BracketDecomp.lean); mine is `KAM.Nekhoroshev.bracket_g`
  per the signature ruling. Neither file opens the other namespace; consumers that `open KAM.NormalForm KAM.Nekhoroshev`
  must qualify.
- Unused signature hypotheses (hρR, hV in bracket; hc in bracket_dominated; hs in ext_part4) are consumed by `have _ :=`.
- No heartbeat problems; no set_option overrides.

## Suspected errata / deviations
None. (Source blueprint bracket-g says |g|_*; signature uses explicit sum form — matched exactly.)

AUDIT FOCUS: design docs/tracks/N/design/N11-LEAN-DESIGN.md row N11-C (bracket/bracket_g, scaled/vf) and its node table; both N11 design audits; signatures /root/code/KAM-inp/.drafts/design/N11Signatures.lean. Audit ONLY KAM/Nekhoroshev/Partial/{Bracket,VectorField}.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
