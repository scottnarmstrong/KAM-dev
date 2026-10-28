# N11-F3 prover handoff (branch inp-n11f3, 7eab4819; contains N11-A (passed); offloaded package run by the main orchestrator)

- Files: new `KAM/Nekhoroshev/Partial/Homological.lean` (~172 lines).
- Declarations (verbatim from N11Signatures.lean): `KAM.Nekhoroshev.homGenerator`, `KAM.Nekhoroshev.hom`
  (`bpN:p11:hom`). Private helpers: fastAction_mem_polyNbhd, fderiv_liftFast, fastAction_single_slow/fast,
  wfield_liftFast, fderiv_eq_sum.
- Approach: `hom` = Part 6 `homological_param` at m = n+(k+k), D = b.base, ω J = freq h (fast projection J); fast
  projection maps polyNbhd b.base R into polyNbhd {Ic} R (holomorphy of ω and divisor bound transfer);
  `wfield c (liftFast h) z = (freq h (fastAction z), 0)` identifies the directional sum with `extBracket`;
  projMode Λ φ = 0 from vanishing coefficients; reality from c10 (symmetry as ∀ j, j∈Λ ↔ -j∈Λ).
- Checks: gate build `KAM.Nekhoroshev.Partial.Homological` succeeds, no warnings in my file; lint_sources.sh:
  check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only message "KAM.lean is out of date"
  (generated; not edited per rules), no >100-col lines.
- `#print axioms KAM.Nekhoroshev.hom`: [propext, Classical.choice, Quot.sound]
- Uncertainties/errata/deviations: none. No heartbeat issues.

AUDIT FOCUS: design docs/tracks/N/design/N11-LEAN-DESIGN.md row N11-F3 (homGenerator wrapper/hom; exact Part 6 homological_param/divisor, extended Part 4) and its node table; both N11 design audits; signatures /root/code/KAM-inp/.drafts/design/N11Signatures.lean. (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node mapped to Homological established (in the proof or as an export); an UNSIGNED export named after a graph node states its literal conclusion; (c) proof soundness, no added premises; the exact Part 6 results consumed as designed; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100. Audit ONLY KAM/Nekhoroshev/Partial/Homological.lean.
