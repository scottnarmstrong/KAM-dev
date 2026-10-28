# A3 prover handoff (P14; branch inp-p14-a3, 865c070d; off inp (A0, A1 on inp); offloaded package run by the main orchestrator; prover on claude-10)


**Files:** new `KAM/Planetary/AMD/Closure.lean` (227 lines). Commit 865c070d on inp-p14-a3 (KAM.lean not touched).

**Declarations (signatures verbatim):** `negativeEnergyDomain`, `element_continuity` (`bpP:p14:closure(a)` helper),
`closure` (`bpP:p14:closure`; steps cl-a/b/c internal). All others in the signature file belong to other packages.
New public names grepped beforehand: none pre-existing. Private helpers are `cl_*`.

**Approach:** radii/energy continuity on {r>0}; domain open as finite intersection; actions = m·sqrt(-m/(2E)),
AMD = ΣΛ − ΣC all continuous on it. `closure`: openness by writing amdOuter as an intersection of preimages of open sets.
Sequential closedness: from `elements` each Λ−C ≥ 0, so Λ_i−C_i ≤ AMD; collar gives C_i ≥ lo_i−(init+nδ)+δ > 0 uniformly and
E_i = −m³/(2Λ_i²) ≤ −m³/(2up_i²) < 0 uniformly; pass to the limit; strict bounds follow from hAMD and lo<lo+δ.

**Checks:** `inp_lake_build.sh . KAM.Planetary.AMD.Closure`: success, one warning (`hmargin` unused: kept so the
signature is verbatim; not needed, the AMD/lower margins suffice). `#print axioms` for `closure` and `element_continuity`:
[propext, Classical.choice, Quot.sound]. `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI OK;
only message "KAM.lean is out of date; run scripts/gen_root_imports.py" (generated file, orchestrator regenerates).

**Uncertainties / errata / deviations:** none. No heartbeat issues. Needed an extra import
`KAM.Frozen.Planetary.Defs.AMDBoxAdmissible` (Setting.lean does not import it).

AUDIT FOCUS (design docs/tracks/P/design/P14-LEAN-DESIGN.md row A3, Appendix A and node rows; audits DESIGN-P14-design-audit-{1,2}.md; signatures .drafts/design/P14Signatures.lean): (1) negativeEnergyDomain, element_continuity, closure = signature file exactly, and the A3 slice COMPLETE; (2) proofs sound (closure and continuity on the negative-energy domain; A0, A1 consumed as designed); no added premises; (3) NAME SHADOWING: the signed theorem KAM.Planetary.closure shadows Mathlib's topological  inside namespace KAM.Planetary. Test whether a module in namespace KAM.Planetary that imports AMD/Closure and writes  (topological closure of a set; many existing KAM.Planetary files do, e.g. the P45 design's ) still elaborates, or now fails/becomes ambiguous; report the result as a finding with a recommendation (keep, or rename via a design note) — do not rename yourself; (4) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/AMD/Closure.lean.
