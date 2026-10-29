# P12-E prover handoff (branch inp-p12e, 60bf4fa5; contains P12-C (in audit) and the T-chain; offloaded package run by the main orchestrator)


Files: KAM/Planetary/PlanarAssembly/Main.lean (new, ~100 lines), KAM/Provider/Planetary/PlanarTwoPlanetKAM.lean
(provider theorem added, ~35 lines).

Approach: `PlanarAssembly.planar` (signature verbatim) eliminates `pg_hypotheses` once, applies the sealed frozen
`properlyDegenerateKAM` (a=b=2, r0, mu0=1, B), picks `radius_choices rG δ c`, threshold `coupling_threshold r c`,
d,D = tubeD/tubeBigD of axisGap/axisMax (`axisData_canonical`, `tubeD_lt_tubeBigD`). For each mu: P-G cylinder set Sc,
`measure` (Borel image, volume equality), `measure_in_tube` (tube, positivity, finiteness), S = total_chart '' Sc,
`transport` for the torus witnesses (range Ψ∘K = Ψ '' range K ⊆ S), `movingKolmogorovSet_of_tube`.
Provider `KAM.Provider.Planetary.planarTwoPlanetKAM` = `PlanarAssembly.planar ...`, telescope identical to the frozen type.

Checks: gate build of KAM.Planetary.PlanarAssembly.Main and KAM.Provider.Planetary.PlanarTwoPlanetKAM: success.
`#print axioms KAM.Provider.Planetary.planarTwoPlanetKAM`: [propext, Classical.choice, Quot.sound].
scripts/lint_sources.sh: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; reports only
"KAM.lean is out of date; run scripts/gen_root_imports.py" (new module Main; KAM.lean is generated, not edited by me:
orchestrator must regenerate).

Seal term for the frozen body of planarTwoPlanetKAM:
`by exact KAM.Provider.Planetary.planarTwoPlanetKAM G m0 m a hG hm0 hm ha hsep eta heta`

Uncertainties: none known; Main imports the frozen P-G theorem file (sealed) as designed. No extra hypotheses, no errata,
no deviations, no heartbeat issues. Private helper `cylinder_subset_of_le` in Main.

AUDIT FOCUS (SEAL-KEY AUDIT for the frozen anchor KAM.Planetary.planarTwoPlanetKAM, manifest id planetary.planarTwoPlanetKAM.v1, frozen file KAM/Frozen/Planetary/Theorems/PlanarTwoPlanetKAM.lean; provider KAM/Provider/Planetary/PlanarTwoPlanetKAM.lean): design docs/tracks/P/design/P1213-LEAN-DESIGN.md row P12-E (C+D, SEALED properlyDegenerateKAM, P6-5 Assembly; prove planar; terminal provider matches the frozen type) and its node table; P1213 design audits; signatures /root/code/KAM-inp/.drafts/design/P1213Signatures.lean (PlanarAssembly.planar, the provider). (1) Exact-type probe in a scratch file outside KAM/: example : type_of% @KAM.Planetary.planarTwoPlanetKAM := @KAM.Provider.Planetary.planarTwoPlanetKAM, and report it. (2) PROSPECTIVE seal: in a scratch copy only (never edit frozen files, the provider or the manifest), copy the complete frozen telescope with the body replaced by the handoff's seal term (by exact KAM.Provider.Planetary.planarTwoPlanetKAM G m0 m a hG hm0 hm ha hsep eta heta); confirm it elaborates and #print axioms shows only propext, Classical.choice, Quot.sound. (3) Provider quarantine: the provider imports the library (PlanarAssembly.Main), never the frozen theorem file of planarTwoPlanetKAM; Main may import the SEALED properlyDegenerateKAM. (4) planar's binders match the frozen telescope exactly; no added premise; the proof genuinely applies properlyDegenerateKAM to pg_hypotheses (P12-C, in its own audit). Audit KAM/Planetary/PlanarAssembly/Main.lean and KAM/Provider/Planetary/PlanarTwoPlanetKAM.lean in full. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
