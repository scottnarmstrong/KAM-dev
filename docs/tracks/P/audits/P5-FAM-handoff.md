# P5-FAM prover handoff (branch inp-p5fam, 1005e639; offloaded package run by the main orchestrator)


## Files (new)
- KAM/Planetary/PGAssembly/Family.lean (facade + declarations): PGFamily, physicalTorus, PGFamilySpec,
  torus_conv, pgFamily, kset, rawUnion (verbatim from P45Signatures.lean).
- KAM/Planetary/PGAssembly/FamilyFreq.lean: frequency_bounds.
- KAM/Planetary/PGAssembly/FamilyAux.lean: fam_realTube_eq, fam_isOpen_realNbhd, fam_angleScale_injective,
  fam_hvf_congr, fam_cyl_ext, fam_ham_eq (H∘phi∘angleScale/(2π) = Re(kamH+kamF) on the real strip),
  fam_lattice (lattice torus transfer), fam_lipschitz.
- KAM/Planetary/PGAssembly/FamilySigma.lean: fam_isSigmaCompact_D0 and closedness helpers.
All files < 300 lines. KAM.lean NOT regenerated (lint says out of date; orchestrator to run gen_root_imports.py).

## Approach
torus_conv destructures the single two_scale_kam output on pg_kam_hyp (hL = Eq.refl); raw J θ := K (realFreq (kamH) J) θ;
pg_kam_dictionary identifies dioBase with pgD0, and 32*eHat*rhoHat with rK; I₀(realFreq J)=J gives K ω θ = Φ(θ, i J).
Lipschitz: defect bounds + limitmap_data/norm comparison. Periodicity/injectivity: lattice-torus clauses + phi_chart (Q2) + location.
Measure: two_scale_kam volume bound (set inclusion). Cylinder torus: fam_lattice then P1 cyl_pipeline with phi_chart, location.
σ-compactness: pgD0 = (open box) ∩ (closed set) using continuity of fastFrequency on V and of realFreq(kamH) on the tube.
frequency_bounds: complexFrequency real-slice bridge + norm_jpGrad_le/norm_jpTheta_le + h0bounds (M0).

## Checks
- Gate build `KAM.Planetary.PGAssembly.Family` (and FamilyFreq, FamilyAux, FamilySigma): Build completed successfully.
- `#print axioms` torus_conv, frequency_bounds: [propext, Classical.choice, Quot.sound].
- No sorry/axiom/maxHeartbeats; lines ≤ 100 (checked with awk).
- scripts/lint_sources.sh: only complaints were the two long lines (since fixed) and "KAM.lean is out of date"
  (generated; not edited); modules/frozen/ABI checks PASS.

## Uncertainties / errata / deviations
- No statement defects found; signatures unchanged. PGFamily and physicalTorus are defined in Family.lean (signature file puts them there).
- Extra public helper names all prefixed `fam_`; none shadow existing names.
- No design signals (no heartbeat issues).

AUDIT FOCUS: design docs/tracks/P/design/P45-LEAN-DESIGN.md (incl. Revision 4) row P5-FAM (PGFamilySpec, torus_conv, pgFamily, kset, rawUnion, frequency_bounds; P3 KamHyp and the joint output of two_scale_kam; P1 cyl_pipeline) and its node table; P45 design audits; signatures /root/code/KAM-inp/.drafts/design/P45Signatures.lean. Check in particular that two_scale_kam's JOINT output is consumed with shared witnesses (not re-chosen). Audit ONLY KAM/Planetary/PGAssembly/Family{,Aux,Freq,Sigma}.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
