# P4-ONE prover handoff (branch inp-p4one, 5703c89; contains inp-p4li, inp-p4af, inp-p4lt (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/PGMeasure/OneScale.lean` (205 lines); commit 5703c89 on branch inp-p4one. No other file touched.

**Node proved:** `bpP:p5:dio-one` -> `KAM.Planetary.dio_one`, statement verbatim from the signature file (also `dioConstant`, verbatim).

**Added declarations (not in the signature file's OneScale slice):**
- `pgInverse`, `pgInverseL`, `pgInverseR` (verbatim from the design signatures, which list them under lip-inverse), plus `pgInverse_spec`. They are NOT in `Setting.lean` or `CompactLipschitz.lean` on this branch, and `dioConstant` needs them, so they are defined in OneScale.
  **Orchestrator action:** if P5/other packages expect them in CompactLipschitz, move them there (and make OneScale import them) to avoid duplicate definitions at merge.
- Helpers: `latticeS_mono` (S(n,τ) ≤ S(m,τ) for n ≤ m < τ; needed since the lattice has dimension a but the constant uses a+b), `resonantSlabs`, `volume_resonantSlabs_le`, `volume_le_of_lipschitz`.

**Approach:** bad set ⊆ pgInverse '' (ω(closure V) ∩ resonantSlabs); each slab bounded by `affine_slab` (‖k‖∞ ≥ 1), summed with `lattice_tail`; pushed forward by the L-Lipschitz inverse using μH[a] = volume on Fin a → ℝ (`hausdorffMeasure_pi_real`, sup norm), `LipschitzOnWith.hausdorffMeasure_image_le`.

**Checks:**
- `inp_lake_build.sh /root/code/KAM-inp-p4one KAM.Planetary.PGMeasure.OneScale`: "Build completed successfully (9067 jobs)"; no warnings in OneScale, no sorry.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only message "KAM.lean is out of date; run scripts/gen_root_imports.py" (generated root; not edited per rules, orchestrator to regenerate).
- `#print axioms KAM.Planetary.dio_one`: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations:** none on the statement. Design signal: a first monolithic proof hit the default heartbeat limit; resolved by splitting into the helper lemmas above (no heartbeat override used).

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P4-ONE and its proof plan; audits DESIGN-P45-design-audit-{1,2,3}.md; signatures .drafts/design/P45Signatures.lean): (1) statement = design signature (dio_one, dioConstant), frozen IsDiophantine consumed exactly; (2) proof sound; no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Planetary/PGMeasure/OneScale*.lean.
