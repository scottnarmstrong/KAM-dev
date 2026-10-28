# B06 prover handoff (branch inp-p11b-b06, e1e6b184; off inp; offloaded P11B package run by the main orchestrator)


**Files:** new `KAM/Planetary/WeakKAM/Initial.lean`. No other file touched (KAM.lean not edited).

**Declarations (signature file, verbatim):** `selectionInitial` (def), `initial` (theorem). Both belong to B06; no other signature assigned here.
Helpers (new, distinct names, grepped): `selectionInitial_segment_mem`, `selectionInitial_actionNbhd_mono`,
`selectionInitial_fderiv_apply`, `selectionInitial_gradient_differentiableOn`, `selectionInitial_taylor`.
Imports `KAM.Planetary.WeakKAM.Data` and `KAM.Head.DerivativeBounds` (for `KAM.Head.isOpen_actionNbhd`).

**Approach:** Holomorphy by composition (h, f, h(b), gradient via `holomorphic_regularity_of_finiteDimensional`).
Taylor bound without second-order Taylor: fencing lemma `image_norm_le_of_norm_deriv_right_le_deriv_boundary` for
s ↦ h(b+sη) - h b - s Dh(b)η with boundary n C₁‖η‖² s²/2; derivative bounded using the Hessian bound along the
segment (`Convex.norm_image_sub_le_of_norm_fderiv_le`). Periodicity from `hf.periodic`; reality from `d.real`, `hf.real`.

**Checks:** gate build `KAM.Planetary.WeakKAM.Initial`: "Build completed successfully"; no warnings in file.
`scripts/lint_sources.sh`: all PASS except "KAM.lean is out of date; run scripts/gen_root_imports.py" (expected: new
module; root file is generated, not edited by me).
`#print axioms KAM.Planetary.initial`: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations:** none. No heartbeat issues. Statements true as given (no extra hypotheses;
`hs : 0 < s₀` is unused, binder renamed `_hs` only to silence the linter, type unchanged).

AUDIT FOCUS (design docs/tracks/P/design/P11B-LEAN-DESIGN.md row B06 and its proof plan; P11B design audits; signatures /root/code/KAM-inp/.drafts/design/P11BSignatures.lean): (1) selectionInitial (def) and initial (theorem) = signature file EXACTLY, and the B06 slice COMPLETE: check the design row and proof plan for every obligation assigned to B06 (a sibling package B04 failed only because a proof-plan obligation was omitted, so read the plan line by line); (2) the definition means the source object on its whole carrier (no fallback branch); (3) proof soundness: holomorphy by composition, the fencing-lemma Taylor bound with constant n C1 |eta|^2 s^2/2 versus the blueprint's constant, periodicity and reality; no added premises; (4) hygiene (no EuclideanSpace; no public short name already used elsewhere in KAM; no root shadow). Audit ONLY KAM/Planetary/WeakKAM/Initial.lean.
