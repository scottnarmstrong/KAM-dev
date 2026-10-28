# T11 prover handoff (branch inp-p11c-t11, d053b6bf; contains T9 and T14 (passed); offloaded package run by the main orchestrator)


## Files (new)
`KAM/Planetary/PlanarTorsion/Lift.lean` (facade + the two signed theorems) and
`Lift/{Defs,Field,Orbit,Iterate,Inverse,Injective}.lean` (1048 lines total, each file < 240).
No `KAM.lean` edit (see lint note below).

## Declarations
- `p11c_liftFlow`, `p11c_tube` (Lift/Defs): verbatim.
- `full_lift_hamiltonian`, `lift_map` (Lift.lean): statements verbatim (checked by whitespace-normalised diff).
- Graph nodes `lm-ham` / `lm-prop`: local steps inside the two theorems (no separate exports).

## Approach
- Full field: `p11cL_field_assemble` computes X_H at assembled points: (∂_I chi, ∂_p chi ; 0, −∂_q chi).
- `p11cL_ext`: re-centres the T9 flow at time 1/2 so the trajectory is a solution on the open (-1/2, 3/2)
  (the signed `flow` only gives a solution on closed [-1,1], endpoint derivative of the angle integral
  needs an open interval). `p11cL_orbit_solution`: slow solution + angle integral solves the full field
  (FTC with continuity of ∂_I chi along the trajectory). This is `full_lift_hamiltonian`.
- `lift_map` analytic + symplectic (Lift/Iterate): all orbits (zero-angle slab, |lam|<1) lie in one compact
  K₃; R2's `p11cQ_flow_compact_nbhd` gives a short-time analytic map Ψ=Φ_{1/m} on a nbhd U ⊇ K₃ of the FULL
  field; ODE uniqueness gives liftFlow = Ψ^[m] on the slab; analytic by iterate lemma, symplectic by R3's
  `p11cVar_isSymplecticOn` at each orbit point + chain rule. General angles by translation covariance
  (immediate from the definition).
- Injectivity (Lift/Injective): lift of −chi is a left inverse on the tube: T9's last `flow` clause inverts the
  slow part, backward −chi trajectory = reversed chi trajectory (uniqueness), angle integral odd under time
  reversal. Radius r = min(r₁/2, r₂/2), r₂ from `flow` applied to the negated family `p11cL_negFamily`.
- No complex SmallField shortcut, no KAM.Canonical, no provider/frozen-theorem import.

## Checks
- `LEAN_NUM_THREADS=1 inp_lake_build.sh <wt> KAM.Planetary.PlanarTorsion.Lift`: "Build completed successfully (9167 jobs)"; no sorry/error; only style warnings (deprecated `push_neg` used as elsewhere in repo, unused-simp/`<;>` lint in Inverse).
- `#print axioms` for `full_lift_hamiltonian` and `lift_map`: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen anchors OK, ABI hashes OK; the ONLY failure is
  "KAM.lean is out of date; run scripts/gen_root_imports.py" (new modules not yet in the generated root; orchestrator must regenerate).
- All lines ≤ 100 columns; no maxHeartbeats/recDepth overrides; no EuclideanSpace.

## Notes / uncertainties
- New public helper names are all prefixed `p11cL_` (grep: unused elsewhere in KAM). Only new non-`p11cL_` names: none.
- `lift_map` needs, internally, the negated family's `flow`; no extra hypotheses on any signed statement.
- No suspected errata in pinned sources; no deviations from signatures. Design signals: none (default heartbeats everywhere).

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row T11 (full_lift_hamiltonian, lift_map; T9/R3, U9 inverse rotation lift adapter; no complex SmallField shortcut) and its node table incl. lm-ham, lm-prop; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean. Check the design's ban on a complex SmallField shortcut is respected. Audit ONLY KAM/Planetary/PlanarTorsion/Lift.lean and Lift/*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
