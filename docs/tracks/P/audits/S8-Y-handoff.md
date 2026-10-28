# S8-Y prover handoff (branch inp-s8y, 2a6ddf3; offloaded package run by the main orchestrator; prover on claude-12)


**File:** `KAM/Planetary/SecularForm/Symmetry.lean` (new, ~580 lines). KAM.lean untouched (lint reports it out of date, as expected).

**Declarations (statements verbatim from P810Signatures.lean):** `rotateSlow`, `rotatePhysical`, `symmetries`, `evenness`, `evenness_taylor` (all in `KAM.Planetary.SecularForm`). No signature changed; no extra hypotheses.

**Approach**
- One-planet chart identities proved from uniqueness of the Kepler equation (`keplerLong_unique`): `poincare_antipode` (S1), `poincare_rotate` (S2, via `rotBlock`), `poincare_reflect` (S3, `sigmaRefl`). Lifted to `poincareProd` via `ofPlanets` (`symmetries`).
- `slowDom` characterised by `mem_slowDom_iff` (holds for all t, so periodicity is available at every angle).
- `perturbation_map`: fFix/fMov invariant under additive isometries of positions/momenta; gives `perturbation_antipode/rotate/reflect`, and `perturbation_periodic` via `poincareProd_lattice`.
- Torus average invariance without integrability (so the non-integrable case is covered): `cell_integral_add`, `cell_integral_neg`, by a fundamental-domain argument (ZSpan basis scaled by 2π, `IsAddFundamentalDomain.setIntegral_eq`, `image_of_equiv`).
- `evenness` on all of `slowDom` (strictly stronger domain than the analytic polydisc, as in the design).
- `evenness_taylor`: `iteratedFDeriv_odd_eq_zero` (general: even function near 0 has zero odd iterated derivatives, no smoothness needed, via `ContinuousLinearEquiv.iteratedFDerivWithin_comp_right` with neg) + evenness on the open neighbourhood `{(u.1,I,u.2) ∈ slowDom}` of 0.

**Checks**
- `lake env lean` on the file: no errors, no warnings.
- Gate build `inp_lake_build.sh /root/code/KAM-inp-s8y KAM.Planetary.SecularForm.Symmetry`: succeeded on the final file: "✔ [9111/9111] Built KAM.Planetary.SecularForm.Symmetry".
- `scripts/lint_sources.sh`: only message is "KAM.lean is out of date" (generated; not edited by me); check_lean_modules PASS, frozen guard OK, ABI hashes OK, no >100-char lines.
- No sorry/axiom/admit/unsafe/opaque, no heartbeat options.
- `#print axioms` for `symmetries`, `evenness`, `evenness_taylor`: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties / design signals:** none; no heartbeat problems. Imports: Mathlib, ParameterIntegral (→ Basic → Poincare/Product), Poincare/Chart; no provider or frozen theorem.

**Suspected errata / deviations:** none. Note (not an erratum): the blueprint's proof of evenness invokes analyticity for the Taylor step; the Lean `evenness_taylor` needs none, since odd iterated derivatives of an even function vanish at the centre unconditionally.

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S8-Y and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) statements = design signatures exactly (rotateSlow, rotatePhysical, symmetries, evenness, evenness_taylor); (2) proofs sound (torus-average invariance, evenness from the reflection symmetry, Taylor evenness); no added premises; (3) hygiene. Audit ONLY KAM/Planetary/SecularForm/Symmetry.lean (compare with branch inp).
