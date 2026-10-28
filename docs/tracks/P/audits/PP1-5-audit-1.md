# PP1-5 independent audit 1

**Overall verdict: PASS WITH NOTES.** Both assigned nodes are proved with the designed statements. No material defect found. No frozen theorem anchor or provider is delivered by this package, so frozen/provider type equality and seal-body checks are not applicable; this verdict certifies these infrastructure exports, not any planetary headline or frozen seal.

Audited HEAD `c42426e27d7bed55756075aea4aa8226addc01fd`; comparison `inp` = `88983f74ff9952994d1de31d0ed671307437b563`. `git diff inp...HEAD` contains exactly one added file, `KAM/Planetary/Hamiltonian/HolChart.lean` (112 lines). Scope is only `HolChart*`, as required by the handoff. Read AGENTS.md, PLAN, DECISIONS, the package audit brief, handoff, track-P statement conventions, the Part 1 design and its audit, blueprint-P Part 1 and the two graph-node contracts. The user's explicit absolute report path overrides the generic brief's main-worktree destination. No source, frozen file, manifest, or git state was changed.

## Declaration and node verdicts

All implementation locators below refer to `KAM/Planetary/Hamiltonian/HolChart.lean`; public names are in `KAM.Planetary`.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| Real inclusion, private definition, line 39 | `phaseToCL` | PASS | Product of the actual coordinatewise continuous real-linear inclusions. |
| Inclusion identity, private theorem, line 42 | `phaseToCL_apply` | PASS | Definitional equality with `KAM.Kepler.phaseToC`. |
| Real projection, private definition, line 44 | `realPartL` | PASS | Product of coordinatewise real parts on the whole complex phase space. |
| Left inverse, private theorem, line 47 | `realPartL_phaseToC` | PASS | Coordinatewise real part of the real embedding is the identity. |
| Form compatibility, private theorem, line 50 | `symplFormC_phaseToC` | PASS | Exact cast of the frozen form, with sign and coordinate order preserved. |
| Real-slice openness, private theorem, line 54 | `isOpen_preimage_phaseToC` | PASS | Continuous-preimage theorem; arbitrary open complex domain. |
| `stepP:p1:hc-real-derivative`, line 60 | `fderiv_real_slice` | PASS | Exact design signature; analytic real restriction and equality of embedded real derivative with the complex derivative on real vectors. Stronger than the graph step in omitting irrelevant positivity and symplectic premises. |
| `bpP:p1:hol-chart`, line 94 | `hol_chart` | PASS WITH NOTES | Exact design signature; open slice, analytic conformally symplectic chart and derivative identity. Unused `hc` is harmless (N2). |

The public signatures are byte-identical, including binder order, to `docs/tracks/P/design/PART1-LEAN-DESIGN.md:566–584` before their proof bodies. An independent scratch probe copied those signatures into fresh declarations, supplied the implementation exports as proofs, and checked `example : type_of% @design_<name> := @KAM.Planetary.<name>` for each. Both passed. This is an elaborated design-type check, not a frozen-anchor seal check.

Blueprint fidelity: `blueprint-P/parts/p1-hamiltonian-tools.tex:72–77` explicitly allows any total extension outside the open real slice. `hagree` supplies precisely the source's real restriction, without requiring behavior outside that slice. `hsympl` is the complex bilinear matrix identity evaluated at real base points and all complex tangent vectors. It is a source premise, not an assumed chart conclusion. The target `IsChart` unfolds to real analyticity and the delivered `IsSymplecticOn`; no injectivity or global inverse is silently assumed. The ambient types and frozen sign `sum (u.2*v.1 - u.1*v.2)` agree literally. There are no constants with hidden dependence or norm substitutions.

## Proof and definition review

At lines 66–74, complex differentiability on the arbitrary open domain gives complex analyticity by the delivered generic theorem `KAM.analyticOnNhd_of_differentiableOn`. Restrict scalars to real, compose with the real-linear inclusion and real-part projection, and use neighborhood equality from `hagree`. Openness ensures that equality holds throughout a neighborhood, so arbitrary values of the total extension outside the slice do not affect analyticity or derivatives.

At lines 76–90, the two derivatives of the locally equal maps `phaseToCL ∘ Ψr` and `Ψ ∘ phaseToCL` coincide by uniqueness of Fréchet derivatives. Evaluation on each real vector yields the claimed derivative identity. At lines 103–108, instantiate complex symplecticity on embedded real vectors, substitute that derivative identity and the cast compatibility of the two forms, then use injectivity of the real-to-complex cast. No difficult step is assumed as a bundled field or extra premise.

Definition classification is complete: the only new definitions are the private `phaseToCL` and `realPartL`; both are standard continuous real-linear maps on their entire carriers. No new abbreviation, structure, fallback, conditional junk value, or replacement frozen object is introduced. The argument also handles empty domains and zero dimension without extra assumptions.

## Hygiene and independent checks

All Lean-related commands below ran sequentially with `LEAN_NUM_THREADS=1` and niceness 5. No concurrent Lean command was launched by this audit. The build used the required compile gate. No heartbeat, recursion-depth, or synthesis-budget override was used.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-pp15 KAM.Planetary.Hamiltonian.HolChart
   ```

   Exit 0. Gate output: `[inp-gate] slot 1 acquired 06:39:07 for KAM.Planetary.Hamiltonian.HolChart`.
   Final output: `Build completed successfully (9074 jobs).` The module was replayed. Its sole warning was `HolChart.lean:94:27: Variable name hc is not explicitly referenced.` Replayed dependencies Algebra (146:39) and Chart (193:36) also emitted unused-`hc` warnings, outside the assigned scope.

2. Signature/application probes and axioms:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/PP15Audit.lean
   ```

   Exit 0, no probe errors. Exact axiom output:

   ```text
   'KAM.Planetary.fderiv_real_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.hol_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.analyticOnNhd_of_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   This covers every new public theorem and additionally the imported analytic bridge. Neither `sorryAx` nor another axiom occurs. The scratch probe was deleted after checking.

3. Kernel replay (one invocation, the sole new lemma module; no provider exists):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Hamiltonian.HolChart
   ```

   Exit 0. Complete output: `replaying KAM.Planetary.Hamiltonian.HolChart`.

4. Full source lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1 solely for the explicitly permitted stale generated root. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (422 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No line-length or other hygiene failure was emitted.

5. Static checks: `git diff --check inp...HEAD` exited 0 with no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` exited 0 with empty output. A search for `sorry|admit|axiom|unsafe|opaque|set_option|EuclideanSpace` in the assigned module had no matches (exit 1). Python Unicode-character counting found 112 total lines and maximum width 100. Copyright, `module`, public imports, module docstring and public section are present; the section has `@[expose]`.

   Recursive inspection of KAM source imports found 28 modules in the closure, no provider imports and no frozen theorem imports (SEALED or DRAFT_SORRY). The frozen dependencies are definitions only: Phase, SymplecticForm, HamiltonianVectorField, IsDiophantine, FastShift, ComplexStrip, OmegaZero, IsRealOnReals and IsPrimaryOnStrip, plus HamiltonianVectorFieldC. Their meanings were not changed.

## Notes, errata, deviations and limits

**N1 (informational):** `HolChart.lean:14` explicitly imports `KAM.Strip.AnalyticTaylor` and line 66 uses its generic finite-dimensional analyticity theorem. The design proof plan at `PART1-LEAN-DESIGN.md:255–259` proposed reducing the product carrier to a finite function space and applying `KAM.holomorphic_analytic`. The implementation uses the underlying general theorem directly, with exactly the needed hypotheses. This is a valid proof-route deviation, with no cycle, extra premise or source weakening. It also avoids the misnamed real-restriction reference already identified in design audit N2.

**N2 (informational):** `HolChart.lean:94` retains design premise `hc : 0 < c`, though the conclusion as defined is true without positivity. Retaining it preserves the approved design interface and blueprint convention; this warning does not affect soundness. The handoff calls this a “frozen signature,” but this is a design signature: neither node has a frozen anchor, as recorded in the graph packet. No frozen seal is being approved here.

No suspected defect in a pinned source or the assigned blueprint statement was found. No material uncertainty remains for the two audited exports. Their proofs discharge the arbitrary-open-domain real-derivative obligation at the implementation level; this report does not edit graph status, certify downstream consumers, or claim closure of P-G, P-PLANAR or P-FIXED. Only this report is an intended repository edit.
