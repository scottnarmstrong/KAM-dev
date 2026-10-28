# PP1-7 independent proof audit 1

Overall verdict: **PASS WITH NOTES**. No material mathematical defect was found. The notes concern literal byte identity, the generated root, and an old blueprint sentence. This is acceptance of Part 1 infrastructure, not sealing of a frozen root.

## Scope and snapshot

Audited only `KAM/Planetary/Hamiltonian/Liouville.lean`, as required by the handoff's AUDIT FOCUS. HEAD is `b1e76a270a0b61f1091490f5d53171a13321a0d1`; `inp` is `9580e5654bb30057ca30df9bbabf6c8e234b38a4`. `git diff inp...HEAD` warns of multiple merge bases and selects `d030f8799fbc9a4c5e23582162b9bd844fa49574`; its changes are Chart (248 added lines) and Liouville (233 added lines). Chart is an upstream dependency, not re-audited as PP1-7. At entry the working tree already had an uncommitted Liouville Haar-docstring wrap and an untracked handoff. The audited working file includes that formatting repair: 234 lines, maximum 99 Unicode characters per line, SHA-256 `6859d178c21b7916b2c798bae9caedf57bdfe7d4c2dd3856344a4830998ec73c`. No implementation edit was made by this auditor.

Read AGENTS, PLAN, DECISIONS, the package-audit brief, handoff, track P statement, Part 1 design (row P1-7, signatures, proof plan), its independent design audit, Kepler design D17/P6-5(b)/dependency item 8/F6, and blueprint Part 1 lines 191–209 and Part 6 lines 253–258. Checked the imported frozen definitions and the actual Chart, Kepler symplectic, ODE shift, and Mathlib Jacobian interfaces.

**Frozen-anchor verdict: not applicable.** PP1-7 introduces no provider or frozen theorem. Provider/frozen ABI and seal-copy checks therefore have no anchor to test. Instead the scratch probe copies all six planned theorem signatures under fresh names, supplies the explicit implementation applications in binder order, and checks full types with `type_of%`. It separately copies the Kepler consumer signature and proves the unit-cell definitional equality. No frozen text is rewritten.

## Declaration fidelity and proof findings

All names below are in `KAM.Planetary`. The six design theorem types preserve binder order, constants, dimensions, sets, and the distinction between Borel `MeasurableSet` and Lebesgue `NullMeasurableSet`. All dimensions, including zero, remain permitted. No new conclusion-shaped premise, hidden hard-step instance, enlarged constant dependence, or weaker conclusion was found.

| Node / contract | Declaration (working-file line) | Verdict | Reason |
|---|---|---|---|
| Liouville Haar helper | `isAddHaarMeasure_volume_phase` (37) | PASS | Exact design type; existing product Haar instance for the actual product volume. Local use only. |
| Cell data | `unitCell` (41) | PASS | Exactly the half-open cell in all position coordinates; momenta unrestricted. |
| IFT helper | `IsChart.exists_open_injOn` (43) | PASS | Produces an open neighborhood contained in O on which the chart is injective, from analytic regularity and invertible derivative. No global injectivity premise. |
| `bpP:p1:liouville`, `stepP:p1:li-borel` | `measurableSet_chart_image` (60) | PASS | Borel image without global injectivity, using countably many locally injective open neighborhoods. Exact design signature. |
| `bpP:p1:liouville`, `stepP:p1:li-meas`, `li-vol` | `chart_measure_image` (83) | PASS | Null measurability, upper bound, and equality conditional on injectivity on A, exactly as designed. |
| Cell helper | `measurableSet_unitCell` (121) | PASS | Borel cell as intersection of coordinate preimages of Ico. |
| Lattice helper | `exists_shift_mem_unitCell` (129) | PASS | Negative coordinate floors give an integer shift in A and the half-open cell; only set periodicity assumed. |
| Lattice helper | `injOn_unitCell` (140) | PASS | Q2 makes colliding points differ by an integer; two cell coordinates differ by strictly less than one, so every integer is zero. |
| `bpP:p1:liouville-lattice` | `liouville_lattice` (163) | PASS | Full image/cell-image equality, exact c^d cell-volume formula, positivity iff, bounded-cell finiteness. Exact design signature. |
| `bpP:p1:liouville-lattice`, Borel clause | `liouville_lattice_measurableSet` (203) | PASS | Exact Borel interface. Cell reduction and the proved local Borel-image theorem suffice. |
| Kepler D17, P6-5(b) | `measure_chart_image` (217) | PASS WITH NOTES | Elaborated signature equals the Kepler and Part 1 interfaces. Literal text differs only by wrapping hQ1; see N1. Full-position-lattice scope retained. |

**Area formula.** At lines 89–118 the proof chooses a Borel B contained in A with B ae-equal to A. The remainder A\B is null. Differentiability on that remainder gives a null image using `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`; this theorem does not require Borelness of the remainder. Thus replacing A by B preserves both image volume and input volume. On B, `IsChart.abs_det_fderiv` identifies the Jacobian with c^d, and the Mathlib inequality/equality formulas apply with their genuine derivative and injectivity hypotheses. The proof handles infinite volume through ENNReal without cancellation or finiteness assumptions. It implements the documented alternative route in design section 4.9.

**Borel images.** The IFT helper constructs a continuous linear equivalence from the actual derivative, then an open partial homeomorphism. Intersecting its source with O retains openness and injectivity. `countable_cover_nhdsWithin` gives a countable cover; each A∩U has Borel image by continuous injectivity. The union gives the global Borel image. Global injectivity is not silently assumed.

**Lattice and Haar.** Q1 identifies the image after the floor shift; Q2 proves injectivity on the cell. Countability of `Fin d → ℤ`, translation invariance of the actual product Haar measure, and a countable null cover prove positivity in the reverse direction. The bounded-cell conclusion uses bounded-set finite measure and a finite ENNReal factor. No global instance was installed. Design-audit N1's permitted alternative is implemented: Chart line 214 installs the product Haar instance directly, so keeping the named helper in Liouville creates no import cycle.

**Consumer applicability.** The Kepler theorem takes separate analyticity and symplectic hypotheses and the exact inline integer shift, definitionally equal to `angleShift`. It supplies Borelness, volume scaling, and positivity for P6-5(b); the tube-volume finiteness clause belongs to P6-5(a). Q1/Q2 and A-periodicity are for the entire position lattice. F6 remains binding: this does not provide the fast-only lattice interface for Cartesian P-G cylinder tori. P12 must use `chart_measure_image` on its injective cell and discharge its own chart/family obligations. No downstream assembly or root proof is certified here.

## Definition and import classification

`unitCell` is the sole new definition; there are no new abbrevs, structures, instances, or alternative measure objects. Its intended body is valid on the entire carrier and has no fallback or junk branch. The module-wide `@[expose] public noncomputable section` exposes the definition as required. The four extra helper theorems state local topology, measurability, and lattice facts; none assumes the Liouville conclusion.

The transitive repository import closure comprises Liouville, Chart, Algebra, `KAM.Kepler.Basic`, `KAM.ODE.Basic`, and five frozen definition modules: SymplecticForm, HamiltonianVectorField, IsDiophantine, Phase, FastShift. There is no provider or frozen theorem import, including no DRAFT_SORRY theorem. Thus no imported frozen theorem manifest state needs approval. The frozen Phase is literally `(Fin d → ℝ) × (Fin d → ℝ)` with the intended product volume.

## Independent validation

Commands were run from `/root/code/KAM-inp-pp17`. The targeted build, signature/axiom probe, and kernel replay are separate sequential invocations. No cache changes, clean, library-wide build, or implementation mutation was requested.

1. **Targeted build:**
   ```sh
   env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-pp17 KAM.Planetary.Hamiltonian.Liouville
   ```
   Exit **0**. Gate output: `[inp-gate] slot 1 acquired 06:23:59 for KAM.Planetary.Hamiltonian.Liouville`. Final output: `✔ [9056/9056] Built KAM.Planetary.Hamiltonian.Liouville (8.9s)` and `Build completed successfully (9056 jobs).` Dependencies were replayed from the build overlay; the displayed job count is not a rebuild of the library. Only pre-existing warnings: Algebra:146:39 and Chart:193:36, each `Variable name hc is not explicitly referenced.` No PP1-7 warning or error.

2. **Lint:**
   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```
   Exit **1**, exclusively the permitted generated-root exception:
   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (419 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```
   An initial `sh scripts/lint_sources.sh` returned the same results, but omitted the explicit thread/niceness environment; it was rerun as above after build completion. This invocation mistake is an audit-procedure deviation, not an implementation change. No audit proof check is based solely on that initial invocation.

3. **Elaborated signatures, explicit applications, unit-cell body, and all public theorem axioms:**
   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/PP17Audit.lean
   ```
   Exit **0**, with no warnings/errors. Probe construction: copy the six theorem headers from Part 1 Appendix F, rename them `PP17Audit.signature_<name>`, and use `by exact KAM.Planetary.<name>` with their explicit binder arguments in order. Copy Kepler design lines 2034–2045 separately as `kepler_signature_measure_chart_image`, with the corresponding explicit application. Check `example : type_of% @signature_<name> := @KAM.Planetary.<name>` for all six planned theorems. Check `unitCell d = {z : Phase d | ∀ i, z.1 i ∈ Ico (0 : ℝ) 1}` by rfl. Finally run `#print axioms` for each of the ten public theorems. Exact axiom output:
   ```text
   'KAM.Planetary.isAddHaarMeasure_volume_phase' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.IsChart.exists_open_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.measurableSet_chart_image' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.chart_measure_image' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.measurableSet_unitCell' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.exists_shift_mem_unitCell' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.injOn_unitCell' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.liouville_lattice' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.liouville_lattice_measurableSet' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.measure_chart_image' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. **Kernel replay, one invocation for the sole in-scope module (no provider module exists):**
   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Hamiltonian.Liouville > /tmp/pp17-audit-1-leanchecker.log 2>&1
   ```
   Exit **0**. Exact output:
   ```text
   replaying KAM.Planetary.Hamiltonian.Liouville
   ```

5. **Static hygiene:** no occurrences of `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `set_option`, or `EuclideanSpace` in the audited module. Copyright, module command, public imports, module docstring, public exposed section, 1500-line cap, and 100-character limit all pass. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` exits **0**, with empty stdout (only the multiple-merge-base warning on stderr). `git diff --check` exits **0**. Scratch cleanup and final report checks are recorded below.


## Notes, source defects, and limits

**N1 — Low, literal byte-identity wording.** Kepler design lines 2034–2045 and Part 1 appendix lines 811–822 contain a single-line hQ1 binder; implementation lines 219–220 wrap it to meet the 100-character lint. Five other design theorem headers match exactly. `measure_chart_image` matches both references after whitespace normalization and in elaborated type, but it is not literally byte-identical. The handoff already discloses the formatting deviation. No signature repair is required; “identical up to whitespace, with identical elaborated type” is the precise receipt.

**N2 — Low, stale blueprint explanation.** `blueprint-P/parts/p12-planar-assembly.tex:205` says the Borel-image assertion “needs that hypothesis,” referring to injectivity on A. In the analytic nondegenerate chart setting it does not: the countable local-inverse proof above establishes the general assertion, as the current Part 1 lines 192 and 197 also explain. The P12 use on an injective cell is valid; its required injectivity for volume equality remains. Suggested replacement for the final clause: “Injectivity on the cell is used here for volume equality; Borelness follows already from the local-chart statement in Part 1.” This is a blueprint wording issue, not a pinned-source erratum or a proof blocker.

**N3 — Generated root.** Lint's sole remaining complaint is the expected stale generated KAM.lean. The orchestrator should regenerate it when landing. It was not edited during this audit.

No suspected defect in a pinned mathematical source was established. No source PDF was needed for the local Mathlib-backed proof obligations. No heartbeat-budget failure or resource override occurred in the audited implementation. Upstream Chart/Algebra warnings are not PP1-7 failures. No frozen declaration, manifest, generated file, design, handoff, or source was edited; no state-changing git command was used.

Final cleanup: removed `.lake/abi-scratch/PP17Audit.lean`; no auditor-created Lean scratch remains. Rechecked the implementation SHA-256 against the entry snapshot and confirmed it unchanged. Final report has eleven declaration rows (ten theorems and one definition); no pending validation fields remain. Final `git diff --check` exits 0. The only repository artifact created by this audit is this report at the user-requested worktree path.
