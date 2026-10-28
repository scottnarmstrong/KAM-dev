# Independent S9-T package audit 1

Verdict: **PASS WITH NOTES** for `diagonalize_transport` and `diagonalize_period_one`. The signed S9-T slice is complete; no material proof or statement defect found. This is infrastructure acceptance, not permission to seal a frozen anchor: S9-T has no provider or frozen export and closes no planetary headline.

Audited only `KAM/Planetary/SecularSpectrum/Transport.lean`, HEAD `950705fcff43011546118ff1c8fc7bbcd0508771`, against `git diff inp...HEAD` (`inp` resolved to `d9183adae208ecf2e726620694b69c8168e33006`). The full three-dot diff also contains fifteen S8-Q/S9-Q files; those are outside this audit. The target is one new file, 247 lines (the handoff says 246). The pre-existing untracked handoff was left intact. No production edits, git state changes, generated-root edits or frozen edits were made.

Read the package brief, AGENTS.md, PLAN.md, DECISIONS.md, handoff, P810 Revision 2 design and both design audits, signed `P810Signatures.lean`, relevant P7/P9 graph and blueprint contracts, track P statement, relevant frozen definitions and planetary theorem boundaries, and the actual lift/polar/product/Part 1 suppliers. The user's exact worktree report path overrides the generic brief's main-worktree destination.

## Contract and proof review

All four signed declarations at `/root/code/KAM-inp/.drafts/design/P810Signatures.lean:813–835` match after whitespace normalization: two definition bodies and two theorem signatures. Independent elaboration copied the signed definitions and theorem statements into a fresh namespace, proved the statements by applying the production exports with their explicit binders in order, checked `type_of%` assignments in both directions for all four declarations, and checked both definition equalities by `rfl`. No premise, constant, carrier or conclusion was changed.

Names below are relative to `KAM.Planetary.SecularSpectrum` except `KAM.Planetary.isOpen_polarDom`. The private cuts are included to make the proof boundary reviewable.

| Node / role | Declaration (Transport.lean line) | Verdict | Reason |
|---|---|---|---|
| P7 positive-action polar domain | `KAM.Planetary.isOpen_polarDom` (30) | PASS | Finite intersection of strict inequalities of continuous coordinate projections. No dimension or positivity assumption hidden. |
| P9 lift fast equivariance | `liftInv_add_append` (45) | PASS | Expands the literal inverse lift; correction depends only on actions and slow variables. Valid for every R, even without regularity. |
| P9 integer fast shifts | `liftInv_add_fastShift` (63) | PASS | Specializes the preceding constant translation to `2*pi*k`. |
| P7/P9 action preservation | `fast_snd_add_fastShift` (68) | PASS | Fast shift changes only positions. |
| P7 polar action preservation | `fast_snd_polarMap` (72) | PASS | Literal polar map keeps fast actions. |
| Fin reindexing Q1 | `phaseCast_fullShift` (75) | PASS | Cast permutes the same integer lattice in positions, with zero momenta. |
| Inverse Fin reindexing | `phaseCast_symm_fullShift` (82) | PASS | Exact inverse-cast lattice identity. |
| P9 lift injectivity | `liftInv_injOn` (90) | PASS | Applies the proved left inverse at both points; only SO at their action values is needed. Equality premise is appropriate for an injectivity lemma. |
| P9 physical chart | `rotatedPhysicalChart` (103) | PASS | Exact signed composition; classification below. |
| P9 physical chart domain | `rotatedDomain` (105) | PASS | Exact signed domain; classification below. |
| Private domain before cast | `rotatedDomain'` (110) | PASS | Same domain on Phase(n+n). |
| Private domain reindexing | `rotatedDomain_eq` (113) | PASS | Definitional preimage equality. |
| Private lift-domain membership | `polarMap_mem_liftDomain` (116) | PASS | Fast-action preservation supplies precisely W membership. |
| Private openness | `isOpen_rotatedDomain'` (121) | PASS | Continuity on the open polar/W intersection and preimage of open product-chart domain; does not assume global smoothness of arbitrary R. |
| Private chart composition | `rotatedChart'_isChart` (138) | PASS | Analytic and symplectic compositions with MapsTo guards at both interfaces and scale 1*1=1. |
| Private Q1 | `rotated_shift` (162) | PASS | Full polar shift becomes fast Cartesian shift; lift commutes with that shift; product chart preserves domain and image. |
| Private Q2 | `rotated_inj` (176) | PASS | Product-chart equality gives fast shift; inverse-lift injectivity/equivariance removes lift; positive-radius polar quotient gives full lattice shift. |
| `bpP:p9:diagonalize(d)`, `stepP:p9:d-d` | `diagonalize_transport` (192) | PASS | Exports open domain, analytic symplectic chart and both full-lattice quotient implications. Cast directions are inverse and preserve all integer indices. |
| `stepP:p9:d-d`, Part 1 physical pipeline | `diagonalize_period_one` (232) | PASS | Uses the preceding chart/Q1/Q2 and proved `phys_pipeline`; exact physical H, frequency omega/(2*pi), range equality and unchanged physical time. |

### Graph coverage and the five P7 obligations

Design lines 170–175 map `d-a`, `d-b`, `d-c` and the oscillator dictionary into S9-Q's `diagonalize`; only clause (d) additionally maps to the polar-composed Part 1 transport route. Design row S9-T at line 442 owns `diagonalize_transport`, `diagonalize_period_one` and polar/lift/cast Q1/Q2. The S9-T exports pay that complete transport cut under the explicit signed repair described below. They do not assert that the whole graph node `bpP:p9:diagonalize` is proved by this file. In particular, quadratic identities, translated secular averages, negativity, the uniform fourth-order remainder, the frozen dictionary and its norm comparison remain S9-Q obligations, outside this review.

The design's N2 and lines 303–317 do not license assuming five missing P7 results. Their current boundaries are:

| P7 obligation | Actual supplier / literal conclusion | S9-T disposition |
|---|---|---|
| `bpP:p7:product-chart(b)` | `SecularForm.product_chart`, ProductInterface.lean:196: analytic action Hamiltonian, first/second derivatives and explicit decoupled field | S7-R-owned; not assumed or re-exported here and not needed for geometric transport. |
| `stepP:p7:pc-prod` | `SecularForm.pc_prod`, ProductInterface.lean:259: analytic/symplectic product chart, image, quotient injectivity, analytic local inverse | S7-R-owned; S9-T imports proved Product ingredients directly, including analytic/symplectic and lattice/equality facts. |
| `stepP:p7:pc-dec` | `SecularForm.pc_dec`, ProductInterface.lean:295: Kepler field transport without pair collision guard | S7-R-owned; not a premise here. |
| `stepP:p7:pc-share` | `SecularForm.pc_share`, ProductInterface.lean:276: matched physical-Hamiltonian split and field transport with NoCollision guard | S7-R-owned; not a premise here. Generic torus transport does not assert or require a planetary Hamiltonian split. |
| `bpP:p7:lattice` | `SecularSpectrum.lattice`, ProductInterface.lean:320: literal polar map regularity, symplecticity, MapsTo, radian Q1/Q2 and period-one conformal factor | Existing S7-R aggregate; S9-T uses the underlying Poincare/Lattice lemmas directly and proves the new lifted Q1/Q2. No new missing export in this slice. |

The P7 polar cuts `la-polar`, `la-inv`, `la-per` are supplied by the existing `analyticOnNhd_polarMap`, `polarMap_symplectic`, `polarMap_mapsTo`, `polarDom_shift`, `polarMap_shift`, `polarMap_eq_shift`, `poincareProd_polar_lattice`, and `poincareProd_polar_periodOne_symplectic`/`poincareProd_polar_periodOne_lattice`. The separate `la-ham` is upstream `polar_hamiltonian_split`, not a hidden premise of S9-T. This is a boundary inventory and source inspection, not a new independent audit of S7-R.

### Why no S9-Q import is required

The signed transport theorem assumes only positive physical Data, W open, R analytic on W and R(I) in SO. Geometry and lattice transport hold for any such R; no eigensystem equation or spectral estimate is used. Thus omitting `SecularSpectrum.Diagonalize` is a valid strengthening relative to the spectral setting, and avoids importing results the proof does not need. A consumer chooses the same R as in diagonalization and uses the two packages together. S9-T does not claim to construct R or prove that it diagonalizes the secular matrix.

`hκ` in the period-one theorem is the existing torus of the pulled-back Hamiltonian to be transported, exactly as in the signed conditional transport contract and Part 1. It is not a premise that assumes physical torus existence or any S9-T chart/Q1/Q2 conclusion. Its domain clause also supplies actual domain points when used. No theorem here claims nonemptiness of the chart domain or existence of a KAM torus from physical source data alone.

## Definition classification

- `rotatedPhysicalChart`: exposed noncomputable total map, the literal Poincare product chart after inverse lift, oscillator polar map and Fin cast. Imported square roots and derivatives are total outside their natural domain, but every chart assertion is restricted to the explicit domain where polar actions are positive, the rotation is analytic, and the image lies in the Poincare domain. No fallback or junk value is used by a proof.
- `rotatedDomain`: exposed set given by the three signed guards after reindexing. The last guard is a genuine domain preimage, not an assumed chart or quotient conclusion. The proof establishes openness from regularity. No replacement carrier or stronger hidden domain is introduced.
- Private `rotatedDomain'`: the same conjunction before reindexing; used only to factor the proof. No new structures, abbreviations, instances or other definitions.

## Notes, blueprint defects and deviations

**N1 — minor handoff correction.** The handoff says `SecularSpectrum.lattice` is imported from S7-R/ProductInterface. In fact Transport.lean imports Hamiltonian.Transport, Poincare.Lattice and SecularSpectrum.Lift, and its 81-module KAM import closure contains no ProductInterface. An import-only probe reports `Unknown identifier KAM.Planetary.SecularSpectrum.lattice`. The aggregate exists in ProductInterface.lean:320, but the proof uses the underlying proved components rather than that aggregate. No production change is required; correct the dependency description when recording the receipt.

**N2 — retained blueprint source gap; explicit signed repair, not literal closure of the unrepaired wording.** `blueprint-P/parts/p9-secular-spectrum.tex:143` says “Psi o Phi_varrho^{-1} ... satisfies the lattice compatibility (Q1)–(Q2)” and line 152 concludes “hence z'=z+2*pi*m”. The Cartesian slow coordinates are not full oscillator angles, so the full-lattice transport assertion for the lift-only map is not the statement proved here. The design already records this gap at lines 369–371 and prescribes polar composition and period conversion. S9-T implements exactly that repair: Psi o liftInv R o polarMap o phaseCast, on the signed domain, then omega/(2*pi). Do not mark the unrepaired full Cartesian-lattice wording as literally proved; record the corrected Lean contract and design locator in graph status. No new pinned-paper erratum is alleged and no blueprint or ledger was edited.

No other suspected source defect or implementation deviation found in scope. Empty W and n=0 are allowed by the stronger geometric helper; no existence or positive-volume conclusion is inferred from those cases. No new public short name duplicates a declaration elsewhere under KAM (whole-tree declaration-name scan); all declarations remain under KAM.Planetary or its SecularSpectrum namespace, with no root shadowing.

## Independent validation

Every Lean/Lake invocation was serial, with `LEAN_NUM_THREADS=1` and `nice -n 5`; the targeted build used the required compile gate. No heartbeat, recursion or synthesis budget override. No clean/update/cache command. Probe files and logs were confined to `.lake/abi-scratch/` and removed after recording the results.

1. Targeted build (exit **0**):

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s9t KAM.Planetary.SecularSpectrum.Transport
   ```

   Gate output: `[inp-gate] slot 2 acquired 17:34:34 for KAM.Planetary.SecularSpectrum.Transport`.
   Final output: `Build completed successfully (9127 jobs).`
   Replayed upstream unused-variable warnings occurred in Hamiltonian.Algebra:146, Hamiltonian.Chart:193, Hamiltonian.Diophantine:124, Hamiltonian.Transport:55, Kepler.Energy:106, Poincare.Chart:212/247, and Kepler.Mass:147/157/500/524. No warning or error in Transport.lean. The build wrapper applies `nice -n 5` internally.

2. Exact signature/body and axiom probe (final exit **0**):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S9TAudit.lean
   ```

   No errors or warnings; the complete output was:

   ```text
   'KAM.Planetary.isOpen_polarDom' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.liftInv_add_append' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.liftInv_add_fastShift' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.fast_snd_add_fastShift' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.fast_snd_polarMap' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.phaseCast_fullShift' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.phaseCast_symm_fullShift' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.liftInv_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.diagonalize_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.diagonalize_period_one' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   The probe imported only the target module, opened the owning namespaces, and copied the four signed declarations into `AuditS9T` under `noncomputable section`. The fresh transport proof bodies were respectively `by exact KAM.Planetary.SecularSpectrum.diagonalize_transport D hW hAn hR` and `by exact KAM.Planetary.SecularSpectrum.diagonalize_period_one D hW hAn hR H κ ω hκ hγ hτ hω`. Each fresh and production declaration was assigned to the other's `type_of%`, with both public definition equalities also checked by `rfl`.

   Initial harness run exited 1 because the harness omitted `noncomputable section` and deliberately checked the handoff's unavailable aggregate `lattice`. Adding the section and separating that import-availability check produced the clean run above. These were scratch harness errors, not target failures or changed contracts. No default-heartbeat failure occurred.

3. Kernel replay (exit **0**):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularSpectrum.Transport
   ```

   Complete output:

   ```text
   replaying KAM.Planetary.SecularSpectrum.Transport
   ```

   One invocation, covering the sole in-scope module (including its private proof cuts). No provider module exists to add.

4. Repository lint (exit **1**, solely the explicitly permitted generated-root exception):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (819 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   Module checks, frozen guard and all 144 frozen ABI hashes pass. The brief explicitly permits leaving `KAM.lean` stale; it was not regenerated. No other lint complaint.

5. Read-only diff and static checks:

   ```sh
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff --check inp...HEAD -- KAM/Planetary/SecularSpectrum/Transport.lean
   ```

   Both exited **0**, with no output. Code-mask scan of the target found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or `set_option`. The 247-line file has the copyright/license/authors, `module`, public imports, module docstring and exposed public noncomputable section. A whole-KAM declaration-name scan found zero duplicate short names for all twelve public exports. The recursively inspected 81-module KAM import closure contains no frozen theorem module and no provider, hence no DRAFT_SORRY anchor is imported; frozen definitions are allowed. Provider/frozen type equality and a frozen seal-body test are **not applicable**, because this package exports infrastructure only; the signed-type application probes above are the corresponding applicable check.

Final limitations: no S9-Q or S7-R package verdict is issued here, and no frozen theorem closure or torus-existence theorem is claimed. The only remaining notes in this slice are the handoff import description, the known corrected blueprint transport boundary, and the allowed stale generated root. Report-only scope preserved; all auditor-owned scratch files removed.
