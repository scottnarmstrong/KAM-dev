# P5-FAM independent package audit 1

Verdict: **PASS WITH NOTES for the scoped infrastructure package**. The signed interfaces and proof bodies pass independent review. This package supplies no provider and seals no frozen anchor. In particular, P-G (`KAM.Planetary.properlyDegenerateKAM`) remains `DRAFT_SORRY`; its anchor verdict is **not seal-ready from this package**. The notes concern inherited branch comparison changes, the signed decomposition of the blueprint, and later assembly obligations, not a refuted scoped theorem.

## Scope and authority

Audited HEAD `1005e6394f3da22fb5263f98658969aa2071587c`. Read AGENTS.md, PLAN, DECISIONS, the package-audit brief, the P5-FAM handoff and AUDIT FOCUS, P45 design including Revision 4 and design audits 1–4, the shared signatures, Part 5 blueprint, relevant graph records, Track P statement, frozen P-G and its cylinder-torus/Hamiltonian/frequency consumer definitions. The user's explicit report path overrides the generic brief's main-worktree destination. Only this report is a persistent audit edit.

Implementation scope is exactly:

- `KAM/Planetary/PGAssembly/Family.lean`
- `KAM/Planetary/PGAssembly/FamilyAux.lean`
- `KAM/Planetary/PGAssembly/FamilyFreq.lean`
- `KAM/Planetary/PGAssembly/FamilySigma.lean`

The upstream proofs are interface dependencies, not independently re-audited packages. No external paper search was needed for this local Lean/design audit, and no paper erratum is certified.

`git diff inp...HEAD` was used, including its file inventory and the complete scoped code and protected-path changes. Git warns `multiple merge bases, using 966e014f9ca917f428e12331f0466f34fdd1d44e`; `git merge-base --all inp HEAD` also returns `7413c7f87f6e8cdabb0c32c8683d46b65135ef5e`. The chosen three-dot comparison contains 146 files, 18883 insertions and 801 deletions, including inherited work outside this audit. It is not represented as a four-file-only branch diff. The complete comparison was captured in `/tmp/maud-p5fam-full.diff`.

**Protected-path note.** The required `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**: it contains regenerated root imports and the inherited AMD confinement seal (`by sorry` replaced by the provider application; manifest state `DRAFT_SORRY` changed to `SEALED`). This literal whole-history hygiene condition is not a PASS. Attribution is checked separately: `git diff ef8b6bb8 HEAD --name-only`, using the parent immediately before the P5-FAM commits, lists only the four audited files; the corresponding protected-path diff is empty. No P5-FAM commit changed a protected file. This is why the scoped verdict carries notes, rather than asserting clean whole-branch hygiene.

## Exact signatures and definitions

Shared signature source: `/root/code/KAM-inp/.drafts/design/P45Signatures.lean`, SHA256 `586ed2e3188b154d5cc6d44d3f85b420ef85ddd7faaa2bcbb6d6ca6db7d0f304`.

Direct extraction/comparison finds byte-identical `PGFamily`, and byte-identical declarations including bodies for `physicalTorus`, `PGFamilySpec`, `pgFamily`, `kset`, `rawUnion`. Both theorem headers, `torus_conv` and `frequency_bounds`, are byte-identical through the type before `:=`. Fresh elaboration additionally copies those theorem statements under distinct names with bodies `by exact torus_conv d r mu h` and `by exact frequency_bounds d`; checks `example : type_of% @original := @copy`; and checks each copied definition equals the production definition by `rfl`. Thus implicit parameters, instances, constants and quantifier dependence are checked, not just printed short names. There is no provider/frozen exact-type or seal-body probe to run for this infrastructure slice.

| Node / role | Declaration (namespace `KAM.Planetary`) | Verdict | Reason |
|---|---|---|---|
| `bpP:p5:kset` | `PGFamily` | PASS | Intended total raw action-indexed family; one map field, no assumed specification. |
| `bpP:p5:kset` | `physicalTorus` | PASS | Exact `phi ∘ angleScale (2*pi) ∘ raw`; frozen phase order and physical time retained. |
| `bpP:p5:torus-conv` | `PGFamilySpec` | PASS | Exact signed seven-clause quantitative output; no premise is smuggled into source data. |
| `bpP:p5:torus-conv` | `torus_conv` | PASS | One joint P3 output, all seven clauses proved for its same raw family. |
| `bpP:p5:torus-conv` | `pgFamily` | PASS | Choice from the proved existential, independent of later B. |
| `bpP:p5:kset` | `kset` | PASS | Union of entire physical ranges over B; no angle-cell truncation. |
| `bpP:p5:kset` | `rawUnion` | PASS | Union of entire raw ranges over the same B and chosen family. |
| `stepP:p5:tc-freq` | `frequency_bounds` | PASS | Cw selected from d before r and mu; fast bound Cw, slow bound Cw*mu. |
| `stepP:p5:tc-chart` | local chart data; `fam_ham_eq`; `torus_conv` | PASS | Uses `phi_chart`, location, and exact pulled-back Hamiltonian divided by 2*pi. |
| `stepP:p5:tc-LT` | `fam_lattice`; `torus_conv` | PASS | Transfers lattice-torus clauses using neighbourhood equality of Hamiltonians. |
| `stepP:p5:tc-pipe` | final clause of `torus_conv` | PASS | P1 `cyl_pipeline`, same frequency, whole image in cylinder. |
| tube identity | `fam_realTube_eq` | PASS | Whole-carrier equality for arbitrary D,s; no nonemptiness assumption. |
| openness | `fam_isOpen_realNbhd` | PASS | Union of open balls, including empty/negative-radius cases. |
| angle scaling | `fam_angleScale_injective` | PASS | Nonzero c is the necessary source premise. |
| Hamiltonian derivative congruence | `fam_hvf_congr` | PASS | Requires neighbourhood equality, not only equality at a point. |
| Revision-4 attachment | `fam_cyl_ext` | PASS | Proves both extension-domain and original closed-cylinder membership. |
| Hamiltonian attachment | `fam_ham_eq` | PASS | Uses averaging conjugacy, original-law agreement and H0 bridge. |
| torus transfer | `fam_lattice` | PASS | Retains analytic map, lattice, immersion, Lagrangian and flow clauses. |
| joint Lipschitz adapter | `fam_lipschitz` | PASS | Generic conditional helper with distinct name; derives ordinary norm bound from two defect bounds. |
| sigma-compact intersection | `fam_isSigmaCompact_inter` | PASS | Open subset of finite-dimensional real space has compact exhaustion; intersect with closed C. |
| closedness adapter | `fam_isClosed_forall` | PASS | Arbitrary intersection of closed predicates. |
| closedness adapter | `fam_isClosed_imp` | PASS | Antecedent A is independent of x; case split is legitimate. |
| two-scale closedness | `fam_isClosed_twoScale` | PASS | Closed mode inequalities, no continuity assertion for a varying denominator. |
| ordinary closedness | `fam_isClosed_dio` | PASS | Literal frozen Diophantine mode inequalities. |
| frequency regularity | `fam_continuousOn_realFreq` | PASS | Holomorphic derivative continuity, restricted by real inclusion to the real tube. |
| `bpP:p5:kset` sigma compactness | `fam_isSigmaCompact_D0` | PASS | Open action box intersected with ambient closed sets representing relatively closed frequency constraints. |

Definition classification: the six new objects are one structure (`PGFamily`) and five definitions (`physicalTorus`, `PGFamilySpec`, `pgFamily`, `kset`, `rawUnion`). There is no new abbreviation, instance, norm, measure, carrier or fallback definition. `PGFamilySpec` is an output predicate; `pgFamily` chooses an actual proved witness. The chosen raw map has unconstrained off-D0 values, as its signed total type permits; every property and every later restricted union uses B contained in D0. The total unions themselves are mathematically defined for arbitrary B, without asserting off-D0 torus properties. No proof depends on junk values.

## Adversarial proof and consumer review

**Shared witnesses.** At `Family.lean:67–69`, exactly one application of `two_scale_kam (pg_kam_hyp ...) (Eq.refl ...)` is destructured into i, Phi, K, I0, KC and their joint clauses. `hI0J` proves I0(realFreq J)=J from the same inverse-locus clause, so `hKe` identifies raw(J,theta)=Phi(theta,i J). The Lipschitz proof uses hi and hPhi from that very destructuring. Parameter injectivity uses its hinj after chart Q2 and injectivity of angle scaling. The measure proof uses its hvol, transferring the whole frequency-indexed union to the whole action-indexed union through the same I0. No separately chosen upstream family or independently selected estimates appear. `pgFamily` makes one downstream choice of the complete proved contract.

**Original Hamiltonian and Revision 4.** `FamilyAux.lean:59–85` proves that a physical cylinder point lies in the extension domain and in the closure of the original cylinder. Consequently `fam_ham_eq` supplies the added Revision-4 premise of `PGExtension.agrees`. It does not assert unrestricted original-law agreement outside that cylinder. `fam_lattice` establishes equality throughout an open real tube containing each torus point, then uses eventual equality to transfer fderiv, differentiability and the Hamiltonian field. Thus derivatives are not inferred from a pointwise identity at a single point. Division by 2*pi occurs in the Hamiltonian pullback once; the final period-one frequency is `freq/(2*pi)` once, with unchanged time.

**Completeness versus signed narrowing.** The design node table at lines 190–195 maps exactly kset, torus-conv and tc-chart/LT/pipe/freq to this slice (pgD0 itself is owned upstream by Parameters). All are supplied by the exported contract and the local proof steps above. No unsigned export named after a graph node substitutes a narrowed statement.

The signed `PGFamilySpec` does not itself repeat the blueprint's Diophantine clause. This does not lose the consumer: pgD0 membership already contains twoScaleDiophantine for the exact frozen frequency; P1 `isDiophantine_min_of_mem_twoScale` supplies gamma=min(gamma1,gamma2), and admissibility plus pgScales_k0_pos makes both constants positive. `pgTau=a+b+1` gives the required strict exponent bound. A fresh scratch consumer probe establishes the exact existential gamma/tau clause of frozen `IsCylinderKolmogorovSet` from these existing facts. The cylinder containment is in `IsCylinderTorus` itself, and frequency_bounds supplies the data-only fast/slow constant. No additional theorem premise is needed.

For P5-CT, sigma compactness of D0, Lipschitz control on D0 × unitCube, raw lattice periodicity, parameter injectivity and location are retained. For P5-BU the exact complement inequality and its numerical coefficient are retained. For P5-ST the same chosen family and its joint raw Lipschitz parametrization are retained. For P5-MAIN, whole ranges ensure every point has a witnessing whole torus, while the parameter condition and frequency_bounds provide the remaining frequency predicates. A scratch `choose_spec` probe verifies the signed specification is obtainable for `pgFamily` without a new export. Searches find no current production consumer outside these four files; later CT/BU/ST/MAIN obligations remain separate packages and are not claimed proved here.

`frequency_bounds` uses Cw=(2*pi)^(-1)*(M0+jpBound+jetK2+b*jetK4), a positive data-only bound. It bounds the slow action by 1 using admissibility and the shell, then uses the real/complex frequency identity and the jet derivative bounds. This implements the signed existence of Cw, not the blueprint's particular displayed formula for Cw. The signed interface deliberately leaves the numerical choice existential; every consumer needs the resulting uniform bound rather than that displayed expression. Ordinary Pi/Prod max norms are preserved.

## Hygiene and independent checks

All commands run from `/root/code/KAM-inp-p5fam`. Every Lean/Lake invocation issued by this audit is serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`. No heartbeat, recursion-depth or synthesis-budget override was used. No clean, update, cache download or root regeneration was run.

1. Targeted compile gate (exit **0**):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5fam KAM.Planetary.PGAssembly.Family KAM.Planetary.PGAssembly.FamilyAux KAM.Planetary.PGAssembly.FamilyFreq KAM.Planetary.PGAssembly.FamilySigma
   ```

   Final output: `Build completed successfully (9373 jobs).` The build replayed upstream linter warnings; no elaboration error. Log: `/tmp/maud-p5fam-build.log`.

2. Exact-signature, body, public-theorem axioms and consumer probe (exit **0**):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5FamAudit.lean
   ```

   The completed probe emits exactly the following 17 axiom lines and no errors or warnings; its remaining signature/body/consumer examples elaborate silently. Log: `/tmp/maud-p5fam-probe.log`. Scratch was removed after checking.

```text
'KAM.Planetary.torus_conv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fam_realTube_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fam_isOpen_realNbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fam_angleScale_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fam_hvf_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fam_cyl_ext' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fam_ham_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fam_lattice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fam_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.frequency_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fam_isSigmaCompact_inter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fam_isClosed_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fam_isClosed_imp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fam_isClosed_twoScale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fam_isClosed_dio' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fam_continuousOn_realFreq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fam_isSigmaCompact_D0' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. One kernel-replay invocation (exit **0**):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.Family KAM.Planetary.PGAssembly.FamilyAux KAM.Planetary.PGAssembly.FamilyFreq KAM.Planetary.PGAssembly.FamilySigma
   ```

   Exact output (`/tmp/maud-p5fam-kernel.log`):

```text
replaying KAM.Planetary.PGAssembly.FamilySigma
replaying KAM.Planetary.PGAssembly.FamilyFreq
replaying KAM.Planetary.PGAssembly.FamilyAux
replaying KAM.Planetary.PGAssembly.Family
```

4. Repository lint command:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely for the explicitly permitted stale generated-root exception. Exact output (`/tmp/maud-p5fam-lint.log`):

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (907 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No forbidden-token, line-length, file-length, module-system, frozen-anchor or ABI failure. The generated file was not changed. The ABI subprocess inherits nice priority and LEAN_NUM_THREADS=1 from the lint command and runs after kernel/probe completion.

5. Static checks: 23 explicitly declared public names, including all 17 public theorems, inventoried above. A recursive import scan visits 327 KAM modules, including 55 frozen definition modules, **zero frozen theorem modules and zero providers**. Thus no DRAFT_SORRY theorem import, direct or transitive, enters the package. A declaration-name scan across the remaining KAM files finds no reused short name among these 23 names, including every `fam_` helper; no root namespace definition or global instance is introduced. Forbidden-token/resource-override scan of the four modules returns no matches.

| Module basename | File lines | Maximum Unicode line length |
|---|---:|---:|
| Family | 175 | 100 |
| FamilyAux | 214 | 99 |
| FamilyFreq | 120 | 98 |
| FamilySigma | 158 | 99 |

All four have copyright, `module`, public imports, module docstring and exposed public noncomputable section. The 1500-line cap and 100-character limit both pass. `git diff --check` exits **0**. No tracked production edit was made; the pre-existing untracked handoff is preserved.


## Findings, errata and limits

No blocking defect was found in a scoped public declaration, its source premises, definition body, proof or required consumer interface. No suspected new pinned-paper erratum or frozen-statement defect was identified.

The known Revision-4 blueprint wording defect remains visible at `blueprint-P/parts/p5-pg-assembly.tex:30`, “P~ = P at real points” throughout the extension tube, and its periodicity argument at line 35. Read literally this prescribes uncontrolled original values outside the closed cylinder. Revision 4 narrows agreement to original closed-cylinder points. The scoped proof correctly supplies that premise, as above; it introduces no new deviation. This is a pre-existing project-blueprint defect, not an independently established error in CP10/CP11.

The three-dot protected-path condition and generated-root lint exception must remain visible to the landing orchestrator. They are not repaired during this read-only audit. The package's successful checks do not prove later assembly, freeze a new statement, or seal P-G.

Final integrity: all four scoped SHA256 fingerprints rechecked unchanged; `git diff --check` exits 0; only this report and the pre-existing handoff are untracked. Audit probe deleted; lint removed its own ABI scratch file. No production source, frozen file, manifest, generated root, README, signature source or handoff was edited.
