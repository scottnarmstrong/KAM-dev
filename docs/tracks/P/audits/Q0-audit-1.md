# Q0 independent package audit 1

Date: 2026-10-28. Scope: **only** `KAM/Planetary/Quantitative/Interface.lean`, HEAD `b21a1ea42737c74e005a0896daef0932b4ed3190`.

## Verdict

**PASS WITH NOTES — definitions package only.** Q0 has no provider, theorem, frozen anchor to seal, or existence claim. This does not prove `weak_kam_quantitative`, construct a family, or discharge Q5/Q6. No substantive mathematical defect found in the five declarations. Notes below concern inherited comparison changes and a misleading copied docstring.

Authority: user instructions and Q0-handoff AUDIT FOCUS; `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`; `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`; `docs/tracks/P/design/P11C-LEAN-DESIGN.md` §§1–3, §7 Q0/Q5 rows L195–196 and Appendix A; `/root/code/KAM-inp/docs/tracks/P/design/DESIGN-P11C-design-audit-1.md`; `blueprint-P/parts/p11a5-quantitative-theorem.tex` L72–91 and `p11a1-weak-measure.tex` derivative conventions and index definition L18–46; track P statement conventions. The explicitly requested worktree report destination overrides the generic brief's MAIN destination. Statement-audit skill applied to body/carrier and expanded-field fidelity; these local non-manifest declarations are not frozen anchors.

## Declaration inventory and definition classification

| Node / purpose | Declaration (Interface line) | Verdict | Classification and correspondence |
|---|---|---|---|
| p11a:index-def scalar | `p11c_scalar` L36 | PASS | Literal finite sum `(c·w(y))^rho`, signature L190–191; no fallback or choice. |
| p11a:weak-kam-quantitative domain | `p11c_realDomain` L39 | PASS | Literal real preimage of the max-norm complex action neighborhood `K+2*vartheta`, signature L193–194; angles unrestricted. |
| p11a:sec-q-thm#data / A1–A4 | `QuantitativeInput` L42 | PASS | Literal conjunction of source analytic/finite-type premises; signature L196–213. No assumed iteration, torus, Diophantine or measure conclusion. |
| p11a:weak-kam-quantitative K3 | `p11c_displacement` L62 | PASS WITH NOTES | Literal `min 2^-18 (cDelta*sqrt eps/gamma)`; signature L216–217. Misplaced preceding docstring, see N2. |
| p11a:weak-kam-quantitative K1–K4 | `QuantitativeFamily` L65 | PASS | Data-valued output record, including every generated projection and constructor; signature L219–238. No inhabitant is asserted. |

For **each** row: BODY_MATCH: OK; PUBLIC_CARRIER: OK; WELL_DEFINEDNESS: N/A_LITERAL; CHARACTERIZATION: N/A_LITERAL; CHOICE_INDEPENDENCE: N/A; DEFINITION_VERDICT: PASS. The structure is a literal output specification, not a characterized choice of a unique family. None of these definitions selects arbitrary witnesses or hides proof gaps in default branches. The numerical formula is total using Lean's usual sqrt/division; its quantitative meaning is used under the separate numerical validity and nonnegative-size premises, not claimed for invalid data. Generic N/rho carriers match the signatures; no imported norm instance is replaced.

The complete block from `def p11c_scalar` through `QuantitativeFamily.compact_closed` is **byte-identical** to signature L190–238, not merely type-compatible. The signature SHA-256 is `34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079`; Appendix A extraction is also identical. Interface SHA-256: `d38ab7d56e1299b24d0fb700e1e460a535b1a4a9755079cb8fdfa46cb229be80`. Design hash: `51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36`; quantitative blueprint hash: `f4ea938ec9baf0a280fded708fc7b2bbac4584a6347ad9d49da1291c73ad9b1d`.

Q0 completeness: Q0 owns A1–A4 and family output. Design node table L72 explicitly assigns `zero_case; p11c_zeroGood` to Q5; §7 L195 places the input/family in preceding Q0. Omission of `p11c_zeroGood` is correct. The older sec-q-thm data row L85 says Q1/Q5, but the explicit package row resolves the interface split.

## Expanded logical inputs and outputs

`{N}` is TYPING; `d`, `h`, `f` are source data, not proof assumptions. There are no instance binders or hidden proof fields in `QuantitativeData` (Q1 supplies numerical data and K; validity is separate).

| Expanded QuantitativeInput component | Class | Source / meaning |
|---|---|---|
| `DifferentiableOn ℂ h U` | SOURCE | A1 holomorphy on open action neighborhood |
| `DifferentiableOn ℂ f (strip × U)` | SOURCE | A1 holomorphy on product |
| integer-angle translation invariance of f | SOURCE | A1 period one |
| reality of h on real U | SOURCE | A1 |
| reality of f on real product | SOURCE | A1 |
| each Euclidean-unit c and y∈K has j≤mu and a Euclidean-unit diagonal direction with derivative ≥beta | SOURCE | A2 index definition; includes j=0, extrema attained on compact spheres for valid data |
| orders 1 through mu+1, y in closed Euclidean thickening, all Euclidean-unit-ball tuples bounded by M | SOURCE | A3 full operator derivative bound, not diagonal bound |
| complex gradient derivative operator norm ≤C1 on U | SOURCE | A4 max-to-max Hessian norm; Pi coordinates carry max norm |
| orders 0 through mu, diagonal Euclidean-unit directions, Euclidean target frequency derivative ≤M0 | SOURCE | A4 diagonal norm, including order zero |

Logical premise-component counts: SOURCE 9; STANDING 0; RULED 0; EXCESS 0. Pure data/type binders are described above and do not contribute logical assumptions. Differentiability on the open complex domain supplies the smooth real frequency map; no independent conclusion-shaped smoothness premise is added. Here the local variable `V` denotes the closed Euclidean thickening K_vartheta, not A1's larger real open set; the actual set body agrees with A3/A4.

`QuantitativeFamily` has the following **outputs**, not hypotheses of any theorem in Q0:

| Fields | Source conclusion |
|---|---|
| `good`, `compact`, `subset`, `measure` | K1 compact retained set and measure loss, written as an ENNReal addition inequality |
| `torus`, `freq`, `lattice`, `dio` | K2 analytic primary lattice tori, immersion, Lagrangian property, global HasDerivAt, Diophantine frequency |
| `displacement` | K3 max norm bound |
| `lower`, `upper` | K4 pair max norm constants 1−2^-10 and 1+2^-10 for all angle/action pairs |
| `borel`, `cell_lower`, `compact_closed` | K4 half-open unit-cell image measurable and ≥2^(-2N) times good measure; closed-cell image compact |

`H`, `cDelta`, `eps` are record parameters. Q0 asserts neither a relationship between arbitrary H and h/f nor a uniform choice of cDelta; Q6 must instantiate the record at `realHamiltonian h f` and prove the prescribed constant dependence. K5/K6 budget/power theorems belong to other packages.

Imported `IsLatticeTorus` at `Hamiltonian/Transport.lean` L44–52 has exactly the signature L33–41 body. Its dimension binder is a preceding implicit variable; this is the same elaborated binder as the explicit `{d}` in the excerpt. `PG/Setting.lean` L94 `unitCube` equals signature L43, up to binder naming and `pi` versus `Set.pi`. Disposable rfl probes check these equalities. `Phase` is the frozen product of real Pi coordinate spaces, `actionNbhd` is the strict complex max-neighborhood, `complexStrip` the coordinatewise imaginary strip, `frequencyMap` the real gradient of Re h, `euclid` is sqrt of sum of squared coordinate norms, and `IsDiophantine` uses the l1 integer-mode norm. Their bodies preserve the source carriers and norm distinctions.

## Hygiene and independent checks

All Lean/Lake invocations by this audit were sequential with `LEAN_NUM_THREADS=1` and `nice -n 5` (build niceness through the required wrapper). No resource override, source fix, generated-root regeneration, frozen/manifest edit, or git mutation performed. Scratch probes were confined to `.lake/abi-scratch/` and removed after checking.

1. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-q0 KAM.Planetary.Quantitative.Interface` — **exit 0**. Gate slot 2 acquired at 15:23:49 UTC; `Build completed successfully (9108 jobs).` Only replayed upstream unused-variable warnings: Hamiltonian/Algebra L146, Chart L193, Diophantine L124, Transport L55.

2. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Q0Audit.lean` — **exit 0**. Six exact `rfl` checks passed: the four literal definitions (including QuantitativeInput), imported IsLatticeTorus and imported unitCube against independent signature excerpts. QuantitativeFamily was checked by full source-block byte comparison, including every field. The initial probe exited 1 because its copied displacement definition lacked a noncomputable section; adding that scratch-only section fixed the probe. No production change was needed.

`#print axioms` output for each of `KAM.Planetary.p11c_scalar`, `p11c_realDomain`, `QuantitativeInput`, `p11c_displacement`, `QuantitativeFamily`, `QuantitativeFamily.mk`, `.lattice`, `.dio`, `.cell_lower` was exactly `depends on axioms: [propext, Classical.choice, Quot.sound]`. There are no new public theorems/provider exports; their seal/type probes are N/A.

3. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Quantitative.Interface` — **exit 0**, exact output:

```text
replaying KAM.Planetary.Quantitative.Interface
```

4. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh` — **exit 1**, solely the explicitly permitted generated-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (774 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

5. `git diff --check -- docs/tracks/P/audits/Q0-audit-1.md` and an explicit trailing-whitespace/conflict-marker check on the untracked report — exit 0, no findings. Disposable `Q0Audit.lean` deleted.

Static inspection: Interface is 86 lines, proper copyright/module/public imports/module docstring/exposed public section; no forbidden proof escapes, EuclideanSpace, heartbeat/recursion/synthesis overrides, or new instances. `rg` for the five new names across KAM finds only Interface, including references inside their own bodies. An import-closure script visited 62 project modules, found zero provider modules, and all 24 reachable frozen definitions have manifest state SEALED; no DRAFT_SORRY theorem is imported. Frozen byte/ABI guards are reported with lint below.

## Notes, uncertainty, suspected errata and deviations

**N1 — inherited comparison scope.** Required `git diff inp...HEAD` warns of multiple merge bases and chooses `329a7ec947d310893332f54cb558e7973d15da40`; inp at inspection is `442f6c97a2a78e359368bb82314e4160d8f4ae90`. Its protected-path diff is **not empty**: KAM.lean has seven added imports (SecularSpectrum.TwoPlanets; five TwoScale.Measure modules; WeakKAM.Data). Frozen, manifest and README diffs are empty. HEAD's own commit modifies **only Interface** (`git diff HEAD^ HEAD --name-only`); `git diff --quiet HEAD^ HEAD -- KAM/Frozen manifest KAM.lean README.md` exits 0. Thus the literal branch-wide protected-path check has an inherited generated-root deviation, not a Q0 edit. Unrelated inherited packages are outside this audit.

**N2 — low, misleading signature docstring.** Interface L61 / signature L215 says “Hessian is the max-to-max derivative of the complex gradient, as in A4.” It immediately documents `p11c_displacement`, which is a scalar minimum formula. This is a copied placement error, not a false formula: the comment describes the Hessian clause at Interface L57. Recommend moving it in a separately authorized source/signature update. No correction made during this report-only audit.

No additional suspected mathematical source/blueprint erratum found. The prior design audit's graph-hash and package-DAG notes do not alter Q0 bodies or certify downstream consumers. No frozen theorem status is promoted. The pre-existing untracked Q0-handoff was preserved; this report is the sole lasting audit edit.
