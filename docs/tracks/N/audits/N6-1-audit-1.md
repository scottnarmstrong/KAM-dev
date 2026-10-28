# N6-1 independent package audit 1

**Verdict: PASS for N6-1** (`p6#data`, `setting`, `lipschitz`, `divisor`). The implementation matches design v2 and the audited blueprint contracts. No material mathematical or statement-fidelity finding was identified. This is shared infrastructure: there is **no frozen theorem anchor or provider in this package**, so “seal-ready” is inapplicable; no N/I/P headline theorem is certified by this report.

Date: 2026-10-28. Scope: only `KAM/Nekhoroshev/NormalForm/Setting.lean`. This report is intentionally written in `/root/code/KAM-inp-n61`, following the user's explicit destination, which overrides the generic brief's main-worktree destination.

## Snapshot and method

- HEAD: `2fd6a16af38753b60db07cc952737d53b1bef19d`.
- `inp` observed: `f45c6617a5e134742856494cfee2a6f95ea2d1b6`.
- `git diff inp...HEAD`: exactly one added file, 179 lines, the audited module.
- Initial working tree: only untracked `docs/tracks/N/audits/N6-1-handoff.md`; preserved.
- Permission envelope: read-only source inspection, targeted serialized checks, transient probes exclusively in `.lake/abi-scratch/`, and this report. No source repair, git mutation, dependency edits, or delegation.
- Focused source-correspondence audit: independently reconstructed the blueprint contracts, compared every new public declaration, read every proof, and performed a second adversarial pass over possible failure cases before the hygiene closeout. Prior design audits supplied context, not proof-body certification.

Inputs frozen for this review:

| Input | SHA-256 |
|---|---|
| `KAM/Nekhoroshev/NormalForm/Setting.lean` | `c5b5cea712c16ed67bca33e0cad5ed7939c30905b4cb7c3ff6359b8f4c9ae841` |
| `blueprint-N/parts/p6-normal-form.tex` | `1c9c5e640ba0825040f1a2ad1de3aac9b38df9dbfcc1b280245ed53c3f2533ac` |
| `docs/tracks/N/design/PART67-LEAN-DESIGN.md` | `9376271a6f311a2fa9bdf530680433ae2b759a84747a05aa1aa8ad07d2e53be2` |
| `/root/code/KAM-inp/.drafts/design/NPart67Signatures.lean` | `c588818b1772d3f7e106aac256b8207623c8a142cf40ef0e778f0507b1945c9f` |
| `docs/tracks/N/design/DESIGN-N67-design-audit-1.md` | `0105c58da5e8821f8ba28499a26834478f4cffd2cfab740fcda0f824101529f7` |
| `docs/tracks/N/design/DESIGN-N67-design-audit-2.md` | `53d7b97ad2c50290843c2f0a2dc4e6adf69d270e710727a7adbc0a0a11a546ea` |
| `docs/tracks/N/audits/N6-1-handoff.md` | `da3792fbdec7e00d35f3170b2d4e1cda682ef7db4cf8f992a018655ab4bbb963` |
| `docs/tracks/N/statement.md` | `f73137a6125d6c7f06714c62815ba8f0a4478f156ad5c2453e3bc7e1e05380a3` |
| `manifest/frozen-anchors.json` | `5d8d31f1cc70c3cc67375ab28562e4fd4280215c7455dd329004c4dcd7a2f6fa` |

Read the repository rules, PLAN, DECISIONS, package audit brief, design §0/§1/§3.1/§4/§7.1 and Appendix A, both design audits, and the track statement. Mathematical authority for this package is the supplied blueprint and design signatures; no fresh audit of the original Pöschel PDF or of other packages is claimed.

## Declaration ledger

All names below are in `KAM.NormalForm`. Line references are to the hashed module above; blueprint references are to the hashed Part 6 source.

| Node | Declaration / line | Verdict | Reason |
|---|---|---|---|
| `p6#data` | `zBall`, 34 | PASS | Exact ℓ¹ cut-off `modeSize k ≤ K`; blueprint L11. |
| `p6#data` | `freq`, 37 | PASS | Coordinate differential `Dh(I)eᵢ` over ℂ, with Pi max-norm carrier. |
| `p6#data` | `dotC`, 40 | PASS | Bilinear integer/complex pairing, no complex conjugation. |
| `p6#data` | `conjExp`, 43 | PASS | Exactly `p/(p-1)`; divisor use has `p>1`. |
| `setting` | `IsNonresonant`, 46 | PASS | N1 at base points `I∈D`, and exactly `Z_K ∖ Λ`; blueprint L30–32. |
| `setting` | `FreqLipschitz`, 51 | PASS | N2 retains both base-point and local-distance restrictions; blueprint L33. |
| `setting` | `DivisorBound`, 55 | PASS | Uniform lower bound on the supplied set, same modes and frequency; no extra result packaged as a premise. |
| `setting` | `IsDecomp`, 61 | PASS | Finite sum, width order, analytic class and summable weighted bounds; exact v2 structure. |
| `setting` | `starNorm`, 71 | PASS | Exact half-sum of radius ratios weighted by supplied bounds; blueprint L36–37 and design bound convention. |
| helper | `norm_dotC_le`, 74 | PASS | Unconditional ℓ¹/max dual estimate used in blueprint L18 and divisor proof L55. |
| helper | `differentiableAt_freq`, 84 | PASS | Derives frequency regularity from holomorphy on an open set; assumes no derivative regularity conclusion. |
| `lipschitz` | `lipschitz`, 93 | PASS | Exact v2 operator-norm statement; segment mean-value proof matches blueprint L43–47. |
| `lipschitz` | `lipschitz_entries`, 107 | PASS | Exact v2 entrywise Hessian statement, constant precisely `n*Mc`. |
| `divisor` | `divisor`, 148 | PASS | Exact v2 statement: both `α-KLr` and `α/q` bounds on the full neighbourhood. |

A mechanical comparison removed whitespace and, for theorems, proof bodies. Output: `MATCH` for all twelve planned declarations (nine definitions/structures and three theorems). The only definition formatting change is the wrapped `IsNonresonant` signature. No binder, instance, constant dependence, coefficient, or conclusion changed.

## Binder and hypothesis audit

TYPING means carrier/data binders; STANDING means the blueprint setting at L11 and L30; SOURCE means an explicit estimate or hypothesis of the lemma. No RULED or EXCESS input occurs. The table includes implicit binders inherited from `variable {n : ℕ}`. No theorem has instance binders.

| Theorem | Binder | Bin | Evidence |
|---|---|---|---|
| `norm_dotC_le` | `n : ℕ` | TYPING | Finite coordinate dimension, arbitrary in blueprint L9. |
| same | `k : Fin n → ℤ` | TYPING | Integer mode, blueprint L18. |
| same | `v : Fin n → ℂ` | TYPING | Complex vector, blueprint L18. |
| `differentiableAt_freq` | `n : ℕ` | TYPING | Finite coordinate dimension. |
| same | `h : ℂⁿ → ℂ` | TYPING | Scalar integrable Hamiltonian. |
| same | `U : Set ℂⁿ` | TYPING | Generalized open neighbourhood. |
| same | `hU : IsOpen U` | SOURCE | Open holomorphic domain; helper generalizes `V_rD`. |
| same | `hh : DifferentiableOn ℂ h U` | SOURCE | Holomorphy, blueprint L30. |
| same | `I : ℂⁿ` | TYPING | Evaluation point. |
| same | `hI : I ∈ U` | SOURCE | Point in the holomorphic domain. |
| `lipschitz` | `n : ℕ` | TYPING | Blueprint L9. |
| same | `D : Set ℂⁿ` | TYPING | Blueprint L30. |
| same | `r : ℝ` | TYPING | Neighbourhood radius. |
| same | `L : ℝ` | TYPING | Prescribed bound, no existential constant. |
| same | `h : ℂⁿ → ℂ` | TYPING | Blueprint L30. |
| same | `hh` | STANDING | Holomorphy of h on `V_rD`, L30; regularity of ω is proved. |
| same | `hD2` | SOURCE | For every `I∈V_rD`, `‖Dω(I)‖≤L`, L43. |
| `lipschitz_entries` | `n : ℕ` | TYPING | Blueprint L9. |
| same | `D : Set ℂⁿ` | TYPING | Blueprint L30. |
| same | `r : ℝ` | TYPING | Neighbourhood radius. |
| same | `Mc : ℝ` | TYPING | Prescribed entrywise bound. |
| same | `h : ℂⁿ → ℂ` | TYPING | Blueprint L30. |
| same | `hh` | STANDING | Holomorphy of h on `V_rD`, L30. |
| same | `hD2` | SOURCE | For every `I∈V_rD` and every coordinate pair `i,j`, the displayed Hessian entry has norm ≤Mc; L43. |
| `divisor` | `n : ℕ` | TYPING | Arbitrary finite dimension. |
| same | `D : Set ℂⁿ` | TYPING | Arbitrary base set. |
| same | `r : ℝ` | TYPING | Neighbourhood radius. |
| same | `K : ℝ` | TYPING | Cut-off. |
| same | `α : ℝ` | TYPING | Nonresonance threshold. |
| same | `L : ℝ` | TYPING | Lipschitz bound. |
| same | `p : ℝ` | TYPING | Conjugate-exponent parameter. |
| same | `Λ : Set ℤⁿ` | TYPING | Arbitrary resonance set, no sublattice requirement. |
| same | `h : ℂⁿ → ℂ` | TYPING | Frequency's Hamiltonian. |
| same | `hp : 1 < p` | STANDING | Blueprint L11. |
| same | `hα : 0 < α` | STANDING | Blueprint L30. |
| same | `hK : 0 ≤ K` | STANDING | Blueprint L30. |
| same | `hL : 0 ≤ L` | STANDING | Blueprint L30. |
| same | `hnr` | SOURCE | N1, L32 and L51; expanded below. |
| same | `hlip` | SOURCE | N2, L33 and L51; expanded below. |
| same | `hrad : K*L*r ≤ α/p` | SOURCE | Exact radius condition, L51. |

Counts by theorem `(SOURCE, STANDING, TYPING, RULED, EXCESS)`:
`norm_dotC_le` = `(0,0,3,0,0)`; `differentiableAt_freq` = `(3,0,4,0,0)`;
`lipschitz` = `(1,1,5,0,0)`; `lipschitz_entries` = `(1,1,5,0,0)`;
`divisor` = `(3,4,9,0,0)`.

Complete logical expansion of bundled theorem premises:

- `hnr`: `∀ I ∈ D, ∀ k ∈ {k | ∑i |(k i : ℝ)| ≤ K} ∖ Λ, α ≤ ‖∑i (k i : ℂ) * (fderiv ℂ h I (Pi.single i 1))‖`. Both domain membership guards and the inequality are SOURCE (N1); `I,k` are TYPING. No regularity or divisor-on-the-neighbourhood result is hidden here.
- `hlip`: `∀ I₀ ∈ D, ∀ I, (∃ J ∈ D, ‖I-J‖<r) → ‖I-I₀‖<r → ‖freq h I-freq h I₀‖≤L*‖I-I₀‖`. All four restrictions/estimate are SOURCE (N2); quantified points are TYPING. Membership's witness is the domain definition, not an assumed proof step.
- `hh` is ordinary Mathlib complex differentiability on the stated open neighbourhood; it does not assume differentiability of `freq h`.
- The `hD2` inputs are exactly the operator bound and entry bound displayed in their declarations; no other project-owned alias is hidden in them.

The proofs omit source assumptions they do not need: no positivity of r or holomorphy premise is needed by `divisor` beyond its N1/N2 input, and `lipschitz` does not separately require positivity of r or L. These are stronger statements, exactly as designed, with empty-neighbourhood cases harmless.

## Definition classification

All nine new definition/structure declarations are **literal formulas or literal source-data predicates**, not objects selected by characterization. No choice construction occurs.

| Declaration | Full-body/carrier assessment |
|---|---|
| `zBall` | Literal finite-lattice ℓ¹ inequality, using `modeSize = ∑i |(k i : ℝ)|`. |
| `freq` | Literal coordinate derivative. Standard total `fderiv` is used; every analytic application proves differentiability on the domain first. No new fallback branch. |
| `dotC` | Literal finite sum, valid also in dimension zero. |
| `conjExp` | Literal real rational expression; theorem use is restricted to `p>1`, where its denominator is nonzero. |
| `IsNonresonant` | Literal N1; threshold on D, not a neighbourhood substituted for D. |
| `FreqLipschitz` | Literal N2 with both point sets and strict radius condition. |
| `DivisorBound` | Literal pointwise lower-divisor predicate; it names the conclusion but is never smuggled into its source-form proof as a hypothesis. |
| `IsDecomp` | Five literal fields: global sum equality, two width inequalities, class membership and weighted bounds. `InClass` expands to holomorphy and period-one periodicity; `WBound` to summability AND the coefficient sum bound for every action point. Global sum equality follows the v2 total-function representation; it specifies no chosen extension. |
| `starNorm` | Literal finite sum using the supplied `Mj` bounds, as explicitly authorized by design §0.3. On admissible widths its denominators are positive. It is not claimed to be the intrinsic norm or independent of decomposition/bounds. |

For **each** row: `BODY_MATCH: OK`; `PUBLIC_CARRIER: OK`; `WELL_DEFINEDNESS: N/A_LITERAL`; `CHARACTERIZATION: N/A_LITERAL`; `CHOICE_INDEPENDENCE: N/A`; `DEFINITION_VERDICT: PASS`.
The bound representation is intentional: using upper bounds for component norms changes the numeric value of `starNorm` when bounds are loose; this is the documented design interface, and the sharp norm instance recovers the blueprint expression. No theorem in N6-1 asserts an equality for loose bounds.

## Proof and adversarial review

- `norm_dotC_le`: triangle inequality, complex integer-cast norm, and the Pi coordinate bound yield precisely ℓ¹(mode) times max(vector). No Euclidean factor or conjugation is inserted.
- `differentiableAt_freq`: applies proved `holomorphic_regularity` on an open set, evaluates the continuous-linear-map derivative at each basis vector, and assembles coordinates. It supplies the regularity needed by mean value and `fderiv_pi`.
- `lipschitz`: `ball I₀ r ⊆ polyNbhd D r` uses the actual witness `I₀∈D`; both endpoints belong to this convex ball. The endpoint restriction gives `r>0` whenever needed. D itself need not be convex or open.
- `lipschitz_entries`: for n>0, one diagonal entry bound derives `Mc≥0`; the finite basis expansion and triangle inequality give `‖Dω v‖∞≤n Mc ‖v‖∞`. This proves the conversion, rather than assuming an operator bound. For n=0, the operator is zero and the proof separately establishes the bound without assuming `Mc≥0`. Hessian index order matches the exact signature; no symmetry assumption is needed for the norm bound.
- `divisor`: the neighbourhood witness supplies a base point; N1, N2, and the proved pairing estimate bound the perturbation by `K L r`. Reverse triangle yields `α-KLr`; exact algebra `α/conjExp p=α-α/p` and the radius premise yield the second threshold. Neither bound is assumed in disguise.

Second-pass refutation targets: arbitrary/disconnected D; empty D; r≤0; n=0; K=0; Λ containing or omitting zero; negative Mc in dimension zero; p approaching 1 from above; and the possibility of an unwanted 2π factor. None refutes the statements: empty neighbourhoods are vacuous; n=0 is explicitly handled; zero mode excluded by Λ or ruled out by positive nonresonance at a base point; q identity needs only p>1; no Fourier differentiation occurs in these pairing estimates. No material finding survived this pass. No independent external reviewer was delegated.

## Import and quarantine audit

Recursive project import inventory: 33 project modules, seven frozen modules, all **SEALED definitions** in the manifest:
`ActionNbhd`, `ComplexStrip`, `HamiltonianVectorField`, `HamiltonianVectorFieldC`, `IsPrimaryOnStrip`, `IsRealOnReals`, `OmegaZero` (all under `KAM.Frozen.Defs`). Their definitions were read; no frozen theorem or provider is reachable through the project import closure. Direct imports are exactly `KAM.Weighted.Domains`, `.Norm`, `.Coefficients`, and `KAM.Canonical.Setting`.

Semantic dependencies relevant here were checked at their bodies: `polyNbhd` is existential max-distance <r; `modeSize` is ℓ¹; `InClass` is holomorphy plus period-one periodicity; `WBound` includes actual summability and a sum bound. Standard-foundation axiom checks below also cover the two new helpers.

## Verification receipts

All Lean/lake invocations in this audit are sequential and use `LEAN_NUM_THREADS=1`, with `nice -n 5` (inherited for the lint ABI subprocess). The targeted build used the required compile gate. Other users' processes were neither controlled nor terminated.

1. Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n61 KAM.Nekhoroshev.NormalForm.Setting
```

Output: `[inp-gate] slot 2 acquired 05:59:18 for KAM.Nekhoroshev.NormalForm.Setting`; `Build completed successfully (3162 jobs).` Exit **0**. No rebuild-from-scratch, clean, update, or cache command was run.

2. Exact-type/body probe and all public theorem axioms:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N61Audit.lean
```

The probe copies signature-file A.1 into a fresh namespace, replaces the three `sorry` bodies by exact applications of the implementation, checks all eight function/predicate equations by `rfl`, and checks both directions of the five-field `IsDecomp` correspondence. It contains no sorry. The two extra helpers are included in the axiom census. Exit **0**, no diagnostics beyond:

```text
'KAM.NormalForm.norm_dotC_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.differentiableAt_freq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.lipschitz_entries' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.divisor' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Probe SHA-256: `329f08752473ceeff51f1c4f67395f5daeb90465265e24d951a4f1c83ac4820e`.

3. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.NormalForm.Setting > .lake/abi-scratch/N61-kernel.log 2>&1
```

Exit **0**. Complete output:

```text
replaying KAM.Nekhoroshev.NormalForm.Setting
```

One invocation replays the sole audited module, which contains all five new public theorems.

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh > .lake/abi-scratch/N61-lint.log 2>&1
```

Exit **1**, solely the **explicitly allowed stale generated root**. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (416 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No other lint defect. The root file was left untouched as required. This is a scoped hygiene pass under the brief's stated exception, not an unqualified exit-0 lint claim.

5. Mechanical hygiene:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: **empty**, exit 0.
- `git diff --check inp...HEAD`: **empty**, exit 0.
- `rg -n '\b(sorry|admit|axiom|unsafe|opaque)\b|set_option|EuclideanSpace' KAM/Nekhoroshev/NormalForm/Setting.lean`: **no matches**, exit 1 (normal rg no-match status).
- 179 physical lines (stronger than the ≤1500 code-line requirement); maximum line length **99** Unicode characters.
- Copyright, `module`, public imports, module docstring and `@[expose] public noncomputable section` present. Definitions are exposed through that section.

## Findings, errata, deviations, limits

No suspected blueprint/source defect identified in the scoped nodes. No new mathematical deviation or unauthorized premise found. The handoff's module-path note is confirmed: the design says `KAM/NormalForm/Setting`, while the assigned implementation is `KAM/Nekhoroshev/NormalForm/Setting`; namespace and statements agree. Downstream code must import `KAM.Nekhoroshev.NormalForm.Setting`. This is a documented packaging note, not a theorem defect.

No original-source PDF audit, downstream consumer implementation audit, or other package/root closure is claimed. Frozen provider/type equality and seal-body probes are N/A because no frozen anchor is implemented by N6-1. Only the module above is certified; this report does not promote a design-only theorem elsewhere.

Closeout: all fourteen public declaration rows classified; no EXCESS premise, unresolved finding, or scoped source defect; targeted build, exact-type/definition probes, five axiom checks and kernel replay passed; lint has only the allowed stale-root exception. Auditor-created probe and captured logs were removed from `.lake/abi-scratch/`. Final source hash and diff checks were repeated; the sole auditor-created repository artifact is this report. No source repair or new errata/deviation was introduced.

**Final verdict: PASS for the four N6-1 nodes.** The documented import-path note and expected stale generated root require ordinary integration handling; no mathematical change is requested.
