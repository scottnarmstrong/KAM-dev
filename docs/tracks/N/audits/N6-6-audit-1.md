# N6-6 independent package audit 1

**Overall verdict: PASS WITH NOTES.** Both requested parts of `bpN:p6:iterative-direct`, (c) and (d), pass statement, proof, definition, import, axiom and kernel checks. The notes concern repository-wide lint outside the audited file. This is an infrastructure-package verdict; there is no frozen theorem/provider pair to seal in N6-6, and no headline or whole Iterative Lemma closure is claimed.

## Scope and snapshot

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-n66`. Authority: the package audit brief at `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, this worktree's AGENTS/PLAN/DECISIONS, `docs/tracks/N/audits/N6-6-handoff.md` AUDIT FOCUS, design v2 and its two design audits, and `blueprint-N/parts/p6-normal-form.tex`. Applied the lean-statement-audit workflow to this non-frozen helper package. The user's exact worktree report path overrides the brief's generic main-worktree destination.

| Snapshot input | Revision / SHA-256 |
|---|---|
| HEAD | `ae47845cb5000d13aadb3a9eaba94d704d0f5c19` |
| `inp` observed at intake | `89f791e7f22039b1a5a3ac75858cf8484e971d00` |
| Merge base selected by requested Git comparison | `f1451bf24a5bccd5dace39c45a9687c724360d0e` |
| `KAM/Nekhoroshev/NormalForm/IterativeRemainder.lean` | `090c53590ac5da83669515b567c1a2eeec7aa4aec000d8cc41e231b106a3cd45` |
| `docs/tracks/N/design/PART67-LEAN-DESIGN.md` | `9376271a6f311a2fa9bdf530680433ae2b759a84747a05aa1aa8ad07d2e53be2` |
| `blueprint-N/parts/p6-normal-form.tex` | `1c9c5e640ba0825040f1a2ad1de3aac9b38df9dbfcc1b280245ed53c3f2533ac` |
| `/root/code/KAM-inp/.drafts/design/NPart67Signatures.lean` | `c588818b1772d3f7e106aac256b8207623c8a142cf40ef0e778f0507b1945c9f` |

`git diff inp...HEAD` reports two new Lean files: inherited `IterativeMap.lean` (205 lines) and the audited `IterativeRemainder.lean` (429 lines). Git warns that there are multiple merge bases and identifies the selected base above. Only `IterativeRemainder.lean` is audited, per AUDIT FOCUS; inherited implementations are inspected only where needed to establish meaning and actual dependency consumption. The handoff was already untracked at intake and is preserved.

## Declaration ledger

Names below have prefix `KAM.NormalForm.`. Line numbers refer to the audited file. Every new public declaration is listed; private elementary support lemmas were also inspected.

| Node / role | Lean declaration | Verdict | Evidence |
|---|---|---|---|
| `stepN:p6:it-taylor`, composition data | `IterHyp.compose` (140) | PASS | Derives every ComposeData field from IterHyp and homological_direct; `eta = 2u ≤ 1/2`, with no composition assumption added. |
| Flow identification | `IterHyp.iterMap_eq` (155) | PASS | Definitional equality of the actual time-one flow and ComposeData.omega; no replacement map. |
| `stepN:p6:it-taylor`, homological bracket | `IterHyp.bracket_eq` (161) | PASS | `{h∘snd,φ}=ξ-T_K f` from the homological equation and antisymmetry, at every point of Dom r s. |
| Integrable Hamiltonian class | `IterHyp.hClass` (172) | PASS | Holomorphy of h on the action neighbourhood and angle independence give the required class on the smaller domain. |
| `stepN:p6:it-integrand`, literal integrand | `IterHyp.remIntegrand` (178) | PASS | Exactly the transform integrand `{(1-t){h∘snd,φ}+(g+T_K f),φ}`. Definition classification below. |
| `stepN:p6:it-integrand` | `IterHyp.integrand` (185) | PASS | Proves class, explicit weighted bound, joint continuity of values and of the complex derivative. No integral/continuity obligation is assumed. |
| `stepN:p6:it-decomp`, `it-terms` | `IterHyp.iterF_class_bound` (315) | PASS | Proves smaller-domain class and exact remainder estimate using transform, composition_integral, truncation_tail and composition_series. |
| `bpN:p6:iterative-direct` (c), hence source-form (c) through inherited iterHyp_of_source | `iterative_direct_c` (405) | PASS WITH NOTES | Exact v2 signature; identity, class/bound of ξ and class of f₊. Repository lint notes only. |
| `bpN:p6:iterative-direct` (d), hence source-form (d) through inherited iterHyp_of_source | `iterative_direct_d` (418) | PASS WITH NOTES | Exact v2 signature, with geometric widths, 2π, 2/e, exponential tail and inverse factor unchanged. Repository lint notes only. |

Private support: `inClass_mono'` (38), `wbound_zero` (43), `decomp_wbound` (51), `poissonBracket_lin` (77), `poissonBracket_congr` (95), `isDecomp_snoc` (104), `starNorm_snoc` (120). These prove restriction, zero/sum bounds, bracket linearity/locality, and the finite-decomposition extension and its exact star weight. They add no source-facing assumptions or standalone blueprint claims.

## Statement and binder audit

The raw statements in blueprint p6 (Iterative Lemma (c),(d), lines 100–107; direct-divisor corollary, lines 129–139), design §A.4 (792–805), and supplied signature file agree. Mechanical comparison of each complete theorem header, from `theorem` through the type and before `:=`, returned:

```text
iterative_direct_c DESIGN_HEADER_IDENTICAL True SIGNATURE_HEADER_IDENTICAL True
iterative_direct_d DESIGN_HEADER_IDENTICAL True SIGNATURE_HEADER_IDENTICAL True
```

The transient probe copied each design header under a fresh name, supplied the actual export with `by exact iterative_direct_c H` / `by exact iterative_direct_d H`, and also checked `example : type_of% @audit_iterative_direct_c := @iterative_direct_c` (and d). It elaborated at default settings. No frozen/provider ABI probe applies: these are ordinary infrastructure theorems, not registered provider exports.

The implicit data binders of both targets are separately accounted for below. All are TYPING (blueprint p6 setting and Iterative Lemma, design §A.4); none is an assumed estimate. Their order follows the Lean variable context and dependencies.

| Binder | Classification | Meaning / source |
|---|---|---|
| `n` | TYPING | Arbitrary dimension, including zero; p6 setting. |
| `D` | TYPING | Arbitrary complex action set. |
| `r` | TYPING | Action radius. |
| `s` | TYPING | Geometric angle strip width. |
| `ρ` | TYPING | Action loss. |
| `σ` | TYPING | Angle loss. |
| `K` | TYPING | Real Fourier cutoff. |
| `α` | TYPING | Divisor scale. |
| `p` | TYPING | Hölder parameter; q is p/(p-1). |
| `δ` | TYPING | Explicit upper bound for the perturbation norm. |
| `Λ` | TYPING | Arbitrary subset of integer modes. |
| `h` | TYPING | Complex action function. |
| `g` | TYPING | Complex phase function. |
| `f` | TYPING | Complex phase perturbation. |
| `N` | TYPING | Finite decomposition length. |
| `gj` | TYPING | Family of decomposition functions. |
| `rj` | TYPING | Family of action widths. |
| `sj` | TYPING | Family of angle widths. |
| `Mj` | TYPING | Family of finite norm upper bounds. |

The only explicit input is `H : IterHyp ...`. Expanding it, its project-owned logical bundles, and their conjunctions gives the following leaf obligations. Source rows refer to p6 setting (finite decomposition), Iterative Lemma hypotheses, and the direct-divisor corollary. Finite norm bounds may replace exact norm values monotonically, as specified in design v2. No norm, generator bound, flow estimate, remainder bound, or integral continuity conclusion is imported as a hypothesis.

| Expanded input | Bin | Source / reason |
|---|---|---|
| `H.hp : 1 < p` | SOURCE | p6 Hölder convention / Iterative Lemma. |
| `H.hα : 0 < α` | SOURCE | p6 direct-divisor statement. |
| `H.hK : 0 ≤ K` | SOURCE | p6 cutoff setting. |
| `H.hs : 0 < s` | SOURCE | Iterative Lemma. |
| `H.hρ : 0 < ρ` | SOURCE | Iterative Lemma. |
| `H.hρr : 2*ρ < r` | SOURCE | Iterative Lemma. |
| `H.hσ : 0 < σ` | SOURCE | Iterative Lemma. |
| `H.hσs : 2*σ < s` | SOURCE | Iterative Lemma. |
| `H.h_holo` | SOURCE | h holomorphic on V_r D. |
| `H.divisor`, expanded as ∀ I ∈ V_r D, ∀ k ∈ Z_K ∖ Λ, α/q ≤ ‖k·freq h I‖ | SOURCE | Exactly (N-dir), not a remainder conclusion. |
| `H.decomp.eq_sum` | SOURCE | Finite decomposition g=Σ gj; global extension equality is the specified design representation. |
| `H.decomp.r_le` | SOURCE | Every rj ≥ r. |
| `H.decomp.s_le` | SOURCE | Every sj ≥ s. |
| `H.decomp.inClass.differentiableOn` (for each j) | SOURCE | Each gj holomorphic on its own domain. |
| `H.decomp.inClass.periodic` (for each j) | SOURCE | Each gj period one in each angle. |
| `H.decomp.bound.WSummable` (for every j,I in V_rj D) | SOURCE | Finite weighted Fourier norm, summability explicitly retained. |
| `H.decomp.bound.wsum_le` (for every j,I in V_rj D) | SOURCE | Weighted sum ≤ Mj. |
| `H.f_class.differentiableOn` | SOURCE | f holomorphic on Dom r s. |
| `H.f_class.periodic` | SOURCE | f period one in each angle. |
| `H.f_bound.WSummable` (for every I in V_r D) | SOURCE | f has finite weighted Fourier norm. |
| `H.f_bound.wsum_le` (for every I in V_r D) | SOURCE | Weighted sum ≤ δ. |
| `H.δ_nonneg : 0 ≤ δ` | SOURCE | Nonnegative norm-bound parameter; explicit even for empty D. |
| `H.δ_small` | SOURCE | δ ≤ 2παρσ/(4q), exactly the adopted smallness. |

Per target counts: TYPING 19; SOURCE 23 expanded logical fields; STANDING 0; RULED 0; EXCESS 0. All six public helper theorems take the same source bundle; `iterMap_eq` additionally has a point z as typing data, and `bracket_eq` has a point z and its explicit domain-membership premise (the local identity's SOURCE premise). Their derived conclusions are proved from H, not bundled into H. There are no instance hypotheses hiding an estimate.

`WBound` expands to summability and the coefficient sum bound at every action point; no use of the junk value of a nonsummable `tsum` occurs. Carriers are `Fin n → ℂ`, Fourier modes `Fin n → ℤ`, max norms, period one, weight exp(2πs|k|₁). The estimate is precisely

```text
(1 - 2u)⁻¹ * (2q/(e(2πα)ρσ) * (starNorm + δ) + exp(-2πKσ)) * δ.
```

There are no existential constants with enlarged dependence. Part (c)'s bound on `homRes` expresses the bound on `iterG-g` because `iterG = g+homRes` literally. Holomorphy of homRes on the original domain is also retained. The inherited `iterHyp_of_source` supplies H from the original nonresonance/Lipschitz hypotheses; it is outside this package's proof audit. Part (e) and later normal-form assembly remain outside scope.

## Definition classification

Exactly one new definition, no new abbrev or structure: `KAM.NormalForm.IterHyp.remIntegrand` at lines 178–182. It is a literal formula on all declared real t and complex phase points, using the actual `homGen`, actual bracket, actual g and actual truncation. It contains no choice, conditional, zero/default branch or surrogate object. Interval/domain restrictions belong to its estimates, not to a hidden branch in its body.

```text
BODY_MATCH: OK
PUBLIC_CARRIER: OK
WELL_DEFINEDNESS: N/A_LITERAL
CHARACTERIZATION: N/A_LITERAL
CHOICE_INDEPENDENCE: N/A
DEFINITION_VERDICT: PASS
```

The inherited meanings of iterMap/iterG/iterF/iterU, homGen/homRes, IsDecomp/starNorm, InClass/WBound and ComposeData.omega were inspected at their definitions. In particular iterMap uses exactly the flow domain Dom(r-ρ,s-σ); `iterMap_eq` is rfl. The map's legitimate small-field data are proved in `compose`, rather than relying on arbitrary total-flow values. The only new definition is not a theorem-shaped input bundle.

## Proof and consumer checks

- Lines 140–152 construct ComposeData for inner widths `(r-ρ,s-σ)` and generator widths `(r,s)` with Φ=qδ/(2πα). Width admissibility follows from `2ρ<r`, `2σ<s`; `eta=2u≤1/2` is derived from smallness.
- Lines 161–169 derive the homological sign `{h∘snd,φ}=ξ-T_K f`; the sign agrees with the Taylor identity. Lines 51–74 prove finite class/norm of g from its decomposition, including the empty finite family.
- Lines 219–257 establish the affine bracket representation on an open set and the corresponding fderiv equality locally. Thus complex differentiation is justified by neighbourhood equality and holomorphy, not by merely pointwise equality at one point.
- Lines 274–299 form f_t=(1-t)ξ+tT_Kf with bound δ for 0≤t≤1, append it to the finite decomposition, and consume N6-3 `bracket_g`. The new star weight is exactly δ, and the bound is 2/(eρσ)(starNorm+δ)Φ. Lines 300–312 prove both joint continuity requirements using holomorphic derivative regularity.
- Lines 352–363 consume C5-9 `transform` and C5-8 `composition_integral` with all their actual premises supplied by the preceding proofs. The integral identifies the actual liftRemainder, rather than an arbitrary bounded residual.
- Lines 365–370 consume W4-7 `truncation_tail`, restrict its action width, then use the last two clauses of `composition_series` to control the actual tail after composition, with exp(-2πKσ).
- Lines 372–400 prove the residual equality on Dom(r-2ρ,s-2σ), combine the two bounds, and normalize constants by field arithmetic. The inverse factor here is exactly `1-2u`; there is no unproved comparison substituted for it. Summability is preserved by the WBound APIs.
- Lines 411–423 repackage these facts into the exact target statements. The identity in (c) is intentionally definitional; its analytic class and (d)'s estimate are substantive proved content, as the design specifies.

Direct imports are IterativeMap, BracketDecomp, CompositionIntegral and Transform, plus three Mathlib tactic modules. No Iterative facade import occurs. Recursive source import inspection found 74 KAM modules, no provider, and no frozen theorem imports. The eight reached frozen modules are definitions, each manifest state SEALED: ActionNbhd, ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals and OmegaZero. Their bodies and relevant complex-vector-field/strip conventions were read; frozen bytes/ABI are checked by lint. There is no DRAFT_SORRY import path.

## Independent checks

Every Lean/Lake operation below was serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`. No heartbeat, recursion or synthesis limit was raised; no clean, cache update, package mutation, generated-root edit or state-changing Git command was used.

### Targeted build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n66 KAM.Nekhoroshev.NormalForm.IterativeRemainder
```

Exit 0:

```text
[inp-gate] slot 1 acquired 07:01:04 for KAM.Nekhoroshev.NormalForm.IterativeRemainder
Build completed successfully (3226 jobs).
```

This is a successful targeted incremental build, not a clean rebuild or measured elaboration benchmark.

### Exact-type probes and every public theorem's axioms

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N66Audit.lean
```

Exit 0. The probe imported only the audited module; reconstructed the design headers as described above; and printed:

```text
'KAM.NormalForm.IterHyp.compose' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.IterHyp.iterMap_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.IterHyp.bracket_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.IterHyp.hClass' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.IterHyp.integrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.IterHyp.iterF_class_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.iterative_direct_c' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.iterative_direct_d' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.NormalForm.IterativeRemainder
```

Exit 0; complete output:

```text
replaying KAM.Nekhoroshev.NormalForm.IterativeRemainder
```

There is only one in-scope module and no provider module; the one invocation replays the audited module, including its private support declarations. This is not a claim to have independently replayed every inherited dependency module.

### Lint and protected paths

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, with complete output:

```text
Lean lines over 100 characters:
/root/code/KAM-inp-n66/KAM/Planetary/Hamiltonian/Liouville.lean:35:108
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (436 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This is not a full repository lint PASS. The stale generated root is explicitly permitted by the brief; the inherited Liouville 108-character line is an additional, unwaived repository-wide hygiene failure outside this audit's file scope. Both are nonblocking notes for the N6-6 file verdict. The audited file contributes neither failure; no generated or inherited file was repaired. The Liouville file is byte-identical to the selected merge base and absent from `git diff inp...HEAD`; the newer `inp` tip has different text there, so the note describes this worktree snapshot rather than the current tip. Module-format, frozen-anchor and ABI checks passed.


The target has 429 total lines, no lines longer than 100 characters, and no forbidden proof escapes, option overrides or EuclideanSpace tokens. It has the copyright header, `module`, public interface imports, module docstring, and `@[expose] public noncomputable section`. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` has empty stdout and exits 0 (with the same merge-base warning). `git diff --check` exits 0.

## Findings, uncertainties, errata and handoff

No blocking mathematical, statement, definition, dependency-consumption or axiom defect found in the requested file. No suspected pinned-source or blueprint defect discovered. No mathematical deviation introduced by this audit. The blueprint's already documented smallness restriction to eta≤1/2 and its 2/e improvement are retained exactly; they are not new errata.

Repository hygiene notes are recorded with the lint receipt. They do not justify changing inherited files during this report-only audit. The design audit 2 size-estimate/API notes concern planning documentation or other packages, and do not obstruct the actual 429-line implementation or its verified calls.

Retained auditor change: only `/root/code/KAM-inp-n66/docs/tracks/N/audits/N6-6-audit-1.md`. Auditor scratch probe and logs are removed after receipts are copied here. Existing handoff is preserved. No production code or frozen declaration is changed. N6-6 (c),(d) is accepted as infrastructure, with repository lint notes; this does not seal N-HEAD-C or complete (a)–(e), the later Normal Form Lemma, or any track headline.
