# P23-03 independent package audit 1

**Overall verdict: PASS WITH NOTES.** All three public theorems pass statement fidelity, proof review, exact-type application, axiom closure, and kernel replay. The scoped module has clean hygiene. Full repository lint exits 1 because of the permitted stale generated root and an inherited 108-character line outside this package. No mathematical blocker was found. This is an infrastructure-package verdict, not a seal or proof of any Track I/N/P frozen headline.

## Scope, authorization and frozen inputs

Audited on 2026-10-28 in `/root/code/KAM-inp-p2303`, following the shared `inp-audit-package.md` brief and this worktree's P23-03 handoff. Read AGENTS.md, PLAN.md, DECISIONS.md, Track P statement conventions, design revision 2, both design audits, and the scoped blueprint statements/proofs. Tier 2 focused audit: all three theorem statements and all proof lines reviewed; separate adversarial checks targeted inverse selection, continuation closedness, nonconvex image domains, and degenerate dimensions.

Only this report was added to the repository. Temporary Lean probes were placed under `.lake/abi-scratch/` and deleted after checking. No production, frozen, manifest, generated-root, blueprint, or git-history changes were made. The user's explicit absolute report path overrides the generic main-worktree destination in the shared brief. No subagents were used.

- Package HEAD: `e5b744bd6f47effaefd5fe006ad3add943f899ab`.
- `inp` at audit start: `4f65a1f8055d14808ab27ed9bff2e18d69eac46c`.
- Merge base: `1699a58fc52973a29e47f1636a414db9a7ffda8d`.
- `git diff inp...HEAD`: exactly one file, `KAM/Planetary/TwoScale/Inverse.lean`, 232 insertions. The shared `inp` ref advanced during the audit; the merge base and package diff remained unchanged. These immutable hashes pin the comparison.
- The handoff was already untracked when the audit began; it was read without modification.

SHA256 input manifest:

| Input | SHA256 |
|---|---|
| `KAM/Planetary/TwoScale/Inverse.lean` | `fe574a199fd440e607ad9e86eaaf121bdfea03602486f6586864e8bb6625e5f0` |
| `docs/tracks/P/design/P23-LEAN-DESIGN.md` | `5a03b76eb0f5ea6a090c52a0b64e4dbc9bfb0a3249f84cec1407c0f2e4c9f8b4` |
| `blueprint-P/parts/p3a-two-scale-iteration.tex` | `94327df07e9c89e6ff5186a71261fa66120a18993bfd9b3764ce4607c856328c` |
| `/root/code/KAM-inp/.drafts/design/P23Signatures.lean` | `7d7dae4308ea9ec0ca763a2a21ce4b83280bdbb4b91d2c4f5e7567b71085e834` |
| `docs/tracks/P/design/DESIGN-P23-design-audit-1.md` | `695ebe468de5afa9056cd6c794df0cbcfb44cce7ac86a070b962371081d0362f` |
| `docs/tracks/P/design/DESIGN-P23-design-audit-2.md` | `e222d7c1245f63b5acaee70c4a231d53bb9465a615a5aa4c2847ccd27a21e3a2` |
| `docs/tracks/P/audits/P23-03-handoff.md` | `fb5af734846db132db04025c1ccee771c563085c7268292b660086d05474870c` |

The signature file is absent from this worktree's `.drafts/design/`; the exact shared path named above was used. All three signatures also occur verbatim in this worktree's tracked design Appendix A. No draft signature module was imported into Lean.

## Declaration and node ledger

Locators below refer to the input hashes above. Blueprint source is `blueprint-P/parts/p3a-two-scale-iteration.tex` (P3a); implementation is `KAM/Planetary/TwoScale/Inverse.lean`.

| Node | Lean declaration / implementation | Verdict | Reason |
|---|---|---|---|
| `bpP:p3:ext-ift` | `KAM.Planetary.ext_ift`, L29–72 | PASS | Exact design signature, shared signatures L609–615; P3a L114. Open image, holomorphic inverse into Ω, both inverse laws, and inverse derivative law are proved. |
| `bpP:p3:ext-neumann` | `KAM.Planetary.ext_neumann`, L74–105 | PASS | Exact design signature, signatures L617–620; P3a L118. Actual continuous linear equivalence for id+B and inverse operator norm ≤2. |
| `bpP:p3:ball` | `KAM.Planetary.ball`, L108–230 | PASS | Exact design signature, signatures L623–633; P3a L124–126. Full image-ball coverage and inverse Lipschitz inequality on the specified image ball. |
| `stepP:p3:ball-inv` | `ball`: L119–140 | PASS | Restricts F to the input ball, constructs G and proves its derivative norm ≤m. |
| `stepP:p3:ball-lift` | `ball`: L141–150, L185–221 | PASS | Endpoint-lift predicate with the quantitative radial displacement bound; local convex-ball MVT extends it to the right. |
| `stepP:p3:ball-closed` | `ball`: L148–184, L222–226 | PASS | Compact closed-ball projection proves closedness; continuous induction reaches t=1. This is a valid finite-dimensional replacement for the prose Cauchy-sequence argument. |
| `stepP:p3:ball-lip` | `ball`: L227–230 | PASS | Applies MVT only on the convex target ball already proved to lie in the open image. |

There is no provider or frozen-anchor seal in this package. Provider-equals-frozen and seal-body checks are therefore N/A, rather than a claimed frozen seal. The three exact design declarations are implementation theorems. Future assembly into frozen P-G remains outside scope.

## Binder and semantic fidelity

A byte comparison of each `theorem ... := ` header against both the shared signatures and tracked Appendix A returned True for all three. Binder order, implicitness, witnesses, constants, norms and conclusions match. The Pi norm on `Fin n → ℂ` is the source max norm; derivatives use its induced operator norm. No Euclidean-space or matrix-norm substitution occurs.

The expanded logical inputs are listed below. Repeated binders receive separate rows for each theorem. TYPING covers source data; RULED refers to the reviewed design decision D5 at design L238, not a newly invented owner ruling. There are no bundled project predicates or hidden hypothesis fields in these types.

| Declaration | Binder | Bin | Source / meaning |
|---|---|---|---|
| `ext_ift` | `{n : ℕ}` | TYPING | P3a L114, dimension of ℂⁿ |
| `ext_ift` | `{Ω : Set (Fin n → ℂ)}` | TYPING | P3a L114, domain |
| `ext_ift` | `hΩ : IsOpen Ω` | SOURCE | P3a L114, “Ω open” |
| `ext_ift` | `{F : (Fin n → ℂ) → (Fin n → ℂ)}` | TYPING | P3a L114, map |
| `ext_ift` | `hF : DifferentiableOn ℂ F Ω` | SOURCE | P3a L114, holomorphic |
| `ext_ift` | `hinj : Set.InjOn F Ω` | SOURCE | P3a L114, injective on Ω |
| `ext_ift` | `hD : ∀ x ∈ Ω, Function.Bijective (fderiv ℂ F x)` | SOURCE | P3a L114, nonsingular derivative; expands to injectivity and surjectivity of each square finite-dimensional derivative, equivalent to nonzero determinant |
| `ext_neumann` | `{n : ℕ}` | TYPING | P3a L118, ambient finite-dimensional operator space |
| `ext_neumann` | `B : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)` | TYPING | P3a L118, linear perturbation |
| `ext_neumann` | `hB : ‖B‖ ≤ 1/2` | SOURCE | P3a L118, exact bound |
| `ball` | `{n : ℕ}` | TYPING | P3a L125, dimension |
| `ball` | `{Ω : Set (Fin n → ℂ)}` | TYPING | P3a L125, domain |
| `ball` | `{F : (Fin n → ℂ) → (Fin n → ℂ)}` | TYPING | P3a L125, map |
| `ball` | `hΩ : IsOpen Ω` | SOURCE | P3a L125, open domain |
| `ball` | `hF : DifferentiableOn ℂ F Ω` | SOURCE | P3a L125, holomorphic |
| `ball` | `hinj : Set.InjOn F Ω` | SOURCE | P3a L125, injective |
| `ball` | `{m : ℝ}` | TYPING | P3a L125, inverse bound |
| `ball` | `{δ : ℝ}` | TYPING | P3a L125, radius |
| `ball` | `hm : 0 < m` | RULED | Design D5 L238; positivity explicit in approved design signatures |
| `ball` | `hδ : 0 < δ` | RULED | Design D5 L238; positive radius explicit in reviewed design |
| `ball` | `hder : ∀ x ∈ Ω, ∃ A : _ ≃L[ℂ] _, A.toContinuousLinearMap = fderiv ℂ F x ∧ ‖A.symm.toContinuousLinearMap‖ ≤ m` | SOURCE | P3a L125; expanded fields are existence of the inverse derivative, exact forward derivative identity, and its bound. None is an added result about F's global inverse or image. |
| `ball` | `{x₀ : Fin n → ℂ}` | TYPING | P3a L125, center |
| `ball` | `hx : Metric.ball x₀ δ ⊆ Ω` | SOURCE | P3a L125, exact containment |

Counts (outer binders, with the expansions above): `ext_ift`: SOURCE 4, STANDING 0, TYPING 3, RULED 0, EXCESS 0; `ext_neumann`: SOURCE 1, STANDING 0, TYPING 2, RULED 0, EXCESS 0; `ball`: SOURCE 5, STANDING 0, TYPING 6, RULED 2, EXCESS 0. No theorem assumes existence of a global inverse, path lift, image-ball containment, or inverse Lipschitz conclusion.

The source's target variables w₁,w₂ are represented by x,y in the input ball together with image-ball membership. Image-ball coverage and injectivity make these formulations equivalent: any target pair has preimages in the input ball, and the inequality applies to them. The derivative identity in `ext_ift` is the full inverse identity because its inner derivative is bijective. The empty-domain and n=0 cases introduce no hidden positive-dimension assumption.

## Proof and definition review

`ext_ift`: L37–49 obtains strict differentiability from complex smoothness and promotes the bijective derivative to a continuous linear equivalence. The local IFT proves image openness. `Function.invFunOn F Ω` at L50 has maps-to and both inverse laws proved using injectivity and image membership (L51–53). Local left-inverse differentiation gives holomorphy and the stated derivative identity (L54–72). No inverse regularity is assumed.

`ext_neumann`: L78–89 constructs an actual inverse from `IsUnit (1 - (-B))`, with ‖B‖<1 following from ‖B‖≤1/2. L92–105 obtains the constant 2 from ‖v‖−‖Bv‖≤‖(id+B)v‖ and the operator bound. The non-strict endpoint 1/2 is retained.

`ball`: Restriction to the input ball makes ambient openness unnecessary to this stronger proof; retaining `hΩ` preserves the exact design interface. The inverse derivative bound is derived algebraically from `ext_ift`, not assumed. For each target y, let c=F(x₀), d=‖y−c‖; then md<δ. Every lift is trapped in the compact closed ball of radius md, strictly inside the input ball. L150 defines T by existence of an endpoint lift with ‖x−x₀‖≤mtd. L151–184 realizes T∩[0,1] as the projection of a closed subset of a compact product. L186–221 extends each admissible t<1 through a small target ball contained in the open image, preserving that displacement estimate. L222 invokes one-sided continuous induction. Thus it needs no unsupported assertion that the entire image is convex. The last MVT uses only the convex image ball after coverage is established.

**Definitions:** no new public `def`, `abbrev`, `structure`, instance or notation. Public definition classification is N/A (all three exports are theorems). Local `G`, `A`, `W`, `c`, `d`, `T` and `K` denote inverse witnesses, ordinary sets/scalars, or the explicitly reviewed continuation predicate. `invFunOn` has arbitrary values off the image, but no theorem relies on or specifies those values; G is existential and all inverse/differentiability claims are restricted to the image. This is not a globally exported source-defined inverse with deferred characterization. On its claimed domain the inverse is unique by `hinj`, and both inverse laws are proved in the same theorem.

The complete project import closure is `KAM.Planetary.TwoScale.Inverse`, `KAM.Strip.Regularity`, `KAM.Strip.Cauchy`, and `KAM.Frozen.Defs.ComplexStrip`, plus Mathlib. The only frozen import is the unchanged literal strip definition, manifest ID `kam.complexStrip.v1`, state SEALED. It does not appear in the three exported theorem types. No provider or frozen theorem anchor, draft signature, or DRAFT_SORRY import occurs in this closure.

## Independent verification

All audit-owned Lean/Lake invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`. No heartbeat, recursion-depth or synthesis-budget override was used. No library clean, update, cache fetch or full rebuild was requested.

1. Targeted gated build:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2303 KAM.Planetary.TwoScale.Inverse
```

Exit 0. Output began `[inp-gate] slot 1 acquired 06:57:39 for KAM.Planetary.TwoScale.Inverse`, then `⚠ [9050/9050] Replayed KAM.Planetary.TwoScale.Inverse`; warnings at L109:5 (`hΩ`) and L110:28 (`hδ`) say the variable is not explicitly referenced. Final line: `Build completed successfully (9050 jobs).` This was a cached/replayed targeted build, not a claim of a fresh full compilation; kernel replay below independently checked the module.

2. Exact design-type application and axioms:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2303Audit.lean
```

The probe imported only `KAM.Planetary.TwoScale.Inverse`, opened the same namespaces/scopes, and copied all three headers byte-for-byte from shared signatures L609–633 under fresh names. Its proof bodies applied exactly the explicit binders in order:

```lean
by exact KAM.Planetary.ext_ift hΩ hF hinj hD
by exact KAM.Planetary.ext_neumann B hB
by exact KAM.Planetary.ball hΩ hF hinj hm hδ hder hx
```

Exit 0; full output:

```text
'KAM.Planetary.ext_ift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ext_neumann' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ball' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. One kernel replay invocation for the sole new module:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.TwoScale.Inverse
```

Exit 0; full output: `replaying KAM.Planetary.TwoScale.Inverse`.

4. Full repository lint, run after kernel replay completed:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1; full output:

```text
Lean lines over 100 characters:
/root/code/KAM-inp-p2303/KAM/Planetary/Hamiltonian/Liouville.lean:35:108
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (433 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The Liouville line was independently checked at immutable merge base `1699a58fc52973a29e47f1636a414db9a7ffda8d`: line 35 already had 108 Unicode characters; its package diff is empty. Thus full lint is not reported as passing, while the scoped P23-03 module is clean. The generated-root discrepancy is the exception explicitly allowed in the brief.

5. Mechanical hygiene and integrity:

```sh
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Both exit 0 with no output. Independent Python checks counted 232 physical lines, zero lines over 100 characters, zero forbidden-token matches (`sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, `set_option`), and exactly the three declared public theorems. Copyright, `module`, public interface imports, module docstring and `public section` are present. No definitions need an `@[expose]` annotation. A final hash check confirmed the implementation was unchanged.

## Findings, uncertainty and closeout

- **N1 — inherited hygiene note:** full lint remains nonzero as documented above. No package repair is required; the generated root and the inherited Liouville line belong to integration/out-of-scope maintenance.
- **N2 — harmless interface warnings:** `ball` retains reviewed design binders `hΩ` and `hδ`; its restricted-domain proof does not explicitly need them. Removing them would change the exact audited signature and is not proposed here.
- **Blueprint clarification already adopted:** P3a L125 states “bound ≤m” and the ball radius without explicit positivity. Design D5 L238 says “Make both explicit in the generic helper”; the implementation does exactly that. This is a documented design clarification, not an unreported new premise.
- **Proof-method deviation:** compact projection plus right-neighborhood induction replaces the blueprint's explicit Cauchy continuation. It establishes the same closedness/coverage obligation on the same finite-dimensional carrier. The handoff describes compactness, so there is no undisclosed mathematical gap.
- **Suspected new pinned-source or blueprint defects:** none found. No external source-PDF claim was audited or promoted. The inspected blueprint is the source authority for this bounded package; the prior design audits' CP10/source caveats remain outside scope.

Adversarial checks found no surviving mathematical finding: inverse values off-image are never used, compactness is applied on a strictly interior closed ball, no global image convexity is assumed, and the target-variable form of the inverse estimate is recovered from proved coverage. No uncertainty blocks this package. All scoped nodes have a verdict; exact-signature elaboration, standard-axiom closure and kernel replay are complete. No frozen headline, future consumer assembly, or graph/campaign closure is certified.
