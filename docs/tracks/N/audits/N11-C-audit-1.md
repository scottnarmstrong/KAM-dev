# N11-C independent package audit 1

Overall verdict: **PASS WITH NOTES** for the N11-C infrastructure slice. All five signed theorem types and the literal `scaled` definition match the Revision-2 signatures exactly. All assigned graph obligations are supported by the proofs or the designated independent-dimension Part-4 interfaces. No mathematical blocker or unauthorized premise was found.

This verdict does not seal `KAM.Nekhoroshev.partialConvex_nekhoroshev`: its manifest entry `nekhoroshev.d25.partialConvex_nekhoroshev.v1` remains `DRAFT_SORRY`. There is no N11-C provider or anchor seal to validate. Provider/frozen-type and seal-body probes are therefore inapplicable; fresh copies of all five signed declarations were elaborated with explicit applications of their implementation exports instead.

## Scope and frozen inputs

2026-10-28; tier-2, refute-first package/source-correspondence audit. Only `KAM/Nekhoroshev/Partial/Bracket.lean` and `VectorField.lean` receive a proof/package verdict. Read AGENTS.md, PLAN, DECISIONS, the external package-audit brief, N11-C handoff and AUDIT FOCUS, N11 design, both design audits, signed file, track-N statements, relevant frozen theorem/definitions and blueprint p11b. Source authority for this slice is the pinned blueprint and exact design signatures; no independent re-audit of historical PDFs or other packages is claimed.

Authorization: persistent edit only this report at the user-specified worktree path, which overrides the brief's generic main-worktree destination. Temporary probes/logs used `.lake/abi-scratch/` and were removed after validation. No source repair, git mutation, generated-root regeneration, dependency changes or delegation.

| frozen-v1 input | Revision / SHA-256 |
|---|---|
| HEAD | `3fd1914def12280f375f18e1f5746c989f50de90` |
| `inp` inspected | `7c254d1ada904dce883560fd988ff208b2edcb35` |
| Bracket.lean | `ad44b29bffe89447c490042f898a47721cbe14db2856d01f7f8fcaae35413934` |
| VectorField.lean | `2cd853da99a6343d7faed2d136bc3716250804b09b5e0bc8ca50e090af724af9` |
| `/root/code/KAM-inp/.drafts/design/N11Signatures.lean` | `23bd2cc2645243b3357acccda6e04ff69fad4d055963010025c582f3c886a0e4` |
| N11-LEAN-DESIGN.md | `f0fd0d111b6abd5c335a5ea144135a07b28be326f3d699f3c2761c46ad097609` |
| blueprint p11b | `4005a51b99ed21cba7c6cbca27b8e70392f9d8d6c67d6b59fec9e25cac51232d` |

`git diff inp...HEAD` reports two merge bases and chooses `378dc658463fa8d5de2758f0d9739b60153bb165`; the other is `9d16b3127c8a9fe9af335c5b64874bd29f32ebd8`. The full comparison has four additions: Bracket (380 lines), VectorField (97), inherited Coordinates (298) and Setting (177), total 952 lines. The latter two are dependencies inspected for meaning/imports, outside the requested package verdict. Protected-path diff is empty. No alternative comparison was silently substituted.

## Declaration and node ledger

All names below are qualified by `KAM.Nekhoroshev`. B denotes pinned `blueprint-N/parts/p11b-partial-nf.tex`; implementation locators refer to frozen-v1 above.

| Graph node | Declaration / implementation | Verdict | Evidence |
|---|---|---|---|
| `bpN:p11:ext-part4` | `ext_part4`, Bracket:44 | PASS | Exact signed sup-bound wrapper. B:16–18 also assigns the other Part-4 results by base-dimension instantiation, not to this wrapper alone. |
| `bpN:p11:bracket` | `bracket`, Bracket:171 | PASS | Exact signed class and WBound conclusion; B:20–24 constants, losses and quantifiers retained. Pointwise consequence composes with `ext_part4`. |
| `bpN:p11:bracket` (domination clause) | `bracket_dominated`, Bracket:292 | PASS | Exact signed arithmetic inequality, with the same `(SL)` hypothesis. |
| `stepN:p11:br-fast` | `bracket`, Bracket:252–271 | PASS | Angular derivative sum at fixed base, then Cauchy and product bounds; no spurious n factor. |
| `stepN:p11:br-slow` | `bracket`, Bracket:272–290 | PASS | Each of k products in each of two families bounded by U/(R0−R+ρ)·V/ρ, then multiplied by c. |
| `stepN:p11:br-dom` | `bracket_dominated`, Bracket:301–314 | PASS | Slow term ≤ X/8 and 1/e ≤ 3/8; hence total ≤ (X+Y)/2. |
| `bpN:p11:bracket-g` | `bracket_g`, Bracket:342 | PASS | Exact signed finite decomposition, source star-weight sum and factor V/(ρσ). |
| `bpN:p11:scaled` | `scaled`, VectorField:32 | PASS | Exact body, ordinary maximum coordinate norms in the specified order. |
| `bpN:p11:vf` | `vf`, VectorField:34 | PASS | Exact signed scaled-field and slow-pair estimates; hk is the standing k≥1 premise. |
| `bpN:p11:ext-num` (assigned arithmetic use) | `bracket_dominated` + `Real.exp_one_gt_d9` | PASS | Positive exponential and inverse bound proved; no numerical oracle or new axiom. |

No unsigned public theorem named after a node is introduced: every public theorem is one of the five signed exports. All additional theorem helpers are private. The public short name `bracket_g` also exists in `KAM.NormalForm`; it is the expressly prescribed signed name, not a reused public helper. No root-level declaration or harmful shadow was introduced.

## Source fidelity, expanded inputs and consumer applicability

Mechanical extraction from each `theorem name` through the text before `:=` found **byte-identical headers** for ext_part4, bracket, bracket_dominated, bracket_g and vf. The complete `def scaled` line is byte-identical too. The independent fresh declarations copied the headers from the external signature file, not from the implementations, and supplied the original explicit binders in order. No signature placeholder theorem was imported.

B:16–18 says Part-4 lemmas “hold ... with the same constants”; the design inventory at 183 expressly maps this to `ext_part4; all Part-4 declarations by dimension instantiation`. The generic coefficient, representation, sup conversion, multiplication, angular/action Cauchy and projection exports remain available with m=n+(k+k); general_cauchy applies to EC n k. The fresh probe instantiated these API types; actual cauchy_theta/action and sup-bound applications occur in the kernel-checked implementation. Their types retain independent n/m, geometric widths and exp(2πs|j|₁). `InClass` expands to holomorphy on Dom and coordinate period-one identities; `WBound` expands to summability plus an upper bound at every base point. Thus no zero-valued divergent `tsum` is used as a finite norm.

B:44–49 includes sharp derivative and numerical slow inequalities beyond the two conjuncts signed in vf. They are not lost proof obligations: cauchy_loss.2.1 gives U/(eσ), cauchy_loss.2.2 gives U/ρ, sup_le_wbound makes them pointwise using the derivative classes constructed at VectorField:47–65. `(SL)` implies cU/ρ≤U/(16kσ) for k≥1, σ>0, U≥0; this numerical implication was independently elaborated. Planned canonical_map needs the sharper fast-action displacement, supplied by the former angular derivative bound, and the cU/ρ slow displacement supplied by vf; composition_domain needs vf's first conjunct. These are interface applicability checks, not closure of those future consumer proofs. No future consumer imports a DRAFT signature theorem.

The source scaled formula B:40–42 is `max(|a|/σ,|b|/ρ,|ξ|/ρ)`. On EC, ‖z.2‖ is the maximum over the concatenated I,q,p coordinates, so the signed expression agrees for positive losses. Its closed-ball/polydisc interpretation uses the existing `polydisc_subset_Dom`; no new gauge or altered ambient norm is introduced. The definition uses Lean's ordinary total real division, exactly as signed; theorem uses require positive σ,ρ and do not exploit values at zero.

Five-bin classification follows. Every purely data binder is TYPING, the explicit source inequalities/class/norm clauses are SOURCE, and hk is STANDING (B:4). RULED=0 and EXCESS=0. `PartialBlock` expands only to Ic,S,rB,w data; lam,c,base are literal formulas, with no bundled premise. The table expands each logical InClass/WBound input into its two clauses; all implicit dimension, function, radius and finite-index data are listed separately below.

| Export | Expanded logical input | Bin | Source |
|---|---|---|---|
| `ext_part4` | `hs` | SOURCE | B:16–18 / Part-4 sup bound |
| `ext_part4` | `hu.differentiableOn` | SOURCE | B:16–18 / Part-4 sup bound |
| `ext_part4` | `hu.periodic` | SOURCE | B:16–18 / Part-4 sup bound |
| `ext_part4` | `hb.summable` | SOURCE | B:16–18 / Part-4 sup bound |
| `ext_part4` | `hb.bound` | SOURCE | B:16–18 / Part-4 sup bound |
| `bracket` | `hρ` | SOURCE | B:20–24 / finite norm representation |
| `bracket` | `hρR` | SOURCE | B:20–24 / finite norm representation |
| `bracket` | `hσ` | SOURCE | B:20–24 / finite norm representation |
| `bracket` | `hσs` | SOURCE | B:20–24 / finite norm representation |
| `bracket` | `hR0` | SOURCE | B:20–24 / finite norm representation |
| `bracket` | `hs0` | SOURCE | B:20–24 / finite norm representation |
| `bracket` | `hu.differentiableOn` | SOURCE | B:20–24 / finite norm representation |
| `bracket` | `hu.periodic` | SOURCE | B:20–24 / finite norm representation |
| `bracket` | `hv.differentiableOn` | SOURCE | B:20–24 / finite norm representation |
| `bracket` | `hv.periodic` | SOURCE | B:20–24 / finite norm representation |
| `bracket` | `hU` | SOURCE | B:20–24 / finite norm representation |
| `bracket` | `hV` | SOURCE | B:20–24 / finite norm representation |
| `bracket` | `hbu.summable` | SOURCE | B:20–24 / finite norm representation |
| `bracket` | `hbu.bound` | SOURCE | B:20–24 / finite norm representation |
| `bracket` | `hbv.summable` | SOURCE | B:20–24 / finite norm representation |
| `bracket` | `hbv.bound` | SOURCE | B:20–24 / finite norm representation |
| `bracket_dominated` | `hc` | SOURCE | B:4–6,20–28 / positive c, losses and SL |
| `bracket_dominated` | `hρ` | SOURCE | B:4–6,20–28 / positive c, losses and SL |
| `bracket_dominated` | `hσ` | SOURCE | B:4–6,20–28 / positive c, losses and SL |
| `bracket_dominated` | `hR` | SOURCE | B:4–6,20–28 / positive c, losses and SL |
| `bracket_dominated` | `hs` | SOURCE | B:4–6,20–28 / positive c, losses and SL |
| `bracket_dominated` | `hSL` | SOURCE | B:4–6,20–28 / positive c, losses and SL |
| `bracket_g` | `hρ` | SOURCE | B:31–36 / finite decomposition, Part-6 setting |
| `bracket_g` | `hρR` | SOURCE | B:31–36 / finite decomposition, Part-6 setting |
| `bracket_g` | `hσ` | SOURCE | B:31–36 / finite decomposition, Part-6 setting |
| `bracket_g` | `hσs` | SOURCE | B:31–36 / finite decomposition, Part-6 setting |
| `bracket_g` | `hSL` | SOURCE | B:31–36 / finite decomposition, Part-6 setting |
| `bracket_g` | `hRj` | SOURCE | B:31–36 / finite decomposition, Part-6 setting |
| `bracket_g` | `hsj` | SOURCE | B:31–36 / finite decomposition, Part-6 setting |
| `bracket_g` | `hU` | SOURCE | B:31–36 / finite decomposition, Part-6 setting |
| `bracket_g` | `hV` | SOURCE | B:31–36 / finite decomposition, Part-6 setting |
| `bracket_g` | `hg(j).differentiableOn` | SOURCE | B:31–36 / finite decomposition, Part-6 setting |
| `bracket_g` | `hg(j).periodic` | SOURCE | B:31–36 / finite decomposition, Part-6 setting |
| `bracket_g` | `hgb(j).summable` | SOURCE | B:31–36 / finite decomposition, Part-6 setting |
| `bracket_g` | `hgb(j).bound` | SOURCE | B:31–36 / finite decomposition, Part-6 setting |
| `bracket_g` | `hφ.differentiableOn` | SOURCE | B:31–36 / finite decomposition, Part-6 setting |
| `bracket_g` | `hφ.periodic` | SOURCE | B:31–36 / finite decomposition, Part-6 setting |
| `bracket_g` | `hφb.summable` | SOURCE | B:31–36 / finite decomposition, Part-6 setting |
| `bracket_g` | `hφb.bound` | SOURCE | B:31–36 / finite decomposition, Part-6 setting |
| `vf` | `hk` | STANDING | B:4: k≥1 |
| `vf` | `hρ` | SOURCE | B:44–49 / finite norm representation |
| `vf` | `hρR` | SOURCE | B:44–49 / finite norm representation |
| `vf` | `hσ` | SOURCE | B:44–49 / finite norm representation |
| `vf` | `hσs` | SOURCE | B:44–49 / finite norm representation |
| `vf` | `hSL` | SOURCE | B:44–49 / finite norm representation |
| `vf` | `hU` | SOURCE | B:44–49 / finite norm representation |
| `vf` | `hφ.differentiableOn` | SOURCE | B:44–49 / finite norm representation |
| `vf` | `hφ.periodic` | SOURCE | B:44–49 / finite norm representation |
| `vf` | `hb.summable` | SOURCE | B:44–49 / finite norm representation |
| `vf` | `hb.bound` | SOURCE | B:44–49 / finite norm representation |

Logical-input counts: SOURCE=54, STANDING=1, RULED=0, EXCESS=0. Summability is the finite-norm source guard, and nonnegative U,V are numerical upper-bound data explicitly present in the signed representation, not conclusions about brackets or fields.

| Export | Data binder | Bin | Source convention |
|---|---|---|---|
| `ext_part4` | `n` | TYPING | B:4–49 / exact signed carrier and data |
| `ext_part4` | `k` | TYPING | B:4–49 / exact signed carrier and data |
| `ext_part4` | `b` | TYPING | B:4–49 / exact signed carrier and data |
| `ext_part4` | `R` | TYPING | B:4–49 / exact signed carrier and data |
| `ext_part4` | `s` | TYPING | B:4–49 / exact signed carrier and data |
| `ext_part4` | `U` | TYPING | B:4–49 / exact signed carrier and data |
| `ext_part4` | `u` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket` | `n` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket` | `k` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket` | `b` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket` | `R0` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket` | `s0` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket` | `R` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket` | `s` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket` | `ρ` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket` | `σ` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket` | `U` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket` | `V` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket` | `u` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket` | `v` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_dominated` | `k` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_dominated` | `c` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_dominated` | `ρ` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_dominated` | `σ` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_dominated` | `R0` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_dominated` | `R` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_dominated` | `s0` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_dominated` | `s` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_g` | `n` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_g` | `k` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_g` | `b` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_g` | `N` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_g` | `R` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_g` | `s` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_g` | `ρ` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_g` | `σ` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_g` | `V` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_g` | `gj` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_g` | `Rj` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_g` | `sj` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_g` | `Uj` | TYPING | B:4–49 / exact signed carrier and data |
| `bracket_g` | `φ` | TYPING | B:4–49 / exact signed carrier and data |
| `vf` | `n` | TYPING | B:4–49 / exact signed carrier and data |
| `vf` | `k` | TYPING | B:4–49 / exact signed carrier and data |
| `vf` | `b` | TYPING | B:4–49 / exact signed carrier and data |
| `vf` | `R` | TYPING | B:4–49 / exact signed carrier and data |
| `vf` | `s` | TYPING | B:4–49 / exact signed carrier and data |
| `vf` | `ρ` | TYPING | B:4–49 / exact signed carrier and data |
| `vf` | `σ` | TYPING | B:4–49 / exact signed carrier and data |
| `vf` | `U` | TYPING | B:4–49 / exact signed carrier and data |
| `vf` | `φ` | TYPING | B:4–49 / exact signed carrier and data |
| `scaled` | `n` | TYPING | B:4–49 / exact signed carrier and data |
| `scaled` | `k` | TYPING | B:4–49 / exact signed carrier and data |
| `scaled` | `ρ` | TYPING | B:4–49 / exact signed carrier and data |
| `scaled` | `σ` | TYPING | B:4–49 / exact signed carrier and data |
| `scaled` | `z` | TYPING | B:4–49 / exact signed carrier and data |

There are no added instance premises. Universal indices/base points inside the expanded predicates are TYPING. Repeated logical inputs across different exports are counted independently.

## Definitions and proof review

| New definition | Classification | Body / carrier verdict |
|---|---|---|
| `scaled` | Public literal definition | PASS: max of the two scaled max norms; no choice/default branch. |
| private `BrIdx` | Literal finite-index abbreviation | PASS: Fin n ⊕ Fin n ⊕ Fin k ⊕ Fin k, exactly four product families. |
| private `brCoef` | Literal finite coefficient function | PASS: 1,−1,c,−c on the four summands. |
| private `brTerm` | Literal finite coordinate-product function | PASS: θ/I,I/θ,q/p,p/q derivatives with correct castAdd/natAdd indexing. |

For all four: BODY_MATCH=OK, PUBLIC_CARRIER=OK (private carrier exact where relevant), WELL_DEFINEDNESS=N/A_LITERAL, CHARACTERIZATION=N/A_LITERAL, CHOICE_INDEPENDENCE=N/A, DEFINITION_VERDICT=PASS. No characterized object or selected witness is introduced.

Line-by-line proof review: clm_eq_sum expands a continuous linear functional on every coordinate basis; extBracket_eq is unconditional algebra on the same fderiv values, so it does not silently assume differentiability at an invalid point. Class arguments use restriction to the open smaller domain before derivatives. Finite Fourier sums use coefficient linearity on continuous real slices (positive s−σ), and summability is proved by domination before comparing tsums. Both fast bounds retain sums inside the fixed-base estimates. The slow coefficient is nonnegative from the literal c=2π/lam², including degenerate block data. bracket_g distributes fderiv over a finite sum only at points where all summands are differentiable, using isOpen_Dom and the radius inclusions. Its WBound congruence uses actual equality on the real-angle slice. vf uses the correct sup norms on each component; slow-pair control is obtained coordinatewise, and hk plus SL supplies cσ≤ρ.

Adversarial recheck considered swapped bracket signs, missing k factors, summing suprema too early, non-summable coefficient fallback, zero/empty dimensions or base sets, zero block scales, and circular consumer premises. The unconditional bracket identity has all four signs correct; the 2k family count and fixed-base order survive; explicit summability and positivity guard every use. k=0 is excluded exactly where vf needs it, while the bracket permits it harmlessly. Empty domains yield only vacuous pointwise assertions. Unused signed hs/hρR/hV/hc are retained, not extra hypotheses smuggled into an unsigned result. No reportable mathematical finding survived this recheck.

## Verification evidence

All Lean/Lake commands below were serialized and used `LEAN_NUM_THREADS=1` with `nice -n 5`; no clean, cache download, package edit, resource override or broad build was run. External unrelated jobs on the shared host were not controlled by this audit.

1. `LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n11c KAM.Nekhoroshev.Partial.VectorField`

   Exit 0. Output: `[inp-gate] slot 3 acquired 19:36:49 for KAM.Nekhoroshev.Partial.VectorField`; `Build completed successfully (3227 jobs).` One inherited replay warning: `KAM/Nekhoroshev/Stability/Gradient.lean:168:5: Variable name hgr is not explicitly referenced.` No warning in either audited file. The reported job count includes replayed dependencies, not a clean rebuild.

2. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N11CAudit.lean`

   Exit 0, no errors/warnings. Each copied signature was closed with these exact explicit applications:

   ```lean
   exact ext_part4 b hs hu hb
   exact bracket b hρ hρR hσ hσs hR0 hs0 hu hv hU hV hbu hbv
   exact bracket_dominated hc hρ hσ hR hs hSL
   exact bracket_g b gj Rj sj Uj φ hρ hρR hσ hσs hSL hRj hsj hU hV hg hgb hφ hφb
   exact vf b hk hρ hρR hσ hσs hSL hU hφ hb
   ```

   Five exact signature-copy applications, the scaled rfl equation, extended Part-4 API instantiations, the slow numerical implication and both vf consumer components passed. Exact axiom output:

   ```text
   'KAM.Nekhoroshev.ext_part4' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.bracket_dominated' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.bracket_g' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.vf' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Partial.Bracket KAM.Nekhoroshev.Partial.VectorField`

   Exit 0. Complete verbose output:

   ```text
   replaying KAM.Nekhoroshev.Partial.VectorField
   replaying KAM.Nekhoroshev.Partial.Bracket
   ```

4. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`

   Exit 1 solely for the explicitly permitted stale generated root. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (899 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No forbidden-token, line-length, size, module-system or protected-anchor violation was reported.

5. `git diff --check inp...HEAD`: exit 0, no whitespace diagnostics (only the merge-base warning). `git diff --exit-code inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty diff apart from the same Git warning. Forbidden-token/override/EuclideanSpace scan of the audited files: no matches. Line counts 380 and 97; zero lines over 100 characters. Both files have copyright, module, docstring, public imports and an exposed public noncomputable section. Import-closure traversal found 72 KAM modules, no provider and no DRAFT_SORRY module; the 21 frozen imports are definition modules, not draft theorem anchors.

## Notes, errata and closeout

- Generated-root staleness is the explicit permitted exception in the package brief; the generated file was not repaired by this audit.
- The upstream Gradient warning is outside N11-C and is recorded separately from package correctness.
- The design already records an open-ball note at p11c:31 and a stale adjoint locator ending at p11b:86 rather than 73. Neither is introduced or used by this slice. No new suspected pinned-source defect or implementation deviation was found.
- The short-name overlap for the signed bracket_g is harmless under its specified namespace; consumers opening both namespaces should qualify it. No duplicate ownership of ext_part4 or bracket_dominated was found in the checkout.

The two-file implementation and signed interface are complete within the assigned scope. Frozen theorem closure, future consumer proofs, inherited N11-A proof certification and other tracks remain outside this verdict. Closeout: all assigned nodes and public declarations are classified; no open mathematical blocker; targeted build, exact signed-type applications, standard axiom closure and kernel replay passed; lint passed every substantive check with the explicitly allowed generated-root exception. All four N11C scratch files were deleted. Final hashes of both implementation files, the external signatures, design and blueprint still match frozen-v1. `git diff --check` passes and tracked working-tree diff is empty. Final status contains only this new report and the pre-existing untracked N11-C-handoff.md.
