# N11-E2 independent package audit 1

Overall verdict: **FAIL — assigned graph slice incomplete**. All four SIGNED theorem declarations pass exact-signature and proof checks. The failure is the unimplemented second Taylor display required by `bpN:p11:ext-taylor` and `stepN:p11:et-taylor`; it is not a counterexample to any proved theorem. Adjoint passes with the nonblocking provenance notes below.

## Scope and authority

Audited 2026-10-28 at HEAD `a98999742cddf39478bee09d4d453965820bda1c`, against `inp` at `48e9326d764f4bb7e1704209fddf71863ec4eb9e`. Read AGENTS.md, PLAN.md, DECISIONS.md, the external package-audit brief, the handoff/AUDIT FOCUS, both N11 design audits, the revised design and external signatures, track-N statement, the partial-convex frozen theorem, relevant frozen definitions, p11b and the graph contracts. The user's exact report path overrides the generic brief's main-worktree destination.

Only `KAM/Nekhoroshev/Partial/Lie.lean` and `Adjoint.lean` receive a package verdict. Inspected the full `git diff inp...HEAD`: it adds these two files plus inherited `Bracket.lean` (380 lines) and `VectorField.lean` (97 lines). Those inherited modules are context, not newly certified packages. Git reports multiple merge bases and selects `7c254d1ada904dce883560fd988ff208b2edcb35`; `git merge-base --all inp HEAD` also lists `3fd1914def12280f375f18e1f5746c989f50de90`. The requested three-dot comparison was used without changing branches or refs.

Input hashes:

| Input | SHA-256 |
|---|---|
| External N11Signatures.lean | `23bd2cc2645243b3357acccda6e04ff69fad4d055963010025c582f3c886a0e4` |
| N11-LEAN-DESIGN.md | `f0fd0d111b6abd5c335a5ea144135a07b28be326f3d699f3c2761c46ad097609` |
| p11b-partial-nf.tex | `4005a51b99ed21cba7c6cbca27b8e70392f9d8d6c67d6b59fec9e25cac51232d` |
| Lie.lean | `b09ad827bc16fcd0fac33ac92e4f8984c2de8e16990dbf83319bddec0aa517eb` |
| Adjoint.lean | `cbc5242f1419685ddea99538c4564432f44ea30dfab85dfe30dadf4ec6a1f852` |

No frozen anchor or provider is implemented by N11-E2. Provider/frozen-type and seal-body probes are therefore inapplicable to this package. In particular, this audit does not seal `partialConvex_nekhoroshev`, whose frozen body remains `by sorry`.

## Declaration and node ledger

All theorem names below are in `KAM.Nekhoroshev`; private helpers are explicitly identified. B means `blueprint-N/parts/p11b-partial-nf.tex`.

| Node / declaration | Lean location | Verdict | Reason |
|---|---|---|---|
| SIGNED `ext_taylor_regular` | Lie:110 | PASS | External signatures:792; exact binders, smoothness on the closed interval and every within derivative. |
| SIGNED `ext_taylor` | Lie:119 | PASS | External signatures:240; exact orientation, finite sum, order and integral kernel. |
| SIGNED `ext_taylor_bound` | Lie:160 | PASS | External signatures:759; exact uniform-B formulation and factorial denominator. Source hypotheses are retained even when unused. |
| SIGNED `adjoint` | Adjoint:211 | PASS WITH NOTES | External signatures:231; exact source radii, SL, nonnegative bounds and normalized constant `(e²(2V/(ρσ))/8)^j U`; different valid bracket application. |
| `bpN:p11:ext-taylor` | Lie:39–187 | FAIL (completeness) | General identity, derivative sequence and remainder bound are proved; the second combined identity at B:80 is not proved internally or exported. See F1. |
| `stepN:p11:et-one` | private `hasDerivAt_comp`, Lie:67; `contDiffOn_comp`, Lie:75 | PASS | Restricts the complex derivative to the real scalar field and composes with the actual ODE derivative. Derivative continuity follows in the smoothness induction. |
| `stepN:p11:et-ind` | private `differentiableOn_extAd`, Lie:58; `contDiffOn_comp`, Lie:75; `iteratedDerivWithin_comp`, Lie:93 | PASS | Holomorphic iterates and smoothness/within derivatives proved by induction, using unique differentiability on Icc including endpoints. |
| `stepN:p11:et-taylor` | Lie:119–187 | FAIL (completeness) | Mathlib integral Taylor and the kernel integral are established; graph contract requires “the two displays”, including their combined second identity. |
| `bpN:p11:adjoint` | Adjoint:211–249 | PASS WITH NOTES | Complete iterative class and factorial-normalized WBound conclusion; stale graph locators noted below. |
| `stepN:p11:ad-setup` | private `ad_iter`, Adjoint:126–182 | PASS | Fixed block c, divided losses, same-ratio SL, positive intermediate radii and induction. |
| `stepN:p11:ad-step` | private `step_const`, Adjoint:73; `ad_step`, Adjoint:105 | PASS | Proves the required one-step bound at the exact output radius. |
| `stepN:p11:ad-prod` | private `ad_iter`, Adjoint:126; `factorial_est`, Adjoint:186; public `adjoint` | PASS | Factorial quotient recurrence implements the product; exponential-series factorial bound and final normalization give the literal bound. |

There are no UNSIGNED public exports and no public helper short-name reuse. Every nonprivate theorem in the two files is one of the four signed declarations. All are inside `KAM.Nekhoroshev`; no root declaration or global instance is installed.

## F1 — Missing combined Taylor identity (medium; blocks complete-slice acceptance)

B:79–80 states, for holomorphic h and f₀,

```text
(h+f₀)(γ(1)) = h(z)+{h,φ}c(z)+f₀(z)
  + ∫₀¹ {(1−t){h,φ}c+f₀, φ}c(γ(t)) dt.
```

The graph at `docs/graph/N/DEPGRAPH.md:15986` includes this identity in the parent SOURCE_CONCLUSION; `:16074` explicitly requires “the two displays” for `stepN:p11:et-taylor`. The design node table maps both to the three Taylor declarations in Lie.lean. That file's declarations and proof bodies contain only the general single-observable formula, regularity and the norm bound. No proof specializes N=2 to h and N=1 to f₀, adds the resulting identities, or identifies the resulting integrand with the bracket of `(1−t){h,φ}c+f₀`. No other declaration in the two-file scope supplies it.

Adversarial recheck: the missing display is mathematically derivable from the proved formulas plus bracket linearity and integral linearity, so this is an implementation/coverage gap, not a false statement or signature mismatch. But derivability is not an internal Lean proof of the assigned graph conclusion. The previously passing design audits approved the target interfaces; they did not prove this omitted clause. Deferring it silently to the later Transform package would change the explicit N11-E2 complete-slice contract.

Repair: retain all four exact signed declarations and add a distinctly named companion theorem proving this literal identity from the same holomorphy/open-domain/ODE assumptions, without new premises. An explicitly authorized reassignment of that source clause could alternatively resolve ownership, but none is recorded in the current handoff. No production change was made by this audit.

## Definitions, assumptions and proof review

Neither audited file introduces a `def`, `abbrev` or `structure`: classification is **none**. The proof-only private helpers do not introduce replacement objects or conclusion-shaped assumptions. Existing `EC n k` is the unequal product of Fin-coordinate function spaces; extBracket is exactly `Du · wfield`, and extAd recurses with this orientation. Real-time endpoints use the existing two-sided `HasDerivAt` ODE predicate. Holomorphy is used only on the open domain visited by the curve; global fderiv fallback values are not used as derivatives off-domain.

`WBound` includes WSummable at every action point. Hence no proof relies on the junk value of a nonsummable tsum. Empty bases remain harmless: class/bound assertions are domain restricted, and all arithmetic bounds needed by adjoint are explicitly nonnegative. No maximum on an empty set is chosen in `ext_taylor_bound`; under an actual curve the B-bound formulation gives the source maximum bound once chosen. No change of norm, Fourier weight, carrier or constant dependence was found.

The adjoint proof uses `bracket` with v the generator and u the preceding iterate, rather than the source's antisymmetry route. At step i, its losses are R′−Rᵢ and s′−sᵢ; the other two Cauchy denominators simplify to κ and λ. Both large losses are at least `(j+i)κ`, `(j+i)λ`. `step_const` bounds the fast contribution by 2·(3/8) times the reciprocal denominator and the slow contribution by (1/8) times it, using `16kcλ ≤ κ`. Thus the total is at most 7/8 of that reciprocal, in particular at most the required reciprocal. It does not wrongly apply SL to the enlarged losses. The induction gives `j!/(j+i)!`, and factorial normalization cancels j! at i=j. The block's c never changes with the intermediate radius.

The Taylor proof uses Mathlib's complex-valued integral Taylor theorem, consistent with the source's real/imaginary proof. Its within-derivative identification is guarded by `uniqueDiffOn_Icc zero_lt_one`; the nonempty interval and ordinary endpoint derivatives are preserved. No additional hypothesis or budget override is introduced.

## Independent validation

All Lean/Lake commands below are sequential and use `LEAN_NUM_THREADS=1` and niceness 5. Probe files live only in this worktree's `.lake/abi-scratch/` and are deleted after use. The source signature file was read, not imported with its placeholder proofs.

1. Full history/protected-path inspection:

```sh
git diff inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Protected-path diff: empty. Whitespace check: exit 0. The only diagnostics are the disclosed multiple-merge-base warnings.

2. Targeted gate build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-n11e2 KAM.Nekhoroshev.Partial.Lie KAM.Nekhoroshev.Partial.Adjoint
```

Exit 0. Gate: `[inp-gate] slot 2 acquired 20:24:01 ...`.
Output: `Build completed successfully (3247 jobs).` Targets were replayed from the worktree cache. Warnings: unused hΩ, hφ, hu and hγ in Lie:160–162; inherited unused hgr in Stability/Gradient:168. No elaboration failure or heartbeat design signal.

3. Exact signatures, term applications and axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N11E2Audit.lean
```

Exit 0, with no warnings/errors. Each external signed declaration header was extracted independently, renamed, and proved by application of the production theorem to exactly its explicit binders. Both `example : type_of% @expected := @actual` and the reverse were checked for all four. A separate whitespace-normalized source-header comparison returned True for all four, preserving binder names/order and every premise/conclusion. Probe output:

```text
'KAM.Nekhoroshev.ext_taylor_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.ext_taylor' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.ext_taylor_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
```

4. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Nekhoroshev.Partial.Lie KAM.Nekhoroshev.Partial.Adjoint
```

Exit 0. Complete output:

```text
replaying KAM.Nekhoroshev.Partial.Adjoint
replaying KAM.Nekhoroshev.Partial.Lie
```

5. Hygiene and import checks:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely for the permitted generated-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (922 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No generated root was regenerated. No other lint failure was reported.

Independent static checks: Lie has 194 lines, maximum width 100; Adjoint has 253 lines, maximum width 97. Both have copyright, `module`, `public import`, module docstring and an exposed public noncomputable section. Forbidden-token/override scan of both files has no matches. A recursive read of KAM imports finds 73 local modules, no providers and no frozen theorem imports; all 21 frozen imports are definitions. Thus no DRAFT_SORRY theorem enters their import closure. Scanning other production declarations found no reuse of any of the four public short names. No harmful root shadow is introduced.

6. Cleanup/report checks: temporary `N11E2Audit.lean` removed; `git diff --check` and the untracked-report whitespace check pass. The final working-tree status contains only the pre-existing untracked N11-E2-handoff.md and this audit report. Protected source files remain unchanged.

## Source/blueprint issues, deviations and limits

- Existing stale locator: `docs/graph/N/DEPGRAPH.md:15715` quotes `adjoint@L69-L86`, but the adjoint proof ends at B:73; B:75–86 is Taylor. The parent edge to ad-prod at graph:15731 also quotes L72–85 and overreaches the actual step B:72. The design already reports the first range. These are locator defects, not false mathematical inequalities. No graph was edited.
- Implementation deviation: the adjoint bracket argument ordering and direct constant estimate differ from B:71, as justified above. No change of conclusion or premises results.
- F1 is a code/assignment completeness issue, not a suspected erratum in a pinned mathematical source. No new pinned-source mathematical defect was found; no external PDF re-audit is claimed.
- Private `continuous_slice'` and `wbound_adjoint_const_mul` duplicate existing proof patterns; private names avoid public shadowing. Deduplication is optional and not needed for acceptance.
- No provider, frozen theorem or final N11 campaign result is certified or sealed here. Kernel-valid signed formulas do not discharge the missing graph clause.
