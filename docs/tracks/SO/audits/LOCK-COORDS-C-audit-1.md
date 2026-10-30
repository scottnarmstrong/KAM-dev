# LOCK-COORDS-C independent audit 1

**Overall: PASS WITH NOTES for LOCK-COORDS-C's two-module implementation.** All eight signed declarations match the signed design surface; all 58 public declarations were classified and reviewed. No mathematical blocker was found. The exact lunar emitter-tree equality and the three signed theorem applications pass at default settings. This package has **no frozen theorem anchor or provider to seal**; the verdict does not close LOCK-GRAPH, LOCK-DATA, a checker audit, or the lunar confinement headline.

The literal branch-wide protected-file test is **not empty**, because the requested triple-dot comparison includes inherited integration changes. This is disclosed below, not reported as a clean branch-wide gate. The package commit itself changes only the two scoped modules.

## Scope, authorization, and frozen inputs

Auditor: maud-lockcc-1. Date: 2026-10-30 UTC. Focused tier-2, refute-first review. Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md (including D45), the generic package-audit brief, the package implementation brief, the named handoff, SO-LOCK design §3 and package contracts, SOLockSignatures §6, and design audits 2–3. The handoff has no literal `AUDIT FOCUS` heading; its signed-declaration/tree/proof descriptions, the package brief and the user's additional focus supply the scope.

Authorization: write only this report and temporary verification artifacts in this worktree's `.lake/abi-scratch/`; no implementation repair, commits, generated-file regeneration or frozen/manifest modification. The user's exact worktree report path overrides the generic brief's MAIN-worktree destination. No subagents used. One audit Lean/Lake invocation at a time, `LEAN_NUM_THREADS=1`, with `nice -n 5`; no resource-budget override.

Snapshot `frozen-v1`:

- HEAD `59d5371548f87c4aa870c202f81f8e7caf57179a`.
- Immediate parent `aeabfb1f3bb05acad39f89b47a512e986d9c4158`, the merge of `inp-locksqrt` into this branch.
- Observed `inp`: `1bf1f17e58b446e605ea638600114cc8a7de8560`.
- `git merge-base --all inp HEAD`: `4a10322aa91ac2fe16d7127074a95ba4eab45ba9` and `72cd9d25f9e995b13475054d22d51d2872bb42aa`.
- `git diff inp...HEAD` warns that it uses the first of these bases. Its 57-file, 10,702-line diff includes inherited Lock, Wave, certificate and generated-root integration. The full diff was captured and indexed by path; substantive proof review is confined to the two assigned modules. Inherited implementation is not independently recertified here.

| Input | SHA256 |
|---|---|
| `KAM/SpinOrbit/Lock/Coords/Complex.lean` (178 lines) | `ae90e6f49faf3ff0f82a9d657e4154bce40a56ec7e0f3789d5afcb1940e651d6` |
| `KAM/SpinOrbit/Lock/Coords/HamExpr.lean` (361 lines) | `3cb6ac0a98d41776e8db30e696e9d4adafb3d0aa84d59fbf6c9af604889ae6a7` |
| `/root/code/KAM-inp/.drafts/design/SOLockSignatures.lean` | `aa544d085056410f205df49c08a778e854ad79ea48ad158fffe5302c3d0cd60d` |
| `docs/tracks/SO/design/SO-LOCK-DESIGN.md` | `7785225bb6f3d3985ae7719f3aecf107eb33302530147bbff5672935eb170c6d` |
| `/root/code/KAM-inp-lockgen2/scripts/spin_orbit/lock_ham.py` | `da6405b58e982e4cc4ab84beb924e7a72c874adf8f65e4fc950d243e79a1a142` |
| `/root/code/KAM-inp-lockgen2/scripts/spin_orbit/model.py` | `098081356bb0cdcffedb9fa2be7eb186346136217f9244d2fa117c539b1092bc` |

All source locators below refer to this snapshot. There is no SO blueprint directory or SO statement.md in this checkout; the signed §6 declarations and audited project design are the source contracts. Unrelated I/N/P theorem anchors are not implemented by this slice. Relevant imported frozen definitions were inspected, including the real/complex Hamiltonian vector fields, invariance error, complex strip, frequency map and bordered Hessian. Recursive import inspection found 46 KAM modules, 17 frozen modules, all SEALED definitions, zero providers and zero frozen theorem dependencies. No DRAFT_SORRY or provider is consumed.

## Signed statements and binder fidelity

Namespace throughout: `KAM.SpinOrbit.Lock`. Seven signed headers are text-identical after whitespace normalization. `lockHamExpr` alone shortens `KAM.Certificate.HamExpr 2` to `HamExpr 2` under `open KAM.Certificate`; its elaborated type is identical. Four literal definition bodies (`lockCentreC`, `lockCentreDC`, `lockCentreDDC`, `lockToRotC`) were copied from the signature file under fresh scratch names and checked equal to the implementations by `rfl`. The placeholder signature body of `lockHamExpr` is not mathematical evidence; its body was checked against design §3 and the actual emitter instead.

The three signed theorem headers were copied before `:=` into a scratch namespace under fresh names. Their bodies were exactly:

```lean
exact lockToRotC_ofReal hΩ cs z hI
exact lockHamExpr_eval Ω cs z
exact lockHamExpr_clock Ω hΩ cs z hz
```

These applications pass, preserving binder order, implicit Ω for `_ofReal`, explicit Ω for `_eval`/`_clock`, the real and complex carriers, and the exact clock direction `phaseBasis (.inr 1)`. No draft signature file was imported. No provider/frozen seal probe applies to this infrastructure package.

Every binder of these three results, outer to inner:

| Declaration | Binder | Bin | Contract evidence |
|---|---|---|---|
| `lockToRotC_ofReal` | `{Ω : ℚ}` | TYPING | Signatures:267, design §3 |
| same | `(hΩ : 0 < Ω)` | SOURCE | Signatures:267; positive real-coordinate convention |
| same | `(cs : List ℚ)` | TYPING | Signatures:267 |
| same | `(z : (Fin 2 → ℝ) × (Fin 2 → ℝ))` | TYPING | Signatures:267 |
| same | `(hI : 0 < z.2 0)` | SOURCE | Signatures:268 |
| `lockHamExpr_eval` | `(Ω : ℚ)` | TYPING | Signatures:279; design §3 explicitly every Ω |
| same | `(cs : List ℚ)` | TYPING | Signatures:279 |
| same | `(z : (Fin 2 → ℂ) × (Fin 2 → ℂ))` | TYPING | Signatures:279; every complex z |
| `lockHamExpr_clock` | `(Ω : ℚ)` | TYPING | Signatures:284 |
| same | `(hΩ : 0 < Ω)` | RULED | Signatures:284; design-audit-2 finding 2, accepted in design audit 3 §2 |
| same | `(cs : List ℚ)` | TYPING | Signatures:284 |
| same | `(z : (Fin 2 → ℂ) × (Fin 2 → ℂ))` | TYPING | Signatures:285 |
| same | `(hz : 0 < (z.2 0).re)` | SOURCE | Signatures:285; certified half-plane |

Counts: TYPING 9, SOURCE 3, RULED 1, STANDING 0, EXCESS 0. These propositions contain no hidden assumption bundle, class premise, selected witness or constant-dependence parameter. The logical premises of unsigned generic helpers are visible in their declaration rows below. In particular the summand-derivative premise, the zero summand needed to remove mode 2, and the per-subtree domain-safety premise are used only in generically named helpers; their callers construct the required facts. They do not replace source-level conclusions.

## Complete declaration ledger

`C` means `KAM/SpinOrbit/Lock/Coords/Complex.lean`, `H` means `.../HamExpr.lean`. Every row is one new public declaration; no private declarations, abbreviations or structures are introduced. Contract column `§3` means SO-LOCK coordinates; `tree` also uses LOCK-GEN-2 `lock_ham.py:33–114`. Auxiliary results are stronger/general finite-list or scalar facts rather than substituted source theorems.

| Contract / locator | Declaration | Verdict | Reason / definition classification |
|---|---|---|---|
| §3 / C:33 | `lockCentreC` | PASS | Signed literal complex sine centre; finite sum, 2π(k+1). |
| §3 / C:38 | `lockCentreDC` | PASS | Signed first derivative sum; coefficient 2π(k+1). |
| §3 / C:43 | `lockCentreDDC` | PASS | Signed second derivative sum; negative coefficient and squared frequency. |
| §3 / C:49 | `lockToRotC` | PASS | Signed total map; exact Q₀,Q₁,P₀,P₁ formulas and landed rotated frame. |
| §3 / C:61 | `lockCentreD` | PASS | Literal real first derivative sum; derivative proved below. |
| §3 / C:66 | `lockCentreDD` | PASS | Literal real second derivative sum; derivative proved below. |
| §3 / C:70 | `hasDerivAt_lockSum` | PASS | Generic finite-sum helper; only premise hf is the derivative of each summand. |
| §3 / C:79 | `hasDerivAt_lockCentre_lockCentreD` | PASS | No analytic premise; differentiates each explicit sine summand. |
| §3 / C:91 | `hasDerivAt_lockCentreD` | PASS | No analytic premise; differentiates each explicit cosine summand. |
| §3 / C:104 | `deriv_lockCentre` | PASS | Function equality from the proved pointwise derivative. |
| §3 / C:107 | `deriv_lockCentreD` | PASS | Function equality from the proved pointwise derivative. |
| §3 / C:110 | `deriv_deriv_lockCentre` | PASS | Second derivative follows by rewriting the two preceding equalities. |
| §3 / C:116 | `ofReal_list_sum_map` | PASS | Cast commutes with arbitrary finite list sum. |
| §3 / C:123 | `sqrtE_ofReal_eq` | PASS | All real x, including x≤0; matches the specified total sqrt semantics. |
| §3 / C:132 | `lockCentreC_ofReal` | PASS | All cs and real φ; exact cast identity. |
| §3 / C:139 | `lockCentreDC_ofReal` | PASS | All cs and real φ; exact cast identity. |
| §3 / C:146 | `lockCentreDDC_ofReal` | PASS | All cs and real φ; exact cast identity. |
| §3 / C:153 | `lockToRotC_ofReal` | PASS | Signed contract, Ω>0 and I>0; both premises actually unnecessary for this equality. |
| §3, tree / H:40 | `lockAddAll` | PASS | Literal right-nested sum; empty=const 0, singleton unchanged. |
| §3 / H:45 | `lockAddAll_singleton` | PASS | Exact constructor equation. |
| §3 / H:47 | `lockAddAll_cons_cons` | PASS | Exact constructor equation; preserves right nesting. |
| §3, tree / H:51 | `lockTwoPiExpr` | PASS | Literal (const (2k))·pi; no reassociation in emitted tree. |
| §3, tree / H:54 | `lockXExpr` | PASS | Exact X-root radicand (1/Ω·I)/π and sinMode [1,0]. |
| §3, tree / H:58 | `lockYExpr` | PASS | Exact Y-root radicand (Ω·I)/π and cosMode [1,0]. |
| §3, tree / H:62 | `lockCentreExpr` | PASS | Exact finite sine centre tree; integer keys [0,j+1]. |
| §3, tree / H:67 | `lockCentreDExpr` | PASS | Exact derivative tree and multiplication order. |
| §3, tree / H:72 | `lockCentreDDExpr` | PASS | Exact second derivative tree; negated cs, squared two-pi node. |
| §3, tree / H:78 | `lockForcingModes` | PASS | Exactly ascending modes 1,…,7. |
| §3, tree / H:81 | `lockForcingCosTerm` | PASS | m=2 constant branch is mathematically identical to its zero-frequency cosine. |
| §3, tree / H:86 | `lockForcingSinTerm` | PASS | Literal εA_m sinMode [0,2-m]. |
| §3, tree / H:90 | `lockForcingCos` | PASS | Ascending right-nested forcing sum, constant in second slot. |
| §3, tree / H:93 | `lockForcingSin` | PASS | Same order with m=2 removed; its mathematical sine contribution is zero. |
| §3, tree / H:98 | `lockPotentialExpr` | PASS | Exact addition-formula tree, −cos A·Cs + sin A·Ss; A=4π(c+X). |
| §3, tree / H:104 | `lockHamExpr` | PASS | Signed type; exact six-term emitter design tree, independently kernel-proved at lunar data. |
| §3 / H:111 | `eval_lockAddAll` | PASS | Every list, including empty and singleton; no premise. |
| §3 / H:120 | `eval_lockAddAll_map` | PASS | Every type α, map f, list l and point z; no logical premise. |
| §3 / H:126 | `modePhase_zero_key` | PASS | All integer k; correctly identifies the φ component with factor 2π. |
| §3 / H:130 | `modePhase_alpha` | PASS | Correct α component with factor 2π. |
| §3 / H:133 | `eval_lockXExpr` | PASS | All Ω,z; total division algebra only, including Ω=0. |
| §3 / H:140 | `eval_lockYExpr` | PASS | All Ω,z; multiplication/ring rearrangement only. |
| §3 / H:146 | `eval_lockCentreExpr` | PASS | All cs,z; list evaluation and casts, no positivity premise. |
| §3 / H:154 | `eval_lockCentreDExpr` | PASS | All cs,z; exact derivative coefficient normalization. |
| §3 / H:162 | `eval_lockCentreDDExpr` | PASS | All cs,z; exact sign and squared normalization. |
| §3 / H:170 | `eval_lockForcingCosTerm` | PASS | Every natural m, including m=2; no restricted-mode hypothesis. |
| §3 / H:181 | `eval_lockForcingSinTerm` | PASS | Every natural m; integer-to-complex cast handled correctly. |
| §3 / H:188 | `sum_map_filter_ne_two` | PASS | Generic helper with h:f 2=0; caller proves h by norm_num. |
| §3 / H:202 | `lock_addition_sum` | PASS | Arbitrary complex A and arbitrary finite coefficients/phases; cos addition formula. |
| §3 / H:214 | `eval_lockPotentialExpr` | PASS | All Ω,cs,z; exact seven-mode soVC, including missing zero sine term. |
| §3 / H:251 | `lockHamExpr_eval` | PASS | Signed all-Ω/all-z equality; no root-square or branch premise. |
| §3 / H:263 | `nonvanishingOn_lockAddAll` | PASS | Generic helper assumes domain safety for each list member; actual caller supplies each. |
| §3 / H:274 | `lockCertRegion` | PASS | Literal open half-space {z | 0<Re(z.2 0)}, no hidden compact/domain restriction. |
| §3 / H:276 | `isOpen_lockCertRegion` | PASS | Continuity of action projection and real part; no premise. |
| §3 / H:279 | `re_ratCast_mul_div_pi_pos` | PASS | q>0 and Re w>0 give positive scaled real part; π>0 is proved library fact. |
| §3 / H:287 | `nonvanishingOn_lockXExpr` | PASS | Ω>0 pays for 1/Ω root; π denominator proved nonzero. |
| §3 / H:293 | `nonvanishingOn_lockYExpr` | PASS | Ω>0 pays for Ω root; π denominator proved nonzero. |
| §3 / H:299 | `nonvanishingOn_lockPotentialExpr` | PASS | Ω>0 only; each centre/forcing subtree and X domain obligation supplied. |
| §3 / H:320 | `nonvanishingOn_lockHamExpr` | PASS | Ω>0 only; all six outer terms checked, neither root omitted. |
| §3 / H:342 | `lockHamExpr_clock` | PASS | Signed Ω>0 and Re I>0; full differentiability proved before affine clock-line step. |

## Definition verdicts

All 21 new definitions are literal formulas or finite syntax constructors on their full declared carriers. BODY_MATCH: OK; PUBLIC_CARRIER: OK; WELL_DEFINEDNESS: N/A_LITERAL; CHARACTERIZATION: N/A_LITERAL; CHOICE_INDEPENDENCE: N/A; DEFINITION_VERDICT: PASS, for each definition row above. There is no chosen non-unique mathematical object, deferred characterization, or theorem-shaped assumption bundle.

`cs.getD j 0` is read only for `j` in `List.range cs.length`, so its default never supplies an out-of-range coefficient. The zero branch of `lockAddAll []` is the empty sum, needed for arbitrary lists including `cs=[]`. The `m=2` cosine constant and the filtered zero sine are intended formulas, not arbitrary fallback values. Total rational/complex division at Ω=0 and the inherited specified `sqrtE` semantics on its cut are preserved by all definitions. Their global evaluation identities do not claim global holomorphy. `sqrtE` itself and checker internals are dependencies audited separately, not new definitions of this package.

## Refute-first focus checks

### A. Exact emitter tree, including operation order

Read `/root/code/KAM-inp-lockgen2/scripts/spin_orbit/lock_ham.py`, its rational model table, and the actual Lean constructor definitions. Independently imported that Python module with bytecode writing disabled, then generated:

```python
cs = [Fraction(-3,250000), Fraction(-699,2000000000),
      Fraction(-883,50000000000)]
e = lock_ham.lock_ham_expr(Fraction(8,65), cs, form="design")
emitted = lock_ham.to_lean(e)
```

A fresh Lean example of `lockHamExpr (8/65) lunarLockCentre = <emitted>` closed by:

```lean
norm_num [lockHamExpr, lockAddAll, lockXExpr, lockYExpr, lockCentreExpr,
  lockCentreDExpr, lockCentreDDExpr, lockTwoPiExpr, lockPotentialExpr,
  lockForcingCos, lockForcingSin, lockForcingCosTerm, lockForcingSinTerm,
  lockForcingModes, lunarLockCentre, soEpsQ, soAQ, soCoeffPoly, soEccQ,
  List.range_succ, List.filter]
```

This is equality of inductive expression trees, not just numerical evaluator agreement. It independently repeats the handoff's spot check against freshly read emitter output. The `form="lean"` alternative is not used. For arbitrary nonempty coefficient lists, source inspection confirms the same range/order and coefficient formulas; the concrete equality probe certifies the stated lunar spot check, not an executable Python/Lean universal translation theorem. The emitter's `add_all` does not handle an empty centre list, whereas Lean correctly defines its empty sum. This does not affect its current three-coefficient production tree and is not a disagreement about that emitted tree.

Verified outer right-nested order, with no trailing zero:

1. `.action 1`;
2. `.mul (.const (1/2)) (.pow Y 2)`;
3. `.mul (.const (-1/2)) (.pow C' 2)`;
4. `.mul X C''`;
5. `.add (.mul (.const (-1)) (.mul (.cos A) Cs)) (.mul (.sin A) Ss)`;
6. `.const (-1/2)`.

Here `A = .mul (.mul (.const 4) .pi) (.add C X)`. Centre sums ascend j=0,1,2; forcing cosines ascend m=1,…,7 with the m=2 constant in position 2; sine forcing is m=1,3,4,5,6,7. All scalar rationals match the emitter, including negative Fourier keys and the signs of second-derivative terms. DFS sqrt occurrence order is Y, X in `X C''`, X inside cos A, X inside sin A: four occurrences, two distinct radicands `(Ω·I)/π` and `(1/Ω·I)/π`. No one-root simplification or reassociation changes witness indexing.

### B. All-Ω evaluation and positive-Ω clock

`HamExpr.lean:251–260` literally states `(Ω : ℚ) (cs : List ℚ) (z : complex phase space)` with **no hypotheses**. Expanding `P₀=1+c'+Y` gives `P₀²/2-P₀=(c'+Y)²/2-1/2`; adding `P₁=J̃-c'(c'+Y)+Xc''` cancels the mixed terms and yields `J̃+Y²/2-c'²/2+Xc''+V-1/2`. The proof uses the actual total roots as algebraic atoms. Neither it nor the evaluation helper chain invokes `sqrtE_sq` or replaces a root square by its argument. The X radicand rewrite is a ring identity after casting `1/Ω`; it holds also when Ω=0 under total division. The potential proof pays exactly for its addition formula and m=2 zero sine. Attempted negative/zero Ω and cut-point counterexamples do not invalidate this purely algebraic identity.

`HamExpr.lean:342–357` retains `(hΩ : 0 < Ω)` and `(hz : 0 < Re I)`. The proof constructs `NonvanishingOn lockCertRegion` for the full tree, uses `HamExpr.contDiffOn_eval` on the open region and obtains full `DifferentiableAt ℂ`. Only then does it identify the clock-direction derivative through `eval(z+t·e_J)=eval z+t`. Both root operands have positive real part by positive real scaling, and every division denominator is π≠0. This directly addresses design-audit-2 finding 2: affine dependence on J alone is not used as a substitute for full differentiability. The old negative-Ω counterexample is excluded by the actual signature, not by an undocumented domain convention.

### C. Inherited checker and branch hygiene

HEAD's parent is the merge `aeabfb1f` with parents `72cd9d25` and `4a10322a` (the LOCK-SQRT audited branch). The extra focus explicitly excludes re-auditing the checker. Inspected its exported sqrt/evaluator/domain semantics only to verify the client applies them with the right conditions. No checker, soundness engine, old certificate, or inherited Wave proof is independently certified here.

Refutation of the apparent protected-file violation as a new package edit: `git show --stat HEAD` contains exactly the two assigned additions, 539 lines. `git diff HEAD^ HEAD -- KAM/Frozen manifest KAM.lean KAM/Root README.md` is empty. Nevertheless `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is nonempty: it adds `public import KAM.Root.Wave` to KAM.lean. Frozen/manifest/README diffs alone are empty. The prescribed broad gate is therefore recorded as **NOT SATISFIED, inherited integration**, not silently replaced with a passing narrow command. The whole triple-dot diff also contains inherited generated root-part changes.

Likewise `git diff --check inp...HEAD` exits 2 at `docs/tracks/SO/audits/LOCK-ASM1-audit-1.md:240` (trailing whitespace in a quoted proof line). This path predates HEAD. `git diff --check HEAD^ HEAD` exits 0. These observations survived comparison with the immediate parent; they do not indicate a mathematical or source-hygiene defect in the assigned modules.

## Verification receipt

All Lean-related commands below were serialized by this audit and used `LEAN_NUM_THREADS=1`. The build used the required compile gate; its slot was acquired at 18:20:47 UTC. Dependency warnings were replayed by Lake, not introduced in the scoped files.

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-lockcc KAM.SpinOrbit.Lock.Coords.HamExpr
[inp-gate] slot 2 acquired 18:20:47 for KAM.SpinOrbit.Lock.Coords.HamExpr
⚠ [2904/2919] Replayed KAM.Certificate.Expr.Basic
warning: KAM/Certificate/Expr/Basic.lean:93:5: Variable name `hS` is not explicitly referenced.
Build completed successfully (2919 jobs).
exit 0
```

The gate executes `nice -n 5 lake build`. Both scoped modules were covered. No new production warning or heartbeat failure occurred. No clean/rebuild/cache/update operation was performed.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/LockccAudit.lean
exit 0; no errors or warnings; 37 #print axioms outputs
```

This single successful probe contains the four literal-definition equality checks, the HamExpr type check, all three exact signed theorem applications, all public-theorem axiom checks, and the fresh emitter-tree equality. The first attempt exited 1 because the copied scratch definitions lacked `noncomputable`; restoring the ambient `noncomputable section` fixed the probe without any source change. That initial failure was a probe setup error, not package evidence.

Complete axiom output from the successful run:

```text
'KAM.SpinOrbit.Lock.hasDerivAt_lockSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.hasDerivAt_lockCentre_lockCentreD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.hasDerivAt_lockCentreD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.deriv_lockCentre' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.deriv_lockCentreD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.deriv_deriv_lockCentre' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.ofReal_list_sum_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.sqrtE_ofReal_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockCentreC_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockCentreDC_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockCentreDDC_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockToRotC_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockAddAll_singleton' depends on axioms: [propext, Quot.sound]
'KAM.SpinOrbit.Lock.lockAddAll_cons_cons' depends on axioms: [propext, Quot.sound]
'KAM.SpinOrbit.Lock.eval_lockAddAll' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.eval_lockAddAll_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.modePhase_zero_key' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.modePhase_alpha' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.eval_lockXExpr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.eval_lockYExpr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.eval_lockCentreExpr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.eval_lockCentreDExpr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.eval_lockCentreDDExpr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.eval_lockForcingCosTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.eval_lockForcingSinTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.sum_map_filter_ne_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lock_addition_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.eval_lockPotentialExpr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockHamExpr_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.nonvanishingOn_lockAddAll' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.isOpen_lockCertRegion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.re_ratCast_mul_div_pi_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.nonvanishingOn_lockXExpr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.nonvanishingOn_lockYExpr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.nonvanishingOn_lockPotentialExpr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.nonvanishingOn_lockHamExpr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockHamExpr_clock' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Thus 35 public theorems use `[propext, Classical.choice, Quot.sound]`; the two constructor-equation lemmas use `[propext, Quot.sound]`. All are subsets of the allowed standard axioms. No `sorryAx` or project axiom is present.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.SpinOrbit.Lock.Coords.Complex KAM.SpinOrbit.Lock.Coords.HamExpr
replaying KAM.SpinOrbit.Lock.Coords.HamExpr
replaying KAM.SpinOrbit.Lock.Coords.Complex
exit 0

python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py \
  /root/code/KAM-inp-lockcc KAM.SpinOrbit.Lock.Coords.Complex KAM.SpinOrbit.Lock.Coords.HamExpr
short-name check OK (no reused public short name)
exit 0
```

Both files have copyright comments, `module`, public imports, module docstrings and an exposed public noncomputable section. Both remain below 1500 lines (178 and 361); no line exceeds 100 characters. Their ambient spaces are exactly function spaces on `Fin 2`, with integer Fourier keys. No resource overrides, proof escapes, `sorry`, `admit`, declared axiom, unsafe or opaque declaration was introduced.

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/Certificate.lean, KAM/Root/SpinOrbit.lean)
check_lean_modules: PASS (1658 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
exit 1
```

The sole lint failure is the explicitly permitted stale generated-root line. The module check, frozen-anchor guard and all 158 elaborated ABI hashes pass. No generated root was regenerated. This exception does not turn the separate inherited protected-file diff or inherited whitespace check into passes.

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
warning: inp...HEAD: multiple merge bases, using 4a10322aa91ac2fe16d7127074a95ba4eab45ba9
# nonempty KAM.lean hunk: +public import KAM.Root.Wave

git diff inp...HEAD -- KAM/Frozen manifest README.md
# no diff (same multiple-merge-base warning)

git diff HEAD^ HEAD -- KAM/Frozen manifest KAM.lean KAM/Root README.md
# empty; exit 0

git diff --check inp...HEAD
# exit 2: docs/tracks/SO/audits/LOCK-ASM1-audit-1.md:240: trailing whitespace.

git diff --check HEAD^ HEAD
# exit 0

git diff --check
# exit 0
```

## Findings, uncertainties, errata and closeout

No new mathematical, declaration-fidelity or definition-body defect survived refutation in this package. Design-audit-2 finding 2 is closed by the actual positive-Ω clock signature and its full differentiability proof. No suspected erratum in an external pinned source is alleged. No deviation was introduced into production code by this audit.

Nonblocking notes retained:

- The broad comparison has two merge bases and includes protected/generated integration changes and an inherited Markdown whitespace defect. Attribution is established by the immediate-parent comparison. A policy requiring an entirely empty broad protected-path diff would still need an integration/base decision; this report does not waive that literal gate.
- Generated `KAM/Root/{Certificate,SpinOrbit}.lean` imports are stale. Only the orchestrator should regenerate them, as the audit brief permits.
- `lockToRotC_ofReal` retains signed hΩ and hI even though this total-semantics equality works without them. The new real-centre derivative helper overlaps an existing independently named helper; no short-name collision was found.
- The independent exact tree proof is a lunar-data spot check plus constructor-level source review, not a universal verified Python emitter. It certifies the pinned design form; later emitter changes require a new comparison.

Scope remains the two coordinate modules and their signed client semantics. The separately audited LOCK-SQRT checker, actual certificate values/witnesses, LOCK-GRAPH consumption, physical confinement and the final headline are not certified by this receipt. No new frozen anchor or manifest state was created or sealed.

Closeout: all 58 declaration rows classified; all 21 definition bodies checked; signed binder EXCESS count zero; fresh targeted build, exact probes, all 37 theorem axioms and two-module kernel replay passed; lint passed modulo its named permitted exception; inherited branch hygiene limitations recorded rather than repaired. Snapshot hashes and HEAD/observed inp were rechecked unchanged. The temporary probe, emitted expression, declaration inventory, diff capture and audit logs were deleted after their receipts were included here. The pre-existing untracked handoff was preserved. The only retained auditor-authored file is this report at the user's exact absolute path.
