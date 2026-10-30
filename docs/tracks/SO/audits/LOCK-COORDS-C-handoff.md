# Handoff: LOCK-COORDS-C (track SO part 3, D45)

Branch `inp-lockcc`, worktree /root/code/KAM-inp-lockcc. Base aeabfb1f.

## Files (new)
- `KAM/SpinOrbit/Lock/Coords/Complex.lean` (178 lines): `lockCentreC`, `lockCentreDC`, `lockCentreDDC`,
  `lockToRotC` (all verbatim from the signatures file), real derivative sums `lockCentreD`, `lockCentreDD`,
  `hasDerivAt_lockSum`, `hasDerivAt_lockCentre_lockCentreD`, `hasDerivAt_lockCentreD`, `deriv_lockCentre`,
  `deriv_lockCentreD`, `deriv_deriv_lockCentre`, `ofReal_list_sum_map`, `sqrtE_ofReal_eq`
  (`sqrtE x = √x` for every real `x`), `lockCentreC/DC/DDC_ofReal`, **`lockToRotC_ofReal`** (signed).
- `KAM/SpinOrbit/Lock/Coords/HamExpr.lean` (~360 lines): `lockAddAll` (+ `@[simp]` `lockAddAll_singleton`,
  `lockAddAll_cons_cons`), `lockTwoPiExpr`, `lockXExpr`, `lockYExpr`, `lockCentreExpr`, `lockCentreDExpr`,
  `lockCentreDDExpr`, `lockForcingModes`, `lockForcingCosTerm`, `lockForcingSinTerm`, `lockForcingCos`,
  `lockForcingSin`, `lockPotentialExpr`, **`lockHamExpr`**, eval lemmas for each piece, `lock_addition_sum`,
  **`lockHamExpr_eval`** (signed, all Ω, all z), `lockCertRegion = {z | 0 < Re z.2 0}`, `isOpen_lockCertRegion`,
  `nonvanishingOn_lockHamExpr` (0 < Ω), **`lockHamExpr_clock`** (signed, with `0 < Ω`).

All signed declarations have exactly the names/types of SOLockSignatures.lean §6 (namespace `KAM.SpinOrbit.Lock`;
`sqrtE` is the landed `KAM.Certificate.sqrtE`, opened).

## Approach
- `_ofReal`: `sqrtE (x:ℂ) = (√x : ℂ)` for all real x (both 0 when x ≤ 0), list-sum casts, and
  `deriv (lockCentre cs) = lockCentreD cs`, `deriv (deriv …) = lockCentreDD cs` via HasDerivAt over list sums.
  (`hΩ`, `hI` are not actually needed but kept as signed.)
- `_eval`: `eval_lockAddAll` turns the right-nested sum into a list sum; each piece evaluates to the
  corresponding `lockToRotC` ingredient (radicand `(1/Ω·I)/π = I/(πΩ)`, `(Ω·I)/π = IΩ/π` by `ring`, valid
  for every Ω incl. 0); potential: `soVC` re-indexed as in `soHamExpr_eval`, `2π(2(u+φ)−mφ) = 4πu + 2π(2−m)φ`,
  then a summed addition formula; the sine sum's missing m = 2 term is 0. Pure algebra, no `sqrtE² = z`.
- `_clock`: structural `HamExpr.contDiffOn_eval` on the open `lockCertRegion` (both sqrt operands are
  positive-real multiples of I when 0 < Ω; the divisions are by π) gives differentiability; then
  `fderiv_apply_eq_deriv_line` and `eval(z + t e_{J̃}) = eval z + t` (from `_eval`).

## Exact node order (for LOCK-DATA)
`lockHamExpr Ω cs = lockAddAll [T1..T6]`, right-nested (`add T1 (add T2 (… (add T5 T6)))`, singleton list = its
element, no trailing `const 0`):
1. `.action 1`
2. `.mul (.const (1/2)) (.pow Y 2)`, `Y = .mul (.sqrt (.div (.mul (.const Ω) (.action 0)) .pi)) (.cosMode [1, 0])`
3. `.mul (.const (-1/2)) (.pow C' 2)`, `C' = lockAddAll_j [.mul (.mul (.const cs_j) (.mul (.const (2(j+1))) .pi)) (.cosMode [0, j+1])]`
4. `.mul X C''`, `X = .mul (.sqrt (.div (.mul (.const (1/Ω)) (.action 0)) .pi)) (.sinMode [1, 0])`,
   `C'' = lockAddAll_j [.mul (.mul (.const (-cs_j)) (.pow (.mul (.const (2(j+1))) .pi) 2)) (.sinMode [0, j+1])]`
5. `V = .add (.mul (.const (-1)) (.mul (.cos A) Cs)) (.mul (.sin A) Ss)`, `A = .mul (.mul (.const 4) .pi) (.add C X)`,
   `C = lockAddAll_j [.mul (.const cs_j) (.sinMode [0, j+1])]`;
   `Cs = lockAddAll_{m=1..7} [m = 2 ? .const (εA_2) : .mul (.const (εA_m)) (.cosMode [0, 2-m])]`,
   `Ss = lockAddAll_{m∈{1,3,4,5,6,7}} [.mul (.const (εA_m)) (.sinMode [0, 2-m])]`, `εA_m = soEpsQ * soAQ m`.
6. `.const (-1/2)`

Sqrt nodes in DFS (left-to-right) order: (2) Y-root √((Ω·I)/π); (4) X-root √((1/Ω·I)/π); (5) X-root inside `cos A`;
(5) X-root inside `sin A` — 4 sqrt occurrences, 2 distinct radicands (design two-root form, not the one-root
"lean" variant).

**Checked against the emitter**: in a deleted scratch file,
`example : lockHamExpr (8/65) lunarLockCentre = <output of lock_ham.to_lean(lock_ham_expr(8/65, cs), form "design")>`
closed by `simp only [defs…]; norm_num [List.range_succ, List.filter, lockAddAll_cons_cons, …, soAQ, soCoeffPoly,
soEccQ, soEpsQ]` with no error: the trees agree node for node (ℚ constants equal as values; Lean's constants are
the expressions `soEpsQ * soAQ m`, `2 * ((j:ℚ)+1)`, `1/Ω`, `-cs_j`, which reduce to the emitter's literals).
Emitter output used:
```
(.add (.action 1) (.add (.mul (.const (1 / 2)) (.pow (.mul (.sqrt (.div (.mul (.const (8 / 65)) (.action 0)) .pi)) (.cosMode [1, 0])) 2)) (.add (.mul (.const (-1 / 2)) (.pow (.add (.mul (.mul (.const (-3 / 250000)) (.mul (.const (2)) .pi)) (.cosMode [0, 1])) (.add (.mul (.mul (.const (-699 / 2000000000)) (.mul (.const (4)) .pi)) (.cosMode [0, 2])) (.mul (.mul (.const (-883 / 50000000000)) (.mul (.const (6)) .pi)) (.cosMode [0, 3])))) 2)) (.add (.mul (.mul (.sqrt (.div (.mul (.const (65 / 8)) (.action 0)) .pi)) (.sinMode [1, 0])) (.add (.mul (.mul (.const (3 / 250000)) (.pow (.mul (.const (2)) .pi) 2)) (.sinMode [0, 1])) (.add (.mul (.mul (.const (699 / 2000000000)) (.pow (.mul (.const (4)) .pi) 2)) (.sinMode [0, 2])) (.mul (.mul (.const (883 / 50000000000)) (.pow (.mul (.const (6)) .pi) 2)) (.sinMode [0, 3]))))) (.add (.add (.mul (.const (-1)) (.mul (.cos (.mul (.mul (.const (4)) .pi) (.add (.add (.mul (.const (-3 / 250000)) (.sinMode [0, 1])) (.add (.mul (.const (-699 / 2000000000)) (.sinMode [0, 2])) (.mul (.const (-883 / 50000000000)) (.sinMode [0, 3])))) (.mul (.sqrt (.div (.mul (.const (65 / 8)) (.action 0)) .pi)) (.sinMode [1, 0]))))) (.add (.mul (.const (-30293382628719 / 6400000000000000000)) (.cosMode [0, 1])) (.add (.const (10956894809778832497 / 64000000000000000000000)) (.add (.mul (.const (210729263332437 / 6400000000000000000)) (.cosMode [0, -1])) (.add (.mul (.const (7022811744278271 / 1600000000000000000000)) (.cosMode [0, -2])) (.add (.mul (.const (204324809470484816673 / 409600000000000000000000000)) (.cosMode [0, -3])) (.add (.mul (.const (3340916932132377 / 64000000000000000000000)) (.cosMode [0, -4])) (.mul (.const (261929774188365170769 / 51200000000000000000000000000)) (.cosMode [0, -5])))))))))) (.mul (.sin (.mul (.mul (.const (4)) .pi) (.add (.add (.mul (.const (-3 / 250000)) (.sinMode [0, 1])) (.add (.mul (.const (-699 / 2000000000)) (.sinMode [0, 2])) (.mul (.const (-883 / 50000000000)) (.sinMode [0, 3])))) (.mul (.sqrt (.div (.mul (.const (65 / 8)) (.action 0)) .pi)) (.sinMode [1, 0]))))) (.add (.mul (.const (-30293382628719 / 6400000000000000000)) (.sinMode [0, 1])) (.add (.mul (.const (210729263332437 / 6400000000000000000)) (.sinMode [0, -1])) (.add (.mul (.const (7022811744278271 / 1600000000000000000000)) (.sinMode [0, -2])) (.add (.mul (.const (204324809470484816673 / 409600000000000000000000000)) (.sinMode [0, -3])) (.add (.mul (.const (3340916932132377 / 64000000000000000000000)) (.sinMode [0, -4])) (.mul (.const (261929774188365170769 / 51200000000000000000000000000)) (.sinMode [0, -5]))))))))) (.const (-1 / 2)))))))
```

## Checks
- `inp_lake_build.sh … KAM.SpinOrbit.Lock.Coords.HamExpr` (builds Complex too): `Build completed successfully
  (2919 jobs)`, no warnings in my files.
- `scripts/lint_sources.sh`: no long lines / module issues in my files; `check_lean_modules: PASS`, `FROZEN-ANCHOR
  GUARD OK`, `ABI HASHES OK (158 frozen declarations)`; it also prints `KAM.lean is out of date; run
  scripts/gen_root_imports.py (KAM/Root/Certificate.lean, KAM/Root/SpinOrbit.lean)` — generated root files, not
  edited per rule 10 (Certificate part predates this package: LOCK-SQRT's new files); orchestrator should regenerate.
- `main_shortname_check.py`: `short-name check OK` (after renaming four first-draft names that clashed with
  Assembly.lean/Confine.lean: list-sum HasDerivAt helper, `hasDerivAt_lockCentre`, `lockRegion`, `isOpen_lockRegion`).
  Note: Assembly.lean already proves its own `hasDerivAt_lockCentre`; mine is `hasDerivAt_lockCentre_lockCentreD`
  (same content, explicit-sum derivative) — a later cleanup could dedupe.
- `#print axioms` (scratch, deleted): `lockHamExpr_eval`, `lockHamExpr_clock`, `lockToRotC_ofReal`,
  `nonvanishingOn_lockHamExpr`: `[propext, Classical.choice, Quot.sound]`.

## Uncertainties / deviations / errata
- No signature was wrong. No heartbeat issues (no overrides).
- Deviation (benign): extra public helpers listed above; `lockToRotC_ofReal` does not use its hypotheses.
- No suspected errata in pinned sources.
