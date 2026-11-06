# N5a-2 handoff (T2-CONF): the bridge `Ht ↔ h_m`

Worker g2-n5a (package N5a-2, split off N7): the generic part, committed in b15dedbe8. Worker g2-n6 took over the
instance on 6 November 2026 (g2-n5a hit its usage limit). Brief `.drafts/g2/BRIEF-N5a2-HtBridge.md`. Names were
coordinated with N7 (kam-sjsu-g2-4d).

**Status: complete.**
- **Generic part** (`Tube/Poly/HtDense`, `Tube/Poly/HtBridge`, `SJSU/Ham/HtBridge`): committed in b15dedbe8 and
  audited in N7b-N5a2-AUDIT-1 (PASS WITH NOTES).
- **Instance** (`SJSU/Ham/HtBridgeInst` and its 6 submodules): new and uncommitted. It is a separate deliverable,
  not covered by that audit. `sjsuHD_Ht_eq_hCoef` is proved against N7's built `Ledger.H.HData`. No `sorry`,
  `axiom` or `set_option`; the axioms are only `propext`, `Classical.choice` and `Quot.sound`.

## Files
| file | lines | content |
|---|---:|---|
| `KAM/EffectiveStability/Tube/Poly/HtDense.lean` | 179 | `boxIdx`, `inBox`, `boxKey_boxIdx`, `denseCos_eq_sum`, `pDense`, **`denseCos_pDense`**, `scatter`, `incFrom`, `sum_scatter`, **`denseCos_scatter`**, `all_of_blocks` |
| `KAM/EffectiveStability/Tube/Poly/HtBridge.lean` | 351 | (1) `sum_filter_of_zero`, `sum_regroup_range`, `HData.Ut_eq`, `HData.Vt_eq`, `HData.Ht_eq_range`, **`HData.Ht_eq_sum`**; (2) `ofTriple`, `tripleExp`, `gbQ_eq_prod`, **`gbQ_eq_gbinom`**, `rowCoefQ`, `tTerms`, **`Tn_eq_denseCos`**, `bPairs`, **`tubeCenter_eq_denseCos`**, `tubeCenter_ge`, **`HData.Ht_eq_hCoef`** |
| `KAM/EffectiveStability/SJSU/Ham/HtBridge.lean` | 109 | `sjsuB_margin` (kernel), **`sjsuB_pos`**, `sjsuEccModes_box`, `sjsuBPairs_inc` (kernel), **`sjsuB_eq_denseCos`**, `sjsuHwAll_le`, `sjsuTTerms_box`, **`sjsuTn_eq_denseCos`** |
| `KAM/EffectiveStability/SJSU/Ham/HtBridgeInst.lean` (instance) | 68 | `sjsuTdat_blocks`, `sjsuTdat_eq`, `sjsuHD_Tt_eq`, `sjsuHD_Bt_eq`, **`sjsuHD_Ht_eq_hCoef`** |
| `…/HtBridgeInst/Groups.lean` (instance) | 45 | `sjsuNs_key_chain` (kernel), **`sjsuNs_nodup`**, `sjsuNs_bound`, `sjsuNs_length` (kernel), `tdatOk` |
| `…/HtBridgeInst/Tdat0.lean`, `Tdat1.lean`, `Tdat2.lean` (instance) | 151 each | `sjsuTdat_block0`–`89` (kernel, 8 groups each), `sjsuTdat_blocks0`–`2` (ranges 0–29, 30–59, 60–89) |
| `…/HtBridgeInst/Bdat.lean` (instance) | 50 | `sjsuBdat_check0`–`2` (kernel), `sjsuBdat_check` |
| `…/HtBridgeInst/HwGroups.lean` (instance) | 108 | `nsKey`, `keyMask`, `sjsuNsMask`, `rowGroupOk`, `nsKey_inj`, `exists_of_testBit_keyMask`, `mem_of_rowGroupOk`, `sjsuHw0_groups`–`9` (kernel), **`sjsuHwAll_groups`** |

## Main statements (exact)

```lean
-- (1) N7's statement, verbatim (the Nodup hypothesis is not needed; kept as `_hnd`)
theorem HData.Ht_eq_sum (D : HData) (Tt : ℕ × ℕ × ℕ → (Fin 2 → ℝ) → ℝ) (Pt : ℕ → ℤ → (Fin 2 → ℝ) → ℝ)
    (_hnd : D.ns.Nodup) (hb : ∀ n ∈ D.ns, n.1 ≤ D.Nmax ∧ n.2.1 ≤ D.Nmax ∧ n.2.2 ≤ D.Nmax)
    (m : ℕ × ℕ × ℕ) (φ : Fin 2 → ℝ) :
    D.Ht Tt Pt m φ =
      (D.ns.map fun n => ((gbQ n.1 m.1 * gbQ n.2.1 m.2.1 * gbQ n.2.2 m.2.2 : ℚ) : ℝ) *
        (Tt n φ * Pt 0 ((n.1 : ℤ) - 2 * m.1) φ * Pt 1 ((n.2.1 : ℤ) - 2 * m.2.1) φ *
          Pt 2 ((n.2.2 : ℤ) - 2 * m.2.2) φ)).sum

-- (2) the bridge for an arbitrary D, the data equalities as hypotheses
theorem HData.Ht_eq_hCoef (D : HData) (E N : ℕ) (rows : List ((Mon × Mon) × ℤ))
    (B : (Fin 2 → ℝ) → Fin 3 → ℝ) (hnd : D.ns.Nodup)
    (hb : ∀ n ∈ D.ns, n.1 ≤ D.Nmax ∧ n.2.1 ≤ D.Nmax ∧ n.2.2 ≤ D.Nmax)
    (hT : ∀ n ∈ D.ns, D.Tt n = Tn E N rows (ofTriple n))
    (hB : ∀ j : Fin 3, D.Bt j = fun φ => B φ j) (hpos : ∀ φ j, 0 < B φ j)
    (hns : ∀ e ∈ rows, tripleExp e ∈ D.ns) (m : ℕ × ℕ × ℕ) (φ : Fin 2 → ℝ) :
    D.Ht D.Tt D.Pt m φ = hCoef E N rows B (ofTriple m) φ

theorem gbQ_eq_gbinom (n m : ℕ) : ((gbQ n m : ℚ) : ℝ) = gbinom ((n : ℝ) / 2) m
theorem Tn_eq_denseCos (E N C : ℕ) (rows) (n : ℕ × ℕ × ℕ)
    (hbox : ∀ t ∈ tTerms E N rows n, inBox C t.1 = true) (φ) :
    Tn E N rows (ofTriple n) φ = denseCos C (pDense C (tTerms E N rows n)) φ
theorem tubeCenter_eq_denseCos (C : ℕ) (modes : List (ℤ × ℤ × ℚ)) (Ibar : Fin 3 → ℚ) (j : Fin 3)
    (hbox : ∀ x ∈ modes, inBox C (x.1, x.2.1) = true)
    (hinc : incFrom 0 (bPairs C modes Ibar j) = true) (φ) :
    tubeCenter modes Ibar j φ =
      denseCos C (scatter ((2 * C + 1) * (2 * C + 1)) 0 (bPairs C modes Ibar j)) φ

-- SJSU
theorem sjsuB_pos (φ : Fin 2 → ℝ) (j : Fin 3) : 0 < sjsuB φ j
theorem sjsuB_eq_denseCos (j : Fin 3) : (fun φ => sjsuB φ j) =
    denseCos 30 (scatter ((2 * 30 + 1) * (2 * 30 + 1)) 0 (bPairs 30 sjsuEccModes sjsuEccIbar j))
theorem sjsuTn_eq_denseCos (n : ℕ × ℕ × ℕ) : Tn sjsuE sjsuN sjsuHwAll (ofTriple n) =
    denseCos 9 (pDense 9 (tTerms sjsuE sjsuN sjsuHwAll n))
theorem sjsuHD_Ht_eq_hCoef (m : ℕ × ℕ × ℕ) (φ : Fin 2 → ℝ) :
    sjsuHD.Ht sjsuHD.Tt sjsuHD.Pt m φ = hCoef sjsuE sjsuN sjsuHwAll sjsuB (ofTriple m) φ
```
`hCoef`, `Tn` are N5a's (`Tube/Poly/HTilde.lean`). `hTildeOf_taylor` and `hRem_tube` complete the Taylor split
with the remainder bounds.

## Approach
1. **Regrouping (1).** Each level of N7's nested sum runs over a filtered list. The filters drop only terms with a
   zero `gbQ` factor or an empty inner sum (`sum_filter_of_zero`), so:
   - `Ut` sums over the groups with `(n₁, n₂)` fixed (`Ut_eq`; `n₃ ≤ Nmax` from `hb`);
   - `Vt` and `Ht` sum over `List.range (Nmax + 1)` (`Vt_eq`, `Ht_eq_range`);
   - regrouping the flat sum by `n₁`, then by `n₂` (`sum_regroup_range`), and pushing the factors into the sums
     gives `Ht_eq_sum`.
2. **Bridge (2).**
   - `gbQ n m = binom(n/2, m)` (`gbQ_eq_gbinom`, through N4's `gbinom_ratCast`);
   - `√B^{n − 2m} = B^{n/2 − m}` for `B > 0` (N4's `rpow_half_sub`);
   - the sum over the list `ns` becomes the `Finset` sum over `expSet rows`: every row exponent is a group (`hns`),
     and a group with no row has `T_n = 0` (`Finset.sum_subset`).
3. **Data.**
   - `T_n` is a cosine series of its rows; `denseCos_pDense` writes it as N7's dense box list (slot = sum of the
     values with that box index).
   - `B_j` (N6's `tubeCenter`) is `Ī_j` at the centre plus `−m_j σ` at each mode; `denseCos_scatter` writes the
     index-sorted pairs as a dense list in one pass.
   - `sjsuB_pos`: `|cos| ≤ 1` and a kernel margin `Ī_j − Σ|m_j σ| > 0`. The margins are 2.9·10⁻⁴, 6.5·10⁻⁴ and
     2.4·10⁻⁵ (floats).

## Checks
Generic part: see N7b-N5a2-AUDIT-1 (builds with 0 warnings in the three files; axioms as below). Instance
(g2-n6, 6 November 2026, after N7 built `KAM.EffectiveStability.SJSU.Ledger.H.HData`; N7 confirmed the names final):

- **Builds**, one module at a time through `.drafts/g2/g2lake build`, all "Build completed successfully", no
  warning in the instance files:

  | module | CPU | peak RSS (incl. ~1.5–3.5 GB of mapped imports) |
  |---|---:|---:|
  | `SJSU.Ham.HtBridgeInst.Groups` | 5 s | 2.1 GB |
  | `SJSU.Ham.HtBridgeInst.Tdat0` | 383 s | 5.1 GB |
  | `SJSU.Ham.HtBridgeInst.Tdat1` | 596 s | 5.0 GB |
  | `SJSU.Ham.HtBridgeInst.Tdat2` | 710 s | 6.0 GB |
  | `SJSU.Ham.HtBridgeInst.HwGroups` | 9 s | 2.2 GB |
  | `SJSU.Ham.HtBridgeInst.Bdat` | 37 s | 3.4 GB |
  | `SJSU.Ham.HtBridgeInst` | 4 s | 2.0 GB |

- **Axioms and exact statement** (`.drafts/g2/scratch/n5a2-g2n6/Axioms.lean`, output in `axioms.out`). All of the
  following show `[propext, Classical.choice, Quot.sound]`:
  - generic: `HData.Ht_eq_sum`, `HData.Ht_eq_hCoef`, `gbQ_eq_gbinom`, `Tn_eq_denseCos`, `tubeCenter_eq_denseCos`,
    `tubeCenter_ge`, `denseCos_pDense`, `denseCos_scatter`;
  - SJSU facts: `sjsuB_pos`, `sjsuB_eq_denseCos`, `sjsuTn_eq_denseCos`;
  - instance: `sjsuNs_nodup`, `mem_of_rowGroupOk`, `sjsuHD_Bt_eq`, `sjsuTdat_eq`, `sjsuBdat_check`,
    `sjsuHwAll_groups`, **`sjsuHD_Ht_eq_hCoef`**.

  `all_of_blocks` shows `[propext, Quot.sound]`. The file also elaborates an `example` with the exact statement
  of `sjsuHD_Ht_eq_hCoef`.
- **Hygiene.** No `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `set_option` or `EuclideanSpace` in the instance
  files. Every file is a module (header, `module`, `public import`, docstring, exposed public section), all ≤ 151
  lines, no line over 100 columns.
- **Names.** None of the 125 declarations in `HtBridgeInst/` duplicates a declaration name elsewhere in
  `KAM/EffectiveStability`.
- **Lint.** `.drafts/g2/lint_noabi.sh` (`abi_hashes` skipped, per the rule) exited 1 only for
  `KAM.lean is out of date` (the roots, kam-g2's step: the new SJSU modules, these included). Passed:
  `check_lean_modules: PASS (18629 Lean files)`, the unit tests `OK` (29 and 8), `FROZEN-ANCHOR GUARD OK`. No
  width finding.
- **Audit N7b-N5a2-AUDIT-1 N1** (template placeholders): resolved by this handoff. The status, the line counts,
  the checks and the axioms are filled in, and the instance is labelled as a separate deliverable, not covered by
  that audit. N2 (width) was resolved by the reflow.

## Design signals
- `List.sum` over the 2,790 σ terms gets stuck in the kernel (the `foldr` nests one `Rat.add` per term). The margin
  check uses N7's balanced `treeSumG` (`treeSumG_eq`).
- The per-index filter (`pDense`) is used only for `T_n`, where each group has few terms. For `B_j`, a per-index
  filter over 2,790 modes × 3,721 slots would cost about 10M kernel steps per component, so it uses the linear
  `scatter` of sorted pairs (checked sorted in the kernel). N7 independently moved its own `denseQ` to a one-pass
  merge.
- **Instance (g2-n6).** Four default-limit failures, each fixed by restructuring; no options were used.
  1. **`sjsuNs.Nodup` by `decide +kernel`.** The pairwise check over 714 triples hit the 6 GB memory cap
     (the cgroup OOM-killed `lean`). It is replaced by a linear kernel check that the keys
     `(n₁·32 + n₂)·32 + n₃` are strictly increasing (`List.IsChain (· < ·)`), plus `Nodup.of_map`.
  2. **`tripleExp e ∈ sjsuNs` per `H_w` row.** A linear search for each of about 2,000 rows in degree 9 hit
     the cap. Even with `Nat` keys and `List.elem` it still OOMs: kernel memory grows with the number of
     steps in one declaration. It is replaced by a bit mask `Σ 2^key` of the groups and `Nat.testBit`, a
     constant number of steps per row (`HwGroups`; the degree-9 check now takes seconds).
  3. **`T_n` blocks.** One block of 24 groups needs about 4 GB of anonymous memory, so two blocks
     elaborating in parallel exceed the cap. The blocks are now 8 groups (about 1.7 GB), split over three
     modules. The `B_j` checks are one declaration per component, in their own module.
  4. **Recursion depth.** `all_of_blocks` with implicit `c`, `K` made the unifier solve `8 * 90 =?= ?c * ?K`,
     and `rfl` for `sjsuHD.Bt j = denseCos 30 (sjsuBdat j)` let it evaluate `denseQ 3721`. Both reached the
     maximum recursion depth. They are fixed by passing `(c := 8) (K := 90)` and by unfolding with
     `simp only [HData.Bt, sjsuHD]`.

## Uncertainties / deviations
- `HData.Ht_eq_sum` keeps N7's `Nodup` hypothesis, renamed `_hnd` (unused). `Ht_eq_hCoef` does use `Nodup`.
- `tubeCenter_eq_denseCos` puts `Ī_j` in its own pair (`bPairs.insertPair`). It requires that no mode is `(0, 0)`:
  `incFrom` fails otherwise, so the kernel check would fail rather than prove something false. The SJSU σ has no
  `(0, 0)` mode.
- The instance depends on N7's names: `sjsuNs` (714 groups), `sjsuTdat`, `sjsuBdat`, `sjsuHD` in
  `KAM.EffectiveStability.SJSU.Ledger.H.HData`. N7 confirmed them final. `sjsuHD.Tt n = denseCos 9 (sjsuTdat n)`
  and `sjsuHD.Bt j = denseCos 30 (sjsuBdat j)` hold by definition (`sjsuHD_Tt_eq`, `sjsuHD_Bt_eq`). If N7
  regenerates the ledger, the instance must be rebuilt; the block count 90 assumes ≤ 720 groups.
- **Build cost and memory.** About 29 CPU-minutes, mostly the 90 `T_n` blocks. `Tdat2` peaked at 6.0 GB RSS,
  close to the g2lake cap (the margin is in anonymous memory, which was lower). If it ever OOMs under
  `LEAN_NUM_THREADS=2`, split it further (blocks of 4, or one module per 10 blocks).
- **The instance is unaudited.** It is a separate deliverable, outside N7b-N5a2-AUDIT-1's scope.
- No suspected errata in pinned sources.

READY g2-n5a2
