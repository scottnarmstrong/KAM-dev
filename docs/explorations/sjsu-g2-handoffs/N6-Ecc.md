# N6-Ecc handoff (T2-CONF): rigorous eccentricity enclosure on the tube

Worker g2-n6, 6 November 2026. Status: **complete.** Owner ruling (a) is proved as stated: on the whole tube
(all `φ`, all `|v_k| ≤ 2·10⁻⁶`), the two-sided eccentricity intervals Jupiter `[0.026, 0.062]`, Saturn
`[0.009, 0.085]`, Uranus `[0.006, 0.063]` hold, with a φ-resolved enclosure. **No interval was widened.**
Kernel cost: about **4 CPU-min**, against a budget of about 1 CPU-h. There is no `sorry`, `axiom` or
`set_option`, every file is ≤ 1500 lines, and the axioms are only `propext`, `Classical.choice` and
`Quot.sound`.

## Files

Core, namespace `KAM.EffectiveStability.Tube`, directory `KAM/EffectiveStability/Tube/Ecc/`:

| file | lines | content |
|---|---:|---|
| `Circle.lean` | 383 | Gaussian rationals `GQ` and integers `GZ` with their complex values; power tables `GZ.table`/`GZ.zpowT` (`toC_zpowT`); the rational circle chart `wt t = (1+it)/(1−it)`, `circPt`/`circDer`/`circG`/`circN`; covering `exists_circ`; the remainder `norm_circ_remainder` and chord `norm_circ_sub` bounds |
| `Defs.lean` | 288 | `tubeCenter`, `eccGamma`, `tubeCenterW`, `zW`; `EccData`; the computable checker: `fixOf`, `errSum`, `lipSum₁/₂`, `treeSum`, `globalOK`, `bSumZ`, `sqrtOK`, `zOK`, `leafOK`, `ETree`, `EBox`, `checkTree`, `checkTree_split_intro` |
| `Center.lean` | 325 | centre soundness: `tubeCenter_eq_W`, `abs_tubeCenterW_sub_le` (Lipschitz), `abs_tubeCenterW_sub_fix_le` (rounding), `bSumZ_div_eq` (the integer evaluation), `globalOK_spec` |
| `Gamma.lean` | 223 | `normSq_bounds_of_cell` (the per-cell linearization), `ecc_bounds_of_gamma` |
| `Sound.lean` | 315 | `leafOK_sound`, `checkTree_sound`, `eccGamma_eq_normSq`, `eccGamma_phase`, **`eccGamma_bounds_of_check`** |

SJSU instance, namespace `KAM.EffectiveStability.SJSU`, directory `KAM/EffectiveStability/SJSU/Ecc/`
(application modules for `KAMSJSU`, built by name). Everything except `Main.lean` is generated:

| file | lines | content |
|---|---:|---|
| `Modes0.lean`, `Modes1.lean` | 1426 each | the 2,790 modes `(m₁, m₂, σ)` of `S`, exact, in JSON file order (`dyMode m₁ m₂ n e = (m₁, m₂, n/2^e)`) |
| `Data.lean` | 211 | `sjsuEccModes`, `sjsuEccIbar`, `sjsuEccV` (exact `V′`), `sjsuEccFix` (130 fixed-point modes), `sjsuEccData`, `sjsuEcc_globalOK` (`decide +kernel`) |
| `TreePP/PM/MP/MM.lean` | 1251/559/901/699 | the four chart trees (signs `±, ±`): 900 leaves in 46 blocks of ≤ 32 leaves, one `decide +kernel` per block, assembled by `checkTree_split_intro` |
| `Main.lean` | 114 | `sjsuB`, `sjsuLambdaStar`, `sjsuGammaLo/Hi`, **`sjsu_tube_gamma`, `sjsu_tube_ecc`, `sjsu_tube_ecc_of_dev`** |

Generator and mirror (scratch; not repository code): `.drafts/g2/scratch/N6-Ecc/`. The files are
`common.py` (data), `mirror.py` (exact Fraction mirror of the checker and the tree generator; writes
`trees.pkl`), `gen_lean.py` and `lean_fmt.py` (write all the SJSU files) and `margins.py` (certified ranges).
Reproduce with `python3 mirror.py && python3 gen_lean.py` (about 5 s). Data source:
`.drafts/g2/data/literal-v1.json` (sha256 `95b841cee81ef862…`) and `applications/sjsu/data/sjsu18-o2.json`
(`Lambda_star`).

## Main theorems (exact statements)

Definitions (core, `Defs.lean`):

```lean
def modeK (m₁ m₂ : ℤ) (k : Fin 3) : ℤ := ![m₁, m₂, -m₁ - m₂] k

noncomputable def tubeCenter (modes : List (ℤ × ℤ × ℚ)) (Ibar : Fin 3 → ℚ) (k : Fin 3)
    (φ : Fin 2 → ℝ) : ℝ :=
  (Ibar k : ℝ) + (modes.map fun x =>
    -((modeK x.1 x.2.1 k : ℤ) : ℝ) * (x.2.2 : ℝ) * Real.cos (x.1 * φ 0 + x.2.1 * φ 1)).sum

noncomputable def eccGamma (V : Fin 3 → Fin 3 → ℚ) (I : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (j : Fin 3) : ℝ :=
  (∑ k, (V j k : ℝ) * Real.sqrt (I k) * Real.cos (![φ 0, φ 1, 0] k)) ^ 2 +
    (∑ k, (V j k : ℝ) * Real.sqrt (I k) * Real.sin (![φ 0, φ 1, 0] k)) ^ 2
```

Generic enclosure (`Sound.lean`):

```lean
theorem eccGamma_bounds_of_check {d : EccData} (hg : globalOK d = true) (T : Bool → Bool → ETree)
    (hT : ∀ s₁ s₂, checkTree d (rootBox s₁ s₂) (T s₁ s₂) = true) (φ : Fin 2 → ℝ) (I : Fin 3 → ℝ)
    (hI : ∀ k, |I k - tubeCenter d.modes d.Ibar k φ| ≤ d.r) (j : Fin 3) :
    (d.Glo j : ℝ) ≤ eccGamma d.V I φ j ∧ eccGamma d.V I φ j ≤ d.Ghi j

theorem eccGamma_phase (V : Fin 3 → Fin 3 → ℚ) (I : Fin 3 → ℝ) (θ : Fin 3 → ℝ) (j : Fin 3) :
    (∑ k, (V j k : ℝ) * Real.sqrt (I k) * Real.cos (θ k)) ^ 2 +
        (∑ k, (V j k : ℝ) * Real.sqrt (I k) * Real.sin (θ k)) ^ 2 =
      eccGamma V I ![θ 0 - θ 2, θ 1 - θ 2] j

theorem ecc_bounds_of_gamma {Λ Γ Glo Ghi lo hi : ℝ} (hΛ : 0 < Λ) (hhi : 0 ≤ hi)
    (h1 : Glo ≤ Γ) (h2 : Γ ≤ Ghi) (hu : 0 ≤ 1 - Ghi / Λ)
    (hl : (1 - Glo / Λ) ^ 2 ≤ 1 - lo ^ 2) (hh : 1 - hi ^ 2 ≤ (1 - Ghi / Λ) ^ 2) :
    lo ≤ Real.sqrt (1 - (1 - Γ / Λ) ^ 2) ∧ Real.sqrt (1 - (1 - Γ / Λ) ^ 2) ≤ hi
```

SJSU instance (`Main.lean`), with `sjsuB k φ = tubeCenter sjsuEccModes sjsuEccIbar k φ`:

```lean
def sjsuLambdaStar : Fin 3 → ℝ :=
  ![5.3993226066969503769e-1, 2.1912825008425995084e-1, 4.7474331515411474555e-2]

theorem sjsu_tube_gamma (φ : Fin 2 → ℝ) (I : Fin 3 → ℝ) (hI : ∀ k, |I k - sjsuB k φ| ≤ 2 / 10 ^ 6)
    (j : Fin 3) :
    (sjsuGammaLo j : ℝ) ≤ eccGamma sjsuEccV I φ j ∧ eccGamma sjsuEccV I φ j ≤ sjsuGammaHi j

theorem sjsu_tube_ecc (φ : Fin 2 → ℝ) (I : Fin 3 → ℝ) (hI : ∀ k, |I k - sjsuB k φ| ≤ 2 / 10 ^ 6)
    (j : Fin 3) :
    ![0.026, 0.009, 0.006] j ≤
        Real.sqrt (1 - (1 - eccGamma sjsuEccV I φ j / sjsuLambdaStar j) ^ 2) ∧
      Real.sqrt (1 - (1 - eccGamma sjsuEccV I φ j / sjsuLambdaStar j) ^ 2) ≤
        ![0.062, 0.085, 0.063] j

theorem sjsu_tube_ecc_of_dev (φ : Fin 2 → ℝ) (v : Fin 3 → ℝ) (hv : ∀ k, |v k| ≤ 2 / 10 ^ 6)
    (j : Fin 3) : -- the same with I = fun k => sjsuB k φ + v k
```

The Γ bounds (exact rationals, `sjsuEccData.Glo/Ghi`): `Γ_lo = (713/3906250, 13867/1562500000,
427273/500000000000)` ≈ (1.82528·10⁻⁴, 8.87488·10⁻⁶, 8.54546·10⁻⁷). `Γ_hi = (51937/50000000,
158607/200000000, 117883/1250000000)` ≈ (1.03874·10⁻³, 7.93035·10⁻⁴, 9.43064·10⁻⁵). Each is
`Λ*_j(1 − √(1 − e²))` rounded to 6 digits, inward. The rational conditions of `ecc_bounds_of_gamma` are
`sjsu_ecc_conditions` (`norm_num`).

**For N5.** The statement takes `Γ_j` as a real function of `(I, φ)`. With N2's chart (`polarInv`, angles
`θ`, `phiOf θ = ![θ 0 - θ 2, θ 1 - θ 2]`, `z = V′ w`), `eccGamma_phase` turns
`|Σ_k V′_jk √I_k e^{iθ_k}|²` (absolute angles, written with `cos`/`sin`) into
`eccGamma sjsuEccV I (phiOf θ) j`. `|z_j|² = Γ_j = oscillatorAction` and `w_k = √I_k e^{iθ_k}` are N5's to
connect, together with the identification of `sjsuB` with N5's own centre `B₀` from the same JSON. My modes
are the full 2,790-row `sigma` table in file order, with `B_k = Ī_k + Σ_m (−m_k σ_m) cos(m·φ)` over all
rows, both `±m`, as the JSON `doc` string states.

## Approach

1. **Charts, no π.** Each angle is covered by `± wt t`, `t ∈ [−1, 1]` (`exists_circ`: `t = sin/(1 + cos)`
   for `cos ≥ 0`, else the negated point). At a rational `t_c` the point `P = ±((1 − t²), 2t)/(1 + t²)` is
   an exact rational, and so is the derivative `D`. On `|t − t_c| ≤ h` the chart satisfies
   `w = P + (t − t_c) D + ρ` with `‖ρ‖ ≤ 2h²/(1 + t_c²)`, and `‖w − P‖ ≤ 2h(1 + h)/(1 + t_c²)`. These
   are algebraic identities; no trigonometric enclosure is used.
2. **Quadtree.** Four root boxes `[−1, 1]²` (one per sign pair) are split at midpoints. There are 900
   leaves; the maximum depth is 11 (the t-width at the deepest is 2⁻⁵ on one axis). The splits are guided
   by floats and accepted only by the exact mirror.
3. **The centre at a leaf.** The checker uses a fixed-point copy of σ, `trunc(σ·2⁴⁸)`. 130 modes are
   nonzero, all with `|m_a| ≤ 7`. It evaluates `Σ (−m_k) n Re(P₁^{m₁} P₂^{m₂})` **exactly in Gaussian
   integers**. With `t_c = p/q` in lowest terms, `P = G/N`, `G = ±((q² − p²) + 2pq i)`, `N = q² + p²`, and
   the table holds `G^j N^{7−j}`. One global check covers everything else: `fix = fixOf 48 modes`, the
   rounding sum `Σ|m_k||σ − σ̃| ≤ τ_k` (≈ 10⁻¹²), and the Lipschitz sums `Σ|m_k σ||m_a| ≤ L_{k,a}`, all
   over the exact 2,790 rows. So on a cell, `|B_k(w) − B̃_k(P)| ≤ ε₁L_{k1} + ε₂L_{k2} + τ_k`.
4. **√I.** Leaf certificates `sl_k, sh_k` (numerators over 2⁴⁸) satisfy `sl² ≤ B̃ − η − r` and
   `B̃ + η + r ≤ sh²`, so `√I_k ∈ [sl_k, sh_k]` on the cell.
5. **Γ at a leaf.** Let `z_c = Σ V_jk s_c,k P_k`, `G = |z_c|²`, and let a certificate `Z ≥ |z_c|`. Then
   `δ = z − z_c` has `|Re(z_c conj δ)| ≤ E` and `‖δ‖ ≤ R`. Here
   `E = Σ_k |V| ds_k |Re(z_c conj P_k)| + Σ_a |V| sh_a (h_a |Re(z_c conj D_a)| + Z ρ̄_a)`
   and `R = Σ|V| ds + Σ|V| sh ε`. This gives `|z|² ≤ G + 2E + R²` and `(G − E)² ≤ |z|² G`. The bound is
   exact to first order in the action box (the zonotope support function in the direction `z_c`) and in the
   angles (the exact derivative direction `D`), with quadratic remainders. That is what keeps the grid at
   900 cells; with a plain Lipschitz bound in the angles the same scheme needs 10,540.
6. **Eccentricity.** `e = √(1 − (1 − Γ/Λ)²)` is monotone in `Γ` on `[0, Λ]`, and `ecc_bounds_of_gamma`
   applies the rational conditions.
7. **Kernel shape.** Everything is `ℚ`/`ℤ`. Sums over the 2,790 rows use a balanced pairwise sum
   `treeSum` (see the design signals). Each tree block is one declaration of ≤ 32 leaves, assembled in term
   mode by `checkTree_split_intro`. All big literals are below 2⁶⁴ except the three `Ī`, the nine `V′`
   entries and the dyadic denominators of σ (about 80 distinct powers of 2, global check only). No packed
   literals, so no whitening was needed.

## Checks run (exact commands and output)

All through `.drafts/g2/g2lake`:

Final full rebuild, 16:17–16:20 UTC, after the line-length fixes (it rebuilds every module of mine):

```
g2lake build KAM.EffectiveStability.SJSU.Ecc.Main
✔ Built KAM.EffectiveStability.Tube.Ecc.Circle (3.1s)
✔ Built KAM.EffectiveStability.Tube.Ecc.Defs (1.8s)
✔ Built KAM.EffectiveStability.Tube.Ecc.Gamma (4.0s)
✔ Built KAM.EffectiveStability.SJSU.Ecc.Modes1 (2.8s)
✔ Built KAM.EffectiveStability.SJSU.Ecc.Modes0 (3.1s)
✔ Built KAM.EffectiveStability.Tube.Ecc.Center (1.9s)
✔ Built KAM.EffectiveStability.Tube.Ecc.Sound (2.4s)
✔ Built KAM.EffectiveStability.SJSU.Ecc.Data (43s)
✔ Built KAM.EffectiveStability.SJSU.Ecc.TreePM (38s)
✔ Built KAM.EffectiveStability.SJSU.Ecc.TreeMP (57s)
✔ Built KAM.EffectiveStability.SJSU.Ecc.TreeMM (47s)
✔ Built KAM.EffectiveStability.SJSU.Ecc.TreePP (79s)
✔ Built KAM.EffectiveStability.SJSU.Ecc.Main (1.7s)
Build completed successfully (2190 jobs).
```

There are no warnings in any of my modules.

`#print axioms` (scratch file `.drafts/g2/scratch/N6-Ecc/lean/Axioms.lean`, `g2lake env lean`):

```
'KAM.EffectiveStability.Tube.eccGamma_bounds_of_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.Tube.eccGamma_phase' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.Tube.ecc_bounds_of_gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuEcc_globalOK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuEccTreePP_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsu_tube_gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsu_tube_ecc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsu_tube_ecc_of_dev' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lint: `.drafts/g2/lint_noabi.sh`, run once (16:05–16:15 UTC). **`abi_hashes` was skipped**, per the rule
of 15:25 UTC. It exited 1 for two reasons:
- **Lines over 100 characters.** My files had such lines; all are fixed (generator and hand-written).
  After the fix, `awk 'length > 100'` over all my files prints nothing. The remaining hits are in other
  workers' directories (`Tube/Poly`, `Tube/Check`, …).
- **`KAM.lean is out of date (KAM/Root/EffectiveStability.lean)`.** The roots are generated (rule 10) and
  not mine to regenerate; kam-g2 runs `gen_root_imports.py` at landing. My core modules
  `KAM.EffectiveStability.Tube.Ecc.*` belong in `KAM`. `KAM.EffectiveStability.SJSU.Ecc.*` belongs in the
  opt-in library `KAMSJSU` (a `scripts/build_roots.json` prefix is needed).

All other steps passed: `check_lean_modules: PASS`, the unit tests (29 + 8) `OK`, `FROZEN-ANCHOR GUARD OK`.
I did not rerun the full lint after the line fixes (it takes 10 minutes); the fixes only touched layout.

### Measured kernel cost (the brief's day-1 report)

Measured at 15:45–16:20 UTC: about **4 CPU-min in total**. The module build times are 43 s (`Data`: the
global check, which also elaborates 2,790 rows) and 38 + 47 + 57 + 79 = 221 s for the four trees. Each
includes about 10 s of import replay, so the kernel work is about 0.2 s per leaf. The peak memory per
declaration is ≤ about 3.5 GB including the 2.35 GB import baseline (measured on 16- and 61-leaf blocks),
inside the 6 GB scope.

### Certified ranges (exact mirror, `margins.py`)

| Planet | worst-leaf Γ range | e range implied | statement |
|---|---|---|---|
| Jupiter | [1.82558·10⁻⁴, 1.03747·10⁻³] | [0.02600, 0.06196] | [0.026, 0.062] |
| Saturn | [8.88473·10⁻⁶, 7.92701·10⁻⁴] | [0.00900, 0.08498] | [0.009, 0.085] |
| Uranus | [8.70396·10⁻⁷, 9.42989·10⁻⁵] | [0.00606, 0.06300] | [0.006, 0.063] |

The worst leaves sit just inside the targets because refinement stops as soon as a cell passes. This is not
a fragility: every check is exact rational arithmetic. The true ranges are phase 1's (see the brief).

## Design signals hit

- **Kernel recursion depth.** `List.sum` (a `foldr`) over the 2,790 rows fails in `decide +kernel`, which
  reports a misleading "failed to reduce … stuck at match"; 1,395 rows pass. Fixed by `treeSum`, a balanced
  pairwise sum with logarithmic depth, proved equal to `List.sum`. No options were set.
- **Memory per declaration.** With `ℚ` arithmetic in the mode loop, a 154-leaf declaration was OOM-killed
  at the 6 GB scope after 52 CPU-s: about 200 MB per leaf, from Rat normalization terms. Fixed by moving the
  loop to Gaussian integers, which made it 3× faster and much smaller, and by blocks of ≤ 32 leaves.
- **Elaboration.** A computable 1,395-row list literal hits `maximum recursion depth` in the code
  generator. The data defs are therefore `noncomputable`, as in `gen_t2conf.py`; kernel reduction is
  unaffected.

## Uncertainties

- The SJSU data defs (`sjsuEccModes`, `sjsuEccIbar`, `sjsuEccV`) are mine, generated from the same JSON as
  N5/N7's. If N7 freezes its own data definitions, N5 must prove them equal to mine (a `decide +kernel` list
  equality, or a regeneration of my modules against N7's names). The generator is a one-line switch.
- `Λ*` is entered as the dataset's decimal strings, the same literals as the T2-CONF draft v2.
- The covering of the angle torus uses `φ ∈ ℝ²` directly (`Complex.exp (φ a * I)`), so no periodicity
  assumption is needed.

## Deviations from the brief

- **Cell scheme.** The cell scheme differs from the brief's sketch: an adaptive quadtree in the rational
  chart parameters (900 cells) instead of a uniform grid of about 300² cells with Hessian bounds. The
  second-order effect comes from linearizing exactly along the chart derivative plus a quadratic remainder,
  which needs no Hessian of `B`. `B` enters to first order only (Lipschitz); its contribution is about 16×
  smaller than the angular one.
- **Fixed-point modes.** Per-cell evaluation uses 130 fixed-point modes (`trunc(σ 2⁴⁸)`), not all 2,790.
  The exact statement-level `B` over all 2,790 rows is recovered through the global rounding check.
- **Generated certificates.** The generated certificate files are under `KAM/EffectiveStability/SJSU/Ecc/`
  (my directory). The generator stays in `.drafts/g2/scratch/N6-Ecc/`; kam-g2 may want to move it to
  `scripts/sjsu/rigor/`.
- **Phase lemma.** I added `eccGamma_phase` (common-phase invariance, for N5).

No suspected errata in pinned sources.
