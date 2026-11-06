# N3-Trig handoff: C¹ trigonometric models, tube models and packed products (T2-CONF)

Worker g2-n3, 6 November 2026, branch `inp-sjsu-g2` (shared worktree; nothing committed by me).
Status: **all five deliverables done**; every module builds at default heartbeats, with no
`sorry`/`axiom`/`set_option`. Kernel test: one real-size product costs **≈ 0.13 s per declaration**
(target ≤ 0.2 s); decoding to slot lists is far more expensive (see the kernel test section).

## Files (owned directories only)

| Module | Lines | Content |
|---|---:|---|
| `KAM/EffectiveStability/Tube/Algebra/C1.lean` | 259 | (1) `C1Close` algebra, product rule |
| `KAM/EffectiveStability/Tube/Algebra/Bounds.lean` | 93 | scalar product / Leibniz error bounds |
| `KAM/EffectiveStability/Tube/Trig/Poly.lean` | 396 | (2) evaluation, derivatives, bounds, dense square layout |
| `KAM/EffectiveStability/Tube/Trig/Product.lean` | 262 | (3) exact product = `listConv` (Kronecker), symmetry |
| `KAM/EffectiveStability/Tube/Trig/Trunc.lean` | 296 | (3) truncation (hexagon), rounding, `C1Close` outputs |
| `KAM/EffectiveStability/Tube/Trig/Model.lean` | 137 | scaled models `TP` (one binary scale per polynomial) |
| `KAM/EffectiveStability/Tube/Trig/TubeClose.lean` | 239 | (4) tube closeness predicate and its algebra |
| `KAM/EffectiveStability/Tube/Trig/Tube.lean` | 309 | (4) tube models, products, degree profiles |
| `KAM/EffectiveStability/Tube/Trig/Packed.lean` | 218 | (5) packing, decode lemma, packed product of models |
| `KAM/EffectiveStability/Tube/Trig/Literal.lean` | 216 | (5) whitened literals (packed naturals; core `zdecsX` copy) |

Total 2,425 lines, every file ≤ 1,500. Scratch (not for landing): `.drafts/g2/scratch/n3/`
(`gen_kshard.py`, `run_kshard.sh`, `kshard/` test files and outputs, `Ax.lean`).

All in namespace `KAM.EffectiveStability.Tube`. New modules are not in the generated roots; build by
name.

## Main statements

### (1) `Algebra/C1.lean`
`pderiv f φ a := fderiv ℝ f φ (Pi.single a 1)` (abbrev, syntactically the derivative inside `C1Close`).
- `C1Close.refl (hg : Differentiable ℝ g) : C1Close g g 0 0`; `C1Close.zero`; `mono`; `symm`;
  `trans : C1Close f g e₀ e₁ → C1Close g h d₀ d₁ → C1Close f h (e₀+d₀) (e₁+d₁)`.
- `add`, `sub` (errors add), `neg`, `const_mul H c : C1Close (c * f ·) (c * p ·) (|c| e₀) (|c| e₁)`,
  `sum` over a `Finset`.
- **Product rule** `C1Close.mul (H : C1Close f p e₀ e₁) (K : C1Close g q d₀ d₁)
  (hP₀ : ∀ φ, |p φ| ≤ P₀) (hP₁ : ∀ φ a, |pderiv p φ a| ≤ P₁) (hQ₀ : ∀ φ, |q φ| ≤ Q₀)
  (hQ₁ : ∀ φ a, |pderiv q φ a| ≤ Q₁) :
  C1Close (f * g) (p * q) (P₀ d₀ + Q₀ e₀ + e₀ d₀) (P₁ d₀ + P₀ d₁ + Q₁ e₀ + Q₀ e₁ + e₁ d₀ + e₀ d₁)`
  (the brief's `…` is empty: these six terms are the whole bound).
- `abs_le : |f φ| ≤ P₀ + e₀`, `abs_pderiv_le : |pderiv f φ a| ≤ P₁ + e₁`,
  `le_of_le : (∀ φ, c ≤ p φ) → c - e₀ ≤ f φ`; `pderiv_add/sub/neg/const_mul/mul`.

### (2) `Trig/Poly.lean`
- `trig p x` = `cos x` (even, `p = false`) or `-sin x` (odd); `kdot k φ = k₁ φ₀ + k₂ φ₁`.
- `evalK (κ : ℕ → ℤ × ℤ) (p : Bool) (d : List ℤ) φ = Σ_{i < |d|} d_i · trig p (κ i · φ)`:
  integer mantissas read through a key map. **The square layout** `Layout.key C S i =
  (i % S − C, i / S − C)`, `Layout.len C S = 2CS + 2C + 1`, padding columns `i % S > 2C` zero
  (`colsOk C S d`, decidable).
- `pderiv_evalK : pderiv (evalK κ p d) φ a = evalK κ (!p) (dlist κ a p d) φ` — a parity flip; slot
  `i` multiplied by `psgn p · (κ i)_a` (`psgn false = 1`, `psgn true = -1`).
- `abs_evalK_le : |evalK κ p d φ| ≤ l1 d` (`= Σ|d_i|`);
  `abs_pderiv_evalK_le : |pderiv (evalK κ p d) φ a| ≤ wl1 κ a d` (`= Σ |(κ i)_a| |d_i|`).
- `lowB_le_evalK : lowB κ d ≤ evalK κ false d φ`, `lowB = Σ_{κ i = 0} d_i − Σ_{κ i ≠ 0} |d_i|`.
- `c1Close_evalK : (∀ a, wl1 κ a (lsub c d) ≤ e₁) → C1Close (evalK κ p c) (evalK κ p d) (l1 (lsub c d)) e₁`
  (`lsub` = slotwise difference, zero-padded).
- All computable functions (`l1`, `wl1`, `lowB`, `dlist`, `colsOk`, `lsub`) are kernel-linear (no
  `Array`): maps by `mapIx`, checks by `&&`-chains, and sums by balanced pairwise reduction
  (`sumIx = treeSum 64 ∘ mapIx`, evaluation depth `O(log n)`; `sumIx_eq` gives the `Finset` form).

### (3) `Trig/Product.lean`, `Trig/Trunc.lean`, `Trig/Model.lean`
- `evalK_eq_re : evalK κ p d φ = Re (ω_p Σ_i d_i e^{i κ i·φ})`, `ω_false = 1`, `ω_true = i`.
- `symOk q d := d.reverse == (if q then d.map (-·) else d)`; on the square layout reversal is
  `k ↦ −k` (`Layout.key_reflect`), so this is exactly the phase-1 symmetry/antisymmetry.
- `ek_mul` (Kronecker): `ek (key Ca S) a φ * ek (key Cb S) b φ = ek (key (Ca+Cb) S) (listConv a b) φ`
  under `2(Ca+Cb) < S`, `colsOk Ca S a`, `colsOk Cb S b`.
- **Product identity** `evalK_mul (hS : 2 * (Ca + Cb) < S) (ha : colsOk Ca S a = true)
  (hb : colsOk Cb S b = true) (hbl : b.length = Layout.len Cb S) (hbs : symOk q b = true) φ :
  evalK (Layout.key Ca S) p a φ * evalK (Layout.key Cb S) q b φ =
    psgn (p && q) * evalK (Layout.key (Ca + Cb) S) (xor p q) (listConv a b) φ`
  (only ONE factor needs symmetry; `evalK_mul'` with the symmetric factor first).
- Truncation: all layouts of a computation share the stride `S`; the box `C' ≤ C` is the slice from
  slot `Layout.shift C C' S = (C−C')(S+1)` (`Layout.key_shift`, needs `C + C' < S`).
  `evalK_embed`; **general comparison** `c1Close_sub : C1Close (evalK (key C S) p c)
  (fun φ => m * evalK (key C' S) p t φ) (l1 (lsub c (embed C C' S (t.map (m * ·))))) e₁`.
- `truncRound C C' S s keep c` (one linear pass: slice, mask `keep`, sign-symmetric
  round-to-nearest `rndS s` by `s` bits) and `c1Close_truncRound` (errors = the computed `l1`/`wl1`
  of the slotwise difference). `keepHex K k := hexN k ≤ K`, `hexN k = |k₁|+|k₂|+|k₁+k₂|`.
- A-priori: `abs_sub_rndS_le` (half an ulp), `truncRound_err_le` (slot `i`: `ulpHalf s` if kept,
  `|c_i|` if dropped), summed in `l1_truncRound_le`, weighted in `wl1_truncRound_le`.
- `TP` (`C`, `par`, `e : ℤ`, `d`), `TP.eval S x φ = 2^(-e) evalK (key C S) par d φ`; `TP.ok`;
  `TP.eval_mul` (scales add); `TP.abs_eval_le`, `TP.pderiv_eval`/`TP.deriv`,
  `TP.abs_pderiv_eval_le`, `TP.lowB_le_eval`; `TP.trunc` and
  `TP.c1Close_trunc : C1Close (x.eval S) ((trunc S C' s keep x).eval S) (2^(-e) l1 (truncErr …)) (2^(-e) e₁)`.

### (4) `Trig/TubeClose.lean`, `Trig/Tube.lean`
- `InBox r u := ∀ j, |u j| ≤ r`; `upd F u φ j := fderiv ℝ (fun v => F v φ) u (Pi.single j 1)`.
- `structure TubeClose F G r e₀ e₁ e₂`: on the box, slice differentiability (`φ`-slices everywhere,
  `u`-slices at `u`), `|F − G| ≤ e₀`, both `φ`-partials within `e₁`, all three `u`-partials within `e₂`.
- Algebra: `refl`, `mono`, `symm`, `trans`, `add`, `sub`, `neg`, `const_mul`, `sum`, `zero`,
  `of_c1Close` (`u`-independent, `e₂ = 0`), and **`TubeClose.mul`** with sup bounds `P₀,P₁,P₂`
  (value, `φ`-, `u`-partials of `G`) and `Q₀,Q₁,Q₂`: errors `P₀d₀+Q₀e₀+e₀d₀`, and
  `P_k d₀ + P₀ d_k + Q_k e₀ + Q₀ e_k + e_k d₀ + e₀ d_k` for `k = 1, 2`.
- Models `tmEval s μ g u φ = Σ_{i∈s} u^{μ i} g_i(φ)` (`umon m u = Π u_j^{m_j}`, `mdeg m = Σ m_j`);
  `abs_umon_le : |u^m| ≤ r^{|m|}`; `fderiv_umon : ∂_{u_j} u^m = m_j u^{m − e_j}`;
  `pderiv_tmEval` (∂_φ on coefficients), `upd_tmEval` (∂_{u_j} as `m_j u^{m−e_j} g`);
  `abs_tmEval_le : |tmEval| ≤ Σ G_i r^{|μ i|}` and the derivative versions;
  `tubeClose_tmEval_zero`: a model is `TubeClose`-close to `0` with errors
  `Σ G_i r^{|μ i|}`, `Σ G'_i r^{|μ i|}`, `Σ |μ i| G_i r^{|μ i|−1}` (every dropped part).
- `tmEval_mul` (product = model over pairs, monomials added), `tmEval_split` (by a predicate, e.g.
  `mdeg (m+n) ≤ L`), `tmEval_regroup` (coefficient of `u^p` = sum over `μ i = p`),
  `sum_pairs_deg_eq` (any degree weight `w d e` regrouped by **degree profiles**
  `A_d = Σ_{|m|=d} G_m`, `B_e = Σ_{|n|=e} H_n`), and `abs_dropped_le`: the part of degree `> L` of a
  product is at most `Σ_{d,e} A_d B_e [L < d+e] r^{d+e}` on the box.

### (5) `Trig/Packed.lean`, `Trig/Literal.lean`
- Packing = the landed signed `packSum w d`; decoding = the landed `unpackSlots w N Z` (offset
  digits, balanced mask-and-shift). Models are **defined by decoding** literal integers.
- `packOk w N Z` (decidable: `0 ≤ Z + slotOff w N < 2^{wN}`); `packSum_unpackSlots :
  packOk w N Z = true → packSum w (unpackSlots w N Z) = Z`; `length_unpackSlots`.
- **Decode lemma** `unpackSlots_mul (hw : 0 < w) (hNa : 0 < Na) (hNb : 0 < Nb) (ha : packOk w Na Za)
  (hb : packOk w Nb Zb) (hfit : SlotsBounded w (listConv (unpackSlots w Na Za) (unpackSlots w Nb Zb))) :
  unpackSlots w (Na + Nb − 1) (Za * Zb) = listConv (unpackSlots w Na Za) (unpackSlots w Nb Zb)`.
  No-overflow conditions: landed `convFits` (length-based), `convFits_of_le` (slot bounds
  `2·min(N_a,N_b)·B_a·B_b < 2^w`), and the sharper **`convFitsL1 w M_b a b := 2·l1 a·M_b < 2^w ∧ ∀ c ∈ b, |c| ≤ M_b`**
  (`slotsBounded_listConv_of_l1`; the dense-layout lengths make `convFits` too crude at w = 173).
- **End to end** `evalK_unpackSlots_mul`: for `Za` on layout `Ca`, `Zb` on `Cb` (symmetric of
  parity `q`), `evalK (key Ca S) p (unpack Za) φ * evalK (key Cb S) q (unpack Zb) φ =
  psgn (p && q) * evalK (key (Ca+Cb) S) (xor p q) (unpackSlots w (Layout.len (Ca+Cb) S) (Za * Zb)) φ`.
- `zOf neg n` (signed literal = sign bit + natural magnitude): one `Nat.mul` per product.
- Whitening of packed naturals: `wkey s b n = natRamp b n * wmul s` (chunk `i` keyed by
  `(i+1)·wmul s`, `wmul s` an odd 64-bit multiplier of the salt; closed form, no loop),
  `whiten`/`unwhiten` (one XOR), `unwhiten_whiten`. Use one salt per literal.
- Core copy of `ZCodeX` (`zvar`, `unzig`, `zdec`, `zdecs`, `zkey`, `zvarX`, `zdecX`, `zdecsXAux`,
  `zdecsX`) with a **decode lemma** `zdecsX_zwhitenRows : (∀ c ∈ cs, zdecC c.1 c.2.2 ≤ c.2.1) →
  zdecsX s (zwhitenRows s 0 cs) = zdecs (cs.map fun c => (c.1, c.2.2))` (whitened rows decode to
  what the plain rows decode to, when the whitened byte count covers the bytes read); test theorems
  `zdecs_test`, `zdecsX_test` (`decide +kernel`).
- Literal form: generator `.drafts/g2/scratch/n3/gen_kshard.py` (explicit `Nat.add`/`Nat.shiftLeft`
  trees of 288-bit chunks, sub-definitions of ≤ 256 chunks; SR-6's `tree`/`wrap`).

## Approach

Real cos/sin semantics on dense integer slot lists; the product proved through complex exponentials
(`ω_p`) plus a direct dense Kronecker lemma (`sum_range_cauchy_weighted`, `listConv` reused from
`KAM/Certificate/Poly`), with symmetry required of one factor only and checked by list reversal.
One stride for all layouts of a computation makes truncation a contiguous slice, so every
computable function is a linear pass and every error is either computed exactly (`lsub`, `l1`, `wl1`)
or bounded a priori. Packing/decoding reuse V2-PACKED (`packSum`, `unpackSlots`, `natPack_digits`,
`natDigitsSh_natPack`, `packSum_listConv`, `natRamp`, `natUnmask`, `roundSlot`/`round_err`).

## Checks

- Targeted builds (`.drafts/g2/g2lake build <M>`), all ✔: `KAM.EffectiveStability.Tube.Algebra.C1`,
  `.Algebra.Bounds` (via TubeClose), `.Trig.Poly`, `.Trig.Product`, `.Trig.Trunc`, `.Trig.Model`,
  `.Trig.TubeClose`, `.Trig.Tube`, `.Trig.Packed`, `.Trig.Literal`.
- `#print axioms` (`.drafts/g2/scratch/n3/Ax.lean`): `C1Close.mul/trans/sum`, `pderiv_evalK`,
  `abs_evalK_le`, `abs_pderiv_evalK_le`, `lowB_le_evalK`, `c1Close_evalK`, `evalK_mul`, `ek_mul`,
  `c1Close_sub`, `c1Close_truncRound`, `truncRound_err_le`, `TP.eval_mul`, `TP.c1Close_trunc`,
  `packSum_unpackSlots`, `unpackSlots_mul`, `evalK_unpackSlots_mul`, `zdecsX_zwhitenRows`,
  `TubeClose.mul`, `tubeClose_tmEval_zero`, `upd_tmEval`, `abs_dropped_le`, `tmEval_regroup`:
  `[propext, Classical.choice, Quot.sound]`; `unwhiten_whiten`: `[propext, Quot.sound]`.
- `scripts/lint_sources.sh`: the full script timed out at 10 min in its frozen-anchor step (several
  workers' lints overlapping; that step and the ABI step do not touch my files). Its lines 1–157 (forbidden
  patterns, escapes, `EuclideanSpace`, line length ≤ 100, file size ≤ 1500, roots, `check_lean_modules`)
  ran as `.drafts/g2/scratch/n3/lint_part.sh`: `check_lean_modules: PASS (18376 Lean files)`; no
  pattern or size finding in my files; my nine overlong lines were fixed (re-checked: none left);
  `KAM.lean is out of date` (expected: the new modules are not in the generated roots, kam-g2's step).
  Overlong lines remain in other workers' files (`Tube/Check`, `Tube/Ecc`, `Tube/Poly`).

## Kernel test (deliverable 5)

Generator `.drafts/g2/scratch/n3/gen_kshard.py` (real phase-1 data, as SR-6): A = ∂_{φ₁} of the u_U
slot of F_U (odd, 1,900 modes, layout C = 25), B = √B₀,U (even, 2,791 modes, C = 30), p = 80, w = 173,
S = 121; product layout C = 55 (13,421 slots). Operands 1.05 and 1.26 Mbit, product 2.31 Mbit; literals
whitened (`unwhiten s 288 n lit`, salts 1, 2, 3) and written as `Nat.add`/`Nat.shiftLeft` trees.
Whitening: distinct low 64-bit limbs of the chunks 3,649/3,649 (A), 4,380/4,380 (B), 8,028/8,028 (C)
against 612, 771 and 4,213 raw. Runner `run_kshard.sh`; each file run through `g2lake env lean`.
**CPU time (user + sys)**; the base file (imports + data, no theorem) costs 12.1–12.5 s and 3.3 GB:

| File | Checks (all `decide +kernel`) | CPU s | Over base | Peak RSS |
|---|---|---:|---:|---:|
| `K_prod40` | 40 × `ZA * ZB = ZC` | 17.7 | 5.2 s, **0.13 s per declaration** | 4.27 GB |
| `K_packok` | `packOk` of A and B | 12.9 | 0.7 s | 3.32 GB |
| `K_dec` | `l1 (unpackSlots 173 13421 (ZA * ZB)) = …` | 24.2 | 12 s | 4.74 GB |
| `K_sym` | `symOk` of decoded A and B | 19.4 | 7 s | 3.90 GB |
| `K_cols` | `colsOk` of decoded A and B | 18.2 | 6 s | 3.86 GB |
| `K_fit` | `convFitsL1 173 M_b` of decoded A, B | 20.9 | 9 s | 4.41 GB |

(Earlier wall-clock figures were inflated by waits on the shared build lock. `prod40` matches
SR-6's 0.09–0.15 s.)

**Reading for N5.**
- The packed product with whitened literals meets the target.
- **Decoding to slot lists costs about 0.5–1 ms per slot** (6k–13k slots: 6–12 s per check). At 36k
  products, per-product decoding would cost tens of CPU-hours. The checker should keep its
  per-product work GMP-resident: masks, `gmpRound`, packed norms (V2-PACKED's `loadOk`, `packNorm`).
  It should decode only where a list is unavoidable (symmetry, column checks on inputs, once per
  literal).
- **Design signal (fixed):** the first `K_dec`/`K_fit` runs failed with `(kernel) deep recursion
  detected` because `l1` (a linear non-tail sum) and the landed `maxAbs` (`foldr`) nest once per slot.
  The sums are now balanced pairwise reductions (`pairSum`/`treeSum`, depth `O(log n)`), and
  `convFitsL1` takes an explicit slot bound checked by `List.all`. No recursion option was used.

## Design signals

- None at default heartbeats.
- **Kernel deep recursion** on linear sums over 10⁴-slot lists: fixed by balanced sums (see above).
  The landed `maxAbs`/`convFits` (`KAM/Certificate/Poly/Packed.lean`) have the same hazard at this size.
- **Timing hazard (not a heartbeat signal):** `g2lake` wall times include the wait on the shared
  build lock; my first per-declaration estimates (≈ 2 s) were lock waits. Measure with CPU time.

## Uncertainties

- Symmetry is a hypothesis on one factor (`symOk`), checked on decoded lists; I did not prove that
  `listConv` or `truncRound` preserve it (true mathematically; `rndS` is sign-symmetric and the
  hexagon is `−k`-invariant, so a recheck with `symOk` passes on exact data). N5 should recheck or ask.
- The tube layer's coefficients are abstract differentiable functions with sup bounds; the bridge to
  `TP` is `TP.abs_eval_le`/`TP.abs_pderiv_eval_le` (no dedicated lemma).
- The dropped-degree bound is stated at value level in profile form (`abs_dropped_le`); its
  derivative versions follow from `tubeClose_tmEval_zero` with pair sup bounds and
  `sum_pairs_deg_eq` (any weight `w d e`), not packaged as one theorem.
- `TubeClose` asks slice differentiability only (not joint `C¹`); if N5's chain rule needs joint
  differentiability it must come from the true functions.

## Deviations from the brief

- Signed packing by one signed integer (`packSum`, offset decode) instead of a ± split with 4
  `Nat.mul` (the brief allows either); literals carry a sign bit (`zOf`).
- The whitening of packed naturals uses the salted ramp key (closed form) rather than `zkey`'s
  byte stream; the `zdecsX` byte scheme is copied too, with its decode lemma, for list literals.
- Added `convFitsL1` (sharper no-overflow condition) and `TP` (scaled models).

## Suspected errata

None in pinned sources.
