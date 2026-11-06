/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Ecc.Circle

/-!
# The eccentricity enclosure on the tube: definitions and the checker (T2-CONF, N6)

**The quantity.** The tube is `I_k = B_k(φ) + v_k`, `|v_k| ≤ r`, with the centre
`B_k(φ) = Ī_k + Σ_m (-m_k σ_m) cos(m₁ φ₀ + m₂ φ₁)` over a list of modes `(m₁, m₂, σ_m)`,
`m_3 = -m₁ - m₂` (`tubeCenter`). For the rational matrix `V` and `q = (φ₀, φ₁, 0)`,
`Γ_j = |Σ_k V_jk √I_k e^{i q_k}|²` (`eccGamma`, written with `cos` and `sin`).

**The checker.** Both angles are covered by the rational charts `± wt t`, `|t| ≤ 1`
(`KAM.EffectiveStability.Tube.exists_circ`). A certificate is a binary tree (`ETree`) of midpoint
splits of the chart boxes (`EBox`). At a leaf, `leafOK`:
* evaluates the centre `B_k` exactly at the rational cell centre, with the fixed-point coefficients
  `fix`, in Gaussian-integer arithmetic (`bSumZ`); the global check `globalOK` ties `fix` to
  `modes` and bounds the rounding error
  (`errSum ≤ tau`) and the Lipschitz sums (`lipSum₁ ≤ L₁`, `lipSum₂ ≤ L₂`);
* checks certified bounds `sl_k ≤ √I_k ≤ sh_k` on the cell (`sqrtOK`);
* checks `Glo_j ≤ Γ_j ≤ Ghi_j` by a linearization about the cell centre that is exact in the action
  box and in the angles to first order, with a quadratic chart remainder (`zOK`).

Soundness: `KAM.EffectiveStability.Tube.eccGamma_bounds_of_check`
(`KAM/EffectiveStability/Tube/Ecc/Sound.lean`).
-/

@[expose] public section

open Complex

namespace KAM.EffectiveStability.Tube

/-! ### The quantity -/

/-- The component `k` of the charge-balanced mode `(m₁, m₂, -m₁ - m₂)`. -/
def modeK (m₁ m₂ : ℤ) (k : Fin 3) : ℤ := ![m₁, m₂, -m₁ - m₂] k

/-- The tube centre `B_k(φ) = Ī_k + Σ_m (-m_k σ_m) cos(m₁ φ₀ + m₂ φ₁)`. -/
noncomputable def tubeCenter (modes : List (ℤ × ℤ × ℚ)) (Ibar : Fin 3 → ℚ) (k : Fin 3)
    (φ : Fin 2 → ℝ) : ℝ :=
  (Ibar k : ℝ) + (modes.map fun x =>
    -((modeK x.1 x.2.1 k : ℤ) : ℝ) * (x.2.2 : ℝ) * Real.cos (x.1 * φ 0 + x.2.1 * φ 1)).sum

/-- `Γ_j(I, φ) = |Σ_k V_jk √I_k e^{i q_k}|²` with `q = (φ₀, φ₁, 0)`, in real form. -/
noncomputable def eccGamma (V : Fin 3 → Fin 3 → ℚ) (I : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (j : Fin 3) :
    ℝ :=
  (∑ k, (V j k : ℝ) * Real.sqrt (I k) * Real.cos (![φ 0, φ 1, 0] k)) ^ 2 +
    (∑ k, (V j k : ℝ) * Real.sqrt (I k) * Real.sin (![φ 0, φ 1, 0] k)) ^ 2

/-- The tube centre as a function of the circle points `w₁ = e^{iφ₀}`, `w₂ = e^{iφ₁}`. -/
noncomputable def tubeCenterW (modes : List (ℤ × ℤ × ℚ)) (Ibar : Fin 3 → ℚ) (k : Fin 3)
    (w₁ w₂ : ℂ) : ℝ :=
  (Ibar k : ℝ) + (modes.map fun x =>
    -((modeK x.1 x.2.1 k : ℤ) : ℝ) * (x.2.2 : ℝ) * (w₁ ^ x.1 * w₂ ^ x.2.1).re).sum

/-- `z_j = Σ_k V_jk s_k w_k` with `w₃ = 1`. -/
noncomputable def zW (V : Fin 3 → Fin 3 → ℚ) (s : Fin 3 → ℝ) (w₁ w₂ : ℂ) (j : Fin 3) : ℂ :=
  ((V j 0 : ℝ) : ℂ) * (s 0 : ℂ) * w₁ + ((V j 1 : ℝ) : ℂ) * (s 1 : ℂ) * w₂ +
    ((V j 2 : ℝ) : ℂ) * (s 2 : ℂ)

/-! ### Checker data -/

/-- The data of an eccentricity enclosure. -/
structure EccData where
  /-- The exact modes `(m₁, m₂, σ)` of the centre. -/
  modes : List (ℤ × ℤ × ℚ)
  /-- Fixed-point modes `(m₁, m₂, n)`, `σ̃ = n / 2^K`; `globalOK` checks `fix = fixOf K modes`. -/
  fix : List (ℤ × ℤ × ℤ)
  /-- The fixed-point scale. -/
  K : ℕ
  /-- The constant part `Ī` of the centre. -/
  Ibar : Fin 3 → ℚ
  /-- The rotation `V` (`z = V w`). -/
  V : Fin 3 → Fin 3 → ℚ
  /-- The tube radius. -/
  r : ℚ
  /-- Bounds on `Σ_m |m_k σ_m| |m₁|`. -/
  L₁ : Fin 3 → ℚ
  /-- Bounds on `Σ_m |m_k σ_m| |m₂|`. -/
  L₂ : Fin 3 → ℚ
  /-- Bounds on the rounding errors `Σ_m |m_k| |σ_m - σ̃_m|`. -/
  tau : Fin 3 → ℚ
  /-- The lower bounds of `Γ_j`. -/
  Glo : Fin 3 → ℚ
  /-- The upper bounds of `Γ_j`. -/
  Ghi : Fin 3 → ℚ
  /-- The scale of the leaf certificates (`n / 2^PS`). -/
  PS : ℕ
  /-- The length of the power tables. -/
  M : ℕ

/-- `2^K` as a rational, computed in `ℕ` (the kernel multiplies `ℕ` literals natively). -/
def pow2 (K : ℕ) : ℚ := ((2 ^ K : ℕ) : ℚ)

/-- A dyadic mode row `(m₁, m₂, n / 2^e)`. -/
def dyMode (m₁ m₂ n : ℤ) (e : ℕ) : ℤ × ℤ × ℚ := (m₁, m₂, (n : ℚ) / pow2 e)

/-- Truncation toward zero. -/
def truncQ (x : ℚ) : ℤ := if 0 ≤ x then x.floor else -((-x).floor)

/-- The fixed-point coefficient `σ̃ = trunc(σ 2^K) / 2^K`. -/
def fixVal (K : ℕ) (σ : ℚ) : ℚ := (truncQ (σ * pow2 K) : ℚ) / pow2 K

/-- The nonzero fixed-point modes. -/
def fixOf (K : ℕ) (modes : List (ℤ × ℤ × ℚ)) : List (ℤ × ℤ × ℤ) :=
  modes.filterMap fun x =>
    if truncQ (x.2.2 * pow2 K) = 0 then none else some (x.1, x.2.1, truncQ (x.2.2 * pow2 K))

/-- One pairing pass `[a, b, c, d, …] ↦ [a + b, c + d, …]`. -/
def pairSumQ : List ℚ → List ℚ
  | a :: b :: l => (a + b) :: pairSumQ l
  | l => l

/-- A balanced sum: pairing passes (`n` of them at most), so that the kernel's evaluation depth is
logarithmic in the length; equal to `List.sum` (`treeSumQ_eq`). -/
def treeSumQ : ℕ → List ℚ → ℚ
  | 0, l => l.sum
  | _ + 1, [] => 0
  | _ + 1, [a] => a
  | n + 1, l@(_ :: _ :: _) => treeSumQ n (pairSumQ l)

/-- The rounding error `Σ_m |m_k| |σ_m - σ̃_m|`. -/
def errSum (K : ℕ) (modes : List (ℤ × ℤ × ℚ)) (k : Fin 3) : ℚ :=
  treeSumQ 64 (modes.map fun x => |(modeK x.1 x.2.1 k : ℚ)| * |x.2.2 - fixVal K x.2.2|)

/-- The Lipschitz sum `Σ_m |m_k σ_m| |m₁|`. -/
def lipSum₁ (modes : List (ℤ × ℤ × ℚ)) (k : Fin 3) : ℚ :=
  treeSumQ 64 (modes.map fun x => |(modeK x.1 x.2.1 k : ℚ)| * |x.2.2| * |(x.1 : ℚ)|)

/-- The Lipschitz sum `Σ_m |m_k σ_m| |m₂|`. -/
def lipSum₂ (modes : List (ℤ × ℤ × ℚ)) (k : Fin 3) : ℚ :=
  treeSumQ 64 (modes.map fun x => |(modeK x.1 x.2.1 k : ℚ)| * |x.2.2| * |(x.2.1 : ℚ)|)

/-- The checks on one component `k` of the global data. -/
def globalOKk (d : EccData) (k : Fin 3) : Bool :=
  decide (lipSum₁ d.modes k ≤ d.L₁ k) && decide (lipSum₂ d.modes k ≤ d.L₂ k) &&
    decide (errSum d.K d.modes k ≤ d.tau k)

/-- The global checks, run once. -/
def globalOK (d : EccData) : Bool :=
  decide (d.fix = fixOf d.K d.modes) &&
    d.fix.all (fun x => decide (x.1.natAbs ≤ d.M) && decide (x.2.1.natAbs ≤ d.M)) &&
    globalOKk d 0 && globalOKk d 1 && globalOKk d 2

/-! ### The leaf check -/

/-- The fixed-point centre sum `Σ_fix (-m_k) n Re(T₁[m₁] T₂[m₂])` over power tables `T_a` of
`G_a/N_a` scaled by `N_a^M`; it is `N₁^M N₂^M Σ_fix (-m_k) n Re(P₁^{m₁} P₂^{m₂})` (to be divided by
`2^K N₁^M N₂^M`). -/
def bSumZ (fix : List (ℤ × ℤ × ℤ)) (T₁ T₂ : List GZ) (k : Fin 3) : ℤ :=
  (fix.map fun x => -modeK x.1 x.2.1 k * x.2.2 * GZ.reMul (GZ.zpowT T₁ x.1) (GZ.zpowT T₂ x.2.1)).sum

/-- The square-root bounds on a cell: with `η = ε₁ L₁ + ε₂ L₂ + τ`, `sl² ≤ B_c - η - r` and
`B_c + η + r ≤ sh²`. -/
def sqrtOK (d : EccData) (k : Fin 3) (Bc ε₁ ε₂ sl sh : ℚ) : Bool :=
  decide (0 ≤ sl) && decide (sl * sl ≤ Bc - (ε₁ * d.L₁ k + ε₂ * d.L₂ k + d.tau k) - d.r) &&
    decide (0 ≤ sh) && decide (Bc + (ε₁ * d.L₁ k + ε₂ * d.L₂ k + d.tau k) + d.r ≤ sh * sh)

/-- The centre value `z_c = Σ_k V_jk s_c,k P_k` (`P₃ = 1`). -/
def zCen (V : Fin 3 → Fin 3 → ℚ) (j : Fin 3) (P₁ P₂ : GQ) (sc : Fin 3 → ℚ) : GQ :=
  ⟨V j 0 * sc 0 * P₁.re + V j 1 * sc 1 * P₂.re + V j 2 * sc 2,
    V j 0 * sc 0 * P₁.im + V j 1 * sc 1 * P₂.im⟩

/-- The first-order term `E` of the linearization. -/
def zErr (V : Fin 3 → Fin 3 → ℚ) (j : Fin 3) (zc P₁ P₂ D₁ D₂ : GQ) (h₁ h₂ ρ₁ ρ₂ : ℚ)
    (sh ds : Fin 3 → ℚ) (Z : ℚ) : ℚ :=
  |V j 0| * ds 0 * |zc.reDot P₁| + |V j 1| * ds 1 * |zc.reDot P₂| + |V j 2| * ds 2 * |zc.re| +
    |V j 0| * sh 0 * (h₁ * |zc.reDot D₁| + Z * ρ₁) + |V j 1| * sh 1 * (h₂ * |zc.reDot D₂| + Z * ρ₂)

/-- The radius `R` of the deviation from the centre value. -/
def zRad (V : Fin 3 → Fin 3 → ℚ) (j : Fin 3) (ε₁ ε₂ : ℚ) (sh ds : Fin 3 → ℚ) : ℚ :=
  |V j 0| * ds 0 + |V j 1| * ds 1 + |V j 2| * ds 2 + |V j 0| * sh 0 * ε₁ + |V j 1| * sh 1 * ε₂

/-- The `Γ_j` check on a cell, from `G = |z_c|²`, `E` and `R`: `|z_c| ≤ Z`,
`G + 2E + R² ≤ Ghi` and `Glo G ≤ (G - E)²` with `E ≤ G`, `0 < G`. -/
def gammaOK (Glo Ghi G E R Z : ℚ) : Bool :=
  decide (0 ≤ Z) && decide (G ≤ Z * Z) && decide (G + 2 * E + R * R ≤ Ghi) && decide (0 < G) &&
    decide (E ≤ G) && decide (Glo * G ≤ (G - E) * (G - E))

/-- The `Γ_j` check on a cell. -/
def zOK (d : EccData) (j : Fin 3) (P₁ P₂ D₁ D₂ : GQ) (h₁ h₂ ε₁ ε₂ ρ₁ ρ₂ : ℚ) (sl sh : Fin 3 → ℚ)
    (Z : ℚ) : Bool :=
  let sc : Fin 3 → ℚ := ![(sl 0 + sh 0) / 2, (sl 1 + sh 1) / 2, (sl 2 + sh 2) / 2]
  let ds : Fin 3 → ℚ := ![(sh 0 - sl 0) / 2, (sh 1 - sl 1) / 2, (sh 2 - sl 2) / 2]
  let zc := zCen d.V j P₁ P₂ sc
  gammaOK (d.Glo j) (d.Ghi j) zc.nsq (zErr d.V j zc P₁ P₂ D₁ D₂ h₁ h₂ ρ₁ ρ₂ sh ds Z)
    (zRad d.V j ε₁ ε₂ sh ds) Z

/-- A box of the chart: signs `s₁, s₂` and parameter intervals `[lo₁, hi₁] × [lo₂, hi₂]`. -/
structure EBox where
  /-- The sign of the first chart. -/
  s₁ : Bool
  /-- The sign of the second chart. -/
  s₂ : Bool
  /-- Lower end, first parameter. -/
  lo₁ : ℚ
  /-- Upper end, first parameter. -/
  hi₁ : ℚ
  /-- Lower end, second parameter. -/
  lo₂ : ℚ
  /-- Upper end, second parameter. -/
  hi₂ : ℚ

/-- The centre `(lo + hi)/2` of a parameter interval. -/
def cellT (lo hi : ℚ) : ℚ := (lo + hi) / 2

/-- The half-width `(hi - lo)/2` of a parameter interval. -/
def cellH (lo hi : ℚ) : ℚ := (hi - lo) / 2

/-- The chord bound `2h(1 + h)/(1 + t_c²)` of a parameter interval (`norm_circ_sub`). -/
def cellEps (lo hi : ℚ) : ℚ :=
  2 * cellH lo hi * (1 + cellH lo hi) / (1 + cellT lo hi * cellT lo hi)

/-- The quadratic chart remainder `2h²/(1 + t_c²)` of a parameter interval
(`norm_circ_remainder`). -/
def cellRho (lo hi : ℚ) : ℚ := 2 * cellH lo hi * cellH lo hi / (1 + cellT lo hi * cellT lo hi)

/-- The fixed-point centre `B̃_k` at the cell centre, in Gaussian-integer arithmetic. -/
def cellCenter (d : EccData) (b : EBox) (k : Fin 3) : ℚ :=
  d.Ibar k + (bSumZ d.fix
    (GZ.table (circG b.s₁ (cellT b.lo₁ b.hi₁)) (circN (cellT b.lo₁ b.hi₁)) d.M)
    (GZ.table (circG b.s₂ (cellT b.lo₂ b.hi₂)) (circN (cellT b.lo₂ b.hi₂)) d.M) k : ℚ) /
    (pow2 d.K * ((circN (cellT b.lo₁ b.hi₁) ^ d.M * circN (cellT b.lo₂ b.hi₂) ^ d.M : ℤ) : ℚ))

/-- The `Γ_j` check at the cell of a box. -/
def cellZOK (d : EccData) (b : EBox) (sl sh : Fin 3 → ℚ) (Z : ℚ) (j : Fin 3) : Bool :=
  zOK d j (circPt b.s₁ (cellT b.lo₁ b.hi₁)) (circPt b.s₂ (cellT b.lo₂ b.hi₂))
    (circDer b.s₁ (cellT b.lo₁ b.hi₁)) (circDer b.s₂ (cellT b.lo₂ b.hi₂))
    (cellH b.lo₁ b.hi₁) (cellH b.lo₂ b.hi₂) (cellEps b.lo₁ b.hi₁) (cellEps b.lo₂ b.hi₂)
    (cellRho b.lo₁ b.hi₁) (cellRho b.lo₂ b.hi₂) sl sh Z

/-- The square-root check at the cell of a box. -/
def cellSqrtOK (d : EccData) (b : EBox) (sl sh : ℚ) (k : Fin 3) : Bool :=
  sqrtOK d k (cellCenter d b k) (cellEps b.lo₁ b.hi₁) (cellEps b.lo₂ b.hi₂) sl sh

/-- The leaf check on a box, with certificates `sl, sh` (square-root bounds) and `Z` (`|z_c|`
bounds). -/
def leafOK (d : EccData) (b : EBox) (sl sh Z : Fin 3 → ℚ) : Bool :=
  cellSqrtOK d b (sl 0) (sh 0) 0 && cellSqrtOK d b (sl 1) (sh 1) 1 &&
    cellSqrtOK d b (sl 2) (sh 2) 2 && cellZOK d b sl sh (Z 0) 0 && cellZOK d b sl sh (Z 1) 1 &&
    cellZOK d b sl sh (Z 2) 2

/-- A certificate tree: midpoint splits of the first (`false`) or second (`true`) parameter, with
leaves carrying `sl, sh, Z` as numerators over `2^PS`. -/
inductive ETree where
  /-- A leaf: numerators of `sl₀ sl₁ sl₂ sh₀ sh₁ sh₂ Z₀ Z₁ Z₂`. -/
  | leaf (l₀ l₁ l₂ u₀ u₁ u₂ z₀ z₁ z₂ : ℕ) : ETree
  /-- A midpoint split of the first (`false`) or second (`true`) parameter. -/
  | split (ax : Bool) (lo hi : ETree) : ETree

/-- Three numerators over `2^PS`. -/
def scale3 (PS a₀ a₁ a₂ : ℕ) : Fin 3 → ℚ :=
  ![(a₀ : ℚ) / pow2 PS, (a₁ : ℚ) / pow2 PS, (a₂ : ℚ) / pow2 PS]

/-- The lower half of a box along the first (`false`) or second (`true`) parameter. -/
def EBox.lower (b : EBox) : Bool → EBox
  | false => { b with hi₁ := (b.lo₁ + b.hi₁) / 2 }
  | true => { b with hi₂ := (b.lo₂ + b.hi₂) / 2 }

/-- The upper half of a box along the first (`false`) or second (`true`) parameter. -/
def EBox.upper (b : EBox) : Bool → EBox
  | false => { b with lo₁ := (b.lo₁ + b.hi₁) / 2 }
  | true => { b with lo₂ := (b.lo₂ + b.hi₂) / 2 }

/-- The tree check. -/
def checkTree (d : EccData) : EBox → ETree → Bool
  | b, .leaf l₀ l₁ l₂ u₀ u₁ u₂ z₀ z₁ z₂ =>
    leafOK d b (scale3 d.PS l₀ l₁ l₂) (scale3 d.PS u₀ u₁ u₂) (scale3 d.PS z₀ z₁ z₂)
  | b, .split ax t₁ t₂ => checkTree d (b.lower ax) t₁ && checkTree d (b.upper ax) t₂

/-- Assembling a split from checks of its halves (used to combine per-declaration blocks). -/
theorem checkTree_split_intro {d : EccData} {b : EBox} {ax : Bool} {t₁ t₂ : ETree}
    (h₁ : checkTree d (b.lower ax) t₁ = true) (h₂ : checkTree d (b.upper ax) t₂ = true) :
    checkTree d b (.split ax t₁ t₂) = true := by
  simp [checkTree, h₁, h₂]

/-- The root box of signs `(s₁, s₂)`: `[-1, 1]²`. -/
def rootBox (s₁ s₂ : Bool) : EBox := ⟨s₁, s₂, -1, 1, -1, 1⟩

end KAM.EffectiveStability.Tube

end
