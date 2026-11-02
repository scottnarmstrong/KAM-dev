/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.KeplerEccVector
public import KAM.Frozen.Planetary.Defs.PhysicalAMD
public import KAM.Planetary.Exponential.Dictionary
public import KAM.Planetary.Poincare.Product
public import KAM.Planetary.StrongAMD.Momentum

/-!
# The planar chart dictionary

Source: MAIN Lemma 7 (`LP:MAIN L7 (193–242)`, with N1 at line 238), track LP,
non-frozen.

The repository chart `poincareProd ν 1 : Phase (n + n) → Phase (n * 2)` (period `2π`, `κ = G m₀ =
1`)
is the chart of MAIN Lemma 7 with `(I, λ) = (Λ, λ)` and the slow pair `(ξ, η) = (x, −y)`.
Everything
here restates facts of `Poincare/*` and `Exponential/Dictionary.lean` in MAIN's vocabulary:

* the image of the chart domain is exactly the prograde elliptic region (`lpChart_image`);
* the per-planet dictionary: action `I = Λ`, energy `−ν³/(2 I²)`, momentum `L = I − Γ`, the
  eccentricity vector `keplerEccVector = poincareV`, `e² = 1 − (1 − Γ/I)²`, and MAIN's
  `(k, l) = b_e (x, −y)` (`lpChart_eccVector_xy`);
* the AMD `C = (∑ I_i) − |L|` of MAIN (2) (`strongAMD`, the planar momentum identities) equals `chartAMD w`;
* one-line corollaries: Hamiltonian identity, symplecticity, analyticity, periodicity, inverse.
-/

@[expose] public noncomputable section

open KAM KAM.Kepler KAM.Planetary

namespace KAM.Planetary.StrongAMD

variable {n : ℕ}

/-- MAIN's `b_e = √((1 − Γ/(2I))/I)` (`LP:MAIN L7 (205)`), with `Γ = (x² + y²)/2` replaced by its
value. -/
def lpEccScale (I Γ : ℝ) : ℝ := √((1 - Γ / (2 * I)) / I)

/-- The oscillator action `Γ_i = (ξ_i² + η_i²)/2` of the `i`-th planet in chart coordinates. -/
def lpGamma (w : Phase (n + n)) (i : Fin n) : ℝ := ((slow w.1 i) ^ 2 + (slow w.2 i) ^ 2) / 2

/-! ### Region -/

/-- (LP:MAIN L7 (195)) The chart maps its domain onto the prograde elliptic region. -/
theorem lpChart_image {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) :
    poincareProd ν 1 '' poincareProdDom n = {z | ProgradeElliptic ν z} :=
  poincareProd_image_prograde hν

/-! ### Per-planet dictionary -/

private theorem planetBlock_snd_zero (w : Phase (n + n)) (i : Fin n) :
    (planetBlock w i).2 0 = fast w.2 i := by simp [planetBlock]

/-- (LP:MAIN L7 (200)) `I = Λ`: the Kepler action of planet `i` is the fast action `Λ_i`. -/
theorem lpChart_action {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {w : Phase (n + n)}
    (hw : w ∈ poincareProdDom n) (i : Fin n) :
    keplerAction ν (poincareProd ν 1 w) i = fast w.2 i :=
  (poincareProd_planet_facts hν hw i).1

/-- (LP:MAIN L7 (226)) The eccentricity vector of planet `i` is the regular vector `poincareV`
of its chart block. -/
theorem lpChart_eccVector {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {w : Phase (n + n)}
    (hw : w ∈ poincareProdDom n) (i : Fin n) :
    keplerEccVector ν (poincareProd ν 1 w) i = poincareV (planetBlock w i) := by
  obtain ⟨-, -, -, -, -, hV⟩ := poincare_elements (hν i) one_pos (hw i)
  have hb := poincareProd_block ν 1 w i
  have h1 : bodyVector (poincareProd ν 1 w).1 i = (poincare (ν i) 1 (planetBlock w i)).1 :=
    congrArg Prod.fst hb
  have h2 : bodyVector (poincareProd ν 1 w).2 i = (poincare (ν i) 1 (planetBlock w i)).2 :=
    congrArg Prod.snd hb
  rw [← hV]
  unfold keplerEccVector
  simp only [h1, h2, inv_one, one_smul]

/-- (LP:MAIN L7 (199, 205)) MAIN's `(k, l) = b_e (x, −y)` against the repository's
`poincareV = b_e (ξ, η)`: under `(ξ, η) = (x, −y)` the chart block's eccentricity vector is
`(b_e x, −b_e y)`, i.e. `k = b_e x`, `l = −b_e y`. -/
theorem lpChart_eccVector_xy {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {w : Phase (n + n)}
    (hw : w ∈ poincareProdDom n) (i : Fin n) {x y : ℝ}
    (hx : slow w.1 i = x) (hy : slow w.2 i = -y) :
    keplerEccVector ν (poincareProd ν 1 w) i =
      ![lpEccScale (fast w.2 i) (lpGamma w i) * x,
        -(lpEccScale (fast w.2 i) (lpGamma w i) * y)] := by
  rw [lpChart_eccVector hν hw i]
  have h0 : (planetBlock w i).2 0 = fast w.2 i := planetBlock_snd_zero w i
  have hΓ : poincareGamma (planetBlock w i) = lpGamma w i := by
    simp [poincareGamma, lpGamma, planetBlock, slow]
  have hs : poincareV (planetBlock w i) =
      lpEccScale (fast w.2 i) (lpGamma w i) • ![slow w.1 i, slow w.2 i] := by
    unfold poincareV lpEccScale
    rw [h0, hΓ]
    simp [planetBlock]
  rw [hs, hx, hy]
  funext j
  fin_cases j <;> simp

/-! ### AMD in the chart -/

/-- (LP:MAIN L7 (200)) The physical AMD of the chart image is the chart AMD (exists in track P). -/
theorem lpChart_physicalAMD {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {w : Phase (n + n)}
    (hw : w ∈ poincareProdDom n) : physicalAMD ν (poincareProd ν 1 w) = chartAMD w :=
  (sec_domain_chart_facts hν hw).2.2

/-- (LP:MAIN L7 (200), §1 (2)) MAIN's `C = ∑ I_i − |L|` (`strongAMD`, the planar momentum identities) of the chart
image is `chartAMD w`, i.e. `∑ (x_i² + y_i²)/2`. -/
theorem lpChart_strongAMD {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {w : Phase (n + n)}
    (hw : w ∈ poincareProdDom n) : strongAMD ν (poincareProd ν 1 w) = chartAMD w := by
  have hpro := (sec_domain_chart_facts hν hw).1
  have hL : 0 ≤ totalMomentum (poincareProd ν 1 w) :=
    Finset.sum_nonneg fun i _ => (hpro i).2.2.2.le
  rw [strongAMD_eq_physicalAMD hL, lpChart_physicalAMD hν hw]

/-- The chart AMD is the sum of the oscillator actions `Γ_i`. -/
theorem chartAMD_eq_sum_lpGamma (w : Phase (n + n)) : chartAMD w = ∑ i, lpGamma w i := rfl

/-! ### MAIN-facing corollaries at `κ = 1` -/

/-- The chart Hamiltonian identity: the moving Hamiltonian in chart coordinates is the Kepler part
`hProd 1 ν = −∑ ν_i³/(2 Λ_i²)` plus `μ` times the perturbation. -/
theorem lpChart_hamiltonian {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (μ : ℝ) {w : Phase (n + n)}
    (hw : w ∈ poincareProdDom n) :
    movingHamiltonian 1 1 ν μ (poincareProd ν 1 w) =
      hProd 1 ν w + μ * fMov 1 1 ν (poincareProd ν 1 w) := by
  have := movingHamiltonian_poincareProd (G := 1) (m0 := 1) (μ := μ) hν (by norm_num) hw
  simpa only [mul_one] using this

/-- The inverse on the prograde region: every prograde elliptic point has a chart preimage, unique
modulo the lattice `2π ℤⁿ` of fast angles. -/
theorem lpChart_inverse {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {z : Phase (n * 2)}
    (hz : ProgradeElliptic ν z) :
    ∃ w ∈ poincareProdDom n, poincareProd ν 1 w = z ∧
      ∀ w' ∈ poincareProdDom n, poincareProd ν 1 w' = z ↔
        ∃ k : Fin n → ℤ, w' = w + fastShift (a := n) (b := n) k := by
  have hz' : z ∈ poincareProd ν 1 '' poincareProdDom n := (lpChart_image hν).symm ▸ hz
  obtain ⟨w, hw, rfl⟩ := hz'
  refine ⟨w, hw, rfl, fun w' hw' => ?_⟩
  rw [eq_comm, poincareProd_eq_iff hν one_pos hw hw']

end KAM.Planetary.StrongAMD

end
