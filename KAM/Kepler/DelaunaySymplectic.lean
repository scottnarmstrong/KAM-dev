/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Basic
public import KAM.Kepler.Plane
public import KAM.Kepler.Energy
public import KAM.Kepler.Equation
public import KAM.Kepler.Orbit
public import KAM.Kepler.DelaunayJacobian

/-!
# Symplecticity of the Delaunay map

`delaunay_symplectic` (`𝖰^*(Σ dq ∧ dp) = dℓ ∧ dL + dg ∧ dG`,
    i.e. `IsSymplecticOn 1 delaunay deDom`),
invertibility of `D𝖰`, the Liouville primitive `𝖰^*(Σ p dq) = L dℓ + G dg + dF` with
`F = 2 L e sin u` (`delaunayGen`), and the Hamiltonian-field consequence
(`bpI:p7:symplectic`).

The explicit Jacobian columns `orbitMapColumn` live in `KAM.Kepler.DelaunayJacobian` (imported
publicly, so they are available here and to every importer of this module). Proof plan:

* The six Lagrange brackets of the four columns in the intermediate coordinates `(ℓ, g, L, e)` are
  rational identities in `L, e, cos u, sin u, √(1-e²)`: `br01 … br23` (pure real lemmas, checked
  by `field_simp` and a certificate for the two relations `sin² + cos² = 1`, `k² = 1 - e²`).
  The rotation by `g` drops out (`planeDot_rot`), column `g` is the quarter turn of the orbit.
* The change of variables `e = eccOf L G` gives the Delaunay columns; their brackets are the
  standard ones, so `Ω (Au) (Av) = Ω u v` on the basis, hence everywhere (`symp_of_basis`).
* Liouville: the four identities `lv0 … lv3` on the columns, plus the derivative of `F` along
  coordinate lines.
* Invertibility: `Ω` is nondegenerate, so a symplectic endomorphism is injective, hence bijective.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology
open scoped ContDiff

namespace KAM.Kepler

open KAM KAM.Planetary

section PureAlgebra

private theorem br01 (L e c s k D : ℝ) (hD0 : D ≠ 0) (_hk0 : k ≠ 0) (_hL0 : L ≠ 0)
    (hs : s ^ 2 + c ^ 2 = 1) (hk : k ^ 2 = 1 - e ^ 2) (hD : D = 1 - e * c) :
    (((1/D)*(-(c - e)/(L*D^2)))*(-(L^2*k*s)) + ((1/D)*(-k*s/(L*D^2)))*((L^2*(c - e)))) -
        (((1/D)*(-L^2*s))*(-(k*c/(L*D))) + ((1/D)*(L^2*k*c))*((-s/(L*D)))) = 0 := by
  have key : (((1/D)*(-(c - e)/(L*D^2)))*(-(L^2*k*s)) + ((1/D)*(-k*s/(L*D^2)))*((L^2*(c - e)))) -
      (((1/D)*(-L^2*s))*(-(k*c/(L*D))) + ((1/D)*(L^2*k*c))*((-s/(L*D)))) = (0) / (1 : ℝ) := by
    field_simp
    ring
  have hden : (1 : ℝ) ≠ 0 := by norm_num
  rw [key]
  rw [div_eq_iff hden]
  linear_combination (0) * hs + (0) * hk + (0) * hD

private theorem br02 (L e c s k D : ℝ) (hD0 : D ≠ 0) (_hk0 : k ≠ 0) (hL0 : L ≠ 0)
    (hs : s ^ 2 + c ^ 2 = 1) (hk : k ^ 2 = 1 - e ^ 2) (hD : D = 1 - e * c) :
    (((1/D)*(-(c - e)/(L*D^2)))*(2*L*(c - e)) + ((1/D)*(-k*s/(L*D^2)))*(2*L*k*s)) -
        (((1/D)*(-L^2*s))*(s/(L^2*D)) + ((1/D)*(L^2*k*c))*(-k*c/(L^2*D))) = -1 := by
  have key : (((1/D)*(-(c - e)/(L*D^2)))*(2*L*(c - e)) + ((1/D)*(-k*s/(L*D^2)))*(2*L*k*s)) -
      (((1/D)*(-L^2*s))*(s/(L^2*D)) + ((1/D)*(L^2*k*c))*(-k*c/(L^2*D))) = (D*c^2*k^2 + D*s^2 -
      2*c^2 + 4*c*e - 2*e^2 - 2*k^2*s^2) / (D^3 : ℝ) := by
    field_simp
    ring
  have hden : (D^3 : ℝ) ≠ 0 := by simp [hD0]
  rw [key]
  rw [div_eq_iff hden]
  linear_combination (D - 2*k^2) * hs + (D*c^2 + 2*c^2 - 2) * hk + (D^2 - D*c*e + D - 2*c*e + 2) *
      hD

private theorem br03 (L e c s k D : ℝ) (hD0 : D ≠ 0) (hk0 : k ≠ 0) (hL0 : L ≠ 0)
    (hs : s ^ 2 + c ^ 2 = 1) (hk : k ^ 2 = 1 - e ^ 2) (hD : D = 1 - e * c) :
    (((1/D)*(-(c - e)/(L*D^2)))*((-L^2) + (s/D)*(-L^2*s)) + ((1/D)*(-k*s/(L*D^2)))*((-L^2*e*s/k) +
        (s/D)*(L^2*k*c))) - (((1/D)*(-L^2*s))*((-s*c/(L*D^2)) + (s/D)*(-(c - e)/(L*D^2))) +
        ((1/D)*(L^2*k*c))*((c*(c - e)/(L*D^2*k)) + (s/D)*(-k*s/(L*D^2)))) = 0 := by
  have key : (((1/D)*(-(c - e)/(L*D^2)))*((-L^2) + (s/D)*(-L^2*s)) +
      ((1/D)*(-k*s/(L*D^2)))*((-L^2*e*s/k) + (s/D)*(L^2*k*c))) - (((1/D)*(-L^2*s))*((-s*c/(L*D^2))
      + (s/D)*(-(c - e)/(L*D^2))) + ((1/D)*(L^2*k*c))*((c*(c - e)/(L*D^2*k)) +
      (s/D)*(-k*s/(L*D^2)))) = (-D*L*c^3 + D*L*c^2*e - D*L*c*s^2 + D*L*c + D*L*e*s^2 - D*L*e) /
      (D^4 : ℝ) := by
    field_simp
    ring
  have hden : (D^4 : ℝ) ≠ 0 := by simp [hD0]
  rw [key]
  rw [div_eq_iff hden]
  linear_combination (-D*L*c + D*L*e) * hs + (0) * hk + (0) * hD

private theorem br12 (L e c s k D : ℝ) (hD0 : D ≠ 0) (hk0 : k ≠ 0) (hL0 : L ≠ 0)
    (hs : s ^ 2 + c ^ 2 = 1) (hk : k ^ 2 = 1 - e ^ 2) (hD : D = 1 - e * c) :
    ((-(k*c/(L*D)))*(2*L*(c - e)) + ((-s/(L*D)))*(2*L*k*s)) - ((-(L^2*k*s))*(s/(L^2*D)) + ((L^2*(c
        - e)))*(-k*c/(L^2*D))) = -k := by
  have key : ((-(k*c/(L*D)))*(2*L*(c - e)) + ((-s/(L*D)))*(2*L*k*s)) - ((-(L^2*k*s))*(s/(L^2*D)) +
      ((L^2*(c - e)))*(-k*c/(L^2*D))) = (-c^2*k + c*e*k - k*s^2) / (D : ℝ) := by
    field_simp
    ring
  have hden : (D : ℝ) ≠ 0 := by simp [hD0]
  rw [key]
  rw [div_eq_iff hden]
  linear_combination (-k) * hs + (0) * hk + (k) * hD

private theorem br13 (L e c s k D : ℝ) (hD0 : D ≠ 0) (hk0 : k ≠ 0) (hL0 : L ≠ 0)
    (hs : s ^ 2 + c ^ 2 = 1) (hk : k ^ 2 = 1 - e ^ 2) (hD : D = 1 - e * c) :
    ((-(k*c/(L*D)))*((-L^2) + (s/D)*(-L^2*s)) + ((-s/(L*D)))*((-L^2*e*s/k) + (s/D)*(L^2*k*c))) -
        ((-(L^2*k*s))*((-s*c/(L*D^2)) + (s/D)*(-(c - e)/(L*D^2))) + ((L^2*(c - e)))*((c*(c -
        e)/(L*D^2*k)) + (s/D)*(-k*s/(L*D^2)))) = L*e/k := by
  have key : ((-(k*c/(L*D)))*((-L^2) + (s/D)*(-L^2*s)) + ((-s/(L*D)))*((-L^2*e*s/k) +
      (s/D)*(L^2*k*c))) - ((-(L^2*k*s))*((-s*c/(L*D^2)) + (s/D)*(-(c - e)/(L*D^2))) + ((L^2*(c -
      e)))*((c*(c - e)/(L*D^2*k)) + (s/D)*(-k*s/(L*D^2)))) = (D^2*L*c*k^2 + D^2*L*e*s^2 - D*L*c^3 +
      2*D*L*c^2*e - D*L*c*e^2 - D*L*c*k^2*s^2) / (D^3*k : ℝ) := by
    field_simp
    ring
  have hden : (D^3*k : ℝ) ≠ 0 := by simp [hD0, hk0]
  rw [key]
  rw [div_eq_div_iff hden hk0]
  linear_combination (D^2*L*e*k - D*L*c*k^3) * hs + (D^2*L*c*k + D*L*c^3*k - D*L*c*k) * hk +
      (-D^2*L*e*k - D*L*c^2*e*k + D*L*c*k) * hD

private theorem br23 (L e c s k D : ℝ) (hD0 : D ≠ 0) (hk0 : k ≠ 0) (hL0 : L ≠ 0)
    (hs : s ^ 2 + c ^ 2 = 1) (hk : k ^ 2 = 1 - e ^ 2) (hD : D = 1 - e * c) :
    ((s/(L^2*D))*((-L^2) + (s/D)*(-L^2*s)) + (-k*c/(L^2*D))*((-L^2*e*s/k) + (s/D)*(L^2*k*c))) -
        ((2*L*(c - e))*((-s*c/(L*D^2)) + (s/D)*(-(c - e)/(L*D^2))) + (2*L*k*s)*((c*(c -
        e)/(L*D^2*k)) + (s/D)*(-k*s/(L*D^2)))) = 0 := by
  have key : ((s/(L^2*D))*((-L^2) + (s/D)*(-L^2*s)) + (-k*c/(L^2*D))*((-L^2*e*s/k) +
      (s/D)*(L^2*k*c))) - ((2*L*(c - e))*((-s*c/(L*D^2)) + (s/D)*(-(c - e)/(L*D^2))) +
      (2*L*k*s)*((c*(c - e)/(L*D^2*k)) + (s/D)*(-k*s/(L*D^2)))) = (D^2*c*e*s - D^2*s - D*c^2*k^2*s
      - D*s^3 + 2*c^2*s - 4*c*e*s + 2*e^2*s + 2*k^2*s^3) / (D^3 : ℝ) := by
    field_simp
    ring
  have hden : (D^3 : ℝ) ≠ 0 := by simp [hD0]
  rw [key]
  rw [div_eq_iff hden]
  linear_combination (-D*s + 2*k^2*s) * hs + (-D*c^2*s - 2*c^2*s + 2*s) * hk + (D*c*e*s - D*s +
      2*c*e*s - 2*s) * hD

private theorem lv0 (L e c s k D : ℝ) (hD0 : D ≠ 0) (_hk0 : k ≠ 0) (hL0 : L ≠ 0)
    (hs : s ^ 2 + c ^ 2 = 1) (hk : k ^ 2 = 1 - e ^ 2) (hD : D = 1 - e * c) :
    (-s/(L*D))*((1/D)*(-L^2*s)) + (k*c/(L*D))*((1/D)*(L^2*k*c)) = L + 2*L*e*c/D := by
  have hd : (D^2 : ℝ) ≠ 0 := by simp [hD0]
  have htd : (D : ℝ) ≠ 0 := by simp [hD0]
  have key : (-s/(L*D))*((1/D)*(-L^2*s)) + (k*c/(L*D))*((1/D)*(L^2*k*c)) = (L*c^2*k^2 + L*s^2) /
      (D^2 : ℝ) := by
    field_simp
    ring
  have key2 : L + 2*L*e*c/D = (D*L + 2*L*c*e) / (D : ℝ) := by
    field_simp
  rw [key, key2, div_eq_div_iff hd htd]
  linear_combination (D*L) * hs + (D*L*c^2) * hk + (-D^2*L - D*L*c*e - D*L) * hD

private theorem lv1 (L e c s k D : ℝ) (hD0 : D ≠ 0) (hk0 : k ≠ 0) (hL0 : L ≠ 0)
    (hs : s ^ 2 + c ^ 2 = 1) (hk : k ^ 2 = 1 - e ^ 2) (hD : D = 1 - e * c) :
    (-s/(L*D))*(-(L^2*k*s)) + (k*c/(L*D))*((L^2*(c - e))) = L*k := by
  have hd : (D : ℝ) ≠ 0 := by simp [hD0]
  have htd : (1 : ℝ) ≠ 0 := by norm_num
  have key : (-s/(L*D))*(-(L^2*k*s)) + (k*c/(L*D))*((L^2*(c - e))) = (L*c^2*k - L*c*e*k + L*k*s^2)
      / (D : ℝ) := by
    field_simp
    ring
  have key2 : L*k = (L*k) / (1 : ℝ) := by
    field_simp
  rw [key, key2, div_eq_div_iff hd htd]
  linear_combination (L*k) * hs + (0) * hk + (-L*k) * hD

private theorem lv2 (L e c s k D : ℝ) (hD0 : D ≠ 0) (_hk0 : k ≠ 0) (hL0 : L ≠ 0)
    (hs : s ^ 2 + c ^ 2 = 1) (hk : k ^ 2 = 1 - e ^ 2) (hD : D = 1 - e * c) :
    (-s/(L*D))*(2*L*(c - e)) + (k*c/(L*D))*(2*L*k*s) = 2*e*s := by
  have hd : (D : ℝ) ≠ 0 := by simp [hD0]
  have htd : (1 : ℝ) ≠ 0 := by norm_num
  have key : (-s/(L*D))*(2*L*(c - e)) + (k*c/(L*D))*(2*L*k*s) = (2*c*k^2*s - 2*c*s + 2*e*s) / (D :
      ℝ) := by
    field_simp
    ring
  have key2 : 2*e*s = (2*e*s) / (1 : ℝ) := by
    field_simp
  rw [key, key2, div_eq_div_iff hd htd]
  linear_combination (0) * hs + (2*c*s) * hk + (-2*e*s) * hD

private theorem lv3 (L e c s k D : ℝ) (hD0 : D ≠ 0) (hk0 : k ≠ 0) (hL0 : L ≠ 0)
    (hs : s ^ 2 + c ^ 2 = 1) (hk : k ^ 2 = 1 - e ^ 2) (hD : D = 1 - e * c) :
    (-s/(L*D))*((-L^2) + (s/D)*(-L^2*s)) + (k*c/(L*D))*((-L^2*e*s/k) + (s/D)*(L^2*k*c)) = 2*L*s +
        2*L*e*c*s/D := by
  have hd : (D^2 : ℝ) ≠ 0 := by simp [hD0]
  have htd : (D : ℝ) ≠ 0 := by simp [hD0]
  have key : (-s/(L*D))*((-L^2) + (s/D)*(-L^2*s)) + (k*c/(L*D))*((-L^2*e*s/k) + (s/D)*(L^2*k*c)) =
      (-D*L*c*e*s + D*L*s + L*c^2*k^2*s + L*s^3) / (D^2 : ℝ) := by
    field_simp
    ring
  have key2 : 2*L*s + 2*L*e*c*s/D = (2*D*L*s + 2*L*c*e*s) / (D : ℝ) := by
    field_simp
  rw [key, key2, div_eq_div_iff hd htd]
  linear_combination (D*L*s) * hs + (D*L*c^2*s) * hk + (-2*D^2*L*s - D*L*c*e*s - D*L*s) * hD

end PureAlgebra

section SymplecticAlgebra

private theorem sf_eq (a b : Phase 2) : symplecticForm a b =
    (a.2 0 * b.1 0 + a.2 1 * b.1 1) - (a.1 0 * b.2 0 + a.1 1 * b.2 1) := by
  simp [symplecticForm, Fin.sum_univ_two]

private theorem sf_eq_planeDot (a b : Phase 2) :
    symplecticForm a b = planeDot a.2 b.1 - planeDot a.1 b.2 := by
  simp [symplecticForm, planeDot, Fin.sum_univ_two]

private theorem sf_rot (g : ℝ) (a b : Phase 2) :
    symplecticForm (rot g a.1, rot g a.2) (rot g b.1, rot g b.2) = symplecticForm a b := by
  simp only [sf_eq_planeDot, planeDot_rot]

private theorem sf_add_right (a b b' : Phase 2) :
    symplecticForm a (b + b') = symplecticForm a b + symplecticForm a b' := by
  simp only [sf_eq]; simp; ring

private theorem sf_add_left (a a' b : Phase 2) :
    symplecticForm (a + a') b = symplecticForm a b + symplecticForm a' b := by
  simp only [sf_eq]; simp; ring

private theorem sf_smul_right (r : ℝ) (a b : Phase 2) :
    symplecticForm a (r • b) = r * symplecticForm a b := by
  simp only [sf_eq]; simp; ring

private theorem sf_smul_left (r : ℝ) (a b : Phase 2) :
    symplecticForm (r • a) b = r * symplecticForm a b := by
  simp only [sf_eq]; simp; ring

private theorem sf_sub_right (a b b' : Phase 2) :
    symplecticForm a (b - b') = symplecticForm a b - symplecticForm a b' := by
  simp only [sf_eq]; simp; ring

private theorem sf_self (a : Phase 2) : symplecticForm a a = 0 := by
  simp only [sf_eq]; ring

private theorem sf_comm (a b : Phase 2) : symplecticForm a b = -symplecticForm b a := by
  simp only [sf_eq]; ring

private theorem planeDot_add_right (a b b' : Fin 2 → ℝ) :
    planeDot a (b + b') = planeDot a b + planeDot a b' := by
  simp [planeDot, Fin.sum_univ_two]; ring

private theorem planeDot_smul_right (r : ℝ) (a b : Fin 2 → ℝ) :
    planeDot a (r • b) = r * planeDot a b := by
  simp [planeDot, Fin.sum_univ_two]; ring

/-- The coordinate vectors of `Phase 2` (positions `ℓ, g`, momenta `L, G`). -/
private def b0 : Phase 2 := (Pi.single 0 1, 0)
private def b1 : Phase 2 := (Pi.single 1 1, 0)
private def b2 : Phase 2 := (0, Pi.single 0 1)
private def b3 : Phase 2 := (0, Pi.single 1 1)

private theorem phase2_decomp (u : Phase 2) :
    u = u.1 0 • b0 + u.1 1 • b1 + u.2 0 • b2 + u.2 1 • b3 := by
  ext i <;> fin_cases i <;> simp [b0, b1, b2, b3]

private theorem clm_decomp {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (T : Phase 2 →L[ℝ] V) (u : Phase 2) :
    T u = u.1 0 • T b0 + u.1 1 • T b1 + u.2 0 • T b2 + u.2 1 • T b3 := by
  conv_lhs => rw [phase2_decomp u]
  simp [map_add, map_smul]

/-- A linear map on `Phase 2` which preserves the six brackets of the coordinate vectors preserves
the symplectic form. -/
private theorem symp_of_basis (A : Phase 2 →L[ℝ] Phase 2)
    (h01 : symplecticForm (A b0) (A b1) = 0) (h02 : symplecticForm (A b0) (A b2) = -1)
    (h03 : symplecticForm (A b0) (A b3) = 0) (h12 : symplecticForm (A b1) (A b2) = 0)
    (h13 : symplecticForm (A b1) (A b3) = -1) (h23 : symplecticForm (A b2) (A b3) = 0)
    (u v : Phase 2) : symplecticForm (A u) (A v) = symplecticForm u v := by
  rw [clm_decomp A u, clm_decomp A v]
  simp only [sf_eq] at h01 h02 h03 h12 h13 h23 ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  linear_combination (u.1 0 * v.2 0 - u.2 0 * v.1 0) * h02 + (u.1 1 * v.2 1 - u.2 1 * v.1 1) * h13
    + (u.1 0 * v.1 1 - u.1 1 * v.1 0) * h01 + (u.1 0 * v.2 1 - u.2 1 * v.1 0) * h03
    + (u.1 1 * v.2 0 - u.2 0 * v.1 1) * h12 + (u.2 0 * v.2 1 - u.2 1 * v.2 0) * h23

/-- Nondegeneracy of the symplectic form in the first argument. -/
private theorem eq_zero_of_sf_eq_zero {u : Phase 2} (h : ∀ v, symplecticForm u v = 0) : u = 0 := by
  have h0 : u.2 0 = 0 := by simpa [sf_eq, b0] using h b0
  have h1 : u.2 1 = 0 := by simpa [sf_eq, b1] using h b1
  have h2 : u.1 0 = 0 := by simpa [sf_eq, b2] using h b2
  have h3 : u.1 1 = 0 := by simpa [sf_eq, b3] using h b3
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;> simp [*]

end SymplecticAlgebra

section Columns

/-- The Jacobian columns in the orbit frame, before the rotation by `g` (`c = cos u`, `s = sin u`,
`k = √(1 - e²)`, `D = 1 - e c`; `D` is a parameter so that the pure real lemmas treat it as an
atom). Column `0` is `ℓ`, `1` is `g`, `2` is `L`, `3` is `e`. -/
private def colF0 (L e c s k D : ℝ) : Phase 2 :=
  ((1 / D) • ![-L ^ 2 * s, L ^ 2 * k * c],
   (1 / D) • ![-(c - e) / (L * D ^ 2), -k * s / (L * D ^ 2)])

private def colF1 (L e c s k D : ℝ) : Phase 2 :=
  (quarterTurn ![L ^ 2 * (c - e), L ^ 2 * k * s], quarterTurn ![-s / (L * D), k * c / (L * D)])

private def colF2 (L e c s k D : ℝ) : Phase 2 :=
  (![2 * L * (c - e), 2 * L * k * s], ![s / (L ^ 2 * D), -k * c / (L ^ 2 * D)])

private def colF3 (L e c s k D : ℝ) : Phase 2 :=
  (![-L ^ 2, -L ^ 2 * e * s / k] + (s / D) • ![-L ^ 2 * s, L ^ 2 * k * c],
   ![-s * c / (L * D ^ 2), c * (c - e) / (L * D ^ 2 * k)] +
    (s / D) • ![-(c - e) / (L * D ^ 2), -k * s / (L * D ^ 2)])

private theorem orbitMapColumn_eq0 (ℓ g L e : ℝ) :
    orbitMapColumn ℓ g L e 0 =
      (rot g (colF0 L e (Real.cos (eccAnom ℓ e)) (Real.sin (eccAnom ℓ e)) √(1 - e ^ 2)
          (1 - e * Real.cos (eccAnom ℓ e))).1,
       rot g (colF0 L e (Real.cos (eccAnom ℓ e)) (Real.sin (eccAnom ℓ e)) √(1 - e ^ 2)
          (1 - e * Real.cos (eccAnom ℓ e))).2) := rfl

private theorem orbitMapColumn_eq1 (ℓ g L e : ℝ) :
    orbitMapColumn ℓ g L e 1 =
      (rot g (colF1 L e (Real.cos (eccAnom ℓ e)) (Real.sin (eccAnom ℓ e)) √(1 - e ^ 2)
          (1 - e * Real.cos (eccAnom ℓ e))).1,
       rot g (colF1 L e (Real.cos (eccAnom ℓ e)) (Real.sin (eccAnom ℓ e)) √(1 - e ^ 2)
          (1 - e * Real.cos (eccAnom ℓ e))).2) :=
  Prod.ext (rot_quarterTurn g _).symm (rot_quarterTurn g _).symm

private theorem orbitMapColumn_eq2 (ℓ g L e : ℝ) :
    orbitMapColumn ℓ g L e 2 =
      (rot g (colF2 L e (Real.cos (eccAnom ℓ e)) (Real.sin (eccAnom ℓ e)) √(1 - e ^ 2)
          (1 - e * Real.cos (eccAnom ℓ e))).1,
       rot g (colF2 L e (Real.cos (eccAnom ℓ e)) (Real.sin (eccAnom ℓ e)) √(1 - e ^ 2)
          (1 - e * Real.cos (eccAnom ℓ e))).2) := rfl

private theorem orbitMapColumn_eq3 (ℓ g L e : ℝ) :
    orbitMapColumn ℓ g L e 3 =
      (rot g (colF3 L e (Real.cos (eccAnom ℓ e)) (Real.sin (eccAnom ℓ e)) √(1 - e ^ 2)
          (1 - e * Real.cos (eccAnom ℓ e))).1,
       rot g (colF3 L e (Real.cos (eccAnom ℓ e)) (Real.sin (eccAnom ℓ e)) √(1 - e ^ 2)
          (1 - e * Real.cos (eccAnom ℓ e))).2) := rfl

/-- The hypotheses of the pure bracket lemmas, for `u = eccAnom ℓ e`. -/
private theorem col_hyps {e : ℝ} (u : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) :
    1 - e * Real.cos u ≠ 0 ∧ √(1 - e ^ 2) ≠ 0 ∧ Real.sin u ^ 2 + Real.cos u ^ 2 = 1 ∧
      √(1 - e ^ 2) ^ 2 = 1 - e ^ 2 := by
  have h1 : 0 < 1 - e ^ 2 := by nlinarith
  refine ⟨?_, Real.sqrt_ne_zero'.2 h1, Real.sin_sq_add_cos_sq u, Real.sq_sqrt h1.le⟩
  have := Real.cos_le_one u
  nlinarith

section Brackets
variable {ℓ g L e : ℝ}

private theorem col_br01 (hL : 0 < L) (he0 : 0 ≤ e) (he1 : e < 1) :
    symplecticForm (orbitMapColumn ℓ g L e 0) (orbitMapColumn ℓ g L e 1) = 0 := by
  obtain ⟨hD, hk0, hs, hk⟩ := col_hyps (eccAnom ℓ e) he0 he1
  rw [orbitMapColumn_eq0, orbitMapColumn_eq1, sf_rot, sf_eq]
  simp only [colF0, colF1, quarterTurn, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply,
    smul_eq_mul]
  linear_combination br01 L e _ _ _ _ hD hk0 hL.ne' hs hk rfl

private theorem col_br02 (hL : 0 < L) (he0 : 0 ≤ e) (he1 : e < 1) :
    symplecticForm (orbitMapColumn ℓ g L e 0) (orbitMapColumn ℓ g L e 2) = -1 := by
  obtain ⟨hD, hk0, hs, hk⟩ := col_hyps (eccAnom ℓ e) he0 he1
  rw [orbitMapColumn_eq0, orbitMapColumn_eq2, sf_rot, sf_eq]
  simp only [colF0, colF2, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
  linear_combination br02 L e _ _ _ _ hD hk0 hL.ne' hs hk rfl

private theorem col_br03 (hL : 0 < L) (he0 : 0 ≤ e) (he1 : e < 1) :
    symplecticForm (orbitMapColumn ℓ g L e 0) (orbitMapColumn ℓ g L e 3) = 0 := by
  obtain ⟨hD, hk0, hs, hk⟩ := col_hyps (eccAnom ℓ e) he0 he1
  rw [orbitMapColumn_eq0, orbitMapColumn_eq3, sf_rot, sf_eq]
  simp only [colF0, colF3, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul]
  linear_combination br03 L e _ _ _ _ hD hk0 hL.ne' hs hk rfl

private theorem col_br12 (hL : 0 < L) (he0 : 0 ≤ e) (he1 : e < 1) :
    symplecticForm (orbitMapColumn ℓ g L e 1) (orbitMapColumn ℓ g L e 2) = -√(1 - e ^ 2) := by
  obtain ⟨hD, hk0, hs, hk⟩ := col_hyps (eccAnom ℓ e) he0 he1
  rw [orbitMapColumn_eq1, orbitMapColumn_eq2, sf_rot, sf_eq]
  simp only [colF1, colF2, quarterTurn, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination br12 L e _ _ _ _ hD hk0 hL.ne' hs hk rfl

private theorem col_br13 (hL : 0 < L) (he0 : 0 ≤ e) (he1 : e < 1) :
    symplecticForm (orbitMapColumn ℓ g L e 1) (orbitMapColumn ℓ g L e 3) = L * e / √(1 - e ^ 2)
        := by
  obtain ⟨hD, hk0, hs, hk⟩ := col_hyps (eccAnom ℓ e) he0 he1
  rw [orbitMapColumn_eq1, orbitMapColumn_eq3, sf_rot, sf_eq]
  simp only [colF1, colF3, quarterTurn, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul]
  linear_combination br13 L e _ _ _ _ hD hk0 hL.ne' hs hk rfl

private theorem col_br23 (hL : 0 < L) (he0 : 0 ≤ e) (he1 : e < 1) :
    symplecticForm (orbitMapColumn ℓ g L e 2) (orbitMapColumn ℓ g L e 3) = 0 := by
  obtain ⟨hD, hk0, hs, hk⟩ := col_hyps (eccAnom ℓ e) he0 he1
  rw [orbitMapColumn_eq2, orbitMapColumn_eq3, sf_rot, sf_eq]
  simp only [colF2, colF3, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul]
  linear_combination br23 L e _ _ _ _ hD hk0 hL.ne' hs hk rfl

end Brackets

end Columns
section DelaunayLevel

private theorem eccOf_sqrt {L G : ℝ} (hG : 0 < G) (hGL : G < L) :
    √(1 - eccOf L G ^ 2) = G / L := by
  have hL : 0 < L := hG.trans hGL
  obtain ⟨-, -, hpos⟩ := eccOf_data hG hGL
  have hsq : eccOf L G ^ 2 = 1 - G ^ 2 / L ^ 2 := Real.sq_sqrt hpos.le
  have : 1 - eccOf L G ^ 2 = (G / L) ^ 2 := by rw [hsq, div_pow]; ring
  rw [this]
  exact Real.sqrt_sq (by positivity)

/-- The six brackets of the Delaunay columns (`G = L √(1 - e²)`). -/
private theorem delaunay_brackets {ℓ g L G e : ℝ} (hL : 0 < L) (he0 : 0 < e) (he1 : e < 1)
    (hG : G = L * √(1 - e ^ 2)) :
    symplecticForm (orbitMapColumn ℓ g L e 0) (orbitMapColumn ℓ g L e 1) = 0 ∧
    symplecticForm (orbitMapColumn ℓ g L e 0)
      (orbitMapColumn ℓ g L e 2 + (G ^ 2 / (L ^ 3 * e)) • orbitMapColumn ℓ g L e 3) = -1 ∧
    symplecticForm (orbitMapColumn ℓ g L e 0) ((-G / (L ^ 2 * e)) • orbitMapColumn ℓ g L e 3)
      = 0 ∧
    symplecticForm (orbitMapColumn ℓ g L e 1)
      (orbitMapColumn ℓ g L e 2 + (G ^ 2 / (L ^ 3 * e)) • orbitMapColumn ℓ g L e 3) = 0 ∧
    symplecticForm (orbitMapColumn ℓ g L e 1) ((-G / (L ^ 2 * e)) • orbitMapColumn ℓ g L e 3)
      = -1 ∧
    symplecticForm (orbitMapColumn ℓ g L e 2 + (G ^ 2 / (L ^ 3 * e)) • orbitMapColumn ℓ g L e 3)
      ((-G / (L ^ 2 * e)) • orbitMapColumn ℓ g L e 3) = 0 := by
  have hk : 0 < √(1 - e ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hk0 : √(1 - e ^ 2) ≠ 0 := hk.ne'
  have hL0 : L ≠ 0 := hL.ne'
  have he00 : e ≠ 0 := he0.ne'
  have c01 := col_br01 (ℓ := ℓ) (g := g) hL he0.le he1
  have c02 := col_br02 (ℓ := ℓ) (g := g) hL he0.le he1
  have c03 := col_br03 (ℓ := ℓ) (g := g) hL he0.le he1
  have c12 := col_br12 (ℓ := ℓ) (g := g) hL he0.le he1
  have c13 := col_br13 (ℓ := ℓ) (g := g) hL he0.le he1
  have c23 := col_br23 (ℓ := ℓ) (g := g) hL he0.le he1
  have c33 := sf_self (orbitMapColumn ℓ g L e 3)
  subst hG
  refine ⟨c01, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sf_add_right, sf_smul_right, c02, c03]; ring
  · rw [sf_smul_right, c03]; ring
  · rw [sf_add_right, sf_smul_right, c12, c13]; field_simp; ring
  · rw [sf_smul_right, c13]; field_simp
  · rw [sf_smul_right, sf_add_left, sf_smul_left, c23, c33]; ring

/-- `bpI:p7:symplectic`: `𝖰^*(Σ dq∧dp) = dℓ∧dL + dg∧dG`, i.e. factor one for the frozen form
(positions `(ℓ, g)`, momenta `(L, G)`), and `D𝖰` is invertible. -/
theorem delaunay_symplectic : IsSymplecticOn 1 delaunay deDom := by
  intro w hw u v
  rw [one_mul]
  have hw' := hw
  obtain ⟨hG, hGL⟩ := hw'
  have hL : 0 < w.2 0 := hG.trans hGL
  obtain ⟨he0, he1, -⟩ := eccOf_data hG hGL
  have hGk : w.2 1 = w.2 0 * √(1 - eccOf (w.2 0) (w.2 1) ^ 2) := by
    rw [eccOf_sqrt hG hGL]; field_simp
  obtain ⟨e0, e1, e2, e3⟩ := fderiv_delaunay_basis hw
  obtain ⟨k01, k02, k03, k12, k13, k23⟩ :=
    delaunay_brackets (ℓ := w.1 0) (g := w.1 1) hL he0 he1 hGk
  refine symp_of_basis (fderiv ℝ delaunay w) ?_ ?_ ?_ ?_ ?_ ?_ u v
  · change symplecticForm (fderiv ℝ delaunay w (Pi.single 0 1, 0))
      (fderiv ℝ delaunay w (Pi.single 1 1, 0)) = 0
    rw [e0, e1]; exact k01
  · change symplecticForm (fderiv ℝ delaunay w (Pi.single 0 1, 0))
      (fderiv ℝ delaunay w (0, Pi.single 0 1)) = -1
    rw [e0, e2]; exact k02
  · change symplecticForm (fderiv ℝ delaunay w (Pi.single 0 1, 0))
      (fderiv ℝ delaunay w (0, Pi.single 1 1)) = 0
    rw [e0, e3]; exact k03
  · change symplecticForm (fderiv ℝ delaunay w (Pi.single 1 1, 0))
      (fderiv ℝ delaunay w (0, Pi.single 0 1)) = 0
    rw [e1, e2]; exact k12
  · change symplecticForm (fderiv ℝ delaunay w (Pi.single 1 1, 0))
      (fderiv ℝ delaunay w (0, Pi.single 1 1)) = -1
    rw [e1, e3]; exact k13
  · change symplecticForm (fderiv ℝ delaunay w (0, Pi.single 0 1))
      (fderiv ℝ delaunay w (0, Pi.single 1 1)) = 0
    rw [e2, e3]; exact k23

end DelaunayLevel

section Liouville

/-- The Liouville primitive (`bpI:p7:symplectic`): `𝖰^*(Σ p dq) = L dℓ + G dg + dF`,
    `F = 2 L e sin u`. -/
def delaunayGen (w : Phase 2) : ℝ :=
  2 * w.2 0 * eccOf (w.2 0) (w.2 1) * Real.sin (eccAnom (w.1 0) (eccOf (w.2 0) (w.2 1)))

/-- `∂_ℓ (2 L e sin u) = 2 L e cos u / D`. -/
private def genDℓ (ℓ L e : ℝ) : ℝ :=
  2 * L * e * Real.cos (eccAnom ℓ e) / (1 - e * Real.cos (eccAnom ℓ e))

/-- `∂_L (2 L e sin u) = 2 e sin u`. -/
private def genDL (ℓ _L e : ℝ) : ℝ := 2 * e * Real.sin (eccAnom ℓ e)

/-- `∂_e (2 L e sin u) = 2 L sin u + 2 L e cos u sin u / D` (total, through `u`). -/
private def genDe (ℓ L e : ℝ) : ℝ :=
  2 * L * Real.sin (eccAnom ℓ e) + 2 * L * e * Real.cos (eccAnom ℓ e) * Real.sin (eccAnom ℓ e) /
    (1 - e * Real.cos (eccAnom ℓ e))

private theorem one_sub_mul_cos_pos_abs {e : ℝ} (u : ℝ) (h : |e| < 1) : 0 < 1 - e * Real.cos u := by
  have h1 := mul_nonneg (abs_nonneg e) (sub_nonneg.2 (abs_cos_le_one u))
  have h2 := abs_mul e (Real.cos u)
  have h3 := le_abs_self (e * Real.cos u)
  nlinarith

private theorem hasDerivAt_gen_curve {ℓ L e : ℝ → ℝ} {ℓ' L' e' t : ℝ} (hℓ : HasDerivAt ℓ ℓ' t)
    (hL : HasDerivAt L L' t) (he : HasDerivAt e e' t) (h : |e t| < 1) :
    HasDerivAt (fun s => 2 * L s * e s * Real.sin (eccAnom (ℓ s) (e s)))
      (ℓ' * genDℓ (ℓ t) (L t) (e t) + L' * genDL (ℓ t) (L t) (e t)
        + e' * genDe (ℓ t) (L t) (e t)) t := by
  have hu := hasDerivAt_eccAnom_curve hℓ he h
  have hD := (one_sub_mul_cos_pos_abs (eccAnom (ℓ t) (e t)) h).ne'
  refine (((hL.const_mul 2).mul he).mul hu.sin).congr_deriv ?_
  simp only [genDℓ, genDL, genDe, Pi.mul_apply]
  field_simp
  ring

private theorem hasDerivAt_gen_line {w : Phase 2} (hw : w ∈ deDom) (a _b c d E : ℝ)
    (hE : E = (w.2 1 ^ 2 * c / w.2 0 ^ 3 - w.2 1 * d / w.2 0 ^ 2) / eccOf (w.2 0) (w.2 1)) :
    HasDerivAt (fun t : ℝ => 2 * (w.2 0 + t * c) * eccOf (w.2 0 + t * c) (w.2 1 + t * d) *
        Real.sin (eccAnom (w.1 0 + t * a) (eccOf (w.2 0 + t * c) (w.2 1 + t * d))))
      (a * genDℓ (w.1 0) (w.2 0) (eccOf (w.2 0) (w.2 1))
        + c * genDL (w.1 0) (w.2 0) (eccOf (w.2 0) (w.2 1))
        + E * genDe (w.1 0) (w.2 0) (eccOf (w.2 0) (w.2 1))) 0 := by
  obtain ⟨hG, hGL⟩ := hw
  obtain ⟨he0, he1, -⟩ := eccOf_data hG hGL
  have hc : ∀ x y : ℝ, HasDerivAt (fun s : ℝ => x + s * y) y 0 := fun x y => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const y).const_add x
  have he := hasDerivAt_eccOf_line (L := w.2 0) (G := w.2 1) c d hG hGL
  have habs : |eccOf (w.2 0) (w.2 1)| < 1 := by rw [abs_lt]; constructor <;> linarith
  have := hasDerivAt_gen_curve (hc (w.1 0) a) (hc (w.2 0) c) he (by simpa using habs)
  rw [hE]
  simpa using this

private theorem differentiableAt_delaunayGen {w : Phase 2} (hw : w ∈ deDom) :
    DifferentiableAt ℝ delaunayGen w := by
  obtain ⟨hG, hGL⟩ := hw
  have hL : 0 < w.2 0 := hG.trans hGL
  obtain ⟨he0, he1, hpos⟩ := eccOf_data hG hGL
  have p1 : ∀ i : Fin 2, AnalyticAt ℝ (fun w : Phase 2 => w.1 i) w := fun i =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
      (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))).analyticAt w
  have p2 : ∀ i : Fin 2, AnalyticAt ℝ (fun w : Phase 2 => w.2 i) w := fun i =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
      (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))).analyticAt w
  have hL2 : w.2 0 ^ 2 ≠ 0 := by positivity
  have hecc : AnalyticAt ℝ (fun w : Phase 2 => eccOf (w.2 0) (w.2 1)) w := by
    unfold eccOf
    exact ((analyticAt_const.sub (((p2 1).pow 2).div ((p2 0).pow 2) hL2)).contDiffAt.sqrt
      hpos.ne').analyticAt
  have hx : |eccOf (w.2 0) (w.2 1)| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hu : AnalyticAt ℝ (fun w : Phase 2 => eccAnom (w.1 0) (eccOf (w.2 0) (w.2 1))) w :=
    AnalyticAt.comp (g := fun p : ℝ × ℝ => eccAnom p.1 p.2)
      (f := fun w : Phase 2 => ((w.1 0, eccOf (w.2 0) (w.2 1)) : ℝ × ℝ))
      (analyticOnNhd_eccAnom ((w.1 0, eccOf (w.2 0) (w.2 1)) : ℝ × ℝ) hx) ((p1 0).prod hecc)
  exact (((analyticAt_const.mul (p2 0)).mul hecc).mul (Real.analyticAt_sin.comp
      hu)).differentiableAt

private theorem fderiv_delaunayGen_basis {w : Phase 2} (hw : w ∈ deDom) :
    fderiv ℝ delaunayGen w b0 = genDℓ (w.1 0) (w.2 0) (eccOf (w.2 0) (w.2 1)) ∧
    fderiv ℝ delaunayGen w b1 = 0 ∧
    fderiv ℝ delaunayGen w b2 = genDL (w.1 0) (w.2 0) (eccOf (w.2 0) (w.2 1))
      + (w.2 1 ^ 2 / (w.2 0 ^ 3 * eccOf (w.2 0) (w.2 1)))
        * genDe (w.1 0) (w.2 0) (eccOf (w.2 0) (w.2 1)) ∧
    fderiv ℝ delaunayGen w b3 = (-w.2 1 / (w.2 0 ^ 2 * eccOf (w.2 0) (w.2 1)))
      * genDe (w.1 0) (w.2 0) (eccOf (w.2 0) (w.2 1)) := by
  have hd := differentiableAt_delaunayGen hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine fderiv_apply_eq_of_hasDerivAt_line hd ?_
    simpa [delaunayGen, b0] using hasDerivAt_gen_line hw 1 0 0 0 0 (by simp)
  · refine fderiv_apply_eq_of_hasDerivAt_line hd ?_
    simpa [delaunayGen, b1] using hasDerivAt_gen_line hw 0 1 0 0 0 (by simp)
  · refine fderiv_apply_eq_of_hasDerivAt_line hd ?_
    simpa [delaunayGen, b2] using
      hasDerivAt_gen_line hw 0 0 1 0 (w.2 1 ^ 2 / (w.2 0 ^ 3 * eccOf (w.2 0) (w.2 1))) (by ring)
  · refine fderiv_apply_eq_of_hasDerivAt_line hd ?_
    simpa [delaunayGen, b3] using
      hasDerivAt_gen_line hw 0 0 0 1 (-w.2 1 / (w.2 0 ^ 2 * eccOf (w.2 0) (w.2 1))) (by ring)

/-- The Liouville identities on the four columns (`p = (orbitMapR ℓ g L e).2`). -/
private theorem lv_col {ℓ g L e : ℝ} (hL : 0 < L) (he0 : 0 ≤ e) (he1 : e < 1) :
    planeDot (orbitMapR ℓ g L e).2 (orbitMapColumn ℓ g L e 0).1 = L + genDℓ ℓ L e ∧
    planeDot (orbitMapR ℓ g L e).2 (orbitMapColumn ℓ g L e 1).1 = L * √(1 - e ^ 2) ∧
    planeDot (orbitMapR ℓ g L e).2 (orbitMapColumn ℓ g L e 2).1 = genDL ℓ L e ∧
    planeDot (orbitMapR ℓ g L e).2 (orbitMapColumn ℓ g L e 3).1 = genDe ℓ L e := by
  obtain ⟨hD, hk0, hs, hk⟩ := col_hyps (eccAnom ℓ e) he0 he1
  have hP : ∀ x : Fin 2 → ℝ, planeDot (orbitMapR ℓ g L e).2 (rot g x) =
      planeDot (orbitFrame L e (eccAnom ℓ e)).2 x := fun x => planeDot_rot g _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [orbitMapColumn_eq0]
    show planeDot (orbitMapR ℓ g L e).2 (rot g _) = _
    rw [hP]
    simp only [orbitFrame, colF0, genDℓ, planeDot, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
    linear_combination lv0 L e _ _ _ _ hD hk0 hL.ne' hs hk rfl
  · rw [orbitMapColumn_eq1]
    show planeDot (orbitMapR ℓ g L e).2 (rot g _) = _
    rw [hP]
    simp only [orbitFrame, colF1, quarterTurn, planeDot, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    linear_combination lv1 L e _ _ _ _ hD hk0 hL.ne' hs hk rfl
  · rw [orbitMapColumn_eq2]
    show planeDot (orbitMapR ℓ g L e).2 (rot g _) = _
    rw [hP]
    simp only [orbitFrame, colF2, genDL, planeDot, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    linear_combination lv2 L e _ _ _ _ hD hk0 hL.ne' hs hk rfl
  · rw [orbitMapColumn_eq3]
    show planeDot (orbitMapR ℓ g L e).2 (rot g _) = _
    rw [hP]
    simp only [orbitFrame, colF3, genDe, planeDot, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    linear_combination lv3 L e _ _ _ _ hD hk0 hL.ne' hs hk rfl

/-- Liouville primitive: `p · dq = L dℓ + G dg + dF` for `F = delaunayGen`. -/
theorem delaunay_liouville {w : Phase 2} (hw : w ∈ deDom) (u : Phase 2) :
    planeDot (delaunay w).2 (fderiv ℝ delaunay w u).1 =
      w.2 0 * u.1 0 + w.2 1 * u.1 1 + fderiv ℝ delaunayGen w u := by
  have hw' := hw
  obtain ⟨hG, hGL⟩ := hw'
  have hL : 0 < w.2 0 := hG.trans hGL
  obtain ⟨he0, he1, -⟩ := eccOf_data hG hGL
  have hGk : w.2 1 = w.2 0 * √(1 - eccOf (w.2 0) (w.2 1) ^ 2) := by
    rw [eccOf_sqrt hG hGL]; field_simp
  obtain ⟨e0, e1, e2, e3⟩ := fderiv_delaunay_basis hw
  obtain ⟨g0, g1, g2, g3⟩ := fderiv_delaunayGen_basis hw
  obtain ⟨l0, l1, l2, l3⟩ := lv_col (ℓ := w.1 0) (g := w.1 1) hL he0.le he1
  have hp : (delaunay w).2 = (orbitMapR (w.1 0) (w.1 1) (w.2 0) (eccOf (w.2 0) (w.2 1))).2 := rfl
  have I0 : planeDot (delaunay w).2 (fderiv ℝ delaunay w b0).1 =
      w.2 0 + genDℓ (w.1 0) (w.2 0) (eccOf (w.2 0) (w.2 1)) := by
    change planeDot (delaunay w).2 (fderiv ℝ delaunay w (Pi.single 0 1, 0)).1 = _
    rw [e0, hp]; exact l0
  have I1 : planeDot (delaunay w).2 (fderiv ℝ delaunay w b1).1 = w.2 1 := by
    change planeDot (delaunay w).2 (fderiv ℝ delaunay w (Pi.single 1 1, 0)).1 = _
    rw [e1, hp, l1]; exact hGk.symm
  have I2 : planeDot (delaunay w).2 (fderiv ℝ delaunay w b2).1 =
      genDL (w.1 0) (w.2 0) (eccOf (w.2 0) (w.2 1))
      + (w.2 1 ^ 2 / (w.2 0 ^ 3 * eccOf (w.2 0) (w.2 1)))
        * genDe (w.1 0) (w.2 0) (eccOf (w.2 0) (w.2 1)) := by
    change planeDot (delaunay w).2 (fderiv ℝ delaunay w (0, Pi.single 0 1)).1 = _
    rw [e2, hp, Prod.fst_add, Prod.smul_fst, planeDot_add_right, planeDot_smul_right, l2, l3]
  have I3 : planeDot (delaunay w).2 (fderiv ℝ delaunay w b3).1 =
      (-w.2 1 / (w.2 0 ^ 2 * eccOf (w.2 0) (w.2 1)))
        * genDe (w.1 0) (w.2 0) (eccOf (w.2 0) (w.2 1)) := by
    change planeDot (delaunay w).2 (fderiv ℝ delaunay w (0, Pi.single 1 1)).1 = _
    rw [e3, hp, Prod.smul_fst, planeDot_smul_right, l3]
  rw [clm_decomp (fderiv ℝ delaunay w) u, clm_decomp (fderiv ℝ delaunayGen w) u]
  simp only [Prod.fst_add, Prod.smul_fst, planeDot_add_right, planeDot_smul_right, smul_eq_mul]
  rw [I0, I1, I2, I3, g0, g1, g2, g3]
  ring

end Liouville

section Invertibility

/-- Explicit Jacobian columns, in the intermediate variables (helper for the proof; the symplectic
identity is then six rational identities). -/
theorem delaunay_hasFDerivAt {w : Phase 2} (hw : w ∈ deDom) :
    HasFDerivAt delaunay (fderiv ℝ delaunay w) w :=
  (analyticOnNhd_delaunay w hw).differentiableAt.hasFDerivAt

/-- `D𝖰` is invertible on `deDom`: a symplectic endomorphism of the finite-dimensional space
`Phase 2` is injective (the symplectic form is nondegenerate), hence bijective. -/
theorem delaunay_fderiv_equiv {w : Phase 2} (hw : w ∈ deDom) :
    ∃ A : Phase 2 ≃L[ℝ] Phase 2, (A : Phase 2 →L[ℝ] Phase 2) = fderiv ℝ delaunay w := by
  have hs := delaunay_symplectic w hw
  set A := fderiv ℝ delaunay w with hA
  have hker : LinearMap.ker (A : Phase 2 →ₗ[ℝ] Phase 2) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    refine eq_zero_of_sf_eq_zero fun v => ?_
    have := hs u v
    rw [one_mul] at this
    rw [← this]
    have hu' : A u = 0 := hu
    rw [hu']
    simp [sf_eq]
  have hinj : Function.Injective (A : Phase 2 →ₗ[ℝ] Phase 2) := LinearMap.ker_eq_bot.1 hker
  have hsurj : Function.Surjective (A : Phase 2 →ₗ[ℝ] Phase 2) :=
    LinearMap.injective_iff_surjective.1 hinj
  refine ⟨ContinuousLinearEquiv.ofBijective A hker ?_, ?_⟩
  · exact LinearMap.range_eq_top.2 hsurj
  · exact ContinuousLinearMap.ext fun z => rfl

end Invertibility

section HamiltonianField

/-- `dH(z) v = Ω(v, X_H(z))`. -/
private theorem fderiv_eq_sf (H : Phase 2 → ℝ) (z v : Phase 2) :
    fderiv ℝ H z v = symplecticForm v (hamiltonianVectorField H z) := by
  rw [clm_decomp (fderiv ℝ H z) v, sf_eq]
  simp only [hamiltonianVectorField, b0, b1, b2, b3]
  simp
  ring

/-- C6: the Hamiltonian-field consequence of symplecticity (`D𝖰 X_{H∘𝖰} = X_H ∘ 𝖰`). -/
theorem delaunay_hamiltonianVectorField {H : Phase 2 → ℝ} {w : Phase 2} (hw : w ∈ deDom)
    (hH : DifferentiableAt ℝ H (delaunay w)) :
    fderiv ℝ delaunay w (hamiltonianVectorField (H ∘ delaunay) w) =
      hamiltonianVectorField H (delaunay w) := by
  obtain ⟨A, hA⟩ := delaunay_fderiv_equiv hw
  have hs := delaunay_symplectic w hw
  have hd : DifferentiableAt ℝ delaunay w := (analyticOnNhd_delaunay w hw).differentiableAt
  have hcomp : fderiv ℝ (H ∘ delaunay) w = (fderiv ℝ H (delaunay w)).comp (fderiv ℝ delaunay w) :=
    fderiv_comp w hH hd
  have hAv : ∀ v, fderiv ℝ delaunay w v = A v := fun v => by rw [← hA]; rfl
  have key : ∀ v, symplecticForm (A v) (fderiv ℝ delaunay w
      (hamiltonianVectorField (H ∘ delaunay) w) - hamiltonianVectorField H (delaunay w)) = 0 := by
    intro v
    rw [sf_sub_right]
    have h1 := hs v (hamiltonianVectorField (H ∘ delaunay) w)
    have h2 := fderiv_eq_sf (H ∘ delaunay) w v
    have h3 := fderiv_eq_sf H (delaunay w) (fderiv ℝ delaunay w v)
    rw [hcomp, ContinuousLinearMap.comp_apply] at h2
    simp only [hAv] at h1 h2 h3 ⊢
    rw [one_mul] at h1
    linarith
  refine sub_eq_zero.1 (eq_zero_of_sf_eq_zero fun a => ?_)
  obtain ⟨v, rfl⟩ := A.surjective a
  rw [sf_comm, hAv]
  have := key v
  rw [hAv] at this
  rw [this]
  simp

end HamiltonianField


end KAM.Kepler

end
