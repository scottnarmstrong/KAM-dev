/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import KAM.Frozen.Wave.Defs.Coeff
public import KAM.Frozen.Wave.Defs.EllWeight
public import KAM.Frozen.Wave.Defs.WaveSpace

/-!
# Weighted spaces as transports of `ℓ²` (blueprint-W `bpW:w1:transport`, `bpW:w1:space`)

Off-frontier, source-faithful infrastructure; the dependency graph is still being built.

Every weighted space `ℓ^{a,p}_𝕜` is the image of `lp (fun _ : ℕ+ => 𝕜) 2` under the coefficient map
`coeffW a p` (the blueprint's `κ_{a,p}`), with inverse `tauLp` (`τ_{a,p}`) defined on the sequences
satisfying `IsEll`. No new normed type is introduced.

* `coeffW`: `κ_{a,p} y = (y_j / ω_{a,p}(j))_j`; `coeffW 1 1 = coeff` on real sequences.
* `IsEll`, `ellNormSq`, `ellNorm`, `tauLp`: the space `ℓ^{a,p}` and the map `τ_{a,p}`.
* `bpW:w1:space` (i): `tauLp_coeffW`, `coeffW_tauLp`, `norm_tauLp_sq`, `ellNorm_coeffW`,
  `inner_tauLp`.
* (ii): `norm_coeffW_le`, `coeffWCLM`. (iii): `truncLp`, `tendsto_norm_sub_truncLp`.
* (iv): `coeffW_one_one`, `norm_prod_eq_max_ellNorm`.
-/

@[expose] public noncomputable section

open Filter Topology ENNReal

namespace KAM.Wave

variable {K : Type*} [RCLike K]

/-- The weight `ω_{a,p}(j) = j^p e^{aj}` is strictly positive. -/
theorem ellWeight_pos (a p : ℝ) (j : ℕ+) : 0 < ellWeight a p j := by
  unfold ellWeight
  exact mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast j.pos) _) (Real.exp_pos _)

theorem ellWeight_ne_zero (a p : ℝ) (j : ℕ+) : ellWeight a p j ≠ 0 :=
  (ellWeight_pos a p j).ne'

theorem ellWeight_cast_ne_zero (a p : ℝ) (j : ℕ+) : (ellWeight a p j : K) ≠ 0 := by
  exact_mod_cast ellWeight_ne_zero a p j

theorem norm_ellWeight_cast (a p : ℝ) (j : ℕ+) : ‖(ellWeight a p j : K)‖ = ellWeight a p j := by
  rw [RCLike.norm_ofReal, abs_of_pos (ellWeight_pos a p j)]

/-- `‖f‖² = ∑ ‖f_i‖²` in `ℓ²`. -/
theorem lp_two_hasSum_sq {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    (f : lp E 2) : HasSum (fun i => ‖f i‖ ^ 2) (‖f‖ ^ 2) := by
  have := lp.hasSum_norm (p := 2) (by norm_num) f
  simpa [Real.rpow_two] using this

/-- **Coefficient map** `κ_{a,p}` (blueprint `bpW:w1:transport`):
`(κ_{a,p} y)_j = y_j / ω_{a,p}(j)`.
`coeffW 1 1 = coeff` on real sequences (`coeffW_one_one`). -/
def coeffW (a p : ℝ) (y : lp (fun _ : ℕ+ => K) 2) (j : ℕ+) : K :=
  y j / (ellWeight a p j : K)

/-- Membership in `ℓ^{a,p}_𝕜` (blueprint `bpW:w0:ellap`): `ω_{a,p} · w ∈ ℓ²`. -/
def IsEll (a p : ℝ) (w : ℕ+ → K) : Prop :=
  Memℓp (fun j => (ellWeight a p j : K) * w j) 2

/-- The squared weighted norm `‖w‖²_{a,p} = ∑ (ω_{a,p}(j) |w_j|)²`. -/
def ellNormSq (a p : ℝ) (w : ℕ+ → K) : ℝ :=
  ∑' j : ℕ+, (ellWeight a p j * ‖w j‖) ^ 2

/-- The weighted norm `‖w‖_{a,p}`. -/
def ellNorm (a p : ℝ) (w : ℕ+ → K) : ℝ :=
  Real.sqrt (ellNormSq a p w)

/-- **Transport map** `τ_{a,p}` (blueprint `bpW:w1:transport`): `(τ_{a,p} w)_j = ω_{a,p}(j) w_j`. -/
def tauLp (a p : ℝ) (w : ℕ+ → K) (h : IsEll a p w) : lp (fun _ : ℕ+ => K) 2 :=
  ⟨fun j => (ellWeight a p j : K) * w j, h⟩

@[simp] theorem tauLp_apply (a p : ℝ) (w : ℕ+ → K) (h : IsEll a p w) (j : ℕ+) :
    tauLp a p w h j = (ellWeight a p j : K) * w j := rfl

@[simp] theorem coeffW_apply (a p : ℝ) (y : lp (fun _ : ℕ+ => K) 2) (j : ℕ+) :
    coeffW a p y j = y j / (ellWeight a p j : K) := rfl

/-- `κ_{a,p} y ∈ ℓ^{a,p}`. -/
theorem isEll_coeffW (a p : ℝ) (y : lp (fun _ : ℕ+ => K) 2) : IsEll a p (coeffW a p y) := by
  have : (fun j => (ellWeight a p j : K) * coeffW a p y j) = ⇑y := by
    funext j
    have := ellWeight_cast_ne_zero (K := K) a p j
    simp [coeffW, mul_div_cancel₀ _ this]
  unfold IsEll
  rw [this]
  exact y.2

/-- `bpW:w1:space` (i): `τ ∘ κ = id`. -/
theorem tauLp_coeffW (a p : ℝ) (y : lp (fun _ : ℕ+ => K) 2) :
    tauLp a p (coeffW a p y) (isEll_coeffW a p y) = y := by
  ext j
  have := ellWeight_cast_ne_zero (K := K) a p j
  simp [coeffW, mul_div_cancel₀ _ this]

/-- `bpW:w1:space` (i): `κ ∘ τ = id`. -/
theorem coeffW_tauLp (a p : ℝ) (w : ℕ+ → K) (h : IsEll a p w) :
    coeffW a p (tauLp a p w h) = w := by
  funext j
  have := ellWeight_cast_ne_zero (K := K) a p j
  simp [coeffW, mul_div_cancel_left₀ _ this]

theorem coeffW_injective (a p : ℝ) :
    Function.Injective (coeffW (K := K) a p) := fun y y' h => by
  rw [← tauLp_coeffW a p y, ← tauLp_coeffW a p y']
  simp only [h]

@[simp] theorem coeffW_add (a p : ℝ) (y y' : lp (fun _ : ℕ+ => K) 2) :
    coeffW a p (y + y') = coeffW a p y + coeffW a p y' := by
  funext j; simp [coeffW, add_div]

@[simp] theorem coeffW_smul (a p : ℝ) (c : K) (y : lp (fun _ : ℕ+ => K) 2) :
    coeffW a p (c • y) = c • coeffW a p y := by
  funext j; simp [coeffW, mul_div_assoc]

@[simp] theorem coeffW_neg (a p : ℝ) (y : lp (fun _ : ℕ+ => K) 2) :
    coeffW a p (-y) = -coeffW a p y := by
  funext j; simp [coeffW, neg_div]

@[simp] theorem coeffW_sub (a p : ℝ) (y y' : lp (fun _ : ℕ+ => K) 2) :
    coeffW a p (y - y') = coeffW a p y - coeffW a p y' := by
  funext j; simp [coeffW, sub_div]

/-- `κ_{a,p}` as a `𝕜`-linear map into sequences (`bpW:w1:space` (i)). -/
def coeffWLinear (a p : ℝ) : lp (fun _ : ℕ+ => K) 2 →ₗ[K] (ℕ+ → K) where
  toFun := coeffW a p
  map_add' := coeffW_add a p
  map_smul' := coeffW_smul a p

/-- `bpW:w1:space` (i): `‖τ_{a,p} w‖² = ‖w‖²_{a,p}`. -/
theorem norm_tauLp_sq (a p : ℝ) (w : ℕ+ → K) (h : IsEll a p w) :
    ‖tauLp a p w h‖ ^ 2 = ellNormSq a p w := by
  refine (lp_two_hasSum_sq (tauLp a p w h)).unique ?_
  have : (fun j => ‖tauLp a p w h j‖ ^ 2) = fun j => (ellWeight a p j * ‖w j‖) ^ 2 := by
    funext j; rw [tauLp_apply, norm_mul, norm_ellWeight_cast]
  rw [this]
  unfold ellNormSq
  refine Summable.hasSum ?_
  have hs := (lp_two_hasSum_sq (tauLp a p w h)).summable
  rwa [this] at hs

/-- `bpW:w1:space` (i): `‖κ_{a,p} y‖_{a,p} = ‖y‖`. -/
theorem ellNorm_coeffW (a p : ℝ) (y : lp (fun _ : ℕ+ => K) 2) :
    ellNorm a p (coeffW a p y) = ‖y‖ := by
  have := norm_tauLp_sq a p _ (isEll_coeffW a p y)
  rw [tauLp_coeffW] at this
  rw [ellNorm, ← this, Real.sqrt_sq (norm_nonneg _)]

/-- `bpW:w1:space` (i): the transported inner product
`⟨τ w, τ w'⟩ = ∑ ω_{a,p}(j)² conj(w_j) w'_j`. -/
theorem inner_tauLp (a p : ℝ) (w w' : ℕ+ → K) (h : IsEll a p w) (h' : IsEll a p w') :
    inner K (tauLp a p w h) (tauLp a p w' h') =
      ∑' j : ℕ+, ((ellWeight a p j : K) ^ 2) * (w' j * (starRingEnd K) (w j)) := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun j => ?_
  simp only [tauLp_apply, RCLike.inner_apply, map_mul, RCLike.conj_ofReal]
  ring

/-- `bpW:w1:space` (ii): `|(κ_{a,p} y)_j| ≤ ‖y‖ / ω_{a,p}(j)`. -/
theorem norm_coeffW_le (a p : ℝ) (y : lp (fun _ : ℕ+ => K) 2) (j : ℕ+) :
    ‖coeffW a p y j‖ ≤ ‖y‖ / ellWeight a p j := by
  rw [coeffW_apply, norm_div, norm_ellWeight_cast]
  exact div_le_div_of_nonneg_right (lp.norm_apply_le_norm (by norm_num) y j)
    (ellWeight_pos a p j).le

/-- `bpW:w1:space` (ii): `y ↦ (κ_{a,p} y)_j` is the continuous linear functional
`ω_{a,p}(j)⁻¹ ev_j`. -/
def coeffWCLM (a p : ℝ) (j : ℕ+) : lp (fun _ : ℕ+ => K) 2 →L[K] K :=
  ((ellWeight a p j : K)⁻¹) • lp.evalCLM K (E := fun _ : ℕ+ => K) (p := 2) j

@[simp] theorem coeffWCLM_apply (a p : ℝ) (j : ℕ+) (y : lp (fun _ : ℕ+ => K) 2) :
    coeffWCLM a p j y = coeffW a p y j := by
  simp only [coeffWCLM, smul_apply, coeffW_apply, div_eq_inv_mul]
  rfl

/-- The finite truncation `P_N y = ∑_{j ≤ N} y_j e_j` (blueprint `bpW:w1:space` (iii)). -/
def truncLp (N : ℕ) (y : lp (fun _ : ℕ+ => K) 2) : lp (fun _ : ℕ+ => K) 2 :=
  ∑ j ∈ Finset.image Nat.succPNat (Finset.range N), lp.single 2 j (y j)

/-- `bpW:w1:space` (iii): `‖y - P_N y‖ → 0` as `N → ∞`. -/
theorem tendsto_norm_sub_truncLp (y : lp (fun _ : ℕ+ => K) 2) :
    Tendsto (fun N : ℕ => ‖y - truncLp N y‖) atTop (𝓝 0) := by
  have h := (lp.hasSum_single (E := fun _ : ℕ+ => K) (p := 2) (by simp) y)
  have h2 : Tendsto (fun N : ℕ => truncLp N y) atTop (𝓝 y) :=
    h.comp (tendsto_atTop_finset_of_monotone
      (fun _ _ hab => Finset.image_subset_image (Finset.range_mono hab))
      (fun j => ⟨(j : ℕ), Finset.mem_image.2
        ⟨j.natPred, by simp [PNat.natPred, Nat.sub_lt j.pos], PNat.succPNat_natPred j⟩⟩))
  have := (tendsto_const_nhds (x := y)).sub h2
  rw [sub_self] at this
  have h3 := (continuous_norm.tendsto (0 : lp (fun _ : ℕ+ => K) 2)).comp this
  rwa [norm_zero] at h3

/-- `bpW:w1:space` (iv): `κ_{1,1} = coeff`. -/
theorem coeffW_one_one (y : lp (fun _ : ℕ+ => ℝ) 2) : coeffW 1 1 y = coeff y := by
  funext j
  simp [coeffW, coeff]

/-- `bpW:w1:space` (iv): the norm of the frozen `WaveSpace` is `max (‖q‖_{1,1}, ‖p‖_{1,1})`,
`q = coeff y`, `p = coeff y'`. -/
theorem norm_prod_eq_max_ellNorm (z : WaveSpace) :
    ‖z‖ = max (ellNorm 1 1 (coeff z.1)) (ellNorm 1 1 (coeff z.2)) := by
  rw [Prod.norm_def, ← coeffW_one_one, ← coeffW_one_one, ellNorm_coeffW, ellNorm_coeffW]

end KAM.Wave

end
