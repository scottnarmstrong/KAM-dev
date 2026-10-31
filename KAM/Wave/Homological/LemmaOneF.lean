/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LemmaOneMult
public import KAM.Wave.Homological.SolveImage
public import KAM.Wave.Homological.Taylor
public import KAM.Wave.Homological.AngleSupport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The solution `F` of Theorem `bpW:w4:lemma1`: construction and membership in `𝒯_{s-σ}`
(`bpW:w4:lemma1` (i), steps *Division operators*, *The solution is in the class*)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

* `HomMultBounds τ α w W`: the bounds of the division operators at one parameter value
  (`homMultBounds_of` derives them from `(H_α)`);
* the multiplier families `homTscal`, `homTvec`, `homTdp`, `homTdm`, `homTP`, `homTP'`, `homTQ`,
  `homTQt` (continuous linear maps) and their norm bounds `κ A_k/α` with `κ = 1` or `K_S`;
* `homSolveTaylor`: for `R ∈ 𝒯_s` the Taylor Hamiltonian `F ∈ 𝒯_{s-σ}` whose components are the
  solves of the components of `R` (`F.a0 = homSolve (homTscal w) R.a0`, …).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- The bounds of the division operators at one parameter value (`bpW:w4:lemma1`, step *Division
operators*). -/
structure HomMultBounds (τ α : ℝ) (w : Fin 2 → ℝ) (W : ℕ+ → ℝ) : Prop where
  a0 : ∀ k, ‖homMultA0 w k‖ ≤ 1 * waveA τ k / α
  dp : ∀ k j, ‖homMultDp w W k j‖ ≤ 1 * waveA τ k / α
  dm : ∀ k j, ‖homMultDm w W k j‖ ≤ 1 * waveA τ k / α
  P : ∀ k, HomHadamardBound (homDP w W k) (waveA τ k / α)
  P' : ∀ k, HomHadamardBound (homDP' w W k) (waveA τ k / α)
  Q : ∀ k, HomHadamardBound (homDQ w W k) (waveA τ k / α)
  Qt : ∀ k, HomHadamardBound (homDQt w W k) (waveA τ k / α)
  nz0 : ∀ k, k ≠ 0 → homDelta0 w k ≠ 0
  nzp : ∀ k j, homDeltaPlus w W k j ≠ 0
  nzm : ∀ k j, homDeltaMinus w W k j ≠ 0
  nzP : ∀ k i j, homDeltaP w W k i j ≠ 0
  nzP' : ∀ k i j, homDeltaP' w W k i j ≠ 0
  nzQ : ∀ k i j, (k ≠ 0 ∨ i ≠ j) → homDeltaQ w W k i j ≠ 0

theorem ne_zero_of_divisorBound {Par : Set (Fin 2 → ℝ)} {Mω MΩ τ α : ℝ} {k : Fin 2 → ℤ}
    {wt : ℝ} {δ : (Fin 2 → ℝ) → ℝ} (hα : 0 < α) (hw : 0 < wt)
    (hb : HomDivisorBound τ α Mω MΩ Par k wt δ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) : δ ξ ≠ 0 := by
  intro h0
  have h1 := hb.1 ξ hξ
  rw [h0, abs_zero] at h1
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  have : 0 < α * wt / waveA τ k := by positivity
  linarith

theorem homMultBounds_of {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {M0 Mω MΩ τ α : ℝ} (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hα : 0 < α) (hH : HomMelnikov τ α Par ω Ω) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    HomMultBounds τ α (ω ξ) (Ω ξ) :=
  ⟨norm_homMultA0_le h hα hH hξ, norm_homMultDp_le h hα hH hξ, norm_homMultDm_le h hα hH hξ,
    homDP_bound h hα hH hξ, homDP'_bound h hα hH hξ, homDQ_bound h hα hH hξ,
    homDQt_bound h hα hH hξ,
    fun k hk => ne_zero_of_divisorBound hα one_pos (homDelta0_bound h hα hH hk) hξ,
    fun k j => ne_zero_of_divisorBound hα (by exact_mod_cast j.pos) (homDeltaPlus_bound h hα hH k j) hξ,
    fun k j => ne_zero_of_divisorBound hα (by exact_mod_cast j.pos) (homDeltaMinus_bound h hα hH k j) hξ,
    fun k i j => ne_zero_of_divisorBound hα (by have := i.pos; have := j.pos; positivity)
      (homDeltaP_bound h hα hH k i j) hξ,
    fun k i j => ne_zero_of_divisorBound hα (by have := i.pos; have := j.pos; positivity)
      (homDeltaP'_bound h hα hH k i j) hξ,
    fun k i j hkij => ne_zero_of_divisorBound hα
      (by exact_mod_cast one_le_homWeightQ i j) (homDeltaQ_bound h hα hH hkij) hξ⟩

variable {τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ}

/-- The scalar multiplier `m_k • id`. -/
def homTscal (w : Fin 2 → ℝ) (k : Fin 2 → ℤ) : ℂ →L[ℂ] ℂ :=
  homMultA0 w k • ContinuousLinearMap.id ℂ ℂ

/-- The multiplier of `b`. -/
def homTvec (w : Fin 2 → ℝ) (k : Fin 2 → ℤ) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  homMultA0 w k • ContinuousLinearMap.id ℂ (Fin 2 → ℂ)

/-- The diagonal multiplier of `c^+`. -/
def homTdp (hm : HomMultBounds τ α w W) (k : Fin 2 → ℤ) : HomOp :=
  weightedDiagCLM (homMultDp w W k) (hm.dp k)

/-- The diagonal multiplier of `c^-`. -/
def homTdm (hm : HomMultBounds τ α w W) (k : Fin 2 → ℤ) : HomOp :=
  weightedDiagCLM (homMultDm w W k) (hm.dm k)

/-- The Hadamard multiplier of `P`. -/
def homTP (hm : HomMultBounds τ α w W) (k : Fin 2 → ℤ) : HomOp →L[ℂ] HomOp :=
  homHadamardCLM (hm.P k)

def homTP' (hm : HomMultBounds τ α w W) (k : Fin 2 → ℤ) : HomOp →L[ℂ] HomOp :=
  homHadamardCLM (hm.P' k)

def homTQ (hm : HomMultBounds τ α w W) (k : Fin 2 → ℤ) : HomOp →L[ℂ] HomOp :=
  homHadamardCLM (hm.Q k)

def homTQt (hm : HomMultBounds τ α w W) (k : Fin 2 → ℤ) : HomOp →L[ℂ] HomOp :=
  homHadamardCLM (hm.Qt k)

theorem norm_homTscal_le (hm : HomMultBounds τ α w W) (k : Fin 2 → ℤ) :
    ‖homTscal w k‖ ≤ 1 * waveA τ k / α :=
  ((norm_smul (homMultA0 w k) (ContinuousLinearMap.id ℂ ℂ)).le.trans
    (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _))).trans
    (by simpa using hm.a0 k)

theorem norm_homTvec_le (hm : HomMultBounds τ α w W) (k : Fin 2 → ℤ) :
    ‖homTvec w k‖ ≤ 1 * waveA τ k / α :=
  ((norm_smul (homMultA0 w k) (ContinuousLinearMap.id ℂ (Fin 2 → ℂ))).le.trans
    (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _))).trans
    (by simpa using hm.a0 k)

theorem norm_homTdp_le (hm : HomMultBounds τ α w W) (k : Fin 2 → ℤ) :
    ‖homTdp hm k‖ ≤ 1 * waveA τ k / α := norm_diagCLM_le _ _

theorem norm_homTdm_le (hm : HomMultBounds τ α w W) (k : Fin 2 → ℤ) :
    ‖homTdm hm k‖ ≤ 1 * waveA τ k / α := norm_diagCLM_le _ _

theorem norm_homTP_le (hm : HomMultBounds τ α w W) (k : Fin 2 → ℤ) :
    ‖homTP hm k‖ ≤ homKS * waveA τ k / α := by
  refine (norm_homHadamardCLM_le (hm.P k)).trans (le_of_eq ?_); ring

theorem norm_homTP'_le (hm : HomMultBounds τ α w W) (k : Fin 2 → ℤ) :
    ‖homTP' hm k‖ ≤ homKS * waveA τ k / α := by
  refine (norm_homHadamardCLM_le (hm.P' k)).trans (le_of_eq ?_); ring

theorem norm_homTQ_le (hm : HomMultBounds τ α w W) (k : Fin 2 → ℤ) :
    ‖homTQ hm k‖ ≤ homKS * waveA τ k / α := by
  refine (norm_homHadamardCLM_le (hm.Q k)).trans (le_of_eq ?_); ring

theorem norm_homTQt_le (hm : HomMultBounds τ α w W) (k : Fin 2 → ℤ) :
    ‖homTQt hm k‖ ≤ homKS * waveA τ k / α := by
  refine (norm_homHadamardCLM_le (hm.Qt k)).trans (le_of_eq ?_); ring

/-- A component solved with multipliers of norm `≤ κ A_k/α` is again a component, on `T_{s-σ}`. -/
theorem isHomComp_solve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {s σ κ : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hκ : 1 ≤ κ) (hσ : 0 < σ) (hσs : σ < s)
    {T : (Fin 2 → ℤ) → E →L[ℂ] E} (hT : ∀ k, ‖T k‖ ≤ κ * waveA τ k / α)
    {u : (Fin 2 → ℂ) → E} (hu : IsHomComp s u) : IsHomComp (s - σ) (homSolve T u) := by
  obtain ⟨hd, hp, m, hm⟩ := hu
  obtain ⟨-, -, hb, hd', hp', -⟩ := homSolve_spec hτ hα hκ hσ hσs hT hd hp hm
  exact ⟨hd', hp', _, hb⟩


theorem homCoeff_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {s : ℝ} (hs : 0 < s)
    {u v : (Fin 2 → ℂ) → E} (h : ∀ z ∈ complexStrip 2 s, u z = v z) (k : Fin 2 → ℤ) :
    homCoeff u k = homCoeff v k := by
  unfold homCoeff torusCoeffW
  congr 1
  funext x
  show _ • u (fun j => (x j : ℂ)) = _ • v (fun j => (x j : ℂ))
  rw [h _ (ofReal_mem_complexStrip hs x)]

theorem homSolve_congr {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] {s : ℝ} (hs : 0 < s)
    (T : (Fin 2 → ℤ) → E →L[ℂ] E') {u v : (Fin 2 → ℂ) → E}
    (h : ∀ z ∈ complexStrip 2 s, u z = v z) : homSolve T u = homSolve T v := by
  unfold homSolve
  congr 1
  funext k
  rw [homCoeff_congr hs h]

/-- **Entries of a Hadamard solve** are scalar solves of the entries. -/
theorem homSolve_hadamard_entry {s σ m κ α τ : ℝ} (a p : ℝ) (hτ : 0 ≤ τ) (hα : 0 < α)
    (hκ : 1 ≤ κ) (hσ : 0 < σ) (hσs : σ < s) {d : (Fin 2 → ℤ) → ℕ+ → ℕ+ → ℂ}
    {c : (Fin 2 → ℤ) → ℝ} (hd : ∀ k, HomHadamardBound (d k) (c k))
    (hT : ∀ k, ‖homHadamardCLM (hd k)‖ ≤ κ * waveA τ k / α) {u : (Fin 2 → ℂ) → HomOp}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z)
    (hm : ∀ z ∈ complexStrip 2 s, ‖u z‖ ≤ m) (i j : ℕ+) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 (s - σ)) :
    homNormalEntry a p (homSolve (fun k => homHadamardCLM (hd k)) u θ) i j =
      homSolve (fun k => d k i j • ContinuousLinearMap.id ℂ ℂ)
        (fun z => homNormalEntry a p (u z) i j) θ := by
  have := homSolve_image_eq hτ hα hκ hσ hσs hT (homNormEntryCLM a p i j)
    (T' := fun k => d k i j • ContinuousLinearMap.id ℂ ℂ)
    (fun k => by
      refine ContinuousLinearMap.ext fun A => ?_
      simp only [ContinuousLinearMap.comp_apply, homNormEntryCLM_apply, homHadamardCLM_apply,
        homNormalEntry_hadamard, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul]) hu hp hm hθ
  simpa only [homNormEntryCLM_apply] using this


/-- Entries of the Hadamard solve of an operator component, packaged. -/
theorem homSolve_entry_symm {s σ κ : ℝ} {a p : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hκ : 1 ≤ κ)
    (hσ : 0 < σ) (hσs : σ < s) {d d' : (Fin 2 → ℤ) → ℕ+ → ℕ+ → ℂ} {c c' : (Fin 2 → ℤ) → ℝ}
    (hd : ∀ k, HomHadamardBound (d k) (c k)) (hd' : ∀ k, HomHadamardBound (d' k) (c' k))
    (hT : ∀ k, ‖homHadamardCLM (hd k)‖ ≤ κ * waveA τ k / α)
    (hT' : ∀ k, ‖homHadamardCLM (hd' k)‖ ≤ κ * waveA τ k / α)
    {u u' : (Fin 2 → ℂ) → HomOp} (hu : IsHomComp s u) (hu' : IsHomComp s u')
    (i j : ℕ+) (hdd : ∀ k, d k i j = d' k j i)
    (huu : ∀ z ∈ complexStrip 2 s, homNormalEntry a p (u z) i j = homNormalEntry a p (u' z) j i)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ)) :
    homNormalEntry a p (homSolve (fun k => homHadamardCLM (hd k)) u θ) i j =
      homNormalEntry a p (homSolve (fun k => homHadamardCLM (hd' k)) u' θ) j i := by
  obtain ⟨hud, hup, m, hm⟩ := hu
  obtain ⟨hud', hup', m', hm'⟩ := hu'
  rw [homSolve_hadamard_entry a p hτ hα hκ hσ hσs hd hT hud hup hm i j hθ,
    homSolve_hadamard_entry a p hτ hα hκ hσ hσs hd' hT' hud' hup' hm' j i hθ]
  have hs : 0 < s := hσ.trans hσs
  have := homSolve_congr hs (fun k => d k i j • ContinuousLinearMap.id ℂ ℂ) huu
  rw [this]
  congr 2
  funext k
  rw [hdd k]

/-- **The solution `F ∈ 𝒯_{s-σ}`** of Theorem `bpW:w4:lemma1` (i): its components are the solves of
the components of `R`. -/
def homSolveTaylor {a p s σ : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    (hm : HomMultBounds τ α w W) (R : HomTaylor a p s) : HomTaylor a p (s - σ) where
  a0 := homSolve (homTscal w) R.a0
  b := homSolve (homTvec w) R.b
  cp := homSolve (homTdp hm) R.cp
  cm := homSolve (homTdm hm) R.cm
  P := homSolve (homTP hm) R.P
  P' := homSolve (homTP' hm) R.P'
  Q := homSolve (homTQ hm) R.Q
  Qt := homSolve (homTQt hm) R.Qt
  comp_a0 := isHomComp_solve hτ hα le_rfl hσ hσs (norm_homTscal_le hm) R.comp_a0
  comp_b := isHomComp_solve hτ hα le_rfl hσ hσs (norm_homTvec_le hm) R.comp_b
  comp_cp := isHomComp_solve hτ hα le_rfl hσ hσs (norm_homTdp_le hm) R.comp_cp
  comp_cm := isHomComp_solve hτ hα le_rfl hσ hσs (norm_homTdm_le hm) R.comp_cm
  comp_P := isHomComp_solve hτ hα one_le_homKS hσ hσs (norm_homTP_le hm) R.comp_P
  comp_P' := isHomComp_solve hτ hα one_le_homKS hσ hσs (norm_homTP'_le hm) R.comp_P'
  comp_Q := isHomComp_solve hτ hα one_le_homKS hσ hσs (norm_homTQ_le hm) R.comp_Q
  comp_Qt := isHomComp_solve hτ hα one_le_homKS hσ hσs (norm_homTQt_le hm) R.comp_Qt
  symP := fun θ hθ i j =>
    homSolve_entry_symm (a := a) (p := p) hτ hα one_le_homKS hσ hσs hm.P hm.P (norm_homTP_le hm)
      (norm_homTP_le hm) R.comp_P R.comp_P i j (fun k => homDP_symm w W k i j)
      (fun z hz => R.symP z hz i j) hθ
  symP' := fun θ hθ i j =>
    homSolve_entry_symm (a := a) (p := p) hτ hα one_le_homKS hσ hσs hm.P' hm.P'
      (norm_homTP'_le hm) (norm_homTP'_le hm) R.comp_P' R.comp_P' i j
      (fun k => homDP'_symm w W k i j) (fun z hz => R.symP' z hz i j) hθ
  transQ := fun θ hθ i j =>
    homSolve_entry_symm (a := a) (p := p) hτ hα one_le_homKS hσ hσs hm.Qt hm.Q
      (norm_homTQt_le hm) (norm_homTQ_le hm) R.comp_Qt R.comp_Q i j (fun k => rfl)
      (fun z hz => R.transQ z hz i j) hθ

end KAM.Wave
