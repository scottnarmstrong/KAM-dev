/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.LimitMapLip

/-!
# Two-scale KAM: the checked map `Ǧ` and the scaled Lipschitz constant `L_*` (`bpP:p3:limitmap`)

The source fixes `S(I, θ) = (I/ρ̂₀, 2πθ/s₀)`, `|·|_* = |S ·|` and, for a map `G`, writes
`Ǧ = S G S⁻¹` and `L_*` for Lipschitz constants in `|·|_*`. `sc`, `unsc`, `limitmap_data` are
`S`, `S⁻¹`, `|·|_*`; here `limitmapCheck` is `Ǧ` for an arbitrary map `G`, and `LipStar` is the
statement that `L` is a Lipschitz constant of `G` on a set in `|·|_*`, with the identification
with a Lipschitz bound of `Ǧ` in the max norm and the instance `PsiSteps.psi_lipStar`
(`stepP:p3:pl-lip`).
-/

@[expose] public noncomputable section

open Set Real

namespace KAM.Planetary

section Check

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- `Ǧ = S G S⁻¹` for an arbitrary map `G` of `𝕜ⁿ × 𝕜ⁿ`, in the scaled coordinates `𝕜^(n+n)`. -/
def limitmapCheck (R s : ℝ) (G : (Fin n → 𝕜) × (Fin n → 𝕜) → (Fin n → 𝕜) × (Fin n → 𝕜)) :
    (Fin (n + n) → 𝕜) → (Fin (n + n) → 𝕜) :=
  fun z => sc R s (G (unsc R s z))

theorem limitmapCheck_apply (R s : ℝ)
    (G : (Fin n → 𝕜) × (Fin n → 𝕜) → (Fin n → 𝕜) × (Fin n → 𝕜)) (z : Fin (n + n) → 𝕜) :
    limitmapCheck R s G z = sc R s (G (unsc R s z)) := rfl

theorem limitmapCheck_comp {R s : ℝ} (hR : R ≠ 0) (hs : s ≠ 0)
    (G H : (Fin n → 𝕜) × (Fin n → 𝕜) → (Fin n → 𝕜) × (Fin n → 𝕜)) :
    limitmapCheck R s (G ∘ H) = limitmapCheck R s G ∘ limitmapCheck R s H := by
  funext z
  simp only [limitmapCheck, Function.comp, unsc_sc hR hs]

theorem limitmapCheck_id {R s : ℝ} (hR : R ≠ 0) (hs : s ≠ 0) :
    limitmapCheck R s (id : (Fin n → 𝕜) × (Fin n → 𝕜) → _) = id := by
  funext z; simp [limitmapCheck, sc_unsc hR hs]

/-- `S (G x) = Ǧ (S x)`: the checked map is `G` read in scaled coordinates. -/
theorem limitmapCheck_sc {R s : ℝ} (hR : R ≠ 0) (hs : s ≠ 0)
    (G : (Fin n → 𝕜) × (Fin n → 𝕜) → (Fin n → 𝕜) × (Fin n → 𝕜)) (w : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    limitmapCheck R s G (sc R s w) = sc R s (G w) := by
  simp [limitmapCheck, unsc_sc hR hs]

/-- `(G − id)ˇ = Ǧ − id`. -/
theorem limitmapCheck_sub_id {R s : ℝ} (hR : R ≠ 0) (hs : s ≠ 0)
    (G : (Fin n → 𝕜) × (Fin n → 𝕜) → (Fin n → 𝕜) × (Fin n → 𝕜)) :
    limitmapCheck R s (fun w => G w - w) = fun z => limitmapCheck R s G z - z := by
  funext z
  simp only [limitmapCheck, sc_sub, sc_unsc hR hs]

end Check

section LipStarDef

variable {n : ℕ}

/-- `L_*`: `L` is a Lipschitz constant of `G` on `S` in the scaled norm `|·|_*`
(`limitmap_data R s`), `|G x − G y|_* ≤ L |x − y|_*`. -/
def LipStar (R s L : ℝ) (S : Set (Phase n)) (G : Phase n → Phase n) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, limitmap_data R s (G x - G y) ≤ L * limitmap_data R s (x - y)

/-- `L_*` is the max-norm Lipschitz bound of the checked map `Ǧ` on `S(S)`. -/
theorem lipStar_iff_check {R s L : ℝ} (hR : 0 < R) (hs : 0 < s) (S : Set (Phase n))
    (G : Phase n → Phase n) :
    LipStar R s L S G ↔ ∀ x ∈ S, ∀ y ∈ S,
      ‖limitmapCheck R s G (sc R s x) - limitmapCheck R s G (sc R s y)‖ ≤
        L * ‖sc R s x - sc R s y‖ := by
  simp only [LipStar, limitmapCheck_sc hR.ne' hs.ne', ← sc_sub, ← limitmap_data_eq_norm_sc hR hs]

theorem LipStar.mono {R s L L' : ℝ} {S T : Set (Phase n)} {G : Phase n → Phase n}
    (h : LipStar R s L S G) (hLL : L ≤ L') (hR : 0 < R) (hs : 0 < s) (hTS : T ⊆ S) :
    LipStar R s L' T G := fun x hx y hy =>
  (h x (hTS hx) y (hTS hy)).trans
    (mul_le_mul_of_nonneg_right hLL (limitmap_data_nonneg hR hs _))

end LipStarDef

namespace PsiSteps

variable {a b : ℕ} {sbar : ℝ} {p : ScaleData}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)}

/-- `stepP:p3:pl-lip` as an instance of `L_*`: `L_*(Ψ̌_{j+1} − id; 𝒟_{j+1} × ℝⁿ) ≤ ς_{j+1}`. -/
theorem psi_lipStar (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) :
    LipStar (rhoHat p) p.s
      (192 * ((a + b : ℕ) : ℝ) * (((24 : ℝ) ^ (p.τ + 1) / 6) ^ j * eHat (seq p j)))
      (phaseTube (Ds (j + 1)) ((seq p (j + 1)).ρ / 2))
      (fun x => psiR (Ψ (j + 1)) x - x) :=
  fun _ hx _ hy => P.psi_lip_step j hx hy

end PsiSteps

end KAM.Planetary

end
