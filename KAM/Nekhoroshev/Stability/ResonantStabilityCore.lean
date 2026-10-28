/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Stability.Resonant
public import KAM.Nekhoroshev.Stability.ResonantStabilityHess

/-!
# The transfer step of `resonant-prop2` (steps `p2-t12`, `p2-t3`, `p2-concl`)

`prop2_core`: given a conjugacy `Ψ : Dom (r/2) s̃ → Dom r s` with `H ∘ Ψ = h + g + f_*`, the
resonant setting data of `g`, `f_*`, the displacement `d ≤ ρ'/4` and the surjectivity (T2), the
confinement of `H`-orbits follows from `resonant_lemma2` (at radius `r/2`) and `transfer`
(with `Nrm = ‖·‖₂`). The three cases of the proposition only supply this data.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Stability

open KAM.Weighted KAM.Canonical
open KAM.Nekhoroshev (euclid)

variable {n : ℕ}

/-- The hypotheses `H ∘ Ψ = h + g + f_*` etc. are premises (typing data of the normal form); the
conclusion is the confinement of `H`-orbits in `‖·‖₂`-radius `r/2`. -/
theorem prop2_core (hn : 1 ≤ n) {D : Set (Fin n → ℝ)} {r s s' K m M ℓ δ ε Mg η ζ d : ℝ}
    {Λ : Set (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {f g fs : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hr : 0 < r) (hs : 0 < s) (hs' : 0 < s') (hss : s' ≤ s) (hm : 0 < m) (hmM : m ≤ M) (hε0 : 0 ≤ ε)
    (hδ : 0 < δ)
    (hh : DifferentiableOn ℂ h (polyNbhd (cpx D) r))
    (hhr : RealOn (Dom n (cpx D) r s) (fun w => h w.2))
    (hess : HessBound (realNbhd D (r / 2)) h M)
    (hqc : IsQuasiConvex (realNbhd D r) h ℓ m)
    (hf : InClass (cpx D) r s f) (hfr : RealOn (Dom n (cpx D) r s) f)
    (hclose : IsCloseToRes D Λ h δ) (hδb : δ ≤ m * r / 8)
    (hc2 : r ≤ 4 * ℓ / m) (hc3 : M * r ≤ ℓ / 2)
    (hg : InClass (cpx D) (r / 2) s' g) (hgr : RealOn (Dom n (cpx D) (r / 2) s') g)
    (hgb : WBound (cpx D) (r / 2) s' g Mg)
    (hgres : ∀ I ∈ polyNbhd (cpx D) (r / 2), ∀ k, k ∉ Λ → coeff g I k = 0)
    (hfs : InClass (cpx D) (r / 2) s' fs) (hfsr : RealOn (Dom n (cpx D) (r / 2) s') fs)
    (hfsb : WBound (cpx D) (r / 2) s' fs η) (hη : 0 ≤ η) (hζ1 : Mg + η ≤ ζ)
    (hζ2 : ζ ≤ m * r ^ 2 / 128)
    (hΨ : DifferentiableOn ℂ Ψ (Dom n (cpx D) (r / 2) s'))
    (hΨmap : MapsTo Ψ (Dom n (cpx D) (r / 2) s') (Dom n (cpx D) r s))
    (hΨreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ),
      KAM.realInclusion₂ n x ∈ Dom n (cpx D) (r / 2) s' →
      Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n))
    (hΨsympl : ∀ z ∈ Dom n (cpx D) (r / 2) s', ∀ v w,
      symplFormC (fderiv ℂ Ψ z v) (fderiv ℂ Ψ z w) = symplFormC v w)
    (hconj : ∀ z ∈ Dom n (cpx D) (r / 2) s', h z.2 + g z + fs z = h (Ψ z).2 + f (Ψ z))
    (hT1 : ∀ x ∈ realStrip D (r / 2), euclid ((reMap Ψ x).2 - x.2) ≤ d)
    (hT2 : ∀ y : (Fin n → ℝ) × (Fin n → ℝ), y.2 ∈ D →
      ∃ x ∈ realStrip D (r / 2), reMap Ψ x = y)
    (hd0 : 0 ≤ d) (hd1 : d ≤ resRho (m * r / 8) M / 4)
    (hT : ∀ Ω : ℝ, 0 ≤ Ω → ∀ t : ℝ,
      ((Λ : Set (Fin n → ℤ)) = univ ∨
        |t| * (288 * Ω * ε) ≤ s * m * r ^ 2 * Real.exp (2 * Real.pi * K * s / 6)) →
      |t| * (12 * Ω * η) ≤ s' * m * (r / 2) ^ 2) :
    ∀ I₀ ∈ D, ∀ Ω : ℝ, (∀ I, euclid (I - I₀) ≤ r / 2 → euclid (KAM.frequencyMap h I) ≤ Ω) →
      ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z, IsOrbit (fun w => h w.2 + f w) D r J z →
        (z 0).2 = I₀ → ∀ t ∈ J, ((Λ : Set (Fin n → ℤ)) = univ ∨
            |t| * (288 * Ω * ε) ≤ s * m * r ^ 2 * Real.exp (2 * Real.pi * K * s / 6)) →
          euclid ((z t).2 - I₀) ≤ r / 2 := by
  intro I₀ hI₀ Ω hΩ J hJ h0 z hz hz0 t ht htime
  have hMpos : 0 < M := lt_of_lt_of_le hm hmM
  set ρ' := resRho (m * r / 8) M with hρ'def
  have hρ : 0 < ρ' := by rw [hρ'def]; unfold resRho; positivity
  have hρr : ρ' ≤ r / 32 := by
    rw [hρ'def, resRho, div_le_iff₀ (by positivity)]
    nlinarith
  have hΩ0 : 0 ≤ Ω := by
    have := hΩ I₀ (by simp [euclid]; positivity)
    exact (Real.sqrt_nonneg _).trans this
  have hRS : ResSetting D (r / 2) s' Λ h m M g fs Mg η ζ (m * r / 8) :=
    { hn := hn
      hr := by positivity
      hs := hs'
      h_holo := hh.mono (polyNbhd_mono (by linarith))
      h_real := fun x hx => hhr x (Dom_mono (by linarith) hss hx)
      hm := hm
      hmM := hmM
      hess := hess
      g_class := hg
      g_real := hgr
      g_bound := hgb
      g_res := hgres
      fs_class := hfs
      fs_real := hfsr
      fs_bound := hfsb
      η_nonneg := hη
      ζ_ge := hζ1
      hδ := by positivity
      close := fun I hI => by
        obtain ⟨w, hw, hle⟩ := hclose I hI
        exact ⟨w, hw, hle.trans hδb⟩
      δ_le := by linarith
      ζ_le := by nlinarith }
  have hclass : ∀ (r₁ : ℝ) (s₁ : ℝ), r₁ ≤ r → InClass (cpx D) r₁ s₁ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2) :=
    fun r₁ s₁ hr₁ => ⟨(hh.mono (polyNbhd_mono hr₁)).comp differentiable_snd.differentiableOn
      fun z hz => hz.2, fun _ _ _ => rfl⟩
  have hH : InClass (cpx D) r s (fun w => h w.2 + f w) :=
    ⟨(hclass r s le_rfl).differentiableOn.add hf.differentiableOn, fun j z hz => by
      show h z.2 + f (z.1 + Pi.single j 1, z.2) = h z.2 + f z
      rw [hf.periodic j z hz]⟩
  have hHr : RealOn (Dom n (cpx D) r s) (fun w => h w.2 + f w) := fun x hx => by
    have h1 : (h (KAM.realInclusion₂ n x).2).im = 0 := hhr x hx
    have h2 : (f (KAM.realInclusion₂ n x)).im = 0 := hfr x hx
    show (h (KAM.realInclusion₂ n x).2 + f (KAM.realInclusion₂ n x)).im = 0
    rw [Complex.add_im, h1, h2, add_zero]
  have hH' : InClass (cpx D) (r / 2) s' (fun w => h w.2 + g w + fs w) :=
    ⟨((hclass (r / 2) s' (by linarith)).differentiableOn.add hg.differentiableOn).add
      hfs.differentiableOn, fun j z hz => by
      show h z.2 + g (z.1 + Pi.single j 1, z.2) + fs (z.1 + Pi.single j 1, z.2) =
        h z.2 + g z + fs z
      rw [hg.periodic j z hz, hfs.periodic j z hz]⟩
  have hH'r : RealOn (Dom n (cpx D) (r / 2) s') (fun w => h w.2 + g w + fs w) := fun x hx => by
    have h1 : (h (KAM.realInclusion₂ n x).2).im = 0 := hRS.h_real x hx
    have h2 : (g (KAM.realInclusion₂ n x)).im = 0 := hgr x hx
    have h3 : (fs (KAM.realInclusion₂ n x)).im = 0 := hfsr x hx
    show (h (KAM.realInclusion₂ n x).2 + g (KAM.realInclusion₂ n x) +
      fs (KAM.realInclusion₂ n x)).im = 0
    rw [Complex.add_im, Complex.add_im, h1, h2, h3]; simp
  have hadm : ∀ I t t', |t'| ≤ |t| → (fun I t => I = I₀ ∧ ((Λ : Set (Fin n → ℤ)) = univ ∨
      |t| * (288 * Ω * ε) ≤ s * m * r ^ 2 * Real.exp (2 * Real.pi * K * s / 6))) I t →
      (fun I t => I = I₀ ∧ ((Λ : Set (Fin n → ℤ)) = univ ∨
      |t| * (288 * Ω * ε) ≤ s * m * r ^ 2 * Real.exp (2 * Real.pi * K * s / 6))) I t' := by
    intro I t t' htt ⟨hI, hc⟩
    refine ⟨hI, hc.imp_right fun hc => ?_⟩
    have h288 : 0 ≤ 288 * Ω * ε := by positivity
    exact (mul_le_mul_of_nonneg_right htt h288).trans hc
  have key := transfer (D := D) (r := r) (s := s) (r' := r / 2) (s' := s') (d := d)
    (ϱ := r / 2 - ρ') (Nrm := fun a : Fin n → ℝ => euclid a)
    (adm := fun I t => I = I₀ ∧ ((Λ : Set (Fin n → ℤ)) = univ ∨
      |t| * (288 * Ω * ε) ≤ s * m * r ^ 2 * Real.exp (2 * Real.pi * K * s / 6)))
    (H := fun w => h w.2 + f w) (H' := fun w => h w.2 + g w + fs w) (Ψ := Ψ)
    hs hs' isActionNorm_euclid hadm hH hHr hH' hH'r hΨ hΨmap hΨreal hΨsympl hconj hT1 hT2
    (by linarith) (by linarith) ?_
  · have := key J hJ h0 z hz (by rw [hz0]; exact hI₀) t ht ⟨hz0, htime⟩
    rw [hz0] at this
    linarith
  · intro Iy hIy J' hJ' h0' z' hz' hd' t' ht' ⟨hIyI, hc⟩
    have hd'' : euclid ((z' 0).2 - I₀) ≤ d := hIyI ▸ hd'
    have hI0adm : IsAdmissible D (m * r / 8) M (z' 0).2 :=
      ⟨I₀, hI₀, lt_of_le_of_lt hd'' (by linarith)⟩
    have hΩ' : ∀ I, euclid (I - (z' 0).2) ≤ r / 2 - resRho (m * r / 8) M →
        euclid (KAM.frequencyMap h I) ≤ Ω := by
      intro I hI
      refine hΩ I ?_
      have e : I - I₀ = (I - (z' 0).2) + ((z' 0).2 - I₀) := by abel
      rw [e]
      refine (isActionNorm_euclid.add_le _ _).trans ?_
      have : euclid (I - (z' 0).2) ≤ r / 2 - ρ' := hI
      linarith
    exact resonant_lemma2 hRS (ℓ := ℓ) (fun I hI => hqc I (realNbhd_mono D (by linarith) hI))
      (by
        have := (le_div_iff₀ hm).1 hc2
        rw [le_div_iff₀ hm]
        nlinarith)
      (by linarith) hI0adm hΩ' J' hJ' h0' z' hz' rfl t' ht' (hT Ω hΩ0 t' hc)

end KAM.Stability

end
