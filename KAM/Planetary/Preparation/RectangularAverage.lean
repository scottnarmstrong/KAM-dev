/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Preparation.RectangularAverageCore
public import KAM.Planetary.Preparation.RectangularAverageDomain

/-!
# Rectangular two-scale averaging (P11A-P4, `bpP:p11:aniso-avg`)

`aniso_avg` is the finite averaging iteration `p11_nfb_core` applied to the closed polydisc
`p11AvgBase c r₁ r₂` with the single radius `r_* = min r₁ r₂` (`stepP:p11:aa-same`): its
`r_*`-neighbourhood is the rectangle `p11Box c r₁ r₂`, so the block radii enter only through
the inclusions of `RectangularAverageDomain`. The quadratic bound of `g - f̂₀` is
`stepP:p11:aa-quad`. The width `s` of `KAM.Weighted` is the geometric one, so `κ = 2 π T s`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

/-- Rectangular averaging statement; divisor hypotheses are the literal B1, not an assumed
  output. -/
theorem aniso_avg {a b : ℕ} {c : P11CVec (a+b)} {r1 r2 s T alpha1 alpha2 E : ℝ}
    (hr1 : 0 < r1) (hr2 : 0 < r2) (hs : 0 < s) (hT : 0 < T)
    (hk : 6 ≤ 2*Real.pi*T*s) (ha : 0 < alpha2) (ha' : alpha2 ≤ alpha1)
    {h : P11CVec (a+b) → ℂ} {f : P11Phase (a+b) → ℂ}
    (hh : DifferentiableOn ℂ h (p11Box c r1 r2))
    (hf : DifferentiableOn ℂ f (KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2))
    (hp : ∀ z ∈ KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2,
      ∀ i : Fin (a+b), f (z.1+Pi.single i 1,z.2)=f z)
    (hrealh : ∀ x : P11Vec (a+b), KAM.realInclusion (a+b) x ∈ p11Box c r1 r2 →
      (h (KAM.realInclusion (a+b) x)).im=0)
    (hrealf : KAM.Canonical.RealOn (KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2) f)
    (hE : 0 ≤ E) (hb : p11WBound (p11Box c r1 r2) s f E)
    (hsmall : E ≤ alpha2*min r1 r2/(128*T))
    (hdiv : ∀ I ∈ p11Box c r1 r2, ∀ k : Fin (a+b) → ℤ, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      (if (fun i : Fin a => k (Fin.castAdd b i))=0 then alpha2 else alpha1) ≤
        ‖p11dotC k (fun i => fderiv ℂ h I (Pi.single i 1))‖) :
    ∃ Psi : P11Phase (a+b) → P11Phase (a+b), ∃ g : P11CVec (a+b) → ℂ,
      ∃ fs : P11Phase (a+b) → ℂ,
      let U := KAM.complexStrip (a+b) (s/6) ×ˢ p11Box c (r1/2) (r2/2)
      DifferentiableOn ℂ Psi U ∧ InjOn Psi U ∧
      DifferentiableOn ℂ g (p11Box c (r1/2) (r2/2)) ∧ DifferentiableOn ℂ fs U ∧
      KAM.Canonical.RealOn U fs ∧
      (∀ I : P11Vec (a+b), KAM.realInclusion (a+b) I ∈ p11Box c (r1/2) (r2/2) →
        (g (KAM.realInclusion (a+b) I)).im=0) ∧
      (∀ z ∈ U, ∀ k : Fin (a+b)
        → ℤ, Psi (z.1+(fun i => (k i : ℂ)),z.2)=Psi z+((fun i => (k i : ℂ)),0)) ∧
      (∀ z ∈ U, ∀ i : Fin (a+b), fs (z.1+Pi.single i 1,z.2)=fs z) ∧
      (∀ z : Phase (a+b), KAM.realInclusion₂ (a+b) z ∈ U → ∀ i,
        ((Psi (KAM.realInclusion₂ (a+b) z)).1 i).im=0 ∧
        ((Psi (KAM.realInclusion₂ (a+b) z)).2 i).im=0) ∧
      MapsTo Psi U (KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2) ∧
      (∀ z ∈ U, h (Psi z).2+f (Psi z)=h z.2+g z.2+fs z) ∧
      p11WBound (p11Box c (r1/2) (r2/2)) (s/6) fs (Real.exp (-2*Real.pi*T*s/6)*E) ∧
      p11WBound (p11Box c (r1/2) (r2/2)) (s/6)
        (fun z : P11Phase (a+b) 
          => g z.2-KAM.Weighted.coeff f z.2 0) (130*E^2/(2*Real.pi*alpha2*min r1 r2*s)) ∧
      p11WBound (p11Box c (r1/2) (r2/2)) (s/6)
        (fun z : P11Phase (a+b) => g z.2-KAM.Weighted.coeff f z.2 0) (E/(2*Real.pi*T*s)) ∧
      (∀ z ∈ U,
        2*Real.pi*alpha1*s*‖(fun i : Fin a 
          => (Psi z).2 (Fin.castAdd b i)-z.2 (Fin.castAdd b i))‖ ≤ 3*E ∧
        2*Real.pi*alpha2*s*‖(fun i : Fin b => (Psi z).2 (Fin.natAdd a i)-z.2 (Fin.natAdd a i))‖
          ≤ 3*E) ∧
      (∀ z ∈ U, ‖(Psi z).1-z.1‖ ≤ 9*E/(2*Real.pi*alpha2*min r1 r2)) ∧
      (∀ z ∈ U, ∀ u v, KAM.Canonical.symplFormC (fderiv ℂ Psi z u) (fderiv ℂ Psi z v)=
        KAM.Canonical.symplFormC u v) := by
  classical
  have hm0 : 0 < min r1 r2 := lt_min hr1 hr2
  have hsub := polyNbhd_avgBase_subset c r1 r2
  have hhalf := box_half_subset c hr1 hr2
  have hDom : KAM.Weighted.Dom (a+b) (p11AvgBase c r1 r2) (min r1 r2) (0+s) ⊆
      KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2 := by
    rw [zero_add]; exact fun z hz => ⟨hz.1, hsub hz.2⟩
  have H : P11AvgHyp (p11AvgBase c r1 r2) (min r1 r2) 0 s T alpha1 alpha2 E h f :=
    { r_pos := hm0, sbar_nonneg := le_rfl, s_pos := hs, K_pos := hT, budget := hk,
      α₂_pos := ha, α_order := ha', E_nonneg := hE, holo := hh.mono hsub,
      real_h := fun x hx => hrealh x.2 (hsub (show KAM.realInclusion (a+b) x.2 ∈ _ from hx.2))
      real_f := fun x hx => hrealf x (hDom hx)
      cls := ⟨hf.mono hDom, fun j z hz => hp z (hDom hz) j⟩
      bound := fun I hI => by rw [zero_add]; exact hb I (hsub hI)
      div := fun I hI k hk hkK => by rw [div_one]; exact hdiv I (hsub hI) k hk hkK
      small := hsmall }
  obtain ⟨Ψ, g, fs, hV⟩ := p11_nfb_core H
  refine ⟨Ψ, g, fs, ?_⟩
  intro U
  simp only [zero_add] at hV
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hV
  have hUV : U ⊆ KAM.Weighted.Dom (a+b) (p11AvgBase c r1 r2) (min r1 r2 / 2) (s / 6) :=
    fun z hz => ⟨hz.1, hhalf hz.2⟩
  have hX : 0 < 2 * Real.pi * alpha2 * min r1 r2 * s := by positivity
  refine ⟨c1.mono hUV, c2.mono hUV, c7.mono hhalf, c13.differentiableOn.mono hUV,
    fun x hx => c9 x (hUV hx), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro I hI
    have := c8 (0, I) (hUV ⟨by intro i; simp; positivity, hI⟩)
    exact this
  · intro z hz k
    have e : (z.1 + (fun i => (k i : ℂ)), z.2) = z + ((fun i => (k i : ℂ)), 0) := by
      ext <;> simp
    rw [e]; exact c5 z (hUV hz) k
  · exact fun z hz i => c13.periodic i z (hUV hz)
  · intro z hz i
    obtain ⟨y, hy⟩ := c6 z (hUV hz)
    rw [← hy]
    simp
  · exact fun z hz => ⟨(c3 (hUV hz)).1, hsub (c3 (hUV hz)).2⟩
  · exact fun z hz => c10 z (hUV hz)
  · intro I hI
    have := c14 I (hhalf hI)
    rwa [show -2 * Real.pi * T * s / 6 = -(2 * Real.pi * T * s) / 6 by ring]
  · intro I hI
    obtain ⟨h1, h2⟩ := c12 I (hhalf hI)
    refine ⟨h1, h2.trans ?_⟩
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg E]) hX.le
  · exact fun I hI => c11 I (hhalf hI)
  · intro z hz
    obtain ⟨d1, d2, d3⟩ := c15 z (hUV hz)
    exact ⟨d1, d2⟩
  · intro z hz
    obtain ⟨d1, d2, d3⟩ := c15 z (hUV hz)
    rw [le_div_iff₀ (by positivity)]
    linarith
  · exact fun z hz u v => c4 z (hUV hz) u v

end KAM.Planetary

end
