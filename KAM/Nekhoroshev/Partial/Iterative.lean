/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.IterativeMap
public import KAM.Nekhoroshev.Partial.IterativeRemainder

/-!
# The Iterative Lemma with slow parameters (`bpN:p11:iterative`)

Part 11, package N11-H. The signed `iterative` (Lemma B.6ᵉ): for the generating function
`φ = homGenerator K Λ h f` of the homological equation and `Φ = X¹_φ = extFlow b R s ρ σ φ 1`,

* (a) `Φ` is holomorphic on `𝒟_{R-3ρ/2,s-3σ/2}` with values in `𝒟_{R-ρ,s-σ}`, commutes with
  integer angle translations, is canonical (`ExtCanonical b.c`), and on `𝒟_{R-2ρ,s-2σ}` has the
  left inverse `X⁻¹_φ`, hence is injective there (design Revision 2, F2);
* (b) the componentwise displacements;
* (c), (d) `H ∘ Φ = h + g₊ + f₊`, `|g₊ - g| ≤ δ`, `f₊ ∈ 𝒪_{R-2ρ,s-2σ}` with the source bound;
* (e) reality.

Steps: `it-gen` (`NitHyp.nit_hom`, `NitHyp.nit_V_le`), `it-map` (the signed `canonical_map`,
`NitHyp.nit_disp`, `nit_injOn`), `it-taylor` and `it-est` (`NitHyp.nit_remainder`); reality by
`NitHyp.nit_real` and the reality clause of `canonical_map`. The premise `hc : 0 < b.c` is the
lane-N ruling F2-C1 (option (a) of `N11-F2-audit-1`), needed by the signed `canonical_map`.
Design `docs/tracks/N/design/N11-LEAN-DESIGN.md`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.NormalForm

variable {n k : ℕ}

-- Lane-N ruling F2-C1 (Zohar's team, 2026-10-28): `(hc : 0 < b.c)` added, option (a) of
-- N11-F2-audit-1; `nf` supplies it from `ExtNFHyp.radius_pos`/`slow_width_pos`.
theorem iterative (b : PartialBlock n k) (hk : 1 ≤ k) {R s ρ σ K α p δ : ℝ}
    (h : (Fin n → ℂ) → ℂ) (f : EC n k → ℂ) (Λ : Set (Fin n → ℤ))
    (hR : 0 < ρ) (hR' : 2*ρ < R) (hs : 0 < σ) (hs' : 2*σ < s)
    (hSL : slowLoss b.c ρ σ k) (hc : 0 < b.c) (hα : 0 < α) (hp : 1 < p) (hK : 0 ≤ K)
    (hh : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} R))
    (hdiv : DivisorBound (polyNbhd {KAM.realInclusion n b.Ic} R) K Λ h (α/conjExp p))
    (hδ : 0 ≤ δ) (hf : InClass b.base R s f) (hfb : WBound b.base R s f δ)
    (hsmall : δ ≤ 2*Real.pi*α*ρ*σ/(4*conjExp p))
    {N : ℕ} (gj : Fin N → EC n k → ℂ) (Rj sj Uj : Fin N → ℝ)
    (hRj : ∀ j, R ≤ Rj j) (hsj : ∀ j, s ≤ sj j) (hUj : ∀ j, 0 ≤ Uj j)
    (hgj : ∀ j, InClass b.base (Rj j) (sj j) (gj j))
    (hgjb : ∀ j, WBound b.base (Rj j) (sj j) (gj j) (Uj j)) :
    let q := conjExp p
    let φ := homGenerator K Λ h f
    let Φ := extFlow b R s ρ σ φ 1
    let g := fun z => ∑ j, gj j z
    let gp := g+projMode Λ (truncate K f)
    DifferentiableOn ℂ Φ (Dom n b.base (R-3*ρ/2) (s-3*σ/2)) ∧
    MapsTo Φ (Dom n b.base (R-3*ρ/2) (s-3*σ/2)) (Dom n b.base (R-ρ) (s-σ)) ∧
    (∀ z ∈ Dom n b.base (R-3*ρ/2) (s-3*σ/2), ∀ ℓ : Fin n → ℤ,
      Φ (z.1+(fun i => (ℓ i:ℂ)),z.2) = Φ z+((fun i => (ℓ i:ℂ)),0)) ∧
    (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), extFlow b R s ρ σ φ (-1) (Φ z) = z) ∧
    ∃ fp : EC n k → ℂ,
      InClass b.base (R-2*ρ) (s-2*σ) fp ∧
      (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ),
        liftFast h (Φ z)+g (Φ z)+f (Φ z) = liftFast h z+gp z+fp z) ∧
      WBound b.base (R-2*ρ) (s-2*σ) fp
        ((1-2*q*δ/(2*Real.pi*α*ρ*σ))⁻¹*
          (q/(2*Real.pi*α*ρ*σ)*((∑ j, (1/2)*(ρ/(Rj j-R+ρ)+σ/(sj j-s+σ))*Uj j)+δ)+
            Real.exp (-2*Real.pi*K*σ))*δ) ∧
      ExtCanonical b.c (Dom n b.base (R-3*ρ/2) (s-3*σ/2)) Φ ∧
      Set.InjOn Φ (Dom n b.base (R-2*ρ) (s-2*σ)) ∧
      WBound b.base (R-2*ρ) (s-2*σ) (gp-g) δ ∧
      (∀ z ∈ Dom n b.base (R-3*ρ/2) (s-3*σ/2),
        ‖(Φ z).1-z.1‖ ≤ q*δ/(2*Real.pi*α*ρ) ∧
        ‖fastAction (Φ z)-fastAction z‖ ≤ q*δ/(Real.exp 1*2*Real.pi*α*σ) ∧
        ‖slowPair (Φ z)-slowPair z‖ ≤ q*δ/(16*k*2*Real.pi*α*σ)) ∧
      ((∀ j, j ∈ Λ ↔ -j ∈ Λ) →
        (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n b.Ic} R →
          (h (KAM.realInclusion n I)).im = 0) →
        extReal (Dom n b.base R s) g → extReal (Dom n b.base R s) f →
        extReal (Dom n b.base R s) φ ∧ extReal (Dom n b.base (R-2*ρ) (s-2*σ)) gp ∧
        extReal (Dom n b.base (R-2*ρ) (s-2*σ)) fp ∧
        ∀ z : ER n k, extCx z ∈ Dom n b.base (R-3*ρ/2) (s-3*σ/2) →
          extCx (extRe (Φ (extCx z))) = Φ (extCx z)) := by
  intro q φ Φ g gp
  have H : NitHyp b R s ρ σ K α p δ h f Λ :=
    ⟨hk, hR, hR', hs, hs', hSL, hc, hα, hp, hK, hh, hdiv, hδ, hf, hfb, hsmall⟩
  -- step `it-gen` and step `it-map`: the signed `canonical_map` with `V = qδ/(2πα)`
  obtain ⟨m1, -, m3, -, m5, m6, m7, m8, -, m10⟩ :=
    canonical_map b hk hc hR (by linarith) hs (by linarith) hSL H.nit_V_nonneg H.nit_V_half
      H.nit_phi_class H.nit_phi_bound
  -- steps `it-taylor` and `it-est`
  obtain ⟨r1, r2⟩ := H.nit_remainder gj Rj sj Uj hRj hsj hUj hgj hgjb
  refine ⟨m1, m3, m7, fun z hz => (m8 z hz).1,
    nitF b R s ρ σ φ h g f (projMode Λ (truncate K f)), r1,
    fun z _ => nitF_identity b R s ρ σ φ h g f (projMode Λ (truncate K f)) z, r2, m5,
    nit_injOn (Ψ := extFlow b R s ρ σ φ (-1)) fun z hz => (m8 z hz).1,
    H.nit_gp_bound g, H.nit_disp m6, ?_⟩
  -- clause (e)
  intro hΛ hhr hgr hfr
  obtain ⟨e1, e2, e3⟩ := H.nit_real hΛ hhr hgr hfr
  exact ⟨e1, e2, e3, m10 e1⟩

end KAM.Nekhoroshev

end
