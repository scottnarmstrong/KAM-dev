/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Lock.Graph
public import KAM.SpinOrbit.Data.LockN65.GraphK

/-!
# The librational barrier from the graph check with a key per SOS square (lock-owned)

`lockBarrier_of_certifiedK` and `lockBarrier_of_certV2K` are the landed `lockBarrier_of_certified`
and `lockBarrier_of_certV2` (`KAM/SpinOrbit/Lock/Graph.lean`) with the graph check `checkSoGraphK`
(`GraphK.lean`) in place of `checkSoGraph`. The landed proofs use only the four facts of
`checkSoGraph_sound`, which `checkSoGraphK_sound` gives verbatim; the proofs are copied with that
one lemma replaced. Core and the band are untouched.
-/

@[expose] public noncomputable section

open Real Filter Topology

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Lock SoGraph

variable {α : Type} [CertArith α]

/-- **Engine-generic core**, with the graph check `checkSoGraphK`. The black-box output
`CertifiedTorus` of ANY sound certificate check, the static check, the certified nonvanishing of
the Hamiltonian on the certified domain, a passing graph check, the `hham` tie to `κ ·
lockHamExpr Ω cs` and the positivity margin give the librational barrier, with the band widened
by `disp`. -/
theorem lockBarrier_of_certifiedK [LawfulCertArith α] (g : LockGraphCert α) (hΩ : 0 < g.Ω)
    (hκ : 0 < g.κ) (hham : g.graph.base.ham = .mul (.const g.κ) (lockHamExpr g.Ω g.cs))
    (hlo : 0 < (g.graph.pLo : ℝ) - g.graph.base.params.disp)
    (hs : checkStatic g.graph.base = true)
    (hnv : g.graph.base.ham.NonvanishingOn g.graph.base.D)
    (hg : checkSoGraphK g.graph = true) {ωstar : Fin 2 → ℝ}
    (hT : CertifiedTorus g.graph.base ωstar)
    (hdio : IsDiophantine (g.graph.base.params.γ : ℝ) (g.graph.base.params.tau : ℝ) ωstar) :
    Nonempty (LockBarrier (g.Ω : ℝ) (lockCentre g.cs)
      ((g.graph.pLo : ℝ) - g.graph.base.params.disp)
      ((g.graph.pHi : ℝ) + g.graph.base.params.disp)) := by
  have S := checkStatic_sound hs
  obtain ⟨hm, hmono, hlo', hhi'⟩ := checkSoGraphK_sound S.hW S.hpe hg
  obtain ⟨Kinf, sinf, hs1, -, hholo, hprim, hreal, hinv, -, hball, -, hdisp, -⟩ := hT
  have hρ : (0 : ℝ) < g.graph.base.params.rhoInf := S.hρinf
  have hsinf : 0 < sinf := by linarith
  have hK : Differentiable ℂ g.graph.base.K := CertEmbedding.differentiable_eval 2 g.graph.base.emb
  set d : ℝ := (g.graph.base.params.disp : ℝ)
  have hpt : ∀ x y : ℝ, ‖Kinf (realPt x y) - g.graph.base.K (realPt x y)‖ ≤ d :=
    fun x y => hdisp _ (realPt_mem hρ x y)
  have hH : g.graph.base.H = (HamExpr.mul (.const g.κ) (lockHamExpr g.Ω g.cs)).eval := by
    rw [TorusCertificate.H, hham]
  rw [hH] at hinv
  have hD := re_action_pos_of_nonvanishingOn hΩ (hham ▸ hnv)
  have hKD : ∀ θ ∈ complexStrip 2 g.graph.base.params.rhoInf, 0 < ((Kinf θ).2 0).re :=
    fun θ hθ => hD _ (hball θ hθ (Metric.mem_ball_self (by have := S.hμ; positivity)))
  refine lockBarrier_of_exact_torus hΩ hκ g.cs hρ hholo hprim hreal hinv hKD
    (mul_pos hsinf (by exact_mod_cast S.hγ)) (isDiophantine_smul_scale hsinf hdio)
    (m := (g.graph.mono : ℝ) - d / g.graph.base.params.rhoInf) ?_ (fun x y => ?_) hlo
    (fun x y => ?_) (fun x y => ?_)
  · rw [sub_pos, div_lt_iff₀ hρ]; exact hm
  · have h := soGraph_deriv_transfer hρ hholo hK hdisp x y
    have h' : |((fderiv ℂ Kinf (realPt x y) (realPt 1 0)).1 0).re -
        ((fderiv ℂ g.graph.base.K (realPt x y) (realPt 1 0)).1 0).re| ≤
          d / g.graph.base.params.rhoInf := by
      rwa [le_div_iff₀ hρ]
    have := hmono x y
    have := (abs_le.1 h').1
    linarith
  · have h := (Complex.abs_re_le_norm _).trans
      ((norm_snd_apply_sub_le (Kinf (realPt x y)) (g.graph.base.K (realPt x y))).trans (hpt x y))
    rw [Complex.sub_re] at h
    have := hlo' x y
    have := (abs_le.1 h).1
    linarith
  · have h := (Complex.abs_re_le_norm _).trans
      ((norm_snd_apply_sub_le (Kinf (realPt x y)) (g.graph.base.K (realPt x y))).trans (hpt x y))
    rw [Complex.sub_re] at h
    have := hhi' x y
    have := (abs_le.1 h).2
    linarith

/-- A passing v2 certificate and the graph check with a key per SOS square give the physical
librational barrier (`lockBarrier_of_certV2` with `checkSoGraphK`). -/
theorem lockBarrier_of_certV2K [LawfulCertArith α] (g : LockGraphCert α) (hΩ : 0 < g.Ω)
    (hκ : 0 < g.κ) (hham : g.graph.base.ham = .mul (.const g.κ) (lockHamExpr g.Ω g.cs))
    (hlo : 0 < (g.graph.pLo : ℝ) - g.graph.base.params.disp)
    {w : routeAV2.Wit} (hc : checkTorusCertificateV2 routeAV2 g.graph.base w = true)
    (hg : checkSoGraphK g.graph = true) {ωstar : Fin 2 → ℝ}
    (hω : FreqEncloses 2 g.graph.base.freqBox ωstar)
    (hdio : IsDiophantine (g.graph.base.params.γ : ℝ) (g.graph.base.params.tau : ℝ) ωstar) :
    Nonempty (LockBarrier (g.Ω : ℝ) (lockCentre g.cs)
      ((g.graph.pLo : ℝ) - g.graph.base.params.disp)
      ((g.graph.pHi : ℝ) + g.graph.base.params.disp)) := by
  have hc' := hc
  simp only [checkTorusCertificateV2, checkV2With, landedBase, Bool.and_eq_true] at hc'
  have hs := hc'.1.1.1.1.1.1.1
  exact lockBarrier_of_certifiedK g hΩ hκ hham hlo hs
    (checkHamBounds_sound hs hc'.1.1.1.1.1.1.2).1 hg
    (checkTorusCertificateV2_sound routeAV2 hc hω hdio) hdio

end KAM.SpinOrbit.Data.LockN65

end
