/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.WrapperDatum
public import KAM.Planetary.WeakMeasure.Basic
public import KAM.Head.Frequency

/-!
# Admissibility of `Ĥ_ε` (P11A-P10, `bpP:p11:data-star`, KAM clauses (A1)-(A4))

`p11_wr_qi`: the prepared data `(N_ε, P_ε)` of the full spec, with amount `β ≤ index_def`, is
`QuantitativeInput` for the datum `p11WrDatum D β`.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff
namespace KAM.Planetary

section QI

variable {n : ℕ}

theorem p11_actionNbhd_mono {N : ℕ} (B : Set (Fin N → ℝ)) {r r' : ℝ} (h : r ≤ r') :
    KAM.actionNbhd B r ⊆ KAM.actionNbhd B r' := by
  rintro I ⟨J, hJ, hI⟩
  exact ⟨J, hJ, hI.trans_le h⟩

/-- Real frequency map equals the real part of the complex gradient. -/
theorem p11_freq_eq {N : ℕ} {h : (Fin N → ℂ) → ℂ} {U : Set (Fin N → ℂ)} (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U)
    (hre : ∀ I : Fin N → ℝ, KAM.realInclusion N I ∈ U → (h (KAM.realInclusion N I)).im = 0)
    {I : Fin N → ℝ} (hI : KAM.realInclusion N I ∈ U) :
    frequencyMap h I = fun i => (fderiv ℂ h (KAM.realInclusion N I) (Pi.single i 1)).re := by
  funext i
  have hW : IsOpen (KAM.realInclusion N ⁻¹' U) := hU.preimage (KAM.realInclusion N).continuous
  have := KAM.Head.fderiv_realInclusion_of_real (F := h) (hh.differentiableAt (hU.mem_nhds hI))
    (Filter.eventually_of_mem (hW.mem_nhds hI) fun J hJ => hre J hJ) (Pi.single i 1)
  rw [KAM.Head.realInclusion_single] at this
  rw [this, Complex.ofReal_re]
  rfl

theorem p11_wr_qi {D : P11Physical n} {nu eps c : ℝ} {Q : P11PreparedData n}
    (hspec : P11PreparedFullSpec D nu eps c Q) {β : ℝ}
    (hβ : β ≤ index_def 2 (p11PatchData D).mu (p11PreparedFreqR Q) (p11PreparedBox n)) :
    QuantitativeInput (p11WrDatum D β) Q.N Q.P := by
  have hn : 1 ≤ n + n := by have := D.n_ge; omega
  obtain ⟨hs0, -, -, hjet, -⟩ := hspec
  obtain ⟨-, hNd, hPd, hper, -, hRP, hNre, -, -, hDW, -, -, hop, -⟩ := hs0
  have hU1 : IsOpen (KAM.actionNbhd (p11PreparedBox n) 1) := p11c_zero_isOpen_nbhd _ _
  have hW1 : IsOpen (KAM.realInclusion (n+n) ⁻¹' KAM.actionNbhd (p11PreparedBox n) 1) :=
    hU1.preimage (KAM.realInclusion (n+n)).continuous
  have hfreq : ∀ I, KAM.realInclusion (n+n) I ∈ KAM.actionNbhd (p11PreparedBox n) 1 →
      frequencyMap Q.N I = p11PreparedFreqR Q I := fun I hI => p11_freq_eq hU1 hNd hNre hI
  have hEq : ∀ y, KAM.realInclusion (n+n) y ∈ KAM.actionNbhd (p11PreparedBox n) 1 →
      ∀ c' : P11Vec (n+n), p11scalar 2 (p11PreparedFreqR Q) c' =ᶠ[𝓝 y]
        fun x (_ : Fin 1) => p11c_scalar 2 (frequencyMap Q.N) c' x := fun y hy c' => by
    filter_upwards [hW1.mem_nhds hy] with x hx
    funext _
    simp [p11scalar, p11c_scalar, p11dot, hfreq x hx]
  have hVsub : ∀ y ∈ p11thick (p11PreparedBox n) (1/4),
      KAM.realInclusion (n+n) y ∈ KAM.actionNbhd (p11PreparedBox n) 1 := by
    rintro y ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    show ‖KAM.realInclusion (n+n) y - KAM.realInclusion (n+n) x‖ < 1
    rw [← map_sub, KAM.norm_realInclusion]
    exact lt_of_le_of_lt ((KAM.Nekhoroshev.norm_le_euclid _).1.trans hxy) (by norm_num)
  have hKsub : ∀ y ∈ p11PreparedBox n,
      KAM.realInclusion (n+n) y ∈ KAM.actionNbhd (p11PreparedBox n) 1 := fun y hy =>
    hVsub y ⟨y, hy, by simp [p11euclid_zero]⟩
  have hfc := p11c_zero_contDiffOn_freq hU1 hNd
  have hcd : ∀ y, KAM.realInclusion (n+n) y ∈ KAM.actionNbhd (p11PreparedBox n) 1 →
      ∀ c' : P11Vec (n+n), ContDiffAt ℝ ∞ (p11c_scalar 2 (frequencyMap Q.N) c') y :=
    fun y hy c' => p11c_zero_contDiffAt_scalar hW1 hfc 2 c' hy
  have hiter : ∀ y, KAM.realInclusion (n+n) y ∈ KAM.actionNbhd (p11PreparedBox n) 1 →
      ∀ (c' : P11Vec (n+n)) (j : ℕ) (a : Fin j → P11Vec (n+n)),
      p11euclid (iteratedFDeriv ℝ j (p11scalar 2 (p11PreparedFreqR Q) c') y a) =
        |iteratedFDeriv ℝ j (p11c_scalar 2 (frequencyMap Q.N) c') y a| := by
    intro y hy c' j a
    rw [((hEq y hy c').iteratedFDeriv ℝ j).self_of_nhds]
    exact p11c_zero_euclid_iter (hcd y hy c') j a
  have hmono : KAM.actionNbhd (p11PreparedBox n) (2*(1/4)) ⊆
      KAM.actionNbhd (p11PreparedBox n) 1 := p11_actionNbhd_mono _ (by norm_num)
  refine ⟨hNd.mono hmono, hPd.mono (Set.prod_mono subset_rfl hmono), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz k
    exact p11_periodic_int hper z ⟨hz.1, hmono hz.2⟩ k
  · intro y hy
    exact hNre y (hmono hy)
  · intro z hz
    exact hRP z ⟨hz.1, hmono hz.2⟩
  · intro c' hc' y hy
    have hy' := hKsub y hy
    have h1 : β ≤ p11maxJet (p11PatchData D).mu (p11scalar 2 (p11PreparedFreqR Q) c') y :=
      hβ.trans (index_def_le 2 _ _ hc' hy)
    obtain ⟨j, hj, hjeq⟩ := p11maxJet_attained (f := p11scalar 2 (p11PreparedFreqR Q) c')
      (y := y) (p11PatchData D).mu
    obtain ⟨a, ha, haeq⟩ := p11dg_attained (p11scalar 2 (p11PreparedFreqR Q) c') j y hn
    refine ⟨j, hj, a, ha, ?_⟩
    show β ≤ |iteratedFDeriv ℝ j (p11c_scalar 2 (frequencyMap Q.N) c') y (fun _ => a)|
    rw [← hiter y hy' c' j (fun _ => a), ← haeq, ← hjeq]
    exact h1
  · intro c' hc' j hj1 hj2 y hy v hv
    have hy' := hVsub y hy
    have h1 := (le_p11op (p11scalar 2 (p11PreparedFreqR Q) c') j y v hv).trans
      (hop c' hc' j hj1 hj2 y hy)
    rw [hiter y hy' c' j v] at h1
    exact h1
  · intro y hy
    exact hDW y (p11_actionNbhd_mono _ (by norm_num : (2*(1/4) : ℝ) ≤ 3/4) hy)
  · intro j hj y hy v hv
    have hy' := hVsub y hy
    have h0 : p11dg (p11PreparedFreqR Q) j y ≤ p11M0 n (p11PatchData D).mu
        (p11SecularData D).L := by simpa using hjet j hj y hy
    have hev : frequencyMap Q.N =ᶠ[𝓝 y] p11PreparedFreqR Q := by
      filter_upwards [hW1.mem_nhds hy'] with x hx using hfreq x hx
    have := (hev.iteratedFDeriv ℝ j).self_of_nhds
    show p11euclid _ ≤ _
    rw [this]
    exact (le_p11dg (p11PreparedFreqR Q) j y v hv).trans h0

end QI

end KAM.Planetary

end
