/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Hamiltonian.Transport
public import KAM.Planetary.Poincare.Lattice
public import KAM.Planetary.SecularSpectrum.Lift

/-!
# Secular spectrum: transport of the rotated physical chart

Blueprint P, Part 9 (`bpP:p9:diagonalize`, the transport step; package S9-T). The rotated physical
chart is `Ψ ∘ liftInv R ∘ polarMap ∘ phaseCast`, with `Ψ = poincareProd`. `diagonalize_transport`
shows it is an analytic symplectic chart (`IsChart 1`) on an open domain with the radian lattice
properties (Q1) and (Q2) for `fullShift`; `diagonalize_period_one` feeds them to `phys_pipeline`,
converting the radian torus to a period-one physical torus. The only translation fact needed of the
lift is its equivariance for constant shifts of the fast angles (`liftInv_add_append`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

theorem isOpen_polarDom (n : ℕ) : IsOpen (polarDom n) := by
  have : polarDom n = ⋂ i : Fin n, ({z : Phase (n + n) | 0 < fast z.2 i} ∩
      {z | 0 < slow z.2 i} ∩ {z | slow z.2 i < fast z.2 i}) := by
    ext z; simp [polarDom, and_assoc]
  rw [this]
  refine isOpen_iInter_of_finite fun i => ?_
  have h1 : Continuous fun z : Phase (n + n) => fast z.2 i := by unfold fast; fun_prop
  have h2 : Continuous fun z : Phase (n + n) => slow z.2 i := by unfold slow; fun_prop
  exact ((isOpen_lt continuous_const h1).inter (isOpen_lt continuous_const h2)).inter
    (isOpen_lt h2 h1)

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

lemma liftInv_add_append (R : Vec n → Mat n) (w : Phase (n+n)) (c : Vec n) :
    liftInv R (w + ((Fin.append c (0 : Vec n) : Fin (n+n) → ℝ), (0 : Fin (n+n) → ℝ))) =
      liftInv R w + ((Fin.append c (0 : Vec n) : Fin (n+n) → ℝ), (0 : Fin (n+n) → ℝ)) := by
  have hf : fast (w + ((Fin.append c (0 : Vec n) : Fin (n+n) → ℝ), (0 : Fin (n+n) → ℝ))).2 =
      fast w.2 := by funext i; simp [fast]
  have hs : slow (w + ((Fin.append c (0 : Vec n) : Fin (n+n) → ℝ), (0 : Fin (n+n) → ℝ))).2 =
      slow w.2 := by funext i; simp [slow]
  have hs1 : slow (w + ((Fin.append c (0 : Vec n) : Fin (n+n) → ℝ), (0 : Fin (n+n) → ℝ))).1 =
      slow w.1 := by funext i; simp [slow]
  have hf1 : fast (w + ((Fin.append c (0 : Vec n) : Fin (n+n) → ℝ), (0 : Fin (n+n) → ℝ))).1 =
      fast w.1 + c := by funext i; simp [fast]
  rw [liftInv, liftInv, assemble_add_append]
  simp only [hf, hs, hs1, hf1]
  congr 1
  funext l
  simp only [Pi.add_apply]
  ring

lemma liftInv_add_fastShift (R : Vec n → Mat n) (w : Phase (n+n)) (k : Fin n → ℤ) :
    liftInv R (w + fastShift (a := n) (b := n) k) =
      liftInv R w + fastShift (a := n) (b := n) k :=
  liftInv_add_append R w (fun i => 2 * π * (k i : ℝ))

lemma fast_snd_add_fastShift (w : Phase (n+n)) (k : Fin n → ℤ) :
    fast (w + fastShift (a := n) (b := n) k).2 = fast w.2 := by
  funext i; simp [fast, fastShift]

lemma fast_snd_polarMap (w : Phase (n+n)) : fast (polarMap w).2 = fast w.2 := by
  funext i; simp [polarMap, fast_snd_assemble]

lemma phaseCast_fullShift (k : Fin (n*2) → ℤ) :
    phaseCast (Nat.mul_two n) (fullShift k) =
      fullShift (fun i : Fin (n+n) => k (Fin.cast (Nat.mul_two n).symm i)) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · simp [(phaseCast_apply (Nat.mul_two n) _ i).1, fullShift]
  · simp [(phaseCast_apply (Nat.mul_two n) _ i).2, fullShift]

lemma phaseCast_symm_fullShift (k : Fin (n+n) → ℤ) :
    (phaseCast (Nat.mul_two n)).symm (fullShift k) =
      fullShift (fun i : Fin (n*2) => k (Fin.cast (Nat.mul_two n) i)) := by
  apply (phaseCast (Nat.mul_two n)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, phaseCast_fullShift]
  congr 1

/-- The lift acts injectively on its domain. -/
lemma liftInv_injOn {W : Set (Vec n)} {R : Vec n → Mat n} (hR : ∀ I ∈ W, isSO (R I))
    {u v : Phase (n+n)} (hu : fast u.2 ∈ W) (hv : fast v.2 ∈ W)
    (h : liftInv R u = liftInv R v) : u = v := by
  have h1 := liftMap_liftInv_of_isSO (R := R) (w := u) (hR _ hu)
  have h2 := liftMap_liftInv_of_isSO (R := R) (w := v) (hR _ hv)
  rw [← h1, ← h2, h]

end SecularSpectrum

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

def rotatedPhysicalChart (D : Data n) (R : Vec n → Mat n) : Phase (n*2) → Phase (n*2) :=
  poincareProd D.m (D.G*D.m0) ∘ liftInv R ∘ polarMap ∘ phaseCast (Nat.mul_two n)
def rotatedDomain (R : Vec n → Mat n) (W : Set (Vec n)) : Set (Phase (n*2)) :=
  {z | let w := phaseCast (Nat.mul_two n) z
    w ∈ polarDom n ∧ fast w.2 ∈ W ∧ liftInv R (polarMap w) ∈ poincareProdDom n}

/-- The domain on `Phase (n+n)` before the reindexing. -/
private def rotatedDomain' (R : Vec n → Mat n) (W : Set (Vec n)) : Set (Phase (n+n)) :=
  {w | w ∈ polarDom n ∧ fast w.2 ∈ W ∧ liftInv R (polarMap w) ∈ poincareProdDom n}

private lemma rotatedDomain_eq (R : Vec n → Mat n) (W : Set (Vec n)) :
    rotatedDomain R W = phaseCast (Nat.mul_two n) ⁻¹' rotatedDomain' R W := rfl

private lemma polarMap_mem_liftDomain {W : Set (Vec n)} {w : Phase (n+n)} (h : fast w.2 ∈ W) :
    polarMap w ∈ liftDomain W := by
  show fast (polarMap w).2 ∈ W
  rwa [fast_snd_polarMap]

private lemma isOpen_rotatedDomain' {W : Set (Vec n)} (hW : IsOpen W) {R : Vec n → Mat n}
    (hAn : AnalyticOnNhd ℝ R W) (hR : ∀ I ∈ W, isSO (R I)) :
    IsOpen (rotatedDomain' R W) := by
  obtain ⟨-, hL, -⟩ := lift hW hAn hR
  have hU : IsOpen (polarDom n ∩ {w : Phase (n+n) | fast w.2 ∈ W}) := by
    refine (isOpen_polarDom n).inter ?_
    exact (isOpen_liftDomain hW)
  have hc : ContinuousOn (liftInv R ∘ polarMap)
      (polarDom n ∩ {w : Phase (n+n) | fast w.2 ∈ W}) :=
    hL.continuousOn.comp ((analyticOnNhd_polarMap n).continuousOn.mono inter_subset_left)
      (fun w hw => polarMap_mem_liftDomain hw.2)
  have := hc.isOpen_inter_preimage hU (isOpen_poincareProdDom n)
  convert this using 1
  ext w
  simp only [rotatedDomain', mem_ofPred_eq, mem_inter_iff, mem_preimage, comp_apply]
  tauto

private lemma rotatedChart'_isChart (D : Data n) {W : Set (Vec n)} (hW : IsOpen W)
    {R : Vec n → Mat n} (hAn : AnalyticOnNhd ℝ R W) (hR : ∀ I ∈ W, isSO (R I)) :
    AnalyticOnNhd ℝ (poincareProd D.m (D.G*D.m0) ∘ liftInv R ∘ polarMap) (rotatedDomain' R W) ∧
    IsSymplecticOn 1 (poincareProd D.m (D.G*D.m0) ∘ liftInv R ∘ polarMap) (rotatedDomain' R W) := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  obtain ⟨-, hLi, -, hLis, -, -⟩ := lift hW hAn hR
  have hmaps : MapsTo polarMap (rotatedDomain' R W) (liftDomain W) :=
    fun w hw => polarMap_mem_liftDomain hw.2.1
  have hsub : rotatedDomain' R W ⊆ polarDom n := fun w hw => hw.1
  have hg : AnalyticOnNhd ℝ (liftInv R ∘ polarMap) (rotatedDomain' R W) :=
    hLi.comp ((analyticOnNhd_polarMap n).mono hsub) hmaps
  have hgm : MapsTo (liftInv R ∘ polarMap) (rotatedDomain' R W) (poincareProdDom n) :=
    fun w hw => hw.2.2
  refine ⟨(analyticOnNhd_poincareProd D.hm hκ).comp hg hgm, ?_⟩
  have h1 : IsSymplecticOn (1 * 1) (liftInv R ∘ polarMap) (rotatedDomain' R W) :=
    IsSymplecticOn.comp (fun z hz => polarMap_symplectic n z (hsub hz)) hLis
      (fun z hz => (analyticOnNhd_polarMap n z (hsub hz)).differentiableAt)
      (fun z hz => (hLi z hz).differentiableAt) hmaps
  rw [mul_one] at h1
  have h2 := IsSymplecticOn.comp h1 (poincareProd_symplectic D.hm hκ)
    (fun z hz => (hg z hz).differentiableAt)
    (fun z hz => ((analyticOnNhd_poincareProd D.hm hκ) z hz).differentiableAt) hgm
  rwa [mul_one] at h2

private lemma rotated_shift (D : Data n) {W : Set (Vec n)} {R : Vec n → Mat n}
    {w : Phase (n+n)} (hw : w ∈ rotatedDomain' R W) (k : Fin (n+n) → ℤ) :
    w + fullShift k ∈ rotatedDomain' R W ∧
      poincareProd D.m (D.G*D.m0) (liftInv R (polarMap (w + fullShift k))) =
        poincareProd D.m (D.G*D.m0) (liftInv R (polarMap w)) := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have hf : fast (w + fullShift k).2 = fast w.2 := by funext i; simp [fast, fullShift]
  have hv : liftInv R (polarMap (w + fullShift k)) = liftInv R (polarMap w) +
      fastShift (a := n) (b := n) (fun i => k (Fin.castAdd n i)) := by
    rw [polarMap_shift, liftInv_add_fastShift]
  obtain ⟨h1, h2⟩ := poincareProd_lattice D.hm hκ hw.2.2 (fun i => k (Fin.castAdd n i))
  refine ⟨⟨polarDom_shift k hw.1, by rw [hf]; exact hw.2.1, by rw [hv]; exact h1⟩, ?_⟩
  rw [hv, h2]

private lemma rotated_inj (D : Data n) {W : Set (Vec n)} {R : Vec n → Mat n}
    (hR : ∀ I ∈ W, isSO (R I)) {w w' : Phase (n+n)} (hw : w ∈ rotatedDomain' R W)
    (hw' : w' ∈ rotatedDomain' R W)
    (h : poincareProd D.m (D.G*D.m0) (liftInv R (polarMap w')) =
      poincareProd D.m (D.G*D.m0) (liftInv R (polarMap w))) :
    ∃ k : Fin (n+n) → ℤ, w' = w + fullShift k := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  obtain ⟨a, ha⟩ := (poincareProd_eq_iff D.hm hκ hw.2.2 hw'.2.2).1 h.symm
  have h1 : polarMap w' = polarMap w + fastShift (a := n) (b := n) a := by
    refine liftInv_injOn hR (u := polarMap w') (v := polarMap w + fastShift (a := n) (b := n) a)
      ?_ ?_ ?_
    · rw [fast_snd_polarMap]; exact hw'.2.1
    · rw [fast_snd_add_fastShift, fast_snd_polarMap]; exact hw.2.1
    · rw [liftInv_add_fastShift]; exact ha
  exact polarMap_eq_shift hw.1 hw'.1 h1

theorem diagonalize_transport (D : Data n) {W : Set (Vec n)} (hW : IsOpen W)
    {R : Vec n → Mat n} (hAn : AnalyticOnNhd ℝ R W) (hR : ∀ I ∈ W, isSO (R I)) :
    IsOpen (rotatedDomain R W) ∧ IsChart 1 (rotatedPhysicalChart D R) (rotatedDomain R W) ∧
    (∀ z ∈ rotatedDomain R W, ∀ k : Fin (n*2) → ℤ,
      z+fullShift k ∈ rotatedDomain R W ∧
      rotatedPhysicalChart D R (z+fullShift k) = rotatedPhysicalChart D R z) ∧
    (∀ z ∈ rotatedDomain R W, ∀ z' ∈ rotatedDomain R W,
      rotatedPhysicalChart D R z' = rotatedPhysicalChart D R z →
      ∃ k : Fin (n*2) → ℤ, z' = z+fullShift k) := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  obtain ⟨hLm, hLi, -, hLis, -, -⟩ := lift hW hAn hR
  have hmem : ∀ {w : Phase (n+n)}, w ∈ rotatedDomain' R W → polarMap w ∈ liftDomain W :=
    fun hw => polarMap_mem_liftDomain hw.2.1
  refine ⟨(isOpen_rotatedDomain' hW hAn hR).preimage (phaseCast (Nat.mul_two n)).continuous,
    ?_, ?_, ?_⟩
  · obtain ⟨han, hsy⟩ := rotatedChart'_isChart D hW hAn hR
    refine ⟨han.comp ((phaseCast_analytic (Nat.mul_two n)).mono (subset_univ _))
      (fun z hz => hz), ?_⟩
    have h1 : IsSymplecticOn 1 (phaseCast (Nat.mul_two n)) (rotatedDomain R W) :=
      fun z _ => phaseCast_symplectic (Nat.mul_two n) z (mem_univ _)
    have h := IsSymplecticOn.comp h1 hsy
      (fun z _ => (phaseCast (Nat.mul_two n)).differentiableAt)
      (fun z hz => (han z hz).differentiableAt) (fun z hz => hz)
    rwa [mul_one] at h
  · intro z hz k
    have hc : phaseCast (Nat.mul_two n) (z + fullShift k) = phaseCast (Nat.mul_two n) z +
        fullShift (fun i : Fin (n+n) => k (Fin.cast (Nat.mul_two n).symm i)) := by
      rw [map_add, phaseCast_fullShift]
    obtain ⟨h1, h2⟩ := rotated_shift D
      (k := fun i : Fin (n+n) => k (Fin.cast (Nat.mul_two n).symm i)) hz
    refine ⟨by rw [rotatedDomain_eq, mem_preimage, hc]; exact h1, ?_⟩
    simp only [rotatedPhysicalChart, comp_apply, hc]
    exact h2
  · intro z hz z' hz' h
    obtain ⟨k, hk⟩ := rotated_inj D hR hz hz' h
    refine ⟨fun i : Fin (n*2) => k (Fin.cast (Nat.mul_two n) i), ?_⟩
    apply (phaseCast (Nat.mul_two n)).injective
    rw [map_add, hk, phaseCast_fullShift]
    congr 2

theorem diagonalize_period_one (D : Data n) {W : Set (Vec n)} (hW : IsOpen W)
    {R : Vec n → Mat n} (hAn : AnalyticOnNhd ℝ R W) (hR : ∀ I ∈ W, isSO (R I))
    (H : Phase (n*2) → ℝ) (κ : (Fin (n*2) → ℝ) → Phase (n*2)) (ω : Fin (n*2) → ℝ)
    (hκ : IsTwoPiLatticeTorus (H ∘ rotatedPhysicalChart D R) (rotatedDomain R W) ω κ)
    {γ τ : ℝ} (hγ : 0 < γ) (hτ : ((n*2 : ℕ) : ℝ)-1 < τ) (hω : IsDiophantine γ τ ω) :
    IsPhysicalTorus H ((2*π)⁻¹ • ω) (rotatedPhysicalChart D R ∘ periodOne κ) ∧
      range (rotatedPhysicalChart D R ∘ periodOne κ) = rotatedPhysicalChart D R '' range κ := by
  obtain ⟨-, hΦ, hQ1, hQ2⟩ := diagonalize_transport D hW hAn hR
  exact phys_pipeline hΦ (fun z hz k => hQ1 z hz k)
    (fun z hz z' hz' h => hQ2 z hz z' hz' h) hκ hγ hτ hω

end SecularSpectrum

end KAM.Planetary

end
