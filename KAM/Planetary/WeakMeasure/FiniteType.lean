/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakMeasure.Basic
public import KAM.Planetary.Nondegeneracy.FiniteType

/-!
# Weak-measure finite type: port of Part 10 (P11A-W2b)

Blueprint P, Part 11a (`bpP:p11a:rank-compact`). The Part 10 declarations `finite_type`,
`cp09_lemma1`, `cp09_unsquared` (and `rnd_def`) already exist in
`KAM.Planetary.Nondegeneracy`; they are imported, not redefined. This module identifies the Part 10
jet maximum `jetMax` and infimum `betaFamily` with the Part 11a gauge `p11maxJet` and amount
`index_def`, and derives the existence of a finite positive order, `rank_compact`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace KAM.Planetary
open Nondegeneracy

variable {n m : ℕ}

theorem p11euclid_eq_length2 (x : P11Vec n) : p11euclid x = SecularSpectrum.length2 x := by
  simp [p11euclid, KAM.Nekhoroshev.euclid, SecularSpectrum.length2]

/-- The order-`j` gauge of a scalar function, as a one-component map, is Part 10's
`scalarJet`. -/
theorem p11dg_scalar_eq_scalarJet (hn : 1 ≤ n) (g : P11Vec n → ℝ) (j : ℕ) (y : P11Vec n) :
    p11dg (fun (x : P11Vec n) (_ : Fin 1) => g x) j y = scalarJet g j y := by
  let e : ℝ ≃ₗᵢ[ℝ] (Fin 1 → ℝ) := { (LinearEquiv.funUnique (Fin 1) ℝ ℝ).symm with
      norm_map' := fun r => by simp [Pi.norm_def] }
  have hf : (fun (x : P11Vec n) (_ : Fin 1) => g x) = e.toContinuousLinearEquiv ∘ g := rfl
  have hval : ∀ a : P11Vec n, p11euclid (iteratedFDeriv ℝ j
      (fun (x : P11Vec n) (_ : Fin 1) => g x) y (fun _ => a)) =
      |iteratedFDeriv ℝ j g y (fun _ => a)| := fun a => by
    rw [hf, (e.toContinuousLinearEquiv).iteratedFDeriv_comp_left]
    simp [p11euclid, KAM.Nekhoroshev.euclid, e, Real.sqrt_sq_eq_abs]
  unfold p11dg scalarJet
  obtain ⟨a0, ha0⟩ := p11sphere_nonempty hn
  have hset : {v | ∃ a : P11Vec n, p11euclid a = 1 ∧ v = p11euclid (iteratedFDeriv ℝ j
      (fun (x : P11Vec n) (_ : Fin 1) => g x) y (fun _ => a))} =
      {r | ∃ v : P11Vec n, SecularSpectrum.length2 v = 1 ∧
        r = |iteratedFDeriv ℝ j g y (fun _ => v)|} := by
    ext r
    simp only [mem_ofPred_eq, hval, p11euclid_eq_length2]
  rw [hset]
  split_ifs with h0
  · subst h0
    have : {r | ∃ v : P11Vec n, SecularSpectrum.length2 v = 1 ∧
        r = |iteratedFDeriv ℝ 0 g y (fun _ => v)|} = {|g y|} := by
      ext r
      refine ⟨fun ⟨v, _, hr⟩ => ?_, fun hr => ⟨a0, by rw [← p11euclid_eq_length2]; exact ha0, ?_⟩⟩
      · simpa [iteratedFDeriv_zero_apply] using hr
      · simpa [iteratedFDeriv_zero_apply] using hr
    rw [this, csSup_singleton]
  · rfl

theorem p11maxJet_scalar_eq_jetMax (hn : 1 ≤ n) (g : P11Vec n → ℝ) (mu : ℕ) (y : P11Vec n) :
    p11maxJet mu (fun (x : P11Vec n) (_ : Fin 1) => g x) y = jetMax g mu y := by
  unfold p11maxJet jetMax
  congr 1
  ext v
  simp only [mem_ofPred_eq, mem_image, p11dg_scalar_eq_scalarJet hn]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

theorem index_def_eq_betaFamily (hn : 1 ≤ n) (rho mu : ℕ) (w : P11Vec n → P11Vec m)
    (K : Set (P11Vec n)) :
    index_def rho mu w K =
      betaFamily (fun c y => (∑ i, c i * w y i) ^ rho) (sphere m) K mu := by
  unfold index_def betaFamily
  congr 1
  ext v
  simp only [mem_ofPred_eq, mem_image, mem_prod, Prod.exists, sphere]
  constructor
  · rintro ⟨c, hc, y, hy, rfl⟩
    exact ⟨c, y, ⟨by rwa [← p11euclid_eq_length2], hy⟩,
      (p11maxJet_scalar_eq_jetMax hn _ mu y).symm⟩
  · rintro ⟨c, y, ⟨hc, hy⟩, rfl⟩
    exact ⟨c, by rwa [p11euclid_eq_length2], y, hy, (p11maxJet_scalar_eq_jetMax hn _ mu y).symm⟩

theorem rank_compact {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    {V K : Set (P11Vec n)} (hV : IsOpen V) (hconn : IsPreconnected V)
    (hK : IsCompact K) (hne : K.Nonempty) (hsub : K ⊆ V)
    {w : P11Vec n → P11Vec m} (hw : AnalyticOnNhd ℝ w V)
    (hr : p11RNondegenerate V w) {rho : ℕ} (hp : rho=1 ∨ rho=2) :
    ∃ mu : ℕ, 1 ≤ mu ∧ 0 < index_def rho mu w K := by
  have hVc : IsConnected V := ⟨hne.mono hsub, hconn⟩
  have hR : rnd_def V w := hr
  rcases hp with rfl | rfl
  · obtain ⟨mu, hmu, hb⟩ := cp09_unsquared hm hV hVc hK hne hsub hw hR
    refine ⟨mu, hmu, ?_⟩
    rw [index_def_eq_betaFamily hn]
    simpa using hb
  · obtain ⟨mu, hmu, hb, -⟩ := cp09_lemma1 hm hV hVc hK hne hsub hw hR
    refine ⟨mu, hmu, ?_⟩
    rw [index_def_eq_betaFamily hn]
    exact hb

end KAM.Planetary
