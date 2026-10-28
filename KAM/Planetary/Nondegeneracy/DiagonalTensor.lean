/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.Norms

/-!
# Nondegeneracy: diagonal tensor norms, polarization and the Leibniz formula

Blueprint P, Part 10 (`bpP:p10:sec-index#data`, `bpP:p10:f-pol`, `bpP:p10:f-leib`): the CP09
diagonal Euclidean tensor norms `jetNorm`, `scalarJet`, `jetMax` (with the separate order-zero
convention), the polarization fact `f_pol` for symmetric continuous multilinear forms and the
Leibniz formula `f_leib` for the diagonal derivative of a product of analytic functions.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {d m : ℕ}

/-- CP09 diagonal Euclidean tensor norm, with the separate order-zero convention. -/
def jetNorm {m : ℕ} (f : Vec d → Vec m) (ν : ℕ) (y : Vec d) : ℝ :=
  if ν = 0 then length2 (f y) else
    sSup {r | ∃ v : Vec d, length2 v = 1 ∧ r = length2 (iteratedFDeriv ℝ ν f y (fun _ => v))}
def scalarJet (g : Vec d → ℝ) (ν : ℕ) (y : Vec d) : ℝ :=
  if ν = 0 then |g y| else
    sSup {r | ∃ v : Vec d, length2 v = 1 ∧ r = |iteratedFDeriv ℝ ν g y (fun _ => v)|}
def jetMax (g : Vec d → ℝ) (μ : ℕ) (y : Vec d) : ℝ :=
  sSup ((fun ν => scalarJet g ν y) '' {ν | ν ≤ μ})

/-! ### Polarization -/

/-- The derivative of the diagonal along a line. -/
lemma hasDerivAt_diag {ν : ℕ} (T : (Fin d → ℝ) [×ν]→L[ℝ] ℝ) (x w : Fin d → ℝ) :
    HasDerivAt (fun s : ℝ => T (fun _ => x + s • w))
      (∑ i, T (Function.update (fun _ => x) i w)) 0 := by
  classical
  have h1 : HasDerivAt (fun s : ℝ => fun _ : Fin ν => x + s • w) (fun _ => w) 0 :=
    hasDerivAt_pi.2 fun _ => by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
  have h2 := (T.hasFDerivAt (fun _ => x + (0 : ℝ) • w)).comp_hasDerivAt (0 : ℝ) h1
  simp only [ContinuousMultilinearMap.linearDeriv_apply, zero_smul, add_zero] at h2
  exact h2

/-- A symmetric form with vanishing diagonal has vanishing mixed diagonal. -/
lemma sum_update_eq_zero {ν : ℕ} (T : (Fin d → ℝ) [×ν]→L[ℝ] ℝ)
    (h : ∀ v : Fin d → ℝ, T (fun _ => v) = 0) (x w : Fin d → ℝ) :
    ∑ i, T (Function.update (fun _ => x) i w) = 0 := by
  have h0 : (fun s : ℝ => T (fun _ => x + s • w)) = fun _ => 0 := funext fun s => h _
  have := hasDerivAt_diag T x w
  rw [h0] at this
  exact this.unique (hasDerivAt_const _ _)

/-- Symmetry makes every term of the mixed diagonal sum equal to the one in the first slot. -/
lemma sum_update_eq {n : ℕ} (T : (Fin d → ℝ) [×(n + 1)]→L[ℝ] ℝ)
    (hSym : ∀ (p : Equiv.Perm (Fin (n + 1))) (v : Fin (n + 1) → (Fin d → ℝ)), T (v ∘ p) = T v)
    (x w : Fin d → ℝ) :
    ∑ i, T (Function.update (fun _ => x) i w) =
      (n + 1 : ℝ) * T (Fin.cons w (fun _ : Fin n => x)) := by
  have hi : ∀ i, T (Function.update (fun _ => x) i w) = T (Fin.cons w (fun _ : Fin n => x)) := by
    intro i
    have : Function.update (fun _ : Fin (n + 1) => x) i w =
        (Fin.cons w (fun _ : Fin n => x) : Fin (n + 1) → Fin d → ℝ) ∘ Equiv.swap 0 i := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · have h0 : Equiv.swap (0 : Fin (n + 1)) i j ≠ 0 := by
          intro h
          exact hj (by simpa using (Equiv.swap_apply_eq_iff.1 h).symm ▸ rfl)
        obtain ⟨k, hk⟩ := Fin.exists_succ_eq.2 h0
        simp [Function.update_of_ne hj, ← hk]
    rw [this, hSym]
  simp [hi, Finset.sum_const, nsmul_eq_mul]

/-- Polarization, by induction on the order. -/
lemma pol_aux (d : ℕ) : ∀ (n : ℕ) (T : (Fin d → ℝ) [×n]→L[ℝ] ℝ),
    (∀ (p : Equiv.Perm (Fin n)) (v : Fin n → (Fin d → ℝ)), T (v ∘ p) = T v) →
    (∀ v : Fin d → ℝ, T (fun _ => v) = 0) → T = 0 := by
  intro n
  induction n with
  | zero =>
    intro T _ h
    ext m
    have : m = fun _ => 0 := funext fun i => i.elim0
    rw [this]
    simpa using h 0
  | succ n ih =>
    intro T hSym h
    have key : ∀ w, T.curryLeft w = 0 := by
      intro w
      refine ih _ ?_ ?_
      · intro p v
        rw [ContinuousMultilinearMap.curryLeft_apply, ContinuousMultilinearMap.curryLeft_apply]
        have : (Fin.cons w (v ∘ p) : Fin (n + 1) → Fin d → ℝ) =
            (Fin.cons w v : Fin (n + 1) → Fin d → ℝ) ∘ Equiv.Perm.decomposeFin.symm (0, p) := by
          funext i
          refine Fin.cases ?_ (fun k => ?_) i <;> simp
        rw [this, hSym]
      · intro x
        have h1 := sum_update_eq T hSym x w
        rw [sum_update_eq_zero T h x w] at h1
        have h2 : T (Fin.cons w (fun _ : Fin n => x)) = 0 := by
          have : (n + 1 : ℝ) ≠ 0 := by positivity
          exact (mul_eq_zero.1 h1.symm).resolve_left this
        simpa using h2
    ext m
    have := congrArg (fun S => S (Fin.tail m)) (key (m 0))
    simpa [ContinuousMultilinearMap.curryLeft_apply] using this

theorem f_pol {ν : ℕ} (T : (Fin d → ℝ) [×ν]→L[ℝ] ℝ)
    (hSym : ∀ (p : Equiv.Perm (Fin ν)) (v : Fin ν → (Fin d → ℝ)), T (v ∘ p) = T v) :
    T = 0 ↔ ∀ v : Fin d → ℝ, T (fun _ => v) = 0 := by
  refine ⟨fun h v => by simp [h], pol_aux d ν T hSym⟩

/-! ### Leibniz formula -/

/-- The diagonal derivative of a smooth function on an open set is the one-variable derivative
along the line. -/
lemma iteratedFDeriv_diag_eq {B : Set (Fin d → ℝ)} (hB : IsOpen B) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ⊤ f B) {y : Fin d → ℝ} (hy : y ∈ B) (v : Fin d → ℝ) (k : ℕ) :
    iteratedFDeriv ℝ k f y (fun _ => v) = iteratedDeriv k (fun t : ℝ => f (y + t • v)) 0 := by
  set L : ℝ →L[ℝ] (Fin d → ℝ) := ContinuousLinearMap.toSpanSingleton ℝ v with hL
  set B' : Set (Fin d → ℝ) := (fun z => y + z) ⁻¹' B with hB'
  have hB'o : IsOpen B' := hB.preimage (continuous_const.add continuous_id)
  have h0 : (0 : Fin d → ℝ) ∈ B' := by simpa [hB'] using hy
  have hf2 : ContDiffOn ℝ ⊤ (fun z => f (y + z)) B' :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn fun z hz => hz
  have hLo : IsOpen (L ⁻¹' B') := hB'o.preimage L.continuous
  have hLm : (0 : ℝ) ∈ L ⁻¹' B' := by simpa using h0
  have h3 := L.iteratedFDerivWithin_comp_right (n := ⊤) hf2 hB'o.uniqueDiffOn
    hLo.uniqueDiffOn (x := 0) (by simpa using h0) (i := k) (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen k hLo hLm,
    iteratedFDerivWithin_of_isOpen k hB'o (by simpa using h0)] at h3
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have h4 : (fun t : ℝ => f (y + t • v)) = (fun z => f (y + z)) ∘ L := by
    funext t; simp [hL]
  rw [h4, h3, iteratedFDeriv_comp_add_left]
  simp [hL]

theorem f_leib {B : Set (Fin d → ℝ)} (hB : IsOpen B) {f g : (Fin d → ℝ) → ℝ}
    (hf : AnalyticOnNhd ℝ f B) (hg : AnalyticOnNhd ℝ g B)
    {y : Fin d → ℝ} (hy : y ∈ B) (v : Fin d → ℝ) (ν : ℕ) :
    iteratedFDeriv ℝ ν (fun z => f z*g z) y (fun _ => v) =
      ∑ k ∈ Finset.range (ν+1), (ν.choose k : ℝ) *
        iteratedFDeriv ℝ k f y (fun _ => v) * iteratedFDeriv ℝ (ν-k) g y (fun _ => v) := by
  have hf' : ContDiffOn ℝ ⊤ f B := hf.contDiffOn hB.uniqueDiffOn
  have hg' : ContDiffOn ℝ ⊤ g B := hg.contDiffOn hB.uniqueDiffOn
  have hfg : ContDiffOn ℝ ⊤ (fun z => f z * g z) B := hf'.mul hg'
  have hA : ContDiff ℝ ⊤ (fun t : ℝ => y + t • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hc : ∀ h : (Fin d → ℝ) → ℝ, ContDiffOn ℝ ⊤ h B →
      ContDiffAt ℝ ν (fun t : ℝ => h (y + t • v)) 0 := by
    intro h hh
    have hy' : ContDiffAt ℝ ⊤ h (y + (0 : ℝ) • v) := by
      simpa using hh.contDiffAt (hB.mem_nhds hy)
    exact (hy'.comp (0 : ℝ) hA.contDiffAt).of_le le_top
  rw [iteratedFDeriv_diag_eq hB hfg hy v ν]
  have hm := iteratedDeriv_fun_mul (n := ν) (x := (0 : ℝ)) (hc f hf') (hc g hg')
  refine hm.trans (Finset.sum_congr rfl fun k hk => ?_)
  rw [iteratedFDeriv_diag_eq hB hf' hy v k, iteratedFDeriv_diag_eq hB hg' hy v (ν - k)]

end Nondegeneracy
end KAM.Planetary
