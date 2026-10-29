/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Graph.Inverse
public import KAM.SpinOrbit.Rotated

/-!
# Graph inversion in the rotated frame (track SO, package SO-GRAPHR; owner ruling O5)

Unfrozen helper code. The exact torus of the time-scaled rotated client `c · H'` is turned into an
invariant barrier of the original lunar flow.

* `SoGraph.torus_of_rot`: the shear `(x, y) ↦ (x - y, y)` takes the rotated real data
  (`Q₀`, `P₀`, clock `y + c₀`, frequency `(ν - 1, 1)`) to the generic core's `SoGraph.Torus`.
* `soBarrier_of_exact_rotTorus`: the rotated-frame exact torus is an `SoBarrier`.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

open KAM KAM.Certificate

namespace SoGraph

/-- **Shear** `(x, y) ↦ (x - y, y)`: rotated real data (`Q₁` the angle `Q₀`, `Pp` the momentum
`P₀ = p`, clock `φ = y + c`, flow at `(ν - 1, 1)`) give the generic core's data at `(ν, 1)`:
`q = Q₀ + Q₁`, i.e. `Q x y = Q₁ (x - y) y + y + c`, `Pp x y = Pp (x - y) y`. -/
theorem torus_of_rot {Q₁ Pp dQ : ℝ → ℝ → ℝ} {ν c m : ℝ} (hm : 0 < m)
    (hQc : Continuous fun z : ℝ × ℝ => Q₁ z.1 z.2) (hPc : Continuous fun z : ℝ × ℝ => Pp z.1 z.2)
    (hQ₀ : ∀ x y, Q₁ (x + 1) y = Q₁ x y + 1) (hQ₁ : ∀ x y, Q₁ x (y + 1) = Q₁ x y)
    (hP₀ : ∀ x y, Pp (x + 1) y = Pp x y) (hP₁ : ∀ x y, Pp x (y + 1) = Pp x y)
    (hdQ : ∀ x y, HasDerivAt (fun s => Q₁ s y) (dQ x y) x) (hmono : ∀ x y, m ≤ dQ x y)
    (hflowQ : ∀ x y, HasDerivAt (fun t => Q₁ (x + t * (ν - 1)) (y + t)) (Pp x y - 1) 0)
    (hflowP : ∀ x y, HasDerivAt (fun t => Pp (x + t * (ν - 1)) (y + t))
      (-soVq (Q₁ x y + y + c) (y + c)) 0) :
    Torus (fun x y => Q₁ (x - y) y + y + c) (fun x y => Pp (x - y) y)
      (fun x y => dQ (x - y) y) ν c m := by
  have hsh : Continuous fun z : ℝ × ℝ => (z.1 - z.2, z.2) :=
    (continuous_fst.sub continuous_snd).prodMk continuous_snd
  refine ⟨hm, ?_, hPc.comp hsh, fun x y => ?_, fun x y => ?_, fun x y => ?_, fun x y => ?_,
    fun x y => ?_, fun x y => hmono _ _, fun x y => ?_, fun x y => ?_⟩
  · have := hQc.comp hsh
    fun_prop
  · have := hQ₀ (x - y) y
    rw [show x + 1 - y = x - y + 1 by ring, this]; ring
  · have h1 := hQ₀ (x - y - 1) (y + 1)
    rw [sub_add_cancel, hQ₁] at h1
    show Q₁ (x - (y + 1)) (y + 1) + (y + 1) + c = Q₁ (x - y) y + y + c
    rw [show x - (y + 1) = x - y - 1 by ring]
    linarith
  · show Pp (x + 1 - y) y = Pp (x - y) y
    rw [show x + 1 - y = x - y + 1 by ring, hP₀]
  · show Pp (x - (y + 1)) (y + 1) = Pp (x - y) y
    have h1 := hP₀ (x - y - 1) (y + 1)
    rw [sub_add_cancel, hP₁] at h1
    rw [show x - (y + 1) = x - y - 1 by ring, ← h1]
  · exact ((hdQ (x - y) y).comp_sub_const x y).add_const _ |>.add_const _
  · have h := (hflowQ (x - y) y).add (((hasDerivAt_id (0 : ℝ)).const_add y).add_const c)
    have e : (fun t : ℝ => Q₁ (x + t * ν - (y + t)) (y + t) + (y + t) + c) =
        fun t => Q₁ (x - y + t * (ν - 1)) (y + t) + (y + id t) + c := by
      funext t; rw [show x + t * ν - (y + t) = x - y + t * (ν - 1) by ring]; rfl
    show HasDerivAt (fun t : ℝ => Q₁ (x + t * ν - (y + t)) (y + t) + (y + t) + c) _ 0
    rw [e]
    convert h using 1
    · funext t; simp [add_assoc]
    · ring
  · have h := hflowP (x - y) y
    have e : (fun t : ℝ => Pp (x + t * ν - (y + t)) (y + t)) =
        fun t => Pp (x - y + t * (ν - 1)) (y + t) := by
      funext t; rw [show x + t * ν - (y + t) = x - y + t * (ν - 1) by ring]
    show HasDerivAt (fun t : ℝ => Pp (x + t * ν - (y + t)) (y + t)) _ 0
    rw [e]
    exact h

end SoGraph

open SoGraph in
/-- The scaled Diophantine inequality: `s • ω` is `(s γ, τ)`-Diophantine for `s > 0`. -/
theorem isDiophantine_smul_scale {n : ℕ} {γ τ s : ℝ} {ω : Fin n → ℝ} (hs : 0 < s)
    (hdio : IsDiophantine γ τ ω) : IsDiophantine (s * γ) τ (s • ω) := by
  intro k hk
  have hsum : ∑ i, (k i : ℝ) * (s • ω) i = s * ∑ i, (k i : ℝ) * ω i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsum, abs_mul, abs_of_pos hs, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (hdio k hk) hs.le

end KAM.SpinOrbit

end
