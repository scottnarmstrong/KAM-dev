/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.Hw.C0
public import KAM.EffectiveStability.SJSU.Ham.Hw.H1
public import KAM.EffectiveStability.SJSU.Ham.Hw.H2
public import KAM.EffectiveStability.SJSU.Ham.Hw.H3
public import KAM.EffectiveStability.SJSU.Ham.Hw.H4
public import KAM.EffectiveStability.SJSU.Ham.Hw.H5
public import KAM.EffectiveStability.SJSU.Ham.Hw.H6
public import KAM.EffectiveStability.SJSU.Ham.Hw.H7
public import KAM.EffectiveStability.SJSU.Ham.Hw.H8
public import KAM.EffectiveStability.SJSU.Ham.Hw.H9
public import Mathlib.Tactic.IntervalCases

/-!
# The modal Hamiltonian `H_w` of `SJSU18-O2` (T2-CONF, N5a)

`sjsuHw d` is the literal integer form of `H_w = H_z ∘ (z = V′ w)` in degree `d`: rows
`((b, b'), c)` with coefficient `c / (N^{2d} 10^E)` of `w^b w̄^{b'}` (`denseRows` of the dense
matrix `sjsuH<d>` along the monomials `sjsuA<d>`). It is checked in the kernel row by row as
`Sᵀ (C S)` (`sjsuH<d>_eval`); `bevalAt_sjsuIntChunks` collects the degrees, and every row has
charge zero (`sjsuHw_charge`).
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The rows of `H_w` in degree `d`. -/
def sjsuHw : ℕ → List ((Mon × Mon) × ℤ)
  | 1 => denseRows sjsuA1 sjsuH1
  | 2 => denseRows sjsuA2 sjsuH2
  | 3 => denseRows sjsuA3 sjsuH3
  | 4 => denseRows sjsuA4 sjsuH4
  | 5 => denseRows sjsuA5 sjsuH5
  | 6 => denseRows sjsuA6 sjsuH6
  | 7 => denseRows sjsuA7 sjsuH7
  | 8 => denseRows sjsuA8 sjsuH8
  | 9 => denseRows sjsuA9 sjsuH9
  | _ => []

/-- **The composition in degree `d`**: the degree-`d` model rows at `(M w, M v)` are `H_{w,d}` at
`(w, v)`. -/
theorem bevalAt_sjsuIntChunks {R : Type*} [CommRing R] {d : ℕ} (hd : d < 10) (w v : Fin 3 → R) :
    bevalAt (sjsuIntChunks d).flatten (sjsuM.apply w) (sjsuM.apply v) = bevalAt (sjsuHw d) w v := by
  interval_cases d
  · rw [sjsuC0_check]; rfl
  · exact sjsuH1_eval w v
  · exact sjsuH2_eval w v
  · exact sjsuH3_eval w v
  · exact sjsuH4_eval w v
  · exact sjsuH5_eval w v
  · exact sjsuH6_eval w v
  · exact sjsuH7_eval w v
  · exact sjsuH8_eval w v
  · exact sjsuH9_eval w v

/-- All rows of `H_w`. -/
def sjsuHwAll : List ((Mon × Mon) × ℤ) :=
  sjsuHw 0 ++ sjsuHw 1 ++ sjsuHw 2 ++ sjsuHw 3 ++ sjsuHw 4 ++ sjsuHw 5 ++ sjsuHw 6 ++ sjsuHw 7 ++
    sjsuHw 8 ++ sjsuHw 9

private theorem charge_of_mem {A : List Mon} {H : List (List ℤ)} {d : ℕ}
    (hA : ∀ b ∈ A, Mon.deg b = d) {e : (Mon × Mon) × ℤ} (he : e ∈ denseRows A H) :
    Mon.deg e.1.1 = Mon.deg e.1.2 := by
  obtain ⟨h1, h2⟩ := mem_denseRows he
  rw [hA _ h1, hA _ h2]

/-- **Charge zero**: `|b| = |b'|` for every row of `H_w`. -/
theorem sjsuHw_charge {e : (Mon × Mon) × ℤ} (he : e ∈ sjsuHwAll) :
    Mon.deg e.1.1 = Mon.deg e.1.2 := by
  simp only [sjsuHwAll, sjsuHw, List.mem_append, List.not_mem_nil, false_or] at he
  rcases he with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
  · exact charge_of_mem sjsuA1_deg h
  · exact charge_of_mem sjsuA2_deg h
  · exact charge_of_mem sjsuA3_deg h
  · exact charge_of_mem sjsuA4_deg h
  · exact charge_of_mem sjsuA5_deg h
  · exact charge_of_mem sjsuA6_deg h
  · exact charge_of_mem sjsuA7_deg h
  · exact charge_of_mem sjsuA8_deg h
  · exact charge_of_mem sjsuA9_deg h

end KAM.EffectiveStability.SJSU

end
