/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainWeak

/-!
# Real restrictions of `K` and `X_K` (blueprint-W `bpW:w3:main` (ii))

Package W3-MAIN, blueprint labels `bpW:w3:main`, `bpW:w3:real-restrict`.

On the real ball `{x ∈ E | 320 C_F ‖x‖² < 1}` (so `‖𝒵 x‖ < ρ₁`): `x ↦ K(𝒵 x)` is real valued and
real analytic (`birkKExt_real`), `x ↦ Π X_K(𝒵 x)` is a real analytic map into `E_{a,p+1}` with
`𝒵 Π X_K(𝒵 x) = X_K(𝒵 x)` (`birkXKExt_real`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {m : ℝ} {hm : 0 < m} {a p : ℝ} {ha : 0 ≤ a} {hp : 1 / 2 ≤ p}

include hm hp in
theorem birkKExt_real :
    AnalyticOnNhd ℝ (fun x : BirkReal => (birkKExt m hm ha hp (birkZR x)).re)
        {x : BirkReal | 320 * birkCF m p * ‖x‖ ^ 2 < 1} ∧
      ∀ x : BirkReal, 320 * birkCF m p * ‖x‖ ^ 2 < 1 →
        (((birkKExt m hm ha hp (birkZR x)).re : ℝ) : ℂ) = birkKExt m hm ha hp (birkZR x) := by
  have h := real_restrict_fun (U := {w : BirkSpace | 160 * birkCF m p * ‖w‖ ^ 2 < 1})
    (P := birkKExt m hm ha hp)
    (fun w hw => (birkKExt_isClassA (ha := ha) (hm := hm) (hp := hp)).analytic w hw)
    (fun w hw => (birkKExt_isClassA (ha := ha) (hm := hm) (hp := hp)).real w hw)
  refine ⟨fun x hx => h.1 x (birkZR_dom (hm := hm) (hp := hp) x hx), fun x hx =>
    h.2 x (birkZR_dom (hm := hm) (hp := hp) x hx)⟩

include hm hp in
theorem birkXKExt_real :
    AnalyticOnNhd ℝ (fun x : BirkReal => birkPi (birkXKExt m hm ha hp (birkZR x)))
        {x : BirkReal | 320 * birkCF m p * ‖x‖ ^ 2 < 1} ∧
      ∀ x : BirkReal, 320 * birkCF m p * ‖x‖ ^ 2 < 1 →
        birkZR (birkPi (birkXKExt m hm ha hp (birkZR x))) = birkXKExt m hm ha hp (birkZR x) := by
  have h := real_restrict (U := {w : BirkSpace | 160 * birkCF m p * ‖w‖ ^ 2 < 1})
    (f := birkXKExt m hm ha hp)
    (fun w hw => (birkKExt_isClassA (ha := ha) (hm := hm) (hp := hp)).analytic_field w hw)
    (fun w hw => (birkKExt_isClassA (ha := ha) (hm := hm) (hp := hp)).field_rho hw)
  refine ⟨fun x hx => h.1 x (birkZR_dom (hm := hm) (hp := hp) x hx), fun x hx =>
    h.2 x (birkZR_dom (hm := hm) (hp := hp) x hx)⟩

end KAM.Wave

end
