/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.Site3

/-!
# Sharding the fibre walk

One kernel declaration holds about `2.5·10³` fibres under a `4 GB` process cap (the kernel caches
about `215 KB` per fibre; `docs/campaign/handoffs/V2-3FREQ.md`), while a planetary site needs
`10⁶–10⁸`. The walk is a bisection, so its subtrees are independent computations:

* `balFold_succ_of`: two halves give the parent (`balFold f (l+1) a`), so any subtree of
  `walk2 M N l = balFold (row2 M N l) l 0`, and of a row `balFold (cell2 M N i) l 0`, can be its own
  `decide +kernel` theorem, and the parents follow by this lemma without recomputation;
* `row2_of_le`: a row of the diamond is the bisection of its cells;
* `fiberSiteOk_of`: the fibered site test from its cheap conjuncts, a separately proved walk
  value `s` and the bound `fibBound … s ≤ B`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.Fiber

/-- Two halves of a bisection give the parent. -/
theorem balFold_succ_of {f : ℕ → Option ℕ} {l a x y : ℕ} (h1 : balFold f l a = some x)
    (h2 : balFold f l (a + pow2 l) = some y) : balFold f (l + 1) a = some (x + y) := by
  simp only [balFold, h1, h2]

/-- A row of the diamond is the bisection of its cells. -/
theorem row2_of_le {M : ℤ → ℤ → Option ℕ} {N l i : ℕ} (hi : i ≤ 2 * N) :
    row2 M N l i = balFold (cell2 M N i) l 0 := by
  rw [row2, ite_eq_right (by omega)]

/-- A row outside the diamond is `0`. -/
theorem row2_of_lt {M : ℤ → ℤ → Option ℕ} {N l i : ℕ} (hi : 2 * N < i) :
    row2 M N l i = some 0 := by
  rw [row2, ite_eq_left hi]

/-- The cheap conjuncts of `fiberSiteOk` (everything but the walk and its bound). -/
def fiberPreOk (n τ : ℕ) (box : FreqBox) (γ b c : ℚ) (w : FibWit) : Bool :=
  decide (n = 3) && decide (0 < c) && decide (0 < b) && decide (0 < γ) &&
    decide (0 < clockC box - clockR box) && dboxOk box w.D && decide (0 < cLoQ (2 * b) τ w.N) &&
    decide (w.e ≤ 2 ^ w.P) && decide ((2 : ℚ) ^ w.P ≤ w.e * expLowQ (2 * b) w.J) &&
    decide (2 * w.N + 1 ≤ 2 ^ w.l) &&
    decide (2 ^ n * w.B * ((clockC box - clockR box) ^ 2)⁻¹ * (γ * b ^ τ) ^ 2 ≤
      (2 * (31415 / 10000) * c) ^ 2)

/-- **Sharding of a fibered site**: the test from its cheap part, the walk's value (proved by
shards and `balFold_succ_of`) and the bound. -/
theorem fiberSiteOk_of {n τ : ℕ} {box : FreqBox} {γ b c : ℚ} {w : FibWit} {s : ℕ}
    (hpre : fiberPreOk n τ box γ b c w = true)
    (hs : walk2 (mode3K w.D w.e w.P) w.N w.l = some s) (hB : fibBound box γ b τ w s ≤ w.B) :
    fiberSiteOk n τ box γ b c w = true := by
  simp only [fiberPreOk, Bool.and_eq_true, decide_eq_true_eq] at hpre
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := hpre
  have hsum : fibSumOk box γ b τ w = true := by
    simp only [fibSumOk, hs, decide_eq_true_eq]
    exact hB
  simp only [fiberSiteOk, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, hsum⟩, h11⟩

/-- A site of the engines from a sharded fibered test. -/
theorem siteOkG_fiber_of {n τ J : ℕ} {box : FreqBox} {κ γ b c : ℚ} {w : FibWit}
    (h : fiberSiteOk n τ box γ b c w = true) : siteOkG n τ J box κ γ b c (.fiber w) = true := h

end KAM.CertificateSharp.V2

end
