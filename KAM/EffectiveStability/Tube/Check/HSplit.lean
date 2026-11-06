/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Check.TailMaj
public import KAM.EffectiveStability.Tube.Check.BracketBound
public import KAM.EffectiveStability.Tube.Poly.HTildeBounds

/-!
# The Taylor split of `h̃` as a list observable (T2-CONF, N9 (C))

* `sum_truncSet_fin3`: a sum over N4's `truncSet (Fin 3) L` as a triple range sum;
* `sum_truncSet_eq_list`: the same sum over a list `l` of triples enumerating `truncSet` (each
  monomial once);
* `hTildeOf_eq_listObs`: N5a's Taylor split `h̃ = Σ_{|m| ≤ L} h_m u^m + R` as
  `listObs l monOf (h_m) + R`;
* `differentiableAt_hRem`: the remainder `R` is jointly differentiable where `B > 0` and
  `B + u > 0` (from `h̃` and the coefficients, which are);
* `reducedBracket_hTilde_bound`: the bracket of a list observable with `h̃` on the tube, from the
  certificates, the kept and dropped bounds, and the remainder budget (N9 (B) with `h = h̃`).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open Finset

/-- A sum over `truncSet (Fin 3) L` as a triple range sum. -/
theorem sum_truncSet_fin3 (F : (Fin 3 → ℕ) → ℝ) (L : ℕ) :
    ∑ p ∈ truncSet (Fin 3) L, F p = ∑ a ∈ range (L + 1), ∑ b ∈ range (L + 1),
      ∑ c ∈ range (L + 1), if a + b + c ≤ L then F ![a, b, c] else 0 := by
  rw [truncSet, Finset.sum_filter, ← Finset.sum_product', ← Finset.sum_product']
  refine Finset.sum_nbij' (fun p => ((p 0, p 1), p 2)) (fun t => ![t.1.1, t.1.2, t.2])
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Fintype.mem_piFinset] at hp
    simp [mem_product, hp 0, hp 1, hp 2]
  · intro t ht
    simp only [mem_product] at ht
    simp only [Fintype.mem_piFinset]
    intro j; fin_cases j <;> simp [ht.1.1, ht.1.2, ht.2]
  · intro p _; ext j; fin_cases j <;> rfl
  · intro t _; rfl
  · intro p _
    have e : ![p 0, p 1, p 2] = p := by ext j; fin_cases j <;> rfl
    simp only [Fin.sum_univ_three, e]

/-- A sum over `truncSet (Fin 3) L` along a list of triples enumerating it. -/
theorem sum_truncSet_eq_list {L : ℕ} (l : List (ℕ × ℕ × ℕ)) (hnd : (l.map monOf).Nodup)
    (hmem : ∀ t ∈ l, t.1 + t.2.1 + t.2.2 ≤ L)
    (hcov : ∀ a b c, a + b + c ≤ L → (a, b, c) ∈ l) (F : (Fin 3 → ℕ) → ℝ) :
    ∑ p ∈ truncSet (Fin 3) L, F p = (l.map fun t => F (monOf t)).sum := by
  have hset : truncSet (Fin 3) L = (l.map monOf).toFinset := by
    ext p
    rw [mem_truncSet_iff, List.mem_toFinset, List.mem_map]
    constructor
    · intro hp
      refine ⟨(p 0, p 1, p 2), hcov _ _ _ ?_, ?_⟩
      · simpa [mdeg, Fin.sum_univ_three] using hp
      · ext j; fin_cases j <;> rfl
    · rintro ⟨t, ht, rfl⟩
      simpa [mdeg, monOf, Fin.sum_univ_three] using hmem t ht
  rw [hset, List.sum_toFinset _ hnd, List.map_map]
  rfl

variable (E N : ℕ)

/-- **The Taylor split as a list observable.** -/
theorem hTildeOf_eq_listObs {L : ℕ} (rows : List ((Mon × Mon) × ℤ)) (B : (Fin 2 → ℝ) → Fin 3 → ℝ)
    (l : List (ℕ × ℕ × ℕ)) (hnd : (l.map monOf).Nodup) (hmem : ∀ t ∈ l, t.1 + t.2.1 + t.2.2 ≤ L)
    (hcov : ∀ a b c, a + b + c ≤ L → (a, b, c) ∈ l) (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) :
    hTildeOf E N rows B p =
      listObs l (fun t => monOf t) (fun t => hCoef E N rows B (monOf t)) p +
        hRem E N rows B L p := by
  rw [hTildeOf_taylor E N rows B L p, sum_truncSet_eq_list l hnd hmem hcov, listObs]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  ring

/-- The remainder is jointly differentiable where `B > 0` and `B + u > 0`. -/
theorem differentiableAt_hRem {L : ℕ} (rows : List ((Mon × Mon) × ℤ))
    (B : (Fin 2 → ℝ) → Fin 3 → ℝ) (hB : Differentiable ℝ B) (hpos : ∀ φ j, 0 < B φ j)
    {p : (Fin 3 → ℝ) × (Fin 2 → ℝ)} (hpu : ∀ j, 0 < B p.2 j + p.1 j) :
    DifferentiableAt ℝ (hRem E N rows B L) p := by
  have e : hRem E N rows B L = fun q => hTildeOf E N rows B q -
      ∑ m ∈ truncSet (Fin 3) L, hCoef E N rows B m q.2 * umon m q.1 := by
    funext q; rw [hTildeOf_taylor E N rows B L q]; ring
  rw [e]
  refine (differentiableAt_hTildeOf E N rows B (hB p.2) hpu).sub
    (DifferentiableAt.fun_sum fun m _ => ?_)
  exact ((differentiable_hCoef E N rows B hB hpos m p.2).comp p differentiableAt_snd).mul
    ((differentiable_umon m p.1).comp p differentiableAt_fst)

/-- **The bracket with `h̃` on the tube.** For a list observable `f`, N5a's
`h̃ = hTildeOf E N rows B` (with `B > 0` differentiable), the Taylor split at degree `L` written
along a list `Hl` enumerating `truncSet (Fin 3) L`, true coefficients `hc_t = h_{monOf t}`, models
`k_t` with `C¹` certificates, kept-monomial bounds `G` (degree `≤ L'`), a bound `D` of the dropped
part, `f`-partial bounds `Fd`, `Fp` and remainder bounds `Ru`, `Rp` at `(u, φ)` with
`B(φ) + u > 0`:
`|{f, h̃}(u, φ)| ≤ KEPT + D + ERR + TAIL`. -/
theorem reducedBracket_hTilde_bound {ι : Type*} (Fl : List ι) (μ : ι → Fin 3 → ℕ)
    (g : ι → (Fin 2 → ℝ) → ℝ) (hg : ∀ i ∈ Fl, Differentiable ℝ (g i))
    (rows : List ((Mon × Mon) × ℤ)) (B : (Fin 2 → ℝ) → Fin 3 → ℝ) (hB : Differentiable ℝ B)
    (hpos : ∀ φ j, 0 < B φ j) {L : ℕ} (Hl : List (ℕ × ℕ × ℕ)) (hnd : (Hl.map monOf).Nodup)
    (hmem : ∀ t ∈ Hl, t.1 + t.2.1 + t.2.2 ≤ L) (hcov : ∀ a b c, a + b + c ≤ L → (a, b, c) ∈ Hl)
    (k hc : ℕ × ℕ × ℕ → (Fin 2 → ℝ) → ℝ)
    (hbr : ∀ t ∈ Hl, ∀ φ, hc t φ = hCoef E N rows B (monOf t) φ)
    {e₀ e₁ : ℕ × ℕ × ℕ → ℝ} (hcert : ∀ t ∈ Hl, C1Close (hc t) (k t) (e₀ t) (e₁ t))
    {L' : ℕ} {r D : ℝ} {G : (Fin 3 → ℕ) → ℝ}
    (hG : ∀ p ∈ truncSet (Fin 3) L', ∀ φ, |((bterms Fl Hl).filter fun b =>
      decide (b.mon μ (fun t => monOf t) = p)).map
        (fun b => (b.coef μ (fun t => monOf t) : ℝ) * b.val g k φ) |>.sum| ≤ G p)
    {u : Fin 3 → ℝ} (hu : ∀ l, |u l| ≤ r) (φ : Fin 2 → ℝ)
    (hDrop : |((bterms Fl Hl).filter fun b => decide (L' < mdeg (b.mon μ (fun t => monOf t)))).map
      (fun b => (b.coef μ (fun t => monOf t) : ℝ) * umon (b.mon μ (fun t => monOf t)) u *
        b.val g k φ) |>.sum| ≤ D)
    {Fd Fp : Fin 2 → ℝ}
    (hFd : ∀ a : Fin 2, |fderiv ℝ (listObs Fl μ g) (u, φ) (Pi.single a.castSucc 1, 0) -
      fderiv ℝ (listObs Fl μ g) (u, φ) (Pi.single 2 1, 0)| ≤ Fd a)
    (hFp : ∀ a : Fin 2, |fderiv ℝ (listObs Fl μ g) (u, φ) (0, Pi.single a 1)| ≤ Fp a)
    (hpu : ∀ j, 0 < B φ j + u j) {Ru : Fin 3 → ℝ} {Rp : ℝ}
    (hRu : ∀ l, |fderiv ℝ (fun v => hRem E N rows B L (v, φ)) u (Pi.single l 1)| ≤ Ru l)
    (hRp : ∀ a, |fderiv ℝ (fun ψ => hRem E N rows B L (u, ψ)) φ (Pi.single a 1)| ≤ Rp) :
    |reducedBracket (listObs Fl μ g) (hTildeOf E N rows B) (u, φ)| ≤
      bracketKept L' r G + D + bracketErr Hl (fun t => monOf t) r e₀ e₁ Fd Fp +
        bracketTail Fd Fp Ru Rp := by
  have hdec : ∀ p, hTildeOf E N rows B p =
      listObs Hl (fun t => monOf t) hc p + hRem E N rows B L p := by
    intro p
    rw [hTildeOf_eq_listObs E N rows B Hl hnd hmem hcov p]
    congr 1
    unfold listObs
    exact congrArg List.sum (List.map_congr_left fun t ht => by rw [hbr t ht])
  exact reducedBracket_bound_of_drop Fl μ g Hl (fun t => monOf t) k hc hg hcert hdec hG hu φ hDrop
    hFd hFp (differentiableAt_hRem E N rows B hB hpos (p := (u, φ)) hpu) hRu hRp

end KAM.EffectiveStability.Tube

end
