/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Assembly.Patch
public import KAM.Wave.Measure.Coords

/-!
# W8: separation of frequencies across shells (blueprint `bpW:w8:nu-injective`, W6-free steps)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w8:nu-injective` (milestone W8), its W6-free steps only.

Lemma `bpW:w8:nu-injective` itself consumes Lemma `bpW:w8:freq-shell` (ii), (iii), a W6 result
(through `bpW:w8:w6-general`); it is not proved here. This module proves:
* `w8_freq_ne_of_shells` (Step `stepW:w8:ni-diff`): vectors within `α_n/(70 L_A)`, resp.
  `α_{n'}/(70 L_A)`, of `ω⁰` at points of different trimmed shells are different (from
  `bpW:w8:shell-data` (ii) and W7's `bpW:w7:freqcoords` (iv));
* `w8PatchNu_injOn_of_pieces`: the assembly of Steps `stepW:w8:ni-same`, `stepW:w8:ni-diff` for
  arbitrary pieces. It is a conditional helper whose hypotheses `hsame`, `hclose` are, for the
  shell iteration, W6's Lemma `bpW:w8:freq-shell` (ii), (iii); it does not stand in for
  `bpW:w8:nu-injective`.
-/

public section

open Set

namespace KAM.Wave

variable {m : ℝ} (hm : 0 < m) {t0 : ℝ}

/-- Step `stepW:w8:ni-diff` of `bpW:w8:nu-injective`: if `ξ ∈ Π_n`, `ξ' ∈ Π_{n'}`, `n ≠ n'`, and
`|w - ω⁰(ξ)| ≤ α_n/(70 L_A)`, `|w' - ω⁰(ξ')| ≤ α_{n'}/(70 L_A)`, then `w ≠ w'`. -/
theorem w8_freq_ne_of_shells (ht : 0 < t0) {n n' : ℕ} (hnn : n ≠ n') {ξ ξ' : Fin 2 → ℝ}
    (hξ : ξ ∈ w8Pi t0 n) (hξ' : ξ' ∈ w8Pi t0 n') {w w' : Fin 2 → ℝ}
    (hw : ‖w - omegaTan m hm ξ‖ ≤ w8alpha t0 n / (70 * measLA m hm))
    (hw' : ‖w' - omegaTan m hm ξ'‖ ≤ w8alpha t0 n' / (70 * measLA m hm)) : w ≠ w' := by
  intro heq
  subst heq
  have hsep := w8Pi_sep_of_ne ht hnn hξ hξ'
  rw [dist_eq_norm] at hsep
  have hL := measLA_pos m hm
  have h1 := norm_sub_le_measLA_mul m hm ξ ξ'
  have h2 : ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤
      ‖w - omegaTan m hm ξ‖ + ‖w - omegaTan m hm ξ'‖ := by
    calc ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ =
          ‖(w - omegaTan m hm ξ') - (w - omegaTan m hm ξ)‖ := by congr 1; abel
      _ ≤ ‖w - omegaTan m hm ξ'‖ + ‖w - omegaTan m hm ξ‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  set a := w8alpha t0 n
  set a' := w8alpha t0 n'
  have ha := w8alpha_pos ht n
  have ha' := w8alpha_pos ht n'
  have h3 : ‖ξ - ξ'‖ ≤ (a + a') / 70 := by
    calc ‖ξ - ξ'‖ ≤ measLA m hm * (a / (70 * measLA m hm) + a' / (70 * measLA m hm)) :=
          h1.trans (mul_le_mul_of_nonneg_left (h2.trans (add_le_add hw hw')) hL.le)
      _ = (a + a') / 70 := by field_simp
  have h4 : a + a' ≤ 2 * max a a' := by
    linarith [le_max_left a a', le_max_right a a']
  have h5 : 0 < max a a' := lt_max_of_lt_left ha
  linarith

/-- Steps `stepW:w8:ni-same`, `stepW:w8:ni-diff` of `bpW:w8:nu-injective` for arbitrary pieces
(conditional helper; for the shell iteration `hsame`, `hclose` are W6's `bpW:w8:freq-shell` (ii),
(iii), with `ω^{(n)}_* = 2π ν^{(n)}_*`). -/
theorem w8PatchNu_injOn_of_pieces (ht : 0 < t0) {Γs : ℕ → Set (Fin 2 → ℝ)}
    (hΓ : ∀ n, Γs n ⊆ w8Pi t0 n) {νs : ℕ → (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hsame : ∀ n, ∀ ξ ∈ Γs n, ∀ ξ' ∈ Γs n, 7 / (8 * measLA m hm) * ‖ξ - ξ'‖ ≤
      ‖(2 * Real.pi) • νs n ξ - (2 * Real.pi) • νs n ξ'‖)
    (hclose : ∀ n, ∀ ξ ∈ Γs n,
      ‖(2 * Real.pi) • νs n ξ - omegaTan m hm ξ‖ ≤ w8alpha t0 n / (70 * measLA m hm)) :
    InjOn (w8PatchNu t0 Γs νs) (w8PatchSet Γs) := by
  intro I hI I' hI' heq
  obtain ⟨n, hn⟩ := mem_iUnion.1 hI
  obtain ⟨n', hn'⟩ := mem_iUnion.1 hI'
  rw [w8PatchNu_of_mem hΓ ht νs hn, w8PatchNu_of_mem hΓ ht νs hn'] at heq
  by_cases hnn : n = n'
  · subst hnn
    have h := hsame n I hn I' hn'
    rw [heq, sub_self, norm_zero] at h
    have hc : 0 < 7 / (8 * measLA m hm) := by have := measLA_pos m hm; positivity
    have : ‖I - I'‖ ≤ 0 := by nlinarith [norm_nonneg (I - I')]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  · exact absurd (congrArg ((2 * Real.pi) • ·) heq)
      (w8_freq_ne_of_shells hm ht hnn (hΓ n hn) (hΓ n' hn') (hclose n I hn) (hclose n' I' hn'))

end KAM.Wave

end
