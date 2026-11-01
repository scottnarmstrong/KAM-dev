/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Assembly.PatchInst
public import KAM.Wave.Assembly.Unique
public import KAM.Wave.Assembly.Winding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W8: the W8-side reductions for shell embeddings and family injectivity
(blueprint `bpW:w8:shell-embedding`, `bpW:w8:injective`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint labels `bpW:w8:shell-embedding`, `bpW:w8:injective` (milestone W8).

Lemma `bpW:w8:shell-embedding` and Proposition `bpW:w8:injective` consume Lemma
`bpW:w8:torus-shape` and `bpW:w8:shell-inv`, which need W5's action–angle map
(`bpW:w5:action-angle`, not in this base). This module proves the steps that do not:
* `w8_injMod_of_phase` (Step `stepW:w8:se-inj`, last part): if the angle error `X` is
  `ℤ²`-periodic and `½`-Lipschitz and `θ + X(θ) - θ' - X(θ') ∈ ℤ²`, then `θ - θ' ∈ ℤ²`;
* `w8_eq_zero_of_add_clm` (Step `stepW:w8:se-der`, last part): `h_i = -DX_i(θ)h` with
  `‖DX(θ)‖ ≤ ½` forces `h = 0`;
* `w8KOfBirk_eq_of_eq` (Steps `stepW:w8:se-inj`, `stepW:w8:in-birk`): `K(θ) = K'(θ')` for
  `K = Γ^ℝ ∘ 𝒵⁻¹ ∘ Ψ` (`w8KOfBirk`) and real points of `B^E_{r₁}` gives `Ψ(θ) = Ψ'(θ')`
  (injectivity of `Γ^ℝ`, W3 Corollary `bpW:w3:gamma-real` (iii));
* `w8_freq_eq_of_shape` (Step `stepW:w8:in-freq`): two tori whose `+i` coordinates have the shape
  `a(θ) e^{-2πi(θ_i + X_i(θ))}` (`a > 0`, `X` bounded) and which carry the same orbit have the
  same frequency (Lemma `bpW:w8:winding`);
* `w8_injective_of_pieces` (Proposition `bpW:w8:injective`, assembly; conditional helper): clause
  (6) of `nlw2` from clause (3)'s embedding property, clause (4), equal orbits ⇒ equal frequencies,
  and injectivity of `ν` (`w8_nuInjective`).
-/

@[expose] public noncomputable section

open Set Real

namespace KAM.Wave

/-- Step `stepW:w8:se-inj` of `bpW:w8:shell-embedding` (last part): let `X : ℝ² → ℝ²` be
`ℤ²`-periodic and `½`-Lipschitz. If `θ + X(θ) - θ' - X(θ') = k ∈ ℤ²`, then `θ - θ' = k`. -/
theorem w8_injMod_of_phase {X : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hper : ∀ (θ : Fin 2 → ℝ) (k : Fin 2 → ℤ), X (θ + fun i => (k i : ℝ)) = X θ)
    (hlip : ∀ θ θ' : Fin 2 → ℝ, ‖X θ - X θ'‖ ≤ 1 / 2 * ‖θ - θ'‖) {θ θ' : Fin 2 → ℝ}
    {k : Fin 2 → ℤ} (hk : θ + X θ - θ' - X θ' = fun i => (k i : ℝ)) :
    θ - θ' = fun i => (k i : ℝ) := by
  set θ'' := θ' + fun i => (k i : ℝ)
  have hX : X θ'' = X θ' := hper θ' k
  have e : θ - θ'' = X θ'' - X θ := by
    rw [hX]
    have : θ - θ'' = (θ + X θ - θ' - X θ') - (fun i => (k i : ℝ)) + (X θ' - X θ) := by
      simp only [θ'']; abel
    rw [this, hk, sub_self, zero_add]
  have h := hlip θ'' θ
  rw [← e, norm_sub_rev θ'' θ] at h
  have h0 : ‖θ - θ''‖ = 0 := by linarith [norm_nonneg (θ - θ'')]
  have : θ = θ'' := sub_eq_zero.1 (norm_eq_zero.1 h0)
  rw [this]
  simp only [θ'', add_sub_cancel_left]

/-- Step `stepW:w8:se-der` of `bpW:w8:shell-embedding` (last part): if `h = -L h` for a linear map
`L` with `‖L‖ ≤ ½` (here `L = DX(θ)`), then `h = 0`. -/
theorem w8_eq_zero_of_add_clm {L : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)} (hL : ‖L‖ ≤ 1 / 2)
    {h : Fin 2 → ℝ} (hh : h + L h = 0) : h = 0 := by
  have e : h = -L h := eq_neg_of_add_eq_zero_left hh
  have h1 : ‖h‖ ≤ 1 / 2 * ‖h‖ := by
    calc ‖h‖ = ‖L h‖ := by rw [e, norm_neg, ← e]
      _ ≤ ‖L‖ * ‖h‖ := L.le_opNorm h
      _ ≤ 1 / 2 * ‖h‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg h)
  exact norm_eq_zero.1 (le_antisymm (by linarith [norm_nonneg h]) (norm_nonneg h))

/-- Steps `stepW:w8:se-inj`, `stepW:w8:in-birk`: for Birkhoff tori `Ψ, Ψ'` whose points `Ψ(θ)`,
`Ψ'(θ')` are real (`𝒵 Π w = w`) with `𝒵⁻¹` in `B^E_{r₁}`, `K(θ) = K'(θ')` for
`K = w8KOfBirk m hm Ψ`, `K' = w8KOfBirk m hm Ψ'` gives `Ψ(θ) = Ψ'(θ')` (injectivity of `Γ^ℝ`). -/
theorem w8KOfBirk_eq_of_eq {m : ℝ} {hm : 0 < m} {Ψ Ψ' : (Fin 2 → ℝ) → BirkSpace}
    {θ θ' : Fin 2 → ℝ} (hb : birkPi (Ψ θ) ∈ birkRealBall1 m 1)
    (hb' : birkPi (Ψ' θ') ∈ birkRealBall1 m 1) (hr : birkZR (birkPi (Ψ θ)) = Ψ θ)
    (hr' : birkZR (birkPi (Ψ' θ')) = Ψ' θ') (h : w8KOfBirk m hm Ψ θ = w8KOfBirk m hm Ψ' θ') :
    Ψ θ = Ψ' θ' := by
  rw [w8KOfBirk_of_mem hb, w8KOfBirk_of_mem hb'] at h
  have hx := congrArg Subtype.val (birkGammaR_injective h)
  simp only at hx
  rw [← hr, ← hr', hx]

/-- Step `stepW:w8:in-freq` of `bpW:w8:injective`: let `Ψ, Ψ'` be tori whose `+i` coordinates
(`zc i`) have the shape `a(θ)_i e^{-2πi(θ_i + X_i(θ))}`, `a'(θ)_i e^{-2πi(θ_i + X'_i(θ))}` with
continuous `a, a' > 0` and continuous bounded `X, X'` (Lemma `bpW:w8:torus-shape` (i), (ii)). If
they carry the same orbit, `Ψ(θ + tν) = Ψ'(θ' + tν')` for all `t`, then `ν = ν'` (Lemma
`bpW:w8:winding`). -/
theorem w8_freq_eq_of_shape {F : Type*} (zc : Fin 2 → F → ℂ) {Ψ Ψ' : (Fin 2 → ℝ) → F}
    {a a' X X' : (Fin 2 → ℝ) → Fin 2 → ℝ} (ha : Continuous a) (ha' : Continuous a')
    (hX : Continuous X) (hX' : Continuous X') (hpos : ∀ θ i, 0 < a θ i)
    (hpos' : ∀ θ i, 0 < a' θ i) (hXb : ∃ B, ∀ θ i, |X θ i| ≤ B) (hXb' : ∃ B, ∀ θ i, |X' θ i| ≤ B)
    (hsh : ∀ θ i, zc i (Ψ θ) =
      (a θ i : ℂ) * Complex.exp (-(2 * π * Complex.I * ((θ i + X θ i : ℝ) : ℂ))))
    (hsh' : ∀ θ i, zc i (Ψ' θ) =
      (a' θ i : ℂ) * Complex.exp (-(2 * π * Complex.I * ((θ i + X' θ i : ℝ) : ℂ))))
    {ν ν' θ θ' : Fin 2 → ℝ} (horb : ∀ t : ℝ, Ψ (θ + t • ν) = Ψ' (θ' + t • ν')) : ν = ν' := by
  funext i
  have hline : ∀ (θ₀ ν₀ : Fin 2 → ℝ), Continuous fun t : ℝ => θ₀ + t • ν₀ :=
    fun θ₀ ν₀ => continuous_const.add (continuous_id.smul continuous_const)
  have happ : ∀ (θ₀ ν₀ : Fin 2 → ℝ) (t : ℝ), (θ₀ + t • ν₀) i = θ₀ i + t * ν₀ i := fun _ _ _ => by
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  obtain ⟨B, hB⟩ := hXb
  obtain ⟨B', hB'⟩ := hXb'
  refine winding_rate_eq (a := fun t => a (θ + t • ν) i) (a' := fun t => a' (θ' + t • ν') i)
    (φ := fun t => (θ + t • ν) i + X (θ + t • ν) i)
    (φ' := fun t => (θ' + t • ν') i + X' (θ' + t • ν') i)
    ((continuous_apply i).comp (ha.comp (hline θ ν)))
    ((continuous_apply i).comp (ha'.comp (hline θ' ν')))
    (((continuous_apply i).comp (hline θ ν)).add ((continuous_apply i).comp (hX.comp (hline θ ν))))
    (((continuous_apply i).comp (hline θ' ν')).add
      ((continuous_apply i).comp (hX'.comp (hline θ' ν'))))
    (fun t => hpos _ i) (fun t => hpos' _ i) ⟨|θ i| + B, fun t => ?_⟩ ⟨|θ' i| + B', fun t => ?_⟩
    fun t => ?_
  · simp only [happ]
    have : θ i + t * ν i + X (θ + t • ν) i - t * ν i = θ i + X (θ + t • ν) i := by ring
    rw [this]
    exact (abs_add_le _ _).trans (add_le_add le_rfl (hB _ i))
  · simp only [happ]
    have : θ' i + t * ν' i + X' (θ' + t • ν') i - t * ν' i = θ' i + X' (θ' + t • ν') i := by ring
    rw [this]
    exact (abs_add_le _ _).trans (add_le_add le_rfl (hB' _ i))
  · rw [← hsh, ← hsh', horb t]

/-- **Family injectivity, assembly** (blueprint `bpW:w8:injective`, Steps `stepW:w8:in-orbit`,
`stepW:w8:in-act`, `stepW:w8:in-ang`; conditional helper): for any `Γ`, `ν`, `K` such that every
`K_I` (`I ∈ Γ`) is an analytic torus embedding (clause (3), `bpW:w8:shell-embedding`) satisfying
the invariance of clause (4) with `ν(I)` (`bpW:w8:shell-inv` (i)), equal orbits have equal
frequencies (Steps `stepW:w8:in-birk`, `stepW:w8:in-freq`: `w8KOfBirk_eq_of_eq`,
`w8_freq_eq_of_shape`), and `ν` is injective on `Γ` (`w8_nuInjective`): clause (6) of `nlw2`. -/
theorem w8_injective_of_pieces {m : ℝ} (hm : 0 < m) {Γ : Set (Fin 2 → ℝ)}
    {ν : (Fin 2 → ℝ) → Fin 2 → ℝ} {K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → WaveSpace}
    (hemb : ∀ I ∈ Γ, IsAnalyticTorusEmbedding (K I))
    (hinv : ∀ I ∈ Γ, ∀ (θ : Fin 2 → ℝ) (j : ℕ+),
      HasDerivAt (fun t : ℝ => coeff (K I (θ + t • ν I)).1 j) (lam m hm j * coeff (K I θ).2 j) 0 ∧
      HasDerivAt (fun t : ℝ => coeff (K I (θ + t • ν I)).2 j)
        (-(lam m hm j * coeff (K I θ).1 j) - cubicGrad m hm (K I θ).1 j) 0)
    (hfreq : ∀ I ∈ Γ, ∀ I' ∈ Γ, ∀ θ θ' : Fin 2 → ℝ,
      (∀ t : ℝ, K I (θ + t • ν I) = K I' (θ' + t • ν I')) → ν I = ν I')
    (hνinj : InjOn ν Γ) :
    ∀ I ∈ Γ, ∀ I' ∈ Γ, ∀ θ θ' : Fin 2 → ℝ, K I θ = K I' θ' →
      I = I' ∧ ∃ k : Fin 2 → ℤ, θ - θ' = fun i => (k i : ℝ) := by
  intro I hI I' hI' θ θ' hmeet
  have horb : ∀ t : ℝ, K I (θ + t • ν I) = K I' (θ' + t • ν I') := fun t =>
    w8_orbit_eq_of_meet hm (hemb I hI).2.1 (hemb I' hI').2.1 (hinv I hI) (hinv I' hI') hmeet t
  have hII : I = I' := hνinj hI hI' (hfreq I hI I' hI' θ θ' horb)
  subst hII
  exact ⟨rfl, (hemb I hI).2.2.1 θ θ' hmeet⟩

end KAM.Wave

end
